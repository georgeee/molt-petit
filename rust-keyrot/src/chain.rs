//! An IVC-style chain of set transitions with recursive proofs.
//!
//! Each step is its own circuit; a transition circuit *verifies the previous
//! step's proof inside itself*, so a valid proof at step `i` attests the entire
//! history back to the initial set. Every chain proof has exactly four public
//! inputs: the current set **commitment** (`Poseidon(slots)`).
//!
//! Pipeline used by the example: `Base → Transition(Add) → Transition(Remove)`,
//! then `MembershipProof` to show a specific key is in the current set.
//!
//! For an arbitrary-length chain you'd switch to Plonky2's *cyclic* recursion
//! (`common_data_for_recursion` + `conditionally_verify_cyclic_proof_or_dummy`)
//! so one circuit verifies a proof of itself. For this fixed sequence the
//! simpler heterogeneous chain (one distinct circuit per step) is enough.

use anyhow::Result;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget};

use crate::types::{C, D, F};

/// Number of field elements in a Poseidon commitment / chain proof's public inputs.
const COMMITMENT_LEN: usize = 4;

/// A set transition.
#[derive(Clone, Copy, Debug)]
pub enum Op {
    /// Insert `key` into an empty slot.
    Add,
    /// Remove `key` from the slot that holds it.
    Remove,
}

/// Step 0: commit to the initial set. Public inputs: the commitment.
pub struct BaseCircuit {
    pub data: CircuitData<F, C, D>,
    keys: Vec<Target>,
}

impl BaseCircuit {
    pub fn build(capacity: usize) -> Self {
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
        let keys = builder.add_virtual_targets(capacity);
        let commitment = builder.hash_n_to_hash_no_pad::<PoseidonHash>(keys.clone());
        builder.register_public_inputs(&commitment.elements);
        let data = builder.build::<C>();
        Self { data, keys }
    }

    pub fn prove(&self, slots: &[F]) -> Result<ProofWithPublicInputs<F, C, D>> {
        let mut pw = PartialWitness::new();
        set_targets(&mut pw, &self.keys, slots)?;
        self.data.prove(pw)
    }
}

/// Step i (i > 0): verify the previous proof, apply one transition, commit to
/// the new set. Public inputs: the new commitment.
pub struct TransitionCircuit {
    pub data: CircuitData<F, C, D>,
    prev_proof: ProofWithPublicInputsTarget<D>,
    prev_keys: Vec<Target>,
    new_keys: Vec<Target>,
    selector: Vec<BoolTarget>,
    key: Target,
}

impl TransitionCircuit {
    pub fn build(prev: &CircuitData<F, C, D>, op: Op, capacity: usize) -> Self {
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());

        // --- Recursively verify the previous step's proof. ---
        let prev_proof = builder.add_virtual_proof_with_pis(&prev.common);
        let prev_vd = builder.constant_verifier_data(&prev.verifier_only);
        builder.verify_proof::<C>(&prev_proof, &prev_vd, &prev.common);

        let prev_keys = builder.add_virtual_targets(capacity);
        let new_keys = builder.add_virtual_targets(capacity);
        let key = builder.add_virtual_target();

        // Bind prev_keys to the commitment the previous proof asserts.
        let computed_prev = builder.hash_n_to_hash_no_pad::<PoseidonHash>(prev_keys.clone());
        for j in 0..COMMITMENT_LEN {
            builder.connect(computed_prev.elements[j], prev_proof.public_inputs[j]);
        }

        // --- One-hot selector: exactly one slot is touched. ---
        let selector: Vec<BoolTarget> = (0..capacity)
            .map(|_| builder.add_virtual_bool_target_safe())
            .collect();
        let mut sel_sum = builder.zero();
        for s in &selector {
            sel_sum = builder.add(sel_sum, s.target);
        }
        let one = builder.one();
        builder.connect(sel_sum, one);

        // `key_at_selected = Σ_j selector_j * prev_keys_j`  (value in the touched slot).
        let zero = builder.zero();
        let mut key_at_selected = zero;
        for j in 0..capacity {
            let sp = builder.mul(selector[j].target, prev_keys[j]);
            key_at_selected = builder.add(key_at_selected, sp);
        }

        match op {
            Op::Add => {
                // The touched slot must have been empty, and `key` lands there.
                builder.connect(key_at_selected, zero); // prev slot was empty
                for j in 0..capacity {
                    // new_j = prev_j + selector_j * key
                    let sk = builder.mul(selector[j].target, key);
                    let expected = builder.add(prev_keys[j], sk);
                    builder.connect(new_keys[j], expected);
                }
            }
            Op::Remove => {
                // The touched slot held `key`, and is zeroed.
                builder.connect(key_at_selected, key); // prev slot held `key`
                for j in 0..capacity {
                    // new_j = prev_j - selector_j * prev_j = prev_j * (1 - selector_j)
                    let sp = builder.mul(selector[j].target, prev_keys[j]);
                    let expected = builder.sub(prev_keys[j], sp);
                    builder.connect(new_keys[j], expected);
                }
            }
        }

        // --- New commitment is the public output. ---
        let new_commitment = builder.hash_n_to_hash_no_pad::<PoseidonHash>(new_keys.clone());
        builder.register_public_inputs(&new_commitment.elements);

        let data = builder.build::<C>();
        Self {
            data,
            prev_proof,
            prev_keys,
            new_keys,
            selector,
            key,
        }
    }

    /// Prove the transition. `idx` is the slot touched, `key` the added/removed value.
    pub fn prove(
        &self,
        prev_proof: &ProofWithPublicInputs<F, C, D>,
        prev_slots: &[F],
        new_slots: &[F],
        idx: usize,
        key: F,
    ) -> Result<ProofWithPublicInputs<F, C, D>> {
        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&self.prev_proof, prev_proof)?;
        set_targets(&mut pw, &self.prev_keys, prev_slots)?;
        set_targets(&mut pw, &self.new_keys, new_slots)?;
        for (j, s) in self.selector.iter().enumerate() {
            pw.set_bool_target(*s, j == idx)?;
        }
        pw.set_target(self.key, key)?;
        self.data.prove(pw)
    }
}

/// Final step: verify a chain proof and additionally prove a (private) member is
/// in the current, derived set. Public inputs: the current commitment.
pub struct MembershipProofCircuit {
    pub data: CircuitData<F, C, D>,
    chain_proof: ProofWithPublicInputsTarget<D>,
    keys: Vec<Target>,
    member: Target,
}

impl MembershipProofCircuit {
    pub fn build(chain: &CircuitData<F, C, D>, capacity: usize) -> Self {
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());

        // Recursively verify the chain proof (the whole derivation).
        let chain_proof = builder.add_virtual_proof_with_pis(&chain.common);
        let vd = builder.constant_verifier_data(&chain.verifier_only);
        builder.verify_proof::<C>(&chain_proof, &vd, &chain.common);

        // Bind the current keys to the commitment the chain proof asserts.
        let keys = builder.add_virtual_targets(capacity);
        let computed = builder.hash_n_to_hash_no_pad::<PoseidonHash>(keys.clone());
        for j in 0..COMMITMENT_LEN {
            builder.connect(computed.elements[j], chain_proof.public_inputs[j]);
        }

        // Membership: Π_j (member - key_j) == 0. (Empty slots are 0; a real,
        // non-zero member never matches them, so they don't create false hits.)
        let member = builder.add_virtual_target();
        let mut acc = builder.one();
        for &k in &keys {
            let diff = builder.sub(member, k);
            acc = builder.mul(acc, diff);
        }
        let zero = builder.zero();
        builder.connect(acc, zero);

        // Re-expose the current commitment.
        builder.register_public_inputs(&chain_proof.public_inputs[..COMMITMENT_LEN]);

        let data = builder.build::<C>();
        Self {
            data,
            chain_proof,
            keys,
            member,
        }
    }

    pub fn prove(
        &self,
        chain_proof: &ProofWithPublicInputs<F, C, D>,
        current_slots: &[F],
        member: F,
    ) -> Result<ProofWithPublicInputs<F, C, D>> {
        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&self.chain_proof, chain_proof)?;
        set_targets(&mut pw, &self.keys, current_slots)?;
        pw.set_target(self.member, member)?;
        self.data.prove(pw)
    }
}

fn set_targets(pw: &mut PartialWitness<F>, targets: &[Target], values: &[F]) -> Result<()> {
    assert_eq!(targets.len(), values.len(), "target/value length mismatch");
    for (t, v) in targets.iter().zip(values) {
        pw.set_target(*t, *v)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keyset::KeySet;

    #[test]
    fn chain_then_membership() -> Result<()> {
        const CAP: usize = 4;
        let base = BaseCircuit::build(CAP);
        let add = TransitionCircuit::build(&base.data, Op::Add, CAP);
        let remove = TransitionCircuit::build(&add.data, Op::Remove, CAP);
        let membership = MembershipProofCircuit::build(&remove.data, CAP);

        let mut set = KeySet::from_keys(CAP, [11, 22, 33]);
        let p0 = base.prove(&set.padded())?;

        let prev = set.padded();
        let idx = set.add(44).unwrap();
        let p1 = add.prove(&p0, &prev, &set.padded(), idx, KeySet::field_key(44))?;

        let prev = set.padded();
        let idx = set.slot_of(22).unwrap();
        set.remove(22);
        let p2 = remove.prove(&p1, &prev, &set.padded(), idx, KeySet::field_key(22))?;
        remove.data.verify(p2.clone())?;
        assert_eq!(p2.public_inputs[..4], set.commitment().elements);

        // A surviving original key is a provable member.
        let pm = membership.prove(&p2, &set.padded(), KeySet::field_key(33))?;
        membership.data.verify(pm.clone())?;
        assert_eq!(pm.public_inputs[..4], set.commitment().elements);
        Ok(())
    }
}
