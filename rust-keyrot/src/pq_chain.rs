//! Threshold-signed replacement transitions, chained recursively, using the
//! post-quantum [`crate::pq_sig`] signatures.
//!
//! Same shape as [`crate::signed_chain`], but signatures are cheap hash-based
//! blobs verified *by direct in-circuit hashing* rather than by recursively
//! verifying a Plonky2 proof per signature. So each step recursively verifies
//! only ONE proof (the previous chain proof); the signatures add hashing, not
//! recursion. Proof size stays constant across the chain.

use anyhow::Result;
use plonky2::hash::hash_types::HashOut;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::config::Hasher;
use plonky2::plonk::proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget};

use crate::pq_sig::{
    add_signature_targets, set_signature, verify_signature, Signature, SigTargets,
};
use crate::types::{C, D, F};

const COMMITMENT_LEN: usize = 4;

/// Host-side transition digest (256-bit), matching the in-circuit hash.
pub fn transition_digest(old_pk: F, new_pk: F, prev_commitment: &HashOut<F>) -> [F; 4] {
    let mut inputs = vec![old_pk, new_pk];
    inputs.extend_from_slice(&prev_commitment.elements);
    PoseidonHash::hash_no_pad(&inputs).elements
}

pub struct ReplaceWitness<'a> {
    pub prev_proof: &'a ProofWithPublicInputs<F, C, D>,
    pub prev_slots: Vec<F>,
    pub new_slots: Vec<F>,
    pub replace_idx: usize,
    pub old_pk: F,
    pub new_pk: F,
    pub signatures: Vec<Signature>,
    pub signer_idxs: Vec<usize>,
}

pub struct ReplaceCircuit {
    pub data: CircuitData<F, C, D>,
    n: usize,
    threshold: usize,
    prev_proof: ProofWithPublicInputsTarget<D>,
    prev_keys: Vec<Target>,
    new_keys: Vec<Target>,
    replace_sel: Vec<BoolTarget>,
    old_pk: Target,
    new_pk: Target,
    sigs: Vec<SigTargets>,
    signer_sels: Vec<Vec<BoolTarget>>,
}

impl ReplaceCircuit {
    pub fn build(prev: &CircuitData<F, C, D>, n: usize, threshold: usize) -> Self {
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
        let zero = builder.zero();
        let one = builder.one();

        // (1) Recursively verify the previous chain proof (the only recursion).
        let prev_proof = builder.add_virtual_proof_with_pis(&prev.common);
        let prev_vd = builder.constant_verifier_data(&prev.verifier_only);
        builder.verify_proof::<C>(&prev_proof, &prev_vd, &prev.common);

        let prev_keys = builder.add_virtual_targets(n);
        let new_keys = builder.add_virtual_targets(n);
        let old_pk = builder.add_virtual_target();
        let new_pk = builder.add_virtual_target();

        // (2) Bind prev_keys to the commitment the previous proof asserts.
        let computed_prev = builder.hash_n_to_hash_no_pad::<PoseidonHash>(prev_keys.clone());
        for j in 0..COMMITMENT_LEN {
            builder.connect(computed_prev.elements[j], prev_proof.public_inputs[j]);
        }

        // (3) Replacement: exactly one slot goes old_pk -> new_pk.
        let replace_sel = one_hot(&mut builder, n);
        let sel_old = selected_value(&mut builder, &replace_sel, &prev_keys);
        builder.connect(sel_old, old_pk);
        for j in 0..n {
            let delta = builder.sub(new_pk, prev_keys[j]);
            let sd = builder.mul(replace_sel[j].target, delta);
            let expected = builder.add(prev_keys[j], sd);
            builder.connect(new_keys[j], expected);
        }

        // (4) Transition message digest -> 256 bits.
        let mut digest_inputs = vec![old_pk, new_pk];
        for j in 0..COMMITMENT_LEN {
            digest_inputs.push(prev_proof.public_inputs[j]);
        }
        let digest = builder.hash_n_to_hash_no_pad::<PoseidonHash>(digest_inputs);
        let mut msg_bits: Vec<BoolTarget> = Vec::with_capacity(256);
        for j in 0..COMMITMENT_LEN {
            msg_bits.extend(builder.split_le(digest.elements[j], 64));
        }

        // (5) Threshold signatures from distinct current members.
        let mut sigs = Vec::with_capacity(threshold);
        let mut signer_sels = Vec::with_capacity(threshold);
        let mut usage: Vec<Target> = vec![zero; n];
        for _ in 0..threshold {
            let ssel = one_hot(&mut builder, n);
            let signer_pk = selected_value(&mut builder, &ssel, &prev_keys);
            let s = add_signature_targets(&mut builder);
            verify_signature(&mut builder, signer_pk, &msg_bits, &s);
            for j in 0..n {
                usage[j] = builder.add(usage[j], ssel[j].target);
            }
            sigs.push(s);
            signer_sels.push(ssel);
        }
        for u in &usage {
            let um1 = builder.sub(*u, one);
            let prod = builder.mul(*u, um1);
            builder.connect(prod, zero);
        }

        // (6) New commitment is the public output.
        let new_commitment = builder.hash_n_to_hash_no_pad::<PoseidonHash>(new_keys.clone());
        builder.register_public_inputs(&new_commitment.elements);

        let data = builder.build::<C>();
        Self {
            data,
            n,
            threshold,
            prev_proof,
            prev_keys,
            new_keys,
            replace_sel,
            old_pk,
            new_pk,
            sigs,
            signer_sels,
        }
    }

    pub fn prove(&self, w: &ReplaceWitness) -> Result<ProofWithPublicInputs<F, C, D>> {
        assert_eq!(w.prev_slots.len(), self.n);
        assert_eq!(w.new_slots.len(), self.n);
        assert_eq!(w.signatures.len(), self.threshold);
        assert_eq!(w.signer_idxs.len(), self.threshold);

        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&self.prev_proof, w.prev_proof)?;
        for (t, v) in self.prev_keys.iter().zip(&w.prev_slots) {
            pw.set_target(*t, *v)?;
        }
        for (t, v) in self.new_keys.iter().zip(&w.new_slots) {
            pw.set_target(*t, *v)?;
        }
        pw.set_target(self.old_pk, w.old_pk)?;
        pw.set_target(self.new_pk, w.new_pk)?;
        set_one_hot(&mut pw, &self.replace_sel, w.replace_idx)?;
        for k in 0..self.threshold {
            set_signature(&mut pw, &self.sigs[k], &w.signatures[k])?;
            set_one_hot(&mut pw, &self.signer_sels[k], w.signer_idxs[k])?;
        }
        self.data.prove(pw)
    }
}

fn one_hot(builder: &mut CircuitBuilder<F, D>, n: usize) -> Vec<BoolTarget> {
    let sel: Vec<BoolTarget> = (0..n).map(|_| builder.add_virtual_bool_target_safe()).collect();
    let one = builder.one();
    let mut sum = builder.zero();
    for b in &sel {
        sum = builder.add(sum, b.target);
    }
    builder.connect(sum, one);
    sel
}

fn selected_value(builder: &mut CircuitBuilder<F, D>, sel: &[BoolTarget], values: &[Target]) -> Target {
    let mut acc = builder.zero();
    for (s, v) in sel.iter().zip(values) {
        let prod = builder.mul(s.target, *v);
        acc = builder.add(acc, prod);
    }
    acc
}

fn set_one_hot(pw: &mut PartialWitness<F>, sel: &[BoolTarget], idx: usize) -> Result<()> {
    for (j, b) in sel.iter().enumerate() {
        pw.set_bool_target(*b, j == idx)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chain::BaseCircuit;
    use crate::keyset::KeySet;
    use crate::pq_sig::{message_bits, MemberKey};

    #[test]
    fn pq_signed_replacement_roundtrip() -> Result<()> {
        const N: usize = 3;
        const T: usize = 2;

        let base = BaseCircuit::build(N);
        let replace = ReplaceCircuit::build(&base.data, N, T);

        let mut members: Vec<MemberKey> = (0..N as u64).map(MemberKey::keygen).collect();
        let mut set = KeySet::from_field_keys(N, members.iter().map(|m| m.public_key()));

        let p0 = base.prove(&set.padded())?;

        let prev_slots = set.padded();
        let prev_commitment = set.commitment();
        let old_pk = prev_slots[2];
        let new_member = MemberKey::keygen(42);
        let new_pk = new_member.public_key();
        let bits = message_bits(&transition_digest(old_pk, new_pk, &prev_commitment));

        // Members 0 and 1 certify the replacement of slot 2.
        let signatures = vec![members[0].sign(&bits), members[1].sign(&bits)];
        set.replace(old_pk, new_pk).unwrap();
        members[2] = new_member;

        let w = ReplaceWitness {
            prev_proof: &p0,
            prev_slots,
            new_slots: set.padded(),
            replace_idx: 2,
            old_pk,
            new_pk,
            signatures,
            signer_idxs: vec![0, 1],
        };
        let proof = replace.prove(&w)?;
        replace.data.verify(proof.clone())?;
        assert_eq!(proof.public_inputs[..4], set.commitment().elements);
        Ok(())
    }
}
