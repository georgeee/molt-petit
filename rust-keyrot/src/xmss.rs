//! XMSS over Poseidon: a single Merkle tree of height `h` whose `2^h` leaves are
//! WOTS+ public keys. This is the *stateful, single-tree* hash-based signature —
//! exactly SPHINCS+ (`crate::sphincs`) with the FORS layer and the multi-layer
//! hypertree removed (`d = 1`, no FORS). It reuses the **same** Poseidon WOTS+,
//! Merkle, and in-circuit gadgets as `sphincs`, so an in-circuit comparison of
//! the two isolates the structural difference (single tree vs. FORS + hypertree)
//! rather than implementation noise.
//!
//! A signature is one WOTS+ signature on the message digest plus the `h`-element
//! authentication path of the used leaf; the public key is the tree root.
//! Verification recomputes the WOTS+ public key, hashes it into the leaf, climbs
//! the auth path, and compares to the root. Stateful: each leaf signs once (for
//! benchmarking we sign with an explicit leaf index).

use plonky2::field::types::Field;
use plonky2::hash::hash_types::HashOutTarget;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::proof::ProofWithPublicInputs;

use crate::sphincs::{
    add_dig, auth_path, build_subtree, cclimb, chf, cwots_pk_from_sig, hf, merkle_climb,
    wots_pk_from_sig, wots_sign, Dig, Params,
};
use crate::types::{C, D, F};

/// Compress the 256-bit message digest to the `n_fe`-element value WOTS+ signs.
fn msg_of(digest: &[F; 4], n_fe: usize) -> Dig {
    hf(digest, n_fe)
}

#[derive(Clone)]
pub struct Sig {
    pub wots_sig: Vec<Dig>,
    pub auth: Vec<Dig>,
    pub leaf: u64,
}

pub struct Key {
    seed: Vec<F>,
    layers: Vec<Vec<Dig>>,
    pk: Dig,
    pub p: Params,
}

impl Key {
    /// Build the whole tree (all `2^h` WOTS+ leaves, in parallel) and keep it so
    /// signing is cheap. Feasible only for modest `h` — that is XMSS's nature.
    pub fn keygen(p: Params, seed_u64: u64) -> Self {
        let seed: Vec<F> =
            (0..p.n_fe).map(|i| F::from_canonical_u64(seed_u64 ^ (0x5555 * i as u64 + 1))).collect();
        let layers = build_subtree(&seed, 0, 0, &p);
        let pk = layers.last().unwrap()[0].clone();
        Self { seed, layers, pk, p }
    }

    pub fn public_key(&self) -> Dig {
        self.pk.clone()
    }

    pub fn sign(&self, digest: &[F; 4], leaf: u64) -> Sig {
        let p = &self.p;
        let msg = msg_of(digest, p.n_fe);
        let wots_sig = wots_sign(&self.seed, 0, 0, leaf, &msg, p);
        let auth = auth_path(&self.layers, leaf as usize);
        Sig { wots_sig, auth, leaf }
    }
}

/// Native verification (mirrors the in-circuit logic).
pub fn verify(pk: &[F], digest: &[F; 4], sig: &Sig, p: &Params) -> bool {
    let msg = msg_of(digest, p.n_fe);
    let wpk = wots_pk_from_sig(&sig.wots_sig, &msg, p);
    let root = merkle_climb(wpk, &sig.auth, sig.leaf as usize, p.n_fe);
    root == pk
}

// ===================== In-circuit verification =====================

pub struct SigTargets {
    pub wots_sig: Vec<Vec<Target>>,
    pub auth: Vec<Vec<Target>>,
    pub leaf_bits: Vec<BoolTarget>,
}

pub fn add_signature_targets(builder: &mut CircuitBuilder<F, D>, p: &Params) -> SigTargets {
    let n = p.n_fe;
    SigTargets {
        wots_sig: (0..p.len).map(|_| add_dig(builder, n)).collect(),
        auth: (0..p.sub_h).map(|_| add_dig(builder, n)).collect(),
        leaf_bits: (0..p.sub_h).map(|_| builder.add_virtual_bool_target_safe()).collect(),
    }
}

pub fn verify_signature(
    builder: &mut CircuitBuilder<F, D>,
    pk: &[Target],
    digest: HashOutTarget,
    s: &SigTargets,
    p: &Params,
) {
    let msg = chf(builder, digest.elements.to_vec(), p.n_fe);
    let wpk = cwots_pk_from_sig(builder, &s.wots_sig, &msg, p);
    let cur = cclimb(builder, wpk, &s.auth, &s.leaf_bits, p.n_fe);
    for i in 0..p.n_fe {
        builder.connect(cur[i], pk[i]);
    }
}

pub fn set_signature(pw: &mut PartialWitness<F>, s: &SigTargets, sig: &Sig) -> anyhow::Result<()> {
    let set = |pw: &mut PartialWitness<F>, t: &[Target], v: &[F]| -> anyhow::Result<()> {
        for (ti, vi) in t.iter().zip(v) {
            pw.set_target(*ti, *vi)?;
        }
        Ok(())
    };
    for i in 0..s.wots_sig.len() {
        set(pw, &s.wots_sig[i], &sig.wots_sig[i])?;
    }
    for i in 0..s.auth.len() {
        set(pw, &s.auth[i], &sig.auth[i])?;
    }
    for (j, b) in s.leaf_bits.iter().enumerate() {
        pw.set_bool_target(*b, (sig.leaf >> j) & 1 == 1)?;
    }
    Ok(())
}

use plonky2::field::types::PrimeField64;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::Hasher;

pub fn sig_digest(sig: &Sig, p: &Params) -> [u64; 4] {
    let mut elements = Vec::new();
    for w in &sig.wots_sig {
        elements.extend_from_slice(w);
    }
    for a in &sig.auth {
        elements.extend_from_slice(a);
    }
    for j in 0..p.sub_h {
        elements.push(F::from_canonical_u64((sig.leaf >> j) & 1));
    }
    let d = PoseidonHash::hash_no_pad(&elements).elements;
    [
        d[0].to_canonical_u64(),
        d[1].to_canonical_u64(),
        d[2].to_canonical_u64(),
        d[3].to_canonical_u64(),
    ]
}

pub struct VerifierCircuit {
    pub data: CircuitData<F, C, D>,
    pk: Vec<Target>,
    digest: [Target; 4],
    sig: SigTargets,
    pub p: Params,
}

impl VerifierCircuit {
    pub fn build(p: Params) -> Self {
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
        let pk = builder.add_virtual_targets(p.n_fe);
        let digest = [
            builder.add_virtual_target(),
            builder.add_virtual_target(),
            builder.add_virtual_target(),
            builder.add_virtual_target(),
        ];
        let sig = add_signature_targets(&mut builder, &p);
        verify_signature(&mut builder, &pk, HashOutTarget { elements: digest }, &sig, &p);
        let mut sig_targets = Vec::new();
        for w in &sig.wots_sig {
            sig_targets.extend_from_slice(w);
        }
        for a in &sig.auth {
            sig_targets.extend_from_slice(a);
        }
        for b in &sig.leaf_bits {
            sig_targets.push(b.target);
        }
        let sig_digest = builder.hash_n_to_hash_no_pad::<PoseidonHash>(sig_targets);
        builder.register_public_inputs(&pk);
        builder.register_public_inputs(&digest);
        builder.register_public_inputs(&sig_digest.elements);
        let data = builder.build::<C>();
        Self { data, pk, digest, sig, p }
    }

    pub fn prove(
        &self,
        pk: &[F],
        digest: &[F; 4],
        sig: &Sig,
    ) -> anyhow::Result<ProofWithPublicInputs<F, C, D>> {
        let mut pw = PartialWitness::new();
        for (t, v) in self.pk.iter().zip(pk) {
            pw.set_target(*t, *v)?;
        }
        for i in 0..4 {
            pw.set_target(self.digest[i], digest[i])?;
        }
        set_signature(&mut pw, &self.sig, sig)?;
        self.data.prove(pw)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use plonky2::hash::poseidon::PoseidonHash;
    use plonky2::plonk::config::Hasher;

    fn digest(a: u64, b: u64) -> [F; 4] {
        PoseidonHash::hash_no_pad(&[F::from_canonical_u64(a), F::from_canonical_u64(b)]).elements
    }

    #[test]
    fn host_roundtrip() {
        let p = Params::xmss("xmss-test", 2, 4);
        let key = Key::keygen(p.clone(), 7);
        let pk = key.public_key();
        for leaf in 0..(1u64 << p.sub_h) {
            let d = digest(leaf, 99);
            let sig = key.sign(&d, leaf);
            assert!(verify(&pk, &d, &sig, &p), "valid (leaf={leaf})");
            assert!(!verify(&pk, &digest(leaf + 1000, 99), &sig, &p), "wrong message");
        }
    }

    #[test]
    fn circuit_roundtrip_tiny() {
        let p = Params::xmss("xmss-test", 2, 3);
        let key = Key::keygen(p.clone(), 11);
        let pk = key.public_key();
        let circ = VerifierCircuit::build(p.clone());
        let d = digest(2, 99);
        let sig = key.sign(&d, 2);
        let proof = circ.prove(&pk, &d, &sig).expect("prove");
        circ.data.verify(proof).expect("verify");
    }
}
