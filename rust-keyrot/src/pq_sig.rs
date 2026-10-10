//! A quantum-secure, fast-to-sign signature: Lamport one-time signatures over
//! Poseidon, made many-time with a small Merkle tree (an XMSS-style scheme).
//!
//! Why this fits the requirements:
//! * **Post-quantum** — security reduces to Poseidon preimage/collision
//!   resistance; no elliptic curves, no number theory (Grover-only speedups).
//! * **Fastest possible signing** — a Lamport signature is just *revealing
//!   pre-stored secret values*; there is essentially no computation at sign
//!   time (orders of magnitude cheaper than producing a Plonky2 proof).
//! * **Verification is the heavy side**, done later inside the recursive
//!   circuit — pure Poseidon hashing, which is cheap in Plonky2.
//! * **No zero-knowledge needed** — the signature blob (opened preimages, the
//!   unopened public halves, the Merkle auth path) is revealed as witness.
//! * **Many-time** — a member's public key is a Merkle root over `LEAVES`
//!   one-time keys, so each member can sign `LEAVES` times.
//!
//! Parameters below sign a 256-bit digest (4 Goldilocks elements). This is a
//! prototype: a production scheme would use Winternitz chains to shrink the
//! ~512-element-per-signature blob, and track used leaves to prevent reuse.

use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::config::Hasher;

use crate::types::{D, F};

/// Message digest width in bits (4 field elements).
pub const MSG_BITS: usize = 256;
/// Merkle tree depth; a member can sign `2^TREE_DEPTH` times. Raised to 3 (8
/// one-time keys) from the prototype's 2, so a consensus participant has enough
/// one-time signatures to both produce several blocks and co-sign several
/// key-rotation transitions across a run.
pub const TREE_DEPTH: usize = 3;
/// One-time keys per member.
pub const LEAVES: usize = 1 << TREE_DEPTH;

fn h1(x: F) -> F {
    PoseidonHash::hash_no_pad(&[x]).elements[0]
}
fn hash_many(xs: &[F]) -> F {
    PoseidonHash::hash_no_pad(xs).elements[0]
}
fn compress(a: F, b: F) -> F {
    PoseidonHash::hash_no_pad(&[a, b]).elements[0]
}
fn prf(seed: F, leaf: u64, i: u64, b: u64) -> F {
    hash_many(&[
        seed,
        F::from_canonical_u64(leaf),
        F::from_canonical_u64(i),
        F::from_canonical_u64(b),
    ])
}

/// Little-endian bits of a 256-bit digest (4 field elements, 64 bits each).
pub fn message_bits(digest: &[F; 4]) -> Vec<bool> {
    let mut bits = Vec::with_capacity(MSG_BITS);
    for d in digest {
        let v = d.to_canonical_u64();
        for j in 0..64 {
            bits.push((v >> j) & 1 == 1);
        }
    }
    bits
}

/// A signature blob (revealed alongside the transition; not secret).
#[derive(Clone)]
pub struct Signature {
    pub idx: usize,
    pub sig: Vec<F>,   // opened preimages, one per message bit
    pub other: Vec<F>, // unopened public halves, one per message bit
    pub auth: Vec<F>,  // Merkle authentication path
}

/// A member's many-time key (LEAVES Lamport one-time keys under a Merkle root).
pub struct MemberKey {
    ots_secret: Vec<Vec<[F; 2]>>, // [leaf][bit] -> (sk0, sk1)
    ots_public: Vec<Vec<[F; 2]>>, // [leaf][bit] -> (pk0, pk1)
    layers: Vec<Vec<F>>,          // Merkle layers, layers[0] = leaves
    next: usize,
}

impl MemberKey {
    pub fn keygen(seed: u64) -> Self {
        let seed = F::from_canonical_u64(seed);
        let mut ots_secret = Vec::with_capacity(LEAVES);
        let mut ots_public = Vec::with_capacity(LEAVES);
        let mut leaves = Vec::with_capacity(LEAVES);
        for leaf in 0..LEAVES {
            let mut sk = Vec::with_capacity(MSG_BITS);
            let mut pk = Vec::with_capacity(MSG_BITS);
            let mut flat_pub = Vec::with_capacity(MSG_BITS * 2);
            for i in 0..MSG_BITS {
                let s0 = prf(seed, leaf as u64, i as u64, 0);
                let s1 = prf(seed, leaf as u64, i as u64, 1);
                let (p0, p1) = (h1(s0), h1(s1));
                sk.push([s0, s1]);
                pk.push([p0, p1]);
                flat_pub.push(p0);
                flat_pub.push(p1);
            }
            leaves.push(hash_many(&flat_pub));
            ots_secret.push(sk);
            ots_public.push(pk);
        }
        let layers = build_tree(leaves);
        Self {
            ots_secret,
            ots_public,
            layers,
            next: 0,
        }
    }

    /// The member's public key (the Merkle root), stored in the set slot.
    pub fn public_key(&self) -> F {
        *self.layers.last().unwrap().first().unwrap()
    }

    /// Sign a message (its 256 bits). Uses the next unused one-time leaf.
    /// This is just revealing stored values — essentially free.
    pub fn sign(&mut self, msg_bits: &[bool]) -> Signature {
        assert_eq!(msg_bits.len(), MSG_BITS);
        let idx = self.next;
        assert!(idx < LEAVES, "member exhausted its {LEAVES} one-time keys");
        self.next += 1;

        let sk = &self.ots_secret[idx];
        let pk = &self.ots_public[idx];
        let mut sig = Vec::with_capacity(MSG_BITS);
        let mut other = Vec::with_capacity(MSG_BITS);
        for i in 0..MSG_BITS {
            let b = msg_bits[i] as usize;
            sig.push(sk[i][b]);
            other.push(pk[i][1 - b]);
        }
        Signature {
            idx,
            sig,
            other,
            auth: auth_path(&self.layers, idx),
        }
    }
}

fn build_tree(leaves: Vec<F>) -> Vec<Vec<F>> {
    let mut layers = vec![leaves];
    while layers.last().unwrap().len() > 1 {
        let prev = layers.last().unwrap();
        let next: Vec<F> = prev.chunks(2).map(|c| compress(c[0], c[1])).collect();
        layers.push(next);
    }
    layers
}

fn auth_path(layers: &[Vec<F>], mut idx: usize) -> Vec<F> {
    let mut path = Vec::with_capacity(layers.len() - 1);
    for level in &layers[..layers.len() - 1] {
        path.push(level[idx ^ 1]);
        idx >>= 1;
    }
    path
}

// ----- In-circuit verification -----

pub struct SigTargets {
    pub sig: Vec<Target>,
    pub other: Vec<Target>,
    pub auth: Vec<Target>,
    pub idx_bits: Vec<BoolTarget>,
}

pub fn add_signature_targets(builder: &mut CircuitBuilder<F, D>) -> SigTargets {
    SigTargets {
        sig: builder.add_virtual_targets(MSG_BITS),
        other: builder.add_virtual_targets(MSG_BITS),
        auth: builder.add_virtual_targets(TREE_DEPTH),
        idx_bits: (0..TREE_DEPTH)
            .map(|_| builder.add_virtual_bool_target_safe())
            .collect(),
    }
}

/// Verify `s` is a valid signature on `msg_bits` under public key `member_pk`.
pub fn verify_signature(
    builder: &mut CircuitBuilder<F, D>,
    member_pk: Target,
    msg_bits: &[BoolTarget],
    s: &SigTargets,
) {
    debug_assert_eq!(msg_bits.len(), MSG_BITS);

    // Reconstruct the one-time public key from the opened preimages.
    let mut pubs = Vec::with_capacity(MSG_BITS * 2);
    for i in 0..MSG_BITS {
        let opened = builder
            .hash_n_to_hash_no_pad::<PoseidonHash>(vec![s.sig[i]])
            .elements[0];
        // If bit==0 the opened half is pub0; if bit==1 it is pub1.
        let pub0 = builder.select(msg_bits[i], s.other[i], opened);
        let pub1 = builder.select(msg_bits[i], opened, s.other[i]);
        pubs.push(pub0);
        pubs.push(pub1);
    }
    let leaf = builder.hash_n_to_hash_no_pad::<PoseidonHash>(pubs).elements[0];

    // Walk the Merkle authentication path up to the root.
    let mut cur = leaf;
    for level in 0..TREE_DEPTH {
        let sib = s.auth[level];
        let bit = s.idx_bits[level];
        let left = builder.select(bit, sib, cur);
        let right = builder.select(bit, cur, sib);
        cur = builder
            .hash_n_to_hash_no_pad::<PoseidonHash>(vec![left, right])
            .elements[0];
    }
    builder.connect(cur, member_pk);
}

pub fn set_signature(
    pw: &mut PartialWitness<F>,
    s: &SigTargets,
    sig: &Signature,
) -> anyhow::Result<()> {
    for i in 0..MSG_BITS {
        pw.set_target(s.sig[i], sig.sig[i])?;
        pw.set_target(s.other[i], sig.other[i])?;
    }
    for l in 0..TREE_DEPTH {
        pw.set_target(s.auth[l], sig.auth[l])?;
        pw.set_bool_target(s.idx_bits[l], (sig.idx >> l) & 1 == 1)?;
    }
    Ok(())
}

// ----- Native (off-circuit) verification -----

/// Plain-Rust verification, mirroring [`verify_signature`] exactly (reconstruct
/// the one-time public key from the opened preimages, hash to the leaf, walk the
/// Merkle authentication path, compare to `member_pk`).
///
/// The recursive circuit verifies the *transition* signatures by hashing inside
/// the proof; the consensus layer needs a `bool`-returning verifier for the
/// *block-producer* signatures it carries in the signed suffix, which is this.
pub fn verify_native(member_pk: F, msg_bits: &[bool], s: &Signature) -> bool {
    if msg_bits.len() != MSG_BITS
        || s.sig.len() != MSG_BITS
        || s.other.len() != MSG_BITS
        || s.auth.len() != TREE_DEPTH
    {
        return false;
    }

    // Reconstruct the one-time public key from the opened preimages.
    let mut pubs = Vec::with_capacity(MSG_BITS * 2);
    for i in 0..MSG_BITS {
        let opened = h1(s.sig[i]);
        // If bit==0 the opened half is pub0; if bit==1 it is pub1.
        let (pub0, pub1) = if msg_bits[i] {
            (s.other[i], opened)
        } else {
            (opened, s.other[i])
        };
        pubs.push(pub0);
        pubs.push(pub1);
    }
    let leaf = hash_many(&pubs);

    // Walk the Merkle authentication path up to the root.
    let mut cur = leaf;
    for level in 0..TREE_DEPTH {
        let bit = (s.idx >> level) & 1 == 1;
        let sib = s.auth[level];
        let (left, right) = if bit { (sib, cur) } else { (cur, sib) };
        cur = compress(left, right);
    }
    cur == member_pk
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_verify_roundtrip_and_rejects_tampering() {
        let mut member = MemberKey::keygen(7);
        let pk = member.public_key();
        let digest = [
            F::from_canonical_u64(1),
            F::from_canonical_u64(2),
            F::from_canonical_u64(3),
            F::from_canonical_u64(4),
        ];
        let bits = message_bits(&digest);
        let sig = member.sign(&bits);
        assert!(verify_native(pk, &bits, &sig));

        // Wrong public key is rejected.
        let other = MemberKey::keygen(8).public_key();
        assert!(!verify_native(other, &bits, &sig));

        // A flipped message bit is rejected.
        let mut bad_bits = bits.clone();
        bad_bits[0] = !bad_bits[0];
        assert!(!verify_native(pk, &bad_bits, &sig));

        // A tampered opened preimage is rejected.
        let mut bad_sig = sig.clone();
        bad_sig.sig[0] = bad_sig.sig[0] + F::ONE;
        assert!(!verify_native(pk, &bits, &bad_sig));
    }
}
