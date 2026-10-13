//! The bridge between the consensus's opaque 256-bit [`Hash`] (four `u64`
//! limbs) and plonky2's Poseidon world (`[F; 4]` digests over Goldilocks).
//!
//! Every `Hash` that flows through the integration is produced *here* from a
//! Poseidon digest (block ids, payload commitments) or holds a single field
//! element in its low limb (public keys), so the limbs are always canonical
//! field elements and the round-trips are exact.

use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::Hasher;

use molt_petit::{Block, Hash};

use crate::types::F;

/// Poseidon hash to a 256-bit digest (four field elements).
pub fn poseidon4(inputs: &[F]) -> [F; 4] {
    PoseidonHash::hash_no_pad(inputs).elements
}

/// Public key of a secret key: `pk = Poseidon(sk)[0]`. A "signature" in this
/// integration is a plonky2 proof of knowledge of the `sk` behind `pk` (no
/// dedicated signature scheme). The low limb is used so a key is a single field
/// element, matching the key-set representation.
pub fn pk_of(sk: F) -> F {
    poseidon4(&[sk])[0]
}

/// A Poseidon digest as the consensus's 256-bit `Hash`.
pub fn digest_to_hash(d: [F; 4]) -> Hash {
    Hash {
        a: d[0].to_canonical_u64(),
        b: d[1].to_canonical_u64(),
        c: d[2].to_canonical_u64(),
        d: d[3].to_canonical_u64(),
    }
}

/// The four field elements packed in a `Hash` (inverse of `digest_to_hash`).
pub fn hash_to_digest(h: &Hash) -> [F; 4] {
    [
        F::from_canonical_u64(h.a),
        F::from_canonical_u64(h.b),
        F::from_canonical_u64(h.c),
        F::from_canonical_u64(h.d),
    ]
}

/// A single field element (a member's Merkle-root public key) as a `Hash`,
/// stored in the low limb.
pub fn pk_to_hash(pk: F) -> Hash {
    Hash {
        a: pk.to_canonical_u64(),
        b: 0,
        c: 0,
        d: 0,
    }
}

/// Recover the field-element public key from its `Hash` handle.
pub fn hash_to_pk(h: &Hash) -> F {
    F::from_canonical_u64(h.a)
}

/// A participant's secret-key *handle*: just its index, in the low limb. The
/// real secret lives in the `Crypto` dictionary; the protocol only passes this
/// opaque handle around.
pub fn sk_handle(i: u64) -> Hash {
    Hash {
        a: i,
        b: 0,
        c: 0,
        d: 0,
    }
}

pub fn sk_index(h: &Hash) -> u64 {
    h.a
}

/// Deterministic Poseidon block id over the block's fields. (`prev = None` at
/// genesis is hashed as the zero digest.)
pub fn block_id(slot: u64, height: u64, prev: Option<&Hash>, contents: &Hash) -> Hash {
    let mut xs = vec![F::from_canonical_u64(slot), F::from_canonical_u64(height)];
    match prev {
        Some(p) => xs.extend_from_slice(&hash_to_digest(p)),
        None => xs.extend_from_slice(&[F::ZERO; 4]),
    }
    xs.extend_from_slice(&hash_to_digest(contents));
    digest_to_hash(poseidon4(&xs))
}

/// Deterministic Poseidon block id for a fold block over 12 canonical Goldilocks field elements:
/// `[slot, height, has_prev as 0/1, prev[0..4], contents_hash[0..4], key_index]`.
pub fn fold_block_id(
    slot: u64,
    height: u64,
    has_prev: bool,
    prev: [u64; 4],
    contents_hash: [u64; 4],
    key_index: u64,
) -> [u64; 4] {
    let inputs = [
        F::from_canonical_u64(slot),
        F::from_canonical_u64(height),
        F::from_canonical_u64(if has_prev { 1 } else { 0 }),
        F::from_canonical_u64(prev[0]),
        F::from_canonical_u64(prev[1]),
        F::from_canonical_u64(prev[2]),
        F::from_canonical_u64(prev[3]),
        F::from_canonical_u64(contents_hash[0]),
        F::from_canonical_u64(contents_hash[1]),
        F::from_canonical_u64(contents_hash[2]),
        F::from_canonical_u64(contents_hash[3]),
        F::from_canonical_u64(key_index),
    ];
    let digest = PoseidonHash::hash_no_pad(&inputs).elements;
    [
        digest[0].to_canonical_u64(),
        digest[1].to_canonical_u64(),
        digest[2].to_canonical_u64(),
        digest[3].to_canonical_u64(),
    ]
}

/// The 256-bit message a block-producer signature commits to: a Poseidon digest
/// over the block's slot, height, id and payload commitment. Deterministic from
/// the block, so the verifier recomputes the same message.
pub fn block_signing_digest(b: &Block) -> [F; 4] {
    let mut xs = vec![
        F::from_canonical_u64(b.slot),
        F::from_canonical_u64(b.height),
    ];
    xs.extend_from_slice(&hash_to_digest(&b.id));
    xs.extend_from_slice(&hash_to_digest(&b.contents_hash));
    poseidon4(&xs)
}

