//! Integration of the Molt Petit consensus (`molt_petit`) with a plonky2
//! signed key-rotation chain.
//!
//! * Hashing is **Poseidon** over Goldilocks throughout (block ids, payload
//!   commitments, signature/key material).
//! * Signatures are **Lamport-over-Poseidon** one-time signatures behind a
//!   small Merkle tree ("SPHINCS+ with Poseidon"-style; see [`pq_sig`]).
//! * Each consensus block's content is **one** signed key-rotation transition
//!   (`old_pk -> new_pk` in a fixed-capacity key set), and the block's
//!   `contents_hash` is the **Poseidon digest of that transition**.
//! * The certificates the consensus light-client layer checks are **plonky2
//!   recursive proofs** of the whole rotation history ([`pq_chain`]).
//!
//! The consensus protocol itself is reused verbatim from the `molt_petit`
//! crate (the Rust reference that is mechanically extracted to Lean); this
//! crate only supplies a concrete [`crypto::KeyRotCrypto`] dictionary and a
//! driver ([`bin/keyrot_demo`](../keyrot_demo/index.html)).

pub mod backend;
pub mod chain;
pub mod es256;
pub mod crypto;
pub mod keyset;
pub mod mp_circuit;
pub mod pok;
pub mod poseidon_util;
pub mod pq_chain;
pub mod pq_sig;
pub mod spec;
pub mod sphincs;
pub mod types;
pub mod xmss;
