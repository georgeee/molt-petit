//! **ES256** — ECDSA over NIST P-256 / secp256r1 (COSE alg −7), the passkey /
//! FIDO2 / WebAuthn signature — verified inside a **plonky2** circuit
//! (Goldilocks / Poseidon), the classical counterpart to the post-quantum XMSS
//! path. This is the plonky2 sibling of the Plonky3 implementation in
//! `rust-keyrot-p3/src/p256/`, built so the two stacks can be benchmarked
//! apples-to-apples.
//!
//! P-256 is a 256-bit prime-field curve, far larger than the 64-bit Goldilocks
//! field plonky2 proves over, so every field element is emulated as limbs and
//! arithmetic is schoolbook multiply + witnessed quotient/remainder +
//! range-checked carry propagation ([`circuit`]). Goldilocks' 64-bit width lets
//! us use **B=26-bit limbs, K=10 limbs** (vs KoalaBear's B=11/K=24), so a
//! `mulmod` is only `K²=100` partial products.
//!
//! Scope: verify a signature given its message hash `z` (a public input). SHA-256
//! is not computed in-circuit (a separate, comparatively small add-on).

pub mod native;
pub mod circuit;
