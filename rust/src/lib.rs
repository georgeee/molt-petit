//! Molt Petit — Rust reference implementation of the consensus protocol.
//!
//! The Rust analogue of `moltPetit.ts`, written in the fragment of Rust that
//! Charon + Aeneas translate to Lean 4. The *validator* functions mirror the
//! TypeScript reference check-for-check (`valid_chain`,
//! `validate_certified_chain`); block production (`produce_block`,
//! `produce_block_cert`) is deliberately narrower — this crate omits
//! compaction (`produce_block_cert` does no compaction) and chain selection
//! (there is no `select_chain`). The two references also differ in signature
//! preimage scope: TS verifies over `(slot, height, prev, id)` with `keyIndex`
//! bound via the id, while Rust signs the whole `Block`.
//!
//! Cryptographic material — block ids, payload commitments, signatures, keys,
//! certificates — is at least 32 bytes wide in practice, so it is represented
//! by `Hash` (256 bits = four `u64` limbs), never a bare `u64`. Equality is
//! limb-wise primitive `u64` equality (`hash_eq`), which keeps the Aeneas
//! extraction free of opaque `axiom`s (deriving `PartialEq` would emit one).
//!
//! Signatures/keys/certificates are opaque: the protocol never inspects them,
//! it only passes them to the injected `Crypto` dictionary (a Rust trait — the
//! analogue of TypeScript's `SigOps`/`CertOps` records).
//@ [lean] subdir=MoltPetit

// ---------------------------------------------------------------------------
// 256-bit opaque values (hashes, ids, and re-used as crypto handles)
// ---------------------------------------------------------------------------

/// A 256-bit (32-byte) value: block ids and payload commitments. Four `u64`
/// limbs; `Copy` so it can be returned by value from the tip helpers.
#[derive(Clone, Copy)]
pub struct Hash {
    pub a: u64,
    pub b: u64,
    pub c: u64,
    pub d: u64,
}

/// Hash equality, limb-wise (primitive `u64` `==`, no `PartialEq` axiom).
pub fn hash_eq(x: &Hash, y: &Hash) -> bool {
    x.a == y.a && x.b == y.b && x.c == y.c && x.d == y.d
}

// ---------------------------------------------------------------------------
// Blocks and chains
// ---------------------------------------------------------------------------

/// A block: slot, height, parent id (`None` at genesis), own id, and a
/// commitment to the payload (the algorithm never inspects the payload).
pub struct Block {
    pub slot: u64,
    pub height: u64,
    pub prev: Option<Hash>,
    pub id: Hash,
    pub contents_hash: Hash,
    /// The per-producer delegate-key index this block signed under
    /// (consensus-maintained in-band key rotation). The verifier selects the
    /// public key as `key_for(producer_for_slot(n, slot), key_index)`. See
    /// `MoltPetit/Model/KeyIndex.lean` and `georgeee/mini-consensus-lean: KEY_INDEX_DESIGN.md`.
    pub key_index: u64,
}

/// A chain, lowest height first (genesis at the head), newest block last.
pub enum Chain {
    Nil,
    Cons(Block, Box<Chain>),
}

// ---------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------

/// Quorum: `ceil(2n/3)`, computed as `floor((2n + 2)/3)`. Written with `n + n`
/// rather than `2 * n` so the Lean extraction stays within the addition
/// fragment the equivalence bridge reasons about (same value).
pub fn quorum(n: u64) -> u64 {
    (n + n + 2) / 3
}

/// Byzantine budget per window: `floor((n - 1)/3)`.
pub fn max_byzantine(n: u64) -> u64 {
    (n - 1) / 3
}

/// Round-robin slot leader.
pub fn producer_for_slot(n: u64, slot: u64) -> u64 {
    slot % n
}

// ---------------------------------------------------------------------------
// Chain helpers
// ---------------------------------------------------------------------------

pub fn is_nil(c: &Chain) -> bool {
    match c {
        Chain::Nil => true,
        Chain::Cons(_, _) => false,
    }
}

/// Slot of the tip, starting from accumulator `cur`.
pub fn tip_slot_from(cur: u64, c: &Chain) -> u64 {
    match c {
        Chain::Nil => cur,
        Chain::Cons(b, tl) => tip_slot_from(b.slot, tl),
    }
}

/// Height of the tip, starting from accumulator `cur`.
pub fn tip_height_from(cur: u64, c: &Chain) -> u64 {
    match c {
        Chain::Nil => cur,
        Chain::Cons(b, tl) => tip_height_from(b.height, tl),
    }
}

/// Id of the tip, starting from accumulator `cur`.
pub fn tip_id_from(cur: Hash, c: &Chain) -> Hash {
    match c {
        Chain::Nil => cur,
        Chain::Cons(b, tl) => tip_id_from(b.id, tl),
    }
}

/// Append a single block at the end of the chain.
pub fn append_block(c: Chain, nb: Block) -> Chain {
    match c {
        Chain::Nil => Chain::Cons(nb, Box::new(Chain::Nil)),
        Chain::Cons(x, tl) => Chain::Cons(x, Box::new(append_block(*tl, nb))),
    }
}

/// Number of blocks of `c` whose slot lies in the window `[u, u + len)`.
pub fn window_count(c: &Chain, u: u64, len: u64) -> u64 {
    match c {
        Chain::Nil => 0,
        Chain::Cons(b, tl) => {
            let here = if u <= b.slot && b.slot < u + len { 1 } else { 0 };
            here + window_count(tl, u, len)
        }
    }
}

/// One window meets the quorum-density bound.
pub fn window_dense(n: u64, c: &Chain, u: u64) -> bool {
    quorum(n) <= window_count(c, u, n)
}

// ---------------------------------------------------------------------------
// Cumulative window density (anchored, with the slide lemma proved in Lean)
// ---------------------------------------------------------------------------

/// Density at every anchored window start `b.slot + 1` (for `b` in `rest`)
/// that is at least `lo` and has matured at tip slot `t`.
pub fn anchors_dense(all: &Chain, rest: &Chain, lo: u64, t: u64, n: u64) -> bool {
    match rest {
        Chain::Nil => true,
        Chain::Cons(b, tl) => {
            let u = b.slot + 1;
            let ok = if lo <= u && u + n <= t + 1 {
                window_dense(n, all, u)
            } else {
                true
            };
            ok && anchors_dense(all, tl, lo, t, n)
        }
    }
}

/// Every window `[u, u+n)` with `lo <= u` and `u + n <= t + 1` is dense.
pub fn matured_dense(c: &Chain, lo: u64, t: u64, n: u64) -> bool {
    let base = if lo + n <= t + 1 {
        window_dense(n, c, lo)
    } else {
        true
    };
    base && anchors_dense(c, c, lo, t, n)
}

// ---------------------------------------------------------------------------
// Structural validity
// ---------------------------------------------------------------------------

/// Structural validity of a genesis block: height 0, no parent.
pub fn genesis_ok(b: &Block) -> bool {
    b.height == 0 && b.prev.is_none()
}

/// `child` is the immediate successor of `parent`. The parent-id match avoids
/// `PartialEq` on `Option` (which Aeneas would emit as an axiom).
pub fn child_ok(parent: &Block, child: &Block) -> bool {
    let prev_ok = match &child.prev {
        Some(p) => hash_eq(p, &parent.id),
        None => false,
    };
    child.height == parent.height + 1 && parent.slot < child.slot && prev_ok
}

/// Adjacent links from a parent through the rest of the chain.
fn links_from(parent: &Block, c: &Chain) -> bool {
    match c {
        Chain::Nil => true,
        Chain::Cons(b, tl) => child_ok(parent, b) && links_from(b, tl),
    }
}

/// Every adjacent pair of the chain satisfies `child_ok`.
pub fn links_ok(c: &Chain) -> bool {
    match c {
        Chain::Nil => true,
        Chain::Cons(a, tl) => links_from(a, tl),
    }
}

/// Full chain validation, replayed from genesis: the rule every participant
/// applies to every candidate chain. Verifies chains.
pub fn valid_chain(n: u64, c: &Chain) -> bool {
    match c {
        Chain::Nil => true,
        Chain::Cons(g, tl) => {
            let genesis = genesis_ok(g);
            let links = links_ok(c);
            let tip_slot = tip_slot_from(g.slot, tl);
            genesis && links && matured_dense(c, 0, tip_slot, n)
        }
    }
}

// ---------------------------------------------------------------------------
// Key-index validator (in-band key rotation)
//
// STATUS: extracted and BRIDGED. These functions are vendored into
// `Rust/Extracted.lean` (Charon 0.1.212 + Aeneas, toolchain bootstrapped at
// /work/aeneas-toolchain) and proved sound against the model:
// `Rust/Bridge.lean` `valid_chain_k_sound` and the corollary
// `Rust/Results_rust.lean` `rust_valid_chain_k_sound` (acceptance projects to
// the model's ValidChain ∧ KeyIndexMonotone; the ≤ in-force pin follows on
// full chains via `inForcePinned_of_validChainK`), guarded in
// `Rust/Axioms.lean`. `valid_chain_be` (the circuit backend) is deliberately
// NOT extended: the `Backend` trait lacks the needed comparisons, and widening
// it would break the verbatim `Equiv.lean` proof; so the circuit in
// `rust-keyrot/` checks no key indices (the paper's N2 limit, not yet closed).
// ---------------------------------------------------------------------------

/// Every block of `rest` produced by the same producer as `(n, slot)` declares
/// a key index at least `ki` — one block's half of the monotone rule against
/// all later blocks (two-function pattern, like `links_from`).
fn key_mono_against(n: u64, slot: u64, ki: u64, rest: &Chain) -> bool {
    match rest {
        Chain::Nil => true,
        Chain::Cons(b, tl) => {
            let ok = if producer_for_slot(n, slot) == producer_for_slot(n, b.slot) {
                ki <= b.key_index
            } else {
                true
            };
            ok && key_mono_against(n, slot, ki, tl)
        }
    }
}

/// The in-band monotone key-index rule (`KeyIndex.lean` `keyMonoOk`): along
/// the chain, a producer's declared key version never decreases. A rotation is
/// announced by signing under a higher index; this rule forbids any later
/// reversion to a rotated-out one. On a full chain it implies the `<=`
/// in-force pin (`KeyStealingCert.lean` `inForcePinned_of_validChainK`): no
/// block signs under a version below the one in force (Δconf-confirmed) at
/// its slot.
pub fn key_mono_ok(n: u64, c: &Chain) -> bool {
    match c {
        Chain::Nil => true,
        Chain::Cons(b, tl) => key_mono_against(n, b.slot, b.key_index, tl) && key_mono_ok(n, tl),
    }
}

/// The indexed validator (`KeyIndex.lean` `validChainK`): structural validity
/// and density plus the monotone key-index rule — the full-chain enforcement
/// of the key-rotation validator (`validChainK'` follows in the model).
pub fn valid_chain_k(n: u64, c: &Chain) -> bool {
    valid_chain(n, c) && key_mono_ok(n, c)
}

// ---------------------------------------------------------------------------
// Block production (plain chain)
// ---------------------------------------------------------------------------

/// Honest block production for `at_slot`: extend the chain by one new block
/// iff the slot belongs to `me`, the chain is non-empty, and the extension
/// passes full validation. Produces blocks.
pub fn produce_block(
    n: u64,
    me: u64,
    at_slot: u64,
    new_id: Hash,
    contents_hash: Hash,
    key_index: u64,
    c: Chain,
) -> Option<Chain> {
    if producer_for_slot(n, at_slot) != me {
        return None;
    }
    if is_nil(&c) {
        return None;
    }
    let th = tip_height_from(0, &c);
    let ti = tip_id_from(new_id, &c);
    let nb = Block {
        slot: at_slot,
        height: th + 1,
        prev: Some(ti),
        id: new_id,
        contents_hash,
        key_index,
    };
    let extended = append_block(c, nb);
    if valid_chain(n, &extended) {
        Some(extended)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Signatures and certificates (the certified layer, dictionary-passing)
// ---------------------------------------------------------------------------

/// What a certificate attests: the tip (slot/height/id) and a boundary buffer
/// of near-tip blocks the certificate covers.
pub struct CertClaim {
    pub tip_slot: u64,
    pub tip_height: u64,
    pub tip_id: Hash,
    pub tail: Chain,
}

/// A signed chain: like `Chain`, plus each block's signature handle.
pub enum SignedChain {
    SNil,
    SCons(Block, Hash, Box<SignedChain>),
}

/// A certified chain: a certificate handle for the prefix plus a signed suffix
/// of recent blocks. `Invalid` is the failure result of production.
pub enum CertifiedChain {
    Invalid,
    CC(Hash, SignedChain),
}

/// Injected cryptographic operations — the analogue of TypeScript's
/// `SigOps`/`CertOps` records. Signatures, keys and certificates are opaque
/// 256-bit handles (`Hash`); the protocol only passes them to this dictionary.
pub trait Crypto {
    /// Verify a block's signature under the slot producer's public key.
    fn verify(&self, key: &Hash, b: &Block, sig: &Hash) -> bool;
    /// The public key registered for participant `i`'s delegate key at
    /// index `j` (the versioned directory `dk(i, j)`).
    fn key_for(&self, i: u64, j: u64) -> Hash;
    /// Sign a block with the secret key.
    fn sign(&self, sk: &Hash, b: &Block) -> Hash;
    /// Verify a certificate handle (a recursive proof in deployment).
    fn cert_verify(&self, cert: &Hash) -> bool;
    /// The claim a certificate attests.
    fn cert_claim(&self, cert: &Hash) -> CertClaim;
}

/// Drop the signatures, keeping block content.
pub fn strip_sigs(sc: &SignedChain) -> Chain {
    match sc {
        SignedChain::SNil => Chain::Nil,
        SignedChain::SCons(b, _, tl) => {
            let nb = Block {
                slot: b.slot,
                height: b.height,
                prev: b.prev,
                id: b.id,
                contents_hash: b.contents_hash,
                key_index: b.key_index,
            };
            Chain::Cons(nb, Box::new(strip_sigs(tl)))
        }
    }
}

/// Every block's signature verifies under its slot producer's key.
pub fn sigs_ok<C: Crypto>(n: u64, crypto: &C, sc: &SignedChain) -> bool {
    match sc {
        SignedChain::SNil => true,
        SignedChain::SCons(b, sig, tl) => {
            let key = crypto.key_for(producer_for_slot(n, b.slot), b.key_index);
            crypto.verify(&key, b, sig) && sigs_ok(n, crypto, tl)
        }
    }
}

/// Validate a suffix as a continuation of a certified prefix: the first block
/// links to the certified tip, adjacent links hold, and every window that
/// matures within the suffix is dense (counted over the boundary buffer plus
/// the suffix).
/// The first suffix block links to the certified claim's tip (the claim's
/// counterpart of `child_ok`). Factored out so the extraction stays clean.
fn links_to_claim(cl: &CertClaim, s1: &Block) -> bool {
    let prev_ok = match s1.prev {
        Some(p) => hash_eq(&p, &cl.tip_id),
        None => false,
    };
    s1.height == cl.tip_height + 1 && cl.tip_slot < s1.slot && prev_ok
}

/// The maturity lower bound for a claim: `tip_slot + 2 - n` clamped at 0
/// (young claims with `tip_slot + 2 < n` would otherwise underflow u64). The
/// clamp matches the Lean model's Nat truncation. Factored out so the
/// extraction stays clean (each branch returns directly).
fn suffix_lo(n: u64, tip_slot: u64) -> u64 {
    if n > tip_slot + 2 {
        0
    } else {
        tip_slot + 2 - n
    }
}

pub fn validate_suffix(n: u64, cl: &CertClaim, suffix: &Chain) -> bool {
    match suffix {
        Chain::Nil => true,
        Chain::Cons(s1, tl) => {
            let link = links_to_claim(cl, s1);
            let links = links_from(s1, tl);
            let tip_slot = tip_slot_from(s1.slot, tl);
            // counted over the claim's boundary buffer ++ suffix
            let buf = append_suffix_to_buffer(&cl.tail, suffix);
            let lo = suffix_lo(n, cl.tip_slot);
            link && links && matured_dense(&buf, lo, tip_slot, n)
        }
    }
}

/// `buffer ++ suffix` as a plain chain (boundary buffer then suffix blocks).
fn append_suffix_to_buffer(buffer: &Chain, suffix: &Chain) -> Chain {
    match buffer {
        Chain::Nil => clone_chain(suffix),
        Chain::Cons(b, tl) => {
            let nb = Block {
                slot: b.slot,
                height: b.height,
                prev: b.prev,
                id: b.id,
                contents_hash: b.contents_hash,
                key_index: b.key_index,
            };
            Chain::Cons(nb, Box::new(append_suffix_to_buffer(tl, suffix)))
        }
    }
}

fn clone_chain(c: &Chain) -> Chain {
    match c {
        Chain::Nil => Chain::Nil,
        Chain::Cons(b, tl) => {
            let nb = Block {
                slot: b.slot,
                height: b.height,
                prev: b.prev,
                id: b.id,
                contents_hash: b.contents_hash,
                key_index: b.key_index,
            };
            Chain::Cons(nb, Box::new(clone_chain(tl)))
        }
    }
}

// ---------------------------------------------------------------------------
// Certificate-boundary floor snapshot (key-rotation certificates)
// ---------------------------------------------------------------------------

/// The per-producer key-index floor snapshot a key-rotation certificate
/// attests alongside its claim (the Rust analogue of `moltPetit.ts`
/// `FloorList`): one `(producer, floor)` node per producer, canonical shape
/// checked by `floors_shape_ok`.
pub enum FloorList {
    FNil,
    FCons(u64, u64, Box<FloorList>),
}

/// First-match floor read; 0 when absent (a fail-open default that is never
/// consulted once `floors_shape_ok` has pinned the canonical shape).
pub fn floor_lookup(fl: &FloorList, i: u64) -> u64 {
    match fl {
        FloorList::FNil => 0,
        FloorList::FCons(p, f, tl) => {
            if *p == i {
                *f
            } else {
                floor_lookup(tl, i)
            }
        }
    }
}

fn clone_floors(fl: &FloorList) -> FloorList {
    match fl {
        FloorList::FNil => FloorList::FNil,
        FloorList::FCons(p, f, tl) => FloorList::FCons(*p, *f, Box::new(clone_floors(tl))),
    }
}

/// Raise producer `i`'s floor to at least `v` — first matching node only,
/// consistent with `floor_lookup`'s first-match read.
pub fn floor_bump(fl: &FloorList, i: u64, v: u64) -> FloorList {
    match fl {
        FloorList::FNil => FloorList::FNil,
        FloorList::FCons(p, f, tl) => {
            let nf = if *p == i {
                if *f < v {
                    v
                } else {
                    *f
                }
            } else {
                *f
            };
            let rest = if *p == i {
                clone_floors(tl)
            } else {
                floor_bump(tl, i, v)
            };
            FloorList::FCons(*p, nf, Box::new(rest))
        }
    }
}

/// Canonical shape from `i`: producers `i, i+1, ..., n-1`, each exactly once,
/// in order. The TS check also demands nonnegative floors — free at `u64`.
/// The `i < n` gate is redundant for the accepted set (a too-long list fails
/// the TS check too) but keeps the recursion's `i + 1` from overflowing.
fn floors_shape_from(i: u64, n: u64, fl: &FloorList) -> bool {
    match fl {
        FloorList::FNil => i == n,
        FloorList::FCons(p, _f, tl) => *p == i && i < n && floors_shape_from(i + 1, n, tl),
    }
}

/// Canonical snapshot shape (`floorsShapeOk`): producers `0..n-1` exactly
/// once, in order — so `floor_lookup`'s fail-open default is never consulted.
pub fn floors_shape_ok(n: u64, fl: &FloorList) -> bool {
    floors_shape_from(0, n, fl)
}

/// The suffix monotone check against the snapshot (`keyMonoFromTs`): each
/// block's declared key index is at or above its slot producer's floor, and
/// the floor is bumped as the fold walks the suffix.
pub fn key_mono_from(n: u64, fl: &FloorList, c: &Chain) -> bool {
    match c {
        Chain::Nil => true,
        Chain::Cons(b, tl) => {
            let i = producer_for_slot(n, b.slot);
            let ok = floor_lookup(fl, i) <= b.key_index;
            let bumped = floor_bump(fl, i, b.key_index);
            ok && key_mono_from(n, &bumped, tl)
        }
    }
}

/// The certificate-boundary validator (`validateSuffixK`): the plain suffix
/// checks against the claim, the snapshot's canonical shape, and the monotone
/// key-index rule resumed from the attested floor.
pub fn validate_suffix_k(n: u64, cl: &CertClaim, fl: &FloorList, suffix: &Chain) -> bool {
    validate_suffix(n, cl, suffix) && floors_shape_ok(n, fl) && key_mono_from(n, fl, suffix)
}

/// Full validation of a certified chain: verify the certificate, then the
/// suffix signatures, then the structural suffix checks against the claim.
/// This is the verifier rule a light client runs.
pub fn validate_certified_chain<C: Crypto>(n: u64, crypto: &C, cc: &CertifiedChain) -> bool {
    match cc {
        CertifiedChain::Invalid => false,
        CertifiedChain::CC(cert, suffix) => {
            let cl = crypto.cert_claim(cert);
            let stripped = strip_sigs(suffix);
            crypto.cert_verify(cert) && sigs_ok(n, crypto, suffix) && validate_suffix(n, &cl, &stripped)
        }
    }
}

/// Tip height/id of the signed suffix, starting from the certified claim's tip.
fn signed_tip_height_from(cur: u64, sc: &SignedChain) -> u64 {
    match sc {
        SignedChain::SNil => cur,
        SignedChain::SCons(b, _, tl) => signed_tip_height_from(b.height, tl),
    }
}

fn signed_tip_id_from(cur: Hash, sc: &SignedChain) -> Hash {
    match sc {
        SignedChain::SNil => cur,
        SignedChain::SCons(b, _, tl) => signed_tip_id_from(b.id, tl),
    }
}

/// Append a signed block at the end of the signed suffix.
fn append_signed(sc: SignedChain, nb: Block, sig: Hash) -> SignedChain {
    match sc {
        SignedChain::SNil => SignedChain::SCons(nb, sig, Box::new(SignedChain::SNil)),
        SignedChain::SCons(b, s, tl) => {
            SignedChain::SCons(b, s, Box::new(append_signed(*tl, nb, sig)))
        }
    }
}

/// Honest certified block production for `at_slot`: only in the caller's own
/// slot, sign the new block, append it to the suffix, and ship it only if the
/// result passes the same `validate_certified_chain` every node runs.
/// Produces blocks (certified form).
pub fn produce_block_cert<C: Crypto>(
    n: u64,
    me: u64,
    at_slot: u64,
    new_id: Hash,
    contents_hash: Hash,
    key_index: u64,
    sk: Hash,
    crypto: &C,
    cert: Hash,
    suffix: SignedChain,
) -> CertifiedChain {
    if producer_for_slot(n, at_slot) != me {
        return CertifiedChain::Invalid;
    }
    let cl = crypto.cert_claim(&cert);
    let tip_h = signed_tip_height_from(cl.tip_height, &suffix);
    let tip_i = signed_tip_id_from(cl.tip_id, &suffix);
    let nb = Block {
        slot: at_slot,
        height: tip_h + 1,
        prev: Some(tip_i),
        id: new_id,
        contents_hash,
        key_index,
    };
    let sig = crypto.sign(&sk, &nb);
    let new_suffix = append_signed(suffix, nb, sig);
    let cc = CertifiedChain::CC(cert, new_suffix);
    if validate_certified_chain(n, crypto, &cc) {
        cc
    } else {
        CertifiedChain::Invalid
    }
}

// ===========================================================================
// Backend-generic consensus validator.
//
// The concrete `valid_chain` above is unchanged (and stays the proven
// reference). `valid_chain_be` is the SAME validity logic written once over an
// arithmetic/boolean `Backend`: instantiated with the native `U64Backend` here
// (extracted to Lean, proven sound for the model's chain rule), and with a plonky2
// circuit backend in `rust-keyrot/` (`molt_petit_keyrot`) — so the verified validator is the
// one the circuit runs. It is written branch-free (no `if` on backend booleans)
// so a single source serves both the native and circuit instantiations.
// ===========================================================================

/// Arithmetic/boolean backend. `Num` is the number representation (`u64`
/// natively, a field wire in-circuit), `Bool` likewise.
pub trait Backend {
    type Num: Copy;
    type Bool;
    fn zero(&self) -> Self::Num;
    fn one(&self) -> Self::Num;
    fn add(&self, a: Self::Num, b: Self::Num) -> Self::Num;
    fn lt(&self, a: Self::Num, b: Self::Num) -> Self::Bool;
    fn eq(&self, a: Self::Num, b: Self::Num) -> Self::Bool;
    fn and(&self, a: Self::Bool, b: Self::Bool) -> Self::Bool;
    fn or(&self, a: Self::Bool, b: Self::Bool) -> Self::Bool;
    fn not(&self, a: Self::Bool) -> Self::Bool;
    fn bool_const(&self, b: bool) -> Self::Bool;
    fn bool_to_num(&self, b: Self::Bool) -> Self::Num;
}

/// Native backend: the validator just runs over `u64`/`bool`.
pub struct U64Backend;

impl Backend for U64Backend {
    type Num = u64;
    type Bool = bool;
    fn zero(&self) -> u64 { 0 }
    fn one(&self) -> u64 { 1 }
    fn add(&self, a: u64, b: u64) -> u64 { a + b }
    fn lt(&self, a: u64, b: u64) -> bool { a < b }
    fn eq(&self, a: u64, b: u64) -> bool { a == b }
    fn and(&self, a: bool, b: bool) -> bool { a && b }
    fn or(&self, a: bool, b: bool) -> bool { a || b }
    fn not(&self, a: bool) -> bool { !a }
    fn bool_const(&self, b: bool) -> bool { b }
    fn bool_to_num(&self, b: bool) -> u64 { if b { 1 } else { 0 } }
}

/// Generic 256-bit hash (four `Num` limbs).
pub struct HashG<N> {
    pub a: N,
    pub b: N,
    pub c: N,
    pub d: N,
}

/// Generic block. `has_prev = false` marks genesis (no parent), avoiding an
/// `Option` (whose `==` Aeneas would emit as an axiom).
pub struct BlockG<N> {
    pub slot: N,
    pub height: N,
    pub has_prev: bool,
    pub prev: HashG<N>,
    pub id: HashG<N>,
}

/// Generic chain, lowest height first.
pub enum ChainG<N> {
    NilG,
    ConsG(BlockG<N>, Box<ChainG<N>>),
}

/// Four-limb hash equality under the backend.
fn hashg_eq<B: Backend>(be: &B, x: &HashG<B::Num>, y: &HashG<B::Num>) -> B::Bool {
    let ea = be.eq(x.a, y.a);
    let eb = be.eq(x.b, y.b);
    let ec = be.eq(x.c, y.c);
    let ed = be.eq(x.d, y.d);
    let eab = be.and(ea, eb);
    let ecd = be.and(ec, ed);
    be.and(eab, ecd)
}

/// Number of blocks whose slot lies in `[u, u + len)` (branch-free count).
fn window_count_be<B: Backend>(be: &B, c: &ChainG<B::Num>, u: B::Num, len: B::Num) -> B::Num {
    match c {
        ChainG::NilG => be.zero(),
        ChainG::ConsG(b, tl) => {
            let lt_lo = be.lt(b.slot, u); // slot < u
            let ge_u = be.not(lt_lo); // u <= slot
            let hi = be.add(u, len);
            let lt_hi = be.lt(b.slot, hi); // slot < u + len
            let inw = be.and(ge_u, lt_hi);
            let here = be.bool_to_num(inw);
            let rest = window_count_be(be, tl, u, len);
            be.add(here, rest)
        }
    }
}

/// One window meets the quorum-density bound: `q <= window_count`.
fn window_dense_be<B: Backend>(be: &B, q: B::Num, c: &ChainG<B::Num>, u: B::Num, n: B::Num) -> B::Bool {
    let cnt = window_count_be(be, c, u, n);
    let lt = be.lt(cnt, q); // count < q
    be.not(lt) // q <= count
}

/// Structural validity of a genesis block: height 0, no parent.
fn genesis_ok_be<B: Backend>(be: &B, b: &BlockG<B::Num>) -> B::Bool {
    let h0 = be.eq(b.height, be.zero());
    let has = be.bool_const(b.has_prev);
    let np = be.not(has); // no parent
    be.and(h0, np)
}

/// `child` is the immediate successor of `parent`.
fn child_ok_be<B: Backend>(be: &B, parent: &BlockG<B::Num>, child: &BlockG<B::Num>) -> B::Bool {
    let succ = be.add(parent.height, be.one());
    let h_ok = be.eq(child.height, succ);
    let slot_ok = be.lt(parent.slot, child.slot);
    let prev_eq = hashg_eq(be, &child.prev, &parent.id);
    let has = be.bool_const(child.has_prev);
    let prev_ok = be.and(has, prev_eq); // has_prev && prev == parent.id
    let hs = be.and(h_ok, slot_ok);
    be.and(hs, prev_ok)
}

/// Adjacent links from a parent through the rest of the chain.
fn links_from_be<B: Backend>(be: &B, parent: &BlockG<B::Num>, c: &ChainG<B::Num>) -> B::Bool {
    match c {
        ChainG::NilG => be.bool_const(true),
        ChainG::ConsG(b, tl) => {
            let here = child_ok_be(be, parent, b);
            let rest = links_from_be(be, b, tl);
            be.and(here, rest)
        }
    }
}

/// Every adjacent pair of the chain satisfies `child_ok`.
fn links_ok_be<B: Backend>(be: &B, c: &ChainG<B::Num>) -> B::Bool {
    match c {
        ChainG::NilG => be.bool_const(true),
        ChainG::ConsG(a, tl) => links_from_be(be, a, tl),
    }
}

/// Slot of the tip, starting from accumulator `cur`.
fn tip_slot_from_be<B: Backend>(be: &B, cur: B::Num, c: &ChainG<B::Num>) -> B::Num {
    match c {
        ChainG::NilG => cur,
        ChainG::ConsG(b, tl) => tip_slot_from_be(be, b.slot, tl),
    }
}

/// Density at every anchored window start `b.slot + 1` that is matured.
fn anchors_dense_be<B: Backend>(
    be: &B,
    all: &ChainG<B::Num>,
    rest: &ChainG<B::Num>,
    lo: B::Num,
    t: B::Num,
    n: B::Num,
    q: B::Num,
) -> B::Bool {
    match rest {
        ChainG::NilG => be.bool_const(true),
        ChainG::ConsG(b, tl) => {
            let u = be.add(b.slot, be.one());
            let lt_u_lo = be.lt(u, lo);
            let lo_le_u = be.not(lt_u_lo); // lo <= u
            let u_plus_n = be.add(u, n);
            let t1 = be.add(t, be.one());
            let lt_t1 = be.lt(t1, u_plus_n);
            let matured = be.not(lt_t1); // u + n <= t + 1
            let cond = be.and(lo_le_u, matured);
            let dense = window_dense_be(be, q, all, u, n);
            let ncond = be.not(cond);
            let ok = be.or(ncond, dense); // cond => dense
            let rest_ok = anchors_dense_be(be, all, tl, lo, t, n, q);
            be.and(ok, rest_ok)
        }
    }
}

/// Every matured window `[u, u+n)` with `lo <= u` is dense.
fn matured_dense_be<B: Backend>(
    be: &B,
    c: &ChainG<B::Num>,
    lo: B::Num,
    t: B::Num,
    n: B::Num,
    q: B::Num,
) -> B::Bool {
    let lo_plus_n = be.add(lo, n);
    let t1 = be.add(t, be.one());
    let lt_base = be.lt(t1, lo_plus_n);
    let base_matured = be.not(lt_base); // lo + n <= t + 1
    let dense_lo = window_dense_be(be, q, c, lo, n);
    let nbase = be.not(base_matured);
    let base = be.or(nbase, dense_lo); // matured => dense
    let anch = anchors_dense_be(be, c, c, lo, t, n, q);
    be.and(base, anch)
}

/// Full chain validation, generic over the backend. `q` is `quorum(n)`, passed
/// in (a constant for fixed `n`, so no division is needed in-circuit).
pub fn valid_chain_be<B: Backend>(be: &B, n: B::Num, q: B::Num, c: &ChainG<B::Num>) -> B::Bool {
    match c {
        ChainG::NilG => be.bool_const(true),
        ChainG::ConsG(g, tl) => {
            let genesis = genesis_ok_be(be, g);
            let links = links_ok_be(be, c);
            let tip = tip_slot_from_be(be, g.slot, tl);
            let dense = matured_dense_be(be, c, be.zero(), tip, n, q);
            let gl = be.and(genesis, links);
            be.and(gl, dense)
        }
    }
}

// ===========================================================================
// Certificate fold step (review items N2, N5)
//
// One block folded into a certificate state: the checks of the model's
// `GroundedCertK.extend` (mode 1, per-producer floor), `GroundedCertSched.extend`
// (mode 2, pin `slot / era <= key_index`) and `GroundedCertLock.extend` (mode 3,
// threaded generation `g`), minus `Signed b`, which the circuit checks with its
// signature gadget. Written once over `BackendK`, like `valid_chain_be`: the
// native `U64Backend` instance is extracted to Lean and proved against the
// `extend` premises; the plonky2 instance in `rust-keyrot/` is the step of the
// recursive certificate. `Backend` and `valid_chain_be` above are untouched.
//
// The claim's tail is a fixed-length buffer of the last `n - 1` slots, oldest
// first, each with a presence flag (0 = padding, 1 = a real block). It holds a
// superset of the model's filtered tail; the extra (older) slots lie below
// every window the step checks, so window counts agree.
// ===========================================================================

/// Extra arithmetic for the fold step. In-circuit, `div`/`rem` are witnessed
/// (`a = q * d + r`, `r < d`) and `select` is `c * (a - b) + b`.
pub trait BackendK: Backend {
    /// Floor quotient `a / d`; callers pass `d > 0`.
    fn div(&self, a: Self::Num, d: Self::Num) -> Self::Num;
    /// Remainder `a % d`; callers pass `d > 0`.
    fn rem(&self, a: Self::Num, d: Self::Num) -> Self::Num;
    /// `if c { a } else { b }`.
    fn select(&self, c: Self::Bool, a: Self::Num, b: Self::Num) -> Self::Num;
    /// Truncated subtraction (Lean's `Nat` subtraction).
    fn monus(&self, a: Self::Num, b: Self::Num) -> Self::Num;
}

impl BackendK for U64Backend {
    fn div(&self, a: u64, d: u64) -> u64 { a / d }
    fn rem(&self, a: u64, d: u64) -> u64 { a % d }
    fn select(&self, c: bool, a: u64, b: u64) -> u64 { if c { a } else { b } }
    fn monus(&self, a: u64, b: u64) -> u64 { if a < b { 0 } else { a - b } }
}

/// The tail buffer: `(flag, slot)` entries, oldest first.
pub enum TailG<N> {
    TNil,
    TCons(N, N, Box<TailG<N>>),
}

/// Per-producer floors, producer `0` first (mode 1).
pub enum FloorsG<N> {
    FNil,
    FCons(N, Box<FloorsG<N>>),
}

/// The certificate state a fold step reads (the public claim).
pub struct CertStateG<N> {
    pub tip_id: HashG<N>,
    pub tip_slot: N,
    pub tip_height: N,
    pub tail: TailG<N>,
}

/// Number of present buffer entries, plus the new block, in `[u, u + len)`.
fn tail_count_be<B: Backend>(be: &B, t: &TailG<B::Num>, u: B::Num, len: B::Num) -> B::Num {
    match t {
        TailG::TNil => be.zero(),
        TailG::TCons(f, s, tl) => {
            let lt_lo = be.lt(*s, u);
            let ge_u = be.not(lt_lo);
            let hi = be.add(u, len);
            let lt_hi = be.lt(*s, hi);
            let inw = be.and(ge_u, lt_hi);
            let present = be.eq(*f, be.one());
            let counted = be.and(present, inw);
            let here = be.bool_to_num(counted);
            let rest = tail_count_be(be, tl, u, len);
            be.add(here, rest)
        }
    }
}

/// The window `[u, u + n)` is checked by this fold (`tip_slot + 2 <= u + n` and
/// `u + n <= slot + 1`) and then holds `q` blocks of `tail ++ [b]`.
fn fold_window_ok_be<B: Backend>(
    be: &B,
    tail: &TailG<B::Num>,
    tip_slot: B::Num,
    slot: B::Num,
    u: B::Num,
    n: B::Num,
    q: B::Num,
) -> B::Bool {
    let un = be.add(u, n);
    let ts2 = be.add(tip_slot, be.add(be.one(), be.one()));
    let lt_lo = be.lt(un, ts2);
    let lo_ok = be.not(lt_lo); // tip_slot + 2 <= u + n
    let s1 = be.add(slot, be.one());
    let lt_hi = be.lt(s1, un);
    let hi_ok = be.not(lt_hi); // u + n <= slot + 1
    let checked = be.and(lo_ok, hi_ok);
    let in_tail = tail_count_be(be, tail, u, n);
    let b_lo = be.lt(slot, u);
    let b_ge = be.not(b_lo);
    let b_hi = be.lt(slot, un);
    let b_in = be.and(b_ge, b_hi);
    let cnt = be.add(in_tail, be.bool_to_num(b_in));
    let short = be.lt(cnt, q);
    let dense = be.not(short);
    let nchecked = be.not(checked);
    be.or(nchecked, dense) // checked => dense
}

/// The window starting just after each buffered slot is dense (when checked).
fn fold_anchors_ok_be<B: Backend>(
    be: &B,
    all: &TailG<B::Num>,
    rest: &TailG<B::Num>,
    tip_slot: B::Num,
    slot: B::Num,
    n: B::Num,
    q: B::Num,
) -> B::Bool {
    match rest {
        TailG::TNil => be.bool_const(true),
        TailG::TCons(_f, s, tl) => {
            let u = be.add(*s, be.one());
            let here = fold_window_ok_be(be, all, tip_slot, slot, u, n, q);
            let more = fold_anchors_ok_be(be, all, tl, tip_slot, slot, n, q);
            be.and(here, more)
        }
    }
}

/// The mode-independent fold checks: links to the tip and every newly matured
/// window dense. The minimum count over the checked range is at its lower end
/// `tip_slot + 2 - n` or just after some buffered slot, so those suffice.
pub fn cert_step_core_be<B: BackendK>(
    be: &B,
    n: B::Num,
    q: B::Num,
    st: &CertStateG<B::Num>,
    b: &BlockG<B::Num>,
) -> B::Bool {
    let succ = be.add(st.tip_height, be.one());
    let h_ok = be.eq(b.height, succ);
    let slot_ok = be.lt(st.tip_slot, b.slot);
    let prev_eq = hashg_eq(be, &b.prev, &st.tip_id);
    let has = be.bool_const(b.has_prev);
    let prev_ok = be.and(has, prev_eq);
    let links = be.and(be.and(h_ok, slot_ok), prev_ok);
    let ts2 = be.add(st.tip_slot, be.add(be.one(), be.one()));
    let lo = be.monus(ts2, n);
    let base = fold_window_ok_be(be, &st.tail, st.tip_slot, b.slot, lo, n, q);
    let anchors = fold_anchors_ok_be(be, &st.tail, &st.tail, st.tip_slot, b.slot, n, q);
    be.and(links, be.and(base, anchors))
}

/// Mode 1: the producer's floor is at most the block's key index.
fn floors_ok_be<B: BackendK>(be: &B, fl: &FloorsG<B::Num>, i: B::Num, p: B::Num, ki: B::Num) -> B::Bool {
    match fl {
        FloorsG::FNil => be.bool_const(true),
        FloorsG::FCons(f, tl) => {
            let me = be.eq(i, p);
            let below = be.lt(ki, *f);
            let bad = be.and(me, below);
            let ok = be.not(bad);
            let i1 = be.add(i, be.one());
            let more = floors_ok_be(be, tl, i1, p, ki);
            be.and(ok, more)
        }
    }
}

/// Mode 1: raise the producer's floor to the block's key index.
fn floors_bump_be<B: BackendK>(be: &B, fl: &FloorsG<B::Num>, i: B::Num, p: B::Num, ki: B::Num) -> FloorsG<B::Num> {
    match fl {
        FloorsG::FNil => FloorsG::FNil,
        FloorsG::FCons(f, tl) => {
            let me = be.eq(i, p);
            let raise = be.lt(*f, ki);
            let up = be.and(me, raise);
            let nf = be.select(up, ki, *f);
            let i1 = be.add(i, be.one());
            FloorsG::FCons(nf, Box::new(floors_bump_be(be, tl, i1, p, ki)))
        }
    }
}

/// Mode-1 fold step (`GroundedCertK.extend` without `Signed`).
pub fn cert_step_k_be<B: BackendK>(
    be: &B,
    n: B::Num,
    q: B::Num,
    st: &CertStateG<B::Num>,
    fl: &FloorsG<B::Num>,
    b: &BlockG<B::Num>,
    ki: B::Num,
) -> B::Bool {
    let core = cert_step_core_be(be, n, q, st, b);
    let p = be.rem(b.slot, n);
    let fl_ok = floors_ok_be(be, fl, be.zero(), p, ki);
    be.and(core, fl_ok)
}

/// Mode-1 floors after the step.
pub fn cert_next_floors_be<B: BackendK>(
    be: &B,
    n: B::Num,
    fl: &FloorsG<B::Num>,
    b: &BlockG<B::Num>,
    ki: B::Num,
) -> FloorsG<B::Num> {
    let p = be.rem(b.slot, n);
    floors_bump_be(be, fl, be.zero(), p, ki)
}

/// Mode-2 fold step (`GroundedCertSched.extend` without `Signed`), for the
/// schedule `slot / era`.
pub fn cert_step_sched_be<B: BackendK>(
    be: &B,
    n: B::Num,
    q: B::Num,
    era: B::Num,
    st: &CertStateG<B::Num>,
    b: &BlockG<B::Num>,
    ki: B::Num,
) -> B::Bool {
    let core = cert_step_core_be(be, n, q, st, b);
    let gen = be.div(b.slot, era);
    let below = be.lt(ki, gen);
    let pinned = be.not(below);
    be.and(core, pinned)
}

/// Mode-3 fold step (`GroundedCertLock.extend` without `Signed`): `g <= ki`, and
/// a block in the tip's grid window `slot / n` declares `g`. The next state's
/// generation is `ki`.
pub fn cert_step_lock_be<B: BackendK>(
    be: &B,
    n: B::Num,
    q: B::Num,
    st: &CertStateG<B::Num>,
    g: B::Num,
    b: &BlockG<B::Num>,
    ki: B::Num,
) -> B::Bool {
    let core = cert_step_core_be(be, n, q, st, b);
    let below = be.lt(ki, g);
    let ge = be.not(below);
    let w_tip = be.div(st.tip_slot, n);
    let w_b = be.div(b.slot, n);
    let same = be.eq(w_tip, w_b);
    let keeps = be.eq(g, ki);
    let nsame = be.not(same);
    let mix_ok = be.or(nsame, keeps);
    be.and(core, be.and(ge, mix_ok))
}

/// Append `(flag, slot)` at the end of the buffer.
fn tail_push_be<N: Copy>(t: &TailG<N>, f: N, s: N) -> TailG<N> {
    match t {
        TailG::TNil => TailG::TCons(f, s, Box::new(TailG::TNil)),
        TailG::TCons(f0, s0, tl) => TailG::TCons(*f0, *s0, Box::new(tail_push_be(tl, f, s))),
    }
}

/// The buffer after the step: drop the oldest entry, append the new block's
/// slot (length is preserved; an empty buffer, `n = 1`, stays empty).
pub fn cert_next_tail_be<B: Backend>(be: &B, t: &TailG<B::Num>, slot: B::Num) -> TailG<B::Num> {
    match t {
        TailG::TNil => TailG::TNil,
        TailG::TCons(_f, _s, tl) => tail_push_be(tl, be.one(), slot),
    }
}

/// The genesis claim's check (`GroundedCert*.genesis` without `Signed`):
/// `genesis_ok` and slot 0.
pub fn cert_genesis_ok_be<B: Backend>(be: &B, g: &BlockG<B::Num>) -> B::Bool {
    let ok = genesis_ok_be(be, g);
    let s0 = be.eq(g.slot, be.zero());
    be.and(ok, s0)
}

// ---------------------------------------------------------------------------
// Pass 26, stage C: the certificate's floors reach the client
// ---------------------------------------------------------------------------

/// A crypto dictionary whose certificates also expose the per-producer key
/// floors the fold certificate threads (`cert_next_floors_be`), decoded from
/// the proof's public inputs like `cert_claim`.
pub trait CryptoK: Crypto {
    /// The floor list a certificate attests: `(i, floor_i)` for `i = 0..n-1`.
    fn cert_floors(&self, cert: &Hash) -> FloorList;
}

/// Mode 1's verifier rule at a certificate boundary: verify the certificate,
/// the suffix signatures, and the suffix against the claim, with the key
/// floors taken from the certificate (never from the caller).
pub fn validate_certified_chain_k<C: CryptoK>(n: u64, crypto: &C, cc: &CertifiedChain) -> bool {
    match cc {
        CertifiedChain::Invalid => false,
        CertifiedChain::CC(cert, suffix) => {
            let cl = crypto.cert_claim(cert);
            let fl = crypto.cert_floors(cert);
            let stripped = strip_sigs(suffix);
            crypto.cert_verify(cert) && sigs_ok(n, crypto, suffix) && validate_suffix_k(n, &cl, &fl, &stripped)
        }
    }
}

// ===========================================================================
// Pass 28: the deployed client.
//
// Everything the agreement theorems used to take as hypotheses about a client
// is checked here by verified code: block ids are recomputed, the newest block
// is recent on the caller's clock reading, the certificate's claim is decoded
// from the fold certificate's public state by verified code, and each mode's
// key-version rule is run on the tail.
// ===========================================================================

/// What a deployed client needs beyond `Crypto`: the deployment's block-id
/// hash, and the fold certificate's public state (the proof's public inputs).
pub trait CryptoD: Crypto {
    /// The id the hashing layer gives a block with these other fields and
    /// its parent's signature (`None` for the genesis).
    fn block_id(
        &self,
        slot: u64,
        height: u64,
        prev: Option<Hash>,
        parent_sig: Option<Hash>,
        contents_hash: &Hash,
        key_index: u64,
    ) -> Hash;
    /// The signature of the certificate's tip block, which it exposes.
    fn cert_tip_sig(&self, cert: &Hash) -> Hash;
    /// The claim state the fold certificate exposes.
    fn cert_state(&self, cert: &Hash) -> CertStateG<u64>;
    /// Mode 1: the per-producer floors it exposes, producer 0 first.
    fn cert_floors_state(&self, cert: &Hash) -> FloorsG<u64>;
    /// Mode 3: the tip generation it exposes.
    fn cert_gen(&self, cert: &Hash) -> u64;
}

/// Every block's id is the deployment's hash of its other fields and its
/// parent's signature: `parent_sig` for the first block, then each block's
/// own signature for the next.
pub fn ids_ok<C: CryptoD>(crypto: &C, parent_sig: Option<Hash>, sc: &SignedChain) -> bool {
    match sc {
        SignedChain::SNil => true,
        SignedChain::SCons(b, s, tl) => {
            let id = crypto.block_id(b.slot, b.height, b.prev, parent_sig, &b.contents_hash, b.key_index);
            hash_eq(&id, &b.id) && ids_ok(crypto, Some(*s), tl)
        }
    }
}

/// The signature of the newest block of a signed tail, or `cur` if it is empty.
pub fn signed_tip_sig_from(cur: Hash, sc: &SignedChain) -> Hash {
    match sc {
        SignedChain::SNil => cur,
        SignedChain::SCons(_, s, tl) => signed_tip_sig_from(*s, tl),
    }
}

/// The verifier rule's recency check: `now <= tip + delta`, without overflow.
pub fn recent_ok(now: u64, delta: u64, tip: u64) -> bool {
    if now <= tip {
        true
    } else {
        now - tip <= delta
    }
}

/// The claim's tail decoded from the buffer: one block per present entry at
/// or above `lo`, carrying only its slot (the validator reads nothing else).
fn tail_of_buffer(t: &TailG<u64>, lo: u64) -> Chain {
    match t {
        TailG::TNil => Chain::Nil,
        TailG::TCons(f, s, tl) => {
            let rest = tail_of_buffer(tl, lo);
            if *f == 1 && lo <= *s {
                let z = Hash { a: 0, b: 0, c: 0, d: 0 };
                let nb = Block {
                    slot: *s,
                    height: 0,
                    prev: None,
                    id: z,
                    contents_hash: z,
                    key_index: 0,
                };
                Chain::Cons(nb, Box::new(rest))
            } else {
                rest
            }
        }
    }
}

/// The claim a fold certificate's public state stands for.
pub fn claim_of_state(n: u64, st: &CertStateG<u64>) -> CertClaim {
    let tip_id = Hash { a: st.tip_id.a, b: st.tip_id.b, c: st.tip_id.c, d: st.tip_id.d };
    let lo = suffix_lo(n, st.tip_slot);
    CertClaim {
        tip_slot: st.tip_slot,
        tip_height: st.tip_height,
        tip_id,
        tail: tail_of_buffer(&st.tail, lo),
    }
}

/// The floors of the public state as a `FloorList` from producer `i` on.
fn floors_of_state(i: u64, fl: &FloorsG<u64>) -> FloorList {
    match fl {
        FloorsG::FNil => FloorList::FNil,
        FloorsG::FCons(f, tl) => FloorList::FCons(i, *f, Box::new(floors_of_state(i + 1, tl))),
    }
}

/// Mode 2's pin on the tail, for the schedule `slot / era`.
pub fn sched_pin_ok(era: u64, c: &Chain) -> bool {
    match c {
        Chain::Nil => true,
        Chain::Cons(b, tl) => era > 0 && b.slot / era <= b.key_index && sched_pin_ok(era, tl),
    }
}

/// Mode 3's lockstep rule on the tail (`lockstepFrom`): from the claim's tip
/// slot `ts` and generation `g`, no block states less than `g`, and a block in
/// the previous block's grid window states the same version.
pub fn lockstep_from(n: u64, ts: u64, g: u64, c: &Chain) -> bool {
    match c {
        Chain::Nil => true,
        Chain::Cons(b, tl) => {
            let same = ts / n == b.slot / n;
            let ok = g <= b.key_index && (!same || g == b.key_index);
            ok && lockstep_from(n, b.slot, b.key_index, tl)
        }
    }
}

/// The checks every mode runs: the certificate verifies, the tail is
/// non-empty, signed, with recomputed ids, valid against the decoded claim,
/// and its newest block is recent at `now`.
pub fn validate_deployed<C: CryptoD>(n: u64, now: u64, delta: u64, crypto: &C, cert: &Hash, suffix: &SignedChain) -> bool {
    let st = crypto.cert_state(cert);
    let cl = claim_of_state(n, &st);
    let stripped = strip_sigs(suffix);
    let nonempty = !is_nil(&stripped);
    let tip = tip_slot_from(cl.tip_slot, &stripped);
    crypto.cert_verify(cert)
        && nonempty
        && sigs_ok(n, crypto, suffix)
        && ids_ok(crypto, Some(crypto.cert_tip_sig(cert)), suffix)
        && validate_suffix(n, &cl, &stripped)
        && recent_ok(now, delta, tip)
}

/// Mode 1: the deployed checks plus the monotone rule from the certificate's
/// floors.
pub fn validate_deployed_k<C: CryptoD>(n: u64, now: u64, delta: u64, crypto: &C, cert: &Hash, suffix: &SignedChain) -> bool {
    let fl = floors_of_state(0, &crypto.cert_floors_state(cert));
    let stripped = strip_sigs(suffix);
    validate_deployed(n, now, delta, crypto, cert, suffix)
        && floors_shape_ok(n, &fl)
        && key_mono_from(n, &fl, &stripped)
}

/// Mode 2: the deployed checks plus the schedule pin on the tail.
pub fn validate_deployed_sched<C: CryptoD>(n: u64, era: u64, now: u64, delta: u64, crypto: &C, cert: &Hash, suffix: &SignedChain) -> bool {
    let stripped = strip_sigs(suffix);
    validate_deployed(n, now, delta, crypto, cert, suffix) && sched_pin_ok(era, &stripped)
}

/// Mode 3: the deployed checks plus the lockstep rule on the tail, from the
/// certificate's tip slot and generation.
pub fn validate_deployed_lock<C: CryptoD>(n: u64, now: u64, delta: u64, crypto: &C, cert: &Hash, suffix: &SignedChain) -> bool {
    let st = crypto.cert_state(cert);
    let g = crypto.cert_gen(cert);
    let stripped = strip_sigs(suffix);
    validate_deployed(n, now, delta, crypto, cert, suffix) && lockstep_from(n, st.tip_slot, g, &stripped)
}

/// Honest production for the deployed client: only in the caller's own slot,
/// build the next block with its id computed by the hashing layer, sign it,
/// and ship it only if the result passes `validate_deployed` at the new slot.
pub fn produce_block_deployed<C: CryptoD>(
    n: u64,
    me: u64,
    at_slot: u64,
    delta: u64,
    contents_hash: Hash,
    key_index: u64,
    sk: Hash,
    crypto: &C,
    cert: Hash,
    suffix: SignedChain,
) -> CertifiedChain {
    if producer_for_slot(n, at_slot) != me {
        return CertifiedChain::Invalid;
    }
    let cl = claim_of_state(n, &crypto.cert_state(&cert));
    let tip_h = signed_tip_height_from(cl.tip_height, &suffix);
    let tip_i = signed_tip_id_from(cl.tip_id, &suffix);
    let prev = Some(tip_i);
    let parent_sig = Some(signed_tip_sig_from(crypto.cert_tip_sig(&cert), &suffix));
    let id = crypto.block_id(at_slot, tip_h + 1, prev, parent_sig, &contents_hash, key_index);
    let nb = Block {
        slot: at_slot,
        height: tip_h + 1,
        prev,
        id,
        contents_hash,
        key_index,
    };
    let sig = crypto.sign(&sk, &nb);
    let new_suffix = append_signed(suffix, nb, sig);
    if validate_deployed(n, at_slot, delta, crypto, &cert, &new_suffix) {
        CertifiedChain::CC(cert, new_suffix)
    } else {
        CertifiedChain::Invalid
    }
}
