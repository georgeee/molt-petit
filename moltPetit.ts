// Molt Petit V2 — TypeScript reference implementation (Thales-TS subset).
//
// This file is the protocol definition. It is compiled to Lean 4 by
// thales (https://github.com/jessealama/thales); the emitted sidecar is
// vendored at MoltPetit/TS.lean and proved sound against the verified
// model by MoltPetit/V2/TSBridge.lean.
//
// Subset constraints shape the code:
//  * all functions are @total, so every recursion is structural — the
//    chain is a discriminated union (no arrays), and window enumeration
//    is anchored at block slots instead of counting down a bigint
//    (see maturedDense);
//  * a block's fields live inline in its cons cell (the subset has no
//    in-function record construction, but discriminated-union literals
//    lower to Lean constructors);
//  * bigint (Lean Int) everywhere; no `number` (Float) anywhere;
//  * no mutation, no classes, no exceptions, no `%` (the runtime's jsMod
//    is Float-only) — producerForSlot uses subtract-multiple instead;
//  * signatures, keys and certificates are opaque bigint handles
//    (named aliases below), with the actual crypto behind injected
//    dictionaries (SigOps, CertOps) — the subset has no generics over
//    recursive unions, so abstraction is by dictionary passing with
//    concrete handle types.
//
// Protocol rules (n participants, quorum q = ceil(2n/3)):
//  1. Slot s belongs to participant s - (s/n)*n  (= s mod n).
//  2. Block links: height +1, slot strictly increasing, prev = parent id.
//  3. Cumulative window density: every matured window [u, u+n) with
//     u + n <= tip.slot + 1 contains at least q chain blocks.
//     Density is checked at anchored window starts only (the lower bound
//     and b.slot + 1 for each block b) — the Lean bridge proves this
//     implies density of *all* matured windows, because a window's count
//     can only shrink when slid left to its anchor.
//  4. An honest participant produces at most one block per slot, only in
//     its own slot, only as a valid extension of its current chain.

// Cryptographic material is opaque handles. A wire-format signature,
// key or certificate is a fixed-length byte string, i.e. a bounded
// bigint; the integration glue decodes fixed-width (leading zero bytes
// matter). The aliases are documentation only — TypeScript aliases are
// structural, and the thales subset has no intersection types, so the
// branded-newtype idiom is unavailable; nothing stops a key being
// passed where a signature goes. The protocol never inspects these
// values — they only pass through the injected dictionaries.
type RawSignature = bigint;
type RawPublicKey = bigint;
type RawSecretKey = bigint;
type RawCertificate = bigint;

// A block id is the hash of the block contents (collision-resistant in
// deployment). Same caveat as above: the alias is documentation only.
//
// Id-formation contract (enforced by the integration glue, which computes
// and verifies ids — the protocol functions treat them as opaque):
//
//   id = H(slot, height, prev, parentSig, contentsHash, keyIndex)
//
// The parent's *signature* is part of the preimage. This makes future ids
// unpredictable to anyone not holding the parent producer's key —
// predicting another party's signature on a known message is producing a
// verifying forgery (EUF-CMA), so this holds even for deterministic
// schemes like Ed25519. Consequence: a signature coerced out of an honest
// node during an adversarial slot can only reference blocks that already
// exist (window density places the parent of a slot-s block within the
// previous n slots, while the producer's previous coercion opportunity is
// exactly n slots back), so it can never collide with the block the
// producer will honestly sign at its next slot — it can only fork, where
// the Byzantine budget governs. The parent signature is on the wire in
// the SignedChain; at the certificate boundary the (opaque) certificate
// conveys its tip's signature for the glue to check the first suffix
// block's preimage. The glue must verify id formation for every received
// block — already required for hash collision resistance to mean
// anything at all.
type Hash = bigint;

// Opaque block payload commitment: contentsHash = H(payload). The block
// carries only the hash of its contents (transactions travel out of
// band); the algorithm never inspects it. It is bound into the block id
// by the id-formation contract
// (id = H(slot, height, prev, parentSig, contentsHash, keyIndex)).
//
// The id preimage COMMITS keyIndex. This is load-bearing: the model's
// hash-collision-resistance assumption (SignedHashInjective) concludes
// full-block equality INCLUDING keyIndex, so two blocks differing only in
// their declared key version must hash differently — otherwise that
// assumption is uninstantiable once a producer has rotated (two versions
// of the same producer exist). The plonky2 prototype's block_id
// (rust-keyrot/src/poseidon_util.rs) is the reference layout. Because the
// id commits contentsHash and keyIndex, id equality subsumes comparing
// those fields wherever blocks are matched by id (see eqChain).

// A chain, newest block last. Each cons cell is a block: slot, height,
// parent id (null for genesis), own id, and the rest of the chain.
// `keyIndex` is the per-producer delegate-key version the block signed
// under (consensus-maintained, in-band key rotation): the verifier selects
// the public key as keyFor(producerForSlot(n, slot), keyIndex). See
// MoltPetit/V2/KeyIndex.lean and KEY_INDEX_DESIGN.md.
type Chain =
  | { kind: 'nil' }
  | { kind: 'cons'; slot: bigint; height: bigint; prev: Hash | null; id: Hash; contentsHash: Hash; keyIndex: bigint; tail: Chain };

// ---------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------

/** @total */
function quorum(n: bigint): bigint {
  return (2n * n + 2n) / 3n;
}

/** @total */
function maxByzantine(n: bigint): bigint {
  return (n - 1n) / 3n;
}

/** @total */
function producerForSlot(n: bigint, slot: bigint): bigint {
  return slot - (slot / n) * n;
}

// ---------------------------------------------------------------------------
// Chain helpers
// ---------------------------------------------------------------------------

/** @total */
function lengthOf(c: Chain): bigint {
  switch (c.kind) {
    case 'nil':
      return 0n;
    case 'cons':
      return 1n + lengthOf(c.tail);
  }
}

/**
 * Append chain b after chain a.
 * @total
 */
function appendChains(a: Chain, b: Chain): Chain {
  switch (a.kind) {
    case 'nil':
      return b;
    case 'cons': {
      const s = a.slot;
      const h = a.height;
      const p = a.prev;
      const i = a.id;
      const ct = a.contentsHash;
      const ki = a.keyIndex;
      const rest = appendChains(a.tail, b);
      return { kind: 'cons', slot: s, height: h, prev: p, id: i, contentsHash: ct, keyIndex: ki, tail: rest };
    }
  }
}

/**
 * Slot of the last block, starting from accumulator cur.
 * @total
 */
function tipSlotFrom(cur: bigint, t: Chain): bigint {
  switch (t.kind) {
    case 'nil':
      return cur;
    case 'cons':
      return tipSlotFrom(t.slot, t.tail);
  }
}

/**
 * Height of the last block, starting from accumulator cur.
 * @total
 */
function tipHeightFrom(cur: bigint, t: Chain): bigint {
  switch (t.kind) {
    case 'nil':
      return cur;
    case 'cons':
      return tipHeightFrom(t.height, t.tail);
  }
}

/**
 * Id of the last block, starting from accumulator cur.
 * @total
 */
function tipIdFrom(cur: Hash, t: Chain): Hash {
  switch (t.kind) {
    case 'nil':
      return cur;
    case 'cons':
      return tipIdFrom(t.id, t.tail);
  }
}

// ---------------------------------------------------------------------------
// Window density (anchored)
// ---------------------------------------------------------------------------

/**
 * Number of chain blocks with slot in [u, u + n).
 * @total
 */
function windowCount(c: Chain, u: bigint, n: bigint): bigint {
  switch (c.kind) {
    case 'nil':
      return 0n;
    case 'cons': {
      const inWin = u <= c.slot && c.slot < u + n ? 1n : 0n;
      return inWin + windowCount(c.tail, u, n);
    }
  }
}

/** @total */
function windowDense(c: Chain, u: bigint, n: bigint): boolean {
  return quorum(n) <= windowCount(c, u, n);
}

/**
 * Density at every anchored window start b.slot + 1 (b in rest) that is
 * at least lo and matured at tip slot t.
 * @total
 */
function anchorsDense(all: Chain, rest: Chain, lo: bigint, t: bigint, n: bigint): boolean {
  switch (rest.kind) {
    case 'nil':
      return true;
    case 'cons': {
      const u = rest.slot + 1n;
      const ok = lo <= u && u + n <= t + 1n ? windowDense(all, u, n) : true;
      return ok && anchorsDense(all, rest.tail, lo, t, n);
    }
  }
}

/**
 * All windows [u, u+n) with lo <= u and u + n <= t + 1 are quorum-dense
 * in c. Checked at anchors only: u = lo and u = b.slot + 1 for b in c.
 * @total
 */
function maturedDense(c: Chain, lo: bigint, t: bigint, n: bigint): boolean {
  const base = lo + n <= t + 1n ? windowDense(c, lo, n) : true;
  return base && anchorsDense(c, c, lo, t, n);
}

// ---------------------------------------------------------------------------
// Chain validation
// ---------------------------------------------------------------------------

/**
 * Adjacent links from a parent (slot pSlot, height pHeight, id pId)
 * through the whole of t.
 * @total
 */
function linksFrom(pSlot: bigint, pHeight: bigint, pId: Hash, t: Chain): boolean {
  switch (t.kind) {
    case 'nil':
      return true;
    case 'cons': {
      const link =
        t.height === pHeight + 1n &&
        pSlot < t.slot &&
        t.prev === pId;
      return link && linksFrom(t.slot, t.height, t.id, t.tail);
    }
  }
}

/**
 * Full chain validation, replayed from genesis: the rule every participant
 * applies to every candidate chain before adopting it. The head must be a
 * genesis block (height 0, no parent), every adjacent link must hold, and
 * every matured window must be quorum-dense.
 * @total
 */
function validChain(n: bigint, c: Chain): boolean {
  switch (c.kind) {
    case 'nil':
      return true;
    case 'cons': {
      const genesis = c.height === 0n && c.prev === null;
      const links = linksFrom(c.slot, c.height, c.id, c.tail);
      const tipSlot = tipSlotFrom(c.slot, c.tail);
      return genesis && links && maturedDense(c, 0n, tipSlot, n);
    }
  }
}

/**
 * Every block of rest produced by the same producer as (n, slot) declares
 * a key index at least ki — one block's half of the monotone rule against
 * all later blocks. (Two-function pattern, like linksFrom.)
 * @total
 */
function monoAgainst(n: bigint, slot: bigint, ki: bigint, rest: Chain): boolean {
  switch (rest.kind) {
    case 'nil':
      return true;
    case 'cons': {
      const ok = producerForSlot(n, slot) === producerForSlot(n, rest.slot) ? ki <= rest.keyIndex : true;
      return ok && monoAgainst(n, slot, ki, rest.tail);
    }
  }
}

/**
 * The in-band monotone key-index rule (KeyIndex.lean keyMonoOk): along the
 * chain, a producer's declared key version never decreases. A rotation is
 * announced by signing under a higher index; this rule forbids any later
 * reversion to a rotated-out one. On a full chain it implies the in-force
 * pin (KeyStealingCert.lean inForcePinned_of_validChainK): no block signs
 * under a version below the one in force (Δconf-confirmed) at its slot.
 * @total
 */
function keyMonoOk(n: bigint, c: Chain): boolean {
  switch (c.kind) {
    case 'nil':
      return true;
    case 'cons':
      return monoAgainst(n, c.slot, c.keyIndex, c.tail) && keyMonoOk(n, c.tail);
  }
}

/**
 * The indexed validator (KeyIndex.lean validChainK): structural validity
 * and density plus the monotone key-index rule. Bridged by
 * ts_validChainK_sound: acceptance gives the model's ValidChain and
 * KeyIndexMonotone, and on a full chain the ≤ in-force pin follows, so
 * this is the full-chain enforcement of the key-rotation validator. (The
 * certificate-boundary form — checking a suffix against a claim-carried
 * per-producer floor snapshot, keyMonoFrom in the model — needs the
 * claim-format extension of GroundedCertK and is not yet wired here.)
 * @total
 */
function validChainK(n: bigint, c: Chain): boolean {
  return validChain(n, c) && keyMonoOk(n, c);
}

// ---------------------------------------------------------------------------
// Block production
// ---------------------------------------------------------------------------

/**
 * A one-block chain holding the candidate block.
 * @total
 */
function singletonBlock(slot: bigint, height: bigint, prev: Hash, id: Hash, contentsHash: Hash, keyIndex: bigint): Chain {
  return { kind: 'cons', slot: slot, height: height, prev: prev, id: id, contentsHash: contentsHash, keyIndex: keyIndex, tail: { kind: 'nil' } };
}

/**
 * Honest block production for `slot`: returns the chain extended by one
 * new block iff the slot belongs to `me` under the rotation, the chain is
 * nonempty, and the extension passes full validation. The node's outer
 * loop calls this at most once per slot.
 * @total
 */
function produceBlock(n: bigint, me: bigint, atSlot: bigint, newId: Hash, contentsHash: Hash, keyIndex: bigint, c: Chain): Chain | null {
  if (producerForSlot(n, atSlot) !== me) {
    return null;
  }
  switch (c.kind) {
    case 'nil':
      return null;
    case 'cons': {
      const tipHeight = tipHeightFrom(c.height, c.tail);
      const tipId = tipIdFrom(c.id, c.tail);
      const extended = appendChains(c, singletonBlock(atSlot, tipHeight + 1n, tipId, newId, contentsHash, keyIndex));
      if (validChain(n, extended)) {
        return extended;
      }
      return null;
    }
  }
}

/**
 * Adopt the candidate only if it validates and is strictly longer.
 * @total
 */
function selectChain(n: bigint, cur: Chain, candidate: Chain): Chain {
  if (validChain(n, candidate) && lengthOf(cur) < lengthOf(candidate)) {
    return candidate;
  }
  return cur;
}

// ---------------------------------------------------------------------------
// Certificates: suffix validation
// ---------------------------------------------------------------------------

// What a certificate claims about the chain prefix it attests: the tip
// (id/slot/height) plus `tail`, the prefix blocks with
// slot >= tipSlot + 2 - n (the boundary buffer for density counting).
// Claims are only consumed here, never constructed (the certificate
// system — recursive ZK proofs in production — produces them).
interface CertClaim {
  tipId: Hash;
  tipSlot: bigint;
  tipHeight: bigint;
  tail: Chain;
}

/**
 * Validate a suffix of blocks as a continuation of a certified prefix:
 * 1. the first suffix block links to the certified tip;
 * 2. adjacent links hold within the suffix;
 * 3. every window that newly matures in the suffix is quorum-dense,
 *    counted over tail ++ suffix (anchored; the lower bound
 *    tipSlot + 2 - n is exactly where the tail buffer starts covering).
 * @total
 */
function validateSuffix(n: bigint, c: CertClaim, suffix: Chain): boolean {
  switch (suffix.kind) {
    case 'nil':
      return true;
    case 'cons': {
      const link =
        suffix.height === c.tipHeight + 1n &&
        c.tipSlot < suffix.slot &&
        suffix.prev === c.tipId;
      const links = linksFrom(suffix.slot, suffix.height, suffix.id, suffix.tail);
      const buf = appendChains(c.tail, suffix);
      const lo = c.tipSlot + 2n - n;
      const tipSlot = tipSlotFrom(suffix.slot, suffix.tail);
      return link && links && maturedDense(buf, lo, tipSlot, n);
    }
  }
}

// ---------------------------------------------------------------------------
// Key-index floors at the certificate boundary
// ---------------------------------------------------------------------------

// The per-producer key-floor snapshot a certificate carries alongside its
// claim (the grounded derivation GroundedCertK threads it through every
// fold, so certificate unforgeability attests the PAIR (claim, floors) —
// an unauthenticated floor is a soundness hole: a zeroed snapshot would
// readmit stolen rotated-out keys through the suffix check below).
type FloorList =
  | { kind: 'fnil' }
  | { kind: 'fcons'; producer: bigint; floor: bigint; tail: FloorList };

/**
 * The floor recorded for producer i (first match; 0 if absent — see
 * floorsShapeFrom, which a verifier MUST also check so that absence
 * cannot occur and the default is never consulted).
 * @total
 */
function floorLookup(fl: FloorList, i: bigint): bigint {
  switch (fl.kind) {
    case 'fnil':
      return 0n;
    case 'fcons':
      return fl.producer === i ? fl.floor : floorLookup(fl.tail, i);
  }
}

/**
 * Raise producer i's floor to at least v (first match).
 * @total
 */
function floorBump(fl: FloorList, i: bigint, v: bigint): FloorList {
  switch (fl.kind) {
    case 'fnil':
      return { kind: 'fnil' };
    case 'fcons': {
      const f = fl.producer === i ? (fl.floor < v ? v : fl.floor) : fl.floor;
      const rest = fl.producer === i ? fl.tail : floorBump(fl.tail, i, v);
      return { kind: 'fcons', producer: fl.producer, floor: f, tail: rest };
    }
  }
}

/**
 * Canonical shape from index i: the list is exactly producers
 * i, i+1, ..., n-1, once each, in order, with nonnegative floors.
 * floorsShapeOk(n, fl) = floorsShapeFrom(0, n, fl) makes floorLookup
 * total on 0..n-1 (the fail-open 0 default is never consulted) and rules
 * out negative wire floors (which would pass the monotone gate
 * trivially — fail-open).
 * @total
 */
function floorsShapeFrom(i: bigint, n: bigint, fl: FloorList): boolean {
  switch (fl.kind) {
    case 'fnil':
      return i === n;
    case 'fcons':
      return fl.producer === i && 0n <= fl.floor && floorsShapeFrom(i + 1n, n, fl.tail);
  }
}

/** @total */
function floorsShapeOk(n: bigint, fl: FloorList): boolean {
  return floorsShapeFrom(0n, n, fl);
}

/**
 * The suffix-side monotone key-index check against the certificate's
 * floor snapshot (the model's keyMonoFrom): each suffix block's declared
 * version clears its producer's running floor, which the block then
 * raises. This is the locally checkable form of the monotone rule for a
 * verifier that holds only cert + suffix — it never scans the history
 * behind the certificate for the rotation announcement.
 * @total
 */
function keyMonoFromTs(n: bigint, fl: FloorList, c: Chain): boolean {
  switch (c.kind) {
    case 'nil':
      return true;
    case 'cons': {
      const i = producerForSlot(n, c.slot);
      const ok = floorLookup(fl, i) <= c.keyIndex;
      return ok && keyMonoFromTs(n, floorBump(fl, i, c.keyIndex), c.tail);
    }
  }
}

/**
 * Suffix validation for the index-pinned protocol: the plain structural +
 * density checks, the canonical floor shape, and the suffix monotone
 * check against the certificate-attested floor snapshot. Together with
 * the certificate's own grounding (GroundedCertK: link + density +
 * signature + monotone gate per fold) this is what lets a light client
 * enforce the key-rotation validator from O(n) blocks — the model
 * theorem is keyrot_recent_certified_suffix_agreement.
 * @total
 */
function validateSuffixK(n: bigint, c: CertClaim, fl: FloorList, suffix: Chain): boolean {
  return validateSuffix(n, c, suffix) && floorsShapeOk(n, fl) && keyMonoFromTs(n, fl, suffix);
}

// ---------------------------------------------------------------------------
// Signatures (abstract, dictionary-passing)
// ---------------------------------------------------------------------------

// Signatures, secret/public keys and certificates are opaque handles
// (RawSignature etc., see above): the subset has no generics over
// recursive unions, so the abstraction lives entirely in the injected
// dictionaries below — the protocol never inspects a handle, it only
// passes it back to the dictionary. (On the wire these are real
// signatures and proofs; in the Lean model the dictionaries are
// arbitrary functions over the handle type.)

// A signed chain: like Chain, plus the block's signature handle.
type SignedChain =
  | { kind: 'nil' }
  | { kind: 'cons'; slot: bigint; height: bigint; prev: Hash | null; id: Hash; contentsHash: Hash; keyIndex: bigint; sig: RawSignature; tail: SignedChain };

// Signature operations. `keyFor(i, j)` is the public key of participant i's
// delegate key at index j (the versioned directory dk(i, j)); the in-force
// index travels in band as each block's keyIndex. The registry is part of
// the dictionary; keys are never carried in blocks.
interface SigOps {
  sign: (sk: RawSecretKey, slot: bigint, height: bigint, prev: Hash, id: Hash) => RawSignature;
  verify: (pk: RawPublicKey, slot: bigint, height: bigint, prev: Hash | null, id: Hash, sig: RawSignature) => boolean;
  keyFor: (i: bigint, j: bigint) => RawPublicKey;
}

/** @total */
function lengthOfSigned(sc: SignedChain): bigint {
  switch (sc.kind) {
    case 'nil':
      return 0n;
    case 'cons':
      return 1n + lengthOfSigned(sc.tail);
  }
}

/**
 * Drop the signatures, keeping the block content.
 * @total
 */
function stripSigs(sc: SignedChain): Chain {
  switch (sc.kind) {
    case 'nil':
      return { kind: 'nil' };
    case 'cons': {
      const s = sc.slot;
      const h = sc.height;
      const p = sc.prev;
      const i = sc.id;
      const ct = sc.contentsHash;
      const ki = sc.keyIndex;
      const rest = stripSigs(sc.tail);
      return { kind: 'cons', slot: s, height: h, prev: p, id: i, contentsHash: ct, keyIndex: ki, tail: rest };
    }
  }
}

/**
 * Append signed chain b after signed chain a.
 * @total
 */
function appendSigned(a: SignedChain, b: SignedChain): SignedChain {
  switch (a.kind) {
    case 'nil':
      return b;
    case 'cons': {
      const s = a.slot;
      const h = a.height;
      const p = a.prev;
      const i = a.id;
      const ct = a.contentsHash;
      const ki = a.keyIndex;
      const g = a.sig;
      const rest = appendSigned(a.tail, b);
      return { kind: 'cons', slot: s, height: h, prev: p, id: i, contentsHash: ct, keyIndex: ki, sig: g, tail: rest };
    }
  }
}

/**
 * Every block's signature verifies under its slot producer's key.
 * @total
 */
function sigsOk(n: bigint, sigOps: SigOps, sc: SignedChain): boolean {
  switch (sc.kind) {
    case 'nil':
      return true;
    case 'cons': {
      const ok = sigOps.verify(sigOps.keyFor(producerForSlot(n, sc.slot), sc.keyIndex), sc.slot, sc.height, sc.prev, sc.id, sc.sig);
      return ok && sigsOk(n, sigOps, sc.tail);
    }
  }
}

// ---------------------------------------------------------------------------
// Certificates (abstract, dictionary-passing)
// ---------------------------------------------------------------------------

// Certificate operations. `verify` checks a certificate handle (a ZK proof
// in production). `claim` extracts what the certificate asserts. `certFor`
// queries the registry of certificates that have become available so far,
// by tip block id; how certificates get produced and registered is not part
// of the protocol functions — a handle that verifies is usable, and absence
// is represented by returning a handle that fails verification.
interface CertOps {
  verify: (cert: RawCertificate) => boolean;
  claim: (cert: RawCertificate) => CertClaim;
  certFor: (id: Hash) => RawCertificate;
}

// A certified chain: a certificate for the prefix plus a signed suffix of
// recent blocks. 'invalid' is the failure result of production.
type CertifiedChain =
  | { kind: 'invalid' }
  | { kind: 'cc'; cert: RawCertificate; suffix: SignedChain };

/** @total */
function isNilChain(c: Chain): boolean {
  switch (c.kind) {
    case 'nil':
      return true;
    case 'cons':
      return false;
  }
}

/**
 * Does c start with exactly this head block?
 * @total
 */
function headMatches(pslot: bigint, pheight: bigint, pprev: Hash | null, pid: Hash, c: Chain): boolean {
  switch (c.kind) {
    case 'nil':
      return false;
    case 'cons':
      return pslot === c.slot && pheight === c.height && pprev === c.prev && pid === c.id;
  }
}

/**
 * The tail of c (nil for nil).
 * @total
 */
function tailOf(c: Chain): Chain {
  switch (c.kind) {
    case 'nil':
      return { kind: 'nil' };
    case 'cons':
      return c.tail;
  }
}

/**
 * Structural chain equality over the id-bound fields (slot, height, prev,
 * id). contentsHash and keyIndex are NOT compared directly — they are
 * committed by the id under the id-formation contract
 * (id = H(slot, height, prev, parentSig, contentsHash, keyIndex)), so id
 * equality subsumes them for any glue that verifies id formation (which
 * hash collision resistance already requires). Recursion is on `a`; the
 * helpers above inspect `b`, dodging both nested switches and mutual
 * recursion (neither is in the subset).
 * @total
 */
function eqChain(a: Chain, b: Chain): boolean {
  switch (a.kind) {
    case 'nil':
      return isNilChain(b);
    case 'cons': {
      const head = headMatches(a.slot, a.height, a.prev, a.id, b);
      return head && eqChain(a.tail, tailOf(b));
    }
  }
}

/**
 * Keep the blocks with slot >= lo.
 * @total
 */
function filterLow(c: Chain, lo: bigint): Chain {
  switch (c.kind) {
    case 'nil':
      return { kind: 'nil' };
    case 'cons': {
      const s = c.slot;
      const h = c.height;
      const p = c.prev;
      const i = c.id;
      const ct = c.contentsHash;
      const ki = c.keyIndex;
      const rest = filterLow(c.tail, lo);
      if (lo <= s) {
        return { kind: 'cons', slot: s, height: h, prev: p, id: i, contentsHash: ct, keyIndex: ki, tail: rest };
      }
      return rest;
    }
  }
}

/**
 * Full validation of a certified chain: verify the certificate FIRST, then
 * the suffix signatures, then the structural suffix checks against the
 * certificate's claim.
 * @total
 */
function validateCertifiedChain(n: bigint, sigOps: SigOps, certOps: CertOps, cc: CertifiedChain): boolean {
  switch (cc.kind) {
    case 'invalid':
      return false;
    case 'cc':
      return certOps.verify(cc.cert) && sigsOk(n, sigOps, cc.suffix) && validateSuffix(n, certOps.claim(cc.cert), stripSigs(cc.suffix));
  }
}

/**
 * A certified chain when the guard holds, else 'invalid'.
 * @total
 */
function ccIf(ok: boolean, cert: RawCertificate, suffix: SignedChain): CertifiedChain {
  if (ok) {
    return { kind: 'cc', cert: cert, suffix: suffix };
  }
  return { kind: 'invalid' };
}

/**
 * Prefer the first result when it found a cut.
 * @total
 */
function orFirst(a: CertifiedChain, b: CertifiedChain): CertifiedChain {
  switch (a.kind) {
    case 'invalid':
      return b;
    case 'cc':
      return a;
  }
}

/**
 * Find the newest cut point of the suffix that still leaves n blocks
 * above it and has a verifying, shape-correct certificate available in
 * the registry; drop the whole prefix up to it in one step. Returns
 * 'invalid' when no admissible cut has a certificate yet.
 *
 * Why newest-first with a single jump, rather than walking from the
 * oldest block one certificate at a time: certificate production is
 * batched (one proof covers many transitions, amortizing the large
 * baseline — see V2/ProverTiming.lean), so the registry holds
 * certificates only at batch boundaries. A one-by-one walk stalls at
 * the first depth with no certificate, even though a newer batch
 * certificate exists; scanning from the newest admissible cut finds it.
 *
 * `droppedAcc` accumulates the blocks between the current claim's tip
 * and the candidate cut (oldest first). The shape checks pin the
 * candidate's claim to be exactly the current claim extended by the
 * dropped segment (tip fields equal the cut block, the tail re-filtered
 * at the new bound), so compaction never changes which chain the
 * certified chain represents. The registry is queried eagerly at every
 * position; queries are local and cheap.
 * @total
 */
function tryCut(n: bigint, certOps: CertOps, oldCl: CertClaim, droppedAcc: Chain, suffix: SignedChain): CertifiedChain {
  switch (suffix.kind) {
    case 'nil':
      return { kind: 'invalid' };
    case 'cons': {
      if (lengthOfSigned(suffix.tail) < n) {
        return { kind: 'invalid' };
      }
      const ds = suffix.slot;
      const dh = suffix.height;
      const dp = suffix.prev;
      const di = suffix.id;
      const tail = suffix.tail;
      const dct = suffix.contentsHash;
      const dki = suffix.keyIndex;
      const cutBlock: Chain = { kind: 'cons', slot: ds, height: dh, prev: dp, id: di, contentsHash: dct, keyIndex: dki, tail: { kind: 'nil' } };
      const dropped = appendChains(droppedAcc, cutBlock);
      const deeper = tryCut(n, certOps, oldCl, dropped, tail);
      const cand = certOps.certFor(di);
      const cl = certOps.claim(cand);
      const expectedTail = filterLow(appendChains(oldCl.tail, dropped), ds + 2n - n);
      const shapeOk =
        certOps.verify(cand) &&
        cl.tipId === di &&
        cl.tipSlot === ds &&
        cl.tipHeight === dh &&
        eqChain(cl.tail, expectedTail);
      const here = ccIf(shapeOk, cand, tail);
      return orFirst(deeper, here);
    }
  }
}

/**
 * Keep the cut when one was found, else the chain as it was.
 * @total
 */
function orKeep(cut: CertifiedChain, cert: RawCertificate, suffix: SignedChain): CertifiedChain {
  switch (cut.kind) {
    case 'invalid':
      return { kind: 'cc', cert: cert, suffix: suffix };
    case 'cc':
      return cut;
  }
}

/**
 * Compact a certified chain: cut the suffix at the newest block that has
 * a certificate available, keeping at least n blocks above the cut.
 * Leaves the chain unchanged when no admissible certificate exists yet.
 * @total
 */
function compactChain(n: bigint, certOps: CertOps, cert: RawCertificate, suffix: SignedChain): CertifiedChain {
  const nilChain: Chain = { kind: 'nil' };
  const cut = tryCut(n, certOps, certOps.claim(cert), nilChain, suffix);
  return orKeep(cut, cert, suffix);
}

/**
 * Honest certified block production for `atSlot`:
 *
 * 1. only in the caller's own slot;
 * 2. sign the new block (the signature is part of what ships);
 * 3. append it to the suffix;
 * 4. compact: adopt the latest certificates available for this chain;
 * 5. validate the final certified chain — ship it only if it passes the
 *    same check every other node will run.
 *
 * The node's outer loop calls this at most once per slot.
 * @total
 */
function produceBlockCert(n: bigint, me: bigint, atSlot: bigint, newId: Hash, contentsHash: Hash, keyIndex: bigint, sk: RawSecretKey, sigOps: SigOps, certOps: CertOps, cert: RawCertificate, suffix: SignedChain): CertifiedChain {
  if (producerForSlot(n, atSlot) !== me) {
    return { kind: 'invalid' };
  }
  const cl = certOps.claim(cert);
  const stripped = stripSigs(suffix);
  const tipH = tipHeightFrom(cl.tipHeight, stripped);
  const tipI = tipIdFrom(cl.tipId, stripped);
  const sig = sigOps.sign(sk, atSlot, tipH + 1n, tipI, newId);
  const sb: SignedChain = { kind: 'cons', slot: atSlot, height: tipH + 1n, prev: tipI, id: newId, contentsHash: contentsHash, keyIndex: keyIndex, sig: sig, tail: { kind: 'nil' } };
  const newSuffix = appendSigned(suffix, sb);
  const compacted = compactChain(n, certOps, cert, newSuffix);
  if (validateCertifiedChain(n, sigOps, certOps, compacted)) {
    return compacted;
  }
  return { kind: 'invalid' };
}

/**
 * Effective tip height of a certified chain (-1 for the invalid result, so
 * it never wins selection).
 * @total
 */
function ccHeight(certOps: CertOps, cc: CertifiedChain): bigint {
  switch (cc.kind) {
    case 'invalid':
      return 0n - 1n;
    case 'cc':
      return tipHeightFrom(certOps.claim(cc.cert).tipHeight, stripSigs(cc.suffix));
  }
}

/**
 * Adopt the candidate certified chain only if it validates and is strictly
 * higher.
 * @total
 */
function selectCertifiedChain(n: bigint, sigOps: SigOps, certOps: CertOps, cur: CertifiedChain, candidate: CertifiedChain): CertifiedChain {
  if (validateCertifiedChain(n, sigOps, certOps, candidate) && ccHeight(certOps, cur) < ccHeight(certOps, candidate)) {
    return candidate;
  }
  return cur;
}
