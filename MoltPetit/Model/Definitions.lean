import Mathlib
import MoltPetit.TS.Emitted

/-!
# MoltPetit — all definitions

Every definition needed to *state* the main results (`Results/Results.lean`),
including all transitive subdefinitions, in one file — read this and
`Results.lean` (plus the protocol itself: `moltPetit.ts`, vendored as
the generated sidecar `MoltPetit/TS/Emitted.lean`, namespace `MoltPetit`)
and you have the complete formal content of the development. The
remaining modules contain only proofs.

Contents, in order:

1. the executable model implementation (blocks with opaque byte
   `contentsHash` payload commitments, chains, the window-density validator, signed chains,
   production) — the verified executable the TS bridge targets;
2. certified chains at the model level (claims, certificate
   dictionaries, suffix validation, certified production);
3. the semantic predicates of the safety proof (`ValidChain`,
   `ByzantineBounded`, records);
4. the signing model (`SigCorrect`, `SigningLog`);
5. the TS bridge injections (`toTSChain`/`toTSClaim`/`toTSSigned`) and
   the per-block signature predicate `TSSigned`;
6. the inductive certificate model (`GroundedCert`) and the two
   cryptographic assumptions of the light-client theorems
   (`SignedHashInjective`, `SigUnforgeableRecent`);
7. the real-time signing model (`Exposure`, `SigningExecution`,
   `HonestClock`, `ExposureBounded`) behind the light-client theorem;
8. honest-block delivery (`HonestBlocksCover`) for liveness;
9. the prover-throughput model (`ProverTiming`) behind the slot-duration
   recommendation.
-/

namespace MoltPetit.Model

-- ===========================================================================
-- 1–2. The executable model: blocks, chains, validation, production
-- ===========================================================================


/-- Quorum threshold `⌈2n/3⌉`. -/
def quorum (n : Nat) : Nat := (2 * n + 2) / 3

/-- Maximum tolerated Byzantine slots per `n`-slot window, `⌊(n-1)/3⌋`. -/
def maxByzantine (n : Nat) : Nat := (n - 1) / 3

/-- The designated producer index for a slot under round-robin rotation. -/
def producerForSlot (n slot : Nat) : Nat := slot % n
/--
A block.

`id` abstracts a collision-resistant hash of the block contents; the
implementation receives it from the caller's hashing layer rather than
computing a toy hash here.
-/
structure Block where
  slot : Nat
  height : Nat
  prev : Option Nat
  id : Nat
  /-- Commitment to the block payload: `contentsHash = H(payload)`. The
  payload itself travels out of band; the algorithm never inspects it. -/
  contentsHash : Nat
  /-- The **delegate-key index** the producer signed this block under. This
  is the per-producer signing-key version, carried *in band* so that the
  consensus order is the single agreed order in which key rotations take
  effect (see `MoltPetit/Model/KeyIndex.lean`). The verifier selects the public
  key as `keyFor (producerForSlot n slot) keyIndex`. -/
  keyIndex : Nat
deriving Repr, DecidableEq

/-- A chain is a linear history, lowest height first. -/
abbrev Chain := List Block

/-- Does block `b` occupy a slot in the half-open window `[u, u + len)`? -/
def blockInWindow (u len : Nat) (b : Block) : Bool :=
  decide (u ≤ b.slot ∧ b.slot < u + len)

/-- Number of chain blocks occupying slots in `[u, u + len)`. -/
def windowCount (c : Chain) (u len : Nat) : Nat :=
  (c.filter (blockInWindow u len)).length

/-- One window meets the quorum-density bound. -/
def windowDense (n : Nat) (c : Chain) (u : Nat) : Bool :=
  decide (quorum n ≤ windowCount c u n)

/--
All windows matured at tip slot `t` are dense.

A window `[u, u + n)` is matured once `u + n ≤ t + 1`, so the valid starts
are exactly `0, …, t + 1 - n`, i.e. `List.range (t + 2 - n)`.
-/
def maturedWindowsDense (n : Nat) (c : Chain) (t : Nat) : Bool :=
  (List.range (t + 2 - n)).all fun u => windowDense n c u

/-- Structural validity of a genesis block. -/
def genesisOk (b : Block) : Bool :=
  decide (b.height = 0 ∧ b.prev = none)

/-- Structural validity of `child` as the immediate successor of `parent`. -/
def childOk (parent child : Block) : Bool :=
  decide (child.height = parent.height + 1 ∧
          parent.slot < child.slot ∧
          child.prev = some parent.id)

/-- Every adjacent pair of the chain satisfies `childOk`. -/
def linksOk : Chain → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => childOk a b && linksOk (b :: rest)

/--
Full chain validation, replayed from genesis.

This is the rule every participant applies to every candidate chain before
adopting it as its best tip. It is the reference implementation; production
code may check matured windows incrementally per received block, which is
equivalent because earlier windows were checked when validating the parent.
-/
def validChain (n : Nat) (c : Chain) : Bool :=
  match c with
  | [] => true
  | g :: rest =>
    genesisOk g &&
    linksOk (g :: rest) &&
    (match (g :: rest).getLast? with
     | some tip => maturedWindowsDense n (g :: rest) tip.slot
     | none => true)

/-- Height of the chain tip, if any. -/
def tipHeight (c : Chain) : Option Nat :=
  c.getLast?.map Block.height

/--
Chain selection: adopt `candidate` over `cur` only if it validates and is
strictly higher. Safety does not depend on this rule (the safety theorem
quantifies over arbitrary valid chains); it only affects liveness.
-/
def selectChain (n : Nat) (cur candidate : Chain) : Chain :=
  if validChain n candidate && candidate.length > cur.length then candidate
  else cur

/--
Honest block production for slot `slot`.

Returns `some b` only if

* `slot` belongs to participant `me` under the rotation, and
* appending the new block to the current chain still passes full validation
  (in particular the cumulative density rule; otherwise the slot is skipped).

`newId` is the collision-resistant id of the new block, supplied by the
caller's hashing layer. The node's outer loop calls this at most once per
slot, which together with the conditions above realises the honest-slot
assumptions of the safety proof.
-/
def nextBlock (slot newId : Nat) (contentsHash keyIndex : Nat) (tip : Block) : Block :=
  { slot, height := tip.height + 1, prev := some tip.id, id := newId, contentsHash, keyIndex }

def produceBlock? (n me slot newId : Nat) (contentsHash keyIndex : Nat) (c : Chain) : Option Block :=
  if producerForSlot n slot = me then
    match c.getLast? with
    | none => none
    | some tip =>
      if validChain n (c ++ [nextBlock slot newId contentsHash keyIndex tip]) then
        some (nextBlock slot newId contentsHash keyIndex tip)
      else none
  else none

/-- The genesis block for a fresh deployment: slot 0, height 0, no parent,
key index 0 (producer 0's initial delegate key). -/
def genesisBlock (id : Nat) : Block :=
  { slot := 0, height := 0, prev := none, id, contentsHash := 0, keyIndex := 0 }

-- ---------------------------------------------------------------------------
-- Signature layer
-- ---------------------------------------------------------------------------

/--
Abstract signature operations over signature type `σ` and public-key type `pk`.

The message being signed is the block's content (slot, height, prev, id).
The signature itself is NOT part of the message — it is verified against it.
-/
structure SigOps (σ sk pk : Type) where
  /-- Sign a block with the given secret key. -/
  sign   : sk → Block → σ
  /-- Verify that `sig` is a valid signature of `block` under `key`. -/
  verify : pk → Block → σ → Bool

/--
The **versioned** public-key directory.

`registry i j` is the public key of participant `i`'s delegate key at index
`j`, written `dk(i, j)`. Participant `i` produces the slots `s`
with `s % n = i`; which of its delegate keys is in force is the per-block
`keyIndex`, carried in band. The verifier looks up
`registry (producerForSlot n slot) keyIndex`. The original *static* registry
is the special case where each participant pins a single index — recovered by
`indexed_reduces_to_static` (see `MoltPetit/Model/KeyIndex.lean`).
-/
abbrev KeyRegistry (pk : Type) := Nat → Nat → pk

/--
A block as it appears on the wire: content plus a detached signature.

The proof layer works with `Block` (no signature). The protocol layer works
with `SignedBlock σ`, verifying signatures before accepting blocks.
-/
structure SignedBlock (σ : Type) where
  block : Block
  sig   : σ
deriving Repr

/-- A signed chain. -/
abbrev SignedChain (σ : Type) := List (SignedBlock σ)

/-- Extract the unsigned blocks from a signed chain. -/
def stripSigs {σ : Type} (sc : SignedChain σ) : Chain :=
  sc.map SignedBlock.block

/-- Verify the signature of one signed block against the versioned directory,
selecting the key by the block's producer **and its in-band `keyIndex`**. -/
def sigOk {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk) (registry : KeyRegistry pk)
    (sb : SignedBlock σ) : Bool :=
  ops.verify (registry (producerForSlot n sb.block.slot) sb.block.keyIndex) sb.block sb.sig

/-- True iff every block in the signed chain has a valid signature. -/
def sigsOk {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk) (registry : KeyRegistry pk)
    (sc : SignedChain σ) : Bool :=
  sc.all (sigOk n ops registry)

/--
Full validation of a signed chain: signature check + structural validity.

`sigsOk` is checked first so invalid-signature blocks are rejected before
the more expensive structural replay.
-/
def validSignedChain {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk)
    (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChain n (stripSigs sc)

/--
Honest signed block production.

Signs the candidate block with `myKey`, then returns `some sb` only if:
- the slot belongs to `me` under the rotation,
- the signature verifies against the registry entry for this slot, and
- the extended chain is structurally valid.

The block is signed *before* the validity check so the signature is part of
what the chain validator sees (matching exactly what other participants
receive on the wire).
-/
def produceSignedBlock? {σ sk pk : Type} (n me slot newId : Nat) (contentsHash keyIndex : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (myKey : sk)
    (sc : SignedChain σ) : Option (SignedBlock σ) :=
  if producerForSlot n slot ≠ me then none
  else
    match (stripSigs sc).getLast? with
    | none => none
    | some tip =>
      let b  := nextBlock slot newId contentsHash keyIndex tip
      let sb : SignedBlock σ := { block := b, sig := ops.sign myKey b }
      if validSignedChain n ops registry (sc ++ [sb]) then some sb else none

/--
Signed chain selection: adopt `candidate` if it is valid and strictly longer.
-/
def selectSignedChain {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk)
    (registry : KeyRegistry pk) (cur candidate : SignedChain σ) : SignedChain σ :=
  if validSignedChain n ops registry candidate && candidate.length > cur.length
  then candidate else cur

-- ---------------------------------------------------------------------------
-- Trivial signature implementation (for simulation / testing)
-- ---------------------------------------------------------------------------

/-- Signature ops that accept everything and produce unit signatures. Used in tests and demos. -/
def trivialSigOps : SigOps Unit Unit Unit where
  sign   _ _ := ()
  verify _ _ _ := true

/-- The trivial versioned directory: every (participant, index) maps to the
unit key. -/
def trivialRegistry (_n : Nat) : KeyRegistry Unit :=
  fun _ _ => ()

/-- A signed genesis block with a unit signature. -/
def signedGenesisBlock (id : Nat) : SignedBlock Unit :=
  { block := genesisBlock id, sig := () }

-- ---------------------------------------------------------------------------
-- C-level entry points (unsigned chain interface, for extraction)
-- ---------------------------------------------------------------------------

@[export mcv2_valid_chain]
def validChainExport (n : Nat) (c : Chain) : Bool := validChain n c

@[export mcv2_produce_block]
def produceBlockExport (n me slot newId : Nat) (contentsHash keyIndex : Nat) (c : Chain) : Option Block :=
  produceBlock? n me slot newId contentsHash keyIndex c

@[export mcv2_select_chain]
def selectChainExport (n : Nat) (cur candidate : Chain) : Chain :=
  selectChain n cur candidate


-- ===========================================================================
-- Certified chains at the model level
-- ===========================================================================


/--
What a certificate claims about the prefix chain it attests to.

`tail` carries the last ≤ n-1 stripped prefix blocks (slot info only matters
for density; no signatures needed here since the cert already vouches for them).
-/
structure CertClaim where
  tipId     : Nat
  tipSlot   : Nat
  tipHeight : Nat
  tail      : List Block   -- boundary buffer: stripped prefix blocks near the tip
  deriving Repr, DecidableEq

/-- Abstract certificate operations over certificate type `α`. -/
structure CertOps (α : Type) where
  /-- Extract the claim embedded in the certificate. -/
  claim    : α → CertClaim
  /-- Verify the certificate (e.g. verify a ZK proof; always cheap). -/
  verify   : α → Bool
  /-- Extend the certificate by one new validated (stripped) block. -/
  generate : α → Block → α

/-- A chain: a certificate for the prefix plus a signed suffix. -/
structure CertifiedChain (α σ : Type) where
  cert   : α
  suffix : SignedChain σ
  deriving Repr

/-- Effective tip height of a certified chain. -/
def certTipHeight {α σ : Type} (ops : CertOps α) (cc : CertifiedChain α σ) : Nat :=
  cc.suffix.getLast?.map (·.block.height) |>.getD (ops.claim cc.cert).tipHeight

/-- Effective tip slot. -/
def certTipSlot {α σ : Type} (ops : CertOps α) (cc : CertifiedChain α σ) : Nat :=
  cc.suffix.getLast?.map (·.block.slot) |>.getD (ops.claim cc.cert).tipSlot

/-- Effective tip id. -/
def certTipId {α σ : Type} (ops : CertOps α) (cc : CertifiedChain α σ) : Nat :=
  cc.suffix.getLast?.map (·.block.id) |>.getD (ops.claim cc.cert).tipId

/--
Validate a signed suffix as a continuation of a certified prefix.

Steps:
1. Verify every suffix block's signature against the registry.
2. Check the structural link from cert tip to first suffix block.
3. Check adjacent structural links within the suffix.
4. Check density of newly matured windows, counting from `tail ++ suffix`.
-/
def validateSuffix {α σ sk pk : Type} (n : Nat)
    (sigOps : SigOps σ sk pk) (registry : KeyRegistry pk)
    (certOps : CertOps α) (cert : α)
    (suffix : SignedChain σ) : Bool :=
  -- strip sigs once; structural checks work on Block
  let chain := stripSigs suffix
  sigsOk n sigOps registry suffix &&
  match chain with
  | [] => true
  | first :: rest =>
    let c := certOps.claim cert
    decide (first.height = c.tipHeight + 1 ∧
            c.tipSlot < first.slot ∧
            first.prev = some c.tipId) &&
    linksOk (first :: rest) &&
    (match (first :: rest).getLast? with
     | none   => true
     | some t =>
         let buf := c.tail ++ (first :: rest)
         let lo  := c.tipSlot + 2 - n
         let hi  := t.slot + 2 - n
         (List.range (hi - lo)).all fun d => windowDense n buf (lo + d))

/-- Full validation of a certified chain. -/
def validateCertifiedChain {α σ sk pk : Type} (n : Nat)
    (sigOps : SigOps σ sk pk) (registry : KeyRegistry pk)
    (certOps : CertOps α) (cc : CertifiedChain α σ) : Bool :=
  certOps.verify cc.cert &&
  validateSuffix n sigOps registry certOps cc.cert cc.suffix

/--
Honest signed block production for a certified chain.

Returns `(signedBlock, updated chain)` iff the slot belongs to `me`, the
signature check passes, and the extended suffix is structurally valid.
-/
def produceBlockCert? {α σ sk pk : Type} (n me slot newId : Nat) (contentsHash keyIndex : Nat)
    (sigOps : SigOps σ sk pk) (registry : KeyRegistry pk) (myKey : sk)
    (certOps : CertOps α) (cc : CertifiedChain α σ) :
    Option (SignedBlock σ × CertifiedChain α σ) :=
  if producerForSlot n slot ≠ me then none
  else
    let c   := certOps.claim cc.cert
    let tip : Block :=
      cc.suffix.getLast?.map (·.block) |>.getD
        { slot := c.tipSlot, height := c.tipHeight, prev := none, id := c.tipId, contentsHash := 0, keyIndex := 0 }
    let b  : Block         := { slot, height := tip.height + 1, prev := some tip.id, id := newId, contentsHash, keyIndex }
    let sb : SignedBlock σ := { block := b, sig := sigOps.sign myKey b }
    let newSuffix := cc.suffix ++ [sb]
    if validateSuffix n sigOps registry certOps cc.cert newSuffix then
      some (sb, { cert := cc.cert, suffix := newSuffix })
    else none

/-- Certified chain selection. -/
def selectCertifiedChain {α σ sk pk : Type} (n : Nat)
    (sigOps : SigOps σ sk pk) (registry : KeyRegistry pk)
    (certOps : CertOps α) (current candidate : CertifiedChain α σ) :
    CertifiedChain α σ :=
  if validateCertifiedChain n sigOps registry certOps candidate &&
     certTipHeight certOps candidate > certTipHeight certOps current
  then candidate
  else current

/-! ## Trivial certificate implementation -/

/-- The trivial certificate: the full stripped chain prefix. -/
abbrev TrivialCert := Chain

/-- Certificate operations for the trivial implementation. -/
def trivialCertOps (n : Nat) : CertOps TrivialCert where
  claim c :=
    let tipSlot := c.getLast?.map Block.slot |>.getD 0
    let lo      := tipSlot + 2 - n
    { tipId     := c.getLast?.map Block.id     |>.getD 0
    , tipSlot
    , tipHeight := c.getLast?.map Block.height |>.getD 0
    , tail      := c.filter fun b => lo ≤ b.slot }
  verify c := validChain n c
  generate c b := c ++ [b]

/-- Genesis certified chain under the trivial cert ops with unit signatures. -/
def trivialGenesisCertChain (genesisId : Nat) : CertifiedChain TrivialCert Unit :=
  { cert := [genesisBlock genesisId], suffix := [] }


-- ===========================================================================
-- 3. Semantic predicates of the safety proof
-- ===========================================================================


/-- The set of blocks produced in each slot, over the whole execution. -/
abbrev SlotRecord := Nat → Finset Block

/-- A slot-based adversary schedule. `bad s` means the adversary owns slot `s`. -/
abbrev ByzantineSlots := Nat → Prop

/-- The block stored at a given height. -/
def blockAt? (c : Chain) (h : Nat) : Option Block := getElem? c h

/-- List index and stored height agree. -/
def SequentialHeights (c : Chain) : Prop :=
  ∀ ⦃h⦄ ⦃B : Block⦄, blockAt? c h = some B → B.height = h

/-- Slots strictly increase along the chain. -/
def StrictSlots (c : Chain) : Prop :=
  c.Pairwise fun a b => a.slot < b.slot

/-- Genesis has no parent; every later block points at its predecessor's id. -/
def ParentLinked (c : Chain) : Prop :=
  ∀ ⦃h⦄ ⦃B : Block⦄, blockAt? c h = some B →
    match h with
    | 0 => B.prev = none
    | k + 1 => ∃ P : Block, blockAt? c k = some P ∧ B.prev = some P.id

/--
Cumulative window density: every window matured at any chain block is
quorum-dense. Window `[u, u + n)` is matured at block `D` once
`u + n ≤ D.slot + 1`.
-/
def MaturedWindowsDense (n : Nat) (c : Chain) : Prop :=
  ∀ ⦃m⦄ ⦃D : Block⦄, blockAt? c m = some D →
    ∀ u, u + n ≤ D.slot + 1 →
      quorum n ≤ windowCount c u n

/-- Semantic validity of a chain. -/
def ValidChain (n : Nat) (c : Chain) : Prop :=
  SequentialHeights c ∧ StrictSlots c ∧ ParentLinked c ∧ MaturedWindowsDense n c

/-- Every chain block was actually produced (appears in the slot record). -/
def ChainInRecord (record : SlotRecord) (c : Chain) : Prop :=
  ∀ ⦃k⦄ ⦃B : Block⦄, blockAt? c k = some B → B ∈ record B.slot

/-- An honest slot contains at most one produced block. -/
def HonestSlotsUnique (bad : ByzantineSlots) (record : SlotRecord) : Prop :=
  ∀ s, ¬ bad s →
    ∀ ⦃B B' : Block⦄, B ∈ record s → B' ∈ record s → B = B'

/-- Block ids are globally injective across the record (hashes don't collide). -/
def IdInjective (record : SlotRecord) : Prop :=
  ∀ s t, ∀ ⦃B B' : Block⦄,
    B ∈ record s → B' ∈ record t → B.id = B'.id → B = B'

open Classical in
/-- The Byzantine slots inside the window `[u, u + n)`. -/
noncomputable def badSlotsIn (bad : ByzantineSlots) (u n : Nat) : Finset Nat :=
  (Finset.Ico u (u + n)).filter fun s => bad s

/-- At most `⌊(n-1)/3⌋` Byzantine slots in any `n` consecutive slots. -/
def ByzantineBounded (n : Nat) (bad : ByzantineSlots) : Prop :=
  ∀ u, (badSlotsIn bad u n).card ≤ maxByzantine n

/-- The two chains agree at every height up to `h`. -/
def CommonPrefixUpTo (c c' : Chain) (h : Nat) : Prop :=
  ∀ k, k ≤ h → ∃ B : Block, blockAt? c k = some B ∧ blockAt? c' k = some B

/-- `h` is the last common height of the two chains. -/
def LastCommonHeight (c c' : Chain) (h : Nat) : Prop :=
  CommonPrefixUpTo c c' h ∧
  ∀ k, h < k → ∀ B : Block,
    ¬ (blockAt? c k = some B ∧ blockAt? c' k = some B)

/-- The distinct slots that chain `c` occupies inside the window `[u, u + len)`. -/
def chainSlotsIn (c : Chain) (u len : Nat) : Finset Nat :=
  ((c.filter (blockInWindow u len)).map Block.slot).toFinset


-- ===========================================================================
-- 4. The signing model
-- ===========================================================================


/--
Correctness of the signature scheme: a signature produced with `sk_i`
verifies under the registry entry `registry[i]`, whenever `i` is the
designated producer of the block's slot.
-/
structure SigCorrect {σ sk pk : Type} (n : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (keyPair : Nat → Nat → sk) :
    Prop where
  verify_sign :
    ∀ (i j : Nat) (b : Block),
      producerForSlot n b.slot = i → b.keyIndex = j →
      ops.verify (registry i j) b (ops.sign (keyPair i j) b) = true

/--
The signing log of honest participants: `signed i s = some B` iff honest
participant `i` signed exactly the block `B` for slot `s`, and `none` if it
signed nothing there.

That this is a partial *function* (at most one block per participant per
slot) is precisely the honest behaviour of the implementation: the node's
outer loop calls production at most once per slot.
-/
abbrev SigningLog := Nat → Nat → Option Block


-- ===========================================================================
-- 5. TS bridge injections and the per-block signature predicate
-- ===========================================================================

open MoltPetit in
/-- Inject a model chain into the TS representation (block fields inline in
the cons cells; `Nat` fields cast to `Int`). -/
def toTSChain : Chain → MoltPetit.Chain
  | [] => .nil
  | b :: rest => .cons b.slot b.height (b.prev.map Int.ofNat) b.id b.contentsHash b.keyIndex (toTSChain rest)

open MoltPetit in
/-- Inject a model certificate claim into the TS representation. -/
def toTSClaim (cl : CertClaim) : MoltPetit.CertClaim :=
  { tipId := cl.tipId, tipSlot := cl.tipSlot, tipHeight := cl.tipHeight
  , tail := toTSChain cl.tail }

/-- Inject a model signed chain (signature handles are `Int`) into the TS
representation. -/
def toTSSigned : SignedChain MoltPetit.RawSignature → MoltPetit.SignedChain
  | [] => .nil
  | sb :: rest =>
      .cons sb.block.slot sb.block.height (sb.block.prev.map Int.ofNat)
        sb.block.id sb.block.contentsHash sb.block.keyIndex sb.sig (toTSSigned rest)


/--
Block `B` carries a signature that verifies — with the TS dictionary
`sigOps` — under the public key of its slot's designated producer.

This is the per-block residue of a passing `sigsOk` run, and (after the
signed-grounding change) of every fold of a grounded certificate: **every
block of a TS-validated certified chain is `TSSigned`**, adversarial slots
included — the adversary signs its own blocks with its own key, which is
exactly what `keyFor (producerForSlot n B.slot)` looks up.
-/
def TSSigned (n : Nat) (sigOps : MoltPetit.SigOps) (B : Block) : Prop :=
  ∃ sig : MoltPetit.RawSignature,
    sigOps.verify (sigOps.keyFor (producerForSlot n B.slot) B.keyIndex)
      B.slot B.height (B.prev.map Int.ofNat) B.id sig = true


-- ===========================================================================
-- 6. Grounded certificates and the light-client assumptions
-- ===========================================================================

/--
A certificate claim is **grounded in genesis `G`** when it arose from the
genesis claim by folding in one **signed** block at a time, each fold
checking the protocol rules. This is the inductive model of the
certificate primitive: *certificate unforgeability* says a certificate
that verifies carries a grounded claim — the proof system cannot attest a
fold that never happened.

The fold checks are exactly computable from the claim and the block (no
chain needed):

* the new block links to the claimed tip (height, slot, parent id);
* the new block carries a signature verifying under the public key of its
  slot's designated producer (`TSSigned` — certificates are over *signed*
  chains; the certified prefix never escapes the signature discipline);
* every window the new block matures is quorum-dense, counted over
  `tail ++ [b]` — sound because the tail holds precisely the prefix blocks
  with slot ≥ tipSlot + 2 - n, and newly matured windows start no earlier;
* the tail is then re-filtered to the new bound.
-/
inductive GroundedCert (n : Nat) (Signed : Block → Prop) (G : Block) :
    CertClaim → Prop
  | genesis :
      genesisOk G = true →
      G.slot = 0 →
      GroundedCert n Signed G
        { tipId := G.id, tipSlot := G.slot, tipHeight := G.height
        , tail := [G].filter fun x => decide (G.slot + 2 - n ≤ x.slot) }
  | extend (cl : CertClaim) (b : Block) :
      GroundedCert n Signed G cl →
      b.height = cl.tipHeight + 1 →
      cl.tipSlot < b.slot →
      b.prev = some cl.tipId →
      Signed b →
      (∀ u : Nat, cl.tipSlot + 2 ≤ u + n → u + n ≤ b.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ [b]) u n) →
      GroundedCert n Signed G
        { tipId := b.id, tipSlot := b.slot, tipHeight := b.height
        , tail := (cl.tail ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot) }

/--
**Hash collision resistance over the blocks that can occur.** Every block
of a TS-validated certified chain is the genesis or carries a verifying
producer signature (`TSSigned` — adversarial blocks included: the
adversary signs with its own key). So collision resistance is only ever
needed on this domain; quantifying over *all* of `Block` would be
vacuously false (the type contains colliding values that no execution
produces).
-/
def SignedHashInjective (Signed : Block → Prop) (G : Block) : Prop :=
  ∀ ⦃B B' : Block⦄,
    (B = G ∨ Signed B) → (B' = G ∨ Signed B') →
    B.id = B'.id → B = B'

/--
**Recency-scoped signature unforgeability.** Honest-slot signatures are
pinned to the signing log only for blocks of valid chains whose **tip is recent** — within `Δ`
slots of the verifier's current slot `now`.

The timed headline (`timed_tip_ancestor_agreement`) proves safety at staleness `n` directly;
this residue is only the untimed model's assumption. Over *unbounded* staleness
the patient harvesting attack defeats the unscoped assumption; this
scoping says exactly what survives: stale chains promise nothing,
recent ones pin honest slots.
-/
structure SigUnforgeableRecent (n : Nat) (bad : ByzantineSlots)
    (Signed : Block → Prop) (signed : SigningLog)
    (now Δ : Nat) : Prop where
  verified_was_signed :
    ∀ ⦃B : Block⦄ ⦃c : Chain⦄, ValidChain n c → B ∈ c →
      (∃ t : Block, c.getLast? = some t ∧ now ≤ t.slot + Δ) →
      ¬ bad B.slot → Signed B →
      signed (producerForSlot n B.slot) B.slot = some B

-- ===========================================================================
-- 7. The real-time signing model
-- ===========================================================================

/-- What was signed at each **real** slot: `log r` is the set of blocks whose
producer signature was created at real slot `r`. Who could sign under which
key at that time is the business of `Exposure`/`SigningExecution` below. -/
abbrev TimedLog := Nat → Finset Block

/-- `B` carries a signature that exists somewhere in the execution (or is
the genesis, which is publicly known). The domain of id injectivity. -/
def SignedEver (log : TimedLog) (G : Block) (B : Block) : Prop :=
  B = G ∨ ∃ r, B ∈ log r

/-- `B` exists by real slot `R`: it is the genesis or was signed at some
real slot `≤ R`. -/
def AvailableAt (log : TimedLog) (G : Block) (B : Block) (R : Nat) : Prop :=
  B = G ∨ ∃ r ≤ R, B ∈ log r

/-- Key exposure: `exposed s r` holds when, at real slot `r`, someone other
than its honest holder can sign under the key that verifies stamp `s` — the
stamp's seat is Byzantine, or that key has been stolen. Arbitrary in time: a
stolen key signs whenever its thief likes, any stamp it verifies. -/
abbrev Exposure := Nat → Nat → Prop

/--
The signing execution. `log r` is the set of blocks whose producer
signature was created at real slot `r`.

* `honest_once` — while a stamp's key is unexposed, only its honest holder
  signs under it, and an honest holder signs at most one block per stamp,
  ever (a persisted signing record).
* `chain_order` — id formation: signing a block requires its parent's id
  preimage, which contains the parent's signature, so the parent is
  available then. Predicting an unavailable parent's id is an EUF-CMA forgery.
* `id_inj` — hash collision resistance over the blocks that occur.
-/
structure SigningExecution (exposed : Exposure) (log : TimedLog) (G : Block) : Prop where
  honest_once : ∀ ⦃r r' : Nat⦄ ⦃B B' : Block⦄, B ∈ log r → B' ∈ log r' →
    B.slot = B'.slot → ¬ exposed B.slot r → ¬ exposed B.slot r' → B = B'
  chain_order : ∀ ⦃r : Nat⦄ ⦃B : Block⦄, B ∈ log r →
    ∀ ⦃i : Nat⦄, B.prev = some i →
      ∃ P : Block, P.id = i ∧ AvailableAt log G P r
  id_inj : ∀ ⦃B B' : Block⦄, SignedEver log G B → SignedEver log G B' →
    B.id = B'.id → B = B'

/-- Honest clocks run at most `σ` slots ahead of real time: a signature made
under an unexposed key at real slot `r` is on a stamp at most `r + σ`. -/
def HonestClock (σ : Nat) (exposed : Exposure) (log : TimedLog) : Prop :=
  ∀ ⦃r : Nat⦄ ⦃B : Block⦄, B ∈ log r → ¬ exposed B.slot r → B.slot ≤ r + σ

/--
The signing execution restricted to the blocks a validator admits. `Adm B`
is the per-block acceptance check a verifier runs: the block's signature
verifies, its id is *formed* (the hash of its preimage taken over its
parent's actual signature, which the verifier's hashing layer recomputes),
and, for mode 2, its declared version meets the schedule. Every field is
claimed only for admissible blocks (and the genesis): a block no verifier
would accept --- an unformed id, a dangling or copied parent reference, a
retired key --- may be signed by anyone, at any time, under any key, without
falsifying the hypothesis.

* `honest_once`: per stamp, at most one admissible block is signed while the
  stamp is unexposed.
* `chain_order`: an admissible block that names an occurring admissible block
  (or the genesis) as its parent was signed only once that parent existed ---
  its signature covers its id, whose preimage contains the parent's signature.
* `id_inj`: collision resistance among admissible blocks and the genesis.

`SigningExecution` implies the case `Adm = fun _ => True`.
-/
structure SigningExecutionOn (Adm : Block → Prop) (exposed : Exposure) (log : TimedLog)
    (G : Block) : Prop where
  honest_once : ∀ ⦃r r' : Nat⦄ ⦃B B' : Block⦄, B ∈ log r → B' ∈ log r' → Adm B → Adm B' →
    B.slot = B'.slot → ¬ exposed B.slot r → ¬ exposed B.slot r' → B = B'
  chain_order : ∀ ⦃r : Nat⦄ ⦃B C : Block⦄, B ∈ log r → Adm B →
    SignedEver log G C → (C = G ∨ Adm C) → B.prev = some C.id → AvailableAt log G C r
  id_inj : ∀ ⦃B B' : Block⦄, SignedEver log G B → SignedEver log G B' →
    (B = G ∨ Adm B) → (B' = G ∨ Adm B') → B.id = B'.id → B = B'

/-- Honest clocks, for admissible blocks only. -/
def HonestClockOn (Adm : Block → Prop) (σ : Nat) (exposed : Exposure) (log : TimedLog) : Prop :=
  ∀ ⦃r : Nat⦄ ⦃B : Block⦄, B ∈ log r → Adm B → ¬ exposed B.slot r → B.slot ≤ r + σ

open Classical in
/-- The exposure budget with lookback `ℓ` and freshness `φ`: of any `n`
consecutive stamps `[v, v + n)`, at most `maxByzantine n` have a key exposed
at some real slot `r` with `v - ℓ ≤ r < v + n + φ` — from `ℓ` slots before
the window starts to `φ` slots after it ends. Exposure outside that stretch
is not charged to the window. -/
def ExposureBounded (n ℓ φ : Nat) (exposed : Exposure) : Prop :=
  ∀ v, ((Finset.Ico v (v + n)).filter fun s =>
      ∃ r, v ≤ r + ℓ ∧ r < v + n + φ ∧ exposed s r).card
    ≤ maxByzantine n

open Classical in
/-- The cumulative exposure budget with freshness `φ`: of any `n` consecutive
stamps `[v, v + n)`, at most `maxByzantine n` have a key exposed at any real
slot before `v + n + φ`, however long before the window. It implies
`ExposureBounded n ℓ φ` for every `ℓ`, and needs no clock hypothesis. -/
def ExposureBoundedEver (n φ : Nat) (exposed : Exposure) : Prop :=
  ∀ v, ((Finset.Ico v (v + n)).filter fun s => ∃ r, r < v + n + φ ∧ exposed s r).card
    ≤ maxByzantine n

-- ===========================================================================
-- 8. Honest-block delivery (liveness)
-- ===========================================================================

/--
Honest-block delivery for chain `c` and window `[u, u + n)`: every honest
slot of the window has a produced block that is already part of `c`.

This packages two operational facts: honest producers were live in their
slots (they produced), and the network delivered their blocks in time for
the current producer to have built on them (synchrony). The Byzantine
budget then guarantees the window is quorum-dense
(`window_dense_of_honest_cover`).
-/
def HonestBlocksCover (bad : ByzantineSlots) (record : SlotRecord)
    (c : Chain) (u n : Nat) : Prop :=
  ∀ s, ¬ bad s → u ≤ s → s < u + n → ∃ B : Block, B ∈ record s ∧ B ∈ c

-- ---------------------------------------------------------------------------

-- ===========================================================================
-- 9. The prover-throughput model (slot duration)
-- ===========================================================================

namespace ProverTiming

/-- Time to produce one certificate covering `k` block transitions:
a large shared baseline plus a linear per-transition cost. -/
def certTime (baseline perBlock k : ℚ) : ℚ := baseline + k * perBlock

/-- One prover cycle: folding a backlog of `u` blocks takes
`certTime u`; with at most one block arriving per slot of length `τ`,
at most `certTime u / τ` blocks are uncovered when the certificate
lands — the next backlog. -/
def nextBacklog (baseline perBlock τ u : ℚ) : ℚ :=
  certTime baseline perBlock u / τ

/-- The uncovered suffix peaks just before a certificate lands: the
backlog being folded plus everything that arrived during the fold. -/
def peakSuffix (baseline perBlock τ u : ℚ) : ℚ :=
  u + nextBacklog baseline perBlock τ u

/-- Backlog across successive prover runs, from an initial backlog. -/
def backlog (baseline perBlock τ u₀ : ℚ) : ℕ → ℚ
  | 0 => u₀
  | j + 1 => nextBacklog baseline perBlock τ (backlog baseline perBlock τ u₀ j)

/-- **The recommended slot duration**: `perBlock + 2 · baseline / n`.
Sufficient and necessary (over steady states) for a single-prover node
to keep its chain within certificate + `n` slots' worth of blocks. -/
def recommendedSlot (n baseline perBlock : ℚ) : ℚ :=
  perBlock + 2 * baseline / n

end ProverTiming

end MoltPetit.Model
