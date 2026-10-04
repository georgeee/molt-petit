import Mathlib
import Spec.TS
import Spec.Model

/-!
# MoltPetit — all definitions

Every definition needed to *state* the main results (`Results/Results.lean`),
including all transitive subdefinitions, in one file — read this and
`Results.lean` (plus the protocol itself: `moltPetit.ts`, vendored as
the generated sidecar `Spec/TS.lean`, namespace `MoltPetit`)
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

/-- The genesis block for a fresh deployment: slot 0, height 0, no parent,
key index 0 (producer 0's initial delegate key). -/
def genesisBlock (id : Nat) : Block :=
  { slot := 0, height := 0, prev := none, id, contentsHash := 0, keyIndex := 0 }

-- ---------------------------------------------------------------------------
-- Signature layer
-- ---------------------------------------------------------------------------

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

/-- An honest slot contains at most one produced block. -/
def HonestSlotsUnique (bad : ByzantineSlots) (record : SlotRecord) : Prop :=
  ∀ s, ¬ bad s →
    ∀ ⦃B B' : Block⦄, B ∈ record s → B' ∈ record s → B = B'

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

-- ===========================================================================
-- 5. TS bridge injections and the per-block signature predicate
-- ===========================================================================

-- ===========================================================================
-- 6. Grounded certificates and the light-client assumptions
-- ===========================================================================

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

-- ===========================================================================
-- 8. Honest-block delivery (liveness)
-- ===========================================================================

-- ---------------------------------------------------------------------------

-- ===========================================================================
-- 9. The prover-throughput model (slot duration)
-- ===========================================================================

namespace ProverTiming

end ProverTiming

end MoltPetit.Model
