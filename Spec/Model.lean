import Mathlib
import Spec.TS

/-!
# The protocol model: blocks, chains, validity, signing executions,
exposure and key-rotation predicates.

Definitions only: no theorem, no proof. The development imports this file.
-/

/-! ### From `MoltPetit.Model.Definitions` -/

namespace MoltPetit.Model

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

/--
The signing log of honest participants: `signed i s = some B` iff honest
participant `i` signed exactly the block `B` for slot `s`, and `none` if it
signed nothing there.

That this is a partial *function* (at most one block per participant per
slot) is precisely the honest behaviour of the implementation: the node's
outer loop calls production at most once per slot.
-/
abbrev SigningLog := Nat → Nat → Option Block

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

/-! ### From `MoltPetit.Model.KeyIndex` -/

namespace MoltPetit.Model

/-- The validator's **in-band key-rotation rule**: scanning the chain from
genesis (lowest height first), no earlier block of a producer may carry a
*higher* index than a later block of the same producer. Equivalently, each
producer's indices are non-decreasing in height — a rotation only ever moves
forward, and the move is ordered by consensus like any other block. -/
def keyMonoOk (n : Nat) : Chain → Bool
  | [] => true
  | b :: rest =>
      rest.all (fun b' =>
        decide (producerForSlot n b.slot = producerForSlot n b'.slot →
          b.keyIndex ≤ b'.keyIndex))
      && keyMonoOk n rest

/-- The semantic counterpart of `keyMonoOk`: for any two chain positions of
the **same producer**, the earlier one's index is ≤ the later one's. -/
def KeyIndexMonotone (n : Nat) (c : Chain) : Prop :=
  ∀ ⦃i j : Nat⦄ ⦃B B' : Block⦄, blockAt? c i = some B → blockAt? c j = some B' →
    i ≤ j → producerForSlot n B.slot = producerForSlot n B'.slot →
    B.keyIndex ≤ B'.keyIndex

/-- The full indexed validator: structural validity **and** the in-band
monotone-index rule. -/
def validChainK (n : Nat) (c : Chain) : Bool :=
  validChain n c && keyMonoOk n c

/-- The consensus-maintained **floor** for participant `i`: the highest
delegate index participant `i` has used anywhere in the chain. It is a pure
function of the (consensus-ordered) chain — the in-band counter. -/
def keyFloor (n : Nat) (c : Chain) (i : Nat) : Nat :=
  ((c.filter (fun b => decide (producerForSlot n b.slot = i))).map Block.keyIndex).foldl max 0
end MoltPetit.Model

/-! ### From `MoltPetit.Model.Liveness` -/

namespace MoltPetit.Model

/-- Extend `tip` by one honest block at each schedule slot, each built on
the previous block. -/
def buildFrom (tip : Block) : List Nat → Chain
  | [] => []
  | s :: ss => nextBlock s s 0 0 tip :: buildFrom (nextBlock s s 0 0 tip) ss

/-- A synchronous honest run from genesis `g` over honest schedule `ss`. -/
def buildChain (g : Block) (ss : List Nat) : Chain := g :: buildFrom g ss
end MoltPetit.Model

/-! ### From `MoltPetit.Model.Grounded` -/

namespace MoltPetit.Model

/-- What the grounding derivation reconstructs: a validator-accepted prefix
chain matching the claim exactly, every block of which is the genesis or
carries a verifying producer signature. -/
structure GroundedHistory (n : Nat) (Signed : Block → Prop) (G : Block)
    (cl : CertClaim) (c : Chain) : Prop where
  valid   : validChain n c = true
  head    : blockAt? c 0 = some G
  tip     : ∃ t : Block, c.getLast? = some t ∧
              t.id = cl.tipId ∧ t.slot = cl.tipSlot ∧ t.height = cl.tipHeight
  tail_eq : cl.tail = c.filter fun x => decide (cl.tipSlot + 2 - n ≤ x.slot)
  len_eq  : c.length = cl.tipHeight + 1
  signed  : ∀ B ∈ c, B = G ∨ Signed B
end MoltPetit.Model

/-! ### From `MoltPetit.Model.KeyRotation` -/

namespace MoltPetit.Model

/-- The **confirmed prefix** of `c` as seen from slot `s`: the blocks at least
`Δconf` slots in the past. `Δconf ≥ n` makes these blocks finalized (buried under
a matured, dense window), so all valid chains in one execution agree on them
(`inForce_agreement`, Phase 1b). -/
def confirmedPrefix (Δconf : Nat) (c : Chain) (s : Nat) : Chain :=
  c.filter (fun b => decide (b.slot + Δconf ≤ s))

/-- The **in-force delegate index** of participant `i` as seen from slot `s`:
participant `i`'s key floor over the confirmed prefix. Because it reads only the
confirmed (finalized) prefix, it is the *same* across all valid chains of one
execution in the confirmed zone — the property that pins a rotated-out key dead. -/
def inForce (n Δconf : Nat) (c : Chain) (i s : Nat) : Nat :=
  keyFloor n (confirmedPrefix Δconf c s) i

/-- The in-band **pin**: no block signs under a **rotated-out** index — every
block's declared `keyIndex` is at least the index in force (by the schedule the
chain itself records) at its slot.

**Why `≤` and not `=`.** An equality pin (`keyIndex = inForce`) would make
rotation *impossible*: the in-force floor only rises when a block carrying a
higher index becomes `Δconf`-deep, and an equality pin forbids any block from
ever carrying a higher index — by induction every producer would be frozen at
its initial index forever, and "a rotated-out key is dead" would be vacuous
(nothing is ever rotated out). The `≤` pin is the faithful rule: a producer
**announces** a rotation by signing under the new, higher index (allowed —
`inForce ≤ new`), the announcement confirms after `Δconf` slots, the floor
rises, and from then on the **old** index is below the floor and every block
declaring it is rejected. Theft of the in-force key is thus harmful only for
the ≤ `Δconf` window until the emergency rotation confirms; the corruption
budget (`badKeyrotOn`) accounts for exactly that window.

On a full chain the `≤` pin is implied by the monotone rule (`keyMonoOk`) —
an earlier same-producer block carries the floor's index and monotonicity
lifts it to the current block. It is enforced separately because it is the
**locally checkable** form: a certificate/suffix verifier that never sees the
announcement block can still check a suffix block's index against a carried
floor snapshot, where scanning for monotonicity would need the full history. -/
def inForcePinned (n Δconf : Nat) (c : Chain) : Bool :=
  c.all (fun b => decide (inForce n Δconf c (producerForSlot n b.slot) b.slot ≤ b.keyIndex))

/-- The **index-pinned validator**: structural validity, the monotone-index rule,
**and** the in-force pin (no rotated-out index). This is the "true" reduction —
the pin is enforced, not assumed (cf. the assumed hypothesis of
`indexed_reduces_to_static`).

This is the *unsigned* (model-level) pin. The signature conjunct `sigsOk` — that
each block actually verifies under `registry (producer, keyIndex)` — lives on the
signed layer (`validSignedChain`) and is woven in at Phase 2/3. The pin + `sigsOk`
give the *validator-side* half (`rotated_key_dead`: an accepted block verifies
under its declared registry entry, which is never a rotated-out version); the
rotated-out key is fully killed only once the Phase-2 *unforgeability* half (the
adversary cannot forge under a non-stolen entry) is added. -/
def validChainK' (n Δconf : Nat) (c : Chain) : Bool :=
  validChainK n c && inForcePinned n Δconf c

/-- The index-pinned **signed** validator: versioned-registry signatures + the
structural, monotone-index, in-force-pinned chain. -/
def validSignedChainK' {σ sk pk : Type} (n Δconf : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChainK' n Δconf (stripSigs sc)
end MoltPetit.Model

/-! ### From `MoltPetit.Model.KeyStealing` -/

namespace MoltPetit.Model

/-- The **key-stealing corruption** as seen through a fixed witness chain `c₀`:
slot `s` is bad if its producer is rented, or if **any not-yet-rotated-out key**
of the producer — any version at-or-above the index **in force** at `s` (read
off `c₀`'s confirmed prefix) — is stolen. Chain-independent on the confirmed
zone by `inForce_agreement`, so a genuine `ByzantineSlots` predicate.

This is the predicate that expresses the **healing** story: stealing the
producer's current key makes its slots bad, but only until the emergency
rotation (a block declaring a higher index) becomes `Δconf`-deep — from then on
the stolen version sits *below* the in-force index and no longer satisfies
`inForce ≤ j`, so the slots heal. A stolen **rotated-out** key never counts.
The `∃ j ≥ inForce` form (rather than `Stolen _ inForce` alone) is forced by
the `≤`-pin: an accepted block may sign under any not-yet-rotated-out version
(that is what makes announcing a rotation possible at all), so a slot is only
honest if *none* of those versions is compromised. -/
def badKeyrotOn (n Δconf : Nat) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop)
    (c₀ : Chain) (s : Nat) : Prop :=
  rented s ∨ ∃ j, inForce n Δconf c₀ (producerForSlot n s) s ≤ j ∧
    Stolen (producerForSlot n s) j
end MoltPetit.Model

/-! ### From `MoltPetit.Model.KeyStealingCert` -/

namespace MoltPetit.Model

/-- "Carries a verifying signature under its **declared** registry version" —
the per-block fact the certificate attests (`sigOk`'s content, blockwise).
Strictly stronger than `KeyStealingSigned` (which existentially quantifies the
version): `SignedDeclared → KeyStealingSigned`. -/
def SignedDeclared {Sig sk pk : Type} (n : Nat) (ops : SigOps Sig sk pk)
    (registry : KeyRegistry pk) (B : Block) : Prop :=
  ∃ sig : Sig,
    ops.verify (registry (producerForSlot n B.slot) B.keyIndex) B sig = true
end MoltPetit.Model

/-! ### From `MoltPetit.Model.KeyStealingSchedule` -/

namespace MoltPetit.Model

/-- The **scheduled pin**: no block signs under a version below the one the
public rotation schedule fixes for its slot. Position-determined — a pure
function of `b.slot` — hence identical across all chains. -/
def schedPinned (schedule : Nat → Nat) (c : Chain) : Bool :=
  c.all (fun b => decide (schedule b.slot ≤ b.keyIndex))

/-- The scheduled index-pinned **signed** validator: versioned-registry
signatures + structural/monotone validity + the scheduled pin. -/
def validSignedChainSched {σ sk pk : Type} (n : Nat) (schedule : Nat → Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChainK n (stripSigs sc)
    && schedPinned schedule (stripSigs sc)

/-- **Registry-level EUF-CMA over the scheduled validator** — the same
transparent surface as `KeyStealingEUFCMA`, phrased over `validSignedChainSched`.
A verifying signature under a non-stolen registered version, on a recent
accepted scheduled chain, is the honest producer's unique slot block. -/
structure SchedUnforgeable (n : Nat) (schedule : Nat → Nat) {Sig sk pk : Type}
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (rented : ByzantineSlots)
    (Stolen : Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block)
    (now Δ : Nat) : Prop where
  unforgeable :
    ∀ {sc : SignedChain Sig} {sb : SignedBlock Sig} {j : Nat},
      validSignedChainSched n schedule ops registry sc = true →
      sb ∈ sc →
      (∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) →
      ops.verify (registry (producerForSlot n sb.block.slot) j) sb.block sb.sig = true →
      ¬ rented sb.block.slot →
      ¬ Stolen (producerForSlot n sb.block.slot) j →
      honestSigned (producerForSlot n sb.block.slot) sb.block.slot = some sb.block

/-- The induced corruption under the schedule: a slot is bad if rented, or its
producer holds any stolen not-yet-rotated-out key — where "not yet rotated out"
is judged by the **public schedule** `schedule s`, not by any chain. **This is a
pure function of the slot: chain-independent, identical for the real chain and
any fork.** That is what discharges the anchor (§10.0). -/
def badSched (n : Nat) (schedule : Nat → Nat) (rented : ByzantineSlots)
    (Stolen : Nat → Nat → Prop) (s : Nat) : Prop :=
  rented s ∨ ∃ j, schedule s ≤ j ∧ Stolen (producerForSlot n s) j
end MoltPetit.Model

/-! ### From `MoltPetit.Model.KeyStealingScheduleCert` -/

namespace MoltPetit.Model

/-- The **core** scheduled signed validator: versioned-registry signatures +
structural/density validity + the scheduled pin — without the in-band
monotone-index bookkeeping (`keyMonoOk`), which is the one component whose
certificate-boundary reconstruction would need a floor snapshot, and which is
not load-bearing for scheduled safety (module doc). -/
def validSignedChainSchedCore {σ sk pk : Type} (n : Nat) (schedule : Nat → Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChain n (stripSigs sc)
    && schedPinned schedule (stripSigs sc)

/-- **Registry-level EUF-CMA over the core scheduled validator** — the same
transparent surface as `SchedUnforgeable`, scoped to core acceptance. Because
core validity accepts a superset of the fully-valid chains, this is a (mildly)
stronger named assumption than `SchedUnforgeable` — see the module doc for why
its plausibility argument is unchanged (the pin, which carries the argument, is
in the core) — and `schedUnforgeable_of_core` for the formal relation. -/
structure SchedCoreUnforgeable (n : Nat) (schedule : Nat → Nat) {Sig sk pk : Type}
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (rented : ByzantineSlots)
    (Stolen : Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block)
    (now Δ : Nat) : Prop where
  unforgeable :
    ∀ {sc : SignedChain Sig} {sb : SignedBlock Sig} {j : Nat},
      validSignedChainSchedCore n schedule ops registry sc = true →
      sb ∈ sc →
      (∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) →
      ops.verify (registry (producerForSlot n sb.block.slot) j) sb.block sb.sig = true →
      ¬ rented sb.block.slot →
      ¬ Stolen (producerForSlot n sb.block.slot) j →
      honestSigned (producerForSlot n sb.block.slot) sb.block.slot = some sb.block

/-- A certificate claim is **grounded-sched in genesis `G`** when it arose from
the genesis claim by folding in one signed block at a time, each fold checking
link + signature + density + **the scheduled pin** `schedule b.slot ≤
b.keyIndex`. Every check is a pure function of `(claim, block)` — the fold
threads **no floor**: the pin is computed from the block's own slot. The
certificate state is exactly the plain (`GroundedCert`) state; contrast
`GroundedCertK`, whose folds gate on (and step) a per-producer floor vector.

Deployment note (as in `GroundedCertK`): the genesis constructor requires
`Signed G` and the slot-0 pin `schedule G.slot ≤ G.keyIndex` — the deployment
genesis must carry a verifying registry signature at its declared version
(`sigsOk` has no genesis exemption). -/
inductive GroundedCertSched (n : Nat) (schedule : Nat → Nat) (Signed : Block → Prop)
    (G : Block) : CertClaim → Prop
  | genesis :
      genesisOk G = true →
      G.slot = 0 →
      Signed G →
      schedule G.slot ≤ G.keyIndex →
      GroundedCertSched n schedule Signed G
        { tipId := G.id, tipSlot := G.slot, tipHeight := G.height
        , tail := [G].filter fun x => decide (G.slot + 2 - n ≤ x.slot) }
  | extend (cl : CertClaim) (b : Block) :
      GroundedCertSched n schedule Signed G cl →
      b.height = cl.tipHeight + 1 →
      cl.tipSlot < b.slot →
      b.prev = some cl.tipId →
      Signed b →
      schedule b.slot ≤ b.keyIndex →
      (∀ u : Nat, cl.tipSlot + 2 ≤ u + n → u + n ≤ b.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ [b]) u n) →
      GroundedCertSched n schedule Signed G
        { tipId := b.id, tipSlot := b.slot, tipHeight := b.height
        , tail := (cl.tail ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot) }

/-- What the grounded-sched derivation reconstructs: a `validChain`-accepted,
**schedule-pinned** prefix matching the claim, with every block signed. -/
structure GroundedHistorySched (n : Nat) (schedule : Nat → Nat) (Signed : Block → Prop)
    (G : Block) (cl : CertClaim) (c : Chain) : Prop where
  valid   : validChain n c = true
  pinned  : schedPinned schedule c = true
  head    : blockAt? c 0 = some G
  tip     : ∃ t : Block, c.getLast? = some t ∧
              t.id = cl.tipId ∧ t.slot = cl.tipSlot ∧ t.height = cl.tipHeight
  tail_eq : cl.tail = c.filter fun x => decide (cl.tipSlot + 2 - n ≤ x.slot)
  len_eq  : c.length = cl.tipHeight + 1
  signed  : ∀ B ∈ c, Signed B
end MoltPetit.Model

/-! ### From `MoltPetit.Model.KeyStealingScheduleHorizon` -/

namespace MoltPetit.Model

/-- The Byzantine budget **from a horizon `H` on**: at most `⌊(n−1)/3⌋` bad
slots per `n`-window, required only of windows starting at or after `H`.
Corruption below the horizon is unconstrained. -/
def ByzantineBoundedFrom (H n : Nat) (bad : ByzantineSlots) : Prop :=
  ∀ u, H ≤ u → (badSlotsIn bad u n).card ≤ maxByzantine n
end MoltPetit.Model

/-! ### From `MoltPetit.Model.KeyStealingScheduleBudget` -/

namespace MoltPetit.Model
open Classical

/-- The theft half of `badSched`: the slot's producer holds a stolen key of the
scheduled-current-or-later generation. A pure function of the slot. -/
def theftSched (n : Nat) (schedule : Nat → Nat) (Stolen : Nat → Nat → Prop)
    (s : Nat) : Prop :=
  ∃ j, schedule s ≤ j ∧ Stolen (producerForSlot n s) j

/-- The **exposed producers** of a window, scheduled form: producers holding a
stolen current-or-later-generation key at their (unique) slot in `[u, u+n)`.
Unlike the default `exposedProducers`, this reads no chain — the generation
floor is `schedule s`, a function of the slot. -/
noncomputable def exposedProducersSched (n : Nat) (schedule : Nat → Nat)
    (Stolen : Nat → Nat → Prop) (u : Nat) : Finset Nat :=
  (Finset.Ico u (u + n)).filter (fun s => theftSched n schedule Stolen s) |>.image
    (producerForSlot n)
end MoltPetit.Model

/-! ### From `MoltPetit.Model.KeyStealingLockstep` -/

namespace MoltPetit.Model

/-- The **no-mixing rule**: along the chain, the declared generation is
constant within each `n`-slot window and non-decreasing across windows —
equivalently, `keyIndex` is a monotone function of the window index
`slot / n`. Roster-wide: unlike `keyMonoOk` this compares *all* pairs, not
just same-producer pairs. -/
def lockstepOk (n : Nat) : Chain → Bool
  | [] => true
  | b :: rest =>
      rest.all (fun b' =>
        decide ((b.slot / n = b'.slot / n → b.keyIndex = b'.keyIndex) ∧
          b.keyIndex ≤ b'.keyIndex))
      && lockstepOk n rest

/-- The **lockstep signed validator**: versioned-registry signatures,
structural/monotone validity, and the no-mixing rule. No schedule parameter —
nothing here references `rosterGen`. -/
def validSignedChainLock {σ sk pk : Type} (n : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChainK n (stripSigs sc)
    && lockstepOk n (stripSigs sc)

/-- The lagged schedule induced by a roster-generation function: a block at
slot `s` is pinned at the *previous* window's generation. The lag is what
absorbs the one unmatured tip window. (`Nat` subtraction makes window 0 lag
to itself, which the genesis convention `genesis_gen` pins exactly.) -/
def lagSched (n : Nat) (rosterGen : Nat → Nat) (s : Nat) : Nat :=
  rosterGen (s / n - 1)

/-- **The free-cadence lockstep package** (mode 3, D1′-thin). Fields:

* `mono` + `declared` + `genesis_gen` — **B1 as behaviour**: an
  execution-level, per-window, monotone `rosterGen` that every honest
  signature (and genesis) declares. Discovered, not fixed: no verifier is
  given it and no validator checks against it.
* `unforgeable` — the registry EUF-CMA surface at the **weakest** (constant-0)
  core validator, so its scope covers lockstep-accepted chains.
* `hashInj`, `rentBound`, `exposedBound` (at the lagged schedule — the
  cumulative census, `PackageA`'s shape), `budget_le` — as in `PackageA`.

Honest accounting: assumption-wise this is `PackageA` at `lagSched` plus the
behavioural `rosterGen` fields; what is *bought* is that the validator the
deployment runs is schedule-free. -/
structure LockstepPackage (n : Nat) (rosterGen : Nat → Nat) {Sig sk pk : Type}
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (rented : ByzantineSlots)
    (Stolen : Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block)
    (now Δ : Nat) (G : Block) (R T : Nat) : Prop where
  mono : ∀ ⦃w w' : Nat⦄, w ≤ w' → rosterGen w ≤ rosterGen w'
  unforgeable :
    SchedCoreUnforgeable n (fun _ => 0) ops registry rented Stolen honestSigned now Δ
  declared : ∀ ⦃i s : Nat⦄ ⦃B : Block⦄, honestSigned i s = some B →
    B.keyIndex = rosterGen (s / n)
  hashInj : SignedHashInjective (SignedDeclared n ops registry) G
  genesis_gen : G.keyIndex = rosterGen (G.slot / n)
  rentBound : ∀ u, (badSlotsIn rented u n).card ≤ R
  exposedBound : ∀ u, (exposedProducersSched n (lagSched n rosterGen) Stolen u).card ≤ T
  budget_le : R + T ≤ maxByzantine n
end MoltPetit.Model

/-! ### From `MoltPetit.Model.KeyStealingScheduleTimed` -/

namespace MoltPetit.Model
open Classical

/-- The timeless theft predicate the whole scheduled development consumes,
as the projection of a time-stamped theft relation `stolenAt i j r`
("producer `i`'s generation-`j` key is exfiltrated at real slot `r`"). -/
def stolenOf (stolenAt : Nat → Nat → Nat → Prop) (i j : Nat) : Prop :=
  ∃ r, stolenAt i j r
end MoltPetit.Model

/-! ### From `MoltPetit.Model.KeyStealingWindowCore` -/

namespace MoltPetit.Model

/-- Honest-slot uniqueness, required only on the slots of one window
`[u, u + len)`. `HonestSlotsUnique` is the everywhere form;
`honestSlotsUniqueOn_of_unique` recovers this at any `u`, `len`. What this
buys: a corruption predicate that is sound only on windows pinned to one
value (mode 3's per-generation `badLockAt`) can still be consumed by the
engine, since the engine never asks for uniqueness anywhere else. -/
def HonestSlotsUniqueOn (u len : Nat) (bad : ByzantineSlots) (record : SlotRecord) : Prop :=
  ∀ s, u ≤ s → s < u + len → ¬ bad s →
    ∀ ⦃B B' : Block⦄, B ∈ record s → B' ∈ record s → B = B'
end MoltPetit.Model

/-! ### From `MoltPetit.Model.KeyStealingLockstepGen` -/

namespace MoltPetit.Model
open Classical

/-- **The D1′-full lockstep package.** `B1`-as-behaviour (`declared`), the
constant-0 core EUF-CMA surface (unchanged), hash injectivity, and the
budget in PER-GENERATION form — `genBound` is syntactically `PackageB.
erasure_freeze`'s expression, so a `PackageB` field can be passed verbatim.
NO `exposedBound` (no cumulative census, no `lagSched`), and NO `mono`/
`genesis_gen`: neither is consumed by the new route — the pinning theorem
below is non-inductive and genesis-free, so carrying them would be an
unconsumed field. Incomparable with `LockstepPackage` in general;
`LockstepPackage.toGen` gives thin ⇒ gen when `rosterGen` is surjective
(skips no generation). -/
structure LockstepPackageGen (n : Nat) (rosterGen : Nat → Nat) {Sig sk pk : Type}
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (rented : ByzantineSlots)
    (Stolen : Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block)
    (now Δ : Nat) (G : Block) (R T : Nat) : Prop where
  unforgeable :
    SchedCoreUnforgeable n (fun _ => 0) ops registry rented Stolen honestSigned now Δ
  declared : ∀ ⦃i s : Nat⦄ ⦃B : Block⦄, honestSigned i s = some B →
    B.keyIndex = rosterGen (s / n)
  hashInj : SignedHashInjective (SignedDeclared n ops registry) G
  rentBound : ∀ u, (badSlotsIn rented u n).card ≤ R
  genBound : ∀ j : Nat, ((Finset.range n).filter (fun i => Stolen i j)).card ≤ T
  budget_le : R + T ≤ maxByzantine n
end MoltPetit.Model

/-! ### From `MoltPetit.Model.SchedExposure` -/

namespace MoltPetit.Model

/-- What the mode-2 validator admits, per block: a signature verifying under
the declared registry entry, and a declared version meeting the schedule. -/
def SchedAdmissible {Sig sk pk : Type} (n : Nat) (schedule : Nat → Nat)
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (B : Block) : Prop :=
  SignedDeclared n ops registry B ∧ schedule B.slot ≤ B.keyIndex

/-- Mode-2 exposure. `Controlled p r`: seat `p` is run by the adversary at real
slot `r`. `Stolen p j r`: version `j` of seat `p`'s key is held by someone
other than its honest holder at real slot `r`. Stamp `s` is exposed at `r` iff
its producer is controlled, or a version of its key that still meets `s`'s
schedule floor is stolen. -/
def schedExposed (n : Nat) (schedule : Nat → Nat) (Controlled : Nat → Nat → Prop)
    (Stolen : Nat → Nat → Nat → Prop) : Exposure :=
  fun s r => Controlled (producerForSlot n s) r ∨
    ∃ j, schedule s ≤ j ∧ Stolen (producerForSlot n s) j r
end MoltPetit.Model

/-! ### From `MoltPetit.Model.KeyStealingLockstepTimed` -/

namespace MoltPetit.Model
open Classical

/-- **A3, timed, mode 3 (no premature exposure).** A generation-`j` key can
be stolen at real slot `r` only if the roster has already reached `j` in
`r`'s grid window — the mode-3 twin of `NoPrematureTheft R stolenAt` with the
roster's own switch times `rosterGen ∘ (·/n)` in place of `j * R`. Total even
when `rosterGen` never reaches `j` (no `Nat.find`). -/
def NoPrematureTheftLock (n : Nat) (rosterGen : Nat → Nat)
    (stolenAt : Nat → Nat → Nat → Prop) : Prop :=
  ∀ i j r, stolenAt i j r → j ≤ rosterGen (r / n)

/-- **B2, timed, mode 3 (erasure).** At real slot `r`, nothing of a
generation the roster has already moved past can be stolen — retired
material was destroyed at the switch. The mode-3 twin of `ErasureTimed R
stolenAt`. THIS field is consumed below by `genBound_of_preRetirementBound`
— erasure is load-bearing here, the mirror image of mode 2. -/
def ErasureTimedLock (n : Nat) (rosterGen : Nat → Nat)
    (stolenAt : Nat → Nat → Nat → Prop) : Prop :=
  ∀ i j r, stolenAt i j r → rosterGen (r / n) ≤ j

/-- The per-generation census a mode-3 deployment asserts: seats whose
generation-`j` key is stolen at a real time at which `j` has not yet
retired. Mirror of `recentTheftProducers` with the generation floor replaced
by the retirement ceiling. Under `ErasureTimedLock` it coincides with the
timeless `(Finset.range n).filter (fun i => stolenOf stolenAt i j)`. -/
noncomputable def preRetirementTheftProducers (n : Nat) (rosterGen : Nat → Nat)
    (stolenAt : Nat → Nat → Nat → Prop) (j : Nat) : Finset Nat :=
  (Finset.range n).filter (fun i => ∃ r, stolenAt i j r ∧ rosterGen (r / n) ≤ j)

/-- **Mode 3 with its temporal content formalized** (the twin of
`PackageBTimed`): theft is time-stamped, A3 (`notBefore`) and B2
(`notAfter`) are fields, and the rate is the while-live per-generation
census. `notAfter` is CONSUMED (`toGen` via `genBound_of_preRetirementBound`);
`notBefore` is documentary here (consumed only by `theft_in_era_lock`) —
the exact mirror of mode 2, where `notAfter` is documentary and A3 is
consumed. -/
structure LockstepPackageTimed (n : Nat) (rosterGen : Nat → Nat) {Sig sk pk : Type}
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (rented : ByzantineSlots)
    (stolenAt : Nat → Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block)
    (now Δ : Nat) (G : Block) (R T : Nat) : Prop where
  unforgeable :
    SchedCoreUnforgeable n (fun _ => 0) ops registry rented (stolenOf stolenAt)
      honestSigned now Δ
  declared : ∀ ⦃i s : Nat⦄ ⦃B : Block⦄, honestSigned i s = some B →
    B.keyIndex = rosterGen (s / n)
  hashInj : SignedHashInjective (SignedDeclared n ops registry) G
  notBefore : NoPrematureTheftLock n rosterGen stolenAt
  notAfter : ErasureTimedLock n rosterGen stolenAt
  rentBound : ∀ u, (badSlotsIn rented u n).card ≤ R
  preRetirementTheftBound : ∀ j, (preRetirementTheftProducers n rosterGen stolenAt j).card ≤ T
  budget_le : R + T ≤ maxByzantine n
end MoltPetit.Model

/-! ### From `MoltPetit.Model.KeyStealingLockstepCert` -/

namespace MoltPetit.Model

/-- The suffix-side no-mixing check a certificate-syncing verifier runs: fold
the boundary state (tip slot, tip generation) through the suffix. Each block
must not decrease the generation, and must equal it when the block lies in
the same grid window (`slot / n`) as the current state; the state then
becomes `(b.slot, b.keyIndex)`. Analogue of `keyMonoFrom` with a single `Nat`
instead of an `n`-vector, and of `schedPinned` run over a suffix in mode 2.
Pure function of `(tipSlot, g, suffix)`. -/
def lockstepFrom (n : Nat) : Nat → Nat → Chain → Bool
  | _, _, [] => true
  | ts, g, b :: rest =>
      decide (g ≤ b.keyIndex ∧ (ts / n = b.slot / n → g = b.keyIndex))
      && lockstepFrom n b.slot b.keyIndex rest

/-- The lockstep certificate derivation: `GroundedCertSched`'s shape (same
tail buffer, same Nat-form density premise, so `windowCount_append` /
`windowCount_filter_low` transfer verbatim) with the pin premise replaced by
the two-clause no-mixing check against the threaded tip generation `g`, and
the state stepped to `b.keyIndex`. Every check is a pure function of
`(claim, g, block)` — what a recursive certificate attests per fold. The
genesis state is `G.keyIndex`, matching `LockstepPackage.genesis_gen`. -/
inductive GroundedCertLock (n : Nat) (Signed : Block → Prop) (G : Block) :
    CertClaim → Nat → Prop
  | genesis :
      genesisOk G = true →
      G.slot = 0 →
      Signed G →
      GroundedCertLock n Signed G
        { tipId := G.id, tipSlot := G.slot, tipHeight := G.height
        , tail := [G].filter fun x => decide (G.slot + 2 - n ≤ x.slot) } G.keyIndex
  | extend (cl : CertClaim) (g : Nat) (b : Block) :
      GroundedCertLock n Signed G cl g →
      b.height = cl.tipHeight + 1 →
      cl.tipSlot < b.slot →
      b.prev = some cl.tipId →
      Signed b →
      g ≤ b.keyIndex →
      (cl.tipSlot / n = b.slot / n → g = b.keyIndex) →
      (∀ u : Nat, cl.tipSlot + 2 ≤ u + n → u + n ≤ b.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ [b]) u n) →
      GroundedCertLock n Signed G
        { tipId := b.id, tipSlot := b.slot, tipHeight := b.height
        , tail := (cl.tail ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot) } b.keyIndex
end MoltPetit.Model
