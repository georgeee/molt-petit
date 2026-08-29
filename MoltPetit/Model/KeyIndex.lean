import MoltPetit.Model.Safety
import MoltPetit.Model.Soundness

/-!
# MoltPetit — consensus-maintained key index (in-band key rotation)

Every block carries a per-producer **delegate-key index** `keyIndex`
(`Definitions.lean`), and the verifier selects the public key as
`registry (producerForSlot n slot) keyIndex`. This module makes that index
*consensus state* and proves the two properties the extension promises:

* **(A) Soundness / no disagreement on the index.**
  - `deep_block_keyIndex_agreement` — two valid chains drawn from one
    execution record never disagree on the `keyIndex` of a finalized block
    (an immediate corollary of `deep_block_agreement`: the finalized block
    *is* the same block, so its index is the same).
  - `keyMonoOk_sound` — the in-band monotonicity rule the validator checks
    (`keyMonoOk`) entails the semantic `KeyIndexMonotone`: along a chain a
    producer's index never decreases. *No rollback within a chain.*
  - `keyFloor_le_extend` — the per-producer **floor** (highest index in
    force, read off the chain) never decreases as the chain grows.
    *No rollback across chain extension.*

  Together these make the floor a **distributed monotonic counter**, tied to
  the chain order rather than to an abstract event trace.

* **(B) Same security model.**
  - `validChainK_sound` — the indexed validator `validChainK` (structural
    validity *and* the monotone-index rule) is stronger than the
    original `validChain`: its accepted chains satisfy the very `ValidChain`
    the safety proof consumes. So `deep_block_agreement`, the forged-time
    bound, and liveness transport **verbatim** — adding the index weakens
    nothing.
  - `indexed_reduces_to_static` — fixing the floor `e`, versioned
    verification of a block signing under its current index equals
    verification under the *static, index-blind* directory `pinAt registry
    e`. Chain-connected: per settled state the indexed scheme **is** the
    original static-registry scheme.

See `KEY_INDEX_DESIGN.md`.
-/

namespace MoltPetit.Model

-- ===========================================================================
-- The in-band monotonicity rule and the derived floor
-- ===========================================================================

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

-- ===========================================================================
-- `foldl max` helpers
-- ===========================================================================

private theorem le_foldl_max (a : Nat) (L : List Nat) : a ≤ L.foldl max a := by
  induction L generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left a x) (ih (max a x))

private theorem mem_le_foldl_max (a : Nat) {x : Nat} {L : List Nat} (hx : x ∈ L) :
    x ≤ L.foldl max a := by
  induction L generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hxs
    · exact le_trans (le_max_right a x) (le_foldl_max (max a x) ys)
    · exact ih (max a y) hxs

private theorem foldl_max_append (a : Nat) (L₁ L₂ : List Nat) :
    L₁.foldl max a ≤ (L₁ ++ L₂).foldl max a := by
  rw [List.foldl_append]
  exact le_foldl_max _ L₂

-- ===========================================================================
-- (A) No rollback: the floor is a monotone counter
-- ===========================================================================

/-- **No rollback across chain growth.** Extending a chain never lowers any
participant's floor: the key-index state is a distributed monotone counter,
realized in consensus state and tied to the actual chain. -/
theorem keyFloor_le_extend (n : Nat) (c d : Chain) (i : Nat) :
    keyFloor n c i ≤ keyFloor n (c ++ d) i := by
  unfold keyFloor
  rw [List.filter_append, List.map_append]
  exact foldl_max_append 0 _ _

/-- Every block's index is at most its producer's floor — the floor is the
running maximum the consensus state maintains. -/
theorem block_keyIndex_le_floor (n : Nat) {c : Chain} {k : Nat} {B : Block}
    (h : blockAt? c k = some B) :
    B.keyIndex ≤ keyFloor n c (producerForSlot n B.slot) := by
  unfold keyFloor
  have hmem : B ∈ c := by
    rcases List.getElem?_eq_some_iff.mp h with ⟨hlt, hget⟩
    exact hget ▸ List.getElem_mem hlt
  apply mem_le_foldl_max
  apply List.mem_map.mpr
  exact ⟨B, List.mem_filter.mpr ⟨hmem, by simp⟩, rfl⟩

-- ===========================================================================
-- (A) The in-band rule is sound: `keyMonoOk` ⇒ `KeyIndexMonotone`
-- ===========================================================================

theorem keyMonoOk_iff_pairwise {n : Nat} (c : Chain) :
    keyMonoOk n c = true ↔
      c.Pairwise (fun a b => producerForSlot n a.slot = producerForSlot n b.slot →
        a.keyIndex ≤ b.keyIndex) := by
  induction c with
  | nil => simp [keyMonoOk]
  | cons b rest ih =>
    rw [keyMonoOk, Bool.and_eq_true, List.all_eq_true, List.pairwise_cons, ih]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun a ha => ?_, h2⟩
      have := h1 a ha
      rwa [decide_eq_true_eq] at this
    · rintro ⟨h1, h2⟩
      refine ⟨fun a ha => ?_, h2⟩
      rw [decide_eq_true_eq]
      exact h1 a ha

/-- **No rollback within a chain.** The validator's monotone-index check
entails that along the chain every producer's indices are non-decreasing. -/
theorem keyMonoOk_sound {n : Nat} {c : Chain} (h : keyMonoOk n c = true) :
    KeyIndexMonotone n c := by
  have hp := (keyMonoOk_iff_pairwise c).mp h
  rw [List.pairwise_iff_getElem] at hp
  intro i j B B' hB hB' hij hprod
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · -- same position: B = B'
    rw [hB] at hB'
    rw [Option.some.inj hB']
  · -- earlier position i < j
    obtain ⟨hiLen, hBi⟩ := List.getElem?_eq_some_iff.mp hB
    obtain ⟨hjLen, hB'j⟩ := List.getElem?_eq_some_iff.mp hB'
    have := hp i j hiLen hjLen hlt
    rw [hBi, hB'j] at this
    exact this hprod

-- ===========================================================================
-- (A) No disagreement on the index of a finalized block
-- ===========================================================================

/--
**No disagreement on the index.** Under the same operational assumptions as
the safety theorem, any two valid chains drawn from one execution record
carry the **same `keyIndex`** at every height whose block lies at least `n`
slots behind an observed block of both chains.

This is the key-index form of finality: once a block is `n`-deep, not only
the block but the signing-key index it commits is agreed across the whole
system. It is an immediate corollary of `deep_block_agreement` — the
finalized block *is* the same block.
-/
theorem deep_block_keyIndex_agreement
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hBudget : ByzantineBounded n bad)
    (hHonest : HonestSlotsUnique bad record)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hGenesis : CommonPrefixUpTo c c' 0)
    {k m m' : Nat} {B B' D D' : Block}
    (hB : blockAt? c k = some B) (hB' : blockAt? c' k = some B')
    (hD : blockAt? c m = some D) (hD' : blockAt? c' m' = some D')
    (hDeep : B.slot + n ≤ D.slot) (hDeep' : B.slot + n ≤ D'.slot) :
    B.keyIndex = B'.keyIndex :=
  congrArg Block.keyIndex
    (deep_block_agreement hn hBudget hHonest hId hValid hValid' hRec hRec'
      hGenesis hB hB' hD hD' hDeep hDeep')

-- ===========================================================================
-- (B) Same security model
-- ===========================================================================

/-- **The indexed validator is sound for the original model.** Any chain the
indexed validator accepts satisfies the semantic `ValidChain` consumed by the
safety proof, *and* is key-index monotone. So every original theorem stated
over `ValidChain` (light-client safety, forged-time, liveness) applies to
indexed chains unchanged — the index weakens nothing. -/
theorem validChainK_sound {n : Nat} {c : Chain} (h : validChainK n c = true) :
    ValidChain n c ∧ KeyIndexMonotone n c := by
  rw [validChainK, Bool.and_eq_true] at h
  exact ⟨validChain_sound h.1, keyMonoOk_sound h.2⟩

/-- The **static, index-blind** directory obtained by pinning each producer
at the index `e i` (its current floor). It ignores the per-block index — the
shape of the *original* model's per-producer registry. -/
def pinAt {pk : Type} (registry : KeyRegistry pk) (e : Nat → Nat) : KeyRegistry pk :=
  fun i _ => registry i (e i)

/--
**Reduction to the static registry (chain-connected).** For a fixed floor
`e`, a block signing under its producer's current index `e (producer)`
verifies under the versioned directory **iff** it verifies under the static,
index-blind directory `pinAt registry e`.

Instantiating `e := keyFloor n c` (the floor read off the settled chain),
this says the indexed scheme *is* the original static-registry scheme at each
settled state: the verifier collapses to a per-producer key lookup, so the
original `SigCorrect`/EUF-CMA assumptions and every theorem over them
transport verbatim — the reduction linked to the chain rather than to a free
floor. -/
theorem indexed_reduces_to_static {σ sk pk : Type} (n : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (e : Nat → Nat)
    (sb : SignedBlock σ)
    (h : sb.block.keyIndex = e (producerForSlot n sb.block.slot)) :
    sigOk n ops registry sb = sigOk n ops (pinAt registry e) sb := by
  simp only [sigOk, pinAt, h]

/-- The static pinned directory ignores the per-block index, so a whole
signed chain verifies identically under it and under the versioned directory,
provided every block signs under its producer's pinned index. This lifts
`indexed_reduces_to_static` from one block to a chain. -/
theorem sigsOk_reduces_to_static {σ sk pk : Type} (n : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (e : Nat → Nat)
    (sc : SignedChain σ)
    (h : ∀ sb ∈ sc, sb.block.keyIndex = e (producerForSlot n sb.block.slot)) :
    sigsOk n ops registry sc = sigsOk n ops (pinAt registry e) sc := by
  unfold sigsOk
  induction sc with
  | nil => rfl
  | cons sb rest ih =>
    rw [List.all_cons, List.all_cons,
      indexed_reduces_to_static n ops registry e sb (h sb (List.mem_cons_self ..)),
      ih (fun s hs => h s (List.mem_cons_of_mem _ hs))]

end MoltPetit.Model
