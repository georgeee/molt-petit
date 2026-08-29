import MoltPetit.Model.Definitions


/-!
# MoltPetit — semantic model

Proof-level predicates over the executable types of
`MoltPetit.Model.Impl`. The safety theorem in `Model/Safety.lean` is stated
purely in terms of these predicates; `Model/Soundness.lean` shows that the
executable validator implies the chain-level ones.

The environment-level assumptions (slot record, Byzantine budget, honest
slot uniqueness, id injectivity) model the deployment:

* `SlotRecord` — for each slot, the finite set of blocks that were ever
  produced in that slot, by anyone;
* `bad : ByzantineSlots` — the slots the adversary controls; in a bad slot
  the record is arbitrary (multiple blocks, malformed blocks, nothing);
* `ByzantineBounded` — the adversary controls at most `⌊(n-1)/3⌋` slots in
  any window of `n` consecutive slots (this covers both static one-third
  Byzantine participants under round-robin, and a dynamic adversary that
  picks fresh slots subject to the same per-window budget);
* `HonestSlotsUnique` — an honest slot contains at most one block: the
  honest producer signs exactly one block for its slot and signatures
  cannot be forged;
* `IdInjective` — block ids are collision-resistant hashes;
* `ChainInRecord` — chains observed in the system consist of blocks that
  were actually produced.
-/

namespace MoltPetit.Model

/-! ## Basic lemmas about the model -/

theorem mem_chainSlotsIn {c : Chain} {u len s : Nat} :
    s ∈ chainSlotsIn c u len ↔
      ∃ B : Block, B ∈ c ∧ (u ≤ B.slot ∧ B.slot < u + len) ∧ B.slot = s := by
  simp [chainSlotsIn, List.mem_filter, blockInWindow, and_assoc]

theorem chainSlotsIn_subset_Ico {c : Chain} {u len : Nat} :
    chainSlotsIn c u len ⊆ Finset.Ico u (u + len) := by
  intro s hs
  rcases mem_chainSlotsIn.mp hs with ⟨B, _, hWin, hSlot⟩
  exact Finset.mem_Ico.mpr (by omega)

/-- Index-based form of strict slot monotonicity. -/
theorem strictSlots_lt {c : Chain} (hS : StrictSlots c)
    {i j : Nat} {Bi Bj : Block}
    (hi : blockAt? c i = some Bi) (hj : blockAt? c j = some Bj)
    (hij : i < j) : Bi.slot < Bj.slot := by
  unfold blockAt? at hi hj
  rcases List.getElem?_eq_some_iff.mp hi with ⟨hiLen, hiEq⟩
  rcases List.getElem?_eq_some_iff.mp hj with ⟨hjLen, hjEq⟩
  have := (List.pairwise_iff_getElem.mp hS) i j hiLen hjLen hij
  simpa [hiEq, hjEq] using this

/-- On a strictly-slot-increasing chain, distinct list elements have distinct
slots, so the slot multiset inside a window has no duplicates and its card
equals the window count. -/
theorem chainSlotsIn_card {c : Chain} (hS : StrictSlots c) (u len : Nat) :
    (chainSlotsIn c u len).card = windowCount c u len := by
  have hPairFilter : (c.filter (blockInWindow u len)).Pairwise
      fun a b => a.slot < b.slot := hS.filter _
  have hNodup : ((c.filter (blockInWindow u len)).map Block.slot).Nodup := by
    refine List.Pairwise.map Block.slot (fun a b hab => ?_) hPairFilter
    exact Nat.ne_of_lt hab
  rw [chainSlotsIn, windowCount, List.toFinset_card_of_nodup hNodup,
    List.length_map]

/-- A chain member sits at the index given by its position. -/
theorem exists_blockAt_of_mem {c : Chain} {B : Block} (hB : B ∈ c) :
    ∃ k, blockAt? c k = some B := by
  rcases List.mem_iff_getElem.mp hB with ⟨k, hk, hEq⟩
  refine ⟨k, ?_⟩
  unfold blockAt?
  rw [List.getElem?_eq_getElem hk, hEq]

/-- If a chain contains a block at height `m`, it contains every earlier height. -/
theorem exists_blockAt_of_le {c : Chain} {k m : Nat} (hk : k ≤ m)
    {D : Block} (hAt : blockAt? c m = some D) :
    ∃ C : Block, blockAt? c k = some C := by
  unfold blockAt? at hAt ⊢
  rcases List.getElem?_eq_some_iff.mp hAt with ⟨hmLen, _⟩
  have hkLen : k < c.length := lt_of_le_of_lt hk hmLen
  exact ⟨_, List.getElem?_eq_getElem hkLen⟩

/-- `LastCommonHeight` is symmetric. -/
theorem LastCommonHeight.symm {c c' : Chain} {h : Nat}
    (hL : LastCommonHeight c c' h) : LastCommonHeight c' c h := by
  refine ⟨fun k hk => ?_, fun k hk B hB => hL.2 k hk B ⟨hB.2, hB.1⟩⟩
  rcases hL.1 k hk with ⟨B, hB, hB'⟩
  exact ⟨B, hB', hB⟩

/-- Core arithmetic fact: two quorums overlap beyond the Byzantine budget. -/
theorem quorum_overlap {n : Nat} (hn : 1 ≤ n) :
    n + maxByzantine n < 2 * quorum n := by
  unfold maxByzantine quorum
  omega

end MoltPetit.Model
