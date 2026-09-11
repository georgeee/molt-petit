import MoltPetit.Model.KeyStealingScheduleHorizon

/-!
# MoltPetit — the aligned-window contraction engine (validator-agnostic)

The generalisation `KeyStealingScheduleHorizon.lean`'s `horizon_shared_prefix`
asked for: the pigeonhole run at an ARBITRARY window `u` matured in both
chains, with honest-slot uniqueness required only on that window
(`HonestSlotsUniqueOn`), rather than the fixed trailing window
`tip.slot + 1 − n`. `horizon_shared_prefix` is the special case
`u := tip.slot + 1 − n`; this module's `window_shared_prefix` is what mode
3's per-generation census (W5) needs, since the corruption predicate it
consumes (`badLockAt`) is sound only on windows pinned to one generation, not
on the trailing sliding window (which may straddle the unmatured tip window
where the two chains disagree on generation).

Validator-agnostic and mode-agnostic: no `Sig`/`ops`/`registry`, no schedule,
no lockstep-specific vocabulary anywhere in this file. `horizon_shared_prefix`
itself is untouched; `horizon_shared_prefix_of_window` records it as the
`u := tip.slot + 1 − n` instance of the new engine.
-/

namespace MoltPetit.Model

-- ===========================================================================
-- (1) Honest-slot uniqueness on one window
-- ===========================================================================

/-- Honest-slot uniqueness, required only on the slots of one window
`[u, u + len)`. `HonestSlotsUnique` is the everywhere form;
`honestSlotsUniqueOn_of_unique` recovers this at any `u`, `len`. What this
buys: a corruption predicate that is sound only on windows pinned to one
value (mode 3's per-generation `badLockAt`) can still be consumed by the
engine, since the engine never asks for uniqueness anywhere else. -/
def HonestSlotsUniqueOn (u len : Nat) (bad : ByzantineSlots) (record : SlotRecord) : Prop :=
  ∀ s, u ≤ s → s < u + len → ¬ bad s →
    ∀ ⦃B B' : Block⦄, B ∈ record s → B' ∈ record s → B = B'

theorem honestSlotsUniqueOn_of_unique {u len : Nat} {bad : ByzantineSlots}
    {record : SlotRecord} (h : HonestSlotsUnique bad record) :
    HonestSlotsUniqueOn u len bad record :=
  fun s _ _ hbad => h s hbad

-- ===========================================================================
-- (2) Public copies of the two private KeyStealingScheduleHorizon helpers
-- ===========================================================================

/-- `exists_honest_shared_slot_at` with a public name: the single-window
pigeonhole, budget consumed only at the window it is applied to. Verbatim
copy of the private helper at `KeyStealingScheduleHorizon.lean:86` — a new
module cannot see a `private` declaration in another file, so this is not a
rename, it is a fresh public proof of the same statement. -/
theorem exists_honest_shared_slot_at_win
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {u : Nat}
    (hBudgetU : (badSlotsIn bad u n).card ≤ maxByzantine n)
    {S S' : Finset Nat}
    (hS : S ⊆ Finset.Ico u (u + n)) (hS' : S' ⊆ Finset.Ico u (u + n))
    (hCard : quorum n ≤ S.card) (hCard' : quorum n ≤ S'.card) :
    ∃ s, s ∈ S ∧ s ∈ S' ∧ ¬ bad s := by
  classical
  have hIcoCard : (Finset.Ico u (u + n)).card = n := by
    rw [Nat.card_Ico]
    omega
  have hUnion : (S ∪ S').card ≤ n := by
    calc (S ∪ S').card ≤ (Finset.Ico u (u + n)).card :=
          Finset.card_le_card (Finset.union_subset hS hS')
      _ = n := hIcoCard
  have hSum := Finset.card_union_add_card_inter S S'
  have hOverlap := quorum_overlap hn
  have hInter : maxByzantine n < (S ∩ S').card := by omega
  by_contra hNo
  push Not at hNo
  have hSub : S ∩ S' ⊆ badSlotsIn bad u n := by
    intro s hs
    have hsS := Finset.mem_inter.mp hs
    exact Finset.mem_filter.mpr ⟨hS hsS.1, hNo s hsS.1 hsS.2⟩
  have hLe : (S ∩ S').card ≤ (badSlotsIn bad u n).card := Finset.card_le_card hSub
  omega

/-- `slot_gap_of_position_gap` with a public name: along a strict-slot chain,
`d` positions apart means at least `d` slots apart. Verbatim copy of the
private helper at `KeyStealingScheduleHorizon.lean:116`. -/
theorem slot_gap_of_position_gap_win {c : Chain} (hS : StrictSlots c) :
    ∀ (d p : Nat) {X Y : Block}, blockAt? c p = some X →
      blockAt? c (p + d) = some Y → X.slot + d ≤ Y.slot := by
  intro d
  induction d with
  | zero =>
    intro p X Y hX hY
    rw [Nat.add_zero, hX] at hY
    injection hY with hEq
    subst hEq
    omega
  | succ d ih =>
    intro p X Y hX hY
    have hYlt : p + d + 1 < c.length := by
      unfold blockAt? at hY
      obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hY
      exact h
    obtain ⟨Z, hZ⟩ : ∃ Z, blockAt? c (p + d) = some Z := by
      cases hopt : blockAt? c (p + d) with
      | none =>
        unfold blockAt? at hopt
        have := List.getElem?_eq_none_iff.mp hopt
        omega
      | some Z => exact ⟨Z, rfl⟩
    have h1 := ih p hX hZ
    have h2 : Z.slot < Y.slot :=
      strictSlots_lt hS hZ hY (by omega)
    omega

-- ===========================================================================
-- (3) The aligned-window contraction
-- ===========================================================================

/-- **Aligned-window shared prefix.** Two valid chains from one execution
record, with an ARBITRARY window `u` matured in both (`hMat`/`hMat'`), and
honest-slot uniqueness required only on that window: they share their block
at every height whose slot is below `u`. `horizon_shared_prefix` is the
special case `u := tip.slot + 1 − n`; this is its generalisation with the
slot-gap step dropped (the caller supplies `hBu` directly instead of
deriving it from a fixed trailing-window computation), so a per-generation
corruption predicate — sound only on windows pinned to one generation — can
be consumed at whichever window is actually pinned. -/
theorem window_shared_prefix
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord} {u : Nat}
    (hHonest : HonestSlotsUniqueOn u n bad record)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    {tip tip' : Block} (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hMat : u + n ≤ tip.slot + 1) (hMat' : u + n ≤ tip'.slot + 1)
    (hBudgetU : (badSlotsIn bad u n).card ≤ maxByzantine n)
    {k : Nat} {B : Block} (hB : blockAt? c k = some B) (hBu : B.slot < u) :
    ∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P := by
  obtain ⟨hSeq, hS, hPL, hDense⟩ := hValid
  obtain ⟨hSeq', hS', hPL', hDense'⟩ := hValid'
  have hTipAt : blockAt? c (c.length - 1) = some tip := blockAt_getLast hTip
  have hTipAt' : blockAt? c' (c'.length - 1) = some tip' := blockAt_getLast hTip'
  have hq : quorum n ≤ (chainSlotsIn c u n).card := by
    rw [chainSlotsIn_card hS]
    exact hDense hTipAt u (by omega)
  have hq' : quorum n ≤ (chainSlotsIn c' u n).card := by
    rw [chainSlotsIn_card hS']
    exact hDense' hTipAt' u (by omega)
  obtain ⟨s, hsC, hsC', hsHonest⟩ :=
    exists_honest_shared_slot_at_win hn hBudgetU
      chainSlotsIn_subset_Ico chainSlotsIn_subset_Ico hq hq'
  obtain ⟨B₁, hB₁mem, hB₁win, hB₁slot⟩ := mem_chainSlotsIn.mp hsC
  obtain ⟨B₂, hB₂mem, hB₂win, hB₂slot⟩ := mem_chainSlotsIn.mp hsC'
  obtain ⟨k₁, hk₁⟩ := exists_blockAt_of_mem hB₁mem
  obtain ⟨k₂, hk₂⟩ := exists_blockAt_of_mem hB₂mem
  have hB₁rec : B₁ ∈ record s := by rw [← hB₁slot]; exact hRec hk₁
  have hB₂rec : B₂ ∈ record s := by rw [← hB₂slot]; exact hRec' hk₂
  have hsu : u ≤ s := (Finset.mem_Ico.mp (chainSlotsIn_subset_Ico hsC)).1
  have hsun : s < u + n := (Finset.mem_Ico.mp (chainSlotsIn_subset_Ico hsC)).2
  have hBeq : B₁ = B₂ := hHonest s hsu hsun hsHonest hB₁rec hB₂rec
  have hkk : k₁ = k₂ := by
    have h₁ := hSeq hk₁
    have h₂ := hSeq' hk₂
    rw [hBeq] at h₁
    omega
  have hk_lt : k < k₁ :=
    height_gt_of_slot_gt hS hB hk₁ (by omega)
  have hk₂' : blockAt? c' k₁ = some B₁ := by rw [hkk, hBeq]; exact hk₂
  exact same_block_same_prefix hId hRec hRec' hPL hPL' hk₁ hk₂' (Nat.le_of_lt hk_lt)

/-- A strict-slot chain's tip slot is at least its length minus one: the
length-`(m+1)` chain has `m` strict slot-increments above the head. Used to
establish the `2n`-depth headline's window is well-formed (`(sTip.slot+1)/n
≥ 2` once `2n < length`). -/
theorem chain_length_le_tip_slot {c : Chain} (hS : StrictSlots c) {tip : Block}
    (hTip : c.getLast? = some tip) :
    c.length - 1 ≤ tip.slot := by
  obtain ⟨B0, hB0⟩ : ∃ B0, blockAt? c 0 = some B0 := by
    cases hopt : blockAt? c 0 with
    | none =>
      unfold blockAt? at hopt
      have := List.getElem?_eq_none_iff.mp hopt
      have hlen : c.length ≠ 0 := by
        intro hz
        have hce : c = [] := List.length_eq_zero_iff.mp hz
        rw [hce] at hTip
        simp at hTip
      omega
    | some X => exact ⟨X, rfl⟩
  have hTipAt : blockAt? c (c.length - 1) = some tip := blockAt_getLast hTip
  have := slot_gap_of_position_gap_win hS (c.length - 1) 0
    (by simpa using hB0) (by simpa using hTipAt)
  omega

/-- The old fixed-trailing-window `horizon_shared_prefix` is the `u :=
tip.slot + 1 − n` instance of `window_shared_prefix`: a formal reduction
recording that the new engine strictly generalises the old one. -/
theorem horizon_shared_prefix_of_window
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hHonest : HonestSlotsUnique bad record)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    {tip tip' : Block} (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hle : tip.slot ≤ tip'.slot)
    (hBudgetU : (badSlotsIn bad (tip.slot + 1 - n) n).card ≤ maxByzantine n)
    {k : Nat} (hkdeep : k + n < c.length) :
    ∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P := by
  obtain ⟨B, hB⟩ : ∃ B, blockAt? c k = some B := by
    cases hopt : blockAt? c k with
    | none =>
      unfold blockAt? at hopt
      have := List.getElem?_eq_none_iff.mp hopt
      omega
    | some X => exact ⟨X, rfl⟩
  have hgap : B.slot + n ≤ tip.slot :=
    have hstep := slot_gap_of_position_gap_win hValid.2.1 (c.length - 1 - k) k hB
      (by rw [show k + (c.length - 1 - k) = c.length - 1 by omega]; exact blockAt_getLast hTip)
    by omega
  exact window_shared_prefix hn (honestSlotsUniqueOn_of_unique hHonest) hId hValid hValid'
    hRec hRec' hTip hTip' (by omega) (by omega) hBudgetU hB (by omega)

end MoltPetit.Model
