import Spec.Statements
import MoltPetit.Model.Definitions
import MoltPetit.Model.Liveness
import MoltPetit.Model.Grounded

namespace MoltPetit.Model

theorem linksOk_snoc : ∀ (c : Chain) (t b : Block),
    c.getLast? = some t →
    (linksOk (c ++ [b]) = true ↔ linksOk c = true ∧ childOk t b = true) := by
  intro c
  induction c with
  | nil =>
    intro t b hTip
    simp at hTip
  | cons x xs ih =>
    intro t b hTip
    cases xs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hTip
      subst hTip
      simp [linksOk]
    | cons y ys =>
      have hTip' : (y :: ys).getLast? = some t := hTip
      have ih' := ih t b hTip'
      simp only [List.cons_append, linksOk, Bool.and_eq_true]
      rw [← List.cons_append, ih']
      tauto

theorem childOk_slot_lt {t b : Block} (h : childOk t b = true) : t.slot < b.slot := by
  simp only [childOk, decide_eq_true_eq] at h
  exact h.2.1

theorem windowCount_snoc_of_le {c : Chain} {b : Block} {u n : Nat}
    (h : u + n ≤ b.slot) :
    windowCount (c ++ [b]) u n = windowCount c u n := by
  apply windowCount_append_high
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact h

theorem maturedWindowsDense_iff {n : Nat} (_hn : 1 ≤ n) {c : Chain} {t : Nat} :
    maturedWindowsDense n c t = true ↔
      ∀ u : Nat, u + n ≤ t + 1 → quorum n ≤ windowCount c u n := by
  rw [maturedWindowsDense, List.all_eq_true]
  constructor
  · intro h u hu
    have hu' : u ∈ List.range (t + 2 - n) := by
      rw [List.mem_range]
      omega
    have hDense := h u hu'
    simp only [windowDense, decide_eq_true_eq] at hDense
    exact hDense
  · intro h u hu
    rw [List.mem_range] at hu
    have hu' : u + n ≤ t + 1 := by omega
    have hCount := h u hu'
    simp only [windowDense, decide_eq_true_eq]
    exact hCount

theorem validChain_snoc : MoltPaper.thm_validChain_snoc := by
  intro n hn c t b hTip
  obtain ⟨g, rest, rfl⟩ : ∃ g rest, c = g :: rest := by
    cases c with
    | nil => simp at hTip
    | cons g rest => exact ⟨g, rest, rfl⟩
  have hLastC : (g :: rest).getLast? = some t := hTip
  have hLastCB : ((g :: rest) ++ [b]).getLast? = some b := by
    exact List.getLast?_concat
  have hValidC : validChain n (g :: rest) = true ↔
      (genesisOk g = true ∧ linksOk (g :: rest) = true ∧
       maturedWindowsDense n (g :: rest) t.slot = true) := by
    dsimp [validChain]
    rw [hLastC]
    simp only [Bool.and_eq_true, and_assoc]
  have hValidCB : validChain n ((g :: rest) ++ [b]) = true ↔
      (genesisOk g = true ∧ linksOk ((g :: rest) ++ [b]) = true ∧
       maturedWindowsDense n ((g :: rest) ++ [b]) b.slot = true) := by
    change validChain n (g :: (rest ++ [b])) = true ↔ _
    dsimp [validChain]
    have hLast : (g :: (rest ++ [b])).getLast? = some b := hLastCB
    rw [hLast]
    simp only [Bool.and_eq_true, and_assoc]
  rw [hValidCB]
  rw [linksOk_snoc (g :: rest) t b hTip]
  rw [maturedWindowsDense_iff hn]
  constructor
  · intro ⟨hGen, ⟨hLinks, hChild⟩, hDenseB⟩
    have hSlotLt : t.slot < b.slot := childOk_slot_lt hChild
    have hDenseC : ∀ u : Nat, u + n ≤ t.slot + 1 → quorum n ≤ windowCount (g :: rest) u n := by
      intro u hu
      have huB : u + n ≤ b.slot + 1 := by omega
      have hCountB := hDenseB u huB
      have hLe : u + n ≤ b.slot := by omega
      rw [windowCount_snoc_of_le hLe] at hCountB
      exact hCountB
    refine ⟨hValidC.mpr ⟨hGen, hLinks, (maturedWindowsDense_iff hn).mpr hDenseC⟩, hChild, ?_⟩
    intro u huT huB
    exact hDenseB u huB
  · intro ⟨hValC, hChild, hNewDense⟩
    obtain ⟨hGen, hLinks, hDenseC_bool⟩ := hValidC.mp hValC
    have hDenseC := (maturedWindowsDense_iff hn).mp hDenseC_bool
    have hSlotLt : t.slot < b.slot := childOk_slot_lt hChild
    refine ⟨hGen, ⟨hLinks, hChild⟩, ?_⟩
    intro u huB
    by_cases huT : u + n ≤ t.slot + 1
    · have hLe : u + n ≤ b.slot := by omega
      rw [windowCount_snoc_of_le hLe]
      exact hDenseC u huT
    · have huT2 : t.slot + 2 ≤ u + n := by omega
      exact hNewDense u huT2 huB

end MoltPetit.Model
