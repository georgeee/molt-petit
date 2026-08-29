import MoltPetit.Model.Model
import MoltPetit.Model.Safety

/-!
# MoltPetit — soundness of the executable validator

This module connects the executable validator `validChain` of
`Model/Definitions.lean` to the semantic predicate consumed by the safety
proof. Its result is:

* `validChain_sound` — a chain accepted by the executable validator
  satisfies the semantic `ValidChain` predicate.

The rest of the file is its helper lemmas, in two layers: boolean check
unfolding (`genesisOk_iff`, `childOk_iff`, `linksOk_isChain`) restates the
per-block checks as propositions, and the checks-to-semantics lemmas
(`isChain_adjacent`, `sequentialHeights_of_checks`, `strictSlots_of_checks`,
`parentLinked_of_checks`, `blockAt_getLast`, `maturedDense_of_check`) derive
each conjunct of `ValidChain` — `SequentialHeights`, `StrictSlots`,
`ParentLinked`, `MaturedWindowsDense` — from the accepted checks.
-/

namespace MoltPetit.Model

/-! ## Boolean check unfolding -/

theorem genesisOk_iff {b : Block} :
    genesisOk b = true ↔ b.height = 0 ∧ b.prev = none := by
  simp [genesisOk]

theorem childOk_iff {p b : Block} :
    childOk p b = true ↔
      b.height = p.height + 1 ∧ p.slot < b.slot ∧ b.prev = some p.id := by
  simp [childOk]

theorem linksOk_isChain :
    ∀ {ch : Chain}, linksOk ch = true →
      List.IsChain (fun a b => childOk a b = true) ch
  | [], _ => List.isChain_nil
  | [_], _ => List.isChain_singleton _
  | _ :: _ :: _, hOk => by
    rw [linksOk, Bool.and_eq_true] at hOk
    exact List.isChain_cons_cons.mpr ⟨hOk.1, linksOk_isChain hOk.2⟩

/-! ## From boolean checks to semantic predicates -/

/-- Adjacent-pair relation extracted at concrete indices. -/
theorem isChain_adjacent {ch : Chain}
    (hChain : List.IsChain (fun a b => childOk a b = true) ch)
    {k : Nat} {P B : Block}
    (hP : blockAt? ch k = some P) (hB : blockAt? ch (k + 1) = some B) :
    childOk P B = true := by
  unfold blockAt? at hP hB
  rcases List.getElem?_eq_some_iff.mp hP with ⟨hPLen, hPEq⟩
  rcases List.getElem?_eq_some_iff.mp hB with ⟨hBLen, hBEq⟩
  have := List.isChain_iff_getElem.mp hChain k hBLen
  rw [hPEq, hBEq] at this
  exact this

theorem sequentialHeights_of_checks {ch : Chain}
    (hHead : ∀ ⦃B : Block⦄, blockAt? ch 0 = some B → B.height = 0)
    (hChain : List.IsChain (fun a b => childOk a b = true) ch) :
    SequentialHeights ch := by
  intro k B hAt
  induction k generalizing B with
  | zero => exact hHead hAt
  | succ k ih =>
    obtain ⟨P, hP⟩ := exists_blockAt_of_le (Nat.le_succ k) hAt
    have hPh : P.height = k := ih hP
    have hAdj := isChain_adjacent hChain hP hAt
    have := (childOk_iff.mp hAdj).1
    omega

theorem strictSlots_of_checks {ch : Chain}
    (hChain : List.IsChain (fun a b => childOk a b = true) ch) :
    StrictSlots ch := by
  haveI : Trans (fun a b : Block => a.slot < b.slot)
      (fun a b : Block => a.slot < b.slot)
      (fun a b : Block => a.slot < b.slot) :=
    ⟨fun hab hbc => Nat.lt_trans hab hbc⟩
  exact List.isChain_iff_pairwise.mp
    (hChain.imp fun _ _ hab => (childOk_iff.mp hab).2.1)

theorem parentLinked_of_checks {ch : Chain}
    (hHead : ∀ ⦃B : Block⦄, blockAt? ch 0 = some B → B.prev = none)
    (hChain : List.IsChain (fun a b => childOk a b = true) ch) :
    ParentLinked ch := by
  intro k B hAt
  cases k with
  | zero => exact hHead hAt
  | succ k =>
    obtain ⟨P, hP⟩ := exists_blockAt_of_le (Nat.le_succ k) hAt
    have hAdj := isChain_adjacent hChain hP hAt
    exact ⟨P, hP, (childOk_iff.mp hAdj).2.2⟩

/-- The tip of a nonempty chain sits at index `length - 1`. -/
theorem blockAt_getLast {ch : Chain} {tip : Block}
    (hTip : ch.getLast? = some tip) :
    blockAt? ch (ch.length - 1) = some tip := by
  unfold blockAt?
  rw [← List.getLast?_eq_getElem?]
  exact hTip

theorem maturedDense_of_check {n : Nat} {ch : Chain}
    (hS : StrictSlots ch)
    {tip : Block} (hTip : ch.getLast? = some tip)
    (hCheck : maturedWindowsDense n ch tip.slot = true) :
    MaturedWindowsDense n ch := by
  intro m D hAt u hu
  have hTipAt := blockAt_getLast hTip
  -- every chain block is no later than the tip
  have hDle : D.slot ≤ tip.slot := by
    have hmLen : m < ch.length := by
      have := hAt
      unfold blockAt? at this
      exact (List.getElem?_eq_some_iff.mp this).1
    by_cases hEq : m = ch.length - 1
    · rw [hEq, hTipAt] at hAt
      injection hAt with hAtEq
      rw [hAtEq]
    · have hlt : m < ch.length - 1 := by omega
      exact Nat.le_of_lt (strictSlots_lt hS hAt hTipAt hlt)
  have hMem : u ∈ List.range (tip.slot + 2 - n) :=
    List.mem_range.mpr (by omega)
  have hDense := List.all_eq_true.mp hCheck u hMem
  simpa [windowDense] using hDense

/-- **Validator soundness**: chains accepted by the executable validator
satisfy the semantic validity predicate used by the safety theorem. -/
theorem validChain_sound {n : Nat} :
    ∀ {ch : Chain}, validChain n ch = true → ValidChain n ch := by
  intro ch h
  match ch with
  | [] =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k B hAt
      simp [blockAt?] at hAt
    · exact List.Pairwise.nil
    · intro k B hAt
      simp [blockAt?] at hAt
    · intro m D hAt
      simp [blockAt?] at hAt
  | g :: rest =>
    obtain ⟨tip, hTip⟩ : ∃ tip, (g :: rest).getLast? = some tip := by
      cases hL : (g :: rest).getLast? with
      | some t => exact ⟨t, rfl⟩
      | none => simp at hL
    rw [validChain, hTip, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hGen, hLinks⟩, hDense⟩ := h
    have hChain := linksOk_isChain hLinks
    have hAt0 : ∀ ⦃B : Block⦄, blockAt? (g :: rest) 0 = some B → B = g := by
      intro B hB
      unfold blockAt? at hB
      simp at hB
      exact hB.symm
    have hSeq : SequentialHeights (g :: rest) :=
      sequentialHeights_of_checks
        (fun B hB => (hAt0 hB) ▸ (genesisOk_iff.mp hGen).1) hChain
    have hS : StrictSlots (g :: rest) := strictSlots_of_checks hChain
    have hP : ParentLinked (g :: rest) :=
      parentLinked_of_checks
        (fun B hB => (hAt0 hB) ▸ (genesisOk_iff.mp hGen).2) hChain
    exact ⟨hSeq, hS, hP, maturedDense_of_check hS hTip hDense⟩

end MoltPetit.Model
