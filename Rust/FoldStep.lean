import Rust.Equiv
import MoltPetit.TS.Bridge
import Spec.Model

open Aeneas Std Result
namespace Rust
open molt_petit

/-- `BackendK.select` reduces to the conditional on `U64`. -/
theorem ubk_select (c : Bool) (a b : U64) :
    ∃ z : U64, UBK.select () c a b = ok z ∧ z.val = (if c then a.val else b.val) := by
  cases c
  · exact ⟨b, rfl, rfl⟩
  · exact ⟨a, rfl, rfl⟩

theorem ubk_select_val {c : Bool} {a b z : U64} (h : UBK.select () c a b = ok z) :
    z.val = (if c then a.val else b.val) := by
  cases c
  · injection h with h; subst h; rfl
  · injection h with h; subst h; rfl

/-- `BackendK.div` reduces to Nat division when the divisor is nonzero. -/
theorem ubk_div (a d : U64) (hd : d.val ≠ 0) :
    ∃ z : U64, UBK.div () a d = ok z ∧ z.val = a.val / d.val := by
  have ⟨z, hz, hzv⟩ := UScalar.div_spec a hd
  exact ⟨z, hz, hzv⟩

theorem ubk_div_val {a d z : U64} (hd : d.val ≠ 0) (h : UBK.div () a d = ok z) :
    z.val = a.val / d.val := by
  obtain ⟨z', hz', hzv⟩ := ubk_div a d hd
  rw [hz'] at h
  injection h with h
  subst h
  exact hzv

/-- `BackendK.rem` reduces to Nat remainder when the divisor is nonzero. -/
theorem ubk_rem (a d : U64) (hd : d.val ≠ 0) :
    ∃ z : U64, UBK.rem () a d = ok z ∧ z.val = a.val % d.val := by
  have hrem := UScalar.rem_spec a hd
  cases hres : a % d with
  | ok z =>
    rw [hres] at hrem
    exact ⟨z, hres, hrem⟩
  | fail e =>
    rw [hres] at hrem
    contradiction
  | div =>
    rw [hres] at hrem
    contradiction

theorem ubk_rem_val {a d z : U64} (hd : d.val ≠ 0) (h : UBK.rem () a d = ok z) :
    z.val = a.val % d.val := by
  obtain ⟨z', hz', hzv⟩ := ubk_rem a d hd
  rw [hz'] at h
  injection h with h
  subst h
  exact hzv

/-- `BackendK.monus` gives `a.val - b.val` in Nat. -/
theorem ubk_monus (a b : U64) :
    ∃ z : U64, UBK.monus () a b = ok z ∧ z.val = a.val - b.val := by
  change ∃ z : U64, (if a < b then ok 0#u64 else a - b) = ok z ∧ z.val = a.val - b.val
  split_ifs with hlt
  · refine ⟨0#u64, rfl, ?_⟩
    have : a.val < b.val := by simpa using hlt
    have : (0#u64).val = 0 := rfl
    omega
  · have hge : ¬ a.val < b.val := by
      intro h
      have : a < b := by simpa using h
      contradiction
    have hsub := UScalar.sub_equiv a b
    cases hs : a - b with
    | ok z =>
      rw [hs] at hsub
      refine ⟨z, rfl, ?_⟩
      omega
    | fail e =>
      rw [hs] at hsub
      contradiction
    | div =>
      rw [hs] at hsub
      exact False.elim hsub

theorem ubk_monus_val {a b z : U64} (h : UBK.monus () a b = ok z) :
    z.val = a.val - b.val := by
  obtain ⟨z', hz', hzv⟩ := ubk_monus a b
  rw [hz'] at h
  injection h with h
  subst h
  exact hzv

/-- The slots of entries whose flag is `1`, in order. -/
def presentSlots : TailG U64 → List Nat
  | .TNil => []
  | .TCons f s tl =>
    if f.val = 1 then s.val :: presentSlots tl else presentSlots tl

@[simp] theorem presentSlots_nil : presentSlots (.TNil : TailG U64) = [] := rfl

@[simp] theorem presentSlots_cons (f s : U64) (tl : TailG U64) :
    presentSlots (.TCons f s tl) =
      if f.val = 1 then s.val :: presentSlots tl else presentSlots tl := rfl

attribute [local simp]
  U64Backend.Insts.Molt_petitBackendU64Bool
  U64Backend.Insts.Molt_petitBackendU64Bool.zero
  U64Backend.Insts.Molt_petitBackendU64Bool.one
  U64Backend.Insts.Molt_petitBackendU64Bool.add
  U64Backend.Insts.Molt_petitBackendU64Bool.lt
  U64Backend.Insts.Molt_petitBackendU64Bool.eq
  U64Backend.Insts.Molt_petitBackendU64Bool.and
  U64Backend.Insts.Molt_petitBackendU64Bool.or
  U64Backend.Insts.Molt_petitBackendU64Bool.not
  U64Backend.Insts.Molt_petitBackendU64Bool.bool_const
  U64Backend.Insts.Molt_petitBackendU64Bool.bool_to_num

theorem tail_count_be_corr : ∀ (t : TailG U64) (u len : U64) {w : U64},
    tail_count_be UB () t u len = ok w →
    w.val = ((presentSlots t).filter (fun s => u.val ≤ s ∧ s < u.val + len.val)).length := by
  intro t
  induction t with
  | TNil =>
    intro u len w h
    simp only [tail_count_be, UB, U64Backend.Insts.Molt_petitBackendU64Bool.zero] at h
    injection h with h
    subst h
    rfl
  | TCons f s tl ih =>
    intro u len w h
    simp only [tail_count_be, UB] at h
    simp at h
    obtain ⟨hi, hhi, h⟩ := bind_inv h
    obtain ⟨inw, hinw, h⟩ := bind_inv h
    obtain ⟨counted, hcounted, h⟩ := bind_inv h
    obtain ⟨here, hhere, h⟩ := bind_inv h
    obtain ⟨rest, hrest, h⟩ := bind_inv h
    have hrv := ih u len hrest
    have hwv : w.val = here.val + rest.val := by
      have := UScalar.add_equiv here rest; simp only [h] at this; exact this.2.1
    have hhiv : hi.val = u.val + len.val := by
      have := UScalar.add_equiv u len; simp only [hhi] at this; exact this.2.1
    have hcond :
        ((f.val = 1 ∧ u.val ≤ s.val ∧ s.val < u.val + len.val) ∧ here = 1#u64)
      ∨ (¬ (f.val = 1 ∧ u.val ≤ s.val ∧ s.val < u.val + len.val) ∧ here = 0#u64) := by
      split at hcounted
      · rename_i hf; injection hcounted with hcounted; subst counted
        split at hinw
        · rename_i hle; injection hinw with hinw; subst inw
          split at hhere
          · rename_i hlt; injection hhere with hhere
            left
            have hfv : f.val = 1 := by rw [hf]; rfl
            have hsv : s.val < hi.val := by simpa using hlt
            rw [hhiv] at hsv
            have hlev : u.val ≤ s.val := by simpa using hle
            exact ⟨⟨hfv, hlev, hsv⟩, hhere.symm⟩
          · rename_i hlt; injection hhere with hhere
            right
            refine ⟨?_, hhere.symm⟩
            rintro ⟨_, _, h2⟩
            have : ¬ (s.val < hi.val) := by simpa using hlt
            rw [hhiv] at this; exact this h2
        · rename_i hle; injection hinw with hinw; subst inw
          simp only [Bool.false_eq_true, if_false] at hhere
          injection hhere with hhere
          right
          refine ⟨?_, hhere.symm⟩
          rintro ⟨_, h1, _⟩
          have : ↑u ≤ ↑s := by simpa using h1
          exact hle this
      · rename_i hf; injection hcounted with hcounted; subst counted
        simp only [Bool.false_eq_true, if_false] at hhere
        injection hhere with hhere
        right
        refine ⟨?_, hhere.symm⟩
        rintro ⟨h1, _, _⟩
        have : f = 1#u64 := UScalar.eq_of_val_eq (by rw [h1]; rfl)
        exact hf this
    rcases hcond with ⟨⟨hf1, hu, hs⟩, he⟩ | ⟨hnot, he⟩
    · subst he
      have : (1#u64 : U64).val = 1 := rfl
      rw [this] at hwv
      rw [hwv, hrv]
      simp only [presentSlots_cons, hf1, if_true, List.filter_cons]
      have hcond_true : (decide (u.val ≤ s.val ∧ s.val < u.val + len.val)) = true := by
        simp only [decide_eq_true_eq]
        exact ⟨hu, hs⟩
      simp only [hcond_true, if_true, List.length_cons]
      omega
    · subst he
      have : (0#u64 : U64).val = 0 := rfl
      rw [this] at hwv
      rw [hwv, Nat.zero_add, hrv]
      simp only [presentSlots_cons]
      split_ifs with hf1
      · simp only [List.filter_cons]
        have hcond_false : (decide (u.val ≤ s.val ∧ s.val < u.val + len.val)) = false := by
          simp only [decide_eq_false_iff_not]
          intro hand
          exact hnot ⟨hf1, hand⟩
        simp only [hcond_false, Bool.false_eq_true, if_false]
      · rfl

/-- All entry slots of a buffer, present or not. -/
def entrySlots : TailG U64 → List Nat
  | .TNil => []
  | .TCons _ s tl => s.val :: entrySlots tl

@[simp] theorem entrySlots_nil : entrySlots (.TNil : TailG U64) = [] := rfl

@[simp] theorem entrySlots_cons (f s : U64) (tl : TailG U64) :
    entrySlots (.TCons f s tl) = s.val :: entrySlots tl := rfl

theorem mem_entrySlots_of_mem_presentSlots {t : TailG U64} {s : Nat}
    (h : s ∈ presentSlots t) : s ∈ entrySlots t := by
  induction t with
  | TNil => simp at h
  | TCons f s' tl ih =>
    simp only [presentSlots_cons] at h
    simp only [entrySlots_cons]
    split at h
    · rcases List.mem_cons.mp h with rfl | htl
      · exact .head _
      · exact .tail _ (ih htl)
    · exact .tail _ (ih h)


theorem fold_window_ok_be_sound {tail : TailG U64} {tip_slot slot u n q : U64}
    (h : fold_window_ok_be UB () tail tip_slot slot u n q = ok true)
    (hlo : tip_slot.val + 2 ≤ u.val + n.val)
    (hhi : u.val + n.val ≤ slot.val + 1) :
    q.val ≤ ((presentSlots tail).filter (fun s => u.val ≤ s ∧ s < u.val + n.val)).length +
      (if u.val ≤ slot.val ∧ slot.val < u.val + n.val then 1 else 0) := by
  simp only [fold_window_ok_be, UB] at h
  simp at h
  obtain ⟨un, hun, h⟩ := bind_inv h
  obtain ⟨t1, ht1, h⟩ := bind_inv h
  obtain ⟨ts2, hts2, h⟩ := bind_inv h
  obtain ⟨s1, hs1, h⟩ := bind_inv h
  obtain ⟨checked, hchecked, h⟩ := bind_inv h
  obtain ⟨in_tail, hin_tail, h⟩ := bind_inv h
  obtain ⟨b_in, hb_in, h⟩ := bind_inv h
  obtain ⟨t2, ht2, h⟩ := bind_inv h
  obtain ⟨cnt, hcnt, h⟩ := bind_inv h
  have hunv : un.val = u.val + n.val := by
    have := UScalar.add_equiv u n; simp only [hun] at this; exact this.2.1
  have ht1v : t1.val = 2 := by
    have := UScalar.add_equiv 1#u64 1#u64; simp only [ht1] at this; exact this.2.1
  have hts2v : ts2.val = tip_slot.val + 2 := by
    have := UScalar.add_equiv tip_slot t1; simp only [hts2] at this; omega
  have hs1v : s1.val = slot.val + 1 := by
    have := UScalar.add_equiv slot 1#u64; simp only [hs1] at this; exact this.2.1
  have hchecked_true : checked = true := by
    split at hchecked
    · rename_i hle
      injection hchecked with hchecked
      subst checked
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]
      omega
    · rename_i hnle
      exfalso
      have : ↑ts2 ≤ ↑un := by
        change ts2.val ≤ un.val
        omega
      exact hnle this
  subst hchecked_true
  simp only [Bool.true_eq_false, if_false] at h
  injection h with h
  have hqle : q.val ≤ cnt.val := by
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at h
    exact h
  have hcntv : cnt.val = in_tail.val + t2.val := by
    have := UScalar.add_equiv in_tail t2; simp only [hcnt] at this; exact this.2.1
  have hintv : in_tail.val = ((presentSlots tail).filter (fun s => u.val ≤ s ∧ s < u.val + n.val)).length :=
    tail_count_be_corr tail u n hin_tail
  have ht2v : t2.val = if u.val ≤ slot.val ∧ slot.val < u.val + n.val then 1 else 0 := by
    split at hb_in
    · rename_i hle
      injection hb_in with hb_in
      subst b_in
      cases hbin : decide (slot.val < un.val) with
      | true =>
        simp only [hbin, if_true] at ht2
        injection ht2 with ht2
        subst t2
        have : (1#u64 : U64).val = 1 := rfl
        rw [this]
        have h1 : u.val ≤ slot.val := by change u.val ≤ slot.val at hle; exact hle
        have h2 : slot.val < u.val + n.val := by
          simp only [decide_eq_true_eq] at hbin
          omega
        simp only [h1, h2, and_self, if_true]
      | false =>
        simp only [hbin, Bool.false_eq_true, if_false] at ht2
        injection ht2 with ht2
        subst t2
        have : (0#u64 : U64).val = 0 := rfl
        rw [this]
        simp only [decide_eq_false_iff_not] at hbin
        have : ¬ (slot.val < u.val + n.val) := by omega
        simp only [this, and_false, if_false]
    · rename_i hnle
      injection hb_in with hb_in
      subst b_in
      simp only [Bool.false_eq_true, if_false] at ht2
      injection ht2 with ht2
      subst t2
      have : (0#u64 : U64).val = 0 := rfl
      rw [this]
      have : ¬ (u.val ≤ slot.val) := by
        intro hu
        have : ↑u ≤ ↑slot := hu
        exact hnle this
      simp only [this, false_and, if_false]
  omega


theorem fold_anchors_ok_be_sound {all rest : TailG U64} {tip_slot slot n q : U64}
    (h : fold_anchors_ok_be UB () all rest tip_slot slot n q = ok true) :
    ∀ s ∈ entrySlots rest,
      tip_slot.val + 2 ≤ (s + 1) + n.val →
      (s + 1) + n.val ≤ slot.val + 1 →
      q.val ≤ ((presentSlots all).filter (fun x => s + 1 ≤ x ∧ x < (s + 1) + n.val)).length +
        (if s + 1 ≤ slot.val ∧ slot.val < (s + 1) + n.val then 1 else 0) := by
  induction rest with
  | TNil =>
    intro s hs
    simp only [entrySlots_nil, List.not_mem_nil] at hs
  | TCons f s' tl ih =>
    intro s hs hlo hhi
    simp only [fold_anchors_ok_be, UB] at h
    simp at h
    obtain ⟨u, hu, h⟩ := bind_inv h
    obtain ⟨here, hhere, h⟩ := bind_inv h
    obtain ⟨more, hmore, h⟩ := bind_inv h
    split at h
    · rename_i hheret
      injection h with h
      subst h
      have huv : u.val = s'.val + 1 := by
        have := UScalar.add_equiv s' 1#u64
        simp only [hu] at this
        exact this.2.1
      simp only [entrySlots_cons, List.mem_cons] at hs
      rcases hs with rfl | htl
      · have h1 : tip_slot.val + 2 ≤ u.val + n.val := by omega
        have h2 : u.val + n.val ≤ slot.val + 1 := by omega
        rw [hheret] at hhere
        have hsound := fold_window_ok_be_sound hhere h1 h2
        simpa [huv] using hsound
      · exact ih hmore s htl hlo hhi
    · simp at h

end Rust
