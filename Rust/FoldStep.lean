import Rust.Equiv
import MoltPetit.TS.Bridge
import Spec.Model
import Spec.Statements

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

theorem ubk_select_val_true (b : U64) {a z : U64} (h : UBK.select () true a b = ok z) :
    z = a := by
  dsimp [UBK, BackendK.select, U64Backend.Insts.Molt_petitBackendKU64Bool.select] at h
  injection h with h; subst h; rfl

theorem ubk_select_val_false (a : U64) {b z : U64} (h : UBK.select () false a b = ok z) :
    z = b := by
  dsimp [UBK, BackendK.select, U64Backend.Insts.Molt_petitBackendKU64Bool.select] at h
  injection h with h; subst h; rfl

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




/-- All entry flags of a buffer. -/
def tailFlags : TailG U64 → List Nat
  | .TNil => []
  | .TCons f _ tl => f.val :: tailFlags tl

@[simp] theorem tailFlags_nil : tailFlags (.TNil : TailG U64) = [] := rfl

@[simp] theorem tailFlags_cons (f s : U64) (tl : TailG U64) :
    tailFlags (.TCons f s tl) = f.val :: tailFlags tl := rfl

/-- Present entries form a suffix: once a flag is 1, all subsequent flags are 1. -/
def PresentSuffix : TailG U64 → Prop
  | .TNil => True
  | .TCons f _ tl => (f.val = 1 → ∀ f' ∈ tailFlags tl, f' = 1) ∧ PresentSuffix tl

/-- The buffer representation relation `TailRepr n st cl`. -/
structure TailRepr (n : Nat) (st : CertStateG U64) (cl : MoltPetit.Model.CertClaim) : Prop where
  tip_id : ∃ h : molt_petit.Hash, st.tip_id = toHashG h ∧ hashToNat h = cl.tipId
  tip_slot : st.tip_slot.val = cl.tipSlot
  tip_height : st.tip_height.val = cl.tipHeight
  tail_len : (entrySlots st.tail).length = n - 1
  tail_flags : ∀ f ∈ tailFlags st.tail, f = 0 ∨ f = 1
  tail_suffix : PresentSuffix st.tail
  tail_mono : (presentSlots st.tail).Pairwise (· < ·)
  tail_last : 2 ≤ n → (presentSlots st.tail).getLast? = some cl.tipSlot
  tail_eq : (presentSlots st.tail).filter (cl.tipSlot + 2 - n ≤ ·) = cl.tail.map (·.slot)

theorem windowCount_append (a b : MoltPetit.Model.Chain) (u len : Nat) :
    MoltPetit.Model.windowCount (a ++ b) u len =
      MoltPetit.Model.windowCount a u len + MoltPetit.Model.windowCount b u len := by
  simp [MoltPetit.Model.windowCount, List.filter_append]

theorem windowCount_map_slot (c : MoltPetit.Model.Chain) (u n : Nat) :
    MoltPetit.Model.windowCount c u n =
      ((c.map (·.slot)).filter (fun s => u ≤ s ∧ s < u + n)).length := by
  induction c with
  | nil => rfl
  | cons b tl ih =>
    simp only [MoltPetit.Model.windowCount, MoltPetit.Model.blockInWindow,
      List.filter_cons, List.map_cons]
    unfold MoltPetit.Model.windowCount at ih
    simp only [Bool.decide_and] at *
    by_cases h : u ≤ b.slot ∧ b.slot < u + n <;> simp [h, ih]

theorem filter_presentSlots_of_tailRepr {n : Nat} {st : CertStateG U64}
    {cl : MoltPetit.Model.CertClaim} (hrep : TailRepr n st cl) {u : Nat}
    (hu : cl.tipSlot + 2 - n ≤ u) (len : Nat) :
    ((presentSlots st.tail).filter (fun s => u ≤ s ∧ s < u + len)) =
      ((cl.tail.map (·.slot)).filter (fun s => u ≤ s ∧ s < u + len)) := by
  have heq := hrep.tail_eq
  have hsub : ∀ s, u ≤ s ∧ s < u + len → cl.tipSlot + 2 - n ≤ s := by
    intro s hs; omega
  conv_rhs => rw [← heq]
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  by_cases hx : u ≤ x ∧ x < u + len
  · simp [hx, hsub x hx]
  · simp [hx]

theorem windowCount_eq_presentSlots {n : Nat} {st : CertStateG U64}
    {cl : MoltPetit.Model.CertClaim} (hrep : TailRepr n st cl) {u : Nat}
    (hu : cl.tipSlot + 2 - n ≤ u) (len : Nat) :
    MoltPetit.Model.windowCount cl.tail u len =
      ((presentSlots st.tail).filter (fun s => u ≤ s ∧ s < u + len)).length := by
  rw [windowCount_map_slot, filter_presentSlots_of_tailRepr hrep hu]

theorem windowCount_extend_eq {n : Nat} {st : CertStateG U64}
    {cl : MoltPetit.Model.CertClaim} (hrep : TailRepr n st cl) (b : molt_petit.Block)
    {u : Nat} (hu : cl.tipSlot + 2 - n ≤ u) (len : Nat) :
    MoltPetit.Model.windowCount (cl.tail ++ [toModelBlock b]) u len =
      ((presentSlots st.tail).filter (fun s => u ≤ s ∧ s < u + len)).length +
        (if u ≤ b.slot.val ∧ b.slot.val < u + len then 1 else 0) := by
  rw [windowCount_append, windowCount_eq_presentSlots hrep hu]
  congr 1
  simp only [MoltPetit.Model.windowCount, MoltPetit.Model.blockInWindow, toModelBlock,
    List.filter_cons, List.filter_nil]
  by_cases h : u ≤ b.slot.val ∧ b.slot.val < u + len <;> simp [h]


/-- Soundness of `cert_step_core_be`: the four non-`Signed` premises of
`GroundedCert*.extend` hold for `cl` and `toModelBlock b`. -/
theorem cert_step_core_be_sound {n q : U64} {st : CertStateG U64}
    {cl : MoltPetit.Model.CertClaim} (b : molt_petit.Block)
    (hq : molt_petit.quorum n = ok q)
    (hn : 1 ≤ n.val)
    (hrep : TailRepr n.val st cl)
    (h : cert_step_core_be UBK () n q st (toBlockG b) = ok true) :
    (toModelBlock b).height = cl.tipHeight + 1 ∧
    cl.tipSlot < (toModelBlock b).slot ∧
    (toModelBlock b).prev = some cl.tipId ∧
    (∀ u : Nat, cl.tipSlot + 2 ≤ u + n.val → u + n.val ≤ (toModelBlock b).slot + 1 →
      MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (cl.tail ++ [toModelBlock b]) u n.val) := by
  dsimp [cert_step_core_be] at h
  obtain ⟨t, ht, h⟩ := bind_inv h
  obtain ⟨succ, hsucc, h⟩ := bind_inv h
  obtain ⟨h_ok, hh_ok, h⟩ := bind_inv h
  obtain ⟨slot_ok, hslot_ok, h⟩ := bind_inv h
  obtain ⟨prev_eq, hprev_eq, h⟩ := bind_inv h
  obtain ⟨has, hhas, h⟩ := bind_inv h
  obtain ⟨prev_ok, hprev_ok, h⟩ := bind_inv h
  obtain ⟨t1, ht1, h⟩ := bind_inv h
  obtain ⟨links, hlinks, h⟩ := bind_inv h
  obtain ⟨t2, ht2, h⟩ := bind_inv h
  obtain ⟨ts2, hts2, h⟩ := bind_inv h
  obtain ⟨lo, hlo, h⟩ := bind_inv h
  obtain ⟨base, hbase, h⟩ := bind_inv h
  obtain ⟨anchors, hanchors, h⟩ := bind_inv h
  obtain ⟨t3, ht3, h⟩ := bind_inv h
  split at h
  · rename_i hlinks_t
    injection h with h; subst h
    subst hlinks_t
    split at ht3
    · rename_i hbase_t
      injection ht3 with ht3; subst ht3
      subst hbase_t
      split at hlinks
      · rename_i ht1_t
        injection hlinks with hlinks; subst hlinks
        subst ht1_t
        split at ht1
        · rename_i hh_ok_t
          injection ht1 with ht1; subst ht1
          subst hh_ok_t
          split at hprev_ok
          · rename_i hhas_t
            injection hprev_ok with hprev_ok; subst hprev_ok
            subst hhas_t
            have hts := hrep.tip_slot
            have hsuccv : succ.val = st.tip_height.val + 1 := by
              have htv : t.val = 1 := by injection ht with ht; subst ht; rfl
              have := UScalar.add_equiv st.tip_height t; simp only [hsucc] at this
              omega
            injection hh_ok with hh_ok
            simp only [decide_eq_true_eq] at hh_ok
            have hheight : (toModelBlock b).height = cl.tipHeight + 1 := by
              dsimp [toModelBlock, toBlockG] at hh_ok ⊢
              rw [hh_ok, hsuccv, hrep.tip_height]
            injection hslot_ok with hslot_ok
            have hslot : cl.tipSlot < (toModelBlock b).slot := by
              dsimp [toModelBlock, toBlockG] at hslot_ok ⊢
              have : st.tip_slot.val < b.slot.val := by simpa using hslot_ok
              omega
            injection hhas with hhas
            cases hp : b.prev with
            | none =>
              dsimp [toBlockG] at hhas
              rw [hp] at hhas
              simp at hhas
            | some p =>
              obtain ⟨h_tip, hst_id, hhash_id⟩ := hrep.tip_id
              dsimp [toBlockG] at hprev_eq
              rw [hp, hst_id] at hprev_eq
              rw [hashg_eq_eq] at hprev_eq
              have hpeq := hash_eq_sound hprev_eq
              have hprev : (toModelBlock b).prev = some cl.tipId := by
                dsimp [toModelBlock]
                rw [hp]
                simp [hpeq, hhash_id]
              have hqv : q.val = MoltPetit.Model.quorum n.val := quorum_val_of_ok hq
              have ht2v : t2.val = 2 := by
                have htv : t.val = 1 := by injection ht with ht; subst ht; rfl
                have := UScalar.add_equiv t t; simp only [ht2] at this; omega
              have hts2v : ts2.val = st.tip_slot.val + 2 := by
                have := UScalar.add_equiv st.tip_slot t2; simp only [hts2] at this; omega
              have hlov : lo.val = cl.tipSlot + 2 - n.val := by
                have := ubk_monus_val hlo
                rw [this, hts2v, hts]
              have hbase_dense : lo.val + n.val ≤ b.slot.val + 1 →
                  MoltPetit.Model.quorum n.val ≤
                    MoltPetit.Model.windowCount (cl.tail ++ [toModelBlock b]) lo.val n.val := by
                intro hhi
                have hsound := fold_window_ok_be_sound hbase (by omega) hhi
                have hext := windowCount_extend_eq hrep b (u := lo.val) (by omega) n.val
                rw [hqv] at hsound
                rw [hext]
                exact hsound
              have hanchor_dense : ∀ b' ∈ cl.tail ++ [toModelBlock b],
                  lo.val ≤ b'.slot + 1 → b'.slot + 1 + n.val ≤ b.slot.val + 1 →
                  MoltPetit.Model.quorum n.val ≤
                    MoltPetit.Model.windowCount (cl.tail ++ [toModelBlock b]) (b'.slot + 1) n.val := by
                intro b' hb' hlo' hhi'
                rw [List.mem_append] at hb'
                rcases hb' with htail | hb_new
                · have hslot_mem : b'.slot ∈ cl.tail.map (·.slot) := List.mem_map.mpr ⟨b', htail, rfl⟩
                  rw [← hrep.tail_eq] at hslot_mem
                  have hpres : b'.slot ∈ presentSlots st.tail := List.mem_of_mem_filter hslot_mem
                  have hent : b'.slot ∈ entrySlots st.tail := mem_entrySlots_of_mem_presentSlots hpres
                  have hsound := fold_anchors_ok_be_sound hanchors b'.slot hent (by omega) hhi'
                  have hext := windowCount_extend_eq hrep b (u := b'.slot + 1) (by omega) n.val
                  rw [hqv] at hsound
                  rw [hext]
                  exact hsound
                · simp only [List.mem_singleton] at hb_new
                  subst hb_new
                  dsimp [toModelBlock] at hhi'
                  omega
              have hdense := MoltPetit.Model.anchored_density_sound (c := cl.tail ++ [toModelBlock b])
                (lo := lo.val) (t := b.slot.val) (n := n.val) hbase_dense hanchor_dense
              have hdensity : ∀ u : Nat, cl.tipSlot + 2 ≤ u + n.val → u + n.val ≤ (toModelBlock b).slot + 1 →
                  MoltPetit.Model.quorum n.val ≤
                    MoltPetit.Model.windowCount (cl.tail ++ [toModelBlock b]) u n.val := by
                intro u hu1 hu2
                have hlu : lo.val ≤ u := by omega
                have hmat : u + n.val ≤ b.slot.val + 1 := by
                  change u + n.val ≤ (toModelBlock b).slot + 1 at hu2
                  exact hu2
                exact hdense u hlu hmat
              exact ⟨hheight, hslot, hprev, hdensity⟩
          · simp at hprev_ok
        · simp at ht1
      · simp at hlinks
    · simp at ht3
  · simp at h


def tailPush : TailG U64 → U64 → U64 → TailG U64
  | .TNil, f, s => .TCons f s .TNil
  | .TCons f0 s0 tl, f, s => .TCons f0 s0 (tailPush tl f s)

theorem tail_push_be_eq (t : TailG U64) (f s : U64) :
    tail_push_be core.marker.CopyU64 t f s = ok (tailPush t f s) := by
  induction t with
  | TNil =>
    unfold tail_push_be
    rfl
  | TCons f0 s0 tl ih =>
    unfold tail_push_be
    rw [ih]
    rfl

theorem cert_next_tail_be_corr (t : TailG U64) (slot : U64) :
    cert_next_tail_be UB () t slot = ok (match t with
      | .TNil => .TNil
      | .TCons _ _ tl => tailPush tl 1#u64 slot) := by
  cases t with
  | TNil => rfl
  | TCons f s tl =>
    unfold cert_next_tail_be
    dsimp [UB, U64Backend.Insts.Molt_petitBackendU64Bool.one]
    change tail_push_be core.marker.CopyU64 tl 1#u64 slot = _
    rw [tail_push_be_eq]

@[simp] theorem entrySlots_tailPush (t : TailG U64) (f s : U64) :
    entrySlots (tailPush t f s) = entrySlots t ++ [s.val] := by
  induction t with
  | TNil => rfl
  | TCons f0 s0 tl ih =>
    simp only [tailPush, entrySlots_cons, ih, List.cons_append]

@[simp] theorem tailFlags_tailPush (t : TailG U64) (f s : U64) :
    tailFlags (tailPush t f s) = tailFlags t ++ [f.val] := by
  induction t with
  | TNil => rfl
  | TCons f0 s0 tl ih =>
    simp only [tailPush, tailFlags_cons, ih, List.cons_append]

@[simp] theorem presentSlots_tailPush_one (t : TailG U64) (s : U64) :
    presentSlots (tailPush t 1#u64 s) = presentSlots t ++ [s.val] := by
  induction t with
  | TNil =>
    simp only [tailPush, presentSlots_cons, presentSlots_nil, List.nil_append]
    rfl
  | TCons f0 s0 tl ih =>
    simp only [tailPush, presentSlots_cons, ih]
    split_ifs <;> simp [List.cons_append]

theorem presentSuffix_tailPush_one (t : TailG U64) (s : U64)
    (h : PresentSuffix t) : PresentSuffix (tailPush t 1#u64 s) := by
  induction t with
  | TNil =>
    simp [tailPush, PresentSuffix, tailFlags]
  | TCons f0 s0 tl ih =>
    dsimp [PresentSuffix] at h ⊢
    dsimp [tailPush]
    refine ⟨?_, ih h.2⟩
    intro hf0
    intro f' hf'
    rw [tailFlags_tailPush] at hf'
    rw [List.mem_append] at hf'
    rcases hf' with htl | hlast
    · exact h.1 hf0 f' htl
    · simp only [List.mem_singleton] at hlast
      subst hlast
      rfl

theorem getLast?_append_singleton {α : Type} (l : List α) (x : α) :
    (l ++ [x]).getLast? = some x := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    cases tl with
    | nil => rfl
    | cons b rest =>
      have : (a :: b :: rest ++ [x]).getLast? = (b :: rest ++ [x]).getLast? := rfl
      rw [this, ih]

theorem pairwise_lt_append_singleton (l : List Nat) (x : Nat)
    (hmono : l.Pairwise (· < ·)) (hlt : ∀ y ∈ l, y < x) :
    (l ++ [x]).Pairwise (· < ·) := by
  induction l with
  | nil =>
    simp
  | cons a tl ih =>
    have hmono' : tl.Pairwise (· < ·) := List.Pairwise.of_cons hmono
    have hlt' : ∀ y ∈ tl, y < x := fun y hy => hlt y (List.Mem.tail a hy)
    have hax : a < x := hlt a (List.Mem.head tl)
    have ih' := ih hmono' hlt'
    simp only [List.cons_append, List.pairwise_cons] at hmono ⊢
    refine ⟨?_, ih'⟩
    intro y hy
    rw [List.mem_append] at hy
    rcases hy with htl | hlast
    · exact hmono.1 y htl
    · simp only [List.mem_singleton] at hlast
      subst hlast
      exact hax

theorem le_last_of_pairwise_lt : ∀ (l : List Nat) {last : Nat},
    l.Pairwise (· < ·) → l.getLast? = some last → ∀ y ∈ l, y ≤ last
  | [], _, _, hlast => by simp at hlast
  | [a], last, _, hlast => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hlast
    intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    rfl
  | a :: b :: rest, last, hmono, hlast => by
    have hmono' : (b :: rest).Pairwise (· < ·) := List.Pairwise.of_cons hmono
    have hlast' : (b :: rest).getLast? = some last := by
      have : (a :: b :: rest).getLast? = (b :: rest).getLast? := rfl
      rw [← this]
      exact hlast
    have hab : a < b := List.rel_of_pairwise_cons hmono (by simp)
    have ih := le_last_of_pairwise_lt (b :: rest) hmono' hlast'
    intro y hy
    cases hy with
    | head =>
      have := ih b (List.Mem.head rest)
      omega
    | tail _ hy' =>
      exact ih y hy'

theorem head_le_last_of_pairwise_lt : ∀ (a : Nat) (tl : List Nat) {last : Nat},
    (a :: tl).Pairwise (· < ·) → (a :: tl).getLast? = some last →
    a + tl.length ≤ last
  | a, [], last, _, hlast => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hlast
    simp
  | a, b :: rest, last, hmono, hlast => by
    have hmono' : (b :: rest).Pairwise (· < ·) := List.Pairwise.of_cons hmono
    have hlast' : (b :: rest).getLast? = some last := by
      have : (a :: b :: rest).getLast? = (b :: rest).getLast? := rfl
      rw [← this]
      exact hlast
    have hab : a < b := List.rel_of_pairwise_cons hmono (by simp)
    have ih := head_le_last_of_pairwise_lt b rest hmono' hlast'
    simp only [List.length_cons]
    omega

theorem presentSlots_eq_entrySlots_of_flags_one : ∀ (t : TailG U64),
    (∀ f ∈ tailFlags t, f = 1) → presentSlots t = entrySlots t
  | .TNil, _ => rfl
  | .TCons f s tl, h => by
    have hf : f.val = 1 := h f.val (by simp)
    have htl : ∀ f' ∈ tailFlags tl, f' = 1 := fun f' hf' => h f' (by simp [hf'])
    simp only [presentSlots_cons, entrySlots_cons, hf, if_true]
    rw [presentSlots_eq_entrySlots_of_flags_one tl htl]

theorem map_filter_slot (c : List MoltPetit.Model.Block) (bound : Nat) :
    (c.map (·.slot)).filter (bound ≤ ·) =
    (c.filter fun x => decide (bound ≤ x.slot)).map (·.slot) := by
  induction c with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases h : bound ≤ x.slot
    · simp [h, ih]
    · simp [h, ih]


theorem filter_filter_ge (l : List Nat) (a b : Nat) (hab : a ≤ b) :
    (l.filter (a ≤ ·)).filter (b ≤ ·) = l.filter (b ≤ ·) := by
  induction l with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.filter_cons]
    by_cases hx : b ≤ x
    · have hxa : a ≤ x := by omega
      simp [hx, hxa, ih]
    · by_cases hxa : a ≤ x
      · simp [hx, hxa, ih]
      · simp [hx, hxa, ih]

/-- Soundness of `cert_next_tail_be`: if `TailRepr n st cl` holds, the core step accepts
a block `b`, and `cert_next_tail_be` produces `t'`, then `TailRepr n (stepState b t') cl'`
holds for the claim `cl'` built by `extend`. -/
theorem cert_next_tail_be_repr {n q : U64} {st : CertStateG U64}
    {cl : MoltPetit.Model.CertClaim} (b : molt_petit.Block)
    (hq : molt_petit.quorum n = ok q)
    (hn : 1 ≤ n.val)
    (hrep : TailRepr n.val st cl)
    (hcore : cert_step_core_be UBK () n q st (toBlockG b) = ok true)
    {t' : TailG U64}
    (ht' : cert_next_tail_be UB () st.tail b.slot = ok t') :
    TailRepr n.val (stepState b t')
      { tipId := (toModelBlock b).id
      , tipSlot := (toModelBlock b).slot
      , tipHeight := (toModelBlock b).height
      , tail := (cl.tail ++ [toModelBlock b]).filter fun x => decide ((toModelBlock b).slot + 2 - n.val ≤ x.slot) } := by
  have ⟨hheight, hslot, hprev, hdense⟩ := cert_step_core_be_sound b hq hn hrep hcore
  by_cases hn2 : 2 ≤ n.val
  · have hlen : (entrySlots st.tail).length = n.val - 1 := hrep.tail_len
    cases htail : st.tail with
    | TNil =>
      rw [htail] at hlen
      simp only [entrySlots_nil, List.length_nil] at hlen
      omega
    | TCons f0 s0 tl =>
      have hcorr := cert_next_tail_be_corr (TailG.TCons f0 s0 tl) b.slot
      rw [htail] at ht'
      rw [ht'] at hcorr
      dsimp only at hcorr
      injection hcorr with ht'_eq
      subst ht'_eq
      have hsuff_st : PresentSuffix st.tail := hrep.tail_suffix
      rw [htail] at hsuff_st
      have htl_len : (entrySlots tl).length + 1 = n.val - 1 := by
        rw [htail] at hlen
        simp only [entrySlots_cons, List.length_cons] at hlen
        exact hlen
      have hlen' : (entrySlots (tailPush tl 1#u64 b.slot)).length = n.val - 1 := by
        rw [entrySlots_tailPush]
        simp only [List.length_append, List.length_singleton]
        omega
      have hflags' : ∀ f ∈ tailFlags (tailPush tl 1#u64 b.slot), f = 0 ∨ f = 1 := by
        intro f hf
        rw [tailFlags_tailPush, List.mem_append] at hf
        rcases hf with htl_f | hnew_f
        · have : f ∈ tailFlags st.tail := by
            rw [htail]
            simp only [tailFlags_cons, List.mem_cons]
            right; exact htl_f
          exact hrep.tail_flags f this
        · simp only [List.mem_singleton] at hnew_f
          subst hnew_f
          right; rfl
      have hsuff' : PresentSuffix (tailPush tl 1#u64 b.slot) :=
        presentSuffix_tailPush_one tl b.slot hsuff_st.2
      have hps_tl_mono : (presentSlots tl).Pairwise (· < ·) := by
        have hmono := hrep.tail_mono
        rw [htail] at hmono
        simp only [presentSlots_cons] at hmono
        split_ifs at hmono with hf0
        · exact List.Pairwise.of_cons hmono
        · exact hmono
      have hps_tl_lt : ∀ y ∈ presentSlots tl, y < (toModelBlock b).slot := by
        intro y hy
        have hymem : y ∈ presentSlots st.tail := by
          rw [htail, presentSlots_cons]
          split_ifs with hf0
          · exact List.mem_cons_of_mem _ hy
          · exact hy
        have hlast := hrep.tail_last hn2
        have hle := le_last_of_pairwise_lt (presentSlots st.tail) hrep.tail_mono hlast y hymem
        change cl.tipSlot < b.slot.val at hslot
        dsimp [toModelBlock]
        omega
      have hmono' : (presentSlots (tailPush tl 1#u64 b.slot)).Pairwise (· < ·) := by
        rw [presentSlots_tailPush_one]
        exact pairwise_lt_append_singleton (presentSlots tl) b.slot.val hps_tl_mono hps_tl_lt
      have hlast' : 2 ≤ n.val → (presentSlots (tailPush tl 1#u64 b.slot)).getLast? = some (toModelBlock b).slot := by
        intro _
        rw [presentSlots_tailPush_one]
        exact getLast?_append_singleton (presentSlots tl) b.slot.val
      have htail_eq' : (presentSlots (tailPush tl 1#u64 b.slot)).filter ((toModelBlock b).slot + 2 - n.val ≤ ·) =
          ((cl.tail ++ [toModelBlock b]).filter fun x => decide ((toModelBlock b).slot + 2 - n.val ≤ x.slot)).map (·.slot) := by
        set bound := (toModelBlock b).slot + 2 - n.val
        have hbound_le : bound ≤ b.slot.val := by
          dsimp [bound, toModelBlock]
          omega
        rw [presentSlots_tailPush_one]
        have hfilter_push : ((presentSlots tl ++ [b.slot.val]).filter (bound ≤ ·)) =
            (presentSlots tl).filter (bound ≤ ·) ++ [b.slot.val] := by
          rw [List.filter_append]
          congr 1
          simp only [List.filter_cons, List.filter_nil]
          simp [hbound_le]
        rw [hfilter_push]
        have hfilter_cl : ((cl.tail ++ [toModelBlock b]).filter fun x => decide (bound ≤ x.slot)) =
            (cl.tail.filter fun x => decide (bound ≤ x.slot)) ++ [toModelBlock b] := by
          rw [List.filter_append]
          congr 1
          simp only [List.filter_cons, List.filter_nil]
          have : bound ≤ (toModelBlock b).slot := by
            dsimp [toModelBlock]
            exact hbound_le
          simp [this]
        rw [hfilter_cl, List.map_append, List.map_singleton]
        congr 1
        rw [← map_filter_slot]
        have heq := hrep.tail_eq
        have hbound_ge : cl.tipSlot + 2 - n.val ≤ bound := by
          change cl.tipSlot < b.slot.val at hslot
          dsimp [bound, toModelBlock]
          omega
        have hflt := filter_filter_ge (presentSlots st.tail) (cl.tipSlot + 2 - n.val) bound hbound_ge
        have hdrop_head : (presentSlots st.tail).filter (bound ≤ ·) = (presentSlots tl).filter (bound ≤ ·) := by
          rw [htail, presentSlots_cons]
          split_ifs with hf0
          · simp only [List.filter_cons]
            have hf_all : ∀ f ∈ tailFlags st.tail, f = 1 := by
              rw [htail]
              intro f hf
              simp only [tailFlags_cons, List.mem_cons] at hf
              rcases hf with rfl | hrest
              · exact hf0
              · exact hsuff_st.1 hf0 f hrest
            have heq_slots := presentSlots_eq_entrySlots_of_flags_one st.tail hf_all
            have hps_len : (presentSlots st.tail).length = n.val - 1 := by
              rw [heq_slots, hrep.tail_len]
            have hps_eq : presentSlots st.tail = s0.val :: presentSlots tl := by
              rw [htail, presentSlots_cons, hf0]; rfl
            have htl_ps_len : (presentSlots tl).length = n.val - 2 := by
              rw [hps_eq] at hps_len
              simp only [List.length_cons] at hps_len
              omega
            have hmono_cons : (s0.val :: presentSlots tl).Pairwise (· < ·) := by
              rw [← hps_eq]; exact hrep.tail_mono
            have hlast_cons : (s0.val :: presentSlots tl).getLast? = some cl.tipSlot := by
              rw [← hps_eq]; exact hrep.tail_last hn2
            have hhead_le := head_le_last_of_pairwise_lt s0.val (presentSlots tl) hmono_cons hlast_cons
            have hs0_lt : s0.val < bound := by
              rw [htl_ps_len] at hhead_le
              change cl.tipSlot < b.slot.val at hslot
              dsimp [bound, toModelBlock]
              omega
            have : ¬ (bound ≤ s0.val) := by omega
            simp [this]
          · rfl
        rw [heq] at hflt
        rw [hdrop_head] at hflt
        exact hflt.symm
      dsimp [stepState]
      exact ⟨⟨b.id, rfl, rfl⟩, rfl, rfl, hlen', hflags', hsuff', hmono', hlast', htail_eq'⟩
  · have hn1 : n.val = 1 := by omega
    have hlen : (entrySlots st.tail).length = 0 := by
      have := hrep.tail_len
      omega
    have htail : st.tail = .TNil := by
      cases h : st.tail with
      | TNil => rfl
      | TCons f s tl =>
        rw [h] at hlen
        simp only [entrySlots_cons, List.length_cons] at hlen
        omega
    have hcorr := cert_next_tail_be_corr .TNil b.slot
    rw [htail] at ht'
    rw [ht'] at hcorr
    dsimp only at hcorr
    injection hcorr with ht'_eq
    subst ht'_eq
    have hlen' : (entrySlots (.TNil : TailG U64)).length = n.val - 1 := by
      simp only [entrySlots_nil, List.length_nil]
      omega
    have hflags' : ∀ f ∈ tailFlags (.TNil : TailG U64), f = 0 ∨ f = 1 := by
      intro f hf
      simp only [tailFlags_nil, List.not_mem_nil] at hf
    have hsuff' : PresentSuffix (.TNil : TailG U64) := trivial
    have hmono' : (presentSlots (.TNil : TailG U64)).Pairwise (· < ·) := by simp
    have hlast' : 2 ≤ n.val → (presentSlots (.TNil : TailG U64)).getLast? = some (toModelBlock b).slot := by
      intro h2; omega
    have htail_eq' : (presentSlots (.TNil : TailG U64)).filter ((toModelBlock b).slot + 2 - n.val ≤ ·) =
        ((cl.tail ++ [toModelBlock b]).filter fun x => decide ((toModelBlock b).slot + 2 - n.val ≤ x.slot)).map (·.slot) := by
      simp only [presentSlots_nil, List.filter_nil]
      have hbound : (toModelBlock b).slot + 2 - n.val = (toModelBlock b).slot + 1 := by omega
      rw [hbound]
      have hnil : ((cl.tail ++ [toModelBlock b]).filter fun x => decide ((toModelBlock b).slot + 1 ≤ x.slot)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        simp only [decide_eq_true_iff]
        rw [List.mem_append] at hx
        rcases hx with hcl | hb
        · have : cl.tail = [] := by
            have heq := hrep.tail_eq
            rw [htail] at heq
            simp only [presentSlots_nil, List.filter_nil] at heq
            exact List.map_eq_nil_iff.mp heq.symm
          rw [this] at hcl
          simp at hcl
        · simp only [List.mem_singleton] at hb
          subst hb
          omega
      rw [hnil, List.map_nil]
    dsimp [stepState]
    exact ⟨⟨b.id, rfl, rfl⟩, rfl, rfl, hlen', hflags', hsuff', hmono', hlast', htail_eq'⟩


-- ---------------------------------------------------------------------------
-- Step 6: Prefix claim and genesis representation
-- ---------------------------------------------------------------------------

lemma entrySlots_padTail (k : Nat) (t : TailG U64) :
    entrySlots (padTail k t) = List.replicate k 0 ++ entrySlots t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [padTail, entrySlots_cons]
    change (0#u64 : U64).val :: entrySlots (padTail k t) = 0 :: List.replicate k 0 ++ entrySlots t
    rw [ih]
    rfl

lemma tailFlags_padTail (k : Nat) (t : TailG U64) :
    tailFlags (padTail k t) = List.replicate k 0 ++ tailFlags t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [padTail, tailFlags_cons]
    change (0#u64 : U64).val :: tailFlags (padTail k t) = 0 :: List.replicate k 0 ++ tailFlags t
    rw [ih]
    rfl

lemma presentSlots_padTail (k : Nat) (t : TailG U64) :
    presentSlots (padTail k t) = presentSlots t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [padTail, presentSlots_cons]
    split
    · rename_i h
      have : (0#u64 : U64).val = 0 := rfl
      omega
    · exact ih

lemma presentSuffix_padTail (k : Nat) (t : TailG U64) :
    PresentSuffix (padTail k t) ↔ PresentSuffix t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [padTail, PresentSuffix]
    constructor
    · intro ⟨_, h2⟩; exact ih.mp h2
    · intro h
      refine ⟨?_, ih.mpr h⟩
      intro h1
      have : (0#u64 : U64).val = 0 := rfl
      omega

theorem modelClaimOf_nil (n : Nat) (G : MoltPetit.Model.Block) :
    modelClaimOf n G [] =
      { tipId := G.id,
        tipSlot := G.slot,
        tipHeight := G.height,
        tail := [G].filter fun x => decide (G.slot + 2 - n ≤ x.slot) } := rfl

theorem modelClaimOf_step (n : Nat) (G : MoltPetit.Model.Block)
    (pre : List MoltPetit.Model.Block) (b : MoltPetit.Model.Block)
    (hslot : (modelClaimOf n G pre).tipSlot ≤ b.slot) :
    modelClaimOf n G (pre ++ [b]) =
      { tipId := b.id,
        tipSlot := b.slot,
        tipHeight := b.height,
        tail := ((modelClaimOf n G pre).tail ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot) } := by
  have hlast : (G :: (pre ++ [b])).getLast (List.cons_ne_nil _ _) = b := by
    change ((G :: pre) ++ [b]).getLast _ = b
    exact List.getLast_append_singleton (G :: pre)
  unfold modelClaimOf
  dsimp only
  rw [hlast]
  congr 1
  have hcons : G :: (pre ++ [b]) = (G :: pre) ++ [b] := rfl
  rw [hcons, List.filter_append, List.filter_append]
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  have hle : ((G :: pre).getLast (List.cons_ne_nil G pre)).slot ≤ b.slot := hslot
  by_cases hb : b.slot + 2 - n ≤ x.slot
  · simp [hb]
    omega
  · simp [hb]

theorem modelClaimOf_step_lt (n : Nat) (G : MoltPetit.Model.Block)
    (pre : List MoltPetit.Model.Block) (b : MoltPetit.Model.Block)
    (hslot : (modelClaimOf n G pre).tipSlot < b.slot) :
    modelClaimOf n G (pre ++ [b]) =
      { tipId := b.id,
        tipSlot := b.slot,
        tipHeight := b.height,
        tail := ((modelClaimOf n G pre).tail ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot) } :=
  modelClaimOf_step n G pre b (Nat.le_of_lt hslot)

theorem tailRepr_genesisState (n : Nat) (G : molt_petit.Block) :
    TailRepr n (genesisState n G) (modelClaimOf n (toModelBlock G) []) := by
  dsimp [genesisState, modelClaimOf]
  refine ⟨⟨G.id, rfl, rfl⟩, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- tail_len
    by_cases hn : n < 2
    · unfold initTail
      simp [hn]
      omega
    · unfold initTail
      simp [hn]
      rw [entrySlots_padTail]
      simp only [entrySlots_cons, entrySlots_nil, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
      omega
  · -- tail_flags
    intro f hf
    by_cases hn : n < 2
    · unfold initTail at hf
      simp [hn] at hf
    · unfold initTail at hf
      simp [hn] at hf
      rw [tailFlags_padTail] at hf
      simp only [tailFlags_cons, tailFlags_nil, List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with ⟨_, rfl⟩ | rfl
      · left; rfl
      · right; rfl
  · -- tail_suffix
    by_cases hn : n < 2
    · unfold initTail; simp [hn]; trivial
    · unfold initTail; simp [hn]
      rw [presentSuffix_padTail]
      exact ⟨fun _ _ h => by simp at h, trivial⟩
  · -- tail_mono
    by_cases hn : n < 2
    · unfold initTail; simp [hn]
    · unfold initTail; simp [hn]
      rw [presentSlots_padTail]
      simp only [presentSlots_cons, presentSlots_nil]
      have : (1#u64 : U64).val = 1 := rfl
      simp [this]
  · -- tail_last
    intro hn2
    have hn : ¬ n < 2 := by omega
    unfold initTail
    simp [hn]
    rw [presentSlots_padTail]
    simp only [presentSlots_cons, presentSlots_nil]
    have : (1#u64 : U64).val = 1 := rfl
    simp only [this, ↓reduceIte, List.getLast?_singleton, Option.some.injEq]
    rfl
  · -- tail_eq
    by_cases hn : n < 2
    · unfold initTail
      simp only [hn, ↓reduceIte, presentSlots_nil, List.filter_nil, List.filter_cons]
      have hnot : ¬ ((toModelBlock G).slot + 2 - n ≤ (toModelBlock G).slot) := by
        rcases Nat.eq_zero_or_pos n with rfl | hn1
        · omega
        · have : n = 1 := by omega
          subst this
          omega
      simp [hnot]
    · unfold initTail
      have hnot : ¬ n < 2 := hn
      simp only [hnot, ↓reduceIte]
      rw [presentSlots_padTail]
      simp only [presentSlots_cons, presentSlots_nil]
      have h1 : (1#u64 : U64).val = 1 := rfl
      simp only [h1, ↓reduceIte, List.filter_cons, List.filter_nil]
      have hle1 : (toModelBlock G).slot + 2 - n ≤ G.slot.val := by
        change G.slot.val + 2 - n ≤ G.slot.val
        omega
      have hle2 : (toModelBlock G).slot + 2 - n ≤ (toModelBlock G).slot := by
        change G.slot.val + 2 - n ≤ G.slot.val
        omega
      simp [hle1, hle2]
      rfl

theorem cert_genesis_ok_be_sound {G : molt_petit.Block}
    (h : cert_genesis_ok_be UB () (toBlockG G) = ok true) :
    MoltPetit.Model.genesisOk (toModelBlock G) = true ∧ (toModelBlock G).slot = 0 := by
  dsimp [cert_genesis_ok_be] at h
  obtain ⟨ok1, hok1, h⟩ := bind_inv h
  obtain ⟨t, ht, h⟩ := bind_inv h
  obtain ⟨s0, hs0, h⟩ := bind_inv h
  split at h
  · rename_i hok1_t
    injection h with h; subst h
    rw [hok1_t] at hok1
    have hgen := genesis_ok_be_sound hok1
    injection ht with ht; subst ht
    injection hs0 with hs0
    simp only [decide_eq_true_eq] at hs0
    have : (toModelBlock G).slot = 0 := by
      change G.slot.val = 0
      rw [hs0]
      rfl
    exact ⟨hgen, this⟩
  · injection h with h; contradiction

theorem cert_step_sched_be_sound {n q era : U64} {st : CertStateG U64} {b : molt_petit.Block}
    (hera : 0 < era.val)
    (h : cert_step_sched_be UBK () n q era st (toBlockG b) b.key_index = ok true) :
    cert_step_core_be UBK () n q st (toBlockG b) = ok true ∧
    (toModelBlock b).slot / era.val ≤ (toModelBlock b).keyIndex := by
  dsimp [cert_step_sched_be] at h
  obtain ⟨core, hcore, h⟩ := bind_inv h
  obtain ⟨gen, hgen, h⟩ := bind_inv h
  obtain ⟨below, hbelow, h⟩ := bind_inv h
  obtain ⟨pinned, hpinned, h⟩ := bind_inv h
  split at h
  · rename_i hcore_t
    injection h with h; subst h
    rw [hcore_t] at hcore
    have hgen_val := ubk_div_val (by omega) hgen
    cases below
    · injection hbelow with hbelow
      simp only [decide_eq_false_iff_not] at hbelow
      change ¬ (b.key_index.val < gen.val) at hbelow
      have hle : gen.val ≤ b.key_index.val := by omega
      refine ⟨hcore, ?_⟩
      change b.slot.val / era.val ≤ b.key_index.val
      rw [← hgen_val]
      exact hle
    · injection hpinned with hpinned
      contradiction
  · injection h with h; contradiction


lemma foldSched_sound_aux {n q era : U64} {G : Block}
    {Signed : MoltPetit.Model.Block → Prop}
    (hn : 1 ≤ n.val) (hq : quorum n = ok q) (hera : 0 < era.val) :
    ∀ (bs : List Block) (pre : List Block) (st : CertStateG U64),
    (∀ b ∈ bs, Signed (toModelBlock b)) →
    TailRepr n.val st (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) →
    MoltPetit.Model.GroundedCertSched n.val (fun s => s / era.val) Signed (toModelBlock G)
      (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) →
    FoldSched n q era st bs →
    MoltPetit.Model.GroundedCertSched n.val (fun s => s / era.val) Signed (toModelBlock G)
      (modelClaimOf n.val (toModelBlock G) ((pre ++ bs).map toModelBlock)) := by
  intro bs
  induction bs with
  | nil =>
    intro pre st hSig hrep hsched hfold
    simp only [List.append_nil]
    exact hsched
  | cons b rest ih =>
    intro pre st hSig hrep hsched hfold
    obtain ⟨hstep, t', ht', hfold_rest⟩ := hfold
    obtain ⟨hcore, hpin⟩ := cert_step_sched_be_sound hera hstep
    obtain ⟨hheight, hslot, hprev, hdense⟩ := cert_step_core_be_sound b hq hn hrep hcore
    have hSig_b : Signed (toModelBlock b) := hSig b (by simp)
    have hSig_rest : ∀ x ∈ rest, Signed (toModelBlock x) := fun x hx => hSig x (by simp [hx])
    let cl := modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)
    have hsched' := MoltPetit.Model.GroundedCertSched.extend cl (toModelBlock b)
      hsched hheight hslot hprev hSig_b hpin hdense
    have hcl_eq : modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock ++ [toModelBlock b]) =
        { tipId := (toModelBlock b).id,
          tipSlot := (toModelBlock b).slot,
          tipHeight := (toModelBlock b).height,
          tail := (cl.tail ++ [toModelBlock b]).filter
            fun x => decide ((toModelBlock b).slot + 2 - n.val ≤ x.slot) } :=
      modelClaimOf_step_lt n.val (toModelBlock G) (pre.map toModelBlock) (toModelBlock b) hslot
    have hmap_app : (pre ++ [b]).map toModelBlock = pre.map toModelBlock ++ [toModelBlock b] := by
      simp
    have hsched_step : MoltPetit.Model.GroundedCertSched n.val (fun s => s / era.val) Signed
        (toModelBlock G) (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock)) := by
      rw [hmap_app, hcl_eq]
      exact hsched'
    have hrep' := cert_next_tail_be_repr b hq hn hrep hcore ht'
    have hrep_step : TailRepr n.val (stepState b t')
        (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock)) := by
      rw [hmap_app, hcl_eq]
      exact hrep'
    have hres := ih (pre ++ [b]) (stepState b t') hSig_rest hrep_step hsched_step hfold_rest
    rw [List.append_assoc, List.singleton_append] at hres
    exact hres

theorem cert_fold_sched_sound : MoltPaper.thm_cert_fold_sched_sound := by
  intro n q era G bs Signed hn hq hera hG hSigG hSig hFold
  have ⟨hgen, hslot0⟩ := cert_genesis_ok_be_sound hG
  have hbase_sched : MoltPetit.Model.GroundedCertSched n.val (fun s => s / era.val) Signed
      (toModelBlock G) (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock)) := by
    simp only [List.map_nil]
    have hnil := modelClaimOf_nil n.val (toModelBlock G)
    rw [hnil]
    apply MoltPetit.Model.GroundedCertSched.genesis
    · exact hgen
    · exact hslot0
    · exact hSigG
    · dsimp only
      rw [hslot0]
      simp only [Nat.zero_div, Nat.zero_le]
  have hbase_rep : TailRepr n.val (genesisState n.val G)
      (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock)) := by
    simp only [List.map_nil]
    exact tailRepr_genesisState n.val G
  have hsound := foldSched_sound_aux hn hq hera bs [] (genesisState n.val G)
    hSig hbase_rep hbase_sched hFold
  simp only [List.nil_append] at hsound
  exact hsound

theorem cert_step_lock_be_sound {n q : U64} {st : CertStateG U64} {g : U64} {b : molt_petit.Block}
    (hn : 1 ≤ n.val)
    (h : cert_step_lock_be UBK () n q st g (toBlockG b) b.key_index = ok true) :
    cert_step_core_be UBK () n q st (toBlockG b) = ok true ∧
    g.val ≤ (toModelBlock b).keyIndex ∧
    (st.tip_slot.val / n.val = (toModelBlock b).slot / n.val → g.val = (toModelBlock b).keyIndex) := by
  dsimp [cert_step_lock_be] at h
  obtain ⟨core, hcore, h⟩ := bind_inv h
  obtain ⟨below, hbelow, h⟩ := bind_inv h
  obtain ⟨ge, hge, h⟩ := bind_inv h
  obtain ⟨w_tip, hw_tip, h⟩ := bind_inv h
  obtain ⟨w_b, hw_b, h⟩ := bind_inv h
  obtain ⟨same, hsame, h⟩ := bind_inv h
  obtain ⟨keeps, hkeeps, h⟩ := bind_inv h
  obtain ⟨nsame, hnsame, h⟩ := bind_inv h
  obtain ⟨mix_ok, hmix_ok, h⟩ := bind_inv h
  obtain ⟨t, ht, h⟩ := bind_inv h
  split at h
  · rename_i hcore_t
    injection h with h; subst h
    rw [hcore_t] at hcore
    split at ht
    · rename_i hge_t
      injection ht with ht; subst ht
      injection hge with hge
      have hnot_below : below = false := by
        cases below <;> simp_all
      rw [hnot_below] at hbelow
      injection hbelow with hbelow
      simp only [decide_eq_false_iff_not] at hbelow
      change ¬ (b.key_index.val < g.val) at hbelow
      have hle : g.val ≤ b.key_index.val := by omega
      have hw_tip_val := ubk_div_val (by omega) hw_tip
      have hw_b_val := ubk_div_val (by omega) hw_b
      split at hmix_ok
      · rename_i hnsame_t
        injection hnsame with hnsame
        have hsame_f : same = false := by
          cases same <;> simp_all
        rw [hsame_f] at hsame
        injection hsame with hsame
        simp only [decide_eq_false_iff_not] at hsame
        refine ⟨hcore, hle, ?_⟩
        intro hdiv
        exfalso
        apply hsame
        apply UScalar.eq_of_val_eq
        rw [hw_tip_val, hw_b_val, hdiv]
        rfl
      · rename_i hnsame_f
        injection hmix_ok with hmix_ok
        rw [hmix_ok] at hkeeps
        injection hkeeps with hkeeps
        simp only [decide_eq_true_eq] at hkeeps
        refine ⟨hcore, hle, ?_⟩
        intro _
        rw [hkeeps]
        rfl
    · injection ht with ht; contradiction
  · injection h with h; contradiction



lemma list_getLast_congr {α : Type} {l1 l2 : List α} (h : l1 = l2) (h1 : l1 ≠ []) (h2 : l2 ≠ []) :
    l1.getLast h1 = l2.getLast h2 := by
  subst h; rfl

lemma foldLock_sound_aux {n q : U64} {G : Block}
    {Signed : MoltPetit.Model.Block → Prop}
    (hn : 1 ≤ n.val) (hq : quorum n = ok q) :
    ∀ (bs : List Block) (pre : List Block) (st : CertStateG U64) (g : U64),
    (∀ b ∈ bs, Signed (toModelBlock b)) →
    TailRepr n.val st (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) →
    g = ((G :: pre).getLast (List.cons_ne_nil _ _)).key_index →
    MoltPetit.Model.GroundedCertLock n.val Signed (toModelBlock G)
      (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) g.val →
    FoldLock n q st g bs →
    MoltPetit.Model.GroundedCertLock n.val Signed (toModelBlock G)
      (modelClaimOf n.val (toModelBlock G) ((pre ++ bs).map toModelBlock))
      (((G :: pre ++ bs).getLast (List.cons_ne_nil _ _)).key_index.val) := by
  intro bs
  induction bs with
  | nil =>
    intro pre st g hSig hrep hg hlock hfold
    simp only [List.append_nil]
    rw [← hg]
    exact hlock
  | cons b rest ih =>
    intro pre st g hSig hrep hg hlock hfold
    obtain ⟨hstep, t', ht', hfold_rest⟩ := hfold
    obtain ⟨hcore, hle, hkeeps⟩ := cert_step_lock_be_sound hn hstep
    obtain ⟨hheight, hslot, hprev, hdense⟩ := cert_step_core_be_sound b hq hn hrep hcore
    have hSig_b : Signed (toModelBlock b) := hSig b (by simp)
    have hSig_rest : ∀ x ∈ rest, Signed (toModelBlock x) := fun x hx => hSig x (by simp [hx])
    let cl := modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)
    have hkeeps_cl : cl.tipSlot / n.val = (toModelBlock b).slot / n.val → g.val = (toModelBlock b).keyIndex := by
      intro hdiv
      rw [← hrep.tip_slot] at hdiv
      exact hkeeps hdiv
    have hlock' := MoltPetit.Model.GroundedCertLock.extend cl g.val (toModelBlock b)
      hlock hheight hslot hprev hSig_b hle hkeeps_cl hdense
    have hcl_eq : modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock ++ [toModelBlock b]) =
        { tipId := (toModelBlock b).id,
          tipSlot := (toModelBlock b).slot,
          tipHeight := (toModelBlock b).height,
          tail := (cl.tail ++ [toModelBlock b]).filter
            fun x => decide ((toModelBlock b).slot + 2 - n.val ≤ x.slot) } :=
      modelClaimOf_step_lt n.val (toModelBlock G) (pre.map toModelBlock) (toModelBlock b) hslot
    have hmap_app : (pre ++ [b]).map toModelBlock = pre.map toModelBlock ++ [toModelBlock b] := by
      simp
    have hlock_step : MoltPetit.Model.GroundedCertLock n.val Signed
        (toModelBlock G) (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock))
        b.key_index.val := by
      rw [hmap_app, hcl_eq]
      exact hlock'
    have hrep' := cert_next_tail_be_repr b hq hn hrep hcore ht'
    have hrep_step : TailRepr n.val (stepState b t')
        (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock)) := by
      rw [hmap_app, hcl_eq]
      exact hrep'
    have hlast_b : (G :: (pre ++ [b])).getLast (List.cons_ne_nil _ _) = b := by
      change ((G :: pre) ++ [b]).getLast _ = b
      exact List.getLast_append_singleton (G :: pre)
    have hg_step : b.key_index = ((G :: (pre ++ [b])).getLast (List.cons_ne_nil _ _)).key_index := by
      rw [hlast_b]
    have hres := ih (pre ++ [b]) (stepState b t') b.key_index hSig_rest hrep_step hg_step hlock_step hfold_rest
    rw [List.append_assoc, List.singleton_append] at hres
    have hcons_eq : (G :: (pre ++ [b]) ++ rest) = (G :: pre ++ (b :: rest)) := by simp
    have hlast_eq := list_getLast_congr hcons_eq (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    rw [hlast_eq] at hres
    exact hres

theorem cert_fold_lock_sound : MoltPaper.thm_cert_fold_lock_sound := by
  intro n q G bs Signed hn hq hG hSigG hSig hFold
  have ⟨hgen, hslot0⟩ := cert_genesis_ok_be_sound hG
  have hbase_lock : MoltPetit.Model.GroundedCertLock n.val Signed
      (toModelBlock G) (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock))
      G.key_index.val := by
    simp only [List.map_nil]
    have hnil := modelClaimOf_nil n.val (toModelBlock G)
    rw [hnil]
    exact MoltPetit.Model.GroundedCertLock.genesis hgen hslot0 hSigG
  have hbase_rep : TailRepr n.val (genesisState n.val G)
      (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock)) := by
    simp only [List.map_nil]
    exact tailRepr_genesisState n.val G
  have hsound := foldLock_sound_aux hn hq bs [] (genesisState n.val G) G.key_index
    hSig hbase_rep rfl hbase_lock hFold
  simp only [List.nil_append] at hsound
  exact hsound


def floorsLen : FloorsG U64 → Nat
  | .FNil => 0
  | .FCons _ tl => floorsLen tl + 1

@[simp] lemma floorsLen_nil : floorsLen (.FNil : FloorsG U64) = 0 := rfl
@[simp] lemma floorsLen_cons (f : U64) (tl : FloorsG U64) :
    floorsLen (.FCons f tl) = floorsLen tl + 1 := rfl

@[simp] lemma floorsLen_zeroFloors : ∀ k : Nat, floorsLen (zeroFloors k) = k
  | 0 => rfl
  | k + 1 => by simp [zeroFloors, floorsLen_zeroFloors k]

lemma floorsLen_initFloors : ∀ (n : Nat) (gki : U64), floorsLen (initFloors n gki) = n
  | 0, _ => rfl
  | k + 1, _ => by simp [initFloors, floorsLen_zeroFloors]

lemma floorsFun_zeroFloors : ∀ (k : Nat) (i : Nat), floorsFun (zeroFloors k) i = 0
  | 0, _ => rfl
  | k + 1, 0 => rfl
  | k + 1, i + 1 => by simp [zeroFloors, floorsFun, floorsFun_zeroFloors k i]

lemma floorsFun_initFloors (n : Nat) (hn : 1 ≤ n) (gki : U64) :
    floorsFun (initFloors n gki) = fun i => if i = 0 then gki.val else 0 := by
  funext i
  cases n with
  | zero => contradiction
  | succ k =>
    cases i with
    | zero =>
      simp [initFloors, floorsFun]
    | succ m =>
      simp [initFloors, floorsFun, floorsFun_zeroFloors]

theorem floors_ok_be_corr : ∀ (fl : FloorsG U64) (i p ki : U64),
    floors_ok_be UBK () fl i p ki = ok true →
    ∀ (k : Nat), p.val = i.val + k → floorsFun fl k ≤ ki.val := by
  intro fl
  induction fl with
  | FNil =>
    intro i p ki _ k _
    cases k <;> simp [floorsFun]
  | FCons f tl ih =>
    intro i p ki h k hk
    simp only [floors_ok_be, UBK] at h
    obtain ⟨me, hme, h⟩ := bind_inv h
    obtain ⟨below, hbelow, h⟩ := bind_inv h
    obtain ⟨bad, hbad, h⟩ := bind_inv h
    obtain ⟨ok1, hok1, h⟩ := bind_inv h
    obtain ⟨t, ht, h⟩ := bind_inv h
    obtain ⟨i1, hi1, h⟩ := bind_inv h
    obtain ⟨more, hmore, h⟩ := bind_inv h
    cases ok1 with
    | false =>
      dsimp [U64Backend.Insts.Molt_petitBackendU64Bool.and] at h
      injection h with h
      contradiction
    | true =>
      dsimp [U64Backend.Insts.Molt_petitBackendU64Bool.and] at h
      injection h with h; subst h
      injection ht with ht; subst ht
      have hi1_val : i1.val = i.val + 1 := by
        have hadd := UScalar.add_equiv i 1#u64
        simp only [U64Backend.Insts.Molt_petitBackendU64Bool.add] at hi1
        simp only [hi1] at hadd
        exact hadd.2.1
      dsimp [U64Backend.Insts.Molt_petitBackendU64Bool.not] at hok1
      injection hok1 with hok1
      cases bad
      · dsimp [U64Backend.Insts.Molt_petitBackendU64Bool.and] at hbad
        dsimp [U64Backend.Insts.Molt_petitBackendU64Bool.eq] at hme
        dsimp [U64Backend.Insts.Molt_petitBackendU64Bool.lt] at hbelow
        cases k with
        | zero =>
          simp only [Nat.add_zero] at hk
          have hp_eq_i : p = i := UScalar.eq_of_val_eq hk
          have hi_eq_p : i = p := hp_eq_i.symm
          subst hi_eq_p
          simp only [decide_true] at hme
          injection hme with hme; subst hme
          simp only [if_true] at hbad
          injection hbad with hbad; subst hbad
          injection hbelow with hbelow
          simp only [decide_eq_false_iff_not] at hbelow
          change ¬ (ki.val < f.val) at hbelow
          change f.val ≤ ki.val
          omega
        | succ m =>
          change floorsFun tl m ≤ ki.val
          apply ih i1 p ki hmore m
          rw [hi1_val]
          omega
      · contradiction

lemma floors_bump_be_corr : ∀ (fl : FloorsG U64) (i p ki : U64) (fl' : FloorsG U64),
    floors_bump_be UBK () fl i p ki = ok fl' →
    floorsLen fl' = floorsLen fl ∧
    ∀ (k : Nat), floorsFun fl' k =
      if p.val = i.val + k ∧ k < floorsLen fl then
        max (floorsFun fl k) ki.val
      else
        floorsFun fl k := by
  intro fl
  induction fl with
  | FNil =>
    intro i p ki fl' h
    simp only [floors_bump_be, UBK] at h
    injection h with h; subst h
    simp [floorsLen]
  | FCons f tl ih =>
    intro i p ki fl' h
    simp only [floors_bump_be, UBK] at h
    obtain ⟨me, hme, h⟩ := bind_inv h
    obtain ⟨raise, hraise, h⟩ := bind_inv h
    obtain ⟨up, hup, h⟩ := bind_inv h
    obtain ⟨nf, hnf, h⟩ := bind_inv h
    obtain ⟨t, ht, h⟩ := bind_inv h
    obtain ⟨i1, hi1, h⟩ := bind_inv h
    obtain ⟨fg, hfg, h⟩ := bind_inv h
    injection h with h; subst h
    injection ht with ht; subst ht
    have hi1_val : i1.val = i.val + 1 := by
      have hadd := UScalar.add_equiv i 1#u64
      simp only [U64Backend.Insts.Molt_petitBackendU64Bool.add] at hi1
      simp only [hi1] at hadd
      exact hadd.2.1
    have ⟨hlen_fg, ih_fg⟩ := ih i1 p ki fg hfg
    have hlen_cons : floorsLen (FloorsG.FCons nf fg) = floorsLen (FloorsG.FCons f tl) := by
      simp [floorsLen, hlen_fg]
    refine ⟨hlen_cons, ?_⟩
    intro k
    have hnf_val := ubk_select_val hnf
    dsimp [U64Backend.Insts.Molt_petitBackendU64Bool.eq] at hme
    injection hme with hme; subst hme
    dsimp [U64Backend.Insts.Molt_petitBackendU64Bool.lt] at hraise
    injection hraise with hraise; subst hraise
    dsimp [U64Backend.Insts.Molt_petitBackendU64Bool.and] at hup
    have hnf_cases : nf.val = if p.val = i.val then max f.val ki.val else f.val := by
      by_cases hpi : p.val = i.val
      · rw [if_pos hpi]
        have hp_eq : p = i := UScalar.eq_of_val_eq hpi
        have hi_eq : i = p := hp_eq.symm
        subst hi_eq
        simp only [decide_true, if_true] at hup
        injection hup with hup; subst hup
        by_cases hfk : f.val < ki.val
        · have hdec : decide (f < ki) = true := by
            simp only [decide_eq_true_eq]
            exact hfk
          rw [hdec] at hnf
          have hval := ubk_select_val_true f hnf
          subst hval
          omega
        · have hdec : decide (f < ki) = false := by
            simp only [decide_eq_false_iff_not]
            exact hfk
          rw [hdec] at hnf
          have hval := ubk_select_val_false ki hnf
          subst hval
          omega
      · rw [if_neg hpi]
        have hne : ¬ (i = p) := fun h => hpi (by rw [h])
        have : decide (i = p) = false := by simp [hne]
        rw [this] at hup
        injection hup with hup; subst hup
        have hval := ubk_select_val_false ki hnf
        subst hval
        rfl
    cases k with
    | zero =>
      change nf.val = if p.val = i.val + 0 ∧ 0 < floorsLen tl + 1 then
        max f.val ki.val else f.val
      rw [hnf_cases]
      have : 0 < floorsLen tl + 1 := by omega
      simp only [this, and_true, Nat.add_zero]
    | succ m =>
      change floorsFun fg m =
        if p.val = i.val + (m + 1) ∧ m + 1 < floorsLen tl + 1 then
          max (floorsFun tl m) ki.val
        else
          floorsFun tl m
      rw [ih_fg m]
      have hcond : (p.val = i1.val + m ∧ m < floorsLen tl) ↔
          (p.val = i.val + (m + 1) ∧ m + 1 < floorsLen tl + 1) := by
        rw [hi1_val]
        omega
      by_cases hp : (p.val = i1.val + m ∧ m < floorsLen tl)
      · have hp2 : (p.val = i.val + (m + 1) ∧ m + 1 < floorsLen tl + 1) := hcond.mp hp
        rw [if_pos hp, if_pos hp2]
      · have hp2 : ¬ (p.val = i.val + (m + 1) ∧ m + 1 < floorsLen tl + 1) :=
          fun h => hp (hcond.mpr h)
        rw [if_neg hp, if_neg hp2]

lemma cert_next_floors_be_sound {n : U64} (hn : 1 ≤ n.val)
    {fl : FloorsG U64} {b : molt_petit.Block} {fl' : FloorsG U64}
    (hlen : floorsLen fl = n.val)
    (h : cert_next_floors_be UBK () n fl (toBlockG b) b.key_index = ok fl') :
    floorsLen fl' = n.val ∧
    floorsFun fl' = (fun i =>
      if MoltPetit.Model.producerForSlot n.val (toModelBlock b).slot = i then
        max (floorsFun fl i) (toModelBlock b).keyIndex
      else
        floorsFun fl i) := by
  dsimp [cert_next_floors_be] at h
  obtain ⟨p, hp, h⟩ := bind_inv h
  obtain ⟨t, ht, h⟩ := bind_inv h
  injection ht with ht; subst ht
  have hpv := ubk_rem_val (by omega) hp
  have ⟨hlen', hbump⟩ := floors_bump_be_corr fl 0#u64 p b.key_index fl' h
  rw [hlen] at hlen' hbump
  refine ⟨hlen', ?_⟩
  funext i
  rw [hbump i]
  have hprod : MoltPetit.Model.producerForSlot n.val (toModelBlock b).slot = p.val := by
    dsimp [MoltPetit.Model.producerForSlot]
    rw [hpv]
    rfl
  have hki : (toModelBlock b).keyIndex = b.key_index.val := rfl
  rw [hprod, hki]
  have hplt : p.val < n.val := by
    rw [hpv]
    exact Nat.mod_lt _ (by omega)
  have h0 : (0#u64 : U64).val = 0 := rfl
  rw [h0, Nat.zero_add]
  by_cases hpi : p.val = i
  · have hi : i < n.val := by omega
    have hcond : (p.val = i ∧ i < n.val) := ⟨hpi, hi⟩
    rw [if_pos hcond, if_pos hpi]
  · have hcond : ¬ (p.val = i ∧ i < n.val) := fun h => hpi h.1
    rw [if_neg hcond, if_neg hpi]

theorem cert_step_k_be_sound {n q : U64} {st : CertStateG U64} {fl : FloorsG U64}
    {b : molt_petit.Block} (hn : 1 ≤ n.val)
    (h : cert_step_k_be UBK () n q st fl (toBlockG b) b.key_index = ok true) :
    cert_step_core_be UBK () n q st (toBlockG b) = ok true ∧
    floorsFun fl (MoltPetit.Model.producerForSlot n.val (toModelBlock b).slot) ≤
      (toModelBlock b).keyIndex := by
  dsimp [cert_step_k_be] at h
  obtain ⟨core, hcore, h⟩ := bind_inv h
  obtain ⟨p, hp, h⟩ := bind_inv h
  obtain ⟨t, ht, h⟩ := bind_inv h
  obtain ⟨fl_ok, hfl_ok, h⟩ := bind_inv h
  split at h
  · rename_i hcore_t
    injection h with h; subst h
    rw [hcore_t] at hcore
    injection ht with ht; subst ht
    have hpv := ubk_rem_val (by omega) hp
    have h0 : (0#u64 : U64).val = 0 := rfl
    have hcorr := floors_ok_be_corr fl 0#u64 p b.key_index hfl_ok p.val (by rw [h0, Nat.zero_add])
    have hprod : MoltPetit.Model.producerForSlot n.val (toModelBlock b).slot = p.val := by
      dsimp [MoltPetit.Model.producerForSlot]
      rw [hpv]
      rfl
    have hki : (toModelBlock b).keyIndex = b.key_index.val := rfl
    rw [hprod, hki]
    exact ⟨hcore, hcorr⟩
  · injection h with h; contradiction

lemma foldK_sound_aux {n q : U64} {G : Block}
    {Signed : MoltPetit.Model.Block → Prop}
    (hn : 1 ≤ n.val) (hq : quorum n = ok q) :
    ∀ (bs : List Block) (pre : List Block) (st : CertStateG U64)
      (fl : FloorsG U64) (out : FloorsG U64),
    (∀ b ∈ bs, Signed (toModelBlock b)) →
    TailRepr n.val st (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) →
    floorsLen fl = n.val →
    MoltPetit.Model.GroundedCertK n.val Signed (toModelBlock G)
      (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) (floorsFun fl) →
    FoldK n q st fl bs out →
    MoltPetit.Model.GroundedCertK n.val Signed (toModelBlock G)
      (modelClaimOf n.val (toModelBlock G) ((pre ++ bs).map toModelBlock)) (floorsFun out) := by
  intro bs
  induction bs with
  | nil =>
    intro pre st fl out hSig hrep hlen hK hfold
    simp only [List.append_nil]
    dsimp [FoldK] at hfold
    subst hfold
    exact hK
  | cons b rest ih =>
    intro pre st fl out hSig hrep hlen hK hfold
    obtain ⟨hstep, t', fl', ht', hfl', hfold_rest⟩ := hfold
    obtain ⟨hcore, hle⟩ := cert_step_k_be_sound hn hstep
    obtain ⟨hheight, hslot, hprev, hdense⟩ := cert_step_core_be_sound b hq hn hrep hcore
    have hSig_b : Signed (toModelBlock b) := hSig b (by simp)
    have hSig_rest : ∀ x ∈ rest, Signed (toModelBlock x) :=
      fun x hx => hSig x (by simp [hx])
    let cl := modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)
    have hK' := MoltPetit.Model.GroundedCertK.extend cl (floorsFun fl) (toModelBlock b)
      hK hheight hslot hprev hSig_b hle hdense
    have ⟨hlen', hfun'⟩ := cert_next_floors_be_sound hn hlen hfl'
    have hcl_eq : modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock ++ [toModelBlock b]) =
        { tipId := (toModelBlock b).id,
          tipSlot := (toModelBlock b).slot,
          tipHeight := (toModelBlock b).height,
          tail := (cl.tail ++ [toModelBlock b]).filter
            fun x => decide ((toModelBlock b).slot + 2 - n.val ≤ x.slot) } :=
      modelClaimOf_step_lt n.val (toModelBlock G) (pre.map toModelBlock) (toModelBlock b) hslot
    have hmap_app : (pre ++ [b]).map toModelBlock = pre.map toModelBlock ++ [toModelBlock b] := by
      simp
    have hK_step : MoltPetit.Model.GroundedCertK n.val Signed
        (toModelBlock G) (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock))
        (floorsFun fl') := by
      rw [hmap_app, hcl_eq, hfun']
      exact hK'
    have hrep' := cert_next_tail_be_repr b hq hn hrep hcore ht'
    have hrep_step : TailRepr n.val (stepState b t')
        (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock)) := by
      rw [hmap_app, hcl_eq]
      exact hrep'
    have hres := ih (pre ++ [b]) (stepState b t') fl' out hSig_rest
      hrep_step hlen' hK_step hfold_rest
    rw [List.append_assoc, List.singleton_append] at hres
    exact hres

theorem cert_fold_k_sound : MoltPaper.thm_cert_fold_k_sound := by
  intro n q G bs out Signed hn hq hG hSigG hSig hFold
  have ⟨hgen, hslot0⟩ := cert_genesis_ok_be_sound hG
  have hbase_K : MoltPetit.Model.GroundedCertK n.val Signed
      (toModelBlock G) (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock))
      (floorsFun (initFloors n.val G.key_index)) := by
    simp only [List.map_nil]
    have hnil := modelClaimOf_nil n.val (toModelBlock G)
    rw [hnil]
    have hfun := floorsFun_initFloors n.val hn G.key_index
    rw [hfun]
    have hslot0_m : (toModelBlock G).slot = 0 := hslot0
    have hprod0 : MoltPetit.Model.producerForSlot n.val (toModelBlock G).slot = 0 := by
      dsimp [MoltPetit.Model.producerForSlot]
      rw [hslot0_m]
      exact Nat.zero_mod n.val
    have hfun_eq : (fun i => if i = 0 then G.key_index.val else 0) =
        (fun i => if MoltPetit.Model.producerForSlot n.val (toModelBlock G).slot = i then
          max 0 (toModelBlock G).keyIndex else 0) := by
      funext i
      rw [hprod0]
      have hki : (toModelBlock G).keyIndex = G.key_index.val := rfl
      rw [hki]
      have hmax : max 0 G.key_index.val = G.key_index.val := by omega
      rw [hmax]
      by_cases hi : i = 0
      · subst hi; simp
      · have : ¬ (0 = i) := fun hc => hi hc.symm
        simp [hi, this]
    rw [hfun_eq]
    exact MoltPetit.Model.GroundedCertK.genesis hgen hslot0 hSigG
  have hbase_rep : TailRepr n.val (genesisState n.val G)
      (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock)) := by
    simp only [List.map_nil]
    exact tailRepr_genesisState n.val G
  have hlen0 : floorsLen (initFloors n.val G.key_index) = n.val :=
    floorsLen_initFloors n.val G.key_index
  have hsound := foldK_sound_aux hn hq bs [] (genesisState n.val G)
    (initFloors n.val G.key_index) out hSig hbase_rep hlen0 hbase_K hFold
  simp only [List.nil_append] at hsound
  exact hsound

end Rust
