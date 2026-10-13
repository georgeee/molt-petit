import Rust.Equiv
import Rust.FoldStep
import MoltPetit.Model.Soundness
import MoltPetit.Model.Pass28
import Spec.Statements

open Aeneas Std Result

namespace Rust

open molt_petit

theorem u64_add_ok {x y : U64} (h : x.val + y.val < 2 ^ 64) :
    ∃ z : U64, x + y = ok z ∧ z.val = x.val + y.val := by
  have hadd := UScalar.add_equiv x y
  cases hxy : x + y with
  | ok z =>
    rw [hxy] at hadd
    exact ⟨z, rfl, hadd.2.1⟩
  | fail e =>
    rw [hxy] at hadd
    exfalso
    exact hadd (by simp only [UScalar.inBounds, UScalarTy.numBits]; omega)
  | div =>
    rw [hxy] at hadd
    exact False.elim hadd

theorem hashToNat_inj {x y : molt_petit.Hash} (h : hashToNat x = hashToNat y) : x = y := by
  obtain ⟨xa, xb, xc, xd⟩ := x
  obtain ⟨ya, yb, yc, yd⟩ := y
  have hxa : xa.val < 2 ^ 64 := by scalar_tac
  have hxb : xb.val < 2 ^ 64 := by scalar_tac
  have hxc : xc.val < 2 ^ 64 := by scalar_tac
  have hxd : xd.val < 2 ^ 64 := by scalar_tac
  have hya : ya.val < 2 ^ 64 := by scalar_tac
  have hyb : yb.val < 2 ^ 64 := by scalar_tac
  have hyc : yc.val < 2 ^ 64 := by scalar_tac
  have hyd : yd.val < 2 ^ 64 := by scalar_tac
  dsimp [hashToNat] at h
  have ha : xa = ya := UScalar.val_eq_imp _ _ (by omega)
  have hb : xb = yb := UScalar.val_eq_imp _ _ (by omega)
  have hc : xc = yc := UScalar.val_eq_imp _ _ (by omega)
  have hd : xd = yd := UScalar.val_eq_imp _ _ (by omega)
  rw [ha, hb, hc, hd]

@[simp] theorem hash_eq_self (x : Hash) : molt_petit.hash_eq x x = ok true := by
  unfold molt_petit.hash_eq; simp

theorem genesis_ok_be_complete {b : Block}
    (h : MoltPetit.Model.genesisOk (toModelBlock b) = true) :
    genesis_ok_be UB () (toBlockG b) = ok true := by
  dsimp [toModelBlock, MoltPetit.Model.genesisOk] at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨hh, hp⟩ := h
  have h0 : (0#u64 : U64).val = 0 := rfl
  have hhb : b.height = 0#u64 := UScalar.val_eq_imp _ _ (by rw [h0]; exact hh)
  cases hpv : b.prev with
  | none =>
    dsimp [genesis_ok_be, UB, toBlockG,
      U64Backend.Insts.Molt_petitBackendU64Bool.zero,
      U64Backend.Insts.Molt_petitBackendU64Bool.eq,
      U64Backend.Insts.Molt_petitBackendU64Bool.bool_const,
      U64Backend.Insts.Molt_petitBackendU64Bool.not,
      U64Backend.Insts.Molt_petitBackendU64Bool.and]
    rw [hpv]
    dsimp
    rw [hhb]
    rfl
  | some p =>
    rw [hpv] at hp
    simp only [Option.map_some] at hp
    contradiction

theorem child_ok_be_complete {parent child : Block}
    (hp_bound : parent.height.val < 2 ^ 62)
    (h : MoltPetit.Model.childOk (toModelBlock parent) (toModelBlock child) = true) :
    child_ok_be UB () (toBlockG parent) (toBlockG child) = ok true := by
  dsimp [toModelBlock, MoltPetit.Model.childOk] at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨hh, hs, hp⟩ := h
  have h1 : (1#u64 : U64).val = 1 := rfl
  have hsucc : ∃ succ : U64, parent.height + 1#u64 = ok succ ∧ succ.val = parent.height.val + 1 :=
    u64_add_ok (by rw [h1]; omega)
  obtain ⟨succ, hsucc_eq, hsucc_val⟩ := hsucc
  have hchild_h : child.height = succ := UScalar.val_eq_imp _ _ (by rw [hsucc_val]; exact hh)
  have hlt : decide (parent.slot < child.slot) = true := decide_eq_true hs
  cases hpv : child.prev with
  | none =>
    rw [hpv] at hp
    contradiction
  | some p =>
    rw [hpv] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    have hp_eq : p = parent.id := hashToNat_inj hp
    subst hp_eq
    simp only [child_ok_be, UB, toBlockG,
      U64Backend.Insts.Molt_petitBackendU64Bool.one,
      U64Backend.Insts.Molt_petitBackendU64Bool.add,
      U64Backend.Insts.Molt_petitBackendU64Bool.eq,
      U64Backend.Insts.Molt_petitBackendU64Bool.lt,
      U64Backend.Insts.Molt_petitBackendU64Bool.bool_const,
      U64Backend.Insts.Molt_petitBackendU64Bool.and,
      bind_tc_ok, hsucc_eq, hchild_h, hlt, hpv]
    simp only [hashg_eq_eq, hash_eq_self, bind_tc_ok]
    rfl


theorem links_from_be_complete : ∀ (parent : Block) (c : Chain),
    parent.height.val < 2 ^ 62 →
    (∀ b ∈ toModelChain c, b.height < 2 ^ 62) →
    MoltPetit.Model.linksOk (toModelBlock parent :: toModelChain c) = true →
    links_from_be UB () (toBlockG parent) (toChainG c) = ok true := by
  intro parent c
  induction c generalizing parent with
  | Nil =>
    intro _ _ _
    simp only [toChainG_nil, links_from_be, UB,
      U64Backend.Insts.Molt_petitBackendU64Bool.bool_const]
  | Cons b tl ih =>
    intro hp_bound htl_bound hOk
    simp only [toModelChain_cons, MoltPetit.Model.linksOk, Bool.and_eq_true] at hOk
    obtain ⟨hchild, hrest⟩ := hOk
    have hhere := child_ok_be_complete hp_bound hchild
    have hb_bound : b.height.val < 2 ^ 62 := by
      have : toModelBlock b ∈ toModelChain (Chain.Cons b tl) := by simp [toModelChain]
      have := htl_bound (toModelBlock b) this
      exact this
    have htl_bound' : ∀ x ∈ toModelChain tl, x.height < 2 ^ 62 := by
      intro x hx
      have : x ∈ toModelChain (Chain.Cons b tl) := by simp [toModelChain, hx]
      exact htl_bound x this
    have hih := ih b hb_bound htl_bound' hrest
    simp only [toChainG_cons, links_from_be, UB,
      U64Backend.Insts.Molt_petitBackendU64Bool.and,
      bind_tc_ok, hhere, hih]
    rfl

theorem links_ok_be_complete {c : Chain}
    (hbound : ∀ b ∈ toModelChain c, b.height < 2 ^ 62)
    (h : MoltPetit.Model.linksOk (toModelChain c) = true) :
    links_ok_be UB () (toChainG c) = ok true := by
  cases c with
  | Nil =>
    simp only [toChainG_nil, links_ok_be, UB,
      U64Backend.Insts.Molt_petitBackendU64Bool.bool_const]
  | Cons g tl =>
    simp only [toChainG_cons, links_ok_be]
    have hg_bound : g.height.val < 2 ^ 62 := by
      have : toModelBlock g ∈ toModelChain (Chain.Cons g tl) := by simp [toModelChain]
      exact hbound (toModelBlock g) this
    have htl_bound : ∀ b ∈ toModelChain tl, b.height < 2 ^ 62 := by
      intro b hb
      have : b ∈ toModelChain (Chain.Cons g tl) := by simp [toModelChain, hb]
      exact hbound b this
    exact links_from_be_complete g tl hg_bound htl_bound h


theorem tip_slot_from_be_complete : ∀ (c : Chain) (cur : U64),
    ∃ r : U64, tip_slot_from_be UB () cur (toChainG c) = ok r ∧
      (match (toModelChain c).getLast? with
       | some tip => r.val = tip.slot
       | none => r = cur) := by
  intro c
  induction c with
  | Nil =>
    intro cur
    refine ⟨cur, by simp [toChainG_nil, tip_slot_from_be], ?_⟩
    simp [toModelChain]
  | Cons b tl ih =>
    intro cur
    simp only [toChainG_cons, tip_slot_from_be, toBlockG_slot]
    obtain ⟨r, hr, hval⟩ := ih b.slot
    refine ⟨r, hr, ?_⟩
    simp only [toModelChain_cons]
    cases htl : toModelChain tl with
    | nil =>
      simp only [htl] at hval
      subst hval
      simp [toModelBlock]
    | cons b' tl' =>
      rw [htl] at hval
      simp only [List.getLast?_cons_cons]
      exact hval


theorem u64_backend_not (a : Bool) :
    U64Backend.Insts.Molt_petitBackendU64Bool.not () a = ok (!a) := by
  cases a <;> rfl

theorem u64_backend_and (a b : Bool) :
    U64Backend.Insts.Molt_petitBackendU64Bool.and () a b = ok (a && b) := by
  cases a <;> rfl

theorem u64_backend_or (a b : Bool) :
    U64Backend.Insts.Molt_petitBackendU64Bool.or () a b = ok (a || b) := by
  cases a <;> rfl

theorem u64_backend_bool_to_num (b : Bool) :
    U64Backend.Insts.Molt_petitBackendU64Bool.bool_to_num () b = ok (if b then 1#u64 else 0#u64) := by
  cases b <;> rfl

theorem window_count_be_complete : ∀ (c : Chain) (u len : U64),
    u.val + len.val < 2 ^ 64 →
    MoltPetit.Model.windowCount (toModelChain c) u.val len.val < 2 ^ 64 →
    ∃ w : U64, window_count_be UB () (toChainG c) u len = ok w ∧
      w.val = MoltPetit.Model.windowCount (toModelChain c) u.val len.val := by
  intro c
  induction c with
  | Nil =>
    intro u len _ _
    simp only [toChainG_nil, window_count_be, UB,
      U64Backend.Insts.Molt_petitBackendU64Bool.zero]
    refine ⟨0#u64, rfl, ?_⟩
    simp [toModelChain, MoltPetit.Model.windowCount]
  | Cons b tl ih =>
    intro u len hun hwc
    rw [toModelChain_cons, model_windowCount_cons] at hwc
    have hwc_tl : MoltPetit.Model.windowCount (toModelChain tl) u.val len.val < 2 ^ 64 := by omega
    obtain ⟨rest, hrest, hrest_val⟩ := ih u len hun hwc_tl
    obtain ⟨hi, hhi, hhi_val⟩ := u64_add_ok hun
    set inw : Bool := (!decide (b.slot < u)) && decide (b.slot < hi)
    set here : U64 := if inw then 1#u64 else 0#u64
    have hinw_eq : inw = MoltPetit.Model.blockInWindow u.val len.val (toModelBlock b) := by
      dsimp [inw, MoltPetit.Model.blockInWindow, toModelBlock]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : u.val ≤ b.slot.val := by scalar_tac
        have h2' : b.slot.val < hi.val := by scalar_tac
        have : b.slot.val < u.val + len.val := by omega
        exact ⟨h1', this⟩
      · rintro ⟨h1, h2⟩
        have h2' : b.slot.val < hi.val := by omega
        refine ⟨by scalar_tac, by scalar_tac⟩
    have hhere_val : here.val = if MoltPetit.Model.blockInWindow u.val len.val (toModelBlock b) then 1 else 0 := by
      rw [← hinw_eq]
      dsimp [here]
      cases inw <;> rfl
    have hsum : here.val + rest.val < 2 ^ 64 := by
      rw [hhere_val, hrest_val]
      exact hwc
    obtain ⟨w, hw, hw_val⟩ := u64_add_ok hsum
    refine ⟨w, ?_, ?_⟩
    · simp only [toChainG_cons, window_count_be, toBlockG_slot, UB,
        U64Backend.Insts.Molt_petitBackendU64Bool.lt,
        u64_backend_not,
        U64Backend.Insts.Molt_petitBackendU64Bool.add,
        u64_backend_and, u64_backend_bool_to_num,
        bind_tc_ok, hhi, hrest]
      change here + rest = ok w
      exact hw
    · rw [hw_val, hhere_val, hrest_val, toModelChain_cons, model_windowCount_cons]

theorem window_dense_be_ok {c : Chain} {u n q : U64}
    (h_u_n : u.val + n.val < 2 ^ 64)
    (h_wc : MoltPetit.Model.windowCount (toModelChain c) u.val n.val < 2 ^ 64)
    (hq : quorum n = ok q) :
    ∃ d : Bool, window_dense_be UB () q (toChainG c) u n = ok d ∧
      (d = true ↔ MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (toModelChain c) u.val n.val) := by
  obtain ⟨w, hw, hw_val⟩ := window_count_be_complete c u n h_u_n h_wc
  have hqv := quorum_val_of_ok hq
  simp only [window_dense_be, UB,
    U64Backend.Insts.Molt_petitBackendU64Bool.lt,
    u64_backend_not,
    bind_tc_ok, hw]
  refine ⟨!decide (w < q), rfl, ?_⟩
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  have hnot_lt : (¬ w < q) ↔ q.val ≤ w.val := by
    constructor
    · intro h; scalar_tac
    · intro h; scalar_tac
  rw [hnot_lt, hw_val, hqv]

end Rust
