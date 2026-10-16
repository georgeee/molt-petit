import Rust.Equiv
import Rust.FoldStep
import MoltPetit.Model.Soundness
import MoltPetit.Model.Pass28
import MoltPetit.Model.KeyStealingCert
import MoltPetit.Model.KeyStealingScheduleCert
import MoltPetit.Model.KeyStealingLockstepCert
import MoltPetit.Model.ExposureCert
import MoltPetit.Model.Liveness
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

theorem anchors_dense_be_complete : ∀ (all rest : Chain) (lo t n q : U64),
    (∀ b ∈ toModelChain rest, b.slot < 2 ^ 62) →
    (∀ b ∈ toModelChain all, b.slot < 2 ^ 62) →
    (∀ u, MoltPetit.Model.windowCount (toModelChain all) u n.val < 2 ^ 64) →
    t.val < 2 ^ 62 →
    n.val < 2 ^ 62 →
    quorum n = ok q →
    (∀ u, lo.val ≤ u → u + n.val ≤ t.val + 1 →
      MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (toModelChain all) u n.val) →
    anchors_dense_be UB () (toChainG all) (toChainG rest) lo t n q = ok true := by
  intro all rest
  induction rest with
  | Nil =>
    intro lo t n q _ _ _ _ _ _ _
    simp only [toChainG_nil, anchors_dense_be, UB,
      U64Backend.Insts.Molt_petitBackendU64Bool.bool_const]
  | Cons b tl ih =>
    intro lo t n q hrest_bound hall_bound hwc ht hn hq hdense
    have hb_bound : b.slot.val < 2 ^ 62 := by
      have : toModelBlock b ∈ toModelChain (Chain.Cons b tl) := by simp [toModelChain]
      exact hrest_bound (toModelBlock b) this
    have htl_bound : ∀ x ∈ toModelChain tl, x.slot < 2 ^ 62 := by
      intro x hx
      have : x ∈ toModelChain (Chain.Cons b tl) := by simp [toModelChain, hx]
      exact hrest_bound x this
    have h1_val : (1#u64 : U64).val = 1 := rfl
    obtain ⟨u, hu, hu_val⟩ := u64_add_ok (x := b.slot) (y := 1#u64) (by rw [h1_val]; omega)
    obtain ⟨upn, hupn, hupn_val⟩ := u64_add_ok (x := u) (y := n) (by rw [hu_val]; omega)
    obtain ⟨t11, ht11, ht11_val⟩ := u64_add_ok (x := t) (y := 1#u64) (by rw [h1_val]; omega)
    have hu_n_bound : u.val + n.val < 2 ^ 64 := by rw [hu_val]; omega
    obtain ⟨d, hdense_be, hd_iff⟩ := window_dense_be_ok hu_n_bound (hwc u.val) hq
    set cond : Bool := (!decide (u < lo)) && (!decide (t11 < upn))
    have hok1 : (!cond || d) = true := by
      cases hc : cond
      · rfl
      · dsimp [cond] at hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc
        obtain ⟨hlo_le_u, hupn_le_t11⟩ := hc
        have h1_le : lo.val ≤ u.val := by scalar_tac
        have h2_le : u.val + n.val ≤ t.val + 1 := by
          have : upn.val ≤ t11.val := by scalar_tac
          rw [hupn_val, ht11_val] at this
          exact this
        have hdense_u := hdense u.val h1_le h2_le
        have hd_true : d = true := hd_iff.mpr hdense_u
        subst hd_true
        rfl
    have hrest_ok := ih lo t n q htl_bound hall_bound hwc ht hn hq hdense
    rw [toChainG_cons, anchors_dense_be]
    simp only [toBlockG_slot, UB,
      U64Backend.Insts.Molt_petitBackendU64Bool.one,
      U64Backend.Insts.Molt_petitBackendU64Bool.add,
      U64Backend.Insts.Molt_petitBackendU64Bool.lt,
      u64_backend_not,
      u64_backend_and,
      u64_backend_or,
      bind_tc_ok, hu, hupn, ht11, hdense_be, hrest_ok]
    change ok ((!cond || d) && true) = ok true
    rw [hok1]
    rfl


theorem matured_dense_be_complete {c : Chain} {lo t n q : U64}
    (hbound : ∀ b ∈ toModelChain c, b.slot < 2 ^ 62)
    (hwc : ∀ u, MoltPetit.Model.windowCount (toModelChain c) u n.val < 2 ^ 64)
    (hlo : lo.val < 2 ^ 62)
    (ht : t.val < 2 ^ 62)
    (hn : n.val < 2 ^ 62)
    (hq : quorum n = ok q)
    (hdense : ∀ u, lo.val ≤ u → u + n.val ≤ t.val + 1 →
      MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (toModelChain c) u n.val) :
    matured_dense_be UB () (toChainG c) lo t n q = ok true := by
  have h1_val : (1#u64 : U64).val = 1 := rfl
  obtain ⟨lpn, hlpn, hlpn_val⟩ := u64_add_ok (x := lo) (y := n) (by omega)
  obtain ⟨t11, ht11, ht11_val⟩ := u64_add_ok (x := t) (y := 1#u64) (by rw [h1_val]; omega)
  obtain ⟨d_lo, hd_lo_be, hd_lo_iff⟩ := window_dense_be_ok (u := lo) (c := c) (by omega) (hwc lo.val) hq
  have hbase : (!(!decide (t11 < lpn)) || d_lo) = true := by
    cases hlt : decide (t11 < lpn)
    · simp only [Bool.not_false, Bool.true_or, decide_eq_false_iff_not] at hlt ⊢
      have hle : lpn.val ≤ t11.val := by scalar_tac
      rw [hlpn_val, ht11_val] at hle
      have hd := hdense lo.val (by omega) hle
      have hd_true : d_lo = true := hd_lo_iff.mpr hd
      rw [hd_true]
      rfl
    · rfl
  have hanch := anchors_dense_be_complete c c lo t n q hbound hbound hwc ht hn hq hdense
  simp only [matured_dense_be, UB,
    U64Backend.Insts.Molt_petitBackendU64Bool.one,
    U64Backend.Insts.Molt_petitBackendU64Bool.add,
    U64Backend.Insts.Molt_petitBackendU64Bool.lt,
    u64_backend_not,
    u64_backend_or,
    u64_backend_and,
    bind_tc_ok, hlpn, ht11, hd_lo_be, hanch]
  rw [hbase]
  rfl

theorem linksOk_of_isChain :
    ∀ {ch : MoltPetit.Model.Chain}, List.IsChain (fun a b => MoltPetit.Model.childOk a b = true) ch →
      MoltPetit.Model.linksOk ch = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    rw [List.isChain_cons_cons] at h
    rw [MoltPetit.Model.linksOk, Bool.and_eq_true]
    exact ⟨h.1, linksOk_of_isChain h.2⟩

theorem linksOk_of_validChain {ch : MoltPetit.Model.Chain}
    (hSeq : MoltPetit.Model.SequentialHeights ch)
    (hSlots : MoltPetit.Model.StrictSlots ch)
    (hParent : MoltPetit.Model.ParentLinked ch) :
    MoltPetit.Model.linksOk ch = true := by
  apply linksOk_of_isChain
  rw [List.isChain_iff_getElem]
  intro i hi
  have hi_len : i < ch.length := by omega
  have hi1_len : i + 1 < ch.length := hi
  set P := ch[i]
  set B := ch[i + 1]
  have hP_at : MoltPetit.Model.blockAt? ch i = some P := by
    unfold MoltPetit.Model.blockAt?
    rw [List.getElem?_eq_getElem hi_len]
  have hB_at : MoltPetit.Model.blockAt? ch (i + 1) = some B := by
    unfold MoltPetit.Model.blockAt?
    rw [List.getElem?_eq_getElem hi1_len]
  have hPh : P.height = i := hSeq hP_at
  have hBh : B.height = i + 1 := hSeq hB_at
  have hH : B.height = P.height + 1 := by omega
  have hS : P.slot < B.slot := MoltPetit.Model.strictSlots_lt hSlots hP_at hB_at (by omega)
  have hPar := hParent hB_at
  rcases hPar with ⟨P', hP'_at, hPrev⟩
  have hP_eq : P' = P := by
    unfold MoltPetit.Model.blockAt? at hP_at hP'_at
    rw [hP_at] at hP'_at
    injection hP'_at with hP'_eq
    exact hP'_eq.symm
  subst hP_eq
  rw [MoltPetit.Model.childOk_iff]
  exact ⟨hH, hS, hPrev⟩

theorem windowCount_le_length (c : MoltPetit.Model.Chain) (u n : Nat) :
    MoltPetit.Model.windowCount c u n ≤ c.length := by
  dsimp [MoltPetit.Model.windowCount]
  exact List.length_filter_le _ _

theorem windowCount_bound_of_validChain {n : Nat} {c : MoltPetit.Model.Chain}
    (hbound : ∀ B ∈ c, B.height < 2 ^ 62)
    (hSeq : MoltPetit.Model.SequentialHeights c)
    (u : Nat) :
    MoltPetit.Model.windowCount c u n < 2 ^ 64 := by
  have hle := windowCount_le_length c u n
  cases hc : c with
  | nil =>
    dsimp [MoltPetit.Model.windowCount]
    omega
  | cons g tl =>
    obtain ⟨tip, hTip⟩ : ∃ tip, (g :: tl).getLast? = some tip := by
      cases hL : (g :: tl).getLast? with
      | some t => exact ⟨t, rfl⟩
      | none => simp at hL
    have hAt := MoltPetit.Model.blockAt_getLast hTip
    subst hc
    have hH := hSeq hAt
    have hMem : tip ∈ g :: tl := List.mem_of_getLast? hTip
    have hb := hbound tip hMem
    omega

theorem valid_chain_be_complete : MoltPaper.thm_valid_chain_be_complete := by
  intro n q c hn hsmall hq hbound h
  cases c with
  | Nil =>
    simp only [toChainG_nil, valid_chain_be,
      U64Backend.Insts.Molt_petitBackendU64Bool.bool_const]
  | Cons g tl =>
    have hSeq := h.1
    have hSlots := h.2.1
    have hParent := h.2.2.1
    have hDense := h.2.2.2
    have hbound_slot : ∀ b ∈ toModelChain (Chain.Cons g tl), b.slot < 2 ^ 62 := by
      intro b hb; exact (hbound b hb).1
    have hbound_height : ∀ b ∈ toModelChain (Chain.Cons g tl), b.height < 2 ^ 62 := by
      intro b hb; exact (hbound b hb).2
    have hwc : ∀ u, MoltPetit.Model.windowCount (toModelChain (Chain.Cons g tl)) u n.val < 2 ^ 64 := by
      intro u
      exact windowCount_bound_of_validChain hbound_height hSeq u
    have h0_at : MoltPetit.Model.blockAt? (toModelChain (Chain.Cons g tl)) 0 = some (toModelBlock g) := by
      simp [toModelChain, MoltPetit.Model.blockAt?]
    have hg_height : (toModelBlock g).height = 0 := hSeq h0_at
    have hg_prev : (toModelBlock g).prev = none := by
      have := hParent h0_at
      exact this
    have hg_ok : MoltPetit.Model.genesisOk (toModelBlock g) = true := by
      simp [MoltPetit.Model.genesisOk, hg_height, hg_prev]
    have hgenesis_be := genesis_ok_be_complete hg_ok
    have hlinks_ok : MoltPetit.Model.linksOk (toModelChain (Chain.Cons g tl)) = true :=
      linksOk_of_validChain hSeq hSlots hParent
    have hlinks_be := links_ok_be_complete hbound_height hlinks_ok
    obtain ⟨tip, htip_be, htip_val⟩ := tip_slot_from_be_complete tl g.slot
    obtain ⟨tip_block, htip_block⟩ : ∃ tip_block, (toModelChain (Chain.Cons g tl)).getLast? = some tip_block := by
      cases hL : (toModelChain (Chain.Cons g tl)).getLast? with
      | some t => exact ⟨t, rfl⟩
      | none => simp [toModelChain] at hL
    have htip_eq : tip.val = tip_block.slot := by
      simp only [toModelChain_cons] at htip_block
      cases htl : toModelChain tl with
      | nil =>
        simp only [htl, List.getLast?_singleton, Option.some.injEq] at htip_block
        subst htip_block
        have htl_nil : tl = Chain.Nil := by
          cases tl
          · rfl
          · rename_i b' tl'; exfalso; simp [toModelChain] at htl
        subst htl_nil
        simp only [toModelChain_nil] at htip_val
        rw [htip_val]
        rfl
      | cons b' rest =>
        rw [htl] at htip_block
        rw [List.getLast?_cons_cons] at htip_block
        rw [htl] at htip_val
        rw [htip_block] at htip_val
        exact htip_val
    have htip_bound : tip.val < 2 ^ 62 := by
      rw [htip_eq]
      have hmem : tip_block ∈ toModelChain (Chain.Cons g tl) := List.mem_of_getLast? htip_block
      exact (hbound tip_block hmem).1
    have h0_bound : (0#u64 : U64).val < 2 ^ 62 := by
      have : (0#u64 : U64).val = 0 := rfl
      rw [this]; omega
    have hhdense : ∀ u, (0#u64 : U64).val ≤ u → u + n.val ≤ tip.val + 1 →
        MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (toModelChain (Chain.Cons g tl)) u n.val := by
      intro u _ hu
      have hAtTip := MoltPetit.Model.blockAt_getLast htip_block
      rw [htip_eq] at hu
      exact hDense hAtTip u hu
    have hdense_be := matured_dense_be_complete
      (c := Chain.Cons g tl) (lo := 0#u64) (t := tip) (n := n) (q := q)
      hbound_slot hwc h0_bound htip_bound hsmall hq hhdense
    have hlinks_be' : links_ok_be UB () (ChainG.ConsG (toBlockG g) (toChainG tl)) = ok true := by
      have : toChainG (Chain.Cons g tl) = ChainG.ConsG (toBlockG g) (toChainG tl) := rfl
      rw [← this]
      exact hlinks_be
    have hdense_be' : matured_dense_be UB () (ChainG.ConsG (toBlockG g) (toChainG tl)) 0#u64 tip n q = ok true := by
      have : toChainG (Chain.Cons g tl) = ChainG.ConsG (toBlockG g) (toChainG tl) := rfl
      rw [← this]
      exact hdense_be
    rw [toChainG_cons, valid_chain_be]
    simp only [toBlockG_slot, UB,
      U64Backend.Insts.Molt_petitBackendU64Bool.zero,
      u64_backend_and,
      bind_tc_ok, hgenesis_be, hlinks_be', htip_be, hdense_be']
    rfl


theorem presentSlots_filter_cons (f s : U64) (tl : TailG U64) (p : Nat → Prop) [DecidablePred p] :
    ((presentSlots (.TCons f s tl)).filter p) =
      (if f.val = 1 ∧ p s.val then [s.val] else []) ++ (presentSlots tl).filter p := by
  dsimp [presentSlots]
  by_cases h1 : f.val = 1
  · simp only [h1, if_true, List.filter_cons]
    by_cases hp : p s.val
    · simp [h1, hp]
    · simp [h1, hp]
  · simp only [h1, if_false]
    have : ¬(f.val = 1 ∧ p s.val) := fun h => h1 h.1
    simp [this]

theorem presentSlots_filter_length_cons (f s : U64) (tl : TailG U64) (p : Nat → Prop) [DecidablePred p] :
    ((presentSlots (.TCons f s tl)).filter p).length =
      (if f.val = 1 ∧ p s.val then 1 else 0) + ((presentSlots tl).filter p).length := by
  rw [presentSlots_filter_cons]
  simp only [List.length_append]
  split_ifs <;> rfl

theorem tail_count_be_complete : ∀ (t : TailG U64) (u len : U64),
    u.val + len.val < 2 ^ 64 →
    ((presentSlots t).filter (fun s => u.val ≤ s ∧ s < u.val + len.val)).length < 2 ^ 64 →
    ∃ w : U64, tail_count_be UB () t u len = ok w ∧
      w.val = ((presentSlots t).filter (fun s => u.val ≤ s ∧ s < u.val + len.val)).length := by
  intro t
  induction t with
  | TNil =>
    intro u len _ _
    simp only [tail_count_be, UB, U64Backend.Insts.Molt_petitBackendU64Bool.zero]
    refine ⟨0#u64, rfl, ?_⟩
    simp [presentSlots]
  | TCons f s tl ih =>
    intro u len hun hlen
    rw [presentSlots_filter_length_cons] at hlen
    have hlen_tl : ((presentSlots tl).filter (fun s' => u.val ≤ s' ∧ s' < u.val + len.val)).length < 2 ^ 64 := by omega
    obtain ⟨rest, hrest, hrest_val⟩ := ih u len hun hlen_tl
    obtain ⟨hi, hhi, hhi_val⟩ := u64_add_ok hun
    set inw : Bool := (!decide (s < u)) && decide (s < hi)
    have hinw_eq : inw = decide (u.val ≤ s.val ∧ s.val < u.val + len.val) := by
      dsimp [inw]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : u.val ≤ s.val := by scalar_tac
        have h2' : s.val < hi.val := by scalar_tac
        have : s.val < u.val + len.val := by omega
        exact ⟨h1', this⟩
      · rintro ⟨h1, h2⟩
        have h2' : s.val < hi.val := by omega
        refine ⟨by scalar_tac, by scalar_tac⟩
    have hhere_cond : ((decide (f = 1#u64) && inw) = true) ↔ (f.val = 1 ∧ (u.val ≤ s.val ∧ s.val < u.val + len.val)) := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, hinw_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩
        subst h1
        exact ⟨rfl, h2⟩
      · rintro ⟨h1, h2⟩
        have : f = 1#u64 := UScalar.val_eq_imp _ _ (by rw [h1]; rfl)
        exact ⟨this, h2⟩
    set here : U64 := if decide (f = 1#u64) && inw then 1#u64 else 0#u64
    have hhere_val : here.val = if f.val = 1 ∧ (u.val ≤ s.val ∧ s.val < u.val + len.val) then 1 else 0 := by
      dsimp [here]
      by_cases hc : (decide (f = 1#u64) && inw) = true
      · have hc' := hhere_cond.mp hc
        simp [hc, hc']
      · have hc' := mt hhere_cond.mpr hc
        simp [hc, hc']
    have hsum : here.val + rest.val < 2 ^ 64 := by
      rw [hhere_val, hrest_val]
      exact hlen
    obtain ⟨w, hw, hw_val⟩ := u64_add_ok hsum
    refine ⟨w, ?_, ?_⟩
    · simp only [tail_count_be, UB,
        U64Backend.Insts.Molt_petitBackendU64Bool.lt,
        u64_backend_not,
        U64Backend.Insts.Molt_petitBackendU64Bool.add,
        u64_backend_and,
        U64Backend.Insts.Molt_petitBackendU64Bool.one,
        U64Backend.Insts.Molt_petitBackendU64Bool.eq,
        u64_backend_bool_to_num,
        bind_tc_ok, hhi, hrest]
      change here + rest = ok w
      exact hw
    · rw [hw_val, hhere_val, hrest_val, presentSlots_filter_length_cons]
theorem fold_window_ok_be_complete {tail : TailG U64} {tip_slot slot u n q : U64}
    (hun : u.val + n.val < 2 ^ 64)
    (hts : tip_slot.val + 2 < 2 ^ 64)
    (hs : slot.val + 1 < 2 ^ 64)
    (hlen : ((presentSlots tail).filter (fun s => u.val ≤ s ∧ s < u.val + n.val)).length + 1 < 2 ^ 64)
    (hdense : tip_slot.val + 2 ≤ u.val + n.val → u.val + n.val ≤ slot.val + 1 →
      q.val ≤ ((presentSlots tail).filter (fun s => u.val ≤ s ∧ s < u.val + n.val)).length +
        (if u.val ≤ slot.val ∧ slot.val < u.val + n.val then 1 else 0)) :
    fold_window_ok_be UB () tail tip_slot slot u n q = ok true := by
  obtain ⟨un, hun_eq, hun_val⟩ := u64_add_ok hun
  have h1 : (1#u64 : U64).val = 1 := rfl
  have ht1_ok : (1#u64 : U64).val + (1#u64 : U64).val < 2 ^ 64 := by decide
  obtain ⟨t1, ht1_eq, ht1_val⟩ := u64_add_ok ht1_ok
  have hts2_ok : tip_slot.val + t1.val < 2 ^ 64 := by rw [ht1_val]; exact hts
  obtain ⟨ts2, hts2_eq, hts2_val⟩ := u64_add_ok hts2_ok
  have hs1_ok : slot.val + (1#u64 : U64).val < 2 ^ 64 := by rw [h1]; exact hs
  obtain ⟨s1, hs1_eq, hs1_val⟩ := u64_add_ok hs1_ok
  have hlen_tl : ((presentSlots tail).filter (fun s => u.val ≤ s ∧ s < u.val + n.val)).length < 2 ^ 64 := by omega
  obtain ⟨in_tail, hin_tail_eq, hin_tail_val⟩ := tail_count_be_complete tail u n hun hlen_tl
  set bin : Bool := (!decide (slot < u)) && decide (slot < un)
  have hbin_eq : bin = decide (u.val ≤ slot.val ∧ slot.val < u.val + n.val) := by
    dsimp [bin]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    constructor
    · rintro ⟨h1', h2'⟩
      have h1'' : u.val ≤ slot.val := by scalar_tac
      have h2'' : slot.val < un.val := by scalar_tac
      rw [hun_val] at h2''
      exact ⟨h1'', h2''⟩
    · rintro ⟨h1', h2'⟩
      have h2'' : slot.val < un.val := by rw [hun_val]; exact h2'
      refine ⟨by scalar_tac, by scalar_tac⟩
  set t2 : U64 := if bin then 1#u64 else 0#u64
  have ht2_val : t2.val = if u.val ≤ slot.val ∧ slot.val < u.val + n.val then 1 else 0 := by
    dsimp [t2]
    by_cases hc : bin = true
    · rw [hc]
      have hc' : u.val ≤ slot.val ∧ slot.val < u.val + n.val := by
        rw [hbin_eq] at hc; exact of_decide_eq_true hc
      simp [hc']
    · have hcf : bin = false := by revert hc; cases bin <;> decide
      rw [hcf]
      have hc' : ¬(u.val ≤ slot.val ∧ slot.val < u.val + n.val) := by
        rw [hbin_eq] at hcf; exact of_decide_eq_false hcf
      simp [hc']
  have ht2_le1 : t2.val ≤ 1 := by
    rw [ht2_val]
    split_ifs <;> omega
  have hcnt_ok : in_tail.val + t2.val < 2 ^ 64 := by
    rw [hin_tail_val]
    omega
  obtain ⟨cnt, hcnt_eq, hcnt_val⟩ := u64_add_ok hcnt_ok
  set checked : Bool := (!decide (un < ts2)) && (!decide (s1 < un))
  have hcheck_result : (!checked || !decide (cnt < q)) = true := by
    by_cases hck : checked = true
    · dsimp [checked] at hck
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hck
      obtain ⟨hlo, hhi⟩ := hck
      have hlo' : ts2.val ≤ un.val := by scalar_tac
      have hhi' : un.val ≤ s1.val := by scalar_tac
      rw [hun_val, hts2_val, ht1_val] at hlo'
      rw [hun_val, hs1_val, h1] at hhi'
      have hqle := hdense hlo' hhi'
      rw [← hin_tail_val, ← ht2_val] at hqle
      have hcnt_ge : q.val ≤ cnt.val := by rw [hcnt_val]; exact hqle
      have hnot_short : decide (cnt < q) = false := by
        apply decide_eq_false
        intro hc
        have : cnt.val < q.val := by scalar_tac
        omega
      rw [hnot_short]
      simp
    · cases hc : checked
      · rfl
      · contradiction
  simp only [fold_window_ok_be, UB,
    U64Backend.Insts.Molt_petitBackendU64Bool.add,
    U64Backend.Insts.Molt_petitBackendU64Bool.one,
    U64Backend.Insts.Molt_petitBackendU64Bool.lt,
    u64_backend_not,
    u64_backend_and,
    u64_backend_bool_to_num,
    u64_backend_or,
    bind_tc_ok,
    hun_eq, ht1_eq, hts2_eq, hs1_eq, hin_tail_eq]
  change (in_tail + t2 >>= fun cnt => ok (!checked || !decide (cnt < q))) = ok true
  rw [hcnt_eq]
  exact congrArg ok hcheck_result

theorem fold_anchors_ok_be_complete {all rest : TailG U64} {tip_slot slot n q : U64}
    (hrest_bound : ∀ s ∈ entrySlots rest, s < 2 ^ 62)
    (hts : tip_slot.val + 2 < 2 ^ 64)
    (hs : slot.val + 1 < 2 ^ 64)
    (hn : n.val < 2 ^ 62)
    (hlen : ∀ u, ((presentSlots all).filter (fun s => u ≤ s ∧ s < u + n.val)).length + 1 < 2 ^ 64)
    (hdense : ∀ s ∈ entrySlots rest,
      tip_slot.val + 2 ≤ (s + 1) + n.val →
      (s + 1) + n.val ≤ slot.val + 1 →
      q.val ≤ ((presentSlots all).filter (fun x => s + 1 ≤ x ∧ x < (s + 1) + n.val)).length +
        (if s + 1 ≤ slot.val ∧ slot.val < (s + 1) + n.val then 1 else 0)) :
    fold_anchors_ok_be UB () all rest tip_slot slot n q = ok true := by
  induction rest with
  | TNil =>
    simp only [fold_anchors_ok_be, UB, U64Backend.Insts.Molt_petitBackendU64Bool.bool_const]
  | TCons f s tl ih =>
    have hs_bound : s.val < 2 ^ 62 := hrest_bound s.val (by simp [entrySlots])
    have htl_bound : ∀ s' ∈ entrySlots tl, s' < 2 ^ 62 := by
      intro s' hs'
      exact hrest_bound s' (by simp [entrySlots, hs'])
    have h1_ok : s.val + (1#u64 : U64).val < 2 ^ 64 := by
      have : (1#u64 : U64).val = 1 := rfl
      omega
    obtain ⟨u, hu_eq, hu_val⟩ := u64_add_ok h1_ok
    have hu_val' : u.val = s.val + 1 := by
      have : (1#u64 : U64).val = 1 := rfl
      rw [hu_val, this]
    have hun : u.val + n.val < 2 ^ 64 := by omega
    have hhere := fold_window_ok_be_complete (tail := all) (q := q) hun hts hs (hlen u.val) ?_
    · have hmore := ih htl_bound ?_
      · simp only [fold_anchors_ok_be, UB,
          U64Backend.Insts.Molt_petitBackendU64Bool.one,
          U64Backend.Insts.Molt_petitBackendU64Bool.add,
          u64_backend_and,
          bind_tc_ok, hu_eq, hhere, hmore]
        rfl
      · intro s' hs'
        exact hdense s' (by simp [entrySlots, hs'])
    · intro hlo hhi
      rw [hu_val'] at hlo hhi
      have hd := hdense s.val (by simp [entrySlots]) hlo hhi
      rw [hu_val']
      exact hd


theorem cert_step_core_be_complete {n q : U64} {st : CertStateG U64} {b : Block}
    {cl : MoltPetit.Model.CertClaim}
    (hn : 1 ≤ n.val) (hn_bound : n.val < 2 ^ 62)
    (hq : quorum n = ok q)
    (hrep : TailRepr n.val st cl)
    (htip_h : st.tip_height.val < 2 ^ 62)
    (htip_s : st.tip_slot.val < 2 ^ 62)
    (hb_h : b.height.val < 2 ^ 62)
    (hb_s : b.slot.val < 2 ^ 62)
    (hrest_bound : ∀ s ∈ entrySlots st.tail, s < 2 ^ 62)
    (hchild_h : (toModelBlock b).height = cl.tipHeight + 1)
    (hchild_s : cl.tipSlot < (toModelBlock b).slot)
    (hchild_prev : (toModelBlock b).prev = some cl.tipId)
    (hdense : ∀ u : Nat, cl.tipSlot + 2 ≤ u + n.val → u + n.val ≤ (toModelBlock b).slot + 1 →
      q.val ≤ MoltPetit.Model.windowCount (cl.tail ++ [toModelBlock b]) u n.val) :
    cert_step_core_be UBK () n q st (toBlockG b) = ok true := by
  have hsucc_ok : st.tip_height.val + (1#u64 : U64).val < 2 ^ 64 := by
    have : (1#u64 : U64).val = 1 := rfl
    omega
  obtain ⟨succ, hsucc_eq, hsucc_val⟩ := u64_add_ok hsucc_ok
  have hh_eq : b.height = succ := by
    apply UScalar.val_eq_imp
    rw [hsucc_val]
    have : (1#u64 : U64).val = 1 := rfl
    rw [this]
    dsimp [toModelBlock] at hchild_h
    rw [hchild_h, hrep.tip_height]
  have hh_ok : decide (b.height = succ) = true := decide_eq_true hh_eq
  have hslot_lt : decide (st.tip_slot < b.slot) = true := by
    apply decide_eq_true
    dsimp [toModelBlock] at hchild_s
    have : st.tip_slot.val < b.slot.val := by
      rw [hrep.tip_slot]
      exact hchild_s
    scalar_tac
  obtain ⟨p, hp⟩ : ∃ p, b.prev = some p := by
    cases hp : b.prev with
    | none =>
      dsimp [toModelBlock] at hchild_prev
      rw [hp] at hchild_prev
      contradiction
    | some p => exact ⟨p, rfl⟩
  dsimp [toModelBlock] at hchild_prev
  rw [hp] at hchild_prev
  injection hchild_prev with hp_eq
  obtain ⟨h_tip, hst_id, hhash_id⟩ := hrep.tip_id
  have hp_hash : p = h_tip := by
    apply hashToNat_inj
    rw [hp_eq, hhash_id]
  have hprev_g : (toBlockG b).prev = toHashG h_tip := by
    dsimp [toBlockG]
    rw [hp, hp_hash]
  have hhas_prev : (toBlockG b).has_prev = true := by
    dsimp [toBlockG]; rw [hp]; rfl
  have ht2_ok : (1#u64 : U64).val + (1#u64 : U64).val < 2 ^ 64 := by decide
  obtain ⟨t2, ht2_eq, ht2_val⟩ := u64_add_ok ht2_ok
  have hts2_ok : st.tip_slot.val + t2.val < 2 ^ 64 := by
    have : t2.val = 2 := by rw [ht2_val]; rfl
    omega
  obtain ⟨ts2, hts2_eq, hts2_val⟩ := u64_add_ok hts2_ok
  obtain ⟨lo, hlo_eq, hlo_val⟩ := ubk_monus ts2 n
  have hts2_val' : ts2.val = cl.tipSlot + 2 := by
    have : t2.val = 2 := by rw [ht2_val]; rfl
    rw [hts2_val, this, hrep.tip_slot]
  have hlo_val' : lo.val = cl.tipSlot + 2 - n.val := by
    rw [hlo_val, hts2_val']
  have hlo_n : lo.val + n.val < 2 ^ 64 := by
    rw [hlo_val']
    omega
  have hts : st.tip_slot.val + 2 < 2 ^ 64 := by omega
  have hbs : (toBlockG b).slot.val + 1 < 2 ^ 64 := by
    dsimp [toBlockG]; omega
  have hlen : ∀ u, ((presentSlots st.tail).filter (fun s => u ≤ s ∧ s < u + n.val)).length + 1 < 2 ^ 64 := by
    intro u
    have hfl : ((presentSlots st.tail).filter (fun s => u ≤ s ∧ s < u + n.val)).length ≤ (entrySlots st.tail).length := by
      have h1 := List.length_filter_le (fun s => u ≤ s ∧ s < u + n.val) (presentSlots st.tail)
      have h2 : (presentSlots st.tail).length ≤ (entrySlots st.tail).length := by
        induction st.tail with
        | TNil => rfl
        | TCons f s tl ih =>
          dsimp [presentSlots, entrySlots]
          split <;> (try simp [ih]) <;> omega
      omega
    rw [hrep.tail_len] at hfl
    omega
  have hbase := fold_window_ok_be_complete (tail := st.tail) (q := q) hlo_n hts hbs (hlen lo.val) ?_
  · have hanchors := fold_anchors_ok_be_complete (all := st.tail) (rest := st.tail) (tip_slot := st.tip_slot)
      (slot := (toBlockG b).slot) (n := n) (q := q) hrest_bound hts hbs hn_bound hlen ?_
    · dsimp [cert_step_core_be, UBK, UB, U64Backend.Insts.Molt_petitBackendU64Bool.one, U64Backend.Insts.Molt_petitBackendU64Bool.add]
      simp only [bind_tc_ok]
      rw [hsucc_eq]
      simp only [bind_tc_ok]
      dsimp [UBK, UB, U64Backend.Insts.Molt_petitBackendU64Bool.eq]
      rw [hh_ok]
      simp only [bind_tc_ok]
      dsimp [UBK, UB, U64Backend.Insts.Molt_petitBackendU64Bool.lt]
      rw [hslot_lt]
      simp only [bind_tc_ok]
      rw [hprev_g, hst_id]
      rw [hashg_eq_eq, hash_eq_self]
      simp only [bind_tc_ok]
      dsimp [UBK, UB, U64Backend.Insts.Molt_petitBackendU64Bool.bool_const]
      rw [hhas_prev]
      simp only [bind_tc_ok]
      dsimp [UBK, UB, U64Backend.Insts.Molt_petitBackendU64Bool.and]
      rw [ht2_eq]
      simp only [bind_tc_ok]
      rw [hts2_eq]
      simp only [bind_tc_ok]
      change U64Backend.Insts.Molt_petitBackendKU64Bool.monus () ts2 n = ok lo at hlo_eq
      rw [hlo_eq]
      simp only [bind_tc_ok]
      change fold_window_ok_be UB () st.tail st.tip_slot b.slot lo n q = ok true at hbase
      change fold_anchors_ok_be UB () st.tail st.tail st.tip_slot b.slot n q = ok true at hanchors
      rw [hbase, hanchors]
      rfl
    · intro s hs htip_le hu_le
      have h1 : cl.tipSlot + 2 ≤ (s + 1) + n.val := by
        have : st.tip_slot.val = cl.tipSlot := hrep.tip_slot
        omega
      have h2 : (s + 1) + n.val ≤ (toModelBlock b).slot + 1 := by
        dsimp [toModelBlock, toBlockG]; exact hu_le
      have hqle := hdense (s + 1) h1 h2
      have hext := windowCount_extend_eq hrep b (u := s + 1) (by omega) n.val
      rw [hext] at hqle
      dsimp [toBlockG]
      exact hqle
  · intro htip_le hu_le
    have h1 : cl.tipSlot + 2 ≤ lo.val + n.val := by
      rw [hlo_val']; omega
    have h2 : lo.val + n.val ≤ (toModelBlock b).slot + 1 := by
      dsimp [toModelBlock, toBlockG]; exact hu_le
    have hqle := hdense lo.val h1 h2
    have hext := windowCount_extend_eq hrep b (u := lo.val) (by rw [hlo_val']) n.val
    rw [hext] at hqle
    dsimp [toBlockG]
    exact hqle

theorem cert_step_sched_be_complete {n q era : U64} {st : CertStateG U64} {b : Block}
    (hera : 0 < era.val)
    (hcore : cert_step_core_be UBK () n q st (toBlockG b) = ok true)
    (hpin : b.slot.val / era.val ≤ b.key_index.val) :
    cert_step_sched_be UBK () n q era st (toBlockG b) b.key_index = ok true := by
  obtain ⟨gen, hgen, hgen_val⟩ := ubk_div b.slot era (by omega)
  have hlt : decide (b.key_index < gen) = false := by
    apply decide_eq_false
    intro hc
    have : b.key_index.val < gen.val := by scalar_tac
    omega
  dsimp [cert_step_sched_be]
  rw [hcore]
  simp only [bind_tc_ok]
  change U64Backend.Insts.Molt_petitBackendKU64Bool.div () b.slot era = ok gen at hgen
  rw [hgen]
  simp only [bind_tc_ok]
  dsimp [UBK, UB, U64Backend.Insts.Molt_petitBackendU64Bool.lt]
  rw [hlt]
  dsimp [UBK, UB, U64Backend.Insts.Molt_petitBackendU64Bool.not, U64Backend.Insts.Molt_petitBackendU64Bool.and]
  rfl

theorem cert_step_lock_be_complete {n q : U64} {st : CertStateG U64} {g : U64} {b : Block}
    (hn : 1 ≤ n.val)
    (hcore : cert_step_core_be UBK () n q st (toBlockG b) = ok true)
    (hle : g.val ≤ b.key_index.val)
    (hmix : st.tip_slot.val / n.val = b.slot.val / n.val → g.val = b.key_index.val) :
    cert_step_lock_be UBK () n q st g (toBlockG b) b.key_index = ok true := by
  obtain ⟨w_tip, hw_tip, hw_tip_val⟩ := ubk_div st.tip_slot n (by omega)
  obtain ⟨w_b, hw_b, hw_b_val⟩ := ubk_div b.slot n (by omega)
  have hlt : decide (b.key_index < g) = false := by
    apply decide_eq_false
    intro hc
    have : b.key_index.val < g.val := by scalar_tac
    omega
  dsimp [cert_step_lock_be]
  rw [hcore]
  simp only [bind_tc_ok]
  dsimp [UBK, UB, U64Backend.Insts.Molt_petitBackendU64Bool.lt]
  rw [hlt]
  dsimp [UBK, UB, U64Backend.Insts.Molt_petitBackendU64Bool.not]
  change U64Backend.Insts.Molt_petitBackendKU64Bool.div () st.tip_slot n = ok w_tip at hw_tip
  change U64Backend.Insts.Molt_petitBackendKU64Bool.div () b.slot n = ok w_b at hw_b
  rw [hw_tip, hw_b]
  simp only [bind_tc_ok]
  dsimp [UBK, UB, U64Backend.Insts.Molt_petitBackendU64Bool.eq,
    U64Backend.Insts.Molt_petitBackendU64Bool.not,
    U64Backend.Insts.Molt_petitBackendU64Bool.or,
    U64Backend.Insts.Molt_petitBackendU64Bool.and]
  by_cases hsame : w_tip = w_b
  · have hsame_dec : decide (w_tip = w_b) = true := decide_eq_true hsame
    have hw_eq : st.tip_slot.val / n.val = b.slot.val / n.val := by
      rw [← hw_tip_val, ← hw_b_val, hsame]
    have hg_eq := hmix hw_eq
    have hg_u64 : g = b.key_index := UScalar.eq_of_val_eq hg_eq
    have hkeeps_dec : decide (g = b.key_index) = true := decide_eq_true hg_u64
    rw [hsame_dec, hkeeps_dec]
    rfl
  · have hsame_dec : decide (w_tip = w_b) = false := decide_eq_false hsame
    rw [hsame_dec]
    rfl

lemma getLast_map {α β : Type} (f : α → β) (x : α) (xs : List α) :
    ((x :: xs).map f).getLast (List.cons_ne_nil _ _) = f ((x :: xs).getLast (List.cons_ne_nil _ _)) := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    exact ih y

lemma lockstep_append_mem {n : Nat} {A : MoltPetit.Model.Chain} {b : MoltPetit.Model.Block} {B : MoltPetit.Model.Chain}
    (hL : MoltPetit.Model.lockstepOk n (A ++ b :: B) = true) {x : MoltPetit.Model.Block} (hx : x ∈ A) :
    (x.slot / n = b.slot / n → x.keyIndex = b.keyIndex) ∧ x.keyIndex ≤ b.keyIndex := by
  have hpw := (MoltPetit.Model.lockstepOk_iff_pairwise (A ++ b :: B)).mp hL
  have hcross := (List.pairwise_append.mp hpw).2.2
  exact hcross x hx b (List.mem_cons_self ..)

lemma getLast_cons_append_singleton (G : Block) (pre : List Block) (b : Block) :
    (G :: (pre ++ [b])).getLast (List.cons_ne_nil _ _) = b := by
  induction pre generalizing G with
  | nil => rfl
  | cons p ps ih =>
    exact ih p


lemma entrySlots_initTail_bound {n : Nat} {slot : U64} (hslot : slot.val < 2 ^ 62) :
    ∀ s ∈ entrySlots (initTail n slot), s < 2 ^ 62 := by
  intro s hs
  by_cases hn : n < 2
  · unfold initTail at hs
    simp [hn] at hs
  · unfold initTail at hs
    simp [hn] at hs
    rw [entrySlots_padTail] at hs
    simp only [entrySlots_cons, entrySlots_nil, List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with ⟨_, rfl⟩ | rfl
    · omega
    · exact hslot

lemma entrySlots_cert_next_tail_bound {st : CertStateG U64} {b : Block} {t' : TailG U64}
    (hbound : ∀ s ∈ entrySlots st.tail, s < 2 ^ 62)
    (hb : b.slot.val < 2 ^ 62)
    (ht' : cert_next_tail_be UB () st.tail b.slot = ok t') :
    ∀ s ∈ entrySlots (stepState b t').tail, s < 2 ^ 62 := by
  dsimp [stepState]
  cases htail : st.tail with
  | TNil =>
    have hcorr := cert_next_tail_be_corr .TNil b.slot
    rw [htail] at ht'
    rw [ht'] at hcorr
    dsimp only at hcorr
    injection hcorr with ht'_eq
    subst ht'_eq
    simp [entrySlots]
  | TCons f0 s0 tl =>
    have hcorr := cert_next_tail_be_corr (TailG.TCons f0 s0 tl) b.slot
    rw [htail] at ht'
    rw [ht'] at hcorr
    dsimp only at hcorr
    injection hcorr with ht'_eq
    subst ht'_eq
    rw [entrySlots_tailPush]
    intro s hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with htl | rfl
    · apply hbound
      rw [htail]
      simp [entrySlots, htl]
    · exact hb


lemma getElem?_append_head {α : Type} (A : List α) (b : α) (B : List α) :
    (A ++ b :: B)[A.length]? = some b := by
  induction A with
  | nil => rfl
  | cons a A' ih =>
    simp only [List.cons_append, List.length_cons]
    exact ih

lemma strictSlots_append_mem {A : MoltPetit.Model.Chain} {b : MoltPetit.Model.Block} {B : MoltPetit.Model.Chain}
    (hS : MoltPetit.Model.StrictSlots (A ++ b :: B)) {x : MoltPetit.Model.Block} (hx : x ∈ B) :
    b.slot < x.slot := by
  have hpw := (List.pairwise_append.mp hS).2.1
  have hpw' := List.pairwise_cons.mp hpw
  exact hpw'.1 x hx

lemma windowCount_claim_extend_eq {n : Nat} {G : Block} {pre : List Block} {b : Block}
    {u : Nat} (hu : (modelClaimOf n (toModelBlock G) (pre.map toModelBlock)).tipSlot + 2 ≤ u + n) :
    MoltPetit.Model.windowCount ((modelClaimOf n (toModelBlock G) (pre.map toModelBlock)).tail ++ [toModelBlock b]) u n =
    MoltPetit.Model.windowCount (((G :: pre).map toModelBlock) ++ [toModelBlock b]) u n := by
  rw [MoltPetit.Model.windowCount_append, MoltPetit.Model.windowCount_append]
  congr 1
  dsimp [modelClaimOf] at hu ⊢
  have hlo : ((toModelBlock G :: pre.map toModelBlock).getLast (List.cons_ne_nil _ _)).slot + 2 - n ≤ u := by omega
  exact MoltPetit.Model.windowCount_filter_low hlo ((G :: pre).map toModelBlock) n

lemma foldSched_complete_aux {n q era : U64} {G : Block}
    (hn : 1 ≤ n.val) (hsmall : n.val < 2 ^ 62) (hq : quorum n = ok q) (hera : 0 < era.val) :
    ∀ (bs : List Block) (pre : List Block) (st : CertStateG U64),
    (∀ b ∈ G :: pre ++ bs, b.slot.val < 2 ^ 62 ∧ b.height.val < 2 ^ 62) →
    MoltPetit.Model.validChain n.val ((G :: pre ++ bs).map toModelBlock) = true →
    (∀ b ∈ bs, b.slot.val / era.val ≤ b.key_index.val) →
    TailRepr n.val st (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) →
    (∀ s ∈ entrySlots st.tail, s < 2 ^ 62) →
    FoldSched n q era st bs := by
  intro bs
  induction bs with
  | nil =>
    intro pre st hbound hV hPin hrep hrest_bound
    dsimp [FoldSched]
  | cons b rest ih =>
    intro pre st hbound hV hPin hrep hrest_bound
    let cl := modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)
    let A := (G :: pre).map toModelBlock
    let ch := (G :: pre ++ b :: rest).map toModelBlock
    let t := A.getLast (List.cons_ne_nil _ _)
    have ht_mem_A : t ∈ A := List.getLast_mem (List.cons_ne_nil _ _)
    obtain ⟨b₀, hb₀_pre, ht_eq⟩ := List.mem_map.mp ht_mem_A
    have hb₀_all : b₀ ∈ G :: pre ++ b :: rest := by
      exact List.mem_append_left (b :: rest) hb₀_pre
    have ⟨hb₀_s, hb₀_h⟩ := hbound b₀ hb₀_all
    have htip_s : st.tip_slot.val < 2 ^ 62 := by
      rw [hrep.tip_slot]
      change t.slot < 2 ^ 62
      rw [← ht_eq]
      exact hb₀_s
    have htip_h : st.tip_height.val < 2 ^ 62 := by
      rw [hrep.tip_height]
      change t.height < 2 ^ 62
      rw [← ht_eq]
      exact hb₀_h
    have hb_all : b ∈ G :: pre ++ b :: rest := by
      simp only [List.mem_cons, List.mem_append, List.mem_cons, true_or, or_true]
    have ⟨hb_s, hb_h⟩ := hbound b hb_all
    have hVS := MoltPetit.Model.validChain_sound hV
    have hSeq := hVS.1
    have hStrict := hVS.2.1
    have hParent := hVS.2.2.1
    have hDense := hVS.2.2.2
    have hlen_pos : 0 < A.length := by
      dsimp [A]
      simp only [List.length_map, Nat.succ_pos]
    have hch_eq : ch = A ++ toModelBlock b :: rest.map toModelBlock := by
      dsimp [ch, A]
      simp only [List.map_cons, List.map_append]
    have hAt_b : MoltPetit.Model.blockAt? ch A.length = some (toModelBlock b) := by
      unfold MoltPetit.Model.blockAt?
      rw [hch_eq]
      exact getElem?_append_head A (toModelBlock b) (rest.map toModelBlock)
    have hAt_t : MoltPetit.Model.blockAt? ch (A.length - 1) = some t := by
      unfold MoltPetit.Model.blockAt?
      rw [hch_eq, List.getElem?_append_left (by omega)]
      rw [← List.getLast?_eq_getElem?]
      exact List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)
    have hBh : (toModelBlock b).height = A.length := hSeq hAt_b
    have hTh : t.height = A.length - 1 := hSeq hAt_t
    have hcl_h : cl.tipHeight = t.height := rfl
    have hcl_s : cl.tipSlot = t.slot := rfl
    have hcl_id : cl.tipId = t.id := rfl
    have hchild_h : (toModelBlock b).height = cl.tipHeight + 1 := by
      rw [hcl_h, hBh, hTh]
      omega
    have hchild_s : cl.tipSlot < (toModelBlock b).slot := by
      rw [hcl_s]
      exact MoltPetit.Model.strictSlots_lt hStrict hAt_t hAt_b (by omega)
    have hchild_prev : (toModelBlock b).prev = some cl.tipId := by
      have hsucc_len : A.length = (A.length - 1) + 1 := by omega
      have hAt_b' : MoltPetit.Model.blockAt? ch ((A.length - 1) + 1) = some (toModelBlock b) := by
        rwa [← hsucc_len]
      obtain ⟨P, hP_at, hP_prev⟩ := MoltPetit.Model.parentLinked_at_succ hParent hAt_b'
      have hP_eq : P = t := Option.some.inj (hP_at.symm.trans hAt_t)
      rw [hcl_id, ← hP_eq]
      exact hP_prev
    have hdense : ∀ u : Nat, cl.tipSlot + 2 ≤ u + n.val → u + n.val ≤ (toModelBlock b).slot + 1 →
        q.val ≤ MoltPetit.Model.windowCount (cl.tail ++ [toModelBlock b]) u n.val := by
      intro u huT huB
      rw [quorum_val_of_ok hq]
      rw [windowCount_claim_extend_eq huT]
      have hStrict' : MoltPetit.Model.StrictSlots (A ++ toModelBlock b :: rest.map toModelBlock) := by
        rw [← hch_eq]; exact hStrict
      have hrest_gt : ∀ x ∈ rest.map toModelBlock, (toModelBlock b).slot < x.slot := by
        intro x hx
        exact strictSlots_append_mem hStrict' hx
      have hwc_rest : MoltPetit.Model.windowCount ((A ++ [toModelBlock b]) ++ rest.map toModelBlock) u n.val =
          MoltPetit.Model.windowCount (A ++ [toModelBlock b]) u n.val := by
        apply MoltPetit.Model.windowCount_append_high
        intro x hx
        have := hrest_gt x hx
        omega
      rw [← hwc_rest]
      have hch_app : ch = (A ++ [toModelBlock b]) ++ rest.map toModelBlock := by
        rw [hch_eq, List.append_assoc, List.singleton_append]
      rw [← hch_app]
      exact hDense hAt_b u huB
    have hcore := cert_step_core_be_complete hn hsmall hq hrep htip_h htip_s hb_h hb_s hrest_bound hchild_h hchild_s hchild_prev hdense
    have hpin_b := hPin b (by simp)
    have hsched := cert_step_sched_be_complete hera hcore hpin_b
    obtain ⟨t', ht'⟩ : ∃ t', cert_next_tail_be UB () st.tail b.slot = ok t' := ⟨_, cert_next_tail_be_corr _ _⟩
    have hrep' := cert_next_tail_be_repr b hq hn hrep hcore ht'
    have hcl_eq : modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock ++ [toModelBlock b]) =
        { tipId := (toModelBlock b).id,
          tipSlot := (toModelBlock b).slot,
          tipHeight := (toModelBlock b).height,
          tail := (cl.tail ++ [toModelBlock b]).filter
            fun x => decide ((toModelBlock b).slot + 2 - n.val ≤ x.slot) } :=
      modelClaimOf_step_lt n.val (toModelBlock G) (pre.map toModelBlock) (toModelBlock b) hchild_s
    have hmap_app : (pre ++ [b]).map toModelBlock = pre.map toModelBlock ++ [toModelBlock b] := by simp
    have hrep_step : TailRepr n.val (stepState b t')
        (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock)) := by
      rw [hmap_app, hcl_eq]
      exact hrep'
    have hrest_bound_step := entrySlots_cert_next_tail_bound hrest_bound hb_s ht'
    have hassoc : G :: (pre ++ [b]) ++ rest = G :: pre ++ b :: rest := by
      simp
    have hbound' : ∀ x ∈ G :: (pre ++ [b]) ++ rest, x.slot.val < 2 ^ 62 ∧ x.height.val < 2 ^ 62 := by
      rw [hassoc]; exact hbound
    have hV' : MoltPetit.Model.validChain n.val ((G :: (pre ++ [b]) ++ rest).map toModelBlock) = true := by
      rw [hassoc]; exact hV
    have hPin' : ∀ x ∈ rest, x.slot.val / era.val ≤ x.key_index.val := by
      intro x hx
      exact hPin x (by simp [hx])
    have hrest_sched := ih (pre ++ [b]) (stepState b t') hbound' hV' hPin' hrep_step hrest_bound_step
    exact ⟨hsched, t', ht', hrest_sched⟩

theorem cert_fold_sched_complete : MoltPaper.thm_cert_fold_sched_complete := by
  intro n q era G bs hn hsmall hq hera hbound hG hV hPin
  have hbase_rep : TailRepr n.val (genesisState n.val G)
      (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock)) := by
    simp only [List.map_nil]
    exact tailRepr_genesisState n.val G
  have hbase_tail_bound : ∀ s ∈ entrySlots (genesisState n.val G).tail, s < 2 ^ 62 := by
    dsimp [genesisState]
    have hG_bound := hbound G (by simp)
    exact entrySlots_initTail_bound hG_bound.1
  have hbound' : ∀ b ∈ G :: [] ++ bs, b.slot.val < 2 ^ 62 ∧ b.height.val < 2 ^ 62 := by
    intro b hb
    apply hbound
    simp only [List.cons_append, List.nil_append] at hb
    exact hb
  have hV' : MoltPetit.Model.validChain n.val ((G :: [] ++ bs).map toModelBlock) = true := by
    have : (G :: [] ++ bs) = G :: bs := by simp only [List.cons_append, List.nil_append]
    rw [this]
    exact hV
  exact foldSched_complete_aux hn hsmall hq hera bs [] (genesisState n.val G)
    hbound' hV' hPin hbase_rep hbase_tail_bound


lemma foldLock_complete_aux {n q : U64} {G : Block}
    (hn : 1 ≤ n.val) (hsmall : n.val < 2 ^ 62) (hq : quorum n = ok q) :
    ∀ (bs : List Block) (pre : List Block) (st : CertStateG U64) (g : U64),
    (∀ b ∈ G :: pre ++ bs, b.slot.val < 2 ^ 62 ∧ b.height.val < 2 ^ 62) →
    MoltPetit.Model.validChain n.val ((G :: pre ++ bs).map toModelBlock) = true →
    MoltPetit.Model.lockstepOk n.val ((G :: pre ++ bs).map toModelBlock) = true →
    TailRepr n.val st (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) →
    (∀ s ∈ entrySlots st.tail, s < 2 ^ 62) →
    g = ((G :: pre).getLast (List.cons_ne_nil _ _)).key_index →
    FoldLock n q st g bs := by
  intro bs
  induction bs with
  | nil =>
    intro pre st g hbound hV hLock hrep hrest_bound hg
    dsimp [FoldLock]
  | cons b rest ih =>
    intro pre st g hbound hV hLock hrep hrest_bound hg
    let cl := modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)
    let A := (G :: pre).map toModelBlock
    let ch := (G :: pre ++ b :: rest).map toModelBlock
    let t := A.getLast (List.cons_ne_nil _ _)
    have ht_mem_A : t ∈ A := List.getLast_mem (List.cons_ne_nil _ _)
    obtain ⟨b₀, hb₀_pre, ht_eq⟩ := List.mem_map.mp ht_mem_A
    have hb₀_all : b₀ ∈ G :: pre ++ b :: rest := by
      exact List.mem_append_left (b :: rest) hb₀_pre
    have ⟨hb₀_s, hb₀_h⟩ := hbound b₀ hb₀_all
    have htip_s : st.tip_slot.val < 2 ^ 62 := by
      rw [hrep.tip_slot]
      change t.slot < 2 ^ 62
      rw [← ht_eq]
      exact hb₀_s
    have htip_h : st.tip_height.val < 2 ^ 62 := by
      rw [hrep.tip_height]
      change t.height < 2 ^ 62
      rw [← ht_eq]
      exact hb₀_h
    have hb_all : b ∈ G :: pre ++ b :: rest := by
      simp only [List.mem_cons, List.mem_append, List.mem_cons, true_or, or_true]
    have ⟨hb_s, hb_h⟩ := hbound b hb_all
    have hVS := MoltPetit.Model.validChain_sound hV
    have hSeq := hVS.1
    have hStrict := hVS.2.1
    have hParent := hVS.2.2.1
    have hDense := hVS.2.2.2
    have hlen_pos : 0 < A.length := by
      dsimp [A]
      simp only [List.length_map, Nat.succ_pos]
    have hch_eq : ch = A ++ toModelBlock b :: rest.map toModelBlock := by
      dsimp [ch, A]
      simp only [List.map_cons, List.map_append]
    have hAt_b : MoltPetit.Model.blockAt? ch A.length = some (toModelBlock b) := by
      unfold MoltPetit.Model.blockAt?
      rw [hch_eq]
      exact getElem?_append_head A (toModelBlock b) (rest.map toModelBlock)
    have hAt_t : MoltPetit.Model.blockAt? ch (A.length - 1) = some t := by
      unfold MoltPetit.Model.blockAt?
      rw [hch_eq, List.getElem?_append_left (by omega)]
      rw [← List.getLast?_eq_getElem?]
      exact List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)
    have hBh : (toModelBlock b).height = A.length := hSeq hAt_b
    have hTh : t.height = A.length - 1 := hSeq hAt_t
    have hcl_h : cl.tipHeight = t.height := rfl
    have hcl_s : cl.tipSlot = t.slot := rfl
    have hcl_id : cl.tipId = t.id := rfl
    have hchild_h : (toModelBlock b).height = cl.tipHeight + 1 := by
      rw [hcl_h, hBh, hTh]
      omega
    have hchild_s : cl.tipSlot < (toModelBlock b).slot := by
      rw [hcl_s]
      exact MoltPetit.Model.strictSlots_lt hStrict hAt_t hAt_b (by omega)
    have hchild_prev : (toModelBlock b).prev = some cl.tipId := by
      have hsucc_len : A.length = (A.length - 1) + 1 := by omega
      have hAt_b' : MoltPetit.Model.blockAt? ch ((A.length - 1) + 1) = some (toModelBlock b) := by
        rwa [← hsucc_len]
      obtain ⟨P, hP_at, hP_prev⟩ := MoltPetit.Model.parentLinked_at_succ hParent hAt_b'
      have hP_eq : P = t := Option.some.inj (hP_at.symm.trans hAt_t)
      rw [hcl_id, ← hP_eq]
      exact hP_prev
    have hdense : ∀ u : Nat, cl.tipSlot + 2 ≤ u + n.val → u + n.val ≤ (toModelBlock b).slot + 1 →
        q.val ≤ MoltPetit.Model.windowCount (cl.tail ++ [toModelBlock b]) u n.val := by
      intro u huT huB
      rw [quorum_val_of_ok hq]
      rw [windowCount_claim_extend_eq huT]
      have hStrict' : MoltPetit.Model.StrictSlots (A ++ toModelBlock b :: rest.map toModelBlock) := by
        rw [← hch_eq]; exact hStrict
      have hrest_gt : ∀ x ∈ rest.map toModelBlock, (toModelBlock b).slot < x.slot := by
        intro x hx
        exact strictSlots_append_mem hStrict' hx
      have hwc_rest : MoltPetit.Model.windowCount ((A ++ [toModelBlock b]) ++ rest.map toModelBlock) u n.val =
          MoltPetit.Model.windowCount (A ++ [toModelBlock b]) u n.val := by
        apply MoltPetit.Model.windowCount_append_high
        intro x hx
        have := hrest_gt x hx
        omega
      rw [← hwc_rest]
      have hch_app : ch = (A ++ [toModelBlock b]) ++ rest.map toModelBlock := by
        rw [hch_eq, List.append_assoc, List.singleton_append]
      rw [← hch_app]
      exact hDense hAt_b u huB
    have hcore := cert_step_core_be_complete hn hsmall hq hrep htip_h htip_s hb_h hb_s hrest_bound hchild_h hchild_s hchild_prev hdense
    have ht_eq_last : t = toModelBlock ((G :: pre).getLast (List.cons_ne_nil _ _)) := by
      dsimp [t, A]
      exact getLast_map toModelBlock G pre
    have hlast_mem : toModelBlock ((G :: pre).getLast (List.cons_ne_nil _ _)) ∈ A := by
      dsimp [A]
      exact List.mem_map_of_mem (List.getLast_mem (List.cons_ne_nil _ _))
    have hLock_ch : MoltPetit.Model.lockstepOk n.val (A ++ toModelBlock b :: rest.map toModelBlock) = true := by
      rw [← hch_eq]; exact hLock
    have hcross := lockstep_append_mem hLock_ch hlast_mem
    have hle : g.val ≤ b.key_index.val := by
      have hki_eq : (toModelBlock ((G :: pre).getLast (List.cons_ne_nil _ _))).keyIndex = g.val := by
        dsimp [toModelBlock]
        rw [hg]
      have hcross_le := hcross.2
      rwa [hki_eq] at hcross_le
    have hmix : st.tip_slot.val / n.val = b.slot.val / n.val → g.val = b.key_index.val := by
      intro heq
      have hslot_eq : (toModelBlock ((G :: pre).getLast (List.cons_ne_nil _ _))).slot = st.tip_slot.val := by
        rw [hrep.tip_slot, ← ht_eq_last]
        rfl
      have hki_eq : (toModelBlock ((G :: pre).getLast (List.cons_ne_nil _ _))).keyIndex = g.val := by
        dsimp [toModelBlock]
        rw [hg]
      have hreq : (toModelBlock ((G :: pre).getLast (List.cons_ne_nil _ _))).slot / n.val =
          (toModelBlock b).slot / n.val := by
        rw [hslot_eq]
        exact heq
      have hres := hcross.1 hreq
      rw [hki_eq] at hres
      exact hres
    have hlock_step := cert_step_lock_be_complete hn hcore hle hmix
    obtain ⟨t', ht'⟩ : ∃ t', cert_next_tail_be UB () st.tail b.slot = ok t' := ⟨_, cert_next_tail_be_corr _ _⟩
    have hrep' := cert_next_tail_be_repr b hq hn hrep hcore ht'
    have hcl_eq : modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock ++ [toModelBlock b]) =
        { tipId := (toModelBlock b).id,
          tipSlot := (toModelBlock b).slot,
          tipHeight := (toModelBlock b).height,
          tail := (cl.tail ++ [toModelBlock b]).filter
            fun x => decide ((toModelBlock b).slot + 2 - n.val ≤ x.slot) } :=
      modelClaimOf_step_lt n.val (toModelBlock G) (pre.map toModelBlock) (toModelBlock b) hchild_s
    have hmap_app : (pre ++ [b]).map toModelBlock = pre.map toModelBlock ++ [toModelBlock b] := by simp
    have hrep_step : TailRepr n.val (stepState b t')
        (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock)) := by
      rw [hmap_app, hcl_eq]
      exact hrep'
    have hrest_bound_step := entrySlots_cert_next_tail_bound hrest_bound hb_s ht'
    have hassoc : G :: (pre ++ [b]) ++ rest = G :: pre ++ b :: rest := by
      simp
    have hbound' : ∀ x ∈ G :: (pre ++ [b]) ++ rest, x.slot.val < 2 ^ 62 ∧ x.height.val < 2 ^ 62 := by
      rw [hassoc]; exact hbound
    have hV' : MoltPetit.Model.validChain n.val ((G :: (pre ++ [b]) ++ rest).map toModelBlock) = true := by
      rw [hassoc]; exact hV
    have hLock' : MoltPetit.Model.lockstepOk n.val ((G :: (pre ++ [b]) ++ rest).map toModelBlock) = true := by
      rw [hassoc]; exact hLock
    have hg' : b.key_index = ((G :: (pre ++ [b])).getLast (List.cons_ne_nil _ _)).key_index := by
      rw [getLast_cons_append_singleton]
    have hrest_lock := ih (pre ++ [b]) (stepState b t') b.key_index hbound' hV' hLock' hrep_step hrest_bound_step hg'
    exact ⟨hlock_step, t', ht', hrest_lock⟩

theorem cert_fold_lock_complete : MoltPaper.thm_cert_fold_lock_complete := by
  intro n q G bs hn hsmall hq hbound hG hV hLock
  have hbase_rep : TailRepr n.val (genesisState n.val G)
      (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock)) := by
    simp only [List.map_nil]
    exact tailRepr_genesisState n.val G
  have hbase_tail_bound : ∀ s ∈ entrySlots (genesisState n.val G).tail, s < 2 ^ 62 := by
    dsimp [genesisState]
    have hG_bound := hbound G (by simp)
    exact entrySlots_initTail_bound hG_bound.1
  have hbound' : ∀ b ∈ G :: [] ++ bs, b.slot.val < 2 ^ 62 ∧ b.height.val < 2 ^ 62 := by
    intro b hb
    apply hbound
    simp only [List.cons_append, List.nil_append] at hb
    exact hb
  have hV' : MoltPetit.Model.validChain n.val ((G :: [] ++ bs).map toModelBlock) = true := by
    have : (G :: [] ++ bs) = G :: bs := by simp only [List.cons_append, List.nil_append]
    rw [this]
    exact hV
  have hLock' : MoltPetit.Model.lockstepOk n.val ((G :: [] ++ bs).map toModelBlock) = true := by
    have : (G :: [] ++ bs) = G :: bs := by simp only [List.cons_append, List.nil_append]
    rw [this]
    exact hLock
  have hg : G.key_index = ((G :: []).getLast (List.cons_ne_nil _ _)).key_index := rfl
  exact foldLock_complete_aux hn hsmall hq bs [] (genesisState n.val G) G.key_index
    hbound' hV' hLock' hbase_rep hbase_tail_bound hg

lemma foldl_max_le : ∀ (L : List Nat) (a b : Nat),
    L.foldl max a ≤ b ↔ a ≤ b ∧ ∀ x ∈ L, x ≤ b := by
  intro L
  induction L with
  | nil =>
    intro a b
    simp
  | cons x xs ih =>
    intro a b
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih (max a x) b]
    constructor
    · rintro ⟨hmax, hxs⟩
      have ha : a ≤ b := by omega
      have hx : x ≤ b := by omega
      exact ⟨ha, fun y hy => hy.elim (fun h => by subst h; exact hx) (hxs y)⟩
    · rintro ⟨ha, hall⟩
      have hx : x ≤ b := hall x (Or.inl rfl)
      have hmax : max a x ≤ b := by omega
      refine ⟨hmax, fun y hy => hall y (Or.inr hy)⟩

lemma keyFloor_le_iff (n : Nat) (c : MoltPetit.Model.Chain) (i b : Nat) :
    MoltPetit.Model.keyFloor n c i ≤ b ↔
      ∀ B ∈ c, MoltPetit.Model.producerForSlot n B.slot = i → B.keyIndex ≤ b := by
  unfold MoltPetit.Model.keyFloor
  rw [foldl_max_le]
  simp only [Nat.zero_le, true_and, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h B hB hprod
    exact h B.keyIndex ⟨B, ⟨hB, hprod⟩, rfl⟩
  · rintro h x ⟨B, ⟨hB, hprod⟩, rfl⟩
    exact h B hB hprod

lemma keyFloor_snoc (n : Nat) (c : MoltPetit.Model.Chain) (b : MoltPetit.Model.Block) (i : Nat) :
    MoltPetit.Model.keyFloor n (c ++ [b]) i =
      if MoltPetit.Model.producerForSlot n b.slot = i then
        max (MoltPetit.Model.keyFloor n c i) b.keyIndex
      else
        MoltPetit.Model.keyFloor n c i := by
  unfold MoltPetit.Model.keyFloor
  rw [List.filter_append, List.map_append, List.foldl_append]
  dsimp [List.filter]
  by_cases hprod : MoltPetit.Model.producerForSlot n b.slot = i
  · have hdec : decide (MoltPetit.Model.producerForSlot n b.slot = i) = true := decide_eq_true hprod
    rw [hdec]
    simp only [List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [if_pos hprod]
  · have hdec : decide (MoltPetit.Model.producerForSlot n b.slot = i) = false := decide_eq_false hprod
    rw [hdec]
    simp only [List.filter_cons, List.filter_nil, List.map_nil, List.foldl_nil]
    rw [if_neg hprod]

lemma keyFloor_singleton (n : Nat) (G : MoltPetit.Model.Block) (h0 : G.slot = 0) (hn : 1 ≤ n) :
    MoltPetit.Model.keyFloor n [G] = fun i => if i = 0 then G.keyIndex else 0 := by
  funext i
  unfold MoltPetit.Model.keyFloor
  dsimp [List.filter]
  have hprod : MoltPetit.Model.producerForSlot n G.slot = 0 := by
    dsimp [MoltPetit.Model.producerForSlot]
    rw [h0]
    exact Nat.zero_mod n
  by_cases hi : i = 0
  · subst hi
    have hdec : decide (MoltPetit.Model.producerForSlot n G.slot = 0) = true := by
      simp [hprod]
    rw [hdec]
    simp
  · have hdec : decide (MoltPetit.Model.producerForSlot n G.slot = i) = false := by
      rw [hprod]
      simp [hi]
    rw [hdec]
    simp [hi]

lemma floors_bump_be_complete : ∀ (fl : FloorsG U64) (i p ki : U64),
    i.val + floorsLen fl < 2 ^ 64 →
    ∃ fl', floors_bump_be UBK () fl i p ki = ok fl' := by
  intro fl
  induction fl with
  | FNil =>
    intro i p ki _
    refine ⟨FloorsG.FNil, ?_⟩
    rw [floors_bump_be]
  | FCons f tl ih =>
    intro i p ki hbound
    have h1 : (1#u64 : U64).val = 1 := rfl
    have hlt : i.val + 1 < 2 ^ 64 := by
      change i.val + (floorsLen tl + 1) < 2 ^ 64 at hbound
      omega
    have hi1 : ∃ i1 : U64, i + 1#u64 = ok i1 ∧ i1.val = i.val + 1 :=
      u64_add_ok (by rw [h1]; exact hlt)
    obtain ⟨i1, hi1_eq, hi1_val⟩ := hi1
    have hbound_tl : i1.val + floorsLen tl < 2 ^ 64 := by
      rw [hi1_val]
      change i.val + 1 + floorsLen tl < 2 ^ 64
      change i.val + (floorsLen tl + 1) < 2 ^ 64 at hbound
      omega
    obtain ⟨fg, hfg⟩ := ih i1 p ki hbound_tl
    rw [floors_bump_be]
    dsimp [UB, U64Backend.Insts.Molt_petitBackendU64Bool.eq,
      U64Backend.Insts.Molt_petitBackendU64Bool.lt,
      U64Backend.Insts.Molt_petitBackendU64Bool.and,
      U64Backend.Insts.Molt_petitBackendKU64Bool.select,
      BackendK.select,
      U64Backend.Insts.Molt_petitBackendU64Bool.one,
      U64Backend.Insts.Molt_petitBackendU64Bool.add]
    simp only [bind_tc_ok]
    rw [hi1_eq]
    simp only [bind_tc_ok]
    rw [hfg]
    simp only [bind_tc_ok]
    by_cases hip : i = p
    · have hdec : decide (i = p) = true := decide_eq_true hip
      rw [hdec]
      by_cases hfk : f < ki
      · have hdec2 : decide (f < ki) = true := decide_eq_true hfk
        rw [hdec2]
        exact ⟨_, rfl⟩
      · have hdec2 : decide (f < ki) = false := decide_eq_false hfk
        rw [hdec2]
        exact ⟨_, rfl⟩
    · have hdec : decide (i = p) = false := decide_eq_false hip
      rw [hdec]
      exact ⟨_, rfl⟩

lemma floors_ok_be_complete : ∀ (fl : FloorsG U64) (i p ki : U64),
    i.val + floorsLen fl < 2 ^ 64 →
    (∀ (k : Nat), p.val = i.val + k → k < floorsLen fl → floorsFun fl k ≤ ki.val) →
    floors_ok_be UBK () fl i p ki = ok true := by
  intro fl
  induction fl with
  | FNil =>
    intro i p ki _ _
    rw [floors_ok_be]
    simp [UB, U64Backend.Insts.Molt_petitBackendU64Bool.bool_const]
  | FCons f tl ih =>
    intro i p ki hbound hle
    have h1 : (1#u64 : U64).val = 1 := rfl
    have hlt : i.val + 1 < 2 ^ 64 := by
      change i.val + (floorsLen tl + 1) < 2 ^ 64 at hbound
      omega
    have hi1 : ∃ i1 : U64, i + 1#u64 = ok i1 ∧ i1.val = i.val + 1 :=
      u64_add_ok (by rw [h1]; exact hlt)
    obtain ⟨i1, hi1_eq, hi1_val⟩ := hi1
    have hbound_tl : i1.val + floorsLen tl < 2 ^ 64 := by
      rw [hi1_val]
      change i.val + 1 + floorsLen tl < 2 ^ 64
      change i.val + (floorsLen tl + 1) < 2 ^ 64 at hbound
      omega
    have hle_tl : ∀ (k : Nat), p.val = i1.val + k → k < floorsLen tl → floorsFun tl k ≤ ki.val := by
      intro k hk hlen
      have hk' : p.val = i.val + (k + 1) := by
        rw [hk, hi1_val]
        omega
      have hlen' : k + 1 < floorsLen (FloorsG.FCons f tl) := by
        dsimp [floorsLen]
        omega
      have := hle (k + 1) hk' hlen'
      exact this
    have hmore := ih i1 p ki hbound_tl hle_tl
    rw [floors_ok_be]
    dsimp [UB, U64Backend.Insts.Molt_petitBackendU64Bool.eq,
      U64Backend.Insts.Molt_petitBackendU64Bool.lt,
      U64Backend.Insts.Molt_petitBackendU64Bool.and,
      U64Backend.Insts.Molt_petitBackendU64Bool.not,
      U64Backend.Insts.Molt_petitBackendU64Bool.one,
      U64Backend.Insts.Molt_petitBackendU64Bool.add]
    simp only [bind_tc_ok]
    rw [hi1_eq]
    simp only [bind_tc_ok]
    rw [hmore]
    simp only [bind_tc_ok]
    by_cases hip : i = p
    · have h0 : p.val = i.val + 0 := by rw [hip]; omega
      have hlen0 : 0 < floorsLen (FloorsG.FCons f tl) := by
        dsimp [floorsLen]; omega
      have hf_le := hle 0 h0 hlen0
      change f.val ≤ ki.val at hf_le
      have hnot_lt : ¬ (ki < f) := by
        intro hlt'
        change ki.val < f.val at hlt'
        omega
      have hdec : decide (i = p) = true := decide_eq_true hip
      have hdec2 : decide (ki < f) = false := decide_eq_false hnot_lt
      rw [hdec, hdec2]
      rfl
    · have hdec : decide (i = p) = false := decide_eq_false hip
      rw [hdec]
      rfl

theorem cert_step_k_be_complete {n q : U64} {st : CertStateG U64} {fl : FloorsG U64} {b : Block}
    (hn : 1 ≤ n.val)
    (hsmall : n.val < 2 ^ 62)
    (hb_s : b.slot.val < 2 ^ 62)
    (hlen : floorsLen fl = n.val)
    (hcore : cert_step_core_be UBK () n q st (toBlockG b) = ok true)
    (hle : floorsFun fl (b.slot.val % n.val) ≤ b.key_index.val) :
    cert_step_k_be UBK () n q st fl (toBlockG b) b.key_index = ok true := by
  obtain ⟨p, hp, hp_val⟩ := ubk_rem b.slot n (by omega)
  have hbound_fl : (0#u64 : U64).val + floorsLen fl < 2 ^ 64 := by
    rw [hlen]
    change 0 + n.val < 2 ^ 64
    omega
  have hfl_ok := floors_ok_be_complete fl 0#u64 p b.key_index hbound_fl (by
    intro k hk hklen
    have hk_eq : k = b.slot.val % n.val := by
      have h0 : (0#u64 : U64).val = 0 := rfl
      rw [h0, Nat.zero_add] at hk
      rw [← hk, hp_val]
    rw [hk_eq]
    exact hle)
  dsimp [cert_step_k_be]
  rw [hcore]
  simp only [bind_tc_ok]
  change U64Backend.Insts.Molt_petitBackendKU64Bool.rem () b.slot n = ok p at hp
  rw [hp]
  simp only [bind_tc_ok]
  dsimp [UBK, UB, U64Backend.Insts.Molt_petitBackendU64Bool.zero]
  simp only [bind_tc_ok]
  rw [hfl_ok]
  simp only [bind_tc_ok]
  rfl

theorem cert_next_floors_be_complete {n : U64} {fl : FloorsG U64} (b : Block)
    (hn : 1 ≤ n.val)
    (hlen : floorsLen fl = n.val)
    (hsmall : n.val < 2 ^ 62) :
    ∃ fl', cert_next_floors_be UBK () n fl (toBlockG b) b.key_index = ok fl' := by
  obtain ⟨p, hp, _⟩ := ubk_rem b.slot n (by omega)
  have hbound_fl : (0#u64 : U64).val + floorsLen fl < 2 ^ 64 := by
    rw [hlen]
    change 0 + n.val < 2 ^ 64
    omega
  obtain ⟨fl', hfl'⟩ := floors_bump_be_complete fl 0#u64 p b.key_index hbound_fl
  dsimp [cert_next_floors_be]
  change U64Backend.Insts.Molt_petitBackendKU64Bool.rem () b.slot n = ok p at hp
  rw [hp]
  simp only [bind_tc_ok]
  dsimp [UBK, UB, U64Backend.Insts.Molt_petitBackendU64Bool.zero]
  simp only [bind_tc_ok]
  exact ⟨fl', hfl'⟩

lemma foldK_complete_aux {n q : U64} {G : Block}
    (hn : 1 ≤ n.val) (hsmall : n.val < 2 ^ 62) (hq : quorum n = ok q) :
    ∀ (bs : List Block) (pre : List Block) (st : CertStateG U64) (fl : FloorsG U64),
    (∀ b ∈ G :: pre ++ bs, b.slot.val < 2 ^ 62 ∧ b.height.val < 2 ^ 62) →
    MoltPetit.Model.validChain n.val ((G :: pre ++ bs).map toModelBlock) = true →
    MoltPetit.Model.keyMonoOk n.val ((G :: pre ++ bs).map toModelBlock) = true →
    TailRepr n.val st (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) →
    (∀ s ∈ entrySlots st.tail, s < 2 ^ 62) →
    floorsLen fl = n.val →
    floorsFun fl = MoltPetit.Model.keyFloor n.val ((G :: pre).map toModelBlock) →
    ∃ out, FoldK n q st fl bs out := by
  intro bs
  induction bs with
  | nil =>
    intro pre st fl hbound hV hMono hrep hrest_bound hlen hfun
    exact ⟨fl, rfl⟩
  | cons b rest ih =>
    intro pre st fl hbound hV hMono hrep hrest_bound hlen hfun
    let cl := modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)
    let A := (G :: pre).map toModelBlock
    let ch := (G :: pre ++ b :: rest).map toModelBlock
    let t := A.getLast (List.cons_ne_nil _ _)
    have ht_mem_A : t ∈ A := List.getLast_mem (List.cons_ne_nil _ _)
    obtain ⟨b₀, hb₀_pre, ht_eq⟩ := List.mem_map.mp ht_mem_A
    have hb₀_all : b₀ ∈ G :: pre ++ b :: rest := by
      exact List.mem_append_left (b :: rest) hb₀_pre
    have ⟨hb₀_s, hb₀_h⟩ := hbound b₀ hb₀_all
    have htip_s : st.tip_slot.val < 2 ^ 62 := by
      rw [hrep.tip_slot]
      change t.slot < 2 ^ 62
      rw [← ht_eq]
      exact hb₀_s
    have htip_h : st.tip_height.val < 2 ^ 62 := by
      rw [hrep.tip_height]
      change t.height < 2 ^ 62
      rw [← ht_eq]
      exact hb₀_h
    have hb_all : b ∈ G :: pre ++ b :: rest := by
      simp only [List.mem_cons, List.mem_append, List.mem_cons, true_or, or_true]
    have ⟨hb_s, hb_h⟩ := hbound b hb_all
    have hVS := MoltPetit.Model.validChain_sound hV
    have hSeq := hVS.1
    have hStrict := hVS.2.1
    have hParent := hVS.2.2.1
    have hDense := hVS.2.2.2
    have hlen_pos : 0 < A.length := by
      dsimp [A]
      simp only [List.length_map, Nat.succ_pos]
    have hch_eq : ch = A ++ toModelBlock b :: rest.map toModelBlock := by
      dsimp [ch, A]
      simp only [List.map_cons, List.map_append]
    have hAt_b : MoltPetit.Model.blockAt? ch A.length = some (toModelBlock b) := by
      unfold MoltPetit.Model.blockAt?
      rw [hch_eq]
      exact getElem?_append_head A (toModelBlock b) (rest.map toModelBlock)
    have hAt_t : MoltPetit.Model.blockAt? ch (A.length - 1) = some t := by
      unfold MoltPetit.Model.blockAt?
      rw [hch_eq, List.getElem?_append_left (by omega)]
      rw [← List.getLast?_eq_getElem?]
      exact List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)
    have hBh : (toModelBlock b).height = A.length := hSeq hAt_b
    have hTh : t.height = A.length - 1 := hSeq hAt_t
    have hcl_h : cl.tipHeight = t.height := rfl
    have hcl_s : cl.tipSlot = t.slot := rfl
    have hcl_id : cl.tipId = t.id := rfl
    have hchild_h : (toModelBlock b).height = cl.tipHeight + 1 := by
      rw [hcl_h, hBh, hTh]
      omega
    have hchild_s : cl.tipSlot < (toModelBlock b).slot := by
      rw [hcl_s]
      exact MoltPetit.Model.strictSlots_lt hStrict hAt_t hAt_b (by omega)
    have hchild_prev : (toModelBlock b).prev = some cl.tipId := by
      have hsucc_len : A.length = (A.length - 1) + 1 := by omega
      have hAt_b' : MoltPetit.Model.blockAt? ch ((A.length - 1) + 1) = some (toModelBlock b) := by
        rwa [← hsucc_len]
      obtain ⟨P, hP_at, hP_prev⟩ := MoltPetit.Model.parentLinked_at_succ hParent hAt_b'
      have hP_eq : P = t := Option.some.inj (hP_at.symm.trans hAt_t)
      rw [hcl_id, ← hP_eq]
      exact hP_prev
    have hdense : ∀ u : Nat, cl.tipSlot + 2 ≤ u + n.val → u + n.val ≤ (toModelBlock b).slot + 1 →
        q.val ≤ MoltPetit.Model.windowCount (cl.tail ++ [toModelBlock b]) u n.val := by
      intro u huT huB
      rw [quorum_val_of_ok hq]
      rw [windowCount_claim_extend_eq huT]
      have hStrict' : MoltPetit.Model.StrictSlots (A ++ toModelBlock b :: rest.map toModelBlock) := by
        rw [← hch_eq]; exact hStrict
      have hrest_gt : ∀ x ∈ rest.map toModelBlock, (toModelBlock b).slot < x.slot := by
        intro x hx
        exact strictSlots_append_mem hStrict' hx
      have hwc_rest : MoltPetit.Model.windowCount ((A ++ [toModelBlock b]) ++ rest.map toModelBlock) u n.val =
          MoltPetit.Model.windowCount (A ++ [toModelBlock b]) u n.val := by
        apply MoltPetit.Model.windowCount_append_high
        intro x hx
        have := hrest_gt x hx
        omega
      rw [← hwc_rest]
      have hch_app : ch = (A ++ [toModelBlock b]) ++ rest.map toModelBlock := by
        rw [hch_eq, List.append_assoc, List.singleton_append]
      rw [← hch_app]
      exact hDense hAt_b u huB
    have hcore := cert_step_core_be_complete hn hsmall hq hrep htip_h htip_s hb_h hb_s hrest_bound hchild_h hchild_s hchild_prev hdense
    have hMono_sound := MoltPetit.Model.keyMonoOk_sound hMono
    have hle_floor : MoltPetit.Model.keyFloor n.val A (MoltPetit.Model.producerForSlot n.val (toModelBlock b).slot) ≤ (toModelBlock b).keyIndex := by
      rw [keyFloor_le_iff]
      intro B hB hprod
      rcases List.mem_iff_getElem.mp hB with ⟨k, hk_lt, hk_get⟩
      have hAt_B : MoltPetit.Model.blockAt? ch k = some B := by
        unfold MoltPetit.Model.blockAt?
        rw [hch_eq, List.getElem?_append_left hk_lt, List.getElem?_eq_getElem hk_lt, hk_get]
      have hk_le : k ≤ A.length := by omega
      exact hMono_sound hAt_B hAt_b hk_le hprod
    have hle : floorsFun fl (b.slot.val % n.val) ≤ b.key_index.val := by
      rw [hfun]
      change MoltPetit.Model.keyFloor n.val A (MoltPetit.Model.producerForSlot n.val (toModelBlock b).slot) ≤ (toModelBlock b).keyIndex
      exact hle_floor
    have hk_step := cert_step_k_be_complete hn hsmall hb_s hlen hcore hle
    obtain ⟨t', ht'⟩ : ∃ t', cert_next_tail_be UB () st.tail b.slot = ok t' := ⟨_, cert_next_tail_be_corr _ _⟩
    obtain ⟨fl', hfl'⟩ := cert_next_floors_be_complete b hn hlen hsmall
    have hrep' := cert_next_tail_be_repr b hq hn hrep hcore ht'
    have hcl_eq : modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock ++ [toModelBlock b]) =
        { tipId := (toModelBlock b).id,
          tipSlot := (toModelBlock b).slot,
          tipHeight := (toModelBlock b).height,
          tail := (cl.tail ++ [toModelBlock b]).filter
            fun x => decide ((toModelBlock b).slot + 2 - n.val ≤ x.slot) } :=
      modelClaimOf_step_lt n.val (toModelBlock G) (pre.map toModelBlock) (toModelBlock b) hchild_s
    have hmap_app : (pre ++ [b]).map toModelBlock = pre.map toModelBlock ++ [toModelBlock b] := by simp
    have hrep_step : TailRepr n.val (stepState b t')
        (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock)) := by
      rw [hmap_app, hcl_eq]
      exact hrep'
    have hrest_bound_step := entrySlots_cert_next_tail_bound hrest_bound hb_s ht'
    have ⟨hlen', hfun'⟩ := cert_next_floors_be_sound hn hlen hfl'
    have hfun_step : floorsFun fl' = MoltPetit.Model.keyFloor n.val ((G :: (pre ++ [b])).map toModelBlock) := by
      rw [hfun']
      have hA_app : (G :: (pre ++ [b])).map toModelBlock = A ++ [toModelBlock b] := by
        dsimp [A]
        simp
      rw [hA_app]
      funext i
      rw [keyFloor_snoc, hfun]
    have hassoc : G :: (pre ++ [b]) ++ rest = G :: pre ++ b :: rest := by
      simp
    have hbound' : ∀ x ∈ G :: (pre ++ [b]) ++ rest, x.slot.val < 2 ^ 62 ∧ x.height.val < 2 ^ 62 := by
      rw [hassoc]; exact hbound
    have hV' : MoltPetit.Model.validChain n.val ((G :: (pre ++ [b]) ++ rest).map toModelBlock) = true := by
      rw [hassoc]; exact hV
    have hMono' : MoltPetit.Model.keyMonoOk n.val ((G :: (pre ++ [b]) ++ rest).map toModelBlock) = true := by
      rw [hassoc]; exact hMono
    obtain ⟨out, hrest_fold⟩ := ih (pre ++ [b]) (stepState b t') fl' hbound' hV' hMono' hrep_step hrest_bound_step hlen' hfun_step
    exact ⟨out, hk_step, t', fl', ht', hfl', hrest_fold⟩

theorem cert_fold_k_complete : MoltPaper.thm_cert_fold_k_complete := by
  intro n q G bs hn hsmall hq hbound hG hV
  have hbase_rep : TailRepr n.val (genesisState n.val G)
      (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock)) := by
    simp only [List.map_nil]
    exact tailRepr_genesisState n.val G
  have hbase_tail_bound : ∀ s ∈ entrySlots (genesisState n.val G).tail, s < 2 ^ 62 := by
    dsimp [genesisState]
    have hG_bound := hbound G (by simp)
    exact entrySlots_initTail_bound hG_bound.1
  have hbound' : ∀ b ∈ G :: [] ++ bs, b.slot.val < 2 ^ 62 ∧ b.height.val < 2 ^ 62 := by
    intro b hb
    apply hbound
    simp only [List.cons_append, List.nil_append] at hb
    exact hb
  dsimp [MoltPetit.Model.validChainK] at hV
  simp only [Bool.and_eq_true] at hV
  obtain ⟨hV_chain, hV_mono⟩ := hV
  have hV' : MoltPetit.Model.validChain n.val ((G :: [] ++ bs).map toModelBlock) = true := by
    have : (G :: [] ++ bs) = G :: bs := by simp only [List.cons_append, List.nil_append]
    rw [this]
    exact hV_chain
  have hMono' : MoltPetit.Model.keyMonoOk n.val ((G :: [] ++ bs).map toModelBlock) = true := by
    have : (G :: [] ++ bs) = G :: bs := by simp only [List.cons_append, List.nil_append]
    rw [this]
    exact hV_mono
  have hlen0 : floorsLen (initFloors n.val G.key_index) = n.val :=
    floorsLen_initFloors n.val G.key_index
  have ⟨_, hslot0⟩ := cert_genesis_ok_be_sound hG
  have hfun0 : floorsFun (initFloors n.val G.key_index) =
      MoltPetit.Model.keyFloor n.val ((G :: []).map toModelBlock) := by
    have hinit := floorsFun_initFloors n.val hn G.key_index
    rw [hinit]
    have hmap : (G :: []).map toModelBlock = [toModelBlock G] := rfl
    rw [hmap]
    have hslot0_m : (toModelBlock G).slot = 0 := hslot0
    have hfloor_sing := keyFloor_singleton n.val (toModelBlock G) hslot0_m hn
    rw [hfloor_sing]
    have hki : (toModelBlock G).keyIndex = G.key_index.val := rfl
    rw [hki]
  exact foldK_complete_aux hn hsmall hq bs [] (genesisState n.val G) (initFloors n.val G.key_index)
    hbound' hV' hMono' hbase_rep hbase_tail_bound hlen0 hfun0


/-! ## Step 9: Decoding -/

theorem u64_sub_ok {x y : U64} (h : y.val ≤ x.val) :
    ∃ z : U64, x - y = ok z ∧ z.val = x.val - y.val := by
  have hsub := UScalar.sub_equiv x y
  cases hxy : x - y with
  | ok z =>
    rw [hxy] at hsub
    exact ⟨z, rfl, by omega⟩
  | fail e =>
    rw [hxy] at hsub
    omega
  | div =>
    rw [hxy] at hsub
    exact False.elim hsub

theorem tail_of_buffer_corr : ∀ (t : TailG U64) (lo : U64) {c : molt_petit.Chain},
    molt_petit.tail_of_buffer t lo = ok c →
    (toModelChain c).map (·.slot) = (tailSlots t).filter (fun s => decide (lo.val ≤ s)) := by
  intro t
  induction t with
  | TNil =>
    intro lo c h
    rw [molt_petit.tail_of_buffer] at h
    injection h with h; subst h
    rfl
  | TCons f s tl ih =>
    intro lo c h
    rw [molt_petit.tail_of_buffer] at h
    obtain ⟨rest, hrest, h⟩ := molt_petit.bind_inv h
    have ih' := ih lo hrest
    by_cases hf : f = 1#u64
    · have hf_val : f.val = 1 := by rw [hf]; rfl
      have hts : tailSlots (.TCons f s tl) = s.val :: tailSlots tl := by
        simp [tailSlots, hf_val]
      rw [hts]
      simp only [hf, ite_true] at h
      by_cases hlo : lo ≤ s
      · have hlo_val : lo.val ≤ s.val := by scalar_tac
        have hdec : decide (lo.val ≤ s.val) = true := decide_eq_true hlo_val
        simp only [hlo, ite_true] at h
        injection h with hc; subst c
        simp only [toModelChain, toModelBlock, List.map_cons]
        rw [ih']
        simp [hdec]
      · have hlo_val : ¬(lo.val ≤ s.val) := by
          intro hle
          have : lo ≤ s := by scalar_tac
          contradiction
        have hdec : decide (lo.val ≤ s.val) = false := decide_eq_false hlo_val
        simp only [hlo, ite_false] at h
        injection h with hc; subst c
        rw [ih']
        simp [hdec]
    · have hf_val : f.val ≠ 1 := by
        intro heq
        apply hf
        exact UScalar.val_eq_imp _ _ heq
      have hts : tailSlots (.TCons f s tl) = tailSlots tl := by
        simp [tailSlots, hf_val]
      rw [hts]
      simp only [hf, ite_false] at h
      injection h with hc; subst c
      rw [ih']

theorem tail_of_buffer_total : ∀ (t : TailG U64) (lo : U64),
    ∃ c, molt_petit.tail_of_buffer t lo = ok c := by
  intro t
  induction t with
  | TNil =>
    intro lo
    refine ⟨.Nil, ?_⟩
    rw [molt_petit.tail_of_buffer]
  | TCons f s tl ih =>
    intro lo
    obtain ⟨rest, hrest⟩ := ih lo
    rw [molt_petit.tail_of_buffer, hrest]
    simp only [bind_tc_ok]
    by_cases hf : f = 1#u64
    · simp only [hf, ite_true]
      by_cases hlo : lo ≤ s
      · simp only [hlo, ite_true]
        exact ⟨_, rfl⟩
      · simp only [hlo, ite_false]
        exact ⟨_, rfl⟩
    · simp only [hf, ite_false]
      exact ⟨_, rfl⟩

theorem suffix_lo_total (n tip_slot : U64) (h : tip_slot.val + 2 < 2 ^ 64) :
    ∃ lo : U64, molt_petit.suffix_lo n tip_slot = ok lo := by
  obtain ⟨i, hi, hival⟩ := u64_add_ok (x := tip_slot) (y := 2#u64) h
  rw [molt_petit.suffix_lo, hi]
  simp only [bind_tc_ok]
  by_cases hni : i < n
  · simp only [hni, ite_true]
    exact ⟨0#u64, rfl⟩
  · simp only [hni, ite_false]
    have hle : n.val ≤ i.val := by
      by_contra hc
      have : i < n := by scalar_tac
      exact hni this
    obtain ⟨lo, hlo, _⟩ := u64_sub_ok hle
    rw [hlo]
    exact ⟨lo, rfl⟩

theorem claim_of_state_sound {n : U64} {st : CertStateG U64} {cl : molt_petit.CertClaim}
    (hcl : molt_petit.claim_of_state n st = ok cl) :
    MoltPetit.Model.claimView (toModelClaim cl) = stateView n.val st := by
  rw [molt_petit.claim_of_state] at hcl
  obtain ⟨lo, hlo, hcl⟩ := molt_petit.bind_inv hcl
  obtain ⟨c, hc, hcl⟩ := molt_petit.bind_inv hcl
  injection hcl with hcl
  subst cl
  have hlov : lo.val = st.tip_slot.val + 2 - n.val := suffix_lo_val hlo
  have hcorr := tail_of_buffer_corr st.tail lo hc
  dsimp [toModelClaim, MoltPetit.Model.claimView, stateView]
  have hhash : hashToNat
      { a := st.tip_id.a, b := st.tip_id.b, c := st.tip_id.c, d := st.tip_id.d } =
      hashGToNat st.tip_id := rfl
  rw [hhash]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
  dsimp
  rw [hcorr, hlov]

theorem claim_of_state_total (n : U64) (st : CertStateG U64) (h : st.tip_slot.val + 2 < 2 ^ 64) :
    ∃ cl, molt_petit.claim_of_state n st = ok cl := by
  obtain ⟨lo, hlo⟩ := suffix_lo_total n st.tip_slot h
  obtain ⟨c, hc⟩ := tail_of_buffer_total st.tail lo
  rw [molt_petit.claim_of_state, hlo]
  simp only [bind_tc_ok]
  rw [hc]
  simp only [bind_tc_ok]
  exact ⟨_, rfl⟩



theorem windowCount_append_eq_of_tail_map_slot {t₁ t₂ s : List MoltPetit.Model.Block}
    (h : t₁.map (·.slot) = t₂.map (·.slot)) (u n : Nat) :
    MoltPetit.Model.windowCount (t₁ ++ s) u n = MoltPetit.Model.windowCount (t₂ ++ s) u n :=
  windowCount_append_eq_of_map_slot h u n

/-- **View transport for suffix validator**:
If `validate_suffix` accepts `.Cons s1 tl` against `cl`, and `claimView cl₀ = claimView (toModelClaim cl)`,
then the linking and density hypotheses hold against `cl₀` for `toModelBlock s1 :: toModelChain tl`. -/
theorem validate_suffix_sound_view {n : U64} {cl : molt_petit.CertClaim}
    {cl₀ : MoltPetit.Model.CertClaim}
    {s1 : molt_petit.Block} {tl : molt_petit.Chain} {sTip : MoltPetit.Model.Block}
    (hTipS : (toModelBlock s1 :: toModelChain tl).getLast? = some sTip)
    (h : molt_petit.validate_suffix n cl (.Cons s1 tl) = ok true)
    (hcv : MoltPetit.Model.claimView cl₀ = MoltPetit.Model.claimView (toModelClaim cl)) :
    ((toModelBlock s1).height = cl₀.tipHeight + 1 ∧
     cl₀.tipSlot < (toModelBlock s1).slot ∧
     (toModelBlock s1).prev = some cl₀.tipId) ∧
    MoltPetit.Model.linksOk (toModelBlock s1 :: toModelChain tl) = true ∧
    (∀ u : Nat, (cl₀.tipSlot : Int) + 2 - n.val ≤ (u : Int) →
        u + n.val ≤ sTip.slot + 1 →
        MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount
          (cl₀.tail ++ toModelBlock s1 :: toModelChain tl) u n.val) := by
  have h_tipId : cl₀.tipId = (toModelClaim cl).tipId := congrArg (fun v => v.1) hcv
  have h_tipSlot : cl₀.tipSlot = (toModelClaim cl).tipSlot := congrArg (fun v => v.2.1) hcv
  have h_tipHeight : cl₀.tipHeight = (toModelClaim cl).tipHeight := congrArg (fun v => v.2.2.1) hcv
  have h_tail : cl₀.tail.map (·.slot) = (toModelClaim cl).tail.map (·.slot) := congrArg (fun v => v.2.2.2) hcv
  obtain ⟨⟨hh, hs, hp⟩, hlinks, hdense⟩ := validate_suffix_sound hTipS h
  refine ⟨⟨?_, ?_, ?_⟩, hlinks, ?_⟩
  · rw [h_tipHeight]; exact hh
  · rw [h_tipSlot]; exact hs
  · rw [h_tipId]; exact hp
  · intro u hu1 hu2
    rw [h_tipSlot] at hu1
    have hq_le := hdense u hu1 hu2
    rw [windowCount_append_eq_of_map_slot h_tail]
    exact hq_le

/-- **View transport for suffix validator (general chain formulation)**:
If `validate_suffix` accepts `tl` against `cl` where `toModelChain tl = s1 :: srest`,
and `claimView cl₀ = claimView (toModelClaim cl)`,
then the linking and density hypotheses hold against `cl₀` for `s1 :: srest`. -/
theorem validate_suffix_sound_view_of_toModelChain {n : U64} {cl : molt_petit.CertClaim}
    {cl₀ : MoltPetit.Model.CertClaim}
    {tl : molt_petit.Chain} {s1 : MoltPetit.Model.Block} {srest : MoltPetit.Model.Chain}
    {sTip : MoltPetit.Model.Block}
    (hChain : toModelChain tl = s1 :: srest)
    (hTipS : (s1 :: srest).getLast? = some sTip)
    (h : molt_petit.validate_suffix n cl tl = ok true)
    (hcv : MoltPetit.Model.claimView cl₀ = MoltPetit.Model.claimView (toModelClaim cl)) :
    (s1.height = cl₀.tipHeight + 1 ∧
     cl₀.tipSlot < s1.slot ∧
     s1.prev = some cl₀.tipId) ∧
    MoltPetit.Model.linksOk (s1 :: srest) = true ∧
    (∀ u : Nat, (cl₀.tipSlot : Int) + 2 - n.val ≤ (u : Int) →
        u + n.val ≤ sTip.slot + 1 →
        MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount
          (cl₀.tail ++ s1 :: srest) u n.val) := by
  cases tl with
  | Nil =>
    simp [toModelChain] at hChain
  | Cons b tl' =>
    simp only [toModelChain, List.cons.injEq] at hChain
    obtain ⟨rfl, rfl⟩ := hChain
    exact validate_suffix_sound_view hTipS h hcv

/-! ## Step 11: Per-block checks and validator unfolding -/

/-- Div helper: `x / y = ok z` entails non-zero divisor and integer division. -/
theorem u64_div_ok {x y z : U64} (h : x / y = ok z) :
    y.val ≠ 0 ∧ z.val = x.val / y.val := by
  have hnz : y.val ≠ 0 := by
    intro hy0
    dsimp [HDiv.hDiv, UScalar.div] at h
    have : y.bv = 0 := by
      apply BitVec.eq_of_toNat_eq
      simp [hy0]
    simp [this] at h
  have ⟨z', hz', hzv⟩ := UScalar.div_spec x hnz
  rw [hz'] at h
  injection h with h
  subst z'
  exact ⟨hnz, hzv⟩

/-- A passing `sigs_ok` on `SCons b s rest` gives `SigOn` and `sigs_ok rest`. -/
theorem sigs_ok_cons {C} {I : Crypto C} {n : U64} {crypto : C}
    {b : Block} {s : Hash} {rest : SignedChain}
    (h : sigs_ok I n crypto (SignedChain.SCons b s rest) = ok true) :
    SigOn I crypto n b s ∧ sigs_ok I n crypto rest = ok true := by
  rw [sigs_ok] at h
  obtain ⟨i, hi, h⟩ := bind_inv h
  obtain ⟨key, hkey, h⟩ := bind_inv h
  obtain ⟨vb, hvb, h⟩ := bind_inv h
  split at h
  · rename_i hvbt
    rw [hvbt] at hvb
    exact ⟨⟨i, key, hi, hkey, hvb⟩, h⟩
  · simp at h

/-- Signature verification implies the projected model block is `RustSigned`. -/
theorem rustSigned_of_sigOn {C} {I : Crypto C} {crypto : C} {n : U64}
    {b : Block} {s : Hash}
    (h : SigOn I crypto n b s) :
    RustSigned I crypto n (toModelBlock b) := by
  obtain ⟨i, key, hi, hkey, hver⟩ := h
  exact ⟨b, i, key, s, rfl, hi, hkey, hver⟩

/-- Consecutive blocks of `tl` link backwards, starting from `prevId`. -/
def ChainLinks (prevId : Hash) : molt_petit.Chain → Prop
  | .Nil => True
  | .Cons b tl => b.prev = some prevId ∧ ChainLinks b.id tl

theorem chainLinks_of_linksOk {s1 : Block} {tipId : Hash} :
    ∀ (tl_sub : molt_petit.Chain),
    s1.prev = some tipId →
    MoltPetit.Model.linksOk (toModelBlock s1 :: toModelChain tl_sub) = true →
    ChainLinks tipId (molt_petit.Chain.Cons s1 tl_sub)
  | molt_petit.Chain.Nil, hprev, _ => ⟨hprev, trivial⟩
  | molt_petit.Chain.Cons s2 rest, hprev, hlinks => by
    refine ⟨hprev, ?_⟩
    rw [toModelChain_cons, MoltPetit.Model.linksOk, Bool.and_eq_true] at hlinks
    obtain ⟨hchild, hrest⟩ := hlinks
    rw [MoltPetit.Model.childOk, decide_eq_true_eq] at hchild
    obtain ⟨_, _, hp⟩ := hchild
    cases hs2_prev : s2.prev with
    | none =>
      simp [toModelBlock, hs2_prev] at hp
    | some p =>
      simp [toModelBlock, hs2_prev] at hp
      have hp_eq : p = s1.id := hashToNat_inj hp
      subst hp_eq
      exact chainLinks_of_linksOk rest hs2_prev hrest

theorem chainLinks_of_toModel_linksOk {s1 : Block} {tipId : Hash} (tl_sub : molt_petit.Chain)
    (hprev : (toModelBlock s1).prev = some (hashToNat tipId))
    (hlinks : MoltPetit.Model.linksOk (toModelBlock s1 :: toModelChain tl_sub) = true) :
    ChainLinks tipId (molt_petit.Chain.Cons s1 tl_sub) := by
  have hp : s1.prev = some tipId := by
    cases hs : s1.prev with
    | none => simp [toModelBlock, hs] at hprev
    | some p =>
      simp [toModelBlock, hs] at hprev
      exact congrArg some (hashToNat_inj hprev)
  exact chainLinks_of_linksOk tl_sub hp hlinks

/-- A passing `ids_ok` on a linked chain makes every block of the model chain `RustFormed`. -/
theorem ids_ok_formed {C} {I : CryptoD C} {crypto : C} {n : U64} {G : Block} :
    ∀ (T : Block) (ts : Hash) (sc : molt_petit.SignedChain) (tl : molt_petit.Chain),
    FormedFrom I crypto n G T →
    SigOn I.CryptoInst crypto n T ts →
    molt_petit.strip_sigs sc = ok tl →
    molt_petit.sigs_ok I.CryptoInst n crypto sc = ok true →
    molt_petit.ids_ok I crypto (some ts) sc = ok true →
    ChainLinks T.id tl →
    ∀ B ∈ toModelChain tl, RustFormed I crypto n G B := by
  intro T ts sc
  induction sc generalizing T ts with
  | SNil =>
    intro tl hT hSigT hstrip hsig hids hlinks B hB
    rw [molt_petit.strip_sigs] at hstrip
    injection hstrip with hstrip; subst hstrip
    simp [toModelChain] at hB
  | SCons b s rest ih =>
    intro tl hT hSigT hstrip hsig hids hlinks B hB
    rw [molt_petit.strip_sigs] at hstrip
    obtain ⟨c, hc, hstrip⟩ := molt_petit.bind_inv hstrip
    injection hstrip with hstrip; subst hstrip
    dsimp [ChainLinks] at hlinks
    obtain ⟨hprev, hlinks_c⟩ := hlinks
    obtain ⟨hSig_b, hsig_rest⟩ := sigs_ok_cons hsig
    rw [molt_petit.ids_ok.eq_def] at hids
    obtain ⟨id, hid, h1⟩ := molt_petit.bind_inv hids
    obtain ⟨b1, hb1, h2⟩ := molt_petit.bind_inv h1
    split at h2
    · rename_i hb1t
      rw [hb1t] at hb1
      have heq := hash_eq_sound hb1
      rw [heq] at hid
      have hb_formed : FormedFrom I crypto n G b :=
        FormedFrom.step hT hSigT hprev hid
      rw [toModelChain_cons] at hB
      rcases List.mem_cons.mp hB with rfl | hBtl
      · exact ⟨b, rfl, hb_formed⟩
      · exact ih b s c hb_formed hSig_b hc hsig_rest h2 hlinks_c B hBtl
    · simp at h2

/-- A passing `recent_ok` gives `now ≤ tip + delta`. -/
theorem recent_ok_sound {now delta tip : U64}
    (h : molt_petit.recent_ok now delta tip = ok true) :
    now.val ≤ tip.val + delta.val := by
  rw [molt_petit.recent_ok] at h
  split_ifs at h with hle
  · have hle_val : now.val ≤ tip.val := by scalar_tac
    omega
  · obtain ⟨i, hi, h⟩ := molt_petit.bind_inv h
    have hsub := UScalar.sub_equiv now tip
    rw [hi] at hsub
    have hiv : i.val = now.val - tip.val := by omega
    clear hsub
    injection h with h
    have hle_delta : i.val ≤ delta.val := of_decide_eq_true h
    omega

/-- Suffix blocks with valid signatures and ids are `DSigned`. -/
theorem dsigned_of_sigs_ok_ids_ok {C} {I : CryptoD C} {n : U64} {crypto : C}
    {G T : Block} {ts : Hash}
    {sc : molt_petit.SignedChain} {stripped : molt_petit.Chain}
    (hT : FormedFrom I crypto n G T)
    (hSigT : SigOn I.CryptoInst crypto n T ts)
    (hsig : molt_petit.sigs_ok I.CryptoInst n crypto sc = ok true)
    (hstrip : molt_petit.strip_sigs sc = ok stripped)
    (hids : molt_petit.ids_ok I crypto (some ts) sc = ok true)
    (hlinks : ChainLinks T.id stripped) :
    ∀ B ∈ toModelChain stripped, DSigned I crypto n G B := by
  intro B hB
  exact ⟨sigs_ok_signed sc hsig hstrip B hB,
         ids_ok_formed T ts sc stripped hT hSigT hstrip hsig hids hlinks B hB⟩


/-- Soundness of the predecessor check in `cert_step_core_be`. -/
theorem cert_step_core_be_prev {n q : U64} {st : CertStateG U64} {b : molt_petit.Block} {T : molt_petit.Block}
    (hst : st.tip_id = toHashG T.id)
    (h : cert_step_core_be UBK () n q st (toBlockG b) = ok true) :
    b.prev = some T.id := by
  dsimp [cert_step_core_be, U64Backend.Insts.Molt_petitBackendU64Bool.and] at h
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
    split at hlinks
    · rename_i ht1_t
      injection hlinks with hlinks; subst hlinks
      subst ht1_t
      split at hprev_ok
      · rename_i hhas_t
        injection hprev_ok with hprev_ok; subst hprev_ok
        subst hhas_t
        injection hhas with hhas
        cases hp : b.prev with
        | none =>
          dsimp [toBlockG] at hhas
          rw [hp] at hhas
          simp at hhas
        | some p =>
          dsimp [toBlockG] at hprev_eq
          rw [hp, hst] at hprev_eq
          rw [hashg_eq_eq] at hprev_eq
          have hpeq := hash_eq_sound hprev_eq
          rw [hpeq]
      · simp at hprev_ok
    · simp at hlinks
  · simp at h

/-- `cert_step_k_be` entails `cert_step_core_be`. -/
theorem cert_step_k_be_core {n q : U64} {st : CertStateG U64} {fl : FloorsG U64}
    {b : molt_petit.Block} {ki : U64}
    (h : cert_step_k_be UBK () n q st fl (toBlockG b) ki = ok true) :
    cert_step_core_be UBK () n q st (toBlockG b) = ok true := by
  dsimp [cert_step_k_be, U64Backend.Insts.Molt_petitBackendU64Bool.and] at h
  obtain ⟨core, hcore, h⟩ := bind_inv h
  obtain ⟨p, hp, h⟩ := bind_inv h
  obtain ⟨t, ht, h⟩ := bind_inv h
  obtain ⟨fl_ok, hfl_ok, h⟩ := bind_inv h
  split at h
  · rename_i hcore_t
    injection h with h; subst h
    rw [hcore_t] at hcore
    exact hcore
  · simp at h

/-- `cert_step_sched_be` entails `cert_step_core_be`. -/
theorem cert_step_sched_be_core {n q era : U64} {st : CertStateG U64}
    {b : molt_petit.Block} {ki : U64}
    (h : cert_step_sched_be UBK () n q era st (toBlockG b) ki = ok true) :
    cert_step_core_be UBK () n q st (toBlockG b) = ok true := by
  dsimp [cert_step_sched_be, U64Backend.Insts.Molt_petitBackendU64Bool.and] at h
  obtain ⟨core, hcore, h⟩ := bind_inv h
  obtain ⟨gen, hgen, h⟩ := bind_inv h
  obtain ⟨below, hbelow, h⟩ := bind_inv h
  obtain ⟨pinned, hpinned, h⟩ := bind_inv h
  split at h
  · rename_i hcore_t
    injection h with h; subst h
    rw [hcore_t] at hcore
    exact hcore
  · simp at h

/-- `cert_step_lock_be` entails `cert_step_core_be`. -/
theorem cert_step_lock_be_core {n q : U64} {st : CertStateG U64} {g : U64}
    {b : molt_petit.Block} {ki : U64}
    (h : cert_step_lock_be UBK () n q st g (toBlockG b) ki = ok true) :
    cert_step_core_be UBK () n q st (toBlockG b) = ok true := by
  dsimp [cert_step_lock_be, U64Backend.Insts.Molt_petitBackendU64Bool.and] at h
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
    exact hcore
  · simp at h

/-- A core fold step sequence: each step passes `cert_step_core_be`. -/
def FoldCoreOut (n q : U64) : CertStateG U64 → List Block → CertStateG U64 → Prop
  | st, [], stO => stO = st
  | st, b :: bs, stO =>
      cert_step_core_be UBK () n q st (toBlockG b) = ok true ∧
      ∃ t', FoldCoreOut n q (stepState b t') bs stO

/-- `FoldKOut` implies `FoldCoreOut`. -/
theorem foldKOut_to_core {n q : U64} :
    ∀ {st fl bs stO out},
    FoldKOut n q st fl bs stO out → FoldCoreOut n q st bs stO := by
  intro st fl bs
  induction bs generalizing st fl with
  | nil =>
    intro stO out h
    dsimp [FoldKOut] at h
    dsimp [FoldCoreOut]
    exact h.1
  | cons b rest ih =>
    intro stO out h
    dsimp [FoldKOut] at h
    obtain ⟨hstep, t', fl', ht', hfl', hrest⟩ := h
    dsimp [FoldCoreOut]
    refine ⟨cert_step_k_be_core hstep, t', ih hrest⟩

/-- `FoldSchedOut` implies `FoldCoreOut`. -/
theorem foldSchedOut_to_core {n q era : U64} :
    ∀ {st bs stO},
    FoldSchedOut n q era st bs stO → FoldCoreOut n q st bs stO := by
  intro st bs
  induction bs generalizing st with
  | nil =>
    intro stO h
    dsimp [FoldSchedOut] at h
    dsimp [FoldCoreOut]
    exact h
  | cons b rest ih =>
    intro stO h
    dsimp [FoldSchedOut] at h
    obtain ⟨hstep, t', ht', hrest⟩ := h
    dsimp [FoldCoreOut]
    refine ⟨cert_step_sched_be_core hstep, t', ih hrest⟩

/-- `FoldLockOut` implies `FoldCoreOut`. -/
theorem foldLockOut_to_core {n q : U64} :
    ∀ {st g bs stO gO},
    FoldLockOut n q st g bs stO gO → FoldCoreOut n q st bs stO := by
  intro st g bs
  induction bs generalizing st g with
  | nil =>
    intro stO gO h
    dsimp [FoldLockOut] at h
    dsimp [FoldCoreOut]
    exact h.1
  | cons b rest ih =>
    intro stO gO h
    dsimp [FoldLockOut] at h
    obtain ⟨hstep, t', ht', hrest⟩ := h
    dsimp [FoldCoreOut]
    refine ⟨cert_step_lock_be_core hstep, t', ih hrest⟩

/-- Soundness of history formedness along `FoldCoreOut`:
generalized induction on `bs : List (Block × Hash)`. -/
lemma foldCoreOut_history_formed_aux {C} {I : CryptoD C} {crypto : C} {n q : U64} {G : Block} :
    ∀ (bs : List (Block × Hash)) (T : Block) (sT : Hash) (st : CertStateG U64)
      (stO : CertStateG U64) (ts : Hash),
    FormedFrom I crypto n G T →
    SigOn I.CryptoInst crypto n T sT →
    st.tip_id = toHashG T.id →
    st.tip_slot = T.slot →
    st.tip_height = T.height →
    SigHist I crypto n sT bs ts →
    FoldCoreOut n q st (bs.map Prod.fst) stO →
    (∀ b ∈ bs.map Prod.fst, FormedFrom I crypto n G b) ∧
    ∃ T' : Block,
      FormedFrom I crypto n G T' ∧
      SigOn I.CryptoInst crypto n T' ts ∧
      stO.tip_id = toHashG T'.id ∧
      stO.tip_slot = T'.slot ∧
      stO.tip_height = T'.height := by
  intro bs
  induction bs with
  | nil =>
    intro T sT st stO ts hT hSigT hst_id hst_slot hst_height hSigHist hFold
    dsimp [SigHist] at hSigHist
    subst hSigHist
    dsimp [FoldCoreOut] at hFold
    subst hFold
    refine ⟨by simp, ⟨T, hT, hSigT, hst_id, hst_slot, hst_height⟩⟩
  | cons pair rest ih =>
    obtain ⟨b, s⟩ := pair
    intro T sT st stO ts hT hSigT hst_id hst_slot hst_height hSigHist hFold
    dsimp [List.map] at hFold
    dsimp [FoldCoreOut] at hFold
    obtain ⟨hstep, t', hfold_rest⟩ := hFold
    dsimp [SigHist] at hSigHist
    obtain ⟨hSig_b, hid_b, hSigHist_rest⟩ := hSigHist
    have hprev := cert_step_core_be_prev hst_id hstep
    have hb_formed : FormedFrom I crypto n G b :=
      FormedFrom.step hT hSigT hprev hid_b
    have hst'_id : (stepState b t').tip_id = toHashG b.id := rfl
    have hst'_slot : (stepState b t').tip_slot = b.slot := rfl
    have hst'_height : (stepState b t').tip_height = b.height := rfl
    have ⟨hrest_formed, T', hT'_formed, hT'_sig, hstO_id, hstO_slot, hstO_height⟩ :=
      ih b s (stepState b t') stO ts hb_formed hSig_b hst'_id hst'_slot hst'_height hSigHist_rest hfold_rest
    refine ⟨?_, ⟨T', hT'_formed, hT'_sig, hstO_id, hstO_slot, hstO_height⟩⟩
    intro x hx
    simp only [List.map_cons, Prod.fst, List.mem_cons] at hx
    rcases hx with rfl | hx_rest
    · exact hb_formed
    · exact hrest_formed x hx_rest

/-- History formedness starting from the genesis state. -/
theorem foldCoreOut_history_formed {C} {I : CryptoD C} {crypto : C} {n q : U64} {G : Block} {sG : Hash}
    {bs : List (Block × Hash)} {stO : CertStateG U64} {ts : Hash}
    (hSigG : SigOn I.CryptoInst crypto n G sG)
    (hSig : SigHist I crypto n sG bs ts)
    (hFold : FoldCoreOut n q (genesisState n.val G) (bs.map Prod.fst) stO) :
    (∀ b ∈ G :: bs.map Prod.fst, FormedFrom I crypto n G b) ∧
    ∃ T : Block,
      FormedFrom I crypto n G T ∧
      SigOn I.CryptoInst crypto n T ts ∧
      stO.tip_id = toHashG T.id ∧
      stO.tip_slot = T.slot ∧
      stO.tip_height = T.height := by
  have hgen : FormedFrom I crypto n G G := FormedFrom.genesis
  have ⟨hbs, hT⟩ := foldCoreOut_history_formed_aux bs G sG (genesisState n.val G) stO ts
    hgen hSigG rfl rfl rfl hSig hFold
  refine ⟨?_, hT⟩
  intro b hb
  simp only [List.mem_cons] at hb
  rcases hb with rfl | hb_rest
  · exact hgen
  · exact hbs b hb_rest

/-- History formedness for mode 1 (`FoldKOut`). -/
theorem foldKOut_history_formed {C} {I : CryptoD C} {crypto : C} {n q : U64} {G : Block} {sG : Hash}
    {bs : List (Block × Hash)} {stO : CertStateG U64} {out : FloorsG U64} {ts : Hash}
    (hSigG : SigOn I.CryptoInst crypto n G sG)
    (hSig : SigHist I crypto n sG bs ts)
    (hFold : FoldKOut n q (genesisState n.val G) (initFloors n.val G.key_index) (bs.map Prod.fst) stO out) :
    (∀ b ∈ G :: bs.map Prod.fst, FormedFrom I crypto n G b) ∧
    ∃ T : Block,
      FormedFrom I crypto n G T ∧
      SigOn I.CryptoInst crypto n T ts ∧
      stO.tip_id = toHashG T.id ∧
      stO.tip_slot = T.slot ∧
      stO.tip_height = T.height :=
  foldCoreOut_history_formed hSigG hSig (foldKOut_to_core hFold)

/-- History formedness for mode 2 (`FoldSchedOut`). -/
theorem foldSchedOut_history_formed {C} {I : CryptoD C} {crypto : C} {n q era : U64} {G : Block} {sG : Hash}
    {bs : List (Block × Hash)} {stO : CertStateG U64} {ts : Hash}
    (hSigG : SigOn I.CryptoInst crypto n G sG)
    (hSig : SigHist I crypto n sG bs ts)
    (hFold : FoldSchedOut n q era (genesisState n.val G) (bs.map Prod.fst) stO) :
    (∀ b ∈ G :: bs.map Prod.fst, FormedFrom I crypto n G b) ∧
    ∃ T : Block,
      FormedFrom I crypto n G T ∧
      SigOn I.CryptoInst crypto n T ts ∧
      stO.tip_id = toHashG T.id ∧
      stO.tip_slot = T.slot ∧
      stO.tip_height = T.height :=
  foldCoreOut_history_formed hSigG hSig (foldSchedOut_to_core hFold)

/-- History formedness for mode 3 (`FoldLockOut`). -/
theorem foldLockOut_history_formed {C} {I : CryptoD C} {crypto : C} {n q : U64} {G : Block} {sG : Hash}
    {bs : List (Block × Hash)} {stO : CertStateG U64} {gO : U64} {ts : Hash}
    (hSigG : SigOn I.CryptoInst crypto n G sG)
    (hSig : SigHist I crypto n sG bs ts)
    (hFold : FoldLockOut n q (genesisState n.val G) G.key_index (bs.map Prod.fst) stO gO) :
    (∀ b ∈ G :: bs.map Prod.fst, FormedFrom I crypto n G b) ∧
    ∃ T : Block,
      FormedFrom I crypto n G T ∧
      SigOn I.CryptoInst crypto n T ts ∧
      stO.tip_id = toHashG T.id ∧
      stO.tip_slot = T.slot ∧
      stO.tip_height = T.height :=
  foldCoreOut_history_formed hSigG hSig (foldLockOut_to_core hFold)

/-- Blocks in `SigHist` have verifying signatures (`RustSigned`). -/
lemma sigHist_rustSigned {C} {I : CryptoD C} {crypto : C} {n : U64} :
    ∀ (bs : List (Block × Hash)) (ps ts : Hash),
    SigHist I crypto n ps bs ts →
    ∀ b ∈ bs.map Prod.fst, RustSigned I.CryptoInst crypto n (toModelBlock b) := by
  intro bs
  induction bs with
  | nil =>
    intro ps ts _ b hb
    simp only [List.map_nil, List.not_mem_nil] at hb
  | cons pair rest ih =>
    obtain ⟨b, s⟩ := pair
    intro ps ts hSig x hx
    dsimp [SigHist] at hSig
    obtain ⟨hSig_b, _, hSig_rest⟩ := hSig
    simp only [List.map_cons, Prod.fst, List.mem_cons] at hx
    rcases hx with rfl | hx_rest
    · exact rustSigned_of_sigOn hSig_b
    · exact ih s ts hSig_rest x hx_rest

/-- Every block of the attested history `G :: bs.map Prod.fst` is `DSigned`. -/
theorem foldCoreOut_history_dsigned {C} {I : CryptoD C} {crypto : C} {n q : U64} {G : Block} {sG : Hash}
    {bs : List (Block × Hash)} {stO : CertStateG U64} {ts : Hash}
    (hSigG : SigOn I.CryptoInst crypto n G sG)
    (hSig : SigHist I crypto n sG bs ts)
    (hFold : FoldCoreOut n q (genesisState n.val G) (bs.map Prod.fst) stO) :
    ∀ B ∈ (G :: bs.map Prod.fst).map toModelBlock, DSigned I crypto n G B := by
  intro B hB
  simp only [List.map_cons, List.mem_cons] at hB
  have ⟨hformed, _⟩ := foldCoreOut_history_formed hSigG hSig hFold
  rcases hB with rfl | hB_rest
  · refine ⟨rustSigned_of_sigOn hSigG, ⟨G, rfl, FormedFrom.genesis⟩⟩
  · rw [List.mem_map] at hB_rest
    obtain ⟨b, hb, rfl⟩ := hB_rest
    have hsign := sigHist_rustSigned bs sG ts hSig b hb
    have hform := hformed b (by simp [hb])
    exact ⟨hsign, ⟨b, rfl, hform⟩⟩

/-- A passing `sched_pin_ok` gives the model `schedPinned` predicate. -/
theorem sched_pin_ok_sound {era : U64} :
    ∀ (c : molt_petit.Chain),
    molt_petit.sched_pin_ok era c = ok true →
    MoltPetit.Model.schedPinned (fun s => s / era.val) (toModelChain c) = true
  | molt_petit.Chain.Nil, _ => rfl
  | molt_petit.Chain.Cons b tl, h => by
    rw [molt_petit.sched_pin_ok] at h
    split_ifs at h with hera_gt
    · obtain ⟨i, hi, h⟩ := molt_petit.bind_inv h
      have ⟨_, hdiv⟩ := u64_div_ok hi
      split_ifs at h with hle
      · have hle_val : i.val ≤ b.key_index.val := by scalar_tac
        rw [hdiv] at hle_val
        have hpin_b :
            decide ((toModelBlock b).slot / era.val ≤ (toModelBlock b).keyIndex) = true := by
          simp only [toModelBlock, decide_eq_true_eq]; exact hle_val
        have htl := sched_pin_ok_sound tl h
        simp only [toModelChain, MoltPetit.Model.schedPinned, List.all_cons, Bool.and_eq_true]
        exact ⟨hpin_b, htl⟩
      · simp at h
    · simp at h

/-- Non-empty chain passing `sched_pin_ok` entails `0 < era.val`. -/
theorem sched_pin_ok_era {era : U64} {b : molt_petit.Block} {tl : molt_petit.Chain}
    (h : molt_petit.sched_pin_ok era (.Cons b tl) = ok true) :
    0 < era.val := by
  rw [molt_petit.sched_pin_ok] at h
  split_ifs at h with hera_gt
  · scalar_tac
  · simp at h

/-- A passing `lockstep_from` gives the model `lockstepFrom` predicate. -/
theorem lockstep_from_sound {n ts g : U64} :
    ∀ (c : molt_petit.Chain),
    molt_petit.lockstep_from n ts g c = ok true →
    MoltPetit.Model.lockstepFrom n.val ts.val g.val (toModelChain c) = true
  | molt_petit.Chain.Nil, _ => by
    simp [toModelChain, MoltPetit.Model.lockstepFrom]
  | molt_petit.Chain.Cons b tl, h => by
    rw [molt_petit.lockstep_from] at h
    obtain ⟨i, hi, h⟩ := molt_petit.bind_inv h
    obtain ⟨i1, hi1, h⟩ := molt_petit.bind_inv h
    obtain ⟨ok1, hok1, h⟩ := molt_petit.bind_inv h
    have ⟨_, hdiv_i⟩ := u64_div_ok hi
    have ⟨_, hdiv_i1⟩ := u64_div_ok hi1
    split at h
    · rename_i hok1t
      rw [hok1t] at hok1
      by_cases hg_le : g ≤ b.key_index
      · rw [if_pos hg_le] at hok1
        by_cases h_eq : i = i1
        · rw [if_pos h_eq] at hok1
          injection hok1 with heq
          have hg_eq : g = b.key_index := of_decide_eq_true heq
          have hg_val : g.val = b.key_index.val := congrArg UScalar.val hg_eq
          have hg_le_val : g.val ≤ b.key_index.val := by scalar_tac
          have hcond : g.val ≤ (toModelBlock b).keyIndex ∧
              (ts.val / n.val = (toModelBlock b).slot / n.val →
                g.val = (toModelBlock b).keyIndex) := by
            simp only [toModelBlock]
            exact ⟨hg_le_val, fun _ => hg_val⟩
          simp only [toModelChain, MoltPetit.Model.lockstepFrom, Bool.and_eq_true]
          refine ⟨decide_eq_true hcond, ?_⟩
          exact lockstep_from_sound tl h
        · rw [if_neg h_eq] at hok1
          injection hok1 with heq
          have hg_le_val : g.val ≤ b.key_index.val := by scalar_tac
          have hcond : g.val ≤ (toModelBlock b).keyIndex ∧
              (ts.val / n.val = (toModelBlock b).slot / n.val →
                g.val = (toModelBlock b).keyIndex) := by
            simp only [toModelBlock]
            refine ⟨hg_le_val, fun hdiv_eq => ?_⟩
            have hi_val_eq : i.val = i1.val := by rw [hdiv_i, hdiv_i1, hdiv_eq]
            have : i = i1 := UScalar.eq_of_val_eq hi_val_eq
            exact False.elim (h_eq this)
          simp only [toModelChain, MoltPetit.Model.lockstepFrom, Bool.and_eq_true]
          refine ⟨decide_eq_true hcond, ?_⟩
          exact lockstep_from_sound tl h
      · rw [if_neg hg_le] at hok1
        injection hok1 with hbad
        contradiction
    · simp at h

/-- `is_nil` returns `ok false` iff the chain is a `Cons`. -/
theorem is_nil_false {c : molt_petit.Chain} (h : molt_petit.is_nil c = ok false) :
    ∃ s1 tl, c = molt_petit.Chain.Cons s1 tl := by
  cases c with
  | Nil =>
    rw [molt_petit.is_nil] at h
    injection h with h
    contradiction
  | Cons s1 tl =>
    exact ⟨s1, tl, rfl⟩

/-- **Deployed validator decomposition**: a passing `validate_deployed` splits into:
  - a verifying certificate state `st`
  - a decoded claim `cl`
  - a non-empty stripped tail `s1 :: tl`
  - passing signatures, ids, suffix validation, and recency check against `tip`. -/
theorem validate_deployed_sound {C} {I : CryptoD C} {n now delta : U64} {crypto : C}
    {cert : Hash} {suffix : molt_petit.SignedChain}
    (h : molt_petit.validate_deployed I n now delta crypto cert suffix = ok true) :
    ∃ (st : CertStateG U64) (cl : molt_petit.CertClaim) (stripped : molt_petit.Chain)
      (tip : U64) (s1 : molt_petit.Block) (tl : molt_petit.Chain) (ts : Hash),
      I.cert_state crypto cert = ok st ∧
      molt_petit.claim_of_state n st = ok cl ∧
      molt_petit.strip_sigs suffix = ok stripped ∧
      stripped = molt_petit.Chain.Cons s1 tl ∧
      molt_petit.tip_slot_from cl.tip_slot stripped = ok tip ∧
      I.CryptoInst.cert_verify crypto cert = ok true ∧
      molt_petit.sigs_ok I.CryptoInst n crypto suffix = ok true ∧
      I.cert_tip_sig crypto cert = ok ts ∧
      molt_petit.ids_ok I crypto (some ts) suffix = ok true ∧
      molt_petit.validate_suffix n cl stripped = ok true ∧
      molt_petit.recent_ok now delta tip = ok true := by
  rw [molt_petit.validate_deployed] at h
  obtain ⟨st, hst, h⟩ := molt_petit.bind_inv h
  obtain ⟨cl, hcl, h⟩ := molt_petit.bind_inv h
  obtain ⟨stripped, hstrip, h⟩ := molt_petit.bind_inv h
  obtain ⟨b, hb, h⟩ := molt_petit.bind_inv h
  obtain ⟨tip, htip, h⟩ := molt_petit.bind_inv h
  obtain ⟨b1, hb1, h⟩ := molt_petit.bind_inv h
  split at h
  · rename_i hb1t; rw [hb1t] at hb1
    split at h
    · rename_i hbn; rw [Bool.not_eq_true] at hbn
      have hb_val : b = false := hbn
      rw [hb_val] at hb
      obtain ⟨s1, tl, hcons⟩ := is_nil_false hb
      obtain ⟨b2, hb2, h⟩ := molt_petit.bind_inv h
      split at h
      · rename_i hb2t; rw [hb2t] at hb2
        obtain ⟨ts, hts, h⟩ := molt_petit.bind_inv h
        obtain ⟨b3, hb3, h⟩ := molt_petit.bind_inv h
        split at h
        · rename_i hb3t; rw [hb3t] at hb3
          obtain ⟨b4, hb4, h⟩ := molt_petit.bind_inv h
          split at h
          · rename_i hb4t; rw [hb4t] at hb4
            exact ⟨st, cl, stripped, tip, s1, tl, ts,
                   hst, hcl, hstrip, hcons, htip, hb1, hb2, hts, hb3, hb4, h⟩
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- **Mode 1 deployed validator decomposition**: splits `validate_deployed_k` into
`validate_deployed` and the key-monotonicity checks. -/
theorem validate_deployed_k_sound {C} {I : CryptoD C} {n now delta : U64} {crypto : C}
    {cert : Hash} {suffix : molt_petit.SignedChain}
    (h : molt_petit.validate_deployed_k I n now delta crypto cert suffix = ok true) :
    molt_petit.validate_deployed I n now delta crypto cert suffix = ok true ∧
    ∃ (fg : FloorsG U64) (fl : FloorList) (stripped : molt_petit.Chain),
      I.cert_floors_state crypto cert = ok fg ∧
      molt_petit.floors_of_state 0#u64 fg = ok fl ∧
      molt_petit.strip_sigs suffix = ok stripped ∧
      molt_petit.floors_shape_ok n fl = ok true ∧
      molt_petit.key_mono_from n fl stripped = ok true := by
  rw [molt_petit.validate_deployed_k] at h
  obtain ⟨fg, hfg, h⟩ := molt_petit.bind_inv h
  obtain ⟨fl, hfl, h⟩ := molt_petit.bind_inv h
  obtain ⟨stripped, hstrip, h⟩ := molt_petit.bind_inv h
  obtain ⟨b, hb, h⟩ := molt_petit.bind_inv h
  split at h
  · rename_i hbt; rw [hbt] at hb
    obtain ⟨b1, hb1, h⟩ := molt_petit.bind_inv h
    split at h
    · rename_i hb1t; rw [hb1t] at hb1
      exact ⟨hb, fg, fl, stripped, hfg, hfl, hstrip, hb1, h⟩
    · simp at h
  · simp at h

/-- **Mode 2 deployed validator decomposition**: splits `validate_deployed_sched` into
`validate_deployed` and `sched_pin_ok`. -/
theorem validate_deployed_sched_sound {C} {I : CryptoD C} {n era now delta : U64} {crypto : C}
    {cert : Hash} {suffix : molt_petit.SignedChain}
    (h : molt_petit.validate_deployed_sched I n era now delta crypto cert suffix = ok true) :
    molt_petit.validate_deployed I n now delta crypto cert suffix = ok true ∧
    ∃ (stripped : molt_petit.Chain),
      molt_petit.strip_sigs suffix = ok stripped ∧
      molt_petit.sched_pin_ok era stripped = ok true := by
  rw [molt_petit.validate_deployed_sched] at h
  obtain ⟨stripped, hstrip, h⟩ := molt_petit.bind_inv h
  obtain ⟨b, hb, h⟩ := molt_petit.bind_inv h
  split at h
  · rename_i hbt; rw [hbt] at hb
    exact ⟨hb, stripped, hstrip, h⟩
  · simp at h

/-- **Mode 3 deployed validator decomposition**: splits `validate_deployed_lock` into
`validate_deployed` and `lockstep_from`. -/
theorem validate_deployed_lock_sound {C} {I : CryptoD C} {n now delta : U64} {crypto : C}
    {cert : Hash} {suffix : molt_petit.SignedChain}
    (h : molt_petit.validate_deployed_lock I n now delta crypto cert suffix = ok true) :
    molt_petit.validate_deployed I n now delta crypto cert suffix = ok true ∧
    ∃ (st : CertStateG U64) (g : U64) (stripped : molt_petit.Chain),
      I.cert_state crypto cert = ok st ∧
      I.cert_gen crypto cert = ok g ∧
      molt_petit.strip_sigs suffix = ok stripped ∧
      molt_petit.lockstep_from n st.tip_slot g stripped = ok true := by
  rw [molt_petit.validate_deployed_lock] at h
  obtain ⟨st, hst, h⟩ := molt_petit.bind_inv h
  obtain ⟨g, hg, h⟩ := molt_petit.bind_inv h
  obtain ⟨stripped, hstrip, h⟩ := molt_petit.bind_inv h
  obtain ⟨b, hb, h⟩ := molt_petit.bind_inv h
  split at h
  · rename_i hbt; rw [hbt] at hb
    exact ⟨hb, st, g, stripped, hst, hg, hstrip, h⟩
  · simp at h


/-! ## Step 12: History reconstruction from Attests -/

lemma groundedCert_of_groundedCertK {n : Nat} {Signed : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    {cl : MoltPetit.Model.CertClaim} {fl : Nat → Nat}
    (h : MoltPetit.Model.GroundedCertK n Signed G cl fl) :
    MoltPetit.Model.GroundedCert n Signed G cl := by
  induction h with
  | genesis hG hSlot _ => exact MoltPetit.Model.GroundedCert.genesis hG hSlot
  | extend cl fl b _ hh hs hp hSig _ hd ih =>
    exact MoltPetit.Model.GroundedCert.extend cl b ih hh hs hp hSig hd

lemma groundedCert_of_groundedCertSched {n : Nat} {schedule : Nat → Nat}
    {Signed : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    {cl : MoltPetit.Model.CertClaim}
    (h : MoltPetit.Model.GroundedCertSched n schedule Signed G cl) :
    MoltPetit.Model.GroundedCert n Signed G cl := by
  induction h with
  | genesis hG hSlot _ _ => exact MoltPetit.Model.GroundedCert.genesis hG hSlot
  | extend cl b _ hh hs hp hSig _ hd ih =>
    exact MoltPetit.Model.GroundedCert.extend cl b ih hh hs hp hSig hd

lemma groundedCert_of_groundedCertLock {n : Nat}
    {Signed : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    {cl : MoltPetit.Model.CertClaim} {g : Nat}
    (h : MoltPetit.Model.GroundedCertLock n Signed G cl g) :
    MoltPetit.Model.GroundedCert n Signed G cl := by
  induction h with
  | genesis hG hSlot _ => exact MoltPetit.Model.GroundedCert.genesis hG hSlot
  | extend cl g b _ hh hs hp hSig _ _ hd ih =>
    exact MoltPetit.Model.GroundedCert.extend cl b ih hh hs hp hSig hd

lemma groundedHistory_of_groundedHistoryK {n : Nat} {Signed : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    {cl : MoltPetit.Model.CertClaim} {fl : Nat → Nat} {c : MoltPetit.Model.Chain}
    (h : MoltPetit.Model.GroundedHistoryK n Signed G cl fl c) :
    MoltPetit.Model.GroundedHistory n Signed G cl c := by
  have hcK := h.valid
  rw [MoltPetit.Model.validChainK, Bool.and_eq_true] at hcK
  exact {
    valid := hcK.1
    head := h.head
    tip := h.tip
    tail_eq := h.tail_eq
    len_eq := h.len_eq
    signed := fun B hB => Or.inr (h.signed B hB)
  }

lemma groundedHistory_of_groundedHistorySched {n : Nat} {schedule : Nat → Nat}
    {Signed : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    {cl : MoltPetit.Model.CertClaim} {c : MoltPetit.Model.Chain}
    (h : MoltPetit.Model.GroundedHistorySched n schedule Signed G cl c) :
    MoltPetit.Model.GroundedHistory n Signed G cl c := by
  exact {
    valid := h.valid
    head := h.head
    tip := h.tip
    tail_eq := h.tail_eq
    len_eq := h.len_eq
    signed := fun B hB => Or.inr (h.signed B hB)
  }

lemma groundedHistory_of_groundedHistoryLock {n : Nat}
    {Signed : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    {cl : MoltPetit.Model.CertClaim} {g : Nat} {c : MoltPetit.Model.Chain}
    (h : MoltPetit.Model.GroundedHistoryLock n Signed G cl g c) :
    MoltPetit.Model.GroundedHistory n Signed G cl c := by
  obtain ⟨t, ht_last, ht_id, ht_slot, ht_h, _⟩ := h.tip
  exact {
    valid := h.valid
    head := h.head
    tip := ⟨t, ht_last, ht_id, ht_slot, ht_h⟩
    tail_eq := h.tail_eq
    len_eq := h.len_eq
    signed := fun B hB => Or.inr (h.signed B hB)
  }

lemma groundedHistoryK_genesis {n : Nat} (hn : 1 ≤ n) {Signed : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    (hG : MoltPetit.Model.genesisOk G = true) (hSlot : G.slot = 0) (hSig : Signed G) :
    MoltPetit.Model.GroundedHistoryK n Signed G
      { tipId := G.id, tipSlot := G.slot, tipHeight := G.height,
        tail := [G].filter fun x => decide (G.slot + 2 - n ≤ x.slot) }
      (fun i => if MoltPetit.Model.producerForSlot n G.slot = i then max 0 G.keyIndex else 0)
      [G] := by
  refine ⟨?_, by simp [MoltPetit.Model.blockAt?], ⟨G, by simp, rfl, rfl, rfl⟩, rfl, ?_,
    fun B hB => by rw [List.mem_singleton] at hB; exact hB ▸ hSig, ?_⟩
  · rw [MoltPetit.Model.validChainK, Bool.and_eq_true]
    refine ⟨?_, rfl⟩
    rw [MoltPetit.Model.validChain, show ([G] : MoltPetit.Model.Chain).getLast? = some G from rfl,
      Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨hG, rfl⟩, ?_⟩
    show MoltPetit.Model.maturedWindowsDense n [G] G.slot = true
    rw [MoltPetit.Model.maturedWindowsDense, List.all_eq_true]
    intro u hu
    have hu' := List.mem_range.mp hu
    have hn1 : n = 1 ∧ u = 0 := by omega
    obtain ⟨rfl, rfl⟩ := hn1
    rw [MoltPetit.Model.windowDense, decide_eq_true_eq]
    have : MoltPetit.Model.windowCount [G] 0 1 = 1 := by
      simp [MoltPetit.Model.windowCount, MoltPetit.Model.blockInWindow, hSlot]
    rw [this]
    unfold MoltPetit.Model.quorum
    omega
  · have : G.height = 0 := by
      rw [MoltPetit.Model.genesisOk, decide_eq_true_eq] at hG
      exact hG.1
    simp [this]
  · intro i
    unfold MoltPetit.Model.keyFloor
    by_cases hp : MoltPetit.Model.producerForSlot n G.slot = i
    · simp [hp]
    · simp [hp]

lemma groundedHistoryK_step {n : Nat} {Signed : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    {cl : MoltPetit.Model.CertClaim} {fl : Nat → Nat} {c : MoltPetit.Model.Chain} {b : MoltPetit.Model.Block}
    (hist : MoltPetit.Model.GroundedHistoryK n Signed G cl fl c)
    (hH : b.height = cl.tipHeight + 1)
    (hS : cl.tipSlot < b.slot)
    (hP : b.prev = some cl.tipId)
    (hSig : Signed b)
    (hKI : fl (MoltPetit.Model.producerForSlot n b.slot) ≤ b.keyIndex)
    (hD : ∀ u : Nat, cl.tipSlot + 2 ≤ u + n → u + n ≤ b.slot + 1 →
      MoltPetit.Model.quorum n ≤ MoltPetit.Model.windowCount (cl.tail ++ [b]) u n) :
    MoltPetit.Model.GroundedHistoryK n Signed G
      { tipId := b.id, tipSlot := b.slot, tipHeight := b.height,
        tail := (cl.tail ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot) }
      (fun i => if MoltPetit.Model.producerForSlot n b.slot = i then max (fl i) b.keyIndex else fl i)
      (c ++ [b]) := by
  have hcK := hist.valid
  rw [MoltPetit.Model.validChainK, Bool.and_eq_true] at hcK
  obtain ⟨hcV, hcM⟩ := hcK
  obtain ⟨t, hTipEq, htId, htSlot, htHeight⟩ := hist.tip
  have hChild : MoltPetit.Model.childOk t b = true := by
    rw [MoltPetit.Model.childOk, decide_eq_true_eq]
    exact ⟨by omega, by omega, by rw [hP, htId]⟩
  have hMat := (MoltPetit.Model.validChain_sound hcV).2.2.2
  have hTipAt : MoltPetit.Model.blockAt? c (c.length - 1) = some t := MoltPetit.Model.blockAt_getLast hTipEq
  have hAllDense : ∀ u : Nat, u + n ≤ b.slot + 1 →
      MoltPetit.Model.windowDense n (c ++ [b]) u = true := by
    intro u hu
    rw [MoltPetit.Model.windowDense, decide_eq_true_eq]
    by_cases hOld : u + n ≤ t.slot + 1
    · calc MoltPetit.Model.quorum n ≤ MoltPetit.Model.windowCount c u n := hMat hTipAt u hOld
        _ ≤ MoltPetit.Model.windowCount (c ++ [b]) u n :=
            MoltPetit.Model.windowCount_mono (List.sublist_append_left c [b])
    · have hcount := hD u (by omega) hu
      have heq : MoltPetit.Model.windowCount (cl.tail ++ [b]) u n = MoltPetit.Model.windowCount (c ++ [b]) u n := by
        rw [MoltPetit.Model.windowCount_append, MoltPetit.Model.windowCount_append, hist.tail_eq,
          MoltPetit.Model.windowCount_filter_low (by omega)]
      omega
  refine ⟨?_, ?_, ⟨b, by simp, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [MoltPetit.Model.validChainK, Bool.and_eq_true]
    refine ⟨MoltPetit.Model.validChain_append_one hcV hTipEq hChild hAllDense, ?_⟩
    refine MoltPetit.Model.keyMonoOk_append_of_from hcM ?_
    rw [MoltPetit.Model.keyMonoFrom, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by rw [hist.floors]; exact hKI, rfl⟩
  · have hcLen : 0 < c.length := by
      have := hist.len_eq
      omega
    have hHead := hist.head
    unfold MoltPetit.Model.blockAt? at hHead ⊢
    rw [List.getElem?_append_left hcLen]
    exact hHead
  · show (cl.tail ++ [b]).filter (fun x => decide (b.slot + 2 - n ≤ x.slot)) =
      (c ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot)
    rw [List.filter_append, List.filter_append, hist.tail_eq, List.filter_filter]
    congr 1
    apply List.filter_congr
    intro x _
    by_cases hx : b.slot + 2 - n ≤ x.slot
    · have hlo : cl.tipSlot + 2 - n ≤ x.slot := by omega
      simp [hx, hlo]
    · simp [hx]
  · simp [hist.len_eq, hH]
  · intro B hB
    rcases List.mem_append.mp hB with hBc | hBb
    · exact hist.signed B hBc
    · rw [List.mem_singleton] at hBb
      exact hBb ▸ hSig
  · intro i
    rw [MoltPetit.Model.keyFloor_append_one]
    by_cases hp : MoltPetit.Model.producerForSlot n b.slot = i
    · rw [if_pos hp, if_pos hp, hist.floors]
    · rw [if_neg hp, if_neg hp, hist.floors]

lemma foldK_history_aux {n q : U64} {G : Block}
    {Signed : MoltPetit.Model.Block → Prop}
    (hn : 1 ≤ n.val) (hq : quorum n = ok q) :
    ∀ (bs : List Block) (pre : List Block) (st : CertStateG U64) (fl out : FloorsG U64),
    (∀ b ∈ bs, Signed (toModelBlock b)) →
    TailRepr n.val st (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) →
    floorsLen fl = n.val →
    MoltPetit.Model.GroundedHistoryK n.val Signed (toModelBlock G)
      (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) (floorsFun fl)
      ((G :: pre).map toModelBlock) →
    FoldK n q st fl bs out →
    MoltPetit.Model.GroundedHistoryK n.val Signed (toModelBlock G)
      (modelClaimOf n.val (toModelBlock G) ((pre ++ bs).map toModelBlock)) (floorsFun out)
      ((G :: pre ++ bs).map toModelBlock) := by
  intro bs
  induction bs with
  | nil =>
    intro pre st fl out hSig hrep hlen hhist hfold
    simp only [List.append_nil]
    dsimp [FoldK] at hfold
    subst hfold
    exact hhist
  | cons b rest ih =>
    intro pre st fl out hSig hrep hlen hhist hfold
    obtain ⟨hstep, t', fl', ht', hfl', hfold_rest⟩ := hfold
    obtain ⟨hcore, hle⟩ := cert_step_k_be_sound hn hstep
    obtain ⟨hheight, hslot, hprev, hdense⟩ := cert_step_core_be_sound b hq hn hrep hcore
    have hSig_b : Signed (toModelBlock b) := hSig b (by simp)
    have hSig_rest : ∀ x ∈ rest, Signed (toModelBlock x) :=
      fun x hx => hSig x (by simp [hx])
    let cl := modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)
    have hstep_hist := groundedHistoryK_step hhist hheight hslot hprev hSig_b hle hdense
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
    have hhist_step : MoltPetit.Model.GroundedHistoryK n.val Signed
        (toModelBlock G) (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock))
        (floorsFun fl') ((G :: (pre ++ [b])).map toModelBlock) := by
      have hchain_eq : (G :: (pre ++ [b])).map toModelBlock = ((G :: pre).map toModelBlock) ++ [toModelBlock b] := by
        simp
      rw [hchain_eq, hmap_app, hcl_eq, hfun']
      exact hstep_hist
    have hrep' := cert_next_tail_be_repr b hq hn hrep hcore ht'
    have hrep_step : TailRepr n.val (stepState b t')
        (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock)) := by
      rw [hmap_app, hcl_eq]
      exact hrep'
    have hrec := ih (pre ++ [b]) (stepState b t') fl' out hSig_rest hrep_step hlen' hhist_step hfold_rest
    have h1 : (pre ++ [b]) ++ rest = pre ++ b :: rest := by simp
    have h2 : G :: (pre ++ [b]) ++ rest = G :: (pre ++ b :: rest) := by simp
    rw [h1, h2] at hrec
    exact hrec


lemma attestsK_history {C} {I : CryptoD C} {crypto : C} {n q : U64} {G : Block} {sG : Hash}
    {bs : List (Block × Hash)} {stO : CertStateG U64} {out : FloorsG U64} {ts : Hash}
    (hn : 1 ≤ n.val) (hq : quorum n = ok q)
    (hG : cert_genesis_ok_be UB () (toBlockG G) = ok true)
    (hSigG : SigOn I.CryptoInst crypto n G sG)
    (hA : AttestsK I crypto n q G sG bs stO out ts) :
    let cl₀ := modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)
    MoltPetit.Model.GroundedCert n.val (DSigned I crypto n G) (toModelBlock G) cl₀ ∧
    MoltPetit.Model.GroundedHistory n.val (DSigned I crypto n G) (toModelBlock G) cl₀ ((G :: bs.map Prod.fst).map toModelBlock) ∧
    MoltPetit.Model.GroundedHistoryK n.val (DSigned I crypto n G) (toModelBlock G) cl₀ (floorsFun out) ((G :: bs.map Prod.fst).map toModelBlock) ∧
    stateView n.val stO = MoltPetit.Model.claimView cl₀ := by
  intro cl₀
  obtain ⟨hSig, hFoldOut⟩ := hA
  have hFold := foldKOut_foldK hFoldOut
  have ⟨hgen, hslot0⟩ := cert_genesis_ok_be_sound hG
  have hSigG_ds : DSigned I crypto n G (toModelBlock G) :=
    ⟨rustSigned_of_sigOn hSigG, ⟨G, rfl, FormedFrom.genesis⟩⟩
  have hbase_hist : MoltPetit.Model.GroundedHistoryK n.val (DSigned I crypto n G)
      (toModelBlock G) (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock))
      (floorsFun (initFloors n.val G.key_index)) ((G :: []).map toModelBlock) := by
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
    exact groundedHistoryK_genesis hn hgen hslot0 hSigG_ds
  have hbase_rep : TailRepr n.val (genesisState n.val G)
      (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock)) := by
    simp only [List.map_nil]
    exact tailRepr_genesisState n.val G
  have hlen0 : floorsLen (initFloors n.val G.key_index) = n.val :=
    floorsLen_initFloors n.val G.key_index
  have hhist_ds := foldCoreOut_history_dsigned hSigG hSig (foldKOut_to_core hFoldOut)
  have hSig_bs : ∀ b ∈ bs.map Prod.fst, DSigned I crypto n G (toModelBlock b) := by
    intro b hb
    have hmem : toModelBlock b ∈ (G :: bs.map Prod.fst).map toModelBlock := by
      apply List.mem_cons_of_mem
      rw [List.mem_map]
      exact ⟨b, hb, rfl⟩
    exact hhist_ds (toModelBlock b) hmem
  have hhistK := foldK_history_aux hn hq (bs.map Prod.fst) [] (genesisState n.val G)
    (initFloors n.val G.key_index) out hSig_bs hbase_rep hlen0 hbase_hist hFold
  simp only [List.nil_append] at hhistK
  have hcertK : MoltPetit.Model.GroundedCertK n.val (DSigned I crypto n G)
      (toModelBlock G) cl₀ (floorsFun out) :=
    cert_fold_k_sound hn hq hG hSigG_ds hSig_bs hFold
  have hcert := groundedCert_of_groundedCertK hcertK
  have hhist := groundedHistory_of_groundedHistoryK hhistK
  have hview := stateView_of_foldKOut hn hq hG hFoldOut
  exact ⟨hcert, hhist, hhistK, hview⟩


lemma groundedHistory_genesis {n : Nat} (hn : 1 ≤ n) {Signed : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    (hG : MoltPetit.Model.genesisOk G = true) (hSlot : G.slot = 0) (hSig : Signed G) :
    MoltPetit.Model.GroundedHistory n Signed G
      { tipId := G.id, tipSlot := G.slot, tipHeight := G.height,
        tail := [G].filter fun x => decide (G.slot + 2 - n ≤ x.slot) }
      [G] := by
  refine ⟨?_, by simp [MoltPetit.Model.blockAt?], ⟨G, by simp, rfl, rfl, rfl⟩, rfl, ?_,
    fun B hB => by rw [List.mem_singleton] at hB; exact Or.inr (hB ▸ hSig)⟩
  · rw [MoltPetit.Model.validChain, show ([G] : MoltPetit.Model.Chain).getLast? = some G from rfl,
      Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨hG, rfl⟩, ?_⟩
    show MoltPetit.Model.maturedWindowsDense n [G] G.slot = true
    rw [MoltPetit.Model.maturedWindowsDense, List.all_eq_true]
    intro u hu
    have hu' := List.mem_range.mp hu
    have hn1 : n = 1 ∧ u = 0 := by omega
    obtain ⟨rfl, rfl⟩ := hn1
    rw [MoltPetit.Model.windowDense, decide_eq_true_eq]
    have : MoltPetit.Model.windowCount [G] 0 1 = 1 := by
      simp [MoltPetit.Model.windowCount, MoltPetit.Model.blockInWindow, hSlot]
    rw [this]
    unfold MoltPetit.Model.quorum
    omega
  · have : G.height = 0 := by
      rw [MoltPetit.Model.genesisOk, decide_eq_true_eq] at hG
      exact hG.1
    simp [this]

lemma groundedHistory_step {n : Nat} {Signed : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    {cl : MoltPetit.Model.CertClaim} {c : MoltPetit.Model.Chain} {b : MoltPetit.Model.Block}
    (hist : MoltPetit.Model.GroundedHistory n Signed G cl c)
    (hH : b.height = cl.tipHeight + 1)
    (hS : cl.tipSlot < b.slot)
    (hP : b.prev = some cl.tipId)
    (hSig : Signed b)
    (hD : ∀ u : Nat, cl.tipSlot + 2 ≤ u + n → u + n ≤ b.slot + 1 →
      MoltPetit.Model.quorum n ≤ MoltPetit.Model.windowCount (cl.tail ++ [b]) u n) :
    MoltPetit.Model.GroundedHistory n Signed G
      { tipId := b.id, tipSlot := b.slot, tipHeight := b.height,
        tail := (cl.tail ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot) }
      (c ++ [b]) := by
  have hcV := hist.valid
  obtain ⟨t, hTipEq, htId, htSlot, htHeight⟩ := hist.tip
  have hChild : MoltPetit.Model.childOk t b = true := by
    rw [MoltPetit.Model.childOk, decide_eq_true_eq]
    exact ⟨by omega, by omega, by rw [hP, htId]⟩
  have hMat := (MoltPetit.Model.validChain_sound hcV).2.2.2
  have hTipAt : MoltPetit.Model.blockAt? c (c.length - 1) = some t := MoltPetit.Model.blockAt_getLast hTipEq
  have hAllDense : ∀ u : Nat, u + n ≤ b.slot + 1 →
      MoltPetit.Model.windowDense n (c ++ [b]) u = true := by
    intro u hu
    rw [MoltPetit.Model.windowDense, decide_eq_true_eq]
    by_cases hOld : u + n ≤ t.slot + 1
    · calc MoltPetit.Model.quorum n ≤ MoltPetit.Model.windowCount c u n := hMat hTipAt u hOld
        _ ≤ MoltPetit.Model.windowCount (c ++ [b]) u n :=
            MoltPetit.Model.windowCount_mono (List.sublist_append_left c [b])
    · have hcount := hD u (by omega) hu
      have heq : MoltPetit.Model.windowCount (cl.tail ++ [b]) u n = MoltPetit.Model.windowCount (c ++ [b]) u n := by
        rw [MoltPetit.Model.windowCount_append, MoltPetit.Model.windowCount_append, hist.tail_eq,
          MoltPetit.Model.windowCount_filter_low (by omega)]
      omega
  refine ⟨MoltPetit.Model.validChain_append_one hcV hTipEq hChild hAllDense, ?_, ⟨b, by simp, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · have hcLen : 0 < c.length := by
      have := hist.len_eq
      omega
    have hHead := hist.head
    unfold MoltPetit.Model.blockAt? at hHead ⊢
    rw [List.getElem?_append_left hcLen]
    exact hHead
  · show (cl.tail ++ [b]).filter (fun x => decide (b.slot + 2 - n ≤ x.slot)) =
      (c ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot)
    rw [List.filter_append, List.filter_append, hist.tail_eq, List.filter_filter]
    congr 1
    apply List.filter_congr
    intro x _
    by_cases hx : b.slot + 2 - n ≤ x.slot
    · have hlo : cl.tipSlot + 2 - n ≤ x.slot := by omega
      simp [hx, hlo]
    · simp [hx]
  · simp [hist.len_eq, hH]
  · intro B hB
    rcases List.mem_append.mp hB with hBc | hBb
    · exact hist.signed B hBc
    · rw [List.mem_singleton] at hBb
      exact Or.inr (hBb ▸ hSig)

lemma foldSched_history_aux {n q era : U64} {G : Block}
    {Signed : MoltPetit.Model.Block → Prop}
    (hn : 1 ≤ n.val) (hq : quorum n = ok q) (hera : 0 < era.val) :
    ∀ (bs : List Block) (pre : List Block) (st : CertStateG U64) (stO : CertStateG U64),
    (∀ b ∈ bs, Signed (toModelBlock b)) →
    TailRepr n.val st (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) →
    MoltPetit.Model.GroundedHistory n.val (fun B => Signed B ∧ B.slot / era.val ≤ B.keyIndex) (toModelBlock G)
      (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock))
      ((G :: pre).map toModelBlock) →
    FoldSchedOut n q era st bs stO →
    MoltPetit.Model.GroundedHistory n.val (fun B => Signed B ∧ B.slot / era.val ≤ B.keyIndex) (toModelBlock G)
      (modelClaimOf n.val (toModelBlock G) ((pre ++ bs).map toModelBlock))
      ((G :: pre ++ bs).map toModelBlock) := by
  intro bs
  induction bs with
  | nil =>
    intro pre st stO hSig hrep hhist hfold
    simp only [List.append_nil]
    dsimp [FoldSchedOut] at hfold
    subst hfold
    exact hhist
  | cons b rest ih =>
    intro pre st stO hSig hrep hhist hfold
    obtain ⟨hstep, t', ht', hfold_rest⟩ := hfold
    obtain ⟨hcore, hpin⟩ := cert_step_sched_be_sound hera hstep
    obtain ⟨hheight, hslot, hprev, hdense⟩ := cert_step_core_be_sound b hq hn hrep hcore
    have hSig_b : Signed (toModelBlock b) ∧ (toModelBlock b).slot / era.val ≤ (toModelBlock b).keyIndex :=
      ⟨hSig b (by simp), hpin⟩
    have hSig_rest : ∀ x ∈ rest, Signed (toModelBlock x) :=
      fun x hx => hSig x (by simp [hx])
    let cl := modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)
    have hstep_hist := groundedHistory_step hhist hheight hslot hprev hSig_b hdense
    have hcl_eq : modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock ++ [toModelBlock b]) =
        { tipId := (toModelBlock b).id,
          tipSlot := (toModelBlock b).slot,
          tipHeight := (toModelBlock b).height,
          tail := (cl.tail ++ [toModelBlock b]).filter
            fun x => decide ((toModelBlock b).slot + 2 - n.val ≤ x.slot) } :=
      modelClaimOf_step_lt n.val (toModelBlock G) (pre.map toModelBlock) (toModelBlock b) hslot
    have hmap_app : (pre ++ [b]).map toModelBlock = pre.map toModelBlock ++ [toModelBlock b] := by
      simp
    have hhist_step : MoltPetit.Model.GroundedHistory n.val (fun B => Signed B ∧ B.slot / era.val ≤ B.keyIndex)
        (toModelBlock G) (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock))
        ((G :: (pre ++ [b])).map toModelBlock) := by
      have hchain_eq : (G :: (pre ++ [b])).map toModelBlock = ((G :: pre).map toModelBlock) ++ [toModelBlock b] := by
        simp
      rw [hchain_eq, hmap_app, hcl_eq]
      exact hstep_hist
    have hrep' := cert_next_tail_be_repr b hq hn hrep hcore ht'
    have hrep_step : TailRepr n.val (stepState b t')
        (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock)) := by
      rw [hmap_app, hcl_eq]
      exact hrep'
    have hrec := ih (pre ++ [b]) (stepState b t') stO hSig_rest hrep_step hhist_step hfold_rest
    have h1 : (pre ++ [b]) ++ rest = pre ++ b :: rest := by simp
    have h2 : G :: (pre ++ [b]) ++ rest = G :: (pre ++ b :: rest) := by simp
    rw [h1, h2] at hrec
    exact hrec

lemma groundedCert_pinned_of_groundedCertSched {n : Nat} {schedule : Nat → Nat}
    {Signed : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    {cl : MoltPetit.Model.CertClaim}
    (h : MoltPetit.Model.GroundedCertSched n schedule Signed G cl) :
    MoltPetit.Model.GroundedCert n (fun B => Signed B ∧ schedule B.slot ≤ B.keyIndex) G cl := by
  induction h with
  | genesis hG0 hSlot0 _ _ => exact MoltPetit.Model.GroundedCert.genesis hG0 hSlot0
  | extend cl b _ hh hs hp hS0 hP0 hd ih =>
    exact MoltPetit.Model.GroundedCert.extend cl b ih hh hs hp ⟨hS0, hP0⟩ hd

lemma attestsSched_history {C} {I : CryptoD C} {crypto : C} {n q era : U64} {G : Block} {sG : Hash}
    {bs : List (Block × Hash)} {stO : CertStateG U64} {ts : Hash}
    (hn : 1 ≤ n.val) (hq : quorum n = ok q) (hera : 0 < era.val)
    (hG : cert_genesis_ok_be UB () (toBlockG G) = ok true)
    (hSigG : SigOn I.CryptoInst crypto n G sG)
    (hA : AttestsSched I crypto n q era G sG bs stO ts) :
    let cl₀ := modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)
    MoltPetit.Model.GroundedCert n.val (fun B => DSigned I crypto n G B ∧ B.slot / era.val ≤ B.keyIndex) (toModelBlock G) cl₀ ∧
    MoltPetit.Model.GroundedHistory n.val (fun B => DSigned I crypto n G B ∧ B.slot / era.val ≤ B.keyIndex) (toModelBlock G) cl₀ ((G :: bs.map Prod.fst).map toModelBlock) ∧
    stateView n.val stO = MoltPetit.Model.claimView cl₀ ∧
    (∀ B ∈ (G :: bs.map Prod.fst).map toModelBlock, B.slot / era.val ≤ B.keyIndex) := by
  intro cl₀
  obtain ⟨hSig, hFoldOut⟩ := hA
  have hFold := foldSchedOut_foldSched hFoldOut
  have ⟨hgen, hslot0⟩ := cert_genesis_ok_be_sound hG
  have hSigG_ds : DSigned I crypto n G (toModelBlock G) :=
    ⟨rustSigned_of_sigOn hSigG, ⟨G, rfl, FormedFrom.genesis⟩⟩
  have hSigG_pinned : DSigned I crypto n G (toModelBlock G) ∧ (toModelBlock G).slot / era.val ≤ (toModelBlock G).keyIndex := by
    refine ⟨hSigG_ds, ?_⟩
    have : (toModelBlock G).slot = 0 := hslot0
    rw [this]
    simp
  have hbase_hist : MoltPetit.Model.GroundedHistory n.val (fun B => DSigned I crypto n G B ∧ B.slot / era.val ≤ B.keyIndex)
      (toModelBlock G) (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock))
      ((G :: []).map toModelBlock) := by
    simp only [List.map_nil]
    have hnil := modelClaimOf_nil n.val (toModelBlock G)
    rw [hnil]
    exact groundedHistory_genesis hn hgen hslot0 hSigG_pinned
  have hbase_rep : TailRepr n.val (genesisState n.val G)
      (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock)) := by
    simp only [List.map_nil]
    exact tailRepr_genesisState n.val G
  have hhist_ds := foldCoreOut_history_dsigned hSigG hSig (foldSchedOut_to_core hFoldOut)
  have hSig_bs : ∀ b ∈ bs.map Prod.fst, DSigned I crypto n G (toModelBlock b) := by
    intro b hb
    have hmem : toModelBlock b ∈ (G :: bs.map Prod.fst).map toModelBlock := by
      apply List.mem_cons_of_mem
      rw [List.mem_map]
      exact ⟨b, hb, rfl⟩
    exact hhist_ds (toModelBlock b) hmem
  have hhist := foldSched_history_aux hn hq hera (bs.map Prod.fst) [] (genesisState n.val G)
    stO hSig_bs hbase_rep hbase_hist hFoldOut
  simp only [List.nil_append] at hhist
  have hcertSched : MoltPetit.Model.GroundedCertSched n.val (fun s => s / era.val) (DSigned I crypto n G)
      (toModelBlock G) cl₀ :=
    cert_fold_sched_sound hn hq hera hG hSigG_ds hSig_bs hFold
  have hcert := groundedCert_pinned_of_groundedCertSched hcertSched
  have hview := stateView_of_foldSchedOut hn hq hera hG hFoldOut
  have hpinned : ∀ B ∈ (G :: bs.map Prod.fst).map toModelBlock, B.slot / era.val ≤ B.keyIndex := by
    intro B hB
    have hsignedB := hhist.signed B hB
    rcases hsignedB with hBG | hBS
    · rw [hBG]
      have : (toModelBlock G).slot = 0 := hslot0
      rw [this]
      simp
    · exact hBS.2
  exact ⟨hcert, hhist, hview, hpinned⟩


lemma groundedHistoryLock_genesis {n : Nat} (hn : 1 ≤ n)
    {Signed : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    (hG : MoltPetit.Model.genesisOk G = true) (hSlot : G.slot = 0) (hSig : Signed G) :
    MoltPetit.Model.GroundedHistoryLock n Signed G
      { tipId := G.id, tipSlot := G.slot, tipHeight := G.height,
        tail := [G].filter fun x => decide (G.slot + 2 - n ≤ x.slot) }
      G.keyIndex
      [G] := by
  refine ⟨?_, by simp [MoltPetit.Model.lockstepOk], by simp [MoltPetit.Model.blockAt?],
    ⟨G, by simp, rfl, rfl, rfl, rfl⟩, rfl, ?_,
    fun B hB => by rw [List.mem_singleton] at hB; exact hB ▸ hSig,
    fun B hB => by rw [List.mem_singleton] at hB; exact hB ▸ Nat.le_refl _,
    fun B hB _ => by rw [List.mem_singleton] at hB; exact hB ▸ rfl⟩
  · rw [MoltPetit.Model.validChain, show ([G] : MoltPetit.Model.Chain).getLast? = some G from rfl,
      Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨hG, rfl⟩, ?_⟩
    show MoltPetit.Model.maturedWindowsDense n [G] G.slot = true
    rw [MoltPetit.Model.maturedWindowsDense, List.all_eq_true]
    intro u hu
    have hu' := List.mem_range.mp hu
    have hn1 : n = 1 ∧ u = 0 := by omega
    obtain ⟨rfl, rfl⟩ := hn1
    rw [MoltPetit.Model.windowDense, decide_eq_true_eq]
    have : MoltPetit.Model.windowCount [G] 0 1 = 1 := by
      simp [MoltPetit.Model.windowCount, MoltPetit.Model.blockInWindow, hSlot]
    rw [this]
    unfold MoltPetit.Model.quorum
    omega
  · have : G.height = 0 := by
      rw [MoltPetit.Model.genesisOk, decide_eq_true_eq] at hG
      exact hG.1
    simp [this]

lemma groundedHistoryLock_step {n : Nat} {Signed : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    {cl : MoltPetit.Model.CertClaim} {g : Nat} {c : MoltPetit.Model.Chain} {b : MoltPetit.Model.Block}
    (hist : MoltPetit.Model.GroundedHistoryLock n Signed G cl g c)
    (hH : b.height = cl.tipHeight + 1)
    (hS : cl.tipSlot < b.slot)
    (hP : b.prev = some cl.tipId)
    (hSig : Signed b)
    (hLe : g ≤ b.keyIndex)
    (hWin : cl.tipSlot / n = b.slot / n → g = b.keyIndex)
    (hD : ∀ u : Nat, cl.tipSlot + 2 ≤ u + n → u + n ≤ b.slot + 1 →
      MoltPetit.Model.quorum n ≤ MoltPetit.Model.windowCount (cl.tail ++ [b]) u n) :
    MoltPetit.Model.GroundedHistoryLock n Signed G
      { tipId := b.id, tipSlot := b.slot, tipHeight := b.height,
        tail := (cl.tail ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot) }
      b.keyIndex
      (c ++ [b]) := by
  have hcV := hist.valid
  obtain ⟨t, hTipEq, htId, htSlot, htHeight, htKey⟩ := hist.tip
  have hChild : MoltPetit.Model.childOk t b = true := by
    rw [MoltPetit.Model.childOk, decide_eq_true_eq]
    exact ⟨by omega, by omega, by rw [hP, htId]⟩
  have hMat := (MoltPetit.Model.validChain_sound hcV).2.2.2
  have hStrictC : MoltPetit.Model.StrictSlots c := (MoltPetit.Model.validChain_sound hcV).2.1
  have hTipAt : MoltPetit.Model.blockAt? c (c.length - 1) = some t := MoltPetit.Model.blockAt_getLast hTipEq
  have hAllDense : ∀ u : Nat, u + n ≤ b.slot + 1 →
      MoltPetit.Model.windowDense n (c ++ [b]) u = true := by
    intro u hu
    rw [MoltPetit.Model.windowDense, decide_eq_true_eq]
    by_cases hOld : u + n ≤ t.slot + 1
    · calc MoltPetit.Model.quorum n ≤ MoltPetit.Model.windowCount c u n := hMat hTipAt u hOld
        _ ≤ MoltPetit.Model.windowCount (c ++ [b]) u n :=
            MoltPetit.Model.windowCount_mono (List.sublist_append_left c [b])
    · have hcount := hD u (by omega) hu
      have heq : MoltPetit.Model.windowCount (cl.tail ++ [b]) u n = MoltPetit.Model.windowCount (c ++ [b]) u n := by
        rw [MoltPetit.Model.windowCount_append, MoltPetit.Model.windowCount_append, hist.tail_eq,
          MoltPetit.Model.windowCount_filter_low (by omega)]
      omega
  have hSlotsC : ∀ a ∈ c, a.slot ≤ t.slot := fun a ha =>
    MoltPetit.Model.slot_le_tip_of_mem hStrictC hTipEq ha
  have hLockNew : MoltPetit.Model.lockstepOk n (c ++ [b]) = true :=
    MoltPetit.Model.lockstepOk_append_of_from hist.lock hSlotsC hist.gen_max
      (fun a ha haeq => hist.win_const a ha (by rw [haeq, htSlot]))
      (fun b' hb' => by
        rw [List.mem_singleton] at hb'; symm at hb'; subst hb'; rw [htSlot]; exact hS)
      (by simp [MoltPetit.Model.StrictSlots])
      (by
        unfold MoltPetit.Model.lockstepFrom
        rw [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨htKey ▸ hLe, ?_⟩, rfl⟩
        rw [htSlot]
        intro heq
        exact htKey ▸ hWin heq)
  refine ⟨MoltPetit.Model.validChain_append_one hcV hTipEq hChild hAllDense, hLockNew, ?_,
    ⟨b, by simp, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have hcLen : 0 < c.length := by
      have := hist.len_eq
      omega
    have hHead := hist.head
    unfold MoltPetit.Model.blockAt? at hHead ⊢
    rw [List.getElem?_append_left hcLen]
    exact hHead
  · show (cl.tail ++ [b]).filter (fun x => decide (b.slot + 2 - n ≤ x.slot)) =
      (c ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot)
    rw [List.filter_append, List.filter_append, hist.tail_eq, List.filter_filter]
    congr 1
    apply List.filter_congr
    intro x _
    by_cases hx : b.slot + 2 - n ≤ x.slot
    · have hlo : cl.tipSlot + 2 - n ≤ x.slot := by omega
      simp [hx, hlo]
    · simp [hx]
  · simp [hist.len_eq, hH]
  · intro B hB
    rcases List.mem_append.mp hB with hBc | hBb
    · exact hist.signed B hBc
    · rw [List.mem_singleton] at hBb
      exact hBb ▸ hSig
  · intro B hB
    rcases List.mem_append.mp hB with hBc | hBb
    · exact Nat.le_trans (hist.gen_max B hBc) hLe
    · rw [List.mem_singleton] at hBb; exact hBb ▸ Nat.le_refl _
  · intro B hB hBW
    rcases List.mem_append.mp hB with hBc | hBb
    · have hsand : t.slot / n = B.slot / n := by
        have h1 : B.slot / n ≤ t.slot / n := Nat.div_le_div_right (hSlotsC B hBc)
        have h2 : t.slot / n ≤ b.slot / n := Nat.div_le_div_right (Nat.le_of_lt (htSlot ▸ hS))
        have h3 : B.slot / n = b.slot / n := hBW
        omega
      have hgb : g = b.keyIndex := hWin (by rw [← htSlot]; exact hsand.trans hBW)
      exact (hist.win_const B hBc (by rw [← htSlot]; exact hsand.symm)).trans hgb
    · rw [List.mem_singleton] at hBb; exact hBb ▸ rfl

lemma foldLock_history_aux {n q : U64} {G : Block}
    {Signed : MoltPetit.Model.Block → Prop}
    (hn : 1 ≤ n.val) (hq : quorum n = ok q) :
    ∀ (bs : List Block) (pre : List Block) (st : CertStateG U64) (g : U64) (stO : CertStateG U64) (gO : U64),
    (∀ b ∈ bs, Signed (toModelBlock b)) →
    TailRepr n.val st (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) →
    MoltPetit.Model.GroundedHistoryLock n.val Signed (toModelBlock G)
      (modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)) g.val
      ((G :: pre).map toModelBlock) →
    FoldLockOut n q st g bs stO gO →
    MoltPetit.Model.GroundedHistoryLock n.val Signed (toModelBlock G)
      (modelClaimOf n.val (toModelBlock G) ((pre ++ bs).map toModelBlock)) gO.val
      ((G :: pre ++ bs).map toModelBlock) := by
  intro bs
  induction bs with
  | nil =>
    intro pre st g stO gO hSig hrep hhist hfold
    simp only [List.append_nil]
    dsimp [FoldLockOut] at hfold
    obtain ⟨rfl, rfl⟩ := hfold
    exact hhist
  | cons b rest ih =>
    intro pre st g stO gO hSig hrep hhist hfold
    obtain ⟨hstep, t', ht', hfold_rest⟩ := hfold
    obtain ⟨hcore, hle, hwin⟩ := cert_step_lock_be_sound hn hstep
    obtain ⟨hheight, hslot, hprev, hdense⟩ := cert_step_core_be_sound b hq hn hrep hcore
    have hSig_b : Signed (toModelBlock b) := hSig b (by simp)
    have hSig_rest : ∀ x ∈ rest, Signed (toModelBlock x) :=
      fun x hx => hSig x (by simp [hx])
    let cl := modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock)
    have hwin' : cl.tipSlot / n.val = (toModelBlock b).slot / n.val → g.val = (toModelBlock b).keyIndex := by
      intro heq
      rw [← hrep.tip_slot] at heq
      exact hwin heq
    have hstep_hist := groundedHistoryLock_step hhist hheight hslot hprev hSig_b hle hwin' hdense
    have hcl_eq : modelClaimOf n.val (toModelBlock G) (pre.map toModelBlock ++ [toModelBlock b]) =
        { tipId := (toModelBlock b).id,
          tipSlot := (toModelBlock b).slot,
          tipHeight := (toModelBlock b).height,
          tail := (cl.tail ++ [toModelBlock b]).filter
            fun x => decide ((toModelBlock b).slot + 2 - n.val ≤ x.slot) } :=
      modelClaimOf_step_lt n.val (toModelBlock G) (pre.map toModelBlock) (toModelBlock b) hslot
    have hmap_app : (pre ++ [b]).map toModelBlock = pre.map toModelBlock ++ [toModelBlock b] := by
      simp
    have hhist_step : MoltPetit.Model.GroundedHistoryLock n.val Signed
        (toModelBlock G) (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock))
        b.key_index.val ((G :: (pre ++ [b])).map toModelBlock) := by
      have hchain_eq : (G :: (pre ++ [b])).map toModelBlock = ((G :: pre).map toModelBlock) ++ [toModelBlock b] := by
        simp
      rw [hchain_eq, hmap_app, hcl_eq]
      exact hstep_hist
    have hrep' := cert_next_tail_be_repr b hq hn hrep hcore ht'
    have hrep_step : TailRepr n.val (stepState b t')
        (modelClaimOf n.val (toModelBlock G) ((pre ++ [b]).map toModelBlock)) := by
      rw [hmap_app, hcl_eq]
      exact hrep'
    have hrec := ih (pre ++ [b]) (stepState b t') b.key_index stO gO hSig_rest hrep_step hhist_step hfold_rest
    have h1 : (pre ++ [b]) ++ rest = pre ++ b :: rest := by simp
    have h2 : G :: (pre ++ [b]) ++ rest = G :: (pre ++ b :: rest) := by simp
    rw [h1, h2] at hrec
    exact hrec

lemma attestsLock_history {C} {I : CryptoD C} {crypto : C} {n q : U64} {G : Block} {sG : Hash}
    {bs : List (Block × Hash)} {stO : CertStateG U64} {gO : U64} {ts : Hash}
    (hn : 1 ≤ n.val) (hq : quorum n = ok q)
    (hG : cert_genesis_ok_be UB () (toBlockG G) = ok true)
    (hSigG : SigOn I.CryptoInst crypto n G sG)
    (hA : AttestsLock I crypto n q G sG bs stO gO ts) :
    let cl₀ := modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)
    MoltPetit.Model.GroundedCertLock n.val (DSigned I crypto n G) (toModelBlock G) cl₀ gO.val ∧
    MoltPetit.Model.GroundedHistoryLock n.val (DSigned I crypto n G) (toModelBlock G) cl₀ gO.val ((G :: bs.map Prod.fst).map toModelBlock) ∧
    MoltPetit.Model.GroundedHistory n.val (DSigned I crypto n G) (toModelBlock G) cl₀ ((G :: bs.map Prod.fst).map toModelBlock) ∧
    stateView n.val stO = MoltPetit.Model.claimView cl₀ := by
  intro cl₀
  obtain ⟨hSig, hFoldOut⟩ := hA
  have hFold := foldLockOut_foldLock hFoldOut
  have ⟨hgen, hslot0⟩ := cert_genesis_ok_be_sound hG
  have hSigG_ds : DSigned I crypto n G (toModelBlock G) :=
    ⟨rustSigned_of_sigOn hSigG, ⟨G, rfl, FormedFrom.genesis⟩⟩
  have hbase_hist : MoltPetit.Model.GroundedHistoryLock n.val (DSigned I crypto n G)
      (toModelBlock G) (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock))
      G.key_index.val ((G :: []).map toModelBlock) := by
    simp only [List.map_nil]
    have hnil := modelClaimOf_nil n.val (toModelBlock G)
    rw [hnil]
    have hGki : (toModelBlock G).keyIndex = G.key_index.val := rfl
    rw [← hGki]
    exact groundedHistoryLock_genesis hn hgen hslot0 hSigG_ds
  have hbase_rep : TailRepr n.val (genesisState n.val G)
      (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock)) := by
    simp only [List.map_nil]
    exact tailRepr_genesisState n.val G
  have hhist_ds := foldCoreOut_history_dsigned hSigG hSig (foldLockOut_to_core hFoldOut)
  have hSig_bs : ∀ b ∈ bs.map Prod.fst, DSigned I crypto n G (toModelBlock b) := by
    intro b hb
    have hmem : toModelBlock b ∈ (G :: bs.map Prod.fst).map toModelBlock := by
      apply List.mem_cons_of_mem
      rw [List.mem_map]
      exact ⟨b, hb, rfl⟩
    exact hhist_ds (toModelBlock b) hmem
  have hhistLock := foldLock_history_aux hn hq (bs.map Prod.fst) [] (genesisState n.val G)
    G.key_index stO gO hSig_bs hbase_rep hbase_hist hFoldOut
  simp only [List.nil_append] at hhistLock
  have hcertLock : MoltPetit.Model.GroundedCertLock n.val (DSigned I crypto n G)
      (toModelBlock G) cl₀ gO.val := by
    have h_sound := cert_fold_lock_sound hn hq hG hSigG_ds hSig_bs hFold
    have h_gO := foldLockOut_gO hFoldOut
    rw [h_gO]
    exact h_sound
  have hhist := groundedHistory_of_groundedHistoryLock hhistLock
  have hview := stateView_of_foldLockOut hn hq hG hFoldOut
  exact ⟨hcertLock, hhistLock, hhist, hview⟩

private theorem rust_deployed_agreement_one_time :
  ∀ {σ ℓ φ δ : Nat} {n q Δ : U64} (hn : 1 ≤ n.val) (hq : quorum n = ok q)
    {C} (I : CryptoD C) (crypto : C)
    {exposed : MoltPetit.Model.Exposure} {log : MoltPetit.Model.TimedLog}
    {G : Block} {R : Nat}
    (hG : cert_genesis_ok_be UB () (toBlockG G) = ok true)
    {sG : Hash} (hSigG : SigOn I.CryptoInst crypto n G sG)
    (hexec : MoltPetit.Model.SigningExecutionOn (DSigned I crypto n G) exposed log (toModelBlock G))
    (hClock : MoltPetit.Model.HonestClockOn (DSigned I crypto n G) σ exposed log)
    (hBudget : MoltPetit.Model.ExposureBounded n.val ℓ φ exposed)
    (hL : n.val ≤ ℓ + 1)
    (hL' : n.val + MoltPetit.Model.maxByzantine n.val + σ + 1 ≤ MoltPetit.Model.quorum n.val + ℓ)
    (hbridge : ∀ ⦃B : MoltPetit.Model.Block⦄, DSigned I crypto n G B → ∃ r ≤ R, B ∈ log r)
    (hφ : Δ.val + δ ≤ φ)
    {now now' : U64} (hNow : R ≤ now.val + δ) (hNow' : R ≤ now'.val + δ)
    {cert cert' : Hash} {suffix suffix' : SignedChain}
    (hval  : validate_deployed I n now  Δ crypto cert  suffix  = ok true)
    (hval' : validate_deployed I n now' Δ crypto cert' suffix' = ok true)
    {tl tl' : Chain} (hstr : strip_sigs suffix = ok tl) (hstr' : strip_sigs suffix' = ok tl')
    {bs bs' : List (Block × Hash)} {ts ts' : Hash}
    (hts : I.cert_tip_sig crypto cert = ok ts) (hts' : I.cert_tip_sig crypto cert' = ok ts')
    {stO stO' : CertStateG U64} {out out' : FloorsG U64}
    (hst  : I.cert_state crypto cert  = ok stO) (hst' : I.cert_state crypto cert' = ok stO')
    (hA  : AttestsK I crypto n q G sG bs  stO  out ts)
    (hA' : AttestsK I crypto n q G sG bs' stO' out' ts')
    {h : Nat}
    (hDeep  : h + n.val < (fullChain G bs  tl ).length)
    (hDeep' : h + n.val < (fullChain G bs' tl').length),
    MoltPetit.Model.blockAt? (fullChain G bs tl) h = MoltPetit.Model.blockAt? (fullChain G bs' tl') h := by
  intro σ ℓ φ δ n q Δ hn hq C I crypto exposed log G R hG sG hSigG hexec hClock hBudget hL hL'
        hbridge hφ now now' hNow hNow' cert cert' suffix suffix' hval hval' tl tl' hstr hstr'
        bs bs' ts ts' hts hts' stO stO' out out' hst hst' hA hA' h hDeep hDeep'
  obtain ⟨st, cl, stripped, tip, s1, tl_sub, ts0,
          hst_val, hcl, hstrip, hcons, htip, hverify, hsig, hts_sig, hids, hsuf, hrecent⟩ :=
    validate_deployed_sound hval
  obtain ⟨st', cl', stripped', tip', s1', tl_sub', ts0',
          hst_val', hcl', hstrip', hcons', htip', hverify', hsig', hts_sig', hids', hsuf', hrecent'⟩ :=
    validate_deployed_sound hval'
  rw [hstr] at hstrip
  injection hstrip with hstrip
  subst hstrip
  subst hcons
  rw [hstr'] at hstrip'
  injection hstrip' with hstrip'
  subst hstrip'
  subst hcons'
  rw [hst] at hst_val
  injection hst_val with hst_val
  subst hst_val
  rw [hst'] at hst_val'
  injection hst_val' with hst_val'
  subst hst_val'
  rw [hts] at hts_sig
  injection hts_sig with hts_sig
  subst hts_sig
  rw [hts'] at hts_sig'
  injection hts_sig' with hts_sig'
  subst hts_sig'
  have htip_rw : molt_petit.tip_slot_from cl.tip_slot (molt_petit.Chain.Cons s1 tl_sub) =
                 molt_petit.tip_slot_from s1.slot tl_sub := by
    rw [molt_petit.tip_slot_from]
  rw [htip_rw] at htip
  obtain ⟨sTip, hTipS, hts_slot⟩ :=
    tip_slot_from_eq_getLast tl_sub s1.slot (toModelBlock s1) rfl htip
  have htip_rw' : molt_petit.tip_slot_from cl'.tip_slot (molt_petit.Chain.Cons s1' tl_sub') =
                  molt_petit.tip_slot_from s1'.slot tl_sub' := by
    rw [molt_petit.tip_slot_from]
  rw [htip_rw'] at htip'
  obtain ⟨sTip', hTipS', hts_slot'⟩ :=
    tip_slot_from_eq_getLast tl_sub' s1'.slot (toModelBlock s1') rfl htip'
  obtain ⟨hcert, hhist, _, hview⟩ := attestsK_history hn hq hG hSigG hA
  obtain ⟨hcert', hhist', _, hview'⟩ := attestsK_history hn hq hG hSigG hA'
  have hcv : MoltPetit.Model.claimView (modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)) =
             MoltPetit.Model.claimView (toModelClaim cl) := by
    rw [← hview, claim_of_state_sound hcl]
  have hcv' : MoltPetit.Model.claimView (modelClaimOf n.val (toModelBlock G) ((bs'.map Prod.fst).map toModelBlock)) =
              MoltPetit.Model.claimView (toModelClaim cl') := by
    rw [← hview', claim_of_state_sound hcl']
  obtain ⟨hLink, hLinks, hDense⟩ := validate_suffix_sound_view hTipS hsuf hcv
  obtain ⟨hLink', hLinks', hDense'⟩ := validate_suffix_sound_view hTipS' hsuf' hcv'
  have ⟨_hh, _hs, hp⟩ := hLink
  have ⟨_hh', _hs', hp'⟩ := hLink'
  have ⟨_, T, hT, hSigT, hstO_id, _, _⟩ := foldKOut_history_formed hSigG hA.1 hA.2
  have ⟨_, T', hT', hSigT', hstO'_id, _, _⟩ := foldKOut_history_formed hSigG hA'.1 hA'.2
  have h_tipId : (modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)).tipId = hashToNat T.id := by
    have h1 : (modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)).tipId = hashGToNat stO.tip_id := congrArg (fun v => v.1) hview.symm
    rw [h1, hstO_id, hashGToNat_toHashG]
  have hprev_T : (toModelBlock s1).prev = some (hashToNat T.id) := by
    rw [hp, h_tipId]
  have hlinks : ChainLinks T.id (.Cons s1 tl_sub) :=
    chainLinks_of_toModel_linksOk tl_sub hprev_T hLinks
  have hSigned := dsigned_of_sigs_ok_ids_ok hT hSigT hsig hstr hids hlinks
  have h_tipId' : (modelClaimOf n.val (toModelBlock G) ((bs'.map Prod.fst).map toModelBlock)).tipId = hashToNat T'.id := by
    have h1 : (modelClaimOf n.val (toModelBlock G) ((bs'.map Prod.fst).map toModelBlock)).tipId = hashGToNat stO'.tip_id := congrArg (fun v => v.1) hview'.symm
    rw [h1, hstO'_id, hashGToNat_toHashG]
  have hprev_T' : (toModelBlock s1').prev = some (hashToNat T'.id) := by
    rw [hp', h_tipId']
  have hlinks' : ChainLinks T'.id (.Cons s1' tl_sub') :=
    chainLinks_of_toModel_linksOk tl_sub' hprev_T' hLinks'
  have hSigned' := dsigned_of_sigs_ok_ids_ok hT' hSigT' hsig' hstr' hids' hlinks'
  have hRecent : R ≤ sTip.slot + φ := by
    have hrec := recent_ok_sound hrecent
    omega
  have hRecent' : R ≤ sTip'.slot + φ := by
    have hrec' := recent_ok_sound hrecent'
    omega
  have hagree := MoltPetit.Model.exposure_certified_agreement_on
    hn hexec hClock hBudget hL hL' hbridge
    hcert hcert' hTipS hTipS' hLink hLinks hDense hLink' hLinks' hDense'
    hSigned hSigned' hRecent hRecent' hhist hhist' hDeep hDeep'
  exact hagree

/-- **Theorem 1 (deployed agreement)**: two clients that accept with `validate_deployed`
at clock readings `now`, `now'` agree on every block `n` deep in their full chains. -/
theorem rust_deployed_agreement : MoltPaper.thm_rust_deployed_agreement := by
  intro σ ℓ φ δ n q Δ hn hq C I crypto exposed log G R R' d hG sG hSigG hexec hClock hBudget hL hL'
        hbridge hφ now now' hNow hNow' hRR cert cert' suffix suffix' hval hval' tl tl' hstr hstr'
        bs bs' ts ts' hts hts' stO stO' out out' hst hst' hA hA' h hDeep hDeep'
  exact @rust_deployed_agreement_one_time σ ℓ φ (δ + d) n q Δ hn hq C I crypto exposed log G (max R R')
    hG sG hSigG hexec hClock hBudget hL hL'
    hbridge (by omega) now now' (by omega) (by omega)
    cert cert' suffix suffix' hval hval' tl tl' hstr hstr'
    bs bs' ts ts' hts hts' stO stO' out out' hst hst' hA hA' h hDeep hDeep'

/-- Pointwise agreement between `floorLookup` on `toTSFloors fl` (where `fl` is decoded by
`floors_of_state k fg`) and `floorsFun fg`. -/
lemma floorLookup_floors_of_state (fg : FloorsG U64) :
    ∀ (k : U64) (fl : molt_petit.FloorList),
      molt_petit.floors_of_state k fg = ok fl →
      ∀ (off : Nat),
        MoltPetit.floorLookup (toTSFloors fl) ((k.val + off : Nat) : Int) =
          ((floorsFun fg off : Nat) : Int) := by
  induction fg with
  | FNil =>
    intro k fl h off
    rw [molt_petit.floors_of_state] at h
    injection h with h
    subst h
    simp [toTSFloors, MoltPetit.floorLookup, floorsFun]
  | FCons f tl ih =>
    intro k fl h off
    rw [molt_petit.floors_of_state] at h
    obtain ⟨k1, hk1, h⟩ := molt_petit.bind_inv h
    obtain ⟨fl1, hfl1, h⟩ := molt_petit.bind_inv h
    injection h with h
    subst h
    simp only [toTSFloors]
    rw [MoltPetit.floorLookup]
    have hadd := UScalar.add_equiv k 1#u64
    have hk1v : k1.val = k.val + 1 := by
      simp only [hk1] at hadd
      simpa using hadd.2.1
    cases off with
    | zero =>
      simp only [Nat.add_zero]
      have heq : ((k.val : Int) == (k.val : Int)) = true := by simp
      rw [heq]
      rfl
    | succ off' =>
      have hneq : ((k.val : Int) == ((k.val + (off' + 1) : Nat) : Int)) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro hc
        have : k.val = k.val + off' + 1 := by exact_mod_cast hc
        omega
      rw [hneq]
      have hrewr : ((k.val + (off' + 1) : Nat) : Int) = ((k1.val + off' : Nat) : Int) := by
        rw [hk1v]
        push_cast
        omega
      rw [hrewr]
      exact ih k1 fl1 hfl1 off'

lemma rust_deployed_k_mono {C} (I : CryptoD C) (crypto : C) {n q Δ : U64}
    (hn : 1 ≤ n.val) (hq : quorum n = ok q)
    {G : Block} (hG : cert_genesis_ok_be UB () (toBlockG G) = ok true)
    {sG : Hash} (hSigG : SigOn I.CryptoInst crypto n G sG)
    {now : U64} {cert : Hash} {suffix : SignedChain}
    (hval : validate_deployed_k I n now Δ crypto cert suffix = ok true)
    {tl : Chain} (hstr : strip_sigs suffix = ok tl)
    {bs : List (Block × Hash)} {ts : Hash} {stO : CertStateG U64} {out : FloorsG U64}
    (hfl : I.cert_floors_state crypto cert = ok out)
    (hA : AttestsK I crypto n q G sG bs stO out ts) :
    MoltPetit.Model.KeyIndexMonotone n.val (fullChain G bs tl) := by
  obtain ⟨_, fg, fl, stripped, hfg, hfl_state, hstrip, hshape, hkeymono⟩ :=
    validate_deployed_k_sound hval
  rw [hfl] at hfg
  injection hfg with hfg
  subst hfg
  rw [hstr] at hstrip
  injection hstrip with hstrip
  subst hstrip
  rw [molt_petit.floors_shape_ok] at hshape
  have hshapeTS : MoltPetit.floorsShapeFrom 0 (n.val : Int) (toTSFloors fl) = true := by
    have := floors_shape_from_corr fl 0#u64 n hshape
    simpa using this
  have hhas : ∀ j : Nat, j < n.val → MoltPetit.Model.FloorHas (toTSFloors fl) j :=
    fun j hj => MoltPetit.Model.floorHas_of_shapeFrom (toTSFloors fl) 0 hshapeTS j
      (Int.natCast_nonneg j) (by exact_mod_cast hj)
  have hden : ∀ j : Nat, j < n.val →
      MoltPetit.floorLookup (toTSFloors fl) (j : Int) = ((floorsFun out j : Nat) : Int) := by
    intro j hj
    have hlook := floorLookup_floors_of_state out 0#u64 fl hfl_state j
    have h0 : (0#u64 : U64).val = 0 := rfl
    rw [h0, Nat.zero_add] at hlook
    exact hlook
  have hts := key_mono_from_corr (by omega) tl fl hkeymono
  have hmono_tl :
      MoltPetit.Model.keyMonoFrom n.val (floorsFun out) (toModelChain tl) = true := by
    have hiff :=
      MoltPetit.Model.ts_keyMonoFromTs hn (toModelChain tl) (toTSFloors fl) (floorsFun out) hhas hden
    exact hiff.mp hts
  obtain ⟨hcert, hhist, hhistK, hview⟩ := attestsK_history hn hq hG hSigG hA
  have hcM : MoltPetit.Model.keyMonoOk n.val ((G :: bs.map Prod.fst).map toModelBlock) = true := by
    have := hhistK.valid
    rw [MoltPetit.Model.validChainK, Bool.and_eq_true] at this
    exact this.2
  have hmono_from_floor : MoltPetit.Model.keyMonoFrom n.val
      (MoltPetit.Model.keyFloor n.val ((G :: bs.map Prod.fst).map toModelBlock)) (toModelChain tl) = true := by
    rw [MoltPetit.Model.keyMonoFrom_congr hhistK.floors]
    exact hmono_tl
  have hmono_full : MoltPetit.Model.keyMonoOk n.val (fullChain G bs tl) = true := by
    exact MoltPetit.Model.keyMonoOk_append_of_from hcM hmono_from_floor
  exact MoltPetit.Model.keyMonoOk_sound hmono_full

/-- **Theorem (deployed K agreement)**: mode 1 deployed agreement with monotone key indices. -/
theorem rust_deployed_k_agreement : MoltPaper.thm_rust_deployed_k_agreement := by
  intro σ ℓ φ δ n q Δ hn hq C I crypto exposed log G R R' d hG sG hSigG hexec hClock hBudget hL hL'
        hbridge hφ now now' hNow hNow' hRR cert cert' suffix suffix' hval hval' tl tl' hstr hstr'
        bs bs' ts ts' hts hts' stO stO' out out' hst hst' hfl hfl' hA hA' h hDeep hDeep'
  obtain ⟨hval_dep, _⟩ := validate_deployed_k_sound hval
  obtain ⟨hval'_dep, _⟩ := validate_deployed_k_sound hval'
  have hagree := rust_deployed_agreement hn hq I crypto
    hG hSigG hexec hClock hBudget hL hL' hbridge hφ
    hNow hNow' hRR hval_dep hval'_dep hstr hstr' hts hts' hst hst' hA hA' hDeep hDeep'
  have hmono := rust_deployed_k_mono I crypto hn hq hG hSigG hval hstr hfl hA
  have hmono' := rust_deployed_k_mono I crypto hn hq hG hSigG hval' hstr' hfl' hA'
  exact ⟨hagree, hmono, hmono'⟩


private theorem rust_deployed_sched_agreement_one_time :
  ∀ {σ ℓ φ δ : Nat} {n q era Δ : U64} (hn : 1 ≤ n.val) (hq : quorum n = ok q)
    (hera : 0 < era.val)
    {C} (I : CryptoD C) (crypto : C)
    {Controlled : Nat → Nat → Prop} {Stolen : Nat → Nat → Nat → Prop}
    {log : MoltPetit.Model.TimedLog} {G : Block} {R : Nat}
    (hG : cert_genesis_ok_be UB () (toBlockG G) = ok true)
    {sG : Hash} (hSigG : SigOn I.CryptoInst crypto n G sG)
    (hexec : MoltPetit.Model.SigningExecutionOn
      (fun B => DSigned I crypto n G B ∧ B.slot / era.val ≤ B.keyIndex)
      (MoltPetit.Model.schedExposed n.val (fun s => s / era.val) Controlled Stolen) log (toModelBlock G))
    (hClock : MoltPetit.Model.HonestClockOn
      (fun B => DSigned I crypto n G B ∧ B.slot / era.val ≤ B.keyIndex) σ
      (MoltPetit.Model.schedExposed n.val (fun s => s / era.val) Controlled Stolen) log)
    (hBudget : MoltPetit.Model.ExposureBounded n.val ℓ φ
      (MoltPetit.Model.schedExposed n.val (fun s => s / era.val) Controlled Stolen))
    (hL : n.val ≤ ℓ + 1)
    (hL' : n.val + MoltPetit.Model.maxByzantine n.val + σ + 1 ≤ MoltPetit.Model.quorum n.val + ℓ)
    (hbridge : ∀ ⦃B : MoltPetit.Model.Block⦄, DSigned I crypto n G B → B.slot / era.val ≤ B.keyIndex →
      ∃ r ≤ R, B ∈ log r)
    (hφ : Δ.val + δ ≤ φ)
    {now now' : U64} (hNow : R ≤ now.val + δ) (hNow' : R ≤ now'.val + δ)
    {cert cert' : Hash} {suffix suffix' : SignedChain}
    (hval  : validate_deployed_sched I n era now  Δ crypto cert  suffix  = ok true)
    (hval' : validate_deployed_sched I n era now' Δ crypto cert' suffix' = ok true)
    {tl tl' : Chain} (hstr : strip_sigs suffix = ok tl) (hstr' : strip_sigs suffix' = ok tl')
    {bs bs' : List (Block × Hash)} {ts ts' : Hash}
    (hts : I.cert_tip_sig crypto cert = ok ts) (hts' : I.cert_tip_sig crypto cert' = ok ts')
    {stO stO' : CertStateG U64}
    (hst  : I.cert_state crypto cert  = ok stO) (hst' : I.cert_state crypto cert' = ok stO')
    (hA  : AttestsSched I crypto n q era G sG bs  stO ts)
    (hA' : AttestsSched I crypto n q era G sG bs' stO' ts')
    {h : Nat}
    (hDeep  : h + n.val < (fullChain G bs  tl ).length)
    (hDeep' : h + n.val < (fullChain G bs' tl').length),
    MoltPetit.Model.blockAt? (fullChain G bs tl) h = MoltPetit.Model.blockAt? (fullChain G bs' tl') h ∧
    (∀ B ∈ fullChain G bs tl, B.slot / era.val ≤ B.keyIndex) ∧
    (∀ B ∈ fullChain G bs' tl', B.slot / era.val ≤ B.keyIndex) := by
  intro σ ℓ φ δ n q era Δ hn hq hera C I crypto Controlled Stolen log G R hG sG hSigG hexec hClock hBudget hL hL'
        hbridge hφ now now' hNow hNow' cert cert' suffix suffix' hval hval' tl tl' hstr hstr'
        bs bs' ts ts' hts hts' stO stO' hst hst' hA hA' h hDeep hDeep'
  obtain ⟨hval_dep, stripped, hstrip_sched, hpin⟩ := validate_deployed_sched_sound hval
  obtain ⟨hval'_dep, stripped', hstrip_sched', hpin'⟩ := validate_deployed_sched_sound hval'
  rw [hstr] at hstrip_sched
  injection hstrip_sched with hstrip_sched
  subst hstrip_sched
  rw [hstr'] at hstrip_sched'
  injection hstrip_sched' with hstrip_sched'
  subst hstrip_sched'
  obtain ⟨st, cl, stripped_dep, tip, s1, tl_sub, ts0,
          hst_val, hcl, hstrip_dep, hcons, htip, hverify, hsig, hts_sig, hids, hsuf, hrecent⟩ :=
    validate_deployed_sound hval_dep
  obtain ⟨st', cl', stripped_dep', tip', s1', tl_sub', ts0',
          hst_val', hcl', hstrip_dep', hcons', htip', hverify', hsig', hts_sig', hids', hsuf', hrecent'⟩ :=
    validate_deployed_sound hval'_dep
  rw [hstr] at hstrip_dep
  injection hstrip_dep with hstrip_dep
  subst hstrip_dep
  subst hcons
  rw [hstr'] at hstrip_dep'
  injection hstrip_dep' with hstrip_dep'
  subst hstrip_dep'
  subst hcons'
  rw [hst] at hst_val
  injection hst_val with hst_val
  subst hst_val
  rw [hst'] at hst_val'
  injection hst_val' with hst_val'
  subst hst_val'
  rw [hts] at hts_sig
  injection hts_sig with hts_sig
  subst hts_sig
  rw [hts'] at hts_sig'
  injection hts_sig' with hts_sig'
  subst hts_sig'
  have htip_rw : molt_petit.tip_slot_from cl.tip_slot (molt_petit.Chain.Cons s1 tl_sub) =
                 molt_petit.tip_slot_from s1.slot tl_sub := by
    rw [molt_petit.tip_slot_from]
  rw [htip_rw] at htip
  obtain ⟨sTip, hTipS, hts_slot⟩ :=
    tip_slot_from_eq_getLast tl_sub s1.slot (toModelBlock s1) rfl htip
  have htip_rw' : molt_petit.tip_slot_from cl'.tip_slot (molt_petit.Chain.Cons s1' tl_sub') =
                  molt_petit.tip_slot_from s1'.slot tl_sub' := by
    rw [molt_petit.tip_slot_from]
  rw [htip_rw'] at htip'
  obtain ⟨sTip', hTipS', hts_slot'⟩ :=
    tip_slot_from_eq_getLast tl_sub' s1'.slot (toModelBlock s1') rfl htip'
  obtain ⟨hcert, hhist, hview, hPin_hist⟩ := attestsSched_history hn hq hera hG hSigG hA
  obtain ⟨hcert', hhist', hview', hPin_hist'⟩ := attestsSched_history hn hq hera hG hSigG hA'
  have hcv : MoltPetit.Model.claimView (modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)) =
             MoltPetit.Model.claimView (toModelClaim cl) := by
    rw [← hview, claim_of_state_sound hcl]
  have hcv' : MoltPetit.Model.claimView (modelClaimOf n.val (toModelBlock G) ((bs'.map Prod.fst).map toModelBlock)) =
              MoltPetit.Model.claimView (toModelClaim cl') := by
    rw [← hview', claim_of_state_sound hcl']
  obtain ⟨hLink, hLinks, hDense⟩ := validate_suffix_sound_view hTipS hsuf hcv
  obtain ⟨hLink', hLinks', hDense'⟩ := validate_suffix_sound_view hTipS' hsuf' hcv'
  have ⟨_hh, _hs, hp⟩ := hLink
  have ⟨_hh', _hs', hp'⟩ := hLink'
  have ⟨_, T, hT, hSigT, hstO_id, _, _⟩ := foldSchedOut_history_formed hSigG hA.1 hA.2
  have ⟨_, T', hT', hSigT', hstO'_id, _, _⟩ := foldSchedOut_history_formed hSigG hA'.1 hA'.2
  have h_tipId : (modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)).tipId = hashToNat T.id := by
    have h1 : (modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)).tipId = hashGToNat stO.tip_id := congrArg (fun v => v.1) hview.symm
    rw [h1, hstO_id, hashGToNat_toHashG]
  have hprev_T : (toModelBlock s1).prev = some (hashToNat T.id) := by
    rw [hp, h_tipId]
  have hlinks : ChainLinks T.id (.Cons s1 tl_sub) :=
    chainLinks_of_toModel_linksOk tl_sub hprev_T hLinks
  have hSigned := dsigned_of_sigs_ok_ids_ok hT hSigT hsig hstr hids hlinks
  have h_tipId' : (modelClaimOf n.val (toModelBlock G) ((bs'.map Prod.fst).map toModelBlock)).tipId = hashToNat T'.id := by
    have h1 : (modelClaimOf n.val (toModelBlock G) ((bs'.map Prod.fst).map toModelBlock)).tipId = hashGToNat stO'.tip_id := congrArg (fun v => v.1) hview'.symm
    rw [h1, hstO'_id, hashGToNat_toHashG]
  have hprev_T' : (toModelBlock s1').prev = some (hashToNat T'.id) := by
    rw [hp', h_tipId']
  have hlinks' : ChainLinks T'.id (.Cons s1' tl_sub') :=
    chainLinks_of_toModel_linksOk tl_sub' hprev_T' hLinks'
  have hSigned' := dsigned_of_sigs_ok_ids_ok hT' hSigT' hsig' hstr' hids' hlinks'
  have hPinS := sched_pin_ok_sound (.Cons s1 tl_sub) hpin
  have hPinS' := sched_pin_ok_sound (.Cons s1' tl_sub') hpin'
  have hPin_tl : ∀ B ∈ toModelChain (.Cons s1 tl_sub), B.slot / era.val ≤ B.keyIndex := by
    intro B hB
    rw [MoltPetit.Model.schedPinned, List.all_eq_true] at hPinS
    have hp := hPinS B hB
    exact decide_eq_true_iff.mp hp
  have hPin_tl' : ∀ B ∈ toModelChain (.Cons s1' tl_sub'), B.slot / era.val ≤ B.keyIndex := by
    intro B hB
    rw [MoltPetit.Model.schedPinned, List.all_eq_true] at hPinS'
    have hp := hPinS' B hB
    exact decide_eq_true_iff.mp hp
  have hPin_full : ∀ B ∈ fullChain G bs (.Cons s1 tl_sub), B.slot / era.val ≤ B.keyIndex := by
    intro B hB
    rw [fullChain, List.mem_append] at hB
    cases hB with
    | inl hhist_mem => exact hPin_hist B hhist_mem
    | inr htl_mem => exact hPin_tl B htl_mem
  have hPin_full' : ∀ B ∈ fullChain G bs' (.Cons s1' tl_sub'), B.slot / era.val ≤ B.keyIndex := by
    intro B hB
    rw [fullChain, List.mem_append] at hB
    cases hB with
    | inl hhist_mem => exact hPin_hist' B hhist_mem
    | inr htl_mem => exact hPin_tl' B htl_mem
  have hSigned_sched : ∀ B ∈ toModelChain (.Cons s1 tl_sub),
      DSigned I crypto n G B ∧ B.slot / era.val ≤ B.keyIndex :=
    fun B hB => ⟨hSigned B hB, hPin_tl B hB⟩
  have hSigned_sched' : ∀ B ∈ toModelChain (.Cons s1' tl_sub'),
      DSigned I crypto n G B ∧ B.slot / era.val ≤ B.keyIndex :=
    fun B hB => ⟨hSigned' B hB, hPin_tl' B hB⟩
  have hRecent : R ≤ sTip.slot + φ := by
    have hrec := recent_ok_sound hrecent
    omega
  have hRecent' : R ≤ sTip'.slot + φ := by
    have hrec' := recent_ok_sound hrecent'
    omega
  have hbridge_sched : ∀ ⦃B : MoltPetit.Model.Block⦄,
      (DSigned I crypto n G B ∧ B.slot / era.val ≤ B.keyIndex) → ∃ r ≤ R, B ∈ log r :=
    fun B ⟨h1, h2⟩ => hbridge h1 h2
  have hagree := MoltPetit.Model.exposure_certified_agreement_on
    hn hexec hClock hBudget hL hL' hbridge_sched
    hcert hcert' hTipS hTipS' hLink hLinks hDense hLink' hLinks' hDense'
    hSigned_sched hSigned_sched' hRecent hRecent' hhist hhist' hDeep hDeep'
  exact ⟨hagree, hPin_full, hPin_full'⟩

/-- **Theorem (deployed schedule agreement)**: mode 2 deployed agreement with schedule pin. -/
theorem rust_deployed_sched_agreement : MoltPaper.thm_rust_deployed_sched_agreement := by
  intro σ ℓ φ δ n q era Δ hn hq hera C I crypto Controlled Stolen log G R R' d hG sG hSigG hexec hClock hBudget hL hL'
        hbridge hφ now now' hNow hNow' hRR cert cert' suffix suffix' hval hval' tl tl' hstr hstr'
        bs bs' ts ts' hts hts' stO stO' hst hst' hA hA' h hDeep hDeep'
  exact @rust_deployed_sched_agreement_one_time σ ℓ φ (δ + d) n q era Δ hn hq hera C I crypto
    Controlled Stolen log G (max R R') hG sG hSigG hexec hClock hBudget hL hL'
    hbridge (by omega) now now' (by omega) (by omega)
    cert cert' suffix suffix' hval hval' tl tl' hstr hstr'
    bs bs' ts ts' hts hts' stO stO' hst hst' hA hA' h hDeep hDeep'

/-! ## Step 16: rustOps and rustRegistry bridge -/

/-- `RustSigned` implies the model `SignedDeclared` under `rustOps` and `rustRegistry`. -/
theorem signedDeclared_of_rustSigned {C} (I : molt_petit.Crypto C) (crypto : C) (n : U64)
    (B : MoltPetit.Model.Block) (h : RustSigned I crypto n B) :
    MoltPetit.Model.SignedDeclared n.val (rustOps I crypto) (rustRegistry I crypto) B := by
  classical
  obtain ⟨b, i, key, sig, hto, hprod, hkey, hver⟩ := h
  have hn : 0 < n.val := by
    have hp := hprod
    unfold molt_petit.producer_for_slot at hp
    change UScalar.rem b.slot n = ok i at hp
    unfold UScalar.rem at hp
    split at hp
    · rename_i hne
      have : n.val ≠ 0 := by simpa using hne
      omega
    · contradiction
  have hc := producer_for_slot_corr n b.slot hn
  rw [hprod] at hc
  have hiv : i.val = MoltPetit.Model.producerForSlot n.val b.slot.val := by
    simpa using hc
  have hBslot : B.slot = b.slot.val := by rw [← hto]; rfl
  have hBkey : B.keyIndex = b.key_index.val := by rw [← hto]; rfl
  refine ⟨sig, ?_⟩
  dsimp [rustOps]
  rw [decide_eq_true_iff]
  refine ⟨b, hto, ?_⟩
  have hprod_eq : MoltPetit.Model.producerForSlot n.val B.slot = i.val := by
    rw [hBslot, ← hiv]
  have hreg :
      rustRegistry I crypto (MoltPetit.Model.producerForSlot n.val B.slot) B.keyIndex = key := by
    rw [hprod_eq, hBkey]
    dsimp [rustRegistry]
    have hex : ∃ key' : Hash, ∃ iu ju : U64,
        iu.val = i.val ∧ ju.val = b.key_index.val ∧ I.key_for crypto iu ju = ok key' := by
      exact ⟨key, i, b.key_index, rfl, rfl, hkey⟩
    rw [dif_pos hex]
    have hspec := Classical.choose_spec hex
    obtain ⟨iu, ju, hiu, hju, hkey'⟩ := hspec
    have hiu_eq : iu = i := UScalar.eq_of_val_eq hiu
    have hju_eq : ju = b.key_index := UScalar.eq_of_val_eq hju
    rw [hiu_eq, hju_eq] at hkey'
    rw [hkey] at hkey'
    injection hkey' with hkey'
    exact hkey'.symm
  rw [hreg]
  exact hver

/-- `DSigned` implies the model `SignedFormed` under `rustOps` and `rustRegistry`. -/
theorem signedFormed_of_dSigned {C} (I : CryptoD C) (crypto : C) (n : U64) (G : Block)
    (B : MoltPetit.Model.Block) (h : DSigned I crypto n G B) :
    MoltPetit.Model.SignedFormed n.val (rustOps I.CryptoInst crypto)
      (rustRegistry I.CryptoInst crypto)
      (RustFormed I crypto n G) B :=
  ⟨signedDeclared_of_rustSigned I.CryptoInst crypto n B h.1, h.2⟩

#print axioms Rust.signedDeclared_of_rustSigned
#print axioms Rust.signedFormed_of_dSigned


lemma groundedHistoryLock_mono {n : Nat} {Signed Signed' : MoltPetit.Model.Block → Prop} {G : MoltPetit.Model.Block}
    {cl : MoltPetit.Model.CertClaim} {g : Nat} {c : MoltPetit.Model.Chain}
    (h : MoltPetit.Model.GroundedHistoryLock n Signed G cl g c)
    (hS : ∀ B ∈ c, Signed B → Signed' B) :
    MoltPetit.Model.GroundedHistoryLock n Signed' G cl g c :=
  ⟨h.valid, h.lock, h.head, h.tip, h.tail_eq, h.len_eq, fun B hB => hS B hB (h.signed B hB), h.gen_max, h.win_const⟩

/-! ## Step 17: rust_deployed_lock_agreement -/

/-- **Theorem (mode 3 deployed lock agreement)**: two clients accepted by `validate_deployed_lock`
agree on every block `2n` deep in their full chains. -/
theorem rust_deployed_lock_agreement : MoltPaper.thm_rust_deployed_lock_agreement := by
  intro n q Δ hn hq C I crypto rosterGen rented Stolen honestSigned G R T now now'
        hP hG sG hSigG cert cert' suffix suffix' hval hval' tl tl' hstr hstr'
        bs bs' ts ts' hts hts' stO stO' gO gO' hst hst' hgen hgen' hA hA' h hDeep hDeep'
  obtain ⟨hval_dep, st1, g1, str1, hst1, hg1, hstr1, hlock1⟩ :=
    validate_deployed_lock_sound hval
  obtain ⟨hval'_dep, st1', g1', str1', hst1', hg1', hstr1', hlock1'⟩ :=
    validate_deployed_lock_sound hval'
  rw [hst] at hst1; injection hst1 with hst1; subst hst1
  rw [hst'] at hst1'; injection hst1' with hst1'; subst hst1'
  rw [hgen] at hg1; injection hg1 with hg1; subst hg1
  rw [hgen'] at hg1'; injection hg1' with hg1'; subst hg1'
  rw [hstr] at hstr1; injection hstr1 with hstr1; subst hstr1
  rw [hstr'] at hstr1'; injection hstr1' with hstr1'; subst hstr1'
  obtain ⟨st, cl, stripped, tip, s1, tl_sub, ts0,
          hst_val, hcl, hstrip, hcons, htip, hverify, hsig, hts_sig, hids, hsuf, hrecent⟩ :=
    validate_deployed_sound hval_dep
  obtain ⟨st', cl', stripped', tip', s1', tl_sub', ts0',
          hst_val', hcl', hstrip', hcons', htip', hverify', hsig', hts_sig', hids', hsuf', hrecent'⟩ :=
    validate_deployed_sound hval'_dep
  rw [hstr] at hstrip; injection hstrip with hstrip; subst hstrip; subst hcons
  rw [hstr'] at hstrip'; injection hstrip' with hstrip'; subst hstrip'; subst hcons'
  rw [hst] at hst_val; injection hst_val with hst_val; subst hst_val
  rw [hst'] at hst_val'; injection hst_val' with hst_val'; subst hst_val'
  rw [hts] at hts_sig; injection hts_sig with hts_sig; subst hts_sig
  rw [hts'] at hts_sig'; injection hts_sig' with hts_sig'; subst hts_sig'
  have htip_rw : molt_petit.tip_slot_from cl.tip_slot (molt_petit.Chain.Cons s1 tl_sub) =
                 molt_petit.tip_slot_from s1.slot tl_sub := by
    rw [molt_petit.tip_slot_from]
  rw [htip_rw] at htip
  obtain ⟨sTip, hTipS, hts_slot⟩ :=
    tip_slot_from_eq_getLast tl_sub s1.slot (toModelBlock s1) rfl htip
  have htip_rw' : molt_petit.tip_slot_from cl'.tip_slot (molt_petit.Chain.Cons s1' tl_sub') =
                  molt_petit.tip_slot_from s1'.slot tl_sub' := by
    rw [molt_petit.tip_slot_from]
  rw [htip_rw'] at htip'
  obtain ⟨sTip', hTipS', hts_slot'⟩ :=
    tip_slot_from_eq_getLast tl_sub' s1'.slot (toModelBlock s1') rfl htip'
  obtain ⟨hcert, hhist, _, hview⟩ := attestsLock_history hn hq hG hSigG hA
  obtain ⟨hcert', hhist', _, hview'⟩ := attestsLock_history hn hq hG hSigG hA'
  have hcv : MoltPetit.Model.claimView (modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)) =
             MoltPetit.Model.claimView (toModelClaim cl) := by
    rw [← hview, claim_of_state_sound hcl]
  have hcv' : MoltPetit.Model.claimView (modelClaimOf n.val (toModelBlock G) ((bs'.map Prod.fst).map toModelBlock)) =
              MoltPetit.Model.claimView (toModelClaim cl') := by
    rw [← hview', claim_of_state_sound hcl']
  obtain ⟨hLink, hLinks, hDense⟩ := validate_suffix_sound_view hTipS hsuf hcv
  obtain ⟨hLink', hLinks', hDense'⟩ := validate_suffix_sound_view hTipS' hsuf' hcv'
  have ⟨_hh, _hs, hp⟩ := hLink
  have ⟨_hh', _hs', hp'⟩ := hLink'
  have ⟨_, T, hT, hSigT, hstO_id, _, _⟩ := foldLockOut_history_formed hSigG hA.1 hA.2
  have ⟨_, T', hT', hSigT', hstO'_id, _, _⟩ := foldLockOut_history_formed hSigG hA'.1 hA'.2
  have h_tipId : (modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)).tipId = hashToNat T.id := by
    have h1 : (modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)).tipId = hashGToNat stO.tip_id := congrArg (fun v => v.1) hview.symm
    rw [h1, hstO_id, hashGToNat_toHashG]
  have hprev_T : (toModelBlock s1).prev = some (hashToNat T.id) := by
    rw [hp, h_tipId]
  have hlinks : ChainLinks T.id (.Cons s1 tl_sub) :=
    chainLinks_of_toModel_linksOk tl_sub hprev_T hLinks
  have hSigned_ds := dsigned_of_sigs_ok_ids_ok hT hSigT hsig hstr hids hlinks
  have h_tipId' : (modelClaimOf n.val (toModelBlock G) ((bs'.map Prod.fst).map toModelBlock)).tipId = hashToNat T'.id := by
    have h1 : (modelClaimOf n.val (toModelBlock G) ((bs'.map Prod.fst).map toModelBlock)).tipId = hashGToNat stO'.tip_id := congrArg (fun v => v.1) hview'.symm
    rw [h1, hstO'_id, hashGToNat_toHashG]
  have hprev_T' : (toModelBlock s1').prev = some (hashToNat T'.id) := by
    rw [hp', h_tipId']
  have hlinks' : ChainLinks T'.id (.Cons s1' tl_sub') :=
    chainLinks_of_toModel_linksOk tl_sub' hprev_T' hLinks'
  have hSigned_ds' := dsigned_of_sigs_ok_ids_ok hT' hSigT' hsig' hstr' hids' hlinks'
  have hhist_sf := groundedHistoryLock_mono hhist
    (fun B _ hB => signedFormed_of_dSigned I crypto n G B hB)
  have hhist_sf' := groundedHistoryLock_mono hhist'
    (fun B _ hB => signedFormed_of_dSigned I crypto n G B hB)
  have hSigned : ∀ B ∈ (toModelBlock s1 :: toModelChain tl_sub),
      MoltPetit.Model.SignedFormed n.val (rustOps I.CryptoInst crypto)
        (rustRegistry I.CryptoInst crypto) (RustFormed I crypto n G) B :=
    fun B hB => signedFormed_of_dSigned I crypto n G B (hSigned_ds B hB)
  have hSigned' : ∀ B ∈ (toModelBlock s1' :: toModelChain tl_sub'),
      MoltPetit.Model.SignedFormed n.val (rustOps I.CryptoInst crypto)
        (rustRegistry I.CryptoInst crypto) (RustFormed I crypto n G) B :=
    fun B hB => signedFormed_of_dSigned I crypto n G B (hSigned_ds' B hB)
  have hLockS_st := lockstep_from_sound (.Cons s1 tl_sub) hlock1
  have hLockS_st' := lockstep_from_sound (.Cons s1' tl_sub') hlock1'
  have hts_eq : (modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)).tipSlot = stO.tip_slot.val := by
    have h := congr_arg (fun v => v.2.1) hview
    exact h.symm
  have hts_eq' : (modelClaimOf n.val (toModelBlock G) ((bs'.map Prod.fst).map toModelBlock)).tipSlot = stO'.tip_slot.val := by
    have h := congr_arg (fun v => v.2.1) hview'
    exact h.symm
  have hLockS : MoltPetit.Model.lockstepFrom n.val
      (modelClaimOf n.val (toModelBlock G) ((bs.map Prod.fst).map toModelBlock)).tipSlot gO.val
      (toModelBlock s1 :: toModelChain tl_sub) = true := by
    rw [hts_eq]
    exact hLockS_st
  have hLockS' : MoltPetit.Model.lockstepFrom n.val
      (modelClaimOf n.val (toModelBlock G) ((bs'.map Prod.fst).map toModelBlock)).tipSlot gO'.val
      (toModelBlock s1' :: toModelChain tl_sub') = true := by
    rw [hts_eq']
    exact hLockS_st'
  have hRecent : min now.val now'.val ≤ sTip.slot + Δ.val := by
    have hrec := recent_ok_sound hrecent
    omega
  have hRecent' : min now.val now'.val ≤ sTip'.slot + Δ.val := by
    have hrec' := recent_ok_sound hrecent'
    omega
  have hagree := MoltPetit.Model.lockstepGen_recent_certified_history_agreement
    hn hP hhist_sf hhist_sf' hTipS hTipS'
    hLink hLinks hDense hLockS hSigned
    hLink' hLinks' hDense' hLockS' hSigned'
    hRecent hRecent' hDeep hDeep'
  exact hagree

#print axioms Rust.rust_deployed_lock_agreement

/-! ## Step 18: rust_deployed_ks -/

/-- **Theorem (deployed knowledge soundness)**: knowledge soundness supplies an attested history. -/
theorem rust_deployed_ks : MoltPaper.thm_rust_deployed_ks := by
  intro n q C I crypto G sG hFold now Δ cert suffix hval
  have hdep : validate_deployed I n now Δ crypto cert suffix = ok true := by
    cases hval with
    | inl h => exact h
    | inr h => exact (validate_deployed_k_sound h).left
  obtain ⟨st, cl, stripped, tip, s1, tl, ts,
          hst_val, hcl, hstrip, hcons, htip, hverify, hsig, hts_sig, hids, hsuf, hrecent⟩ :=
    validate_deployed_sound hdep
  exact hFold cert hverify

#print axioms Rust.rust_deployed_ks

/-- **Theorem (deployed schedule knowledge soundness)**:
knowledge soundness supplies an attested history for mode 2. -/
theorem rust_deployed_sched_ks : MoltPaper.thm_rust_deployed_sched_ks := by
  intro n q era C I crypto G sG hFold now Δ cert suffix hval
  obtain ⟨hval_dep, _⟩ := validate_deployed_sched_sound hval
  obtain ⟨st, cl, stripped, tip, s1, tl, ts,
          hst_val, hcl, hstrip, hcons, htip, hverify, hsig, hts_sig, hids, hsuf, hrecent⟩ :=
    validate_deployed_sound hval_dep
  exact hFold cert hverify

#print axioms Rust.rust_deployed_sched_ks

/-- **Theorem (deployed lockstep knowledge soundness)**:
knowledge soundness supplies an attested history for mode 3. -/
theorem rust_deployed_lock_ks : MoltPaper.thm_rust_deployed_lock_ks := by
  intro n q C I crypto G sG hFold now Δ cert suffix hval
  obtain ⟨hval_dep, _⟩ := validate_deployed_lock_sound hval
  obtain ⟨st, cl, stripped, tip, s1, tl, ts,
          hst_val, hcl, hstrip, hcons, htip, hverify, hsig, hts_sig, hids, hsuf, hrecent⟩ :=
    validate_deployed_sound hval_dep
  exact hFold cert hverify

#print axioms Rust.rust_deployed_lock_ks

/-! ## Step 19: rust_produce_block_deployed_live -/

theorem signed_tip_id_from_total (cur : Hash) (sc : SignedChain) :
    ∃ h : Hash, signed_tip_id_from cur sc = ok h := by
  induction sc generalizing cur with
  | SNil =>
    rw [signed_tip_id_from]
    exact ⟨cur, rfl⟩
  | SCons b s tl ih =>
    rw [signed_tip_id_from]
    exact ih b.id

theorem signed_tip_sig_from_total (cur : Hash) (sc : SignedChain) :
    ∃ h : Hash, signed_tip_sig_from cur sc = ok h := by
  induction sc generalizing cur with
  | SNil =>
    rw [signed_tip_sig_from]
    exact ⟨cur, rfl⟩
  | SCons b s tl ih =>
    rw [signed_tip_sig_from]
    exact ih s

theorem append_signed_total (sc : SignedChain) (nb : Block) (sig : Hash) :
    ∃ sc' : SignedChain, append_signed sc nb sig = ok sc' := by
  induction sc with
  | SNil =>
    rw [append_signed]
    exact ⟨SignedChain.SCons nb sig SignedChain.SNil, rfl⟩
  | SCons b s tl ih =>
    obtain ⟨sc1, hsc1⟩ := ih
    rw [append_signed, hsc1]
    exact ⟨SignedChain.SCons b s sc1, rfl⟩

theorem strip_sigs_append_signed : ∀ (sc : SignedChain) (nb : Block) (sig : Hash) (tl : Chain),
    strip_sigs sc = ok tl →
    ∃ (tl' : Chain) (sc' : SignedChain),
      append_signed sc nb sig = ok sc' ∧
      strip_sigs sc' = ok tl' ∧
      toModelChain tl' = toModelChain tl ++ [toModelBlock nb] := by
  intro sc
  induction sc with
  | SNil =>
    intro nb sig tl hstrip
    rw [strip_sigs] at hstrip
    injection hstrip with hstrip; subst hstrip
    rw [append_signed]
    refine ⟨Chain.Cons nb Chain.Nil, SignedChain.SCons nb sig SignedChain.SNil, rfl, ?_, ?_⟩
    · rw [strip_sigs, strip_sigs]
      rfl
    · rfl
  | SCons b s rest ih =>
    intro nb sig tl hstrip
    rw [strip_sigs] at hstrip
    obtain ⟨c, hc, hstrip⟩ := bind_inv hstrip
    injection hstrip with hstrip; subst hstrip
    obtain ⟨tl', sc', happ, hstrip', hmodel⟩ := ih nb sig c hc
    rw [append_signed, happ]
    simp only [bind_tc_ok]
    refine ⟨Chain.Cons b tl', SignedChain.SCons b s sc', rfl, ?_, ?_⟩
    · rw [strip_sigs, hstrip']
      rfl
    · rw [toModelChain_cons, toModelChain_cons, hmodel, List.cons_append]


theorem ids_ok_append_signed {C} {I : CryptoD C} {crypto : C} :
    ∀ (sc : SignedChain) (nb : Block) (sig : Hash) (ts : Hash) (last_sig : Hash) (sc' : SignedChain),
      append_signed sc nb sig = ok sc' →
      signed_tip_sig_from ts sc = ok last_sig →
      I.block_id crypto nb.slot nb.height nb.prev (some last_sig) nb.contents_hash nb.key_index = ok nb.id →
      ids_ok I crypto (some ts) sc = ok true →
      ids_ok I crypto (some ts) sc' = ok true := by
  intro sc
  induction sc with
  | SNil =>
    intro nb sig ts last_sig sc' happ hts hbid hids
    rw [append_signed] at happ
    injection happ with happ; subst happ
    rw [signed_tip_sig_from] at hts
    injection hts with hts; subst hts
    rw [ids_ok.eq_def]
    simp only [bind_tc_ok, hbid, hash_eq_self]
    rw [ids_ok.eq_def]
    rfl
  | SCons b s rest ih =>
    intro nb sig ts last_sig sc' happ hts hbid hids
    rw [append_signed] at happ
    obtain ⟨sc1, hsc1, happ⟩ := bind_inv happ
    injection happ with happ; subst happ
    rw [signed_tip_sig_from] at hts
    rw [ids_ok.eq_def] at hids
    obtain ⟨id, hid, hids⟩ := bind_inv hids
    obtain ⟨b1, hb1, hids⟩ := bind_inv hids
    split at hids
    · rename_i hb1t; subst hb1t
      rw [ids_ok.eq_def]
      simp only [bind_tc_ok, hid, hb1]
      exact ih nb sig s last_sig sc1 hsc1 hts hbid hids
    · simp at hids

theorem sigs_ok_append_signed {C} {I : Crypto C} {n : U64} {crypto : C} :
    ∀ (sc : SignedChain) (nb : Block) (sig : Hash) (me : U64) (key : Hash) (sc' : SignedChain),
      append_signed sc nb sig = ok sc' →
      producer_for_slot n nb.slot = ok me →
      I.key_for crypto me nb.key_index = ok key →
      I.verify crypto key nb sig = ok true →
      sigs_ok I n crypto sc = ok true →
      sigs_ok I n crypto sc' = ok true := by
  intro sc
  induction sc with
  | SNil =>
    intro nb sig me key sc' happ hprod hkey hver hsig
    rw [append_signed] at happ
    injection happ with happ; subst happ
    rw [sigs_ok]
    simp only [bind_tc_ok, hprod, hkey, hver]
    rw [sigs_ok]
    rfl
  | SCons b s rest ih =>
    intro nb sig me key sc' happ hprod hkey hver hsig
    rw [append_signed] at happ
    obtain ⟨sc1, hsc1, happ⟩ := bind_inv happ
    injection happ with happ; subst happ
    rw [sigs_ok] at hsig
    obtain ⟨i, hi, hsig⟩ := bind_inv hsig
    obtain ⟨k, hk, hsig⟩ := bind_inv hsig
    obtain ⟨v, hv, hsig⟩ := bind_inv hsig
    split at hsig
    · rename_i hvt; subst hvt
      rw [sigs_ok]
      simp only [bind_tc_ok, hi, hk, hv]
      exact ih nb sig me key sc1 hsc1 hprod hkey hver hsig
    · simp at hsig

theorem window_count_complete : ∀ (c : Chain) (u len : U64),
    u.val + len.val < 2 ^ 64 →
    MoltPetit.Model.windowCount (toModelChain c) u.val len.val < 2 ^ 64 →
    ∃ w : U64, window_count c u len = ok w ∧
      w.val = MoltPetit.Model.windowCount (toModelChain c) u.val len.val := by
  intro c
  induction c with
  | Nil =>
    intro u len _ _
    rw [window_count]
    refine ⟨0#u64, rfl, ?_⟩
    simp [toModelChain, MoltPetit.Model.windowCount]
  | Cons b tl ih =>
    intro u len hun hwc
    rw [toModelChain_cons, model_windowCount_cons] at hwc
    have hwc_tl : MoltPetit.Model.windowCount (toModelChain tl) u.val len.val < 2 ^ 64 := by omega
    obtain ⟨rest, hrest, hrest_val⟩ := ih u len hun hwc_tl
    obtain ⟨hi, hhi, hhi_val⟩ := u64_add_ok hun
    have h1_val : (1#u64 : U64).val = 1 := rfl
    have h0_val : (0#u64 : U64).val = 0 := rfl
    rw [window_count]
    split
    · rename_i hu_le
      have h1 : u.val ≤ b.slot.val := by scalar_tac
      rw [hhi]
      simp only [bind_tc_ok]
      split
      · rename_i hlt
        have h2 : b.slot.val < u.val + len.val := by
          have : b.slot.val < hi.val := by scalar_tac
          omega
        have hinw : MoltPetit.Model.blockInWindow u.val len.val (toModelBlock b) = true := by
          dsimp [MoltPetit.Model.blockInWindow, toModelBlock]
          simp [h1, h2]
        have hsum : (1#u64 : U64).val + rest.val < 2 ^ 64 := by
          rw [hinw] at hwc
          simp only [Bool.true_and, ite_true] at hwc
          rw [h1_val]
          omega
        obtain ⟨w, hw, hw_val⟩ := u64_add_ok (x := 1#u64) (y := rest) hsum
        rw [hrest]
        simp only [bind_tc_ok]
        rw [hw]
        refine ⟨w, rfl, ?_⟩
        rw [hw_val, hrest_val, h1_val, toModelChain_cons, model_windowCount_cons, hinw]
        simp
      · rename_i hnlt
        have h2 : ¬ (b.slot.val < u.val + len.val) := by
          have : ¬ (b.slot.val < hi.val) := by scalar_tac
          omega
        have hinw : MoltPetit.Model.blockInWindow u.val len.val (toModelBlock b) = false := by
          dsimp [MoltPetit.Model.blockInWindow, toModelBlock]
          simp [h2]
        have hsum : (0#u64 : U64).val + rest.val < 2 ^ 64 := by
          rw [h0_val]; omega
        obtain ⟨w, hw, hw_val⟩ := u64_add_ok (x := 0#u64) (y := rest) hsum
        rw [hrest]
        simp only [bind_tc_ok]
        rw [hw]
        refine ⟨w, rfl, ?_⟩
        rw [hw_val, hrest_val, h0_val, toModelChain_cons, model_windowCount_cons, hinw]
        simp
    · rename_i hnot_le
      have h1 : ¬ (u.val ≤ b.slot.val) := by scalar_tac
      have hinw : MoltPetit.Model.blockInWindow u.val len.val (toModelBlock b) = false := by
        dsimp [MoltPetit.Model.blockInWindow, toModelBlock]
        simp [h1]
      have hsum : (0#u64 : U64).val + rest.val < 2 ^ 64 := by
        rw [h0_val]; omega
      obtain ⟨w, hw, hw_val⟩ := u64_add_ok (x := 0#u64) (y := rest) hsum
      rw [hrest]
      simp only [bind_tc_ok]
      rw [hw]
      refine ⟨w, rfl, ?_⟩
      rw [hw_val, hrest_val, h0_val, toModelChain_cons, model_windowCount_cons, hinw]
      simp


theorem window_dense_complete {c : Chain} {u n : U64}
    (h_u_n : u.val + n.val < 2 ^ 64)
    (h_wc : MoltPetit.Model.windowCount (toModelChain c) u.val n.val < 2 ^ 64)
    (hn : n.val < 2 ^ 62)
    (hdense : MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (toModelChain c) u.val n.val) :
    window_dense n c u = ok true := by
  have hn_max : 2 * n.val + 2 ≤ U64.max := by scalar_tac
  obtain ⟨q, hq, hqv⟩ := molt_petit.spec_ok_exists (quorum_corr n hn_max)
  obtain ⟨w, hw, hw_val⟩ := window_count_complete c u n h_u_n h_wc
  rw [window_dense]
  simp only [bind_tc_ok, hq, hw]
  have hle : q ≤ w := by
    have : q.val ≤ w.val := by rw [hqv, hw_val]; exact hdense
    scalar_tac
  exact congrArg ok (decide_eq_true hle)

theorem anchors_dense_complete : ∀ (all rest : Chain) (lo t n : U64),
    (∀ b ∈ toModelChain rest, b.slot < 2 ^ 62) →
    (∀ b ∈ toModelChain all, b.slot < 2 ^ 62) →
    (∀ u, MoltPetit.Model.windowCount (toModelChain all) u n.val < 2 ^ 64) →
    t.val < 2 ^ 62 →
    n.val < 2 ^ 62 →
    (∀ u, lo.val ≤ u → u + n.val ≤ t.val + 1 →
      MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (toModelChain all) u n.val) →
    anchors_dense all rest lo t n = ok true := by
  intro all rest
  induction rest with
  | Nil =>
    intro lo t n _ _ _ _ _ _
    rw [anchors_dense]
  | Cons b tl ih =>
    intro lo t n hrest_bound hall_bound hwc ht hn hdense
    have hb_bound : b.slot.val < 2 ^ 62 := by
      have : toModelBlock b ∈ toModelChain (Chain.Cons b tl) := by simp [toModelChain]
      exact hrest_bound (toModelBlock b) this
    have htl_bound : ∀ x ∈ toModelChain tl, x.slot < 2 ^ 62 := by
      intro x hx
      have : x ∈ toModelChain (Chain.Cons b tl) := by simp [toModelChain, hx]
      exact hrest_bound x this
    have h1_val : (1#u64 : U64).val = 1 := rfl
    obtain ⟨u, hu, hu_val⟩ := u64_add_ok (x := b.slot) (y := 1#u64) (by rw [h1_val]; omega)
    obtain ⟨upn, hupn, hupn_val⟩ := u64_add_ok (x := u) (y := n) (by rw [hu_val]; omega)
    obtain ⟨t11, ht11, ht11_val⟩ := u64_add_ok (x := t) (y := 1#u64) (by rw [h1_val]; omega)
    have hu_n_bound : u.val + n.val < 2 ^ 64 := by rw [hu_val]; omega
    have hrest_ok := ih lo t n htl_bound hall_bound hwc ht hn hdense
    rw [anchors_dense]
    simp only [bind_tc_ok, hu]
    split
    · rename_i hlo_u
      simp only [bind_tc_ok, hupn, ht11]
      split
      · rename_i hupn_t11
        have h1_le : lo.val ≤ u.val := by scalar_tac
        have h2_le : u.val + n.val ≤ t.val + 1 := by
          have : upn.val ≤ t11.val := by scalar_tac
          rw [hupn_val, ht11_val] at this
          exact this
        have hd := hdense u.val h1_le h2_le
        have hwd := window_dense_complete (c := all) hu_n_bound (hwc u.val) hn hd
        simp only [bind_tc_ok, hwd]
        exact hrest_ok
      · exact hrest_ok
    · exact hrest_ok

theorem matured_dense_complete {c : Chain} {lo t n : U64}
    (hbound : ∀ b ∈ toModelChain c, b.slot < 2 ^ 62)
    (hwc : ∀ u, MoltPetit.Model.windowCount (toModelChain c) u n.val < 2 ^ 64)
    (hlo : lo.val < 2 ^ 62)
    (ht : t.val < 2 ^ 62)
    (hn : n.val < 2 ^ 62)
    (hdense : ∀ u, lo.val ≤ u → u + n.val ≤ t.val + 1 →
      MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (toModelChain c) u n.val) :
    matured_dense c lo t n = ok true := by
  have h1_val : (1#u64 : U64).val = 1 := rfl
  obtain ⟨lpn, hlpn, hlpn_val⟩ := u64_add_ok (x := lo) (y := n) (by omega)
  obtain ⟨t11, ht11, ht11_val⟩ := u64_add_ok (x := t) (y := 1#u64) (by rw [h1_val]; omega)
  have hanch := anchors_dense_complete c c lo t n hbound hbound hwc ht hn hdense
  rw [matured_dense]
  simp only [bind_tc_ok, hlpn, ht11]
  split
  · rename_i hlpn_t11
    have hle : lo.val + n.val ≤ t.val + 1 := by
      have : lpn.val ≤ t11.val := by scalar_tac
      rw [hlpn_val, ht11_val] at this
      exact this
    have hd := hdense lo.val (by omega) hle
    have hwd := window_dense_complete (c := c) (by omega) (hwc lo.val) hn hd
    simp only [bind_tc_ok, hwd, ite_true]
    exact hanch
  · simp only [bind_tc_ok, ite_true]
    exact hanch


theorem clone_chain_total (c : Chain) : ∃ r, clone_chain c = ok r := by
  induction c with
  | Nil =>
    rw [clone_chain]
    exact ⟨Chain.Nil, rfl⟩
  | Cons b tl ih =>
    obtain ⟨r, hr⟩ := ih
    rw [clone_chain, hr]
    exact ⟨Chain.Cons b r, rfl⟩

theorem append_suffix_to_buffer_total (buf sfx : Chain) : ∃ r, append_suffix_to_buffer buf sfx = ok r := by
  induction buf with
  | Nil =>
    obtain ⟨r, hr⟩ := clone_chain_total sfx
    rw [append_suffix_to_buffer, hr]
    exact ⟨r, rfl⟩
  | Cons b tl ih =>
    obtain ⟨r, hr⟩ := ih
    rw [append_suffix_to_buffer, hr]
    exact ⟨Chain.Cons b r, rfl⟩

theorem child_ok_intro {p c : Block}
    (hp : c.prev = some p.id)
    (hh : p.height + 1#u64 = ok c.height)
    (hs : p.slot < c.slot) :
    child_ok p c = ok true := by
  rw [child_ok, hp]
  simp only [bind_tc_ok, hash_eq_self]
  change (do
    let i ← p.height + 1#u64
    if c.height = i then if p.slot < c.slot then ok true else ok false else ok false) = ok true
  rw [hh]
  simp only [bind_tc_ok, hs, ite_true]

theorem links_to_claim_intro {cl : CertClaim} {s1 : Block}
    (hp : s1.prev = some cl.tip_id)
    (hh : cl.tip_height + 1#u64 = ok s1.height)
    (hs : cl.tip_slot < s1.slot) :
    links_to_claim cl s1 = ok true := by
  rw [links_to_claim, hp]
  simp only [bind_tc_ok, hash_eq_self]
  change (do
    let i ← cl.tip_height + 1#u64
    if s1.height = i then if cl.tip_slot < s1.slot then ok true else ok false else ok false) = ok true
  rw [hh]
  simp only [bind_tc_ok, hs, ite_true]


def chain_append : Chain → Block → Chain
  | Chain.Nil, nb => Chain.Cons nb Chain.Nil
  | Chain.Cons b tl, nb => Chain.Cons b (chain_append tl nb)

theorem toModelChain_chain_append (tl : Chain) (nb : Block) :
    toModelChain (chain_append tl nb) = toModelChain tl ++ [toModelBlock nb] := by
  induction tl with
  | Nil => rfl
  | Cons b rest ih =>
    simp only [chain_append, toModelChain_cons, ih, List.cons_append]

theorem strip_sigs_append_signed_eq : ∀ (sc : SignedChain) (nb : Block) (sig : Hash) (tl : Chain) (sc' : SignedChain),
    strip_sigs sc = ok tl →
    append_signed sc nb sig = ok sc' →
    strip_sigs sc' = ok (chain_append tl nb) := by
  intro sc
  induction sc with
  | SNil =>
    intro nb sig tl sc' hstr happ
    rw [strip_sigs] at hstr
    injection hstr with hstr; subst hstr
    rw [append_signed] at happ
    injection happ with happ; subst happ
    rw [chain_append, strip_sigs, strip_sigs]
    rfl
  | SCons b s rest ih =>
    intro nb sig tl sc' hstr happ
    rw [strip_sigs] at hstr
    obtain ⟨c, hc, hstr⟩ := bind_inv hstr
    injection hstr with hstr; subst hstr
    rw [append_signed] at happ
    obtain ⟨sc1, hsc1, happ⟩ := bind_inv happ
    injection happ with happ; subst happ
    rw [strip_sigs, ih nb sig c sc1 hc hsc1]
    rfl

theorem tip_slot_from_chain_append : ∀ (c : Chain) (cur : U64) (nb : Block),
    tip_slot_from cur (chain_append c nb) = ok nb.slot := by
  intro c
  induction c with
  | Nil =>
    intro cur nb
    rw [chain_append, tip_slot_from, tip_slot_from]
  | Cons b tl ih =>
    intro cur nb
    rw [chain_append, tip_slot_from]
    exact ih b.slot nb


theorem links_from_chain_append_nil (parent nb : Block) (h : child_ok parent nb = ok true) :
    links_from parent (chain_append Chain.Nil nb) = ok true := by
  rw [chain_append, links_from]
  simp only [bind_tc_ok, h]
  rw [links_from]
  rfl

theorem links_from_chain_append_cons (b : Block) (tl : Chain) (parent nb : Block)
    (hlinks : links_from parent (Chain.Cons b tl) = ok true)
    (hrest : links_from b (chain_append tl nb) = ok true) :
    links_from parent (chain_append (Chain.Cons b tl) nb) = ok true := by
  rw [chain_append, links_from]
  rw [links_from] at hlinks
  obtain ⟨ch, hch, hlinks⟩ := bind_inv hlinks
  split at hlinks
  · rename_i hcht; subst hcht
    simp only [bind_tc_ok, hch]
    exact hrest
  · simp at hlinks

theorem signed_chain_tip_links : ∀ (rest_sc : SignedChain) (b0 : Block) (sig0 : Hash) (rest_tl : Chain),
    strip_sigs rest_sc = ok rest_tl →
    ∀ (curH : U64) (curI : Hash) (curS : U64) (tipH : U64) (tipI : Hash) (tipS : U64) (nb : Block),
      signed_tip_height_from curH (SignedChain.SCons b0 sig0 rest_sc) = ok tipH →
      signed_tip_id_from curI (SignedChain.SCons b0 sig0 rest_sc) = ok tipI →
      tip_slot_from curS (Chain.Cons b0 rest_tl) = ok tipS →
      nb.prev = some tipI →
      tipH + 1#u64 = ok nb.height →
      tipS < nb.slot →
      links_from b0 rest_tl = ok true →
      links_from b0 (chain_append rest_tl nb) = ok true := by
  intro rest_sc
  induction rest_sc with
  | SNil =>
    intro b0 sig0 rest_tl hstr curH curI curS tipH tipI tipS nb hH hI hS hprev hheight hslot _
    rw [strip_sigs] at hstr
    injection hstr with hstr; subst hstr
    rw [signed_tip_height_from, signed_tip_height_from] at hH
    injection hH with hH; subst hH
    rw [signed_tip_id_from, signed_tip_id_from] at hI
    injection hI with hI; subst hI
    rw [tip_slot_from, tip_slot_from] at hS
    injection hS with hS; subst hS
    have hch : child_ok b0 nb = ok true := child_ok_intro hprev hheight hslot
    exact links_from_chain_append_nil b0 nb hch
  | SCons b1 sig1 rest_sc' ih =>
    intro b0 sig0 rest_tl hstr curH curI curS tipH tipI tipS nb hH hI hS hprev hheight hslot hlinks
    rw [strip_sigs] at hstr
    obtain ⟨tl', htl', hstr⟩ := bind_inv hstr
    injection hstr with hstr; subst hstr
    rw [signed_tip_height_from] at hH
    rw [signed_tip_id_from] at hI
    rw [tip_slot_from] at hS
    rw [links_from] at hlinks
    obtain ⟨ch, hch, hlinks_rest⟩ := bind_inv hlinks
    split at hlinks_rest
    · rename_i hcht; subst hcht
      have hrest := ih b1 sig1 tl' htl' b0.height b0.id b0.slot tipH tipI tipS nb hH hI hS hprev hheight hslot hlinks_rest
      have hlinks_cons : links_from b0 (Chain.Cons b1 tl') = ok true := by
        rw [links_from]
        simp only [bind_tc_ok, hch]
        exact hlinks_rest
      exact links_from_chain_append_cons b1 tl' b0 nb hlinks_cons hrest
    · simp at hlinks_rest


theorem blockInWindow_eq_of_slot_eq {u len : Nat} {b1 b2 : MoltPetit.Model.Block}
    (h : b1.slot = b2.slot) :
    MoltPetit.Model.blockInWindow u len b1 = MoltPetit.Model.blockInWindow u len b2 := by
  unfold MoltPetit.Model.blockInWindow
  rw [h]

theorem windowCount_append_singleton_eq (c : MoltPetit.Model.Chain) (u len : Nat)
    (b1 b2 : MoltPetit.Model.Block) (h : b1.slot = b2.slot) :
    MoltPetit.Model.windowCount (c ++ [b1]) u len = MoltPetit.Model.windowCount (c ++ [b2]) u len := by
  unfold MoltPetit.Model.windowCount
  simp only [List.filter_append, List.length_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil]
  rw [blockInWindow_eq_of_slot_eq h]
  split <;> rfl

theorem child_ok_slot_lt {p c : Block} (h : child_ok p c = ok true) :
    p.slot.val < c.slot.val := by
  have hch := child_ok_sound h
  exact (MoltPetit.Model.childOk_iff.mp hch).2.1

theorem links_to_claim_slot_lt {cl : CertClaim} {s1 : Block} (h : links_to_claim cl s1 = ok true) :
    cl.tip_slot.val < s1.slot.val := by
  have hl := links_to_claim_sound h
  exact hl.2.1

theorem links_from_tip_slot_le : ∀ (tl : Chain) (parent : Block) (tipS : U64),
    links_from parent tl = ok true →
    tip_slot_from parent.slot tl = ok tipS →
    (∀ b ∈ toModelChain tl, b.slot ≤ tipS.val) ∧ (tl ≠ Chain.Nil → parent.slot.val < tipS.val) := by
  intro tl
  induction tl with
  | Nil =>
    intro parent tipS _ htipS
    rw [tip_slot_from] at htipS
    injection htipS with htipS; subst htipS
    refine ⟨by simp [toModelChain], fun h => (h rfl).elim⟩
  | Cons b1 tl' ih =>
    intro parent tipS hlinks htipS
    rw [links_from] at hlinks
    obtain ⟨ch, hch, hlinks⟩ := bind_inv hlinks
    split at hlinks
    · rename_i hcht; subst hcht
      have hslot_lt : parent.slot.val < b1.slot.val := child_ok_slot_lt hch
      rw [tip_slot_from] at htipS
      have ih' := ih b1 tipS hlinks htipS
      cases tl' with
      | Nil =>
        rw [tip_slot_from] at htipS
        injection htipS with htipS; subst htipS
        refine ⟨?_, fun _ => hslot_lt⟩
        intro b hb
        simp only [toModelChain_cons, toModelChain_nil, List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb
        rfl
      | Cons b2 tl'' =>
        have hne : Chain.Cons b2 tl'' ≠ Chain.Nil := by intro; contradiction
        have hb1_lt : b1.slot.val < tipS.val := ih'.2 hne
        refine ⟨?_, fun _ => by omega⟩
        intro b hb
        simp only [toModelChain_cons, List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact Nat.le_of_lt hb1_lt
        · exact ih'.1 b (by simp only [toModelChain_cons, List.mem_cons]; exact hb)
    · simp at hlinks

theorem claim_tip_slot_le_tipS {n : U64} {cl : CertClaim} {tl : Chain} {tipS : U64}
    (hsuf : validate_suffix n cl tl = ok true)
    (htipS : tip_slot_from cl.tip_slot tl = ok tipS) :
    cl.tip_slot.val ≤ tipS.val ∧ (∀ b ∈ toModelChain tl, b.slot ≤ tipS.val) := by
  cases tl with
  | Nil =>
    rw [tip_slot_from] at htipS
    injection htipS with htipS; subst htipS
    exact ⟨Nat.le_refl _, by simp [toModelChain]⟩
  | Cons b0 rest_tl =>
    rw [validate_suffix] at hsuf
    obtain ⟨link, hlink, hsuf⟩ := bind_inv hsuf
    obtain ⟨links, hlinks, hsuf⟩ := bind_inv hsuf
    obtain ⟨ts, hts, hsuf⟩ := bind_inv hsuf
    obtain ⟨buf, hbuf, hsuf⟩ := bind_inv hsuf
    obtain ⟨lo, hlo, hsuf⟩ := bind_inv hsuf
    split at hsuf; rotate_right
    · simp at hsuf
    rename_i hlinkt
    split at hsuf; rotate_right
    · simp at hsuf
    rename_i hlinkst
    rw [hlinkt] at hlink
    rw [hlinkst] at hlinks
    rw [tip_slot_from] at htipS
    have hts_eq : ts = tipS := by
      rw [hts] at htipS; cases htipS; rfl
    have hlt1 := links_to_claim_slot_lt hlink
    have hle2 := links_from_tip_slot_le rest_tl b0 ts hlinks hts
    rw [hts_eq] at hle2
    refine ⟨?_, ?_⟩
    · cases rest_tl with
      | Nil =>
        rw [tip_slot_from] at hts
        injection hts with hts; subst hts
        rw [hts_eq] at hlt1
        exact Nat.le_of_lt hlt1
      | Cons b1 tl' =>
        have hne : Chain.Cons b1 tl' ≠ Chain.Nil := by intro; contradiction
        have := hle2.2 hne
        omega
    · intro b hb
      simp only [toModelChain_cons, List.mem_cons] at hb
      rcases hb with rfl | hb
      · cases rest_tl with
        | Nil =>
          rw [tip_slot_from] at hts
          injection hts with hts; subst hts
          rw [show (toModelBlock b0).slot = b0.slot.val by rfl]
          rw [hts_eq]
        | Cons b1 tl' =>
          have hne : Chain.Cons b1 tl' ≠ Chain.Nil := by intro; contradiction
          have := hle2.2 hne
          have : (toModelBlock b0).slot = b0.slot.val := rfl
          omega
      · exact hle2.1 b hb

theorem validate_suffix_append
    {n at_slot tipS tipH : U64} {cl : CertClaim} {suffix : SignedChain} {tl : Chain}
    {tipI : Hash} {nb : Block}
    (hn : 1 ≤ n.val)
    (hsmall : n.val < 2 ^ 62)
    (hS : at_slot.val < 2 ^ 62)
    (hstr : strip_sigs suffix = ok tl)
    (hsuf : validate_suffix n cl tl = ok true)
    (htipS : tip_slot_from cl.tip_slot tl = ok tipS)
    (htipH : signed_tip_height_from cl.tip_height suffix = ok tipH)
    (htipI : signed_tip_id_from cl.tip_id suffix = ok tipI)
    (hLt : tipS.val < at_slot.val)
    (hH : tipH.val + 1 < 2 ^ 64)
    (htail : ∀ B ∈ toModelChain cl.tail, B.slot ≤ cl.tip_slot.val)
    (hlen : (toModelChain cl.tail).length + (toModelChain tl).length < 2 ^ 62)
    (hnb_slot : nb.slot = at_slot)
    (hnb_prev : nb.prev = some tipI)
    (hnb_height : tipH + 1#u64 = ok nb.height)
    (hDense : ∀ u : Nat, tipS.val + 2 ≤ u + n.val → u + n.val ≤ at_slot.val + 1 →
      MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount
        ((toModelClaim cl).tail ++ toModelChain tl ++
          [{ slot := at_slot.val, height := 0, prev := none, id := 0, contentsHash := 0,
             keyIndex := 0 }]) u n.val) :
    validate_suffix n cl (chain_append tl nb) = ok true := by
  have h_cl_tip := claim_tip_slot_le_tipS hsuf htipS
  have hcl_tip_lt_S : cl.tip_slot.val < at_slot.val := by omega
  have hcl_tip_bound : cl.tip_slot.val < 2 ^ 62 := by omega
  obtain ⟨lo, hlo⟩ := suffix_lo_total n cl.tip_slot (by omega)
  have hlov : lo.val = cl.tip_slot.val + 2 - n.val := suffix_lo_val hlo
  have hlo_bound : lo.val < 2 ^ 62 := by omega
  have hLt_u64 : tipS < nb.slot := by
    rw [hnb_slot]
    scalar_tac
  cases suffix with
  | SNil =>
    rw [strip_sigs] at hstr
    injection hstr with hstr; subst hstr
    rw [signed_tip_height_from] at htipH
    injection htipH with htipH; subst htipH
    rw [signed_tip_id_from] at htipI
    injection htipI with htipI; subst htipI
    rw [tip_slot_from] at htipS
    injection htipS with htipS_eq
    have hlink_nb : links_to_claim cl nb = ok true := by
      refine links_to_claim_intro hnb_prev hnb_height ?_
      rw [hnb_slot]
      have : cl.tip_slot.val < at_slot.val := by omega
      scalar_tac
    have hlinks_nb : links_from nb Chain.Nil = ok true := by rw [links_from]
    have htip_nb : tip_slot_from nb.slot Chain.Nil = ok nb.slot := by rw [tip_slot_from]
    obtain ⟨buf, hbuf⟩ := append_suffix_to_buffer_total cl.tail (Chain.Cons nb Chain.Nil)
    have hbuf_corr := append_suffix_corr cl.tail (Chain.Cons nb Chain.Nil) hbuf
    simp only [chain_append, validate_suffix, bind_tc_ok, hlink_nb, hlinks_nb, htip_nb, hbuf, hlo, ite_true]
    have hbuf_model : toModelChain buf = toModelChain cl.tail ++ [toModelBlock nb] := by
      rw [hbuf_corr, toModelChain_cons, toModelChain_nil]
    have hbound : ∀ b ∈ toModelChain buf, b.slot < 2 ^ 62 := by
      intro b hb
      rw [hbuf_model] at hb
      simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with htail_b | rfl
      · have := htail b htail_b
        omega
      · have : (toModelBlock nb).slot = nb.slot.val := rfl
        rw [this, hnb_slot]
        exact hS
    have hwc : ∀ u, MoltPetit.Model.windowCount (toModelChain buf) u n.val < 2 ^ 64 := by
      intro u
      have hwcle := windowCount_le_length (toModelChain buf) u n.val
      have hlen_buf : (toModelChain buf).length = (toModelChain cl.tail).length + 1 := by
        rw [hbuf_model]
        simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hdense_all : ∀ u, lo.val ≤ u → u + n.val ≤ nb.slot.val + 1 →
        MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (toModelChain buf) u n.val := by
      intro u hlo_u hu_nb
      rw [hbuf_model]
      rw [windowCount_append_singleton_eq (toModelChain cl.tail) u n.val (toModelBlock nb)
        { slot := at_slot.val, height := 0, prev := none, id := 0, contentsHash := 0, keyIndex := 0 }
        (by show (toModelBlock nb).slot = at_slot.val; rw [show (toModelBlock nb).slot = nb.slot.val by rfl, hnb_slot])]
      have hsub_add : cl.tip_slot.val + 2 ≤ lo.val + n.val := by
        rw [hlov]
        omega
      have hu_dense : tipS.val + 2 ≤ u + n.val := by
        rw [← htipS_eq]
        omega
      have hu_dense2 : u + n.val ≤ at_slot.val + 1 := by rw [hnb_slot] at hu_nb; exact hu_nb
      have hd := hDense u hu_dense hu_dense2
      rw [show (toModelChain Chain.Nil : List MoltPetit.Model.Block) = [] by rfl, List.append_nil] at hd
      exact hd
    have hnb_slot_bound : nb.slot.val < 2 ^ 62 := by rw [hnb_slot]; exact hS
    exact matured_dense_complete hbound hwc hlo_bound hnb_slot_bound hsmall hdense_all
  | SCons b0 sig0 rest_sc =>
    rw [strip_sigs] at hstr
    obtain ⟨rest_tl, hrest_tl, hstr⟩ := bind_inv hstr
    injection hstr with hstr; subst hstr
    rw [validate_suffix] at hsuf
    obtain ⟨link0, hlink0, hsuf⟩ := bind_inv hsuf
    obtain ⟨links0, hlinks0, hsuf⟩ := bind_inv hsuf
    obtain ⟨ts0, hts0, hsuf⟩ := bind_inv hsuf
    obtain ⟨buf0, hbuf0, hsuf⟩ := bind_inv hsuf
    obtain ⟨lo0, hlo0, hsuf⟩ := bind_inv hsuf
    split at hsuf; rotate_right
    · simp at hsuf
    rename_i hlink0_t
    split at hsuf; rotate_right
    · simp at hsuf
    rename_i hlinks0_t
    rw [hlink0_t] at hlink0
    rw [hlinks0_t] at hlinks0
    have htipS_saved := htipS
    rw [tip_slot_from] at htipS
    have hts0_eq : ts0 = tipS := by
      rw [hts0] at htipS; cases htipS; rfl
    have hlo0_eq : lo0 = lo := by
      rw [hlo] at hlo0; cases hlo0; rfl
    rw [hts0_eq, hlo0_eq] at hsuf
    have hbuf0_corr := append_suffix_corr cl.tail (Chain.Cons b0 rest_tl) hbuf0
    have hlinks_app : links_from b0 (chain_append rest_tl nb) = ok true := by
      exact signed_chain_tip_links rest_sc b0 sig0 rest_tl hrest_tl cl.tip_height cl.tip_id cl.tip_slot
        tipH tipI tipS nb htipH htipI htipS_saved hnb_prev hnb_height hLt_u64 hlinks0
    have htip_app := tip_slot_from_chain_append rest_tl b0.slot nb
    obtain ⟨buf, hbuf⟩ := append_suffix_to_buffer_total cl.tail (Chain.Cons b0 (chain_append rest_tl nb))
    have hbuf_corr := append_suffix_corr cl.tail (Chain.Cons b0 (chain_append rest_tl nb)) hbuf
    simp only [chain_append, validate_suffix, bind_tc_ok, hlink0, hlinks_app, htip_app, hbuf, hlo, ite_true]
    have hbuf_model : toModelChain buf = toModelChain cl.tail ++ toModelChain (Chain.Cons b0 rest_tl) ++ [toModelBlock nb] := by
      rw [hbuf_corr, toModelChain_cons, toModelChain_chain_append, toModelChain_cons]
      rw [← List.cons_append, List.append_assoc]
    have hbound : ∀ b ∈ toModelChain buf, b.slot < 2 ^ 62 := by
      intro b hb
      rw [hbuf_model] at hb
      simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with (htail_b | htl_b) | rfl
      · have := htail b htail_b; omega
      · have := h_cl_tip.2 b htl_b; omega
      · have : (toModelBlock nb).slot = nb.slot.val := rfl
        rw [this, hnb_slot]
        exact hS
    have hwc : ∀ u, MoltPetit.Model.windowCount (toModelChain buf) u n.val < 2 ^ 64 := by
      intro u
      have hwcle := windowCount_le_length (toModelChain buf) u n.val
      have hlen_buf : (toModelChain buf).length = (toModelChain cl.tail).length + (toModelChain (Chain.Cons b0 rest_tl)).length + 1 := by
        rw [hbuf_model]
        simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hdense_all : ∀ u, lo.val ≤ u → u + n.val ≤ nb.slot.val + 1 →
        MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (toModelChain buf) u n.val := by
      intro u hlo_u hu_nb
      by_cases hu_tip : tipS.val + 2 ≤ u + n.val
      · rw [hbuf_model]
        rw [windowCount_append_singleton_eq (toModelChain cl.tail ++ toModelChain (Chain.Cons b0 rest_tl)) u n.val (toModelBlock nb)
          { slot := at_slot.val, height := 0, prev := none, id := 0, contentsHash := 0, keyIndex := 0 }
          (by show (toModelBlock nb).slot = at_slot.val; rw [show (toModelBlock nb).slot = nb.slot.val by rfl, hnb_slot])]
        have hu_dense2 : u + n.val ≤ at_slot.val + 1 := by rw [hnb_slot] at hu_nb; exact hu_nb
        exact hDense u hu_tip hu_dense2
      · have hu_tip_le : u + n.val ≤ tipS.val + 1 := by omega
        have hmd0 := matured_dense_sound hsuf u hlo_u hu_tip_le
        rw [hbuf0_corr] at hmd0
        rw [hbuf_model]
        have hmono : MoltPetit.Model.windowCount (toModelChain cl.tail ++ toModelChain (Chain.Cons b0 rest_tl)) u n.val ≤
            MoltPetit.Model.windowCount (toModelChain cl.tail ++ toModelChain (Chain.Cons b0 rest_tl) ++ [toModelBlock nb]) u n.val := by
          conv_rhs => rw [MoltPetit.Model.windowCount_append]
          exact Nat.le_add_right _ _
        exact Nat.le_trans hmd0 hmono
    have hnb_slot_bound : nb.slot.val < 2 ^ 62 := by rw [hnb_slot]; exact hS
    exact matured_dense_complete hbound hwc hlo_bound hnb_slot_bound hsmall hdense_all

theorem is_nil_chain_append (tl : Chain) (nb : Block) :
    is_nil (chain_append tl nb) = ok false := by
  cases tl with
  | Nil => rfl
  | Cons b rest => rfl

theorem recent_ok_self (now delta : U64) :
    recent_ok now delta now = ok true := by
  rw [recent_ok]
  split_ifs with hle
  · rfl
  · exfalso
    exact hle (by scalar_tac)

theorem rust_produce_block_deployed_live : MoltPaper.thm_rust_produce_block_deployed_live := by
  intro n me at_slot Δ key_index contents sk cert suffix C I crypto st cl tl tipS tipH ts
    hn hst hts hcl hcv hstr hsig hids hsuf hMine htipS htipH hLt hH hsmall hS htail hlen hSign hId hDense
  obtain ⟨tipI, htipI⟩ := signed_tip_id_from_total cl.tip_id suffix
  obtain ⟨h1, hh1⟩ := signed_tip_sig_from_total ts suffix
  have h1_u64 : (1#u64 : U64).val = 1 := rfl
  obtain ⟨succ, hsucc_eq, hsucc_val⟩ := u64_add_ok (x := tipH) (y := 1#u64) (by rw [h1_u64]; exact hH)
  obtain ⟨id, hid⟩ := hId at_slot succ (some tipI) (some h1) contents key_index
  let nb : Block := {
    slot := at_slot,
    height := succ,
    prev := some tipI,
    id := id,
    contents_hash := contents,
    key_index := key_index
  }
  obtain ⟨key, s, hkey, hsign, hver⟩ := hSign nb
  obtain ⟨new_suffix, happ⟩ := append_signed_total suffix nb s
  have hstrip' : strip_sigs new_suffix = ok (chain_append tl nb) :=
    strip_sigs_append_signed_eq suffix nb s tl new_suffix hstr happ
  have hmodel' : toModelChain (chain_append tl nb) = toModelChain tl ++ [toModelBlock nb] :=
    toModelChain_chain_append tl nb
  have hsigs_app : sigs_ok I.CryptoInst n crypto new_suffix = ok true :=
    sigs_ok_append_signed suffix nb s me key new_suffix happ hMine hkey hver hsig
  have hids_app : ids_ok I crypto (some ts) new_suffix = ok true :=
    ids_ok_append_signed suffix nb s ts h1 new_suffix happ hh1 hid hids
  have hsuf_app : validate_suffix n cl (chain_append tl nb) = ok true :=
    validate_suffix_append hn hsmall hS hstr hsuf htipS htipH htipI hLt hH htail hlen rfl rfl hsucc_eq hDense
  have his_nil : is_nil (chain_append tl nb) = ok false := is_nil_chain_append tl nb
  have htip_app : tip_slot_from cl.tip_slot (chain_append tl nb) = ok nb.slot :=
    tip_slot_from_chain_append tl cl.tip_slot nb
  have hrec : recent_ok at_slot Δ nb.slot = ok true := by
    show recent_ok at_slot Δ at_slot = ok true
    exact recent_ok_self at_slot Δ
  have hval : validate_deployed I n at_slot Δ crypto cert new_suffix = ok true := by
    rw [validate_deployed]
    simp only [bind_tc_ok, hst, hcl, hstrip', his_nil, htip_app, hcv, ite_true, hsigs_app, hts, hids_app, hsuf_app, hrec]
    rfl
  have hprod : produce_block_deployed I n me at_slot Δ contents key_index sk crypto cert suffix =
      ok (CertifiedChain.CC cert new_suffix) := by
    rw [produce_block_deployed]
    simp only [bind_tc_ok, hMine]
    have hne : (me != me) = false := by simp
    simp only [hne, ite_false, bind_tc_ok, hst, hcl, htipH, htipI, hts, hh1, hsucc_eq, hid]
    change (do
      let sig ← I.CryptoInst.sign crypto sk nb
      let new_suffix' ← append_signed suffix nb sig
      let b ← validate_deployed I n at_slot Δ crypto cert new_suffix'
      if b then ok (CertifiedChain.CC cert new_suffix') else ok CertifiedChain.Invalid) =
      ok (CertifiedChain.CC cert new_suffix)
    rw [hsign]
    simp only [bind_tc_ok]
    rw [happ]
    simp only [bind_tc_ok, hval, ite_true]
  refine ⟨new_suffix, chain_append tl nb, nb, hprod, hval, hstrip', hmodel', rfl, rfl, rfl⟩

#print axioms Rust.rust_produce_block_deployed_live


lemma window_dense_of_budget_cover
    {n : U64} {bad : MoltPetit.Model.ByzantineSlots}
    (hBudget : MoltPetit.Model.ByzantineBounded n.val bad)
    {tipS at_slot : U64}
    {cl : CertClaim} {tl : Chain}
    (hCover : ∀ u : Nat, tipS.val + 2 ≤ u + n.val → u + n.val ≤ at_slot.val + 1 →
      ∀ s, ¬ bad s → u ≤ s → s < u + n.val →
        s = at_slot.val ∨ ∃ B ∈ (toModelClaim cl).tail ++ toModelChain tl, B.slot = s)
    {u : Nat} (hu1 : tipS.val + 2 ≤ u + n.val) (hu2 : u + n.val ≤ at_slot.val + 1) :
    MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount
      ((toModelClaim cl).tail ++ toModelChain tl ++
        [{ slot := at_slot.val, height := 0, prev := none, id := 0, contentsHash := 0,
           keyIndex := 0 }]) u n.val := by
  classical
  let dummy : MoltPetit.Model.Block := { slot := at_slot.val, height := 0, prev := none, id := 0, contentsHash := 0, keyIndex := 0 }
  let c : MoltPetit.Model.Chain := (toModelClaim cl).tail ++ toModelChain tl ++ [dummy]
  have hSubset : Finset.Ico u (u + n.val) \ MoltPetit.Model.badSlotsIn bad u n.val ⊆
      (((c.filter (MoltPetit.Model.blockInWindow u n.val)).map MoltPetit.Model.Block.slot).toFinset) := by
    intro s hs
    rw [Finset.mem_sdiff] at hs
    obtain ⟨hIco, hNotBad⟩ := hs
    rw [Finset.mem_Ico] at hIco
    have hHonest : ¬ bad s := by
      intro hbad
      apply hNotBad
      unfold MoltPetit.Model.badSlotsIn
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hIco, hbad⟩
    have hcov := hCover u hu1 hu2 s hHonest hIco.1 hIco.2
    cases hcov with
    | inl hs_at =>
      rw [List.mem_toFinset, List.mem_map]
      refine ⟨dummy, ?_, by simp [dummy, hs_at]⟩
      rw [List.mem_filter]
      refine ⟨by simp [c], ?_⟩
      rw [MoltPetit.Model.blockInWindow, decide_eq_true_iff]
      simp only [dummy]
      omega
    | inr hs_chain =>
      obtain ⟨B, hBmem, hBslot⟩ := hs_chain
      rw [List.mem_toFinset, List.mem_map]
      refine ⟨B, ?_, hBslot⟩
      rw [List.mem_filter]
      refine ⟨by simp only [c, List.mem_append, hBmem, true_or], ?_⟩
      rw [MoltPetit.Model.blockInWindow, decide_eq_true_iff]
      omega
  have hCard := Finset.card_le_card hSubset
  have hToFinset : (((c.filter (MoltPetit.Model.blockInWindow u n.val)).map MoltPetit.Model.Block.slot).toFinset).card ≤
      ((c.filter (MoltPetit.Model.blockInWindow u n.val)).map MoltPetit.Model.Block.slot).length := List.toFinset_card_le _
  rw [List.length_map] at hToFinset
  change _ ≤ MoltPetit.Model.windowCount c u n.val at hToFinset
  have hTarget : MoltPetit.Model.windowCount c u n.val =
      MoltPetit.Model.windowCount
        ((toModelClaim cl).tail ++ toModelChain tl ++
          [{ slot := at_slot.val, height := 0, prev := none, id := 0, contentsHash := 0,
             keyIndex := 0 }]) u n.val := rfl
  rw [hTarget] at hToFinset
  have hSdiff : (Finset.Ico u (u + n.val) \ MoltPetit.Model.badSlotsIn bad u n.val).card =
      (Finset.Ico u (u + n.val)).card -
        (MoltPetit.Model.badSlotsIn bad u n.val ∩ Finset.Ico u (u + n.val)).card :=
    Finset.card_sdiff
  have hInter : (MoltPetit.Model.badSlotsIn bad u n.val ∩ Finset.Ico u (u + n.val)).card ≤
      (MoltPetit.Model.badSlotsIn bad u n.val).card :=
    Finset.card_le_card Finset.inter_subset_left
  have hIcoCard : (Finset.Ico u (u + n.val)).card = n.val := by
    rw [Nat.card_Ico]
    omega
  have hBad := hBudget u
  have hArith := MoltPetit.Model.quorum_plus_byzantine_le n.val
  omega

/-- **Theorem (deployed producer live with budget)**: mode 0 deployed block production succeeds
given the Byzantine budget and honest slot coverage. -/
theorem rust_produce_block_deployed_live_budget : MoltPaper.thm_rust_produce_block_deployed_live_budget := by
  intro n me at_slot Δ key_index contents sk cert suffix C I crypto st cl tl tipS tipH ts
    hn hst hts hcl hcv hstr hsig hids hsuf hMine htipS htipH hLt hH hsmall hS htail hlen hSign hId bad hBudget hCover
  have hDense : ∀ u : Nat, tipS.val + 2 ≤ u + n.val → u + n.val ≤ at_slot.val + 1 →
      MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount
        ((toModelClaim cl).tail ++ toModelChain tl ++
          [{ slot := at_slot.val, height := 0, prev := none, id := 0, contentsHash := 0,
             keyIndex := 0 }]) u n.val := by
    intro u hu1 hu2
    exact window_dense_of_budget_cover hBudget hCover hu1 hu2
  exact rust_produce_block_deployed_live I crypto hn hst hts hcl hcv hstr hsig hids hsuf hMine htipS htipH hLt hH
    hsmall hS htail hlen hSign hId hDense


#print axioms Rust.rust_produce_block_deployed_live_budget

end Rust
