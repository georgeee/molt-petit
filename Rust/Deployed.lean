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

end Rust
