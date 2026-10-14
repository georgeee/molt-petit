import Rust.Equiv
import Rust.FoldStep
import MoltPetit.Model.Soundness
import MoltPetit.Model.Pass28
import MoltPetit.Model.KeyStealingCert
import MoltPetit.Model.KeyStealingScheduleCert
import MoltPetit.Model.KeyStealingLockstepCert
import MoltPetit.Model.ExposureCert
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

/-- A passing `ids_ok` makes every block of the model chain `RustFormed`. -/
theorem ids_ok_formed {C} {I : CryptoD C} {crypto : C} :
    ∀ (c : molt_petit.Chain),
    molt_petit.ids_ok I crypto c = ok true →
    ∀ B ∈ toModelChain c, RustFormed I crypto B
  | molt_petit.Chain.Nil, h, B, hB => by
    simp [toModelChain] at hB
  | molt_petit.Chain.Cons b tl, h, B, hB => by
    rw [molt_petit.ids_ok] at h
    obtain ⟨id, hid, h⟩ := molt_petit.bind_inv h
    obtain ⟨b1, hb1, h⟩ := molt_petit.bind_inv h
    split at h
    · rename_i hb1t
      rw [hb1t] at hb1
      have heq := hash_eq_sound hb1
      simp only [toModelChain, toModelBlock, List.mem_cons] at hB
      rcases hB with rfl | hBtl
      · refine ⟨b, rfl, ?_⟩
        rw [← heq]
        exact hid
      · exact ids_ok_formed tl h B hBtl
    · simp at h

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
    {sc : molt_petit.SignedChain} {stripped : molt_petit.Chain}
    (hsig : molt_petit.sigs_ok I.CryptoInst n crypto sc = ok true)
    (hstrip : molt_petit.strip_sigs sc = ok stripped)
    (hids : molt_petit.ids_ok I crypto stripped = ok true) :
    ∀ B ∈ toModelChain stripped, DSigned I crypto n B := by
  intro B hB
  exact ⟨sigs_ok_signed sc hsig hstrip B hB, ids_ok_formed stripped hids B hB⟩

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
      (tip : U64) (s1 : molt_petit.Block) (tl : molt_petit.Chain),
      I.cert_state crypto cert = ok st ∧
      molt_petit.claim_of_state n st = ok cl ∧
      molt_petit.strip_sigs suffix = ok stripped ∧
      stripped = molt_petit.Chain.Cons s1 tl ∧
      molt_petit.tip_slot_from cl.tip_slot stripped = ok tip ∧
      I.CryptoInst.cert_verify crypto cert = ok true ∧
      molt_petit.sigs_ok I.CryptoInst n crypto suffix = ok true ∧
      molt_petit.ids_ok I crypto stripped = ok true ∧
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
        obtain ⟨b3, hb3, h⟩ := molt_petit.bind_inv h
        split at h
        · rename_i hb3t; rw [hb3t] at hb3
          obtain ⟨b4, hb4, h⟩ := molt_petit.bind_inv h
          split at h
          · rename_i hb4t; rw [hb4t] at hb4
            exact ⟨st, cl, stripped, tip, s1, tl,
                   hst, hcl, hstrip, hcons, htip, hb1, hb2, hb3, hb4, h⟩
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


lemma attestsK_history {C} {I : CryptoD C} {crypto : C} {n q : U64} {G : Block}
    {bs : List Block} {stO : CertStateG U64} {out : FloorsG U64}
    (hn : 1 ≤ n.val) (hq : quorum n = ok q)
    (hG : cert_genesis_ok_be UB () (toBlockG G) = ok true)
    (hSigG : DSigned I crypto n (toModelBlock G))
    (hA : AttestsK I crypto n q G bs stO out) :
    let cl₀ := modelClaimOf n.val (toModelBlock G) (bs.map toModelBlock)
    MoltPetit.Model.GroundedCert n.val (DSigned I crypto n) (toModelBlock G) cl₀ ∧
    MoltPetit.Model.GroundedHistory n.val (DSigned I crypto n) (toModelBlock G) cl₀ ((G :: bs).map toModelBlock) ∧
    MoltPetit.Model.GroundedHistoryK n.val (DSigned I crypto n) (toModelBlock G) cl₀ (floorsFun out) ((G :: bs).map toModelBlock) ∧
    stateView n.val stO = MoltPetit.Model.claimView cl₀ := by
  intro cl₀
  obtain ⟨hSig, hFoldOut⟩ := hA
  have hFold := foldKOut_foldK hFoldOut
  have ⟨hgen, hslot0⟩ := cert_genesis_ok_be_sound hG
  have hbase_hist : MoltPetit.Model.GroundedHistoryK n.val (DSigned I crypto n)
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
    exact groundedHistoryK_genesis hn hgen hslot0 hSigG
  have hbase_rep : TailRepr n.val (genesisState n.val G)
      (modelClaimOf n.val (toModelBlock G) ([].map toModelBlock)) := by
    simp only [List.map_nil]
    exact tailRepr_genesisState n.val G
  have hlen0 : floorsLen (initFloors n.val G.key_index) = n.val :=
    floorsLen_initFloors n.val G.key_index
  have hhistK := foldK_history_aux hn hq bs [] (genesisState n.val G)
    (initFloors n.val G.key_index) out hSig hbase_rep hlen0 hbase_hist hFold
  simp only [List.nil_append] at hhistK
  have hcertK : MoltPetit.Model.GroundedCertK n.val (DSigned I crypto n)
      (toModelBlock G) cl₀ (floorsFun out) :=
    cert_fold_k_sound hn hq hG hSigG hSig hFold
  have hcert := groundedCert_of_groundedCertK hcertK
  have hhist := groundedHistory_of_groundedHistoryK hhistK
  have hview := stateView_of_foldKOut hn hq hG hFoldOut
  exact ⟨hcert, hhist, hhistK, hview⟩

end Rust

