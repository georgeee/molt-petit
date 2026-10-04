import Rust.Bridge
import Spec.RustBridge

/-!
# The backend-generic validator is proven at the `U64` instantiation

`valid_chain_be` is the backend-generic consensus validator: the SAME Rust source
is instantiated with the native `U64Backend` here and with a plonky2 circuit
backend in `molt_petit_keyrot`. What is proved is the `U64` instantiation — we
connect it to the model exactly as `Bridge.lean` connects the concrete
`valid_chain`:

  `valid_chain_be U64 .. n (quorum n) (toChainG c) = ok true`
      ⟹ `MoltPetit.Model.validChain n (toModelChain c) = true`.

Nothing here constrains any other `Backend` instance: that the plonky2 circuit's
gadgets (field arithmetic and its wraparound, range checks) faithfully realise
the backend operations is a named trust assumption — the paper's stated residual
(Section 7) — not a consequence of this file. The generic validator is
branch-free/eager (one source must serve the circuit); we follow `Bridge`'s
"accepts ⇒ model property" idiom, first reducing the U64 backend ops with `simp`.
-/

open Aeneas Std Result

namespace Rust

open molt_petit

-- ---------------------------------------------------------------------------
-- Project the concrete chain to the generic chain at `Num = U64`.
-- ---------------------------------------------------------------------------

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

@[simp] theorem toBlockG_slot (b : Block) : (toBlockG b).slot = b.slot := rfl
@[simp] theorem toBlockG_height (b : Block) : (toBlockG b).height = b.height := rfl
@[simp] theorem toChainG_nil : toChainG Chain.Nil = ChainG.NilG := rfl
@[simp] theorem toChainG_cons (b tl) :
    toChainG (Chain.Cons b tl) = ChainG.ConsG (toBlockG b) (toChainG tl) := rfl

theorem hashg_eq_eq (x y : Hash) :
    hashg_eq UB () (toHashG x) (toHashG y) = molt_petit.hash_eq x y := by
  unfold hashg_eq molt_petit.hash_eq
  simp [toHashG]
  split_ifs <;> simp_all

-- ---------------------------------------------------------------------------
-- window_count_be ⇒ model windowCount
-- ---------------------------------------------------------------------------

theorem window_count_be_corr : ∀ (c : Chain) (u len : U64) {w : U64},
    window_count_be UB () (toChainG c) u len = ok w →
    w.val = MoltPetit.Model.windowCount (toModelChain c) u.val len.val := by
  intro c
  induction c with
  | Nil =>
    intro u len w h
    simp [toChainG, window_count_be, UB] at h
    subst h
    simp [toModelChain, MoltPetit.Model.windowCount]
  | Cons b tl ih =>
    intro u len w h
    simp only [toChainG_cons, window_count_be, toBlockG_slot, UB] at h
    simp at h
    obtain ⟨hi, hhi, h⟩ := bind_inv h
    obtain ⟨inw, hinw, h⟩ := bind_inv h
    obtain ⟨here, hhere, h⟩ := bind_inv h
    obtain ⟨rest, hrest, h⟩ := bind_inv h
    have hrv := ih u len hrest
    have hwv : w.val = here.val + rest.val := by
      have := UScalar.add_equiv here rest; simp only [h] at this; exact this.2.1
    have hhiv : hi.val = u.val + len.val := by
      have := UScalar.add_equiv u len; simp only [hhi] at this; exact this.2.1
    have hhv : here.val = if MoltPetit.Model.blockInWindow u.val len.val (toModelBlock b)
                          then 1 else 0 := by
      have hcond :
          (MoltPetit.Model.blockInWindow u.val len.val (toModelBlock b) = true ∧ here = 1#u64)
        ∨ (MoltPetit.Model.blockInWindow u.val len.val (toModelBlock b) = false ∧ here = 0#u64) := by
        simp only [MoltPetit.Model.blockInWindow, toModelBlock, decide_eq_true_eq,
          decide_eq_false_iff_not]
        split at hinw
        · rename_i hle; injection hinw with hinw; subst inw
          split at hhere
          · rename_i hlt; injection hhere with hhere
            left; refine ⟨⟨by scalar_tac, ?_⟩, hhere.symm⟩
            have : (b.slot.val : ℕ) < hi.val := by simpa using hlt
            rw [hhiv] at this; exact this
          · rename_i hlt; injection hhere with hhere
            right; refine ⟨?_, hhere.symm⟩
            rintro ⟨_, h2⟩
            have : ¬ (b.slot.val : ℕ) < hi.val := by simpa using hlt
            rw [hhiv] at this; exact this h2
        · rename_i hle; injection hinw with hinw; subst inw
          simp only [Bool.false_eq_true, if_false] at hhere
          injection hhere with hhere
          right; refine ⟨?_, hhere.symm⟩
          rintro ⟨h1, _⟩; exact hle h1
      rcases hcond with ⟨hc, he⟩ | ⟨hc, he⟩ <;> rw [hc, he] <;> simp
    rw [toModelChain_cons, model_windowCount_cons, hwv, hhv, hrv]

-- ---------------------------------------------------------------------------
-- window_dense_be ⇒ model window is quorum-dense
-- ---------------------------------------------------------------------------

theorem window_dense_be_sound {n q : U64} {c : Chain} {u : U64}
    (hq : quorum n = ok q)
    (h : window_dense_be UB () q (toChainG c) u n = ok true) :
    MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (toModelChain c) u.val n.val := by
  simp only [window_dense_be, UB] at h
  simp at h
  obtain ⟨cnt, hcnt, h⟩ := bind_inv h
  have hcv := window_count_be_corr c u n hcnt
  have hqv := quorum_val_of_ok hq
  rw [← hqv, ← hcv]
  injection h with h
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Nat.not_lt] at h
  exact h

-- ---------------------------------------------------------------------------
-- genesis_ok_be ⇒ model genesisOk
-- ---------------------------------------------------------------------------

theorem genesis_ok_be_sound {b : Block} (h : genesis_ok_be UB () (toBlockG b) = ok true) :
    MoltPetit.Model.genesisOk (toModelBlock b) = true := by
  simp only [genesis_ok_be, toBlockG, UB] at h
  simp at h
  split at h
  · rename_i hh
    injection h with h
    simp only [MoltPetit.Model.genesisOk, toModelBlock, decide_eq_true_eq]
    refine ⟨by scalar_tac, ?_⟩
    cases hp : b.prev with
    | none => simp
    | some p => rw [hp] at h; simp at h
  · simp at h

-- ---------------------------------------------------------------------------
-- child_ok_be ⇒ model childOk
-- ---------------------------------------------------------------------------

theorem child_ok_be_sound {parent child : Block}
    (h : child_ok_be UB () (toBlockG parent) (toBlockG child) = ok true) :
    MoltPetit.Model.childOk (toModelBlock parent) (toModelBlock child) = true := by
  simp only [child_ok_be, toBlockG] at h
  simp at h
  obtain ⟨succ, hsucc, h⟩ := bind_inv h
  obtain ⟨prev_eq, hpe, h⟩ := bind_inv h
  obtain ⟨prev_ok, hpo, h⟩ := bind_inv h
  obtain ⟨hs, hhs, h⟩ := bind_inv h
  split at h
  · rename_i hst
    injection h with h; subst h
    subst hst
    split at hhs
    · rename_i hheq
      injection hhs with hhs
      simp only [decide_eq_true_eq] at hhs
      split at hpo
      · rename_i hpsome
        injection hpo with hpo; subst hpo
        have hsuccv : succ.val = parent.height.val + 1 := by
          have := UScalar.add_equiv parent.height 1#u64; simp only [hsucc] at this
          simpa using this.2.1
        simp only [MoltPetit.Model.childOk, toModelBlock, decide_eq_true_eq]
        refine ⟨by rw [hheq]; scalar_tac, hhs, ?_⟩
        cases hp : child.prev with
        | none => rw [hp] at hpsome; simp at hpsome
        | some p =>
          simp only [hp, hashg_eq_eq] at hpe
          have hpa := hash_eq_sound hpe
          simp [hpa]
      · simp at hpo
    · simp at hhs
  · simp at h

-- ---------------------------------------------------------------------------
-- links_from_be / links_ok_be ⇒ model linksOk
-- ---------------------------------------------------------------------------

theorem links_from_be_sound : ∀ (parent : Block) (c : Chain),
    links_from_be UB () (toBlockG parent) (toChainG c) = ok true →
    MoltPetit.Model.linksOk (toModelBlock parent :: toModelChain c) = true := by
  intro parent c
  induction c generalizing parent with
  | Nil => intro _; rfl
  | Cons b tl ih =>
    intro h
    simp only [toChainG_cons, links_from_be] at h
    simp at h
    obtain ⟨here, hhere, h⟩ := bind_inv h
    obtain ⟨rest, hrest, h⟩ := bind_inv h
    split at h
    · rename_i hht
      rw [hht] at hhere
      injection h with h; subst h
      have hc := child_ok_be_sound hhere
      have hr := ih b hrest
      simp only [toModelChain_cons]
      show (MoltPetit.Model.childOk (toModelBlock parent) (toModelBlock b) &&
        MoltPetit.Model.linksOk (toModelBlock b :: toModelChain tl)) = true
      rw [Bool.and_eq_true]; exact ⟨hc, hr⟩
    · simp at h

theorem links_ok_be_sound {c : Chain} (h : links_ok_be UB () (toChainG c) = ok true) :
    MoltPetit.Model.linksOk (toModelChain c) = true := by
  cases c with
  | Nil => rfl
  | Cons g tl =>
    simp only [toChainG_cons, links_ok_be, UB] at h
    exact links_from_be_sound g tl h

-- ---------------------------------------------------------------------------
-- tip_slot_from_be computes the model tip slot
-- ---------------------------------------------------------------------------

theorem tip_slot_from_be_getLast : ∀ (c : Chain) (cur : U64) {r : U64}
    (g0 : MoltPetit.Model.Block), g0.slot = cur.val →
    tip_slot_from_be UB () cur (toChainG c) = ok r →
    ∃ tip, (g0 :: toModelChain c).getLast? = some tip ∧ tip.slot = r.val := by
  intro c
  induction c with
  | Nil =>
    intro cur r g0 hg0 h
    simp only [toChainG_nil, tip_slot_from_be] at h
    injection h with h; subst h
    exact ⟨g0, by simp, hg0⟩
  | Cons b tl ih =>
    intro cur r g0 hg0 h
    simp only [toChainG_cons, tip_slot_from_be, toBlockG_slot] at h
    obtain ⟨tip, htip, hts⟩ := ih b.slot (toModelBlock b) rfl h
    refine ⟨tip, ?_, hts⟩
    rw [toModelChain_cons, List.getLast?_cons_cons]
    exact htip

-- ---------------------------------------------------------------------------
-- anchors_dense_be ⇒ each anchored matured window is quorum-dense
-- ---------------------------------------------------------------------------

theorem anchors_dense_be_sound : ∀ (all rest : Chain) (lo t n q : U64),
    quorum n = ok q →
    anchors_dense_be UB () (toChainG all) (toChainG rest) lo t n q = ok true →
    ∀ b' ∈ toModelChain rest, lo.val ≤ b'.slot + 1 → b'.slot + 1 + n.val ≤ t.val + 1 →
      MoltPetit.Model.quorum n.val ≤
        MoltPetit.Model.windowCount (toModelChain all) (b'.slot + 1) n.val := by
  intro all rest
  induction rest with
  | Nil => intro lo t n q _ _ b' hb' _ _; simp [toModelChain] at hb'
  | Cons b tl ih =>
    intro lo t n q hq h b' hb' hlo hmat
    simp only [toChainG_cons, anchors_dense_be, toBlockG_slot] at h
    simp at h
    obtain ⟨u, hu, h⟩ := bind_inv h
    obtain ⟨upn, hupn, h⟩ := bind_inv h
    obtain ⟨t11, ht11, h⟩ := bind_inv h
    obtain ⟨cond, hcond, h⟩ := bind_inv h
    obtain ⟨dense, hdense, h⟩ := bind_inv h
    obtain ⟨ok1, hok1, h⟩ := bind_inv h
    obtain ⟨rest_ok, hrok, h⟩ := bind_inv h
    split at h
    · rename_i hok1t
      injection h with h; subst h
      have huv : u.val = b.slot.val + 1 := by
        have := UScalar.add_equiv b.slot 1#u64; simp only [hu] at this; simpa using this.2.1
      have hupnv : upn.val = u.val + n.val := by
        have := UScalar.add_equiv u n; simp only [hupn] at this; exact this.2.1
      have ht11v : t11.val = t.val + 1 := by
        have := UScalar.add_equiv t 1#u64; simp only [ht11] at this; simpa using this.2.1
      rw [toModelChain_cons] at hb'
      rcases List.mem_cons.mp hb' with rfl | hb'tl
      · simp only [toModelBlock] at hlo hmat ⊢
        have hcondt : cond = true := by
          split at hcond
          · injection hcond with hcond; rw [← hcond]
            simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt, hupnv, ht11v]
            omega
          · rename_i hnle; exfalso; rw [huv] at hnle; exact hnle hlo
        rw [hcondt] at hok1
        simp only [Bool.true_eq_false, if_false] at hok1
        injection hok1 with hok1
        rw [hok1, hok1t] at hdense
        have hwd := window_dense_be_sound hq hdense
        rw [huv] at hwd; exact hwd
      · exact ih lo t n q hq hrok b' hb'tl hlo hmat
    · simp at h

theorem matured_dense_be_sound {c : Chain} {lo t n q : U64}
    (hq : quorum n = ok q)
    (h : matured_dense_be UB () (toChainG c) lo t n q = ok true) :
    ∀ u, lo.val ≤ u → u + n.val ≤ t.val + 1 →
      MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (toModelChain c) u n.val := by
  simp [matured_dense_be] at h
  obtain ⟨lpn, hlpn, h⟩ := bind_inv h
  obtain ⟨t11, ht11, h⟩ := bind_inv h
  obtain ⟨dense_lo, hdl, h⟩ := bind_inv h
  obtain ⟨base, hbase, h⟩ := bind_inv h
  obtain ⟨anch, hanch, h⟩ := bind_inv h
  split at h
  · rename_i hbaset
    injection h with h; subst h
    apply MoltPetit.Model.anchored_density_sound
      (c := toModelChain c) (lo := lo.val) (t := t.val) (n := n.val)
    · intro hbm
      have hlpnv : lpn.val = lo.val + n.val := by
        have := UScalar.add_equiv lo n; simp only [hlpn] at this; exact this.2.1
      have ht11v : t11.val = t.val + 1 := by
        have := UScalar.add_equiv t 1#u64; simp only [ht11] at this; simpa using this.2.1
      have hwd : window_dense_be UB () q (toChainG c) lo n = ok true := by
        rw [hbaset] at hbase
        split at hbase
        · exfalso; rename_i hlt; scalar_tac
        · injection hbase with hbase; rw [hbase] at hdl; exact hdl
      exact window_dense_be_sound hq hwd
    · exact anchors_dense_be_sound c c lo t n q hq hanch
  · simp at h

theorem valid_chain_be_sound {n q : U64} {c : Chain}
    (hq : quorum n = ok q)
    (h : valid_chain_be UB () n q (toChainG c) = ok true) :
    MoltPetit.Model.validChain n.val (toModelChain c) = true := by
  cases c with
  | Nil => rfl
  | Cons g tl =>
    simp only [toChainG_cons, valid_chain_be] at h
    simp at h
    obtain ⟨genesis, hgen, h⟩ := bind_inv h
    obtain ⟨links, hlinks, h⟩ := bind_inv h
    obtain ⟨tip, hts, h⟩ := bind_inv h
    obtain ⟨dense, hdense, h⟩ := bind_inv h
    obtain ⟨gl, hgl, h⟩ := bind_inv h
    rw [← toChainG_cons] at hlinks hdense
    split at h
    · rename_i hglt
      injection h with h; subst h
      rw [hglt] at hgl
      split at hgl
      · rename_i hgent
        injection hgl with hgl; subst hgl
        rw [hgent] at hgen
        have hg := genesis_ok_be_sound hgen
        have hl := links_ok_be_sound hlinks
        obtain ⟨tip', htip, htipv⟩ := tip_slot_from_be_getLast tl g.slot (toModelBlock g) rfl hts
        have hmd := matured_dense_be_sound hq hdense
        show (MoltPetit.Model.genesisOk (toModelBlock g) &&
              MoltPetit.Model.linksOk (toModelBlock g :: toModelChain tl) &&
              (match (toModelBlock g :: toModelChain tl).getLast? with
               | some tip => MoltPetit.Model.maturedWindowsDense n.val
                   (toModelBlock g :: toModelChain tl) tip.slot
               | none => true)) = true
        rw [htip]
        simp only [Bool.and_eq_true]
        refine ⟨⟨hg, hl⟩, ?_⟩
        rw [MoltPetit.Model.maturedWindowsDense, List.all_eq_true]
        intro u hu
        have hru := List.mem_range.mp hu
        rw [MoltPetit.Model.windowDense, decide_eq_true_eq]
        have hd := hmd u (by scalar_tac) (by omega)
        simpa only [toModelChain_cons] using hd
      · simp at hgl
    · simp at h

/-- **The shared validator source is sound at the `U64` instantiation.** If the
backend-generic validator — the SAME source the circuit in `molt_petit_keyrot`
instantiates — accepts a chain at the native `U64` backend (with `q = quorum n`),
the chain is semantically `ValidChain` in the model: the exact conclusion the
proven `valid_chain` gives (`rust_valid_chain_sound`). This binds only the `U64`
instance; the faithfulness of any other `Backend` instance — in particular the
plonky2 gadgets (field wraparound, range checks) — is a named trust assumption,
exactly as the paper's Section 7 states. -/
theorem valid_chain_be_validChain {n q : U64} {c : Chain}
    (hq : quorum n = ok q)
    (h : valid_chain_be UB () n q (toChainG c) = ok true) :
    MoltPetit.Model.ValidChain n.val (toModelChain c) :=
  MoltPetit.Model.validChain_sound (valid_chain_be_sound hq h)

end Rust
