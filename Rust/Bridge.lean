import Rust.Properties
import MoltPetit.Model.Liveness
import MoltPetit.TS.Bridge
import Spec.RustBridge

/-!
# Rust → Lean-model soundness bridge

A projection from the Aeneas-extracted Rust types/functions to the Lean model
(`MoltPetit.Model`), and soundness lemmas: on projected inputs the Rust functions
compute the model functions in the **soundness direction** (validator-acceptance
/ computation-success implies the model predicate; there is no completeness
converse). This is the Rust analogue of the `TSBridge` (which connects the
Thales-emitted TypeScript to the same model).

We project `U64 → Nat` by `.val` (total — no bounds needed) and `Hash → Nat`
by packing its four `u64` limbs little-endian (`a + b·2^64 + c·2^128 + d·2^192`,
injective). We prove the **soundness direction**: success of the Rust
computation witnesses that no machine-integer overflow occurred, so the value
equals the model computation, with no a-priori bounds assumed.

Covered here: the arithmetic core (`quorum`, `max_byzantine`,
`producer_for_slot`) and the genesis check, plus the chain projection used to
state chain-level correspondences. The remaining recursive correspondences
(`window_count`, `links_ok`, `matured_dense`, … ⇒ `valid_chain`) build on the
same projection and are the follow-on, exactly as the TS bridge was developed.
-/

open Aeneas Std Result

namespace Rust

-- ---------------------------------------------------------------------------
-- Projection to the model
-- ---------------------------------------------------------------------------

@[simp] theorem toModelChain_nil : toModelChain .Nil = [] := rfl
@[simp] theorem toModelChain_cons (b tl) :
    toModelChain (.Cons b tl) = toModelBlock b :: toModelChain tl := rfl

-- ---------------------------------------------------------------------------
-- Chain-level equivalence (soundness direction): success of the Rust
-- computation witnesses no overflow, so its value/result equals the model's.
-- ---------------------------------------------------------------------------

theorem model_windowCount_cons (b : MoltPetit.Model.Block) (c : MoltPetit.Model.Chain)
    (u len : Nat) :
    MoltPetit.Model.windowCount (b :: c) u len
      = (if MoltPetit.Model.blockInWindow u len b then 1 else 0)
        + MoltPetit.Model.windowCount c u len := by
  simp only [MoltPetit.Model.windowCount, List.filter_cons]
  cases h : MoltPetit.Model.blockInWindow u len b <;> simp <;> omega

/-- **`window_count` correspondence.** -/
theorem window_count_corr : ∀ (c : molt_petit.Chain) (u len : U64) {w : U64},
    molt_petit.window_count c u len = ok w →
    w.val = MoltPetit.Model.windowCount (toModelChain c) u.val len.val := by
  intro c
  induction c with
  | Nil =>
    intro u len w h
    rw [molt_petit.window_count] at h
    injection h with h; subst h
    simp only [toModelChain_nil, MoltPetit.Model.windowCount, List.filter_nil, List.length_nil]
    scalar_tac
  | Cons b tl ih =>
    intro u len w h
    rw [molt_petit.window_count] at h
    obtain ⟨here, hhere, h⟩ := molt_petit.bind_inv h
    obtain ⟨i, hi, h⟩ := molt_petit.bind_inv h
    have hiv : i.val = MoltPetit.Model.windowCount (toModelChain tl) u.val len.val := ih u len hi
    have hwv : w.val = here.val + i.val := by
      have hadd := UScalar.add_equiv here i; simp only [h] at hadd; exact hadd.2.1
    have hhv : here.val = if MoltPetit.Model.blockInWindow u.val len.val (toModelBlock b)
                          then 1 else 0 := by
      simp only [MoltPetit.Model.blockInWindow, toModelBlock, decide_eq_true_eq]
      split at hhere
      · rename_i hle
        obtain ⟨j, hj, hhere⟩ := molt_petit.bind_inv hhere
        have hjv : j.val = u.val + len.val := by
          have hadd := UScalar.add_equiv u len; simp only [hj] at hadd; exact hadd.2.1
        split at hhere
        · rename_i hlt; injection hhere with hhere; subst hhere
          rw [if_pos ⟨by scalar_tac, by scalar_tac⟩]; scalar_tac
        · rename_i hlt; injection hhere with hhere; subst hhere
          rw [if_neg (by rintro ⟨_, _⟩; scalar_tac)]; scalar_tac
      · rename_i hle; injection hhere with hhere; subst hhere
        rw [if_neg (by rintro ⟨_, _⟩; scalar_tac)]; scalar_tac
    rw [toModelChain_cons, model_windowCount_cons, hwv, hhv, hiv]

-- ---------------------------------------------------------------------------
-- Arithmetic-core equivalence
-- ---------------------------------------------------------------------------

/-- `producer_for_slot` computes the model's round-robin leader. -/
theorem producer_for_slot_corr (n slot : U64) (hn : 0 < n.val) :
    molt_petit.producer_for_slot n slot
      ⦃ r => r.val = MoltPetit.Model.producerForSlot n.val slot.val ⦄ := by
  unfold molt_petit.producer_for_slot
  step with UScalar.rem_spec as ⟨ r, hr ⟩
  simpa [MoltPetit.Model.producerForSlot] using hr

/-- `quorum` computes the model quorum `⌈2n/3⌉`. -/
theorem quorum_corr (n : U64) (h : 2 * n.val + 2 ≤ U64.max) :
    molt_petit.quorum n ⦃ q => q.val = MoltPetit.Model.quorum n.val ⦄ := by
  have hs := molt_petit.quorum_spec n h
  simpa [MoltPetit.Model.quorum] using hs

/-- `max_byzantine` computes the model budget `⌊(n-1)/3⌋`. -/
theorem max_byzantine_corr (n : U64) (hn : 1 ≤ n.val) :
    molt_petit.max_byzantine n ⦃ f => f.val = MoltPetit.Model.maxByzantine n.val ⦄ := by
  have hs := molt_petit.max_byzantine_spec n hn
  simpa [MoltPetit.Model.maxByzantine] using hs

-- ---------------------------------------------------------------------------
-- Soundness toward `valid_chain` ⇒ model `validChain`
-- ---------------------------------------------------------------------------

/-- The quorum value, from a successful call (success witnesses no overflow). -/
theorem quorum_val_of_ok {n q : U64} (h : molt_petit.quorum n = ok q) :
    q.val = MoltPetit.Model.quorum n.val := by
  rw [molt_petit.quorum] at h
  obtain ⟨a, ha, h⟩ := molt_petit.bind_inv h
  obtain ⟨b, hb, h⟩ := molt_petit.bind_inv h
  have hav : a.val = n.val + n.val := by
    have := UScalar.add_equiv n n; simp only [ha] at this; exact this.2.1
  have hbv : b.val = a.val + 2 := by
    have := UScalar.add_equiv a 2#u64; simp only [hb] at this; simpa using this.2.1
  obtain ⟨z, hz, hzv⟩ := UScalar.div_spec b (y := 3#u64) (by decide)
  rw [h] at hz; injection hz with hz; subst hz
  simp only [MoltPetit.Model.quorum]
  rw [hzv, hbv, hav]; congr 1; omega

/-- Hash equality success forces \emph{all four} limbs equal, i.e. the full
256-bit hashes coincide --- `molt_petit.hash_eq` checks every limb. -/
theorem hash_eq_sound {x y : molt_petit.Hash} (h : molt_petit.hash_eq x y = ok true) :
    x = y := by
  obtain ⟨xa, xb, xc, xd⟩ := x
  obtain ⟨ya, yb, yc, yd⟩ := y
  simp only [molt_petit.hash_eq] at h
  split_ifs at h with ha hb hc <;> simp_all

/-- `window_dense` accepting ⇒ the model window is quorum-dense. -/
theorem window_dense_sound {n : U64} {c : molt_petit.Chain} {u : U64}
    (h : molt_petit.window_dense n c u = ok true) :
    MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (toModelChain c) u.val n.val := by
  rw [molt_petit.window_dense] at h
  obtain ⟨q, hq, h⟩ := molt_petit.bind_inv h
  obtain ⟨wc, hwc, h⟩ := molt_petit.bind_inv h
  injection h with h
  have hqv := quorum_val_of_ok hq
  have hwcv := window_count_corr c u n hwc
  rw [← hqv, ← hwcv]; scalar_tac

/-- `genesis_ok` accepting ⇒ the model genesis check holds. -/
theorem genesis_ok_sound {b : molt_petit.Block} (h : molt_petit.genesis_ok b = ok true) :
    MoltPetit.Model.genesisOk (toModelBlock b) = true := by
  rw [molt_petit.genesis_ok] at h
  split at h
  · rename_i hh
    injection h with h
    simp only [MoltPetit.Model.genesisOk, toModelBlock, decide_eq_true_eq]
    refine ⟨by scalar_tac, ?_⟩
    cases hp : b.prev with
    | none => simp
    | some p => rw [hp] at h; simp [core.option.Option.is_none] at h
  · simp at h

/-- `child_ok` accepting ⇒ the model child check holds. One-directional simply
because it is the soundness direction (validator-acceptance ⇒ model predicate);
the hash projection now matches `hash_eq` exactly (full 256-bit equality). -/
theorem child_ok_sound {parent child : molt_petit.Block}
    (h : molt_petit.child_ok parent child = ok true) :
    MoltPetit.Model.childOk (toModelBlock parent) (toModelBlock child) = true := by
  rw [molt_petit.child_ok] at h
  obtain ⟨⟨p1, pok⟩, hm, h⟩ := molt_petit.bind_inv h
  obtain ⟨i, hi, h⟩ := molt_petit.bind_inv h
  split at h
  · rename_i hht
    split at h
    · rename_i hst
      injection h with h; subst h
      have hp1 : p1 = parent ∧ ∃ p, child.prev = some p ∧
          molt_petit.hash_eq p parent.id = ok true := by
        cases hp : child.prev with
        | none => rw [hp] at hm; injection hm with hm; simp at hm
        | some p =>
          rw [hp] at hm
          obtain ⟨hev, hhe, hm⟩ := molt_petit.bind_inv hm
          injection hm with hm
          rw [Prod.mk.injEq] at hm
          obtain ⟨hm1, hm2⟩ := hm
          subst hm2
          exact ⟨hm1.symm, p, rfl, hhe⟩
      obtain ⟨hp1eq, p, hpprev, hpeq⟩ := hp1
      subst p1
      have hpa := hash_eq_sound hpeq
      have hiv : i.val = parent.height.val + 1 := by
        have := UScalar.add_equiv parent.height 1#u64; simp only [hi] at this
        simpa using this.2.1
      simp only [MoltPetit.Model.childOk, toModelBlock, decide_eq_true_eq]
      refine ⟨by scalar_tac, by scalar_tac, ?_⟩
      simp [hpprev, hashToNat, hpa]
    · simp at h
  · simp at h

/-- `links_from` accepting ⇒ the model adjacent links hold. -/
theorem links_from_sound : ∀ (parent : molt_petit.Block) (c : molt_petit.Chain),
    molt_petit.links_from parent c = ok true →
    MoltPetit.Model.linksOk (toModelBlock parent :: toModelChain c) = true := by
  intro parent c
  induction c generalizing parent with
  | Nil => intro _; rfl
  | Cons b tl ih =>
    intro h
    rw [molt_petit.links_from] at h
    obtain ⟨b1, hb1, h⟩ := molt_petit.bind_inv h
    split at h
    · rename_i hb1t; subst hb1t
      have hc := child_ok_sound hb1
      have hrest := ih b h
      simp only [toModelChain_cons]
      show (MoltPetit.Model.childOk (toModelBlock parent) (toModelBlock b) &&
        MoltPetit.Model.linksOk (toModelBlock b :: toModelChain tl)) = true
      rw [Bool.and_eq_true]; exact ⟨hc, hrest⟩
    · simp at h

/-- `links_ok` accepting ⇒ the model chain is internally linked. -/
theorem links_ok_sound {c : molt_petit.Chain} (h : molt_petit.links_ok c = ok true) :
    MoltPetit.Model.linksOk (toModelChain c) = true := by
  cases c with
  | Nil => rfl
  | Cons g tl => rw [molt_petit.links_ok] at h; exact links_from_sound g tl h

/-- `tip_slot_from` computes the slot of the model chain's last block. -/
theorem tip_slot_from_eq_getLast : ∀ (c : molt_petit.Chain) (cur : U64) {r : U64}
    (g0 : MoltPetit.Model.Block), g0.slot = cur.val →
    molt_petit.tip_slot_from cur c = ok r →
    ∃ tip, (g0 :: toModelChain c).getLast? = some tip ∧ tip.slot = r.val := by
  intro c
  induction c with
  | Nil =>
    intro cur r g0 hg0 h
    rw [molt_petit.tip_slot_from] at h; injection h with h; subst h
    exact ⟨g0, by simp, hg0⟩
  | Cons b tl ih =>
    intro cur r g0 hg0 h
    rw [molt_petit.tip_slot_from] at h
    obtain ⟨tip, htip, hts⟩ := ih b.slot (toModelBlock b) rfl h
    refine ⟨tip, ?_, hts⟩
    rw [toModelChain_cons, List.getLast?_cons_cons]
    exact htip

/-- `anchors_dense` accepting ⇒ each anchored window is quorum-dense (the
`hanchor` hypothesis of `anchored_density_sound`). -/
theorem anchors_dense_sound : ∀ (all rest : molt_petit.Chain) (lo t n : U64),
    molt_petit.anchors_dense all rest lo t n = ok true →
    ∀ b' ∈ toModelChain rest, lo.val ≤ b'.slot + 1 → b'.slot + 1 + n.val ≤ t.val + 1 →
      MoltPetit.Model.quorum n.val ≤
        MoltPetit.Model.windowCount (toModelChain all) (b'.slot + 1) n.val := by
  intro all rest
  induction rest with
  | Nil => intro lo t n _ b' hb' _ _; simp [toModelChain] at hb'
  | Cons b tl ih =>
    intro lo t n h b' hb' hlo hmat
    rw [molt_petit.anchors_dense] at h
    obtain ⟨u, hu, h⟩ := molt_petit.bind_inv h
    obtain ⟨o1, ho1, h⟩ := molt_petit.bind_inv h
    split at h
    · rename_i ho1t; subst ho1t
      have huv : u.val = b.slot.val + 1 := by
        have := UScalar.add_equiv b.slot 1#u64; simp only [hu] at this; simpa using this.2.1
      rw [toModelChain_cons] at hb'
      rcases List.mem_cons.mp hb' with rfl | hb'tl
      · simp only [toModelBlock] at hlo hmat ⊢
        have hwd : molt_petit.window_dense n all u = ok true := by
          split at ho1
          · obtain ⟨i, hi, ho1⟩ := molt_petit.bind_inv ho1
            obtain ⟨i1, hi1, ho1⟩ := molt_petit.bind_inv ho1
            split at ho1
            · exact ho1
            · rename_i hni; exfalso
              have hiv : i.val = u.val + n.val := by
                have := UScalar.add_equiv u n; simp only [hi] at this; exact this.2.1
              have hi1v : i1.val = t.val + 1 := by
                have := UScalar.add_equiv t 1#u64; simp only [hi1] at this; simpa using this.2.1
              scalar_tac
          · rename_i hnle; exfalso; scalar_tac
        have hq := window_dense_sound hwd
        rw [huv] at hq; exact hq
      · exact ih lo t n h b' hb'tl hlo hmat
    · simp at h

/-- `matured_dense` accepting ⇒ every matured window of the model chain is
quorum-dense (via the model slide lemma `anchored_density_sound`). -/
theorem matured_dense_sound {c : molt_petit.Chain} {lo t n : U64}
    (h : molt_petit.matured_dense c lo t n = ok true) :
    ∀ u, lo.val ≤ u → u + n.val ≤ t.val + 1 →
      MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount (toModelChain c) u n.val := by
  rw [molt_petit.matured_dense] at h
  obtain ⟨i, hi, h⟩ := molt_petit.bind_inv h
  obtain ⟨i1, hi1, h⟩ := molt_petit.bind_inv h
  obtain ⟨base, hbase, h⟩ := molt_petit.bind_inv h
  split at h
  · rename_i hbaset; subst hbaset
    have hiv : i.val = lo.val + n.val := by
      have := UScalar.add_equiv lo n; simp only [hi] at this; exact this.2.1
    have hi1v : i1.val = t.val + 1 := by
      have := UScalar.add_equiv t 1#u64; simp only [hi1] at this; simpa using this.2.1
    apply MoltPetit.Model.anchored_density_sound
      (c := toModelChain c) (lo := lo.val) (t := t.val) (n := n.val)
    · intro _
      have hwd : molt_petit.window_dense n c lo = ok true := by
        split at hbase
        · exact hbase
        · rename_i hni; exfalso; scalar_tac
      exact window_dense_sound hwd
    · exact anchors_dense_sound c c lo t n h
  · simp at h

/-- **Verifier soundness.** If the Rust `valid_chain` accepts a chain, the model
executable validator `validChain` accepts its projection — hence (via
`validChain_sound`) the projection is semantically `ValidChain`. -/
theorem valid_chain_sound {n : U64} {c : molt_petit.Chain}
    (h : molt_petit.valid_chain n c = ok true) :
    MoltPetit.Model.validChain n.val (toModelChain c) = true := by
  cases c with
  | Nil => rfl
  | Cons g tl =>
    rw [molt_petit.valid_chain] at h
    obtain ⟨genesis, hgen, h⟩ := molt_petit.bind_inv h
    obtain ⟨links, hlinks, h⟩ := molt_petit.bind_inv h
    obtain ⟨ts, hts, h⟩ := molt_petit.bind_inv h
    split at h
    · rename_i hgent
      split at h
      · rename_i hlinkt
        rw [hgent] at hgen
        rw [hlinkt] at hlinks
        have hg := genesis_ok_sound hgen
        have hl := links_ok_sound hlinks
        obtain ⟨tip, htip, htipv⟩ := tip_slot_from_eq_getLast tl g.slot (toModelBlock g) rfl hts
        have hmd := matured_dense_sound h
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
      · simp at h
    · simp at h

/-- `clone_chain` is the identity under projection. -/
theorem clone_chain_corr : ∀ (c : molt_petit.Chain) {r : molt_petit.Chain},
    molt_petit.clone_chain c = ok r → toModelChain r = toModelChain c := by
  intro c
  induction c with
  | Nil => intro r h; rw [molt_petit.clone_chain] at h; injection h with h; subst h; rfl
  | Cons b tl ih =>
    intro r h
    rw [molt_petit.clone_chain] at h
    obtain ⟨c1, hc1, h⟩ := molt_petit.bind_inv h
    injection h with h; subst h
    rw [toModelChain_cons, toModelChain_cons, ih hc1]

/-- `append_suffix_to_buffer` projects to model list append. -/
theorem append_suffix_corr : ∀ (buffer suffix : molt_petit.Chain) {r : molt_petit.Chain},
    molt_petit.append_suffix_to_buffer buffer suffix = ok r →
    toModelChain r = toModelChain buffer ++ toModelChain suffix := by
  intro buffer
  induction buffer with
  | Nil =>
    intro suffix r h
    rw [molt_petit.append_suffix_to_buffer] at h
    rw [toModelChain_nil, List.nil_append]
    exact clone_chain_corr suffix h
  | Cons b tl ih =>
    intro suffix r h
    rw [molt_petit.append_suffix_to_buffer] at h
    obtain ⟨c, hc, h⟩ := molt_petit.bind_inv h
    injection h with h; subst h
    rw [toModelChain_cons, toModelChain_cons, List.cons_append, ih suffix hc]

/-- `links_to_claim` accepting ⇒ the suffix head links to the model claim's
tip (the claim counterpart of `child_ok_sound`). -/
theorem links_to_claim_sound {cl : molt_petit.CertClaim} {s1 : molt_petit.Block}
    (h : molt_petit.links_to_claim cl s1 = ok true) :
    (toModelBlock s1).height = (toModelClaim cl).tipHeight + 1 ∧
    (toModelClaim cl).tipSlot < (toModelBlock s1).slot ∧
    (toModelBlock s1).prev = some (toModelClaim cl).tipId := by
  rw [molt_petit.links_to_claim] at h
  obtain ⟨⟨cl1, pok⟩, hm, h⟩ := molt_petit.bind_inv h
  obtain ⟨i, hi, h⟩ := molt_petit.bind_inv h
  split at h
  · rename_i hht
    split at h
    · rename_i hst
      injection h with h; subst h
      have hp1 : cl1 = cl ∧ ∃ p, s1.prev = some p ∧
          molt_petit.hash_eq p cl.tip_id = ok true := by
        cases hp : s1.prev with
        | none => rw [hp] at hm; injection hm with hm; simp at hm
        | some p =>
          rw [hp] at hm
          obtain ⟨hev, hhe, hm⟩ := molt_petit.bind_inv hm
          injection hm with hm
          rw [Prod.mk.injEq] at hm
          obtain ⟨hm1, hm2⟩ := hm
          subst hm2
          exact ⟨hm1.symm, p, rfl, hhe⟩
      obtain ⟨hcl1eq, p, hpprev, hpeq⟩ := hp1
      subst cl1
      have hpa := hash_eq_sound hpeq
      have hiv : i.val = cl.tip_height.val + 1 := by
        have := UScalar.add_equiv cl.tip_height 1#u64; simp only [hi] at this
        simpa using this.2.1
      simp only [toModelBlock, toModelClaim, decide_eq_true_eq]
      refine ⟨by scalar_tac, by scalar_tac, ?_⟩
      simp [hpprev, hashToNat, hpa]
    · simp at h
  · simp at h

/-- `suffix_lo` computes the model's maturity lower bound `tipSlot + 2 - n`
with Nat semantics: the extracted `ite` clamps at `0` exactly where Nat
subtraction truncates (young claims, `tip_slot + 2 < n`), and runs the
checked subtraction only where it cannot underflow. -/
theorem suffix_lo_val {n tip_slot lo : U64}
    (h : molt_petit.suffix_lo n tip_slot = ok lo) :
    lo.val = tip_slot.val + 2 - n.val := by
  rw [molt_petit.suffix_lo] at h
  obtain ⟨i, hi, h⟩ := molt_petit.bind_inv h
  have hiv : i.val = tip_slot.val + 2 := by
    have := UScalar.add_equiv tip_slot 2#u64; simp only [hi] at this; simpa using this.2.1
  split at h
  · -- young claim (`n > tip_slot + 2`): the Rust returns `0`, the truncation
    injection h with h; subst h
    scalar_tac
  · -- mature claim: the checked subtraction runs, and `n ≤ tip_slot + 2`
    obtain ⟨hle, hval⟩ : n.val ≤ i.val ∧ i.val = lo.val + n.val := by
      have := UScalar.sub_equiv i n; simp only [h] at this; exact ⟨this.1, this.2.1⟩
    scalar_tac

/-- **Suffix-validator soundness** (Rust analogue of `ts_validateSuffix_sound`):
if `validate_suffix` accepts a non-empty suffix, the projected suffix links to
the projected claim's tip, is internally linked, and every window maturing in
the suffix is dense over the boundary buffer ++ suffix. -/
theorem validate_suffix_sound {n : U64} {cl : molt_petit.CertClaim}
    {s1 : molt_petit.Block} {tl : molt_petit.Chain} {sTip : MoltPetit.Model.Block}
    (hTipS : (toModelBlock s1 :: toModelChain tl).getLast? = some sTip)
    (h : molt_petit.validate_suffix n cl (.Cons s1 tl) = ok true) :
    ((toModelBlock s1).height = (toModelClaim cl).tipHeight + 1 ∧
     (toModelClaim cl).tipSlot < (toModelBlock s1).slot ∧
     (toModelBlock s1).prev = some (toModelClaim cl).tipId) ∧
    MoltPetit.Model.linksOk (toModelBlock s1 :: toModelChain tl) = true ∧
    (∀ u : Nat, ((toModelClaim cl).tipSlot : Int) + 2 - n.val ≤ (u : Int) →
        u + n.val ≤ sTip.slot + 1 →
        MoltPetit.Model.quorum n.val ≤ MoltPetit.Model.windowCount
          ((toModelClaim cl).tail ++ toModelBlock s1 :: toModelChain tl) u n.val) := by
  rw [molt_petit.validate_suffix] at h
  obtain ⟨link, hlink, h⟩ := molt_petit.bind_inv h
  obtain ⟨links, hlinks, h⟩ := molt_petit.bind_inv h
  obtain ⟨ts, hts, h⟩ := molt_petit.bind_inv h
  obtain ⟨buf, hbuf, h⟩ := molt_petit.bind_inv h
  obtain ⟨lo, hlo, h⟩ := molt_petit.bind_inv h
  split at h
  · rename_i hlinkt
    split at h
    · rename_i hlinkst
      rw [hlinkt] at hlink
      rw [hlinkst] at hlinks
      -- structural facts
      have hLink := links_to_claim_sound hlink
      have hLinks := links_from_sound s1 tl hlinks
      -- tip slot
      obtain ⟨sTip2, hT2, hT2v⟩ := tip_slot_from_eq_getLast tl s1.slot (toModelBlock s1) rfl hts
      rw [hTipS] at hT2; injection hT2 with hT2; subst sTip2
      -- buffer projection
      have hbufm := append_suffix_corr cl.tail (.Cons s1 tl) hbuf
      rw [toModelChain_cons] at hbufm
      -- lo: the clamped (Nat-truncated) maturity lower bound
      have hlov : lo.val = cl.tip_slot.val + 2 - n.val := suffix_lo_val hlo
      -- density
      have hmd := matured_dense_sound h
      refine ⟨hLink, hLinks, ?_⟩
      intro u hInt hMat
      have htip : (toModelClaim cl).tipSlot = cl.tip_slot.val := rfl
      rw [htip] at hInt
      have hbound : lo.val ≤ u := by omega
      have hd := hmd u hbound (by omega)
      rw [hbufm] at hd
      exact hd
    · simp at h
  · simp at h

-- ---------------------------------------------------------------------------
-- Signatures and the certified validator
-- ---------------------------------------------------------------------------

/-- A passing `sigs_ok` makes every stripped suffix block `RustSigned`. -/
theorem sigs_ok_signed {C} {I : molt_petit.Crypto C} {n : Std.U64} {crypto : C} :
    ∀ (sc : molt_petit.SignedChain) {stripped : molt_petit.Chain},
    molt_petit.sigs_ok I n crypto sc = ok true → molt_petit.strip_sigs sc = ok stripped →
    ∀ B ∈ toModelChain stripped, RustSigned I crypto n B := by
  intro sc
  induction sc with
  | SNil =>
    intro stripped hsig hstrip B hB
    rw [molt_petit.strip_sigs] at hstrip; injection hstrip with hstrip; subst hstrip
    simp [toModelChain] at hB
  | SCons b sig tl ih =>
    intro stripped hsig hstrip B hB
    rw [molt_petit.sigs_ok] at hsig
    obtain ⟨i, hi, hsig⟩ := molt_petit.bind_inv hsig
    obtain ⟨key, hkey, hsig⟩ := molt_petit.bind_inv hsig
    obtain ⟨vb, hvb, hsig⟩ := molt_petit.bind_inv hsig
    split at hsig
    · rename_i hvbt; rw [hvbt] at hvb
      rw [molt_petit.strip_sigs] at hstrip
      obtain ⟨st, hst, hstrip⟩ := molt_petit.bind_inv hstrip
      injection hstrip with hstrip; subst hstrip
      rw [toModelChain_cons] at hB
      rcases List.mem_cons.mp hB with rfl | hBtl
      · exact ⟨b, i, key, sig, rfl, hi, hkey, hvb⟩
      · exact ih hsig hst B hBtl
    · simp at hsig

/-- **Certified-validator decomposition** (Rust analogue of
`ts_validateCertifiedChain_sound`): a passing `validate_certified_chain`
splits into a verifying certificate, a passing `sigs_ok`, and a passing
`validate_suffix` against the (stripped) suffix. -/
theorem validate_certified_chain_sound {C} {I : molt_petit.Crypto C} {n : Std.U64}
    {crypto : C} {cert : molt_petit.Hash} {suffix : molt_petit.SignedChain}
    (h : molt_petit.validate_certified_chain I n crypto (.CC cert suffix) = ok true) :
    ∃ cl stripped, I.cert_claim crypto cert = ok cl ∧ molt_petit.strip_sigs suffix = ok stripped ∧
      I.cert_verify crypto cert = ok true ∧ molt_petit.sigs_ok I n crypto suffix = ok true ∧
      molt_petit.validate_suffix n cl stripped = ok true := by
  rw [molt_petit.validate_certified_chain] at h
  obtain ⟨cl, hcl, h⟩ := molt_petit.bind_inv h
  obtain ⟨stripped, hstrip, h⟩ := molt_petit.bind_inv h
  obtain ⟨b, hb, h⟩ := molt_petit.bind_inv h
  split at h
  · rename_i hbt; rw [hbt] at hb
    obtain ⟨b1, hb1, h⟩ := molt_petit.bind_inv h
    split at h
    · rename_i hb1t; rw [hb1t] at hb1
      exact ⟨cl, stripped, hcl, hstrip, hb, hb1, h⟩
    · simp at h
  · simp at h

/-! ## Key-index validator soundness -/

/-- `key_mono_against` soundness: acceptance means every same-producer block of
the projected rest declares at least `ki`. -/
theorem key_mono_against_sound {n : U64} (hn : 0 < n.val) {slot ki : U64} :
    ∀ {rest : molt_petit.Chain},
      molt_petit.key_mono_against n slot ki rest = ok true →
      ∀ b ∈ toModelChain rest,
        MoltPetit.Model.producerForSlot n.val slot.val =
          MoltPetit.Model.producerForSlot n.val b.slot →
        ki.val ≤ b.keyIndex
  | molt_petit.Chain.Nil, h, b, hb, hprod => by
    simp [toModelChain] at hb
  | molt_petit.Chain.Cons bb tl, h, b, hb, hprod => by
    rw [molt_petit.key_mono_against] at h
    obtain ⟨i, hi, h⟩ := molt_petit.bind_inv h
    obtain ⟨i1, hi1, h⟩ := molt_petit.bind_inv h
    obtain ⟨ok1, hok1, h⟩ := molt_petit.bind_inv h
    have hiv : i.val = MoltPetit.Model.producerForSlot n.val slot.val := by
      have hc := producer_for_slot_corr n slot hn
      rw [hi] at hc
      simpa using hc
    have hi1v : i1.val = MoltPetit.Model.producerForSlot n.val bb.slot.val := by
      have hc := producer_for_slot_corr n bb.slot hn
      rw [hi1] at hc
      simpa using hc
    have htail : molt_petit.key_mono_against n slot ki tl = ok true := by
      split at h
      · exact h
      · simp at h
    have hok1t : ok1 = true := by
      split at h
      · rename_i hx; exact hx
      · simp at h
    rcases List.mem_cons.mp hb with rfl | hbtl
    · -- b is the projected head: producers agree, so the gate fired
      have hii1 : i = i1 := by
        apply UScalar.eq_of_val_eq
        rw [hiv, hi1v]
        exact hprod
      rw [if_pos hii1] at hok1
      injection hok1 with hok1
      rw [hok1t] at hok1
      show ki.val ≤ bb.key_index.val
      have hle : ki ≤ bb.key_index := of_decide_eq_true hok1
      scalar_tac
    · exact key_mono_against_sound hn htail b hbtl hprod

/-- `key_mono_ok` soundness: Rust acceptance gives the model monotone rule on
the projection. -/
theorem key_mono_ok_sound {n : U64} (hn : 0 < n.val) :
    ∀ {c : molt_petit.Chain},
      molt_petit.key_mono_ok n c = ok true →
      MoltPetit.Model.keyMonoOk n.val (toModelChain c) = true
  | molt_petit.Chain.Nil, _ => rfl
  | molt_petit.Chain.Cons bb tl, h => by
    rw [molt_petit.key_mono_ok] at h
    obtain ⟨b1, hb1, h⟩ := molt_petit.bind_inv h
    have hb1t : b1 = true := by
      split at h
      · rename_i hx; exact hx
      · simp at h
    rw [hb1t] at h
    have htl : molt_petit.key_mono_ok n tl = ok true := by
      simpa using h
    rw [hb1t] at hb1
    show MoltPetit.Model.keyMonoOk n.val (toModelBlock bb :: toModelChain tl) = true
    rw [MoltPetit.Model.keyMonoOk, Bool.and_eq_true]
    refine ⟨?_, key_mono_ok_sound hn htl⟩
    rw [List.all_eq_true]
    intro x hx
    rw [decide_eq_true_eq]
    intro hp
    exact key_mono_against_sound hn hb1 x hx hp

/-- **Indexed-validator soundness.** If the Rust `valid_chain_k` accepts a
chain, the model indexed validator `validChainK` accepts its projection —
the Rust analogue of `ts_validChainK_sound`; on a full chain the `≤` in-force
pin follows (`inForcePinned_of_validChainK`). -/
theorem valid_chain_k_sound {n : U64} {c : molt_petit.Chain} (hn : 0 < n.val)
    (h : molt_petit.valid_chain_k n c = ok true) :
    MoltPetit.Model.validChainK n.val (toModelChain c) = true := by
  rw [molt_petit.valid_chain_k] at h
  obtain ⟨b, hb, h⟩ := molt_petit.bind_inv h
  split at h
  · rename_i hbt
    rw [hbt] at hb
    rw [MoltPetit.Model.validChainK, Bool.and_eq_true]
    exact ⟨valid_chain_sound hb, key_mono_ok_sound hn h⟩
  · simp at h

end Rust
