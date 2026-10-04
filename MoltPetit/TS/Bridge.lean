import MoltPetit.Model.Model
import MoltPetit.Model.Soundness
import MoltPetit.Model.KeyIndex

/-!
# MoltPetit — soundness bridge for the TypeScript implementation

`moltPetit.ts` is the protocol definition; thales compiles it to the
Lean sidecar `Spec/TS.lean` (namespace `MoltPetit`). This
module proves that the emitted validators are *sound* with respect to the
verified model: a chain the TypeScript validator accepts satisfies the
semantic `ValidChain` predicate consumed by the safety proof.

Two representation gaps are bridged:

* **Int vs Nat** — TypeScript `bigint` lowers to `Int`; the model uses
  `Nat`. `toTSChain` injects model chains into the TS representation; all
  lemmas are stated over that image (honest nodes hold model chains).
* **Anchored vs universal density** — the TS validator, restricted to
  structural recursion, checks window density only at *anchored* window
  starts (the lower bound, and `b.slot + 1` for each block `b`). The slide
  lemma (`anchored_density_sound`) shows this implies density of **all**
  matured windows: sliding a window left onto its anchor can only shrink
  its count, because the slid-over stretch contains no blocks.

Main results:

* `ts_validateSuffix_sound` — TS `validateSuffix` accepts → the suffix
  links to the claimed tip, is internally linked, and every window that
  newly matures in the suffix is quorum-dense over `tail ++ suffix`.
* `ts_validateCertifiedChain_sound` / `ts_produceBlockCert_sound` —
  certified-chain validation decomposes into certificate, signature, and
  suffix checks; production ships only what passes that same validation.
* `ts_produceBlockCert_image` / `ts_sigsOk_signed` — production output
  stays representable; a passing `sigsOk` makes every block `TSSigned`.
-/

namespace MoltPetit.Model


/-! ## Arithmetic agreement -/

theorem ts_quorum (n : Nat) : MoltPetit.quorum n = quorum n := by
  unfold MoltPetit.quorum quorum
  omega

theorem ts_maxByzantine {n : Nat} (hn : 1 ≤ n) :
    MoltPetit.maxByzantine n = maxByzantine n := by
  unfold MoltPetit.maxByzantine maxByzantine
  omega

theorem ts_producerForSlot (n slot : Nat) :
    MoltPetit.producerForSlot n slot = producerForSlot n slot := by
  unfold MoltPetit.producerForSlot producerForSlot
  have h : (slot : Int) - (slot : Int) / (n : Int) * (n : Int) =
      (slot : Int) % (n : Int) := by
    rw [Int.emod_def]
    ring
  rw [h]
  omega

/-! ## Structural agreement -/

theorem ts_lengthOf (c : Chain) :
    MoltPetit.lengthOf (toTSChain c) = c.length := by
  induction c with
  | nil => simp [toTSChain, MoltPetit.lengthOf]
  | cons b rest ih =>
    simp [toTSChain, MoltPetit.lengthOf, ih]
    omega

theorem ts_appendChains (a b : Chain) :
    MoltPetit.appendChains (toTSChain a) (toTSChain b) = toTSChain (a ++ b) := by
  induction a with
  | nil => simp [toTSChain, MoltPetit.appendChains]
  | cons x rest ih =>
    simp [toTSChain, MoltPetit.appendChains, ih]

/-- A nonempty list has a last element. -/
private theorem exists_getLast (b : Block) (rest : Chain) :
    ∃ t, (b :: rest).getLast? = some t := by
  cases h : (b :: rest).getLast? with
  | some t => exact ⟨t, rfl⟩
  | none => simp at h

theorem ts_tipSlotFrom (cur : Nat) (rest : Chain) :
    MoltPetit.tipSlotFrom cur (toTSChain rest) =
      ((rest.getLast?.map Block.slot).getD cur : Nat) := by
  induction rest generalizing cur with
  | nil => simp [toTSChain, MoltPetit.tipSlotFrom]
  | cons b rest ih =>
    cases rest with
    | nil => simp [toTSChain, MoltPetit.tipSlotFrom]
    | cons b2 rest2 =>
      obtain ⟨t, ht⟩ := exists_getLast b2 rest2
      rw [show toTSChain (b :: b2 :: rest2) =
        .cons b.slot b.height (b.prev.map Int.ofNat) b.id b.contentsHash b.keyIndex (toTSChain (b2 :: rest2)) from rfl]
      rw [MoltPetit.tipSlotFrom, ih, List.getLast?_cons_cons, ht]
      simp

theorem ts_tipHeightFrom (cur : Nat) (rest : Chain) :
    MoltPetit.tipHeightFrom cur (toTSChain rest) =
      ((rest.getLast?.map Block.height).getD cur : Nat) := by
  induction rest generalizing cur with
  | nil => simp [toTSChain, MoltPetit.tipHeightFrom]
  | cons b rest ih =>
    cases rest with
    | nil => simp [toTSChain, MoltPetit.tipHeightFrom]
    | cons b2 rest2 =>
      obtain ⟨t, ht⟩ := exists_getLast b2 rest2
      rw [show toTSChain (b :: b2 :: rest2) =
        .cons b.slot b.height (b.prev.map Int.ofNat) b.id b.contentsHash b.keyIndex (toTSChain (b2 :: rest2)) from rfl]
      rw [MoltPetit.tipHeightFrom, ih, List.getLast?_cons_cons, ht]
      simp

theorem ts_tipIdFrom (cur : Nat) (rest : Chain) :
    MoltPetit.tipIdFrom cur (toTSChain rest) =
      ((rest.getLast?.map Block.id).getD cur : Nat) := by
  induction rest generalizing cur with
  | nil => simp [toTSChain, MoltPetit.tipIdFrom]
  | cons b rest ih =>
    cases rest with
    | nil => simp [toTSChain, MoltPetit.tipIdFrom]
    | cons b2 rest2 =>
      obtain ⟨t, ht⟩ := exists_getLast b2 rest2
      rw [show toTSChain (b :: b2 :: rest2) =
        .cons b.slot b.height (b.prev.map Int.ofNat) b.id b.contentsHash b.keyIndex (toTSChain (b2 :: rest2)) from rfl]
      rw [MoltPetit.tipIdFrom, ih, List.getLast?_cons_cons, ht]
      simp

/-! ## Window counting -/

/-- Cons-step characterization of the model window count. -/
theorem windowCount_cons (b : Block) (rest : Chain) (u len : Nat) :
    windowCount (b :: rest) u len =
      (if blockInWindow u len b then 1 else 0) + windowCount rest u len := by
  rw [windowCount, windowCount, List.filter_cons]
  split <;> simp [Nat.add_comm]

/-- TS window count over the image of a model chain, for a nonnegative
window start, equals the model window count. -/
theorem ts_windowCount (c : Chain) (u n : Nat) :
    MoltPetit.windowCount (toTSChain c) u n = (windowCount c u n : Nat) := by
  induction c with
  | nil => simp [toTSChain, MoltPetit.windowCount, windowCount]
  | cons b rest ih =>
    rw [show toTSChain (b :: rest) =
      .cons b.slot b.height (b.prev.map Int.ofNat) b.id b.contentsHash b.keyIndex (toTSChain rest) from rfl]
    rw [MoltPetit.windowCount, ih, windowCount_cons]
    have hcond : (decide ((u : Int) ≤ b.slot) && decide ((b.slot : Int) < u + n))
        = blockInWindow u n b := by
      rw [Bool.eq_iff_iff]
      simp only [blockInWindow, Bool.and_eq_true, decide_eq_true_eq]
      omega
    rw [hcond]
    split <;> push_cast <;> omega

/-- For a possibly-negative window start the TS count is bounded by the
model count of the truncated window (all slots are nonnegative, so a
negative start only narrows the window). -/
theorem ts_windowCount_le (c : Chain) (u : Int) (n : Nat) :
    MoltPetit.windowCount (toTSChain c) u n ≤
      (windowCount c u.toNat n : Nat) := by
  induction c with
  | nil => simp [toTSChain, MoltPetit.windowCount, windowCount]
  | cons b rest ih =>
    rw [show toTSChain (b :: rest) =
      .cons b.slot b.height (b.prev.map Int.ofNat) b.id b.contentsHash b.keyIndex (toTSChain rest) from rfl]
    rw [MoltPetit.windowCount, windowCount_cons]
    have himp : (decide (u ≤ (b.slot : Int)) && decide ((b.slot : Int) < u + n)) = true →
        blockInWindow u.toNat n b = true := by
      simp only [blockInWindow, Bool.and_eq_true, decide_eq_true_eq]
      omega
    by_cases hc : (decide (u ≤ (b.slot : Int)) && decide ((b.slot : Int) < u + n)) = true
    · rw [hc, himp hc]
      simp only [if_true]
      push_cast
      omega
    · rw [Bool.not_eq_true] at hc
      rw [hc]
      simp only [Bool.false_eq_true, if_false]
      split <;> push_cast <;> omega

theorem ts_windowDense (c : Chain) (u n : Nat) :
    MoltPetit.windowDense (toTSChain c) u n = windowDense n c u := by
  rw [MoltPetit.windowDense, ts_windowCount, ts_quorum, windowDense,
    Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  omega

/-! ## Links -/

/-- The TS link flag agrees with `childOk`. -/
theorem ts_link_eq_childOk (P b : Block) :
    ((((b.height : Int) == (P.height : Int) + 1) &&
      decide ((P.slot : Int) < (b.slot : Int))) &&
     (b.prev.map Int.ofNat == some (P.id : Int))) = childOk P b := by
  rw [Bool.eq_iff_iff, childOk]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, ?_⟩
    cases hp : b.prev with
    | none => rw [hp] at h3; simp at h3
    | some p =>
      rw [hp] at h3
      simp only [Option.map_some, Option.some.injEq] at h3
      rw [Int.ofNat_eq_natCast] at h3
      congr 1
      exact_mod_cast h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩, ?_⟩
    rw [h3]
    simp

theorem ts_linksFrom (P : Block) (rest : Chain) :
    MoltPetit.linksFrom P.slot P.height P.id (toTSChain rest) =
      linksOk (P :: rest) := by
  induction rest generalizing P with
  | nil => simp [toTSChain, MoltPetit.linksFrom, linksOk]
  | cons b rest ih =>
    rw [show toTSChain (b :: rest) =
      .cons b.slot b.height (b.prev.map Int.ofNat) b.id b.contentsHash b.keyIndex (toTSChain rest) from rfl]
    rw [MoltPetit.linksFrom, show linksOk (P :: b :: rest) =
      (childOk P b && linksOk (b :: rest)) from rfl, ← ih]
    rw [ts_link_eq_childOk]


/-! ## The slide lemma: anchored density implies universal density

The TS validator checks density only at anchored window starts (the lower
bound, and `b.slot + 1` for every block `b`). Sliding an arbitrary matured
window left, one slot at a time, onto its nearest anchor can only shrink
the count: a slot that is no block's slot contributes nothing when it
enters the window from the left. -/

/-- Sliding the window one slot right cannot shrink the count when no
block sits at the departing slot. -/
theorem windowCount_slide {c : Chain} {u n : Nat}
    (h : ∀ b ∈ c, b.slot ≠ u) :
    windowCount c u n ≤ windowCount c (u + 1) n := by
  induction c with
  | nil => simp [windowCount]
  | cons b rest ih =>
    rw [windowCount_cons, windowCount_cons]
    have hb : b.slot ≠ u := h b (List.mem_cons_self ..)
    have hrest := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hind : (if blockInWindow u n b then 1 else 0) ≤
        (if blockInWindow (u + 1) n b then (1 : Nat) else 0) := by
      by_cases hw : blockInWindow u n b = true
      · have hw' : blockInWindow (u + 1) n b = true := by
          simp only [blockInWindow, decide_eq_true_eq] at hw ⊢
          omega
        simp [hw, hw']
      · simp only [Bool.not_eq_true] at hw
        simp only [hw, Bool.false_eq_true, if_false]
        omega
    omega

/-- Anchored density implies density of every matured window at or above
the lower bound. -/
theorem anchored_density_sound {c : Chain} {lo t n : Nat}
    (hbase : lo + n ≤ t + 1 → quorum n ≤ windowCount c lo n)
    (hanchor : ∀ b ∈ c, lo ≤ b.slot + 1 → b.slot + 1 + n ≤ t + 1 →
      quorum n ≤ windowCount c (b.slot + 1) n) :
    ∀ u, lo ≤ u → u + n ≤ t + 1 → quorum n ≤ windowCount c u n := by
  intro u hu
  induction u, hu using Nat.le_induction with
  | base => exact hbase
  | succ u hu ih =>
    intro hmat
    by_cases hb : ∃ b ∈ c, b.slot = u
    · obtain ⟨b, hbc, rfl⟩ := hb
      exact hanchor b hbc (by omega) hmat
    · push Not at hb
      have hslide := windowCount_slide (c := c) (n := n) hb
      have := ih (by omega)
      omega

/-! ## Soundness of the anchored TS density check -/

/-- Extract the per-anchor checks from a passing `anchorsDense`. -/
theorem ts_anchorsDense_sound {all : Chain} {lo : Int} {t n : Nat} :
    ∀ {rest : Chain},
    MoltPetit.anchorsDense (toTSChain all) (toTSChain rest) lo t n = true →
    ∀ b ∈ rest, lo ≤ (b.slot : Int) + 1 → b.slot + 1 + n ≤ t + 1 →
      quorum n ≤ windowCount all (b.slot + 1) n := by
  intro rest
  induction rest with
  | nil =>
    intro _ b hb
    simp at hb
  | cons x rest ih =>
    intro h b hb hlo hmat
    rw [show toTSChain (x :: rest) =
      .cons x.slot x.height (x.prev.map Int.ofNat) x.id x.contentsHash x.keyIndex (toTSChain rest) from rfl,
      MoltPetit.anchorsDense] at h
    try dsimp only at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.mp hb with rfl | hb'
    · -- the head anchor: its check must have fired
      have hcond : (decide (lo ≤ (b.slot : Int) + 1) &&
          decide ((b.slot : Int) + 1 + n ≤ (t : Int) + 1)) = true := by
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨hlo, by push_cast; omega⟩
      rw [if_pos hcond] at h
      have hdense := h.1
      have : ((b.slot : Int) + 1) = ((b.slot + 1 : Nat) : Int) := by push_cast; ring
      rw [this, ts_windowDense] at hdense
      rw [windowDense, decide_eq_true_eq] at hdense
      exact hdense
    · exact ih h.2 b hb' hlo hmat

/-- Soundness of the full anchored density check `maturedDense`: every
window at or above the (possibly negative) lower bound that is matured at
`t` is quorum-dense. -/
theorem ts_maturedDense_sound {c : Chain} {lo : Int} {t n : Nat}
    (h : MoltPetit.maturedDense (toTSChain c) lo t n = true) :
    ∀ u : Nat, lo ≤ (u : Int) → u + n ≤ t + 1 → quorum n ≤ windowCount c u n := by
  rw [MoltPetit.maturedDense] at h
  try dsimp only at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hbase, hanchors⟩ := h
  have hmain := anchored_density_sound (c := c) (lo := lo.toNat) (t := t) (n := n)
    ?base ?anchor
  case base =>
    intro hmat
    have hcond : lo + (n : Int) ≤ (t : Int) + 1 := by
      have := Int.self_le_toNat lo
      push_cast
      omega
    rw [if_pos hcond] at hbase
    rw [MoltPetit.windowDense, ts_quorum] at hbase
    have hle := ts_windowCount_le c lo n
    rw [decide_eq_true_eq] at hbase
    omega
  case anchor =>
    intro b hb h1 h2
    exact ts_anchorsDense_sound hanchors b hb (by push_cast; omega) h2
  intro u hu hmat
  exact hmain u (by omega) hmat

/-! ## Validator soundness -/

/-- `getD` through a cons `getLast?`. -/
private theorem getD_getLast_cons {g tip : Block} {rest : Chain}
    (f : Block → Nat) (hTip : (g :: rest).getLast? = some tip) :
    ((rest.getLast?.map f).getD (f g)) = f tip := by
  cases rest with
  | nil =>
    simp at hTip
    simp [hTip]
  | cons b2 rest2 =>
    rw [List.getLast?_cons_cons] at hTip
    simp [hTip]

/--
**TS plain-validator soundness.** A chain the TypeScript `validChain` accepts
(over the model→TS injection `toTSChain`) is semantically `ValidChain` in the
model — the TypeScript analogue of the Rust bridge's `valid_chain_sound`
composed to `ValidChain` (`Rust.rust_valid_chain_sound`). This is the hook that
carries model-level guarantees *stated about* `ValidChain` (e.g. the exposure-model
agreement `exposure_agreement`) over to the function the TypeScript node runs. -/
theorem ts_validChain_sound {n : Nat} {c : Chain}
    (h : MoltPetit.validChain (n : Int) (toTSChain c) = true) :
    ValidChain n c := by
  match c with
  | [] =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k B hAt; simp [blockAt?] at hAt
    · exact List.Pairwise.nil
    · intro k B hAt; simp [blockAt?] at hAt
    · intro m D hAt; simp [blockAt?] at hAt
  | g :: rest =>
    obtain ⟨tip, hTip⟩ : ∃ tip, (g :: rest).getLast? = some tip := by
      cases hL : (g :: rest).getLast? with
      | some t => exact ⟨t, rfl⟩
      | none => simp at hL
    rw [show toTSChain (g :: rest) =
        .cons g.slot g.height (g.prev.map Int.ofNat) g.id g.contentsHash g.keyIndex (toTSChain rest) from rfl,
      MoltPetit.validChain] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hGen, hLinks⟩, hDense⟩ := h
    -- genesis: height 0 and no parent
    obtain ⟨hHt, hPrev⟩ := hGen
    have hHt0 : g.height = 0 := by
      have hh : ((g.height : Int) == 0) = true := hHt
      rw [beq_iff_eq] at hh
      exact_mod_cast hh
    have hPrev0 : g.prev = none := by
      cases hp : g.prev with
      | none => rfl
      | some x => rw [hp] at hPrev; simp at hPrev
    -- internal links
    rw [ts_linksFrom] at hLinks
    have hChain := linksOk_isChain hLinks
    have hAt0 : ∀ ⦃B : Block⦄, blockAt? (g :: rest) 0 = some B → B = g := by
      intro B hB; unfold blockAt? at hB; simp at hB; exact hB.symm
    have hSeq : SequentialHeights (g :: rest) :=
      sequentialHeights_of_checks (fun B hB => (hAt0 hB) ▸ hHt0) hChain
    have hS : StrictSlots (g :: rest) := strictSlots_of_checks hChain
    have hP : ParentLinked (g :: rest) :=
      parentLinked_of_checks (fun B hB => (hAt0 hB) ▸ hPrev0) hChain
    -- matured-window density, via the anchored-check soundness lemma
    rw [show (MoltPetit.Chain.cons (g.slot : Int) (g.height : Int)
        (g.prev.map Int.ofNat) (g.id : Int) g.contentsHash g.keyIndex (toTSChain rest))
          = toTSChain (g :: rest) from rfl,
      ts_tipSlotFrom, getD_getLast_cons Block.slot hTip] at hDense
    have hdense := ts_maturedDense_sound hDense
    have hmwd : maturedWindowsDense n (g :: rest) tip.slot = true := by
      rw [maturedWindowsDense, List.all_eq_true]
      intro u hu
      rw [List.mem_range] at hu
      rw [windowDense, decide_eq_true_eq]
      exact hdense u (by exact_mod_cast Nat.zero_le u) (by omega)
    exact ⟨hSeq, hS, hP, maturedDense_of_check hS hTip hmwd⟩

/-! ## Suffix-validation soundness -/


/-! ## Key-index validator agreement -/

/-- `monoAgainst` over the TS image agrees with the model-side per-block
monotone check: every same-producer block of `rest` declares at least `ki`. -/
theorem ts_monoAgainst {n slot ki : Nat} (rest : Chain) :
    MoltPetit.monoAgainst n slot ki (toTSChain rest) = true ↔
      ∀ b ∈ rest, producerForSlot n slot = producerForSlot n b.slot →
        ki ≤ b.keyIndex := by
  induction rest with
  | nil => simp [toTSChain, MoltPetit.monoAgainst]
  | cons b rest ih =>
    rw [show toTSChain (b :: rest) =
      .cons b.slot b.height (b.prev.map Int.ofNat) b.id b.contentsHash b.keyIndex
        (toTSChain rest) from rfl]
    rw [MoltPetit.monoAgainst, Bool.and_eq_true]
    constructor
    · rintro ⟨hok, hrest⟩ x hx hprod
      rcases List.mem_cons.mp hx with rfl | hxr
      · rw [ts_producerForSlot, ts_producerForSlot] at hok
        split at hok
        · have : (ki : Int) ≤ x.keyIndex := of_decide_eq_true hok
          exact_mod_cast this
        · next hbeq =>
            exact absurd (by rw [beq_iff_eq]; exact_mod_cast hprod) hbeq
      · exact ih.mp hrest x hxr hprod
    · intro h
      refine ⟨?_, ih.mpr fun x hx hp => h x (List.mem_cons_of_mem _ hx) hp⟩
      rw [ts_producerForSlot, ts_producerForSlot]
      split
      · next hbeq =>
          rw [beq_iff_eq] at hbeq
          have hp' : producerForSlot n slot = producerForSlot n b.slot := by
            exact_mod_cast hbeq
          exact decide_eq_true (by exact_mod_cast h b (List.mem_cons_self ..) hp')
      · rfl

/-- The TypeScript monotone key-index rule agrees with the model's
`keyMonoOk` on images of model chains. -/
theorem ts_keyMonoOk {n : Nat} (c : Chain) :
    MoltPetit.keyMonoOk n (toTSChain c) = true ↔ keyMonoOk n c = true := by
  induction c with
  | nil => simp [toTSChain, MoltPetit.keyMonoOk, keyMonoOk]
  | cons b rest ih =>
    rw [show toTSChain (b :: rest) =
      .cons b.slot b.height (b.prev.map Int.ofNat) b.id b.contentsHash b.keyIndex
        (toTSChain rest) from rfl]
    rw [MoltPetit.keyMonoOk, keyMonoOk, Bool.and_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨hmono, hrest⟩
      refine ⟨?_, ih.mp hrest⟩
      rw [List.all_eq_true]
      intro x hx
      rw [decide_eq_true_eq]
      intro hprod
      exact (ts_monoAgainst rest).mp hmono x hx hprod
    · rintro ⟨hall, hrest⟩
      refine ⟨(ts_monoAgainst rest).mpr ?_, ih.mpr hrest⟩
      intro x hx hprod
      rw [List.all_eq_true] at hall
      have := hall x hx
      rw [decide_eq_true_eq] at this
      exact this hprod

/-- **TS indexed-validator soundness.** A chain the TypeScript `validChainK`
accepts is semantically valid **and** key-index monotone — from which the
`≤` in-force pin follows on the full chain
(`inForcePinned_of_validChainK`), i.e. the TS validator enforces the
key-rotation validator `validChainK'` at full-chain level. (The
certificate-boundary form — a suffix checked against a claim-carried floor
snapshot — awaits the claim-format extension; see `GroundedCertK`.) -/
theorem ts_validChainK_sound {n : Nat} {c : Chain}
    (h : MoltPetit.validChainK (n : Int) (toTSChain c) = true) :
    ValidChain n c ∧ KeyIndexMonotone n c := by
  rw [MoltPetit.validChainK, Bool.and_eq_true] at h
  exact ⟨ts_validChain_sound h.1, keyMonoOk_sound ((ts_keyMonoOk c).mp h.2)⟩

/--
**TS suffix-validation soundness.** A nonempty suffix accepted by the
TypeScript `validateSuffix` against a claim:

1. links to the claimed tip (height/slot/parent-id),
2. is internally linked, and
3. makes every window newly matured at the suffix tip quorum-dense,
   counted over `claim.tail ++ suffix`.
-/
theorem ts_validateSuffix_sound {n : Nat} {cl : CertClaim}
    {s₁ : Block} {srest : Chain} {sTip : Block}
    (hTip : (s₁ :: srest).getLast? = some sTip)
    (h : MoltPetit.validateSuffix n (toTSClaim cl) (toTSChain (s₁ :: srest)) = true) :
    (s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId) ∧
    linksOk (s₁ :: srest) = true ∧
    (∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
      quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n) := by
  rw [show toTSChain (s₁ :: srest) =
    .cons s₁.slot s₁.height (s₁.prev.map Int.ofNat) s₁.id s₁.contentsHash s₁.keyIndex (toTSChain srest) from rfl,
    MoltPetit.validateSuffix] at h
  simp only [toTSClaim] at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hLink, hLinks⟩, hDense⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · -- the claim link
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hLink
    obtain ⟨⟨h1, h2⟩, h3⟩ := hLink
    refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, ?_⟩
    cases hp : s₁.prev with
    | none => rw [hp] at h3; simp at h3
    | some p =>
      rw [hp] at h3
      simp only [Option.map_some, Option.some.injEq] at h3
      rw [Int.ofNat_eq_natCast] at h3
      congr 1
      exact_mod_cast h3
  · rw [ts_linksFrom] at hLinks
    exact hLinks
  · -- density over tail ++ suffix
    rw [show (MoltPetit.Chain.cons (s₁.slot : Int) (s₁.height : Int)
        (s₁.prev.map Int.ofNat) (s₁.id : Int) s₁.contentsHash s₁.keyIndex (toTSChain srest)) = toTSChain (s₁ :: srest)
      from rfl, ts_appendChains, ts_tipSlotFrom, getD_getLast_cons Block.slot hTip] at hDense
    exact ts_maturedDense_sound hDense

/-! ## Signed chains and certified chains -/

/-- Stripping signatures commutes with the injection. -/
theorem ts_stripSigs (sc : SignedChain MoltPetit.RawSignature) :
    MoltPetit.stripSigs (toTSSigned sc) = toTSChain (stripSigs sc) := by
  induction sc with
  | nil => simp [toTSSigned, MoltPetit.stripSigs, stripSigs, toTSChain]
  | cons sb rest ih =>
    rw [show toTSSigned (sb :: rest) =
      .cons sb.block.slot sb.block.height (sb.block.prev.map Int.ofNat)
        sb.block.id sb.block.contentsHash sb.block.keyIndex sb.sig (toTSSigned rest) from rfl,
      MoltPetit.stripSigs, ih]
    rfl

/--
**TS certified-chain validation soundness.** Acceptance means: the
certificate verifies, every suffix signature verifies, and the stripped
suffix passes the structural suffix checks against the certificate's claim.
-/
theorem ts_validateCertifiedChain_sound {n : Nat}
    {sigOps : MoltPetit.SigOps} {certOps : MoltPetit.CertOps}
    {h : MoltPetit.RawCertificate} {sc : SignedChain MoltPetit.RawSignature}
    (hv : MoltPetit.validateCertifiedChain n sigOps certOps
            (.cc h (toTSSigned sc)) = true) :
    certOps.verify h = true ∧
    MoltPetit.sigsOk n sigOps (toTSSigned sc) = true ∧
    MoltPetit.validateSuffix n (certOps.claim h)
      (toTSChain (stripSigs sc)) = true := by
  rw [MoltPetit.validateCertifiedChain, Bool.and_eq_true, Bool.and_eq_true,
    ts_stripSigs] at hv
  exact ⟨hv.1.1, hv.1.2, hv.2⟩

/--
**TS certified production soundness.** A successful `produceBlockCert` call
happens only in the caller's own slot, and its result passed the very same
`validateCertifiedChain` every other node will run — production validates
the compacted result before shipping it, so no property of the compaction
path needs to be trusted.
-/
theorem ts_produceBlockCert_sound {n me slot newId : Nat}
    {contentsHash keyIndex : Nat} {sk : MoltPetit.RawSecretKey}
    {sigOps : MoltPetit.SigOps} {certOps : MoltPetit.CertOps}
    {cert : MoltPetit.RawCertificate} {suffix : MoltPetit.SignedChain}
    {h : MoltPetit.RawCertificate} {sfx : MoltPetit.SignedChain}
    (hp : MoltPetit.produceBlockCert n me slot newId contentsHash keyIndex sk sigOps certOps
            cert suffix = .cc h sfx) :
    producerForSlot n slot = me ∧
    MoltPetit.validateCertifiedChain n sigOps certOps (.cc h sfx) = true := by
  rw [MoltPetit.produceBlockCert, ts_producerForSlot] at hp
  by_cases hg : (((producerForSlot n slot : Nat) : Int) != ((me : Nat) : Int)) = true
  · rw [if_pos hg] at hp
    exact absurd hp (by simp)
  · have hMine : producerForSlot n slot = me := by
      rw [bne_iff_ne] at hg
      push Not at hg
      exact_mod_cast hg
    rw [if_neg hg] at hp
    dsimp only at hp
    split at hp
    · rename_i hval
      rw [hp] at hval
      exact ⟨hMine, hval⟩
    · exact absurd hp (by simp)

/-! ## Signature facts extracted from TS validation -/

/-- A passing TS `sigsOk` makes every block of the suffix `TSSigned`. -/
theorem ts_sigsOk_signed {n : Nat} {sigOps : MoltPetit.SigOps} :
    ∀ {sc : SignedChain MoltPetit.RawSignature},
      MoltPetit.sigsOk n sigOps (toTSSigned sc) = true →
      ∀ B ∈ stripSigs sc, TSSigned n sigOps B := by
  intro sc
  induction sc with
  | nil =>
    intro _ B hB
    simp [stripSigs] at hB
  | cons sb rest ih =>
    intro h B hB
    rw [show toTSSigned (sb :: rest) =
      .cons sb.block.slot sb.block.height (sb.block.prev.map Int.ofNat)
        sb.block.id sb.block.contentsHash sb.block.keyIndex sb.sig (toTSSigned rest) from rfl,
      MoltPetit.sigsOk] at h
    try dsimp only at h
    rw [Bool.and_eq_true, ts_producerForSlot] at h
    rw [show stripSigs (sb :: rest) = sb.block :: stripSigs rest from rfl] at hB
    rcases List.mem_cons.mp hB with rfl | hBmem
    · exact ⟨sb.sig, h.1⟩
    · exact ih h.2 B hBmem

/-! ## Production output stays representable -/

/-- The signed-chain injection turns appends into TS `appendSigned`. -/
theorem ts_appendSigned (a b : SignedChain MoltPetit.RawSignature) :
    MoltPetit.appendSigned (toTSSigned a) (toTSSigned b) = toTSSigned (a ++ b) := by
  induction a with
  | nil => rfl
  | cons sb rest ih =>
    rw [show toTSSigned (sb :: rest) =
      .cons sb.block.slot sb.block.height (sb.block.prev.map Int.ofNat)
        sb.block.id sb.block.contentsHash sb.block.keyIndex sb.sig (toTSSigned rest) from rfl,
      MoltPetit.appendSigned]
    try dsimp only
    rw [ih]
    rfl

/-- TS `tryCut` only ever cuts to (a tail-slice of) its input suffix: if
the input is the image of a model signed chain, so is any cut it finds. -/
theorem ts_tryCut_image {n : Int} {certOps : MoltPetit.CertOps} :
    ∀ (msc : SignedChain MoltPetit.RawSignature)
      (oldCl : MoltPetit.CertClaim) (dropped : MoltPetit.Chain)
      (h : MoltPetit.RawCertificate) {sfx : MoltPetit.SignedChain},
      MoltPetit.tryCut n certOps oldCl dropped (toTSSigned msc) = .cc h sfx →
      ∃ msfx : SignedChain MoltPetit.RawSignature, sfx = toTSSigned msfx := by
  intro msc
  induction msc with
  | nil =>
    intro oldCl dropped h sfx hc
    rw [show toTSSigned [] = .nil from rfl, MoltPetit.tryCut] at hc
    exact absurd hc (by simp)
  | cons sb rest ih =>
    intro oldCl dropped h sfx hc
    rw [show toTSSigned (sb :: rest) =
      .cons sb.block.slot sb.block.height (sb.block.prev.map Int.ofNat)
        sb.block.id sb.block.contentsHash sb.block.keyIndex sb.sig (toTSSigned rest) from rfl,
      MoltPetit.tryCut] at hc
    split at hc
    · exact absurd hc (by simp)
    · dsimp only at hc
      unfold MoltPetit.orFirst at hc
      split at hc
      · -- no deeper cut: the head cut, when taken, keeps the input's tail
        unfold MoltPetit.ccIf at hc
        split at hc
        · rw [MoltPetit.CertifiedChain.cc.injEq] at hc
          exact ⟨rest, hc.2.symm⟩
        · exact absurd hc (by simp)
      · -- a deeper cut was found: it is a cut of the input's tail
        exact ih _ _ h hc

/-- TS `compactChain` only ever returns (a tail-slice of) its input suffix:
if the input is the image of a model signed chain, so is the output. -/
theorem ts_compactChain_image {n : Int} {certOps : MoltPetit.CertOps} :
    ∀ (msc : SignedChain MoltPetit.RawSignature)
      (cert h : MoltPetit.RawCertificate) {sfx : MoltPetit.SignedChain},
      MoltPetit.compactChain n certOps cert (toTSSigned msc) = .cc h sfx →
      ∃ msfx : SignedChain MoltPetit.RawSignature, sfx = toTSSigned msfx := by
  intro msc cert h sfx hc
  rw [MoltPetit.compactChain] at hc
  try dsimp only at hc
  unfold MoltPetit.orKeep at hc
  split at hc
  · -- no cut found: the suffix ships unchanged
    rw [MoltPetit.CertifiedChain.cc.injEq] at hc
    exact ⟨msc, hc.2.symm⟩
  · -- a cut was found: it is a tail-slice of the input
    exact ts_tryCut_image msc _ _ h hc

/--
**Production output is representable.** When the producer's stored
certificate carries a model claim (it does whenever the certificate
verifies — certificate unforgeability) and its stored suffix is the image
of a model signed chain, then whatever `produceBlockCert` ships is again
the image of a model signed chain. Together with
`ts_produceBlockCert_sound` this lets every downstream theorem stated over
model suffixes consume produced chains directly.
-/
theorem ts_produceBlockCert_image {n me slot newId : Nat}
    {contentsHash keyIndex : Nat} {sk : MoltPetit.RawSecretKey}
    {sigOps : MoltPetit.SigOps} {certOps : MoltPetit.CertOps}
    {cert : MoltPetit.RawCertificate}
    {msc : SignedChain MoltPetit.RawSignature}
    {mcl : CertClaim} (hclaim : certOps.claim cert = toTSClaim mcl)
    {h : MoltPetit.RawCertificate} {sfx : MoltPetit.SignedChain}
    (hp : MoltPetit.produceBlockCert n me slot newId contentsHash keyIndex sk sigOps certOps
            cert (toTSSigned msc) = .cc h sfx) :
    ∃ msfx : SignedChain MoltPetit.RawSignature, sfx = toTSSigned msfx := by
  rw [MoltPetit.produceBlockCert] at hp
  split at hp
  · exact absurd hp (by simp)
  · dsimp only at hp
    rw [hclaim, ts_stripSigs] at hp
    simp only [toTSClaim] at hp
    rw [ts_tipHeightFrom, ts_tipIdFrom] at hp
    set H : Nat := (((stripSigs msc).getLast?.map Block.height).getD mcl.tipHeight)
      with hH
    set I : Nat := (((stripSigs msc).getLast?.map Block.id).getD mcl.tipId) with hI
    rw [show ((H : Int) + 1) = ((H + 1 : Nat) : Int) by push_cast; ring] at hp
    rw [show (MoltPetit.SignedChain.cons (slot : Int) ((H + 1 : Nat) : Int)
        (some (I : Int)) (newId : Int) contentsHash (keyIndex : Int)
        (sigOps.sign sk slot ((H + 1 : Nat) : Int) I newId) .nil) =
      toTSSigned [⟨⟨slot, H + 1, some I, newId, contentsHash, keyIndex⟩,
        sigOps.sign sk slot ((H + 1 : Nat) : Int) I newId⟩] from rfl,
      ts_appendSigned] at hp
    split at hp
    · exact ts_compactChain_image _ _ h hp
    · exact absurd hp (by simp)

end MoltPetit.Model
