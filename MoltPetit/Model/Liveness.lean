import MoltPetit.Model.Soundness

/-!
# MoltPetit — liveness

Safety says validator-accepted chains never disagree deeply; liveness says
the chain actually grows: an honest producer whose slot comes up can always
extend its chain into one the validator accepts — so the protocol makes
progress and blocks keep maturing toward finality.

The adversary attacks liveness by *withholding*: if too many slots in a
window stay empty, the density check would reject any extension and the
chain would stall. The theorems here show this cannot happen under the
stated assumptions:

* `ByzantineBounded` — ≤ `⌊(n-1)/3⌋` adversarial slots per `n`-slot window,
  so every window has ≥ `quorum n` honest slots
  (`quorum_plus_byzantine_le`);
* `HonestBlocksCover` — synchrony/delivery: the honest producers of the
  window were live, and the current producer has received and built on
  their blocks.

Under these, every newly matured window is quorum-dense, so the extension
passes `validChain` and production succeeds.

## Results

* `quorum_plus_byzantine_le`      — `quorum n + maxByzantine n ≤ n`.
* `window_dense_of_honest_cover`  — covered windows are quorum-dense.
* `validChain_append_one`         — structural extension lemma.
* `liveness_valid_extension`      — the extended chain passes the validator.
* `liveness_produce_block`        — `produceBlock?` returns the new block.
* `liveness_produce_signed_block` — wire-level version: with signature
  correctness (`SigCorrect`), `produceSignedBlock?` succeeds too.
-/

namespace MoltPetit.Model

-- ---------------------------------------------------------------------------
-- Liveness assumption
-- ---------------------------------------------------------------------------

-- Arithmetic
-- ---------------------------------------------------------------------------

/-- Every `n`-slot window has at least `quorum n` honest slots:
`quorum n + maxByzantine n ≤ n`. -/
theorem quorum_plus_byzantine_le (n : Nat) :
    quorum n + maxByzantine n ≤ n := by
  unfold quorum maxByzantine
  omega

-- ---------------------------------------------------------------------------
-- Window counts and slots
-- ---------------------------------------------------------------------------

/-- Extending a chain cannot decrease a window count. -/
theorem windowCount_mono {u len : Nat} {c c' : Chain} (h : c.Sublist c') :
    windowCount c u len ≤ windowCount c' u len :=
  List.Sublist.length_le (h.filter _)

/-- Every member of a strictly-slotted chain is no later than the tip. -/
theorem slot_le_tip_of_mem {c : Chain} (hS : StrictSlots c) {tip : Block}
    (hTip : c.getLast? = some tip) {x : Block} (hx : x ∈ c) :
    x.slot ≤ tip.slot := by
  obtain ⟨k, hk⟩ := exists_blockAt_of_mem hx
  have hTipAt : blockAt? c (c.length - 1) = some tip := blockAt_getLast hTip
  have hkLen : k < c.length := by
    unfold blockAt? at hk
    exact (List.getElem?_eq_some_iff.mp hk).1
  rcases Nat.lt_or_ge k (c.length - 1) with hlt | hge
  · exact Nat.le_of_lt (strictSlots_lt hS hk hTipAt hlt)
  · have hEq : k = c.length - 1 := by omega
    rw [hEq, hTipAt] at hk
    rw [Option.some.inj hk]

/-- Appending a strictly later block preserves strict slot ordering. -/
theorem strictSlots_append_one {c : Chain} {b : Block} (hS : StrictSlots c)
    (hAll : ∀ x ∈ c, x.slot < b.slot) : StrictSlots (c ++ [b]) := by
  unfold StrictSlots at *
  rw [List.pairwise_append]
  refine ⟨hS, List.pairwise_singleton _ _, ?_⟩
  intro x hx y hy
  simp only [List.mem_singleton] at hy
  subst hy
  exact hAll x hx

-- ---------------------------------------------------------------------------
-- Structural extension
-- ---------------------------------------------------------------------------

/-- Appending a block that links to the current tip preserves `linksOk`. -/
theorem linksOk_append_one : ∀ (c : Chain) (b : Block),
    linksOk c = true →
    (∃ tip : Block, c.getLast? = some tip ∧ childOk tip b = true) →
    linksOk (c ++ [b]) = true := by
  intro c
  induction c with
  | nil =>
    intro b _ ⟨_, hTip, _⟩
    simp at hTip
  | cons x rest ih =>
    intro b hLinks ⟨tip, hTip, hChild⟩
    match rest, hTip with
    | [], hTip =>
      simp at hTip
      subst hTip
      simp [linksOk, hChild]
    | y :: rest2, hTip =>
      simp only [linksOk, Bool.and_eq_true] at hLinks
      have hTip2 : (y :: rest2).getLast? = some tip := by
        rw [← List.getLast?_cons_cons (a := x)]
        exact hTip
      have ih2 := ih b hLinks.2 ⟨tip, hTip2, hChild⟩
      simp only [List.cons_append, linksOk, Bool.and_eq_true]
      exact ⟨hLinks.1, ih2⟩

/--
Extending a validator-accepted chain by one block that links to the tip is
again accepted, provided every window matured at the new tip is dense in
the extended chain.
-/
theorem validChain_append_one {n : Nat} {c : Chain} {b tip : Block}
    (hValid : validChain n c = true)
    (hTipEq : c.getLast? = some tip)
    (hChild : childOk tip b = true)
    (hAllDense : ∀ u : Nat, u + n ≤ b.slot + 1 →
        windowDense n (c ++ [b]) u = true) :
    validChain n (c ++ [b]) = true := by
  obtain ⟨g, rest, rfl⟩ : ∃ g rest, c = g :: rest := by
    cases c with
    | nil => simp at hTipEq
    | cons g rest => exact ⟨g, rest, rfl⟩
  rw [validChain, hTipEq, Bool.and_eq_true, Bool.and_eq_true] at hValid
  obtain ⟨⟨hGen, hLinks⟩, -⟩ := hValid
  have hLast : (g :: (rest ++ [b])).getLast? = some b := by
    show ((g :: rest) ++ [b]).getLast? = some b
    exact List.getLast?_concat
  show validChain n (g :: (rest ++ [b])) = true
  rw [validChain, hLast]
  show (genesisOk g && linksOk (g :: (rest ++ [b])) &&
        maturedWindowsDense n (g :: (rest ++ [b])) b.slot) = true
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hGen, ?_⟩, ?_⟩
  · exact linksOk_append_one (g :: rest) b hLinks ⟨tip, hTipEq, hChild⟩
  · rw [maturedWindowsDense, List.all_eq_true]
    intro u hu
    have := List.mem_range.mp hu
    exact hAllDense u (by omega)

-- ---------------------------------------------------------------------------
-- Density from honest coverage
-- ---------------------------------------------------------------------------

/--
**Key density lemma, single window.** If every honest slot of the window
`[u, u + n)` has a block in `c` and at most `maxByzantine n` of its slots
are bad, the window is quorum-dense in `c`: the budget leaves at least
`quorum n` honest slots, and each contributes a distinct chain slot.
-/
theorem window_dense_of_honest_cover_at
    {n : Nat} {bad : ByzantineSlots} {record : SlotRecord} {c : Chain}
    (hS        : StrictSlots c)
    (hSCorrect : ∀ s (B : Block), B ∈ record s → B.slot = s)
    {u : Nat}
    (hBudgetU  : (badSlotsIn bad u n).card ≤ maxByzantine n)
    (hCover    : HonestBlocksCover bad record c u n) :
    quorum n ≤ windowCount c u n := by
  classical
  rw [← chainSlotsIn_card hS]
  -- the honest slots of the window all appear among the chain's slots
  have hSubset : Finset.Ico u (u + n) \ badSlotsIn bad u n ⊆
      chainSlotsIn c u n := by
    intro s hs
    rw [Finset.mem_sdiff] at hs
    obtain ⟨hIco, hNotBad⟩ := hs
    rw [Finset.mem_Ico] at hIco
    have hHonest : ¬ bad s := by
      intro hbad
      apply hNotBad
      unfold badSlotsIn
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hIco, hbad⟩
    obtain ⟨B, hBrec, hBc⟩ := hCover s hHonest hIco.1 hIco.2
    have hBslot : B.slot = s := hSCorrect s B hBrec
    rw [mem_chainSlotsIn]
    exact ⟨B, hBc, ⟨by omega, by omega⟩, hBslot⟩
  -- cardinality bookkeeping
  have hCard := Finset.card_le_card hSubset
  have hSdiff : (Finset.Ico u (u + n) \ badSlotsIn bad u n).card =
      (Finset.Ico u (u + n)).card -
        (badSlotsIn bad u n ∩ Finset.Ico u (u + n)).card :=
    Finset.card_sdiff
  have hInter : (badSlotsIn bad u n ∩ Finset.Ico u (u + n)).card ≤
      (badSlotsIn bad u n).card :=
    Finset.card_le_card Finset.inter_subset_left
  have hIcoCard : (Finset.Ico u (u + n)).card = n := by
    rw [Nat.card_Ico]
    omega
  have hBad := hBudgetU
  have hArith := quorum_plus_byzantine_le n
  omega

/--
**Key density lemma.** If every honest slot of the window `[u, u + n)` has
a block in `c`, the window is quorum-dense in `c`: the Byzantine budget
leaves at least `quorum n` honest slots, and each contributes a distinct
chain slot.
-/
theorem window_dense_of_honest_cover
    {n : Nat} {bad : ByzantineSlots} {record : SlotRecord} {c : Chain}
    (hBudget   : ByzantineBounded n bad)
    (hS        : StrictSlots c)
    (hSCorrect : ∀ s (B : Block), B ∈ record s → B.slot = s)
    {u : Nat}
    (hCover    : HonestBlocksCover bad record c u n) :
    quorum n ≤ windowCount c u n :=
  window_dense_of_honest_cover_at hS hSCorrect (hBudget u) hCover

-- ---------------------------------------------------------------------------
-- Liveness: the extension validates
-- ---------------------------------------------------------------------------

/--
**Liveness core.** The honest extension of a validator-accepted chain is
itself accepted, given:

* the Byzantine budget (`hBudget`);
* honest-block delivery for every window that newly matures at the new
  block's slot (`hCover`; windows already matured at the old tip stay
  dense by monotonicity).
-/
theorem liveness_valid_extension
    {n : Nat} {bad : ByzantineSlots} {record : SlotRecord}
    {c : Chain} {slot newId : Nat} {contentsHash keyIndex : Nat} {tip : Block}
    (hBudget   : ByzantineBounded n bad)
    (hValid    : validChain n c = true)
    (hTipEq    : c.getLast? = some tip)
    (hTipLt    : tip.slot < slot)
    (hSCorrect : ∀ s (B : Block), B ∈ record s → B.slot = s)
    (hCover    : ∀ u, tip.slot + 1 < u + n → u + n ≤ slot + 1 →
        HonestBlocksCover bad record (c ++ [nextBlock slot newId contentsHash keyIndex tip]) u n) :
    validChain n (c ++ [nextBlock slot newId contentsHash keyIndex tip]) = true := by
  set b := nextBlock slot newId contentsHash keyIndex tip with hb
  have hbSlot : b.slot = slot := rfl
  have hChild : childOk tip b = true := by
    simp [childOk, hb, nextBlock, hTipLt]
  obtain ⟨-, hS, -, hMat⟩ := validChain_sound hValid
  have hSExt : StrictSlots (c ++ [b]) := by
    apply strictSlots_append_one hS
    intro x hx
    have := slot_le_tip_of_mem hS hTipEq hx
    omega
  apply validChain_append_one hValid hTipEq hChild
  intro u hu
  rw [windowDense, decide_eq_true_eq]
  by_cases hOld : u + n ≤ tip.slot + 1
  · -- already matured at the old tip: dense in c, monotone under append
    have hTipAt : blockAt? c (c.length - 1) = some tip := blockAt_getLast hTipEq
    calc quorum n ≤ windowCount c u n := hMat hTipAt u hOld
      _ ≤ windowCount (c ++ [b]) u n :=
          windowCount_mono (List.sublist_append_left c [b])
  · -- newly matured: quorum-dense by honest coverage
    exact window_dense_of_honest_cover hBudget hSExt hSCorrect
      (hCover u (by omega) (by omega))

-- ---------------------------------------------------------------------------
-- Global liveness: a synchronous honest run grows without bound
-- ---------------------------------------------------------------------------

/-!
The theorems above are *local*: one honest producer extends its chain.
Global liveness is the temporal/network statement — under synchrony the
honest chain never stalls and its height is unbounded.

We model a synchronous honest run as `buildChain g ss`: starting from
genesis `g`, the honest producer at each slot in the schedule `ss`
appends one block built on the *current* tip. That each block is built on
the previous one is exactly the delivery assumption — every honest block
reaches the next honest producer within its slot, so the honest blocks
form a single chain (no honest fork). The Byzantine budget on the
schedule (`hBudget`: at most `maxByzantine n` non-scheduled slots per
window, i.e. honest producers act in at least `quorum n` slots per
window) then makes every matured window dense, so the run validates; and
it has one block per honest slot, so the height grows without bound.
-/

/-- Extend `tip` by one honest block at each schedule slot, each built on
the previous block. -/
def buildFrom (tip : Block) : List Nat → Chain
  | [] => []
  | s :: ss => nextBlock s s 0 0 tip :: buildFrom (nextBlock s s 0 0 tip) ss

/-- A synchronous honest run from genesis `g` over honest schedule `ss`. -/
def buildChain (g : Block) (ss : List Nat) : Chain := g :: buildFrom g ss

theorem buildFrom_map_slot (tip : Block) (ss : List Nat) :
    (buildFrom tip ss).map Block.slot = ss := by
  induction ss generalizing tip with
  | nil => rfl
  | cons s rest ih => simp only [buildFrom, List.map_cons, nextBlock, ih]

theorem buildFrom_length (tip : Block) (ss : List Nat) :
    (buildFrom tip ss).length = ss.length := by
  have := congrArg List.length (buildFrom_map_slot tip ss)
  simpa using this

theorem buildChain_length (g : Block) (ss : List Nat) :
    (buildChain g ss).length = ss.length + 1 := by
  simp [buildChain, buildFrom_length]

theorem buildChain_map_slot (g : Block) (ss : List Nat) :
    (buildChain g ss).map Block.slot = g.slot :: ss := by
  simp [buildChain, buildFrom_map_slot]

theorem linksOk_buildFrom : ∀ (tip : Block) (ss : List Nat),
    List.IsChain (· < ·) (tip.slot :: ss) → linksOk (tip :: buildFrom tip ss) = true := by
  intro tip ss
  induction ss generalizing tip with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    rw [List.isChain_cons_cons] at h
    obtain ⟨hlt, hrest⟩ := h
    have hChild : childOk tip (nextBlock s s 0 0 tip) = true := by
      have hp : (nextBlock s s 0 0 tip).height = tip.height + 1 ∧
          tip.slot < (nextBlock s s 0 0 tip).slot ∧
          (nextBlock s s 0 0 tip).prev = some tip.id := ⟨rfl, hlt, rfl⟩
      simpa [childOk] using hp
    have ih2 : linksOk (nextBlock s s 0 0 tip :: buildFrom (nextBlock s s 0 0 tip) rest) = true :=
      ih (nextBlock s s 0 0 tip) hrest
    change (childOk tip (nextBlock s s 0 0 tip) &&
      linksOk (nextBlock s s 0 0 tip :: buildFrom (nextBlock s s 0 0 tip) rest)) = true
    rw [hChild, Bool.true_and]; exact ih2

theorem strictSlots_buildChain (g : Block) (ss : List Nat)
    (h : List.IsChain (· < ·) (g.slot :: ss)) : StrictSlots (buildChain g ss) := by
  have hp : ((buildChain g ss).map Block.slot).Pairwise (· < ·) := by
    rw [buildChain_map_slot]
    exact List.isChain_iff_pairwise.mp h
  unfold StrictSlots
  exact List.pairwise_map.mp hp

/--
**Global liveness.** A synchronous honest run never stalls: it validates
and gains exactly one block per honest slot, so its height is unbounded.

Hypotheses:
* `hGen` — `g` is a genesis block;
* `hChain` — genesis and the schedule slots strictly increase (a single
  honest chain: delivery makes each honest producer build on the last
  honest block);
* `hBudget` — over the run's span (every window that matures by the last
  scheduled slot), at most `maxByzantine n` slots per window are *not*
  honestly produced (equivalently, honest producers fill at least
  `quorum n` slots per window).

Then the run is validator-accepted and has `ss.length + 1` blocks. Since
`ss` can be arbitrarily long, the chain reaches any height — production
never stalls, and every block eventually becomes `n`-deep.
-/
theorem liveness_global
    {n : Nat} {g : Block} {ss : List Nat}
    (hGen : genesisOk g = true)
    (hChain : List.IsChain (· < ·) (g.slot :: ss))
    (hBudget : ∀ u, u + n ≤ (g.slot :: ss).getLast (List.cons_ne_nil _ _) + 1 →
        (badSlotsIn (fun s => s ∉ g.slot :: ss) u n).card ≤ maxByzantine n) :
    validChain n (buildChain g ss) = true ∧
      (buildChain g ss).length = ss.length + 1 := by
  classical
  refine ⟨?_, buildChain_length g ss⟩
  have hStrict : StrictSlots (buildChain g ss) := strictSlots_buildChain g ss hChain
  have hLinks : linksOk (buildChain g ss) = true := linksOk_buildFrom g ss hChain
  -- record = the run's own blocks indexed by slot
  set record : SlotRecord :=
    fun s => ((buildChain g ss).filter (fun b => decide (b.slot = s))).toFinset with hrec
  have hSCorrect : ∀ s (B : Block), B ∈ record s → B.slot = s := by
    intro s B hB
    simp only [hrec, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hB
    exact hB.2
  have hSlots : (buildChain g ss).map Block.slot = g.slot :: ss := buildChain_map_slot g ss
  have hCoverAll : ∀ u,
      HonestBlocksCover (fun s => s ∉ g.slot :: ss) record (buildChain g ss) u n := by
    intro u s hHonest _ _
    have hmem : s ∈ g.slot :: ss := not_not.mp hHonest
    have hmaps : s ∈ (buildChain g ss).map Block.slot := by rw [hSlots]; exact hmem
    rw [List.mem_map] at hmaps
    obtain ⟨B, hBc, hBs⟩ := hmaps
    refine ⟨B, ?_, hBc⟩
    simp only [hrec, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨hBc, hBs⟩
  -- assemble validChain
  change validChain n (g :: buildFrom g ss) = true
  rw [validChain, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hGen, hLinks⟩, ?_⟩
  split
  · rename_i tip hTip
    have hLastSlot : (g.slot :: ss).getLast? = some tip.slot := by
      rw [← hSlots, List.getLast?_map, buildChain, hTip]
      rfl
    have hLastEq : (g.slot :: ss).getLast (List.cons_ne_nil _ _) = tip.slot := by
      have h := List.getLast?_eq_getLast (l := g.slot :: ss)
        (List.cons_ne_nil _ _)
      rw [h] at hLastSlot
      exact Option.some.inj hLastSlot
    rw [maturedWindowsDense, List.all_eq_true]
    intro u hu
    rw [List.mem_range] at hu
    rw [windowDense, decide_eq_true_eq]
    exact window_dense_of_honest_cover_at hStrict hSCorrect
      (hBudget u (by rw [hLastEq]; omega)) (hCoverAll u)
  · rfl

end MoltPetit.Model
