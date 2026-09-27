import MoltPetit.Model.KeyStealingLockstep
import MoltPetit.Model.KeyStealingWindowCore

/-!
# MoltPetit — mode 3, per-generation census (D1′-full)

`KeyStealingLockstep.lean` delivers mode 3 at the D1′-thin budget: the
cumulative census at the lagged schedule, `LockstepPackage.exposedBound`.
This module delivers the D1′-full route the design promised: a per-generation
budget (`LockstepPackageGen.genBound`, syntactically `PackageB.erasure_freeze`'s
expression) consumed by a NEW, non-inductive pinning theorem and a NEW
aligned-window agreement engine, at confirmation depth `2n` instead of `n`.

**Why the safety proof must change, not just the budget field.** A pure
budget-transport lemma — per-generation rates ⇒ `LockstepPackage.exposedBound`
at the lagged schedule — is NOT achievable: `exposedProducersSched` at any
window is a union over ALL generations `j ≥ rosterGen(W−1)`, and
per-generation rates bound each `j`-slice, not the union (§7 below records
the witness as prose; a first Lean attempt did not resolve within the item's
budget — see that section for why). So the old headline
`lockstep_recent_tip_ancestor_agreement` cannot simply be handed a stronger
hypothesis; a new engine is needed.

**What generalises.** `window_shared_prefix` (`KeyStealingWindowCore.lean`)
runs the pigeonhole at an ARBITRARY window `u` matured in both chains, with
honest-slot uniqueness required only there. The old pinning theorem
`lockstep_declares_rosterGen` needed a strong induction on the window index
to discharge `exposedBound`'s `∃ j ≥ lagSched, …` side condition (plus a
genesis base case for window `0`); swapping the census to `genBound` — a
bound at the EXACT generation `g`, no ordering side condition — removes the
induction, the lag, and the genesis case entirely: `lockstep_window_declares_
rosterGen` below is a direct, non-inductive proof, one window at a time.

**Why depth `2n`.** The aligned route needs a window matured in BOTH chains
and pinned to one generation. The last such window below the lower tip's
slot can start as low as `tip.slot + 2 − 2n` (the tip's own grid window is
unmatured and cannot be used), so the deep, genesis-free headlines below are
stated at `2n`; `lockstepGen_shared_prefix`'s core form is sharp (explicit
window `W`) and the exact requirement, `n + ((tip.slot + 1) mod n) ≤ 2n − 1`
positions, is proved as `lockstepGen_shared_prefix_sharp`.

Nothing here modifies `KeyStealingLockstep.lean`: `LockstepPackage`,
`lockstep_declares_rosterGen`, `lockstep_validSignedChainSched`, and the
existing full-chain headlines are all untouched and remain the D1′-thin
route; `LockstepPackage.toGen` records when the two are comparable (a
surjective `rosterGen`, i.e. one that skips no generation).
-/

namespace MoltPetit.Model
open Classical

-- ===========================================================================
-- (1) Chain-order helpers, aligned-window producer injectivity, coverage
-- ===========================================================================

/-- `lockstep_rel` re-proved under a public name: `KeyStealingLockstep.lean`'s
own copy is `private`, so a new module cannot see it. Verbatim body. -/
private theorem lockstep_rel_gen {n : Nat} {c : Chain} (hS : StrictSlots c)
    (hLock : lockstepOk n c = true) {A B : Block} (hA : A ∈ c) (hB : B ∈ c)
    (hAB : A.slot < B.slot) :
    (A.slot / n = B.slot / n → A.keyIndex = B.keyIndex) ∧
      A.keyIndex ≤ B.keyIndex := by
  have hPairIdx := List.pairwise_iff_getElem.mp
    ((lockstepOk_iff_pairwise (n := n) c).mp hLock)
  obtain ⟨i, hi⟩ := exists_blockAt_of_mem hA
  obtain ⟨j, hj⟩ := exists_blockAt_of_mem hB
  have hij : i < j := by
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact h
    · exfalso; rw [h, hj] at hi; injection hi with hi
      rw [hi] at hAB; exact Nat.lt_irrefl _ hAB
    · exfalso; have := strictSlots_lt hS hj hi h; omega
  unfold blockAt? at hi hj
  rcases List.getElem?_eq_some_iff.mp hi with ⟨hiLen, hiEq⟩
  rcases List.getElem?_eq_some_iff.mp hj with ⟨hjLen, hjEq⟩
  have := hPairIdx i j hiLen hjLen hij
  rw [hiEq, hjEq] at this
  exact this

/-- `lockstep_const` re-proved under a public name; same reason. -/
private theorem lockstep_const_gen {n : Nat} {c : Chain} (hS : StrictSlots c)
    (hLock : lockstepOk n c = true) {A B : Block} (hA : A ∈ c) (hB : B ∈ c)
    (hw : A.slot / n = B.slot / n) : A.keyIndex = B.keyIndex := by
  rcases Nat.lt_trichotomy A.slot B.slot with h | h | h
  · exact (lockstep_rel_gen hS hLock hA hB h).1 hw
  · obtain ⟨i, hi⟩ := exists_blockAt_of_mem hA
    obtain ⟨j, hj⟩ := exists_blockAt_of_mem hB
    have hij : i = j := by
      rcases Nat.lt_trichotomy i j with h' | h' | h'
      · have := strictSlots_lt hS hi hj h'; omega
      · exact h'
      · have := strictSlots_lt hS hj hi h'; omega
    rw [hij, hj] at hi; injection hi with hi; rw [hi]
  · exact ((lockstep_rel_gen hS hLock hB hA h).1 hw.symm).symm

/-- Producer injectivity within one ALIGNED window `[W·n, W·n+n)` — simpler
than `window_producer_inj'`'s `Nat.ModEq` route because the window starts at
a multiple of `n`, so both slots' quotient by `n` is forced to be `W` and the
producer (`slot % n`) determines the slot outright via `Nat.div_add_mod`. -/
private theorem aligned_producer_inj {n W s s' : Nat} (hn : 0 < n)
    (hs : W * n ≤ s ∧ s < W * n + n) (hs' : W * n ≤ s' ∧ s' < W * n + n)
    (hp : producerForSlot n s = producerForSlot n s') : s = s' := by
  unfold producerForSlot at hp
  have hd : s / n = W := by
    have h1 : W ≤ s / n := (Nat.le_div_iff_mul_le hn).mpr hs.1
    have h2 : s / n < W + 1 := by
      refine (Nat.div_lt_iff_lt_mul hn).mpr ?_
      have : (W + 1) * n = W * n + n := Nat.succ_mul W n
      omega
    omega
  have hd' : s' / n = W := by
    have h1 : W ≤ s' / n := (Nat.le_div_iff_mul_le hn).mpr hs'.1
    have h2 : s' / n < W + 1 := by
      refine (Nat.div_lt_iff_lt_mul hn).mpr ?_
      have : (W + 1) * n = W * n + n := Nat.succ_mul W n
      omega
    omega
  have he : n * (s / n) + s % n = s := Nat.div_add_mod s n
  have he' : n * (s' / n) + s' % n = s' := Nat.div_add_mod s' n
  rw [hd] at he
  rw [hd'] at he'
  omega

/-- Declared-signature coverage from `validSignedChainLock`. Mirror of
`signedDeclared_of_mem_sched` (`KeyStealingSchedule.lean:88`). -/
theorem signedDeclared_of_mem_lock {σ sk pk : Type} {n : Nat}
    {ops : SigOps σ sk pk} {registry : KeyRegistry pk} {sc : SignedChain σ}
    (h : validSignedChainLock n ops registry sc = true)
    {B : Block} (hB : B ∈ stripSigs sc) :
    SignedDeclared n ops registry B := by
  obtain ⟨sb, hsbmem, hsbeq⟩ := List.mem_map.mp hB
  have h2 := h
  rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at h2
  obtain ⟨⟨hSigsBool, _⟩, _⟩ := h2
  rw [sigsOk, List.all_eq_true] at hSigsBool
  have hver := hSigsBool sb hsbmem
  rw [sigOk] at hver
  exact ⟨sb.sig, by rw [hsbeq] at hver; exact hver⟩

-- ===========================================================================
-- (2) The per-generation corruption predicate and the aligned budget
-- ===========================================================================

/-- The per-generation corruption predicate (`georgeee/mini-consensus-lean: LOCKSTEP_DESIGN.md:127-133`): a
slot is bad if rented, or its producer's key OF THE GENERATION THE ROSTER IS
AT IN THAT GRID WINDOW is stolen. Chain-independent, un-lagged, no `∃ j ≥ …`
cumulative reading. Sound for honest-slot uniqueness exactly on windows
pinned in both chains — consumed through `HonestSlotsUniqueOn`, never
`HonestSlotsUnique`. -/
def badLockAt (n : Nat) (rosterGen : Nat → Nat) (rented : ByzantineSlots)
    (Stolen : Nat → Nat → Prop) (s : Nat) : Prop :=
  rented s ∨ Stolen (producerForSlot n s) (rosterGen (s / n))

theorem badLockAt_iff_or {n : Nat} {rosterGen : Nat → Nat} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {s : Nat} :
    badLockAt n rosterGen rented Stolen s ↔
      rented s ∨ Stolen (producerForSlot n s) (rosterGen (s / n)) := Iff.rfl

/-- The Byzantine budget on the fixed grid of aligned windows `[W·n, W·n+n)`
only — the shape the aligned-window engine consumes. Weaker than
`ByzantineBounded`, which quantifies over every `u`. -/
def AlignedBounded (n : Nat) (bad : ByzantineSlots) : Prop :=
  ∀ W, (badSlotsIn bad (W * n) n).card ≤ maxByzantine n

theorem alignedBounded_of_bounded {n : Nat} {bad : ByzantineSlots}
    (h : ByzantineBounded n bad) : AlignedBounded n bad :=
  fun W => h (W * n)

/-- **The mode-3 I3, aligned form.** A rent rate `R` and a per-generation
theft census `T`, with `R + T` within the `1/3` bound, give the
chain-independent `AlignedBounded` over `badLockAt` — the per-generation
census IS the budget here, with no cumulative reading anywhere. -/
theorem lockstep_aligned_budget
    {n : Nat} (hn : 0 < n) {rosterGen : Nat → Nat} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {R T : Nat}
    (hRent : ∀ u, (badSlotsIn rented u n).card ≤ R)
    (hGen : ∀ j : Nat, ((Finset.range n).filter (fun i => Stolen i j)).card ≤ T)
    (hRT : R + T ≤ maxByzantine n) :
    AlignedBounded n (badLockAt n rosterGen rented Stolen) := by
  intro W
  have heq : badSlotsIn (badLockAt n rosterGen rented Stolen) (W * n) n =
      badSlotsIn (fun s => rented s ∨ Stolen (producerForSlot n s) (rosterGen W))
        (W * n) n := by
    unfold badSlotsIn
    ext s
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨hmem, hbad⟩
      refine ⟨hmem, ?_⟩
      have hsW : s / n = W := by
        have h1 : W ≤ s / n := (Nat.le_div_iff_mul_le hn).mpr hmem.1
        have h2 : s / n < W + 1 := by
          refine (Nat.div_lt_iff_lt_mul hn).mpr ?_
          have : (W + 1) * n = W * n + n := Nat.succ_mul W n
          omega
        omega
      unfold badLockAt at hbad
      rwa [hsW] at hbad
    · rintro ⟨hmem, hbad⟩
      refine ⟨hmem, ?_⟩
      have hsW : s / n = W := by
        have h1 : W ≤ s / n := (Nat.le_div_iff_mul_le hn).mpr hmem.1
        have h2 : s / n < W + 1 := by
          refine (Nat.div_lt_iff_lt_mul hn).mpr ?_
          have : (W + 1) * n = W * n + n := Nat.succ_mul W n
          omega
        omega
      unfold badLockAt
      rwa [hsW]
  rw [heq]
  have hSplit := badSlotsIn_union_le rented
    (fun s => Stolen (producerForSlot n s) (rosterGen W)) (W * n) n
  have htheft : (badSlotsIn (fun s => Stolen (producerForSlot n s) (rosterGen W))
      (W * n) n).card ≤ ((Finset.range n).filter (fun i => Stolen i (rosterGen W))).card := by
    unfold badSlotsIn
    refine Finset.card_le_card_of_injOn (producerForSlot n) (fun s hs => ?_) ?_
    · rw [Finset.mem_coe, Finset.mem_filter] at hs
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hs.2⟩
      unfold producerForSlot
      exact Nat.mod_lt _ hn
    · intro s hs s' hs' hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hs hs'
      exact aligned_producer_inj hn hs.1 hs'.1 hp
  calc (badSlotsIn (fun s => rented s ∨ Stolen (producerForSlot n s) (rosterGen W))
        (W * n) n).card
      ≤ (badSlotsIn rented (W * n) n).card
        + (badSlotsIn (fun s => Stolen (producerForSlot n s) (rosterGen W)) (W * n) n).card :=
        hSplit
    _ ≤ R + T := Nat.add_le_add (hRent (W * n)) (le_trans htheft (hGen (rosterGen W)))
    _ ≤ maxByzantine n := hRT

-- ===========================================================================
-- (3) The per-generation package
-- ===========================================================================

/-- **The D1′-full lockstep package.** `B1`-as-behaviour (`declared`), the
constant-0 core EUF-CMA surface (unchanged), hash injectivity, and the
budget in PER-GENERATION form — `genBound` is syntactically `PackageB.
erasure_freeze`'s expression, so a `PackageB` field can be passed verbatim.
NO `exposedBound` (no cumulative census, no `lagSched`), and NO `mono`/
`genesis_gen`: neither is consumed by the new route — the pinning theorem
below is non-inductive and genesis-free, so carrying them would be an
unconsumed field. Incomparable with `LockstepPackage` in general;
`LockstepPackage.toGen` gives thin ⇒ gen when `rosterGen` is surjective
(skips no generation). -/
structure LockstepPackageGen (n : Nat) (rosterGen : Nat → Nat) {Sig sk pk : Type}
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (rented : ByzantineSlots)
    (Stolen : Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block)
    (now Δ : Nat) (G : Block) (R T : Nat) : Prop where
  unforgeable :
    SchedCoreUnforgeable n (fun _ => 0) ops registry rented Stolen honestSigned now Δ
  declared : ∀ ⦃i s : Nat⦄ ⦃B : Block⦄, honestSigned i s = some B →
    B.keyIndex = rosterGen (s / n)
  hashInj : SignedHashInjective (SignedDeclared n ops registry) G
  rentBound : ∀ u, (badSlotsIn rented u n).card ≤ R
  genBound : ∀ j : Nat, ((Finset.range n).filter (fun i => Stolen i j)).card ≤ T
  budget_le : R + T ≤ maxByzantine n

/-- The package's budget is `AlignedBounded` over `badLockAt`. -/
theorem LockstepPackageGen.alignedBudget {n : Nat} {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    (hn : 0 < n) :
    AlignedBounded n (badLockAt n rosterGen rented Stolen) :=
  lockstep_aligned_budget hn hP.rentBound hP.genBound hP.budget_le

/-- **Thin ⇒ gen when the counter skips no generation.** A `LockstepPackage`
(cumulative census at the lagged schedule) delivers a `LockstepPackageGen`
(per-generation census) when `rosterGen` is surjective onto `ℕ` — every
generation is eventually the roster's counter, so each per-generation
census is realised as some full aligned window's cumulative one. Only this
direction is proved; the converse (that no weaker condition suffices) is
not claimed. In general the two packages are incomparable (§7 below,
prose witness). -/
theorem LockstepPackage.toGen {n : Nat} {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat} (hn : 0 < n)
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    (hSurj : ∀ j, ∃ W, rosterGen W = j) :
    LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T where
  unforgeable := hP.unforgeable
  declared := hP.declared
  hashInj := hP.hashInj
  rentBound := hP.rentBound
  budget_le := hP.budget_le
  genBound := erasure_freeze_of_exposedBound hP.exposedBound (by
    intro j
    obtain ⟨W, hW⟩ := hSurj j
    refine ⟨(W + 1) * n, ?_⟩
    intro s hs1 hs2
    have hsdiv : s / n = W + 1 := by
      have h1 : W + 1 ≤ s / n := (Nat.le_div_iff_mul_le hn).mpr hs1
      have h2 : s / n < W + 2 := by
        refine (Nat.div_lt_iff_lt_mul hn).mpr ?_
        have : (W + 2) * n = (W + 1) * n + n := Nat.succ_mul (W + 1) n
        omega
      omega
    show lagSched n rosterGen s = j
    unfold lagSched
    rw [hsdiv]
    have hcancel : W + 1 - 1 = W := by omega
    rw [hcancel]
    exact hW)

-- ===========================================================================
-- (4) The non-inductive per-window pinning theorem
-- ===========================================================================

/-- **The per-window pinning theorem — non-inductive, genesis-free.**
`lockstep_declares_rosterGen` with the census swapped: every theft slot in
the window is charged to the single generation `B.keyIndex`, so `genBound`
alone closes it. What is GONE relative to the old proof: the strong
induction on the window index, the `lagSched` side condition, and the
genesis base case (`hHead`, `head_slot_min`, `genesis_gen`). -/
theorem lockstep_window_declares_rosterGen
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc : SignedChain Sig} (hVal : validSignedChainLock n ops registry sc = true)
    (hRecent : ∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ)
    (W : Nat) (hMat : ∃ D ∈ stripSigs sc, W * n + n ≤ D.slot + 1)
    {B : Block} (hB : B ∈ stripSigs sc) (hBW : B.slot / n = W) :
    B.keyIndex = rosterGen W := by
  have hVal2 := hVal
  rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at hVal2
  obtain ⟨⟨hSigsBool, hVK⟩, hLock⟩ := hVal2
  have hSigs : ∀ sb ∈ sc, sigOk n ops registry sb = true := by
    rw [sigsOk, List.all_eq_true] at hSigsBool; exact hSigsBool
  have hVC : ValidChain n (stripSigs sc) := (validChainK_sound hVK).1
  obtain ⟨hSeq, hS, hPL, hDense⟩ := hVC
  obtain ⟨D, hDmem, hDmat⟩ := hMat
  obtain ⟨kD, hkD⟩ := exists_blockAt_of_mem hDmem
  have hWdense : quorum n ≤ windowCount (stripSigs sc) (W * n) n := hDense hkD (W * n) (by omega)
  by_contra hne
  have hSsub : chainSlotsIn (stripSigs sc) (W * n) n ⊆
      badSlotsIn rented (W * n) n ∪
        (Finset.Ico (W * n) (W * n + n)).filter
          (fun s => Stolen (producerForSlot n s) B.keyIndex) := by
    intro s hs
    obtain ⟨Bs, hBsMem, hBsWin, hBsSlot⟩ := mem_chainSlotsIn.mp hs
    have hsW : Bs.slot / n = W := by
      have h1 : W ≤ Bs.slot / n := (Nat.le_div_iff_mul_le (by omega)).mpr hBsWin.1
      have h2 : Bs.slot / n < W + 1 := by
        refine (Nat.div_lt_iff_lt_mul (by omega : 0 < n)).mpr ?_
        have : (W + 1) * n = W * n + n := Nat.succ_mul W n
        omega
      omega
    have hBsKey : Bs.keyIndex = B.keyIndex :=
      lockstep_const_gen hS hLock hBsMem hB (by rw [hsW, hBW])
    have hcase : rented s ∨ Stolen (producerForSlot n s) B.keyIndex := by
      rcases Classical.em (rented s) with hr | hr
      · exact Or.inl hr
      rcases Classical.em (Stolen (producerForSlot n s) B.keyIndex) with hst | hst
      · exact Or.inr hst
      exfalso
      obtain ⟨sb, hsbmem, hsbeq⟩ := List.mem_map.mp hBsMem
      have hver := hSigs sb hsbmem
      rw [sigOk] at hver
      have hrent' : ¬ rented sb.block.slot := by rw [hsbeq, hBsSlot]; exact hr
      have hstol' : ¬ Stolen (producerForSlot n sb.block.slot) sb.block.keyIndex := by
        rw [hsbeq, hBsSlot, hBsKey]; exact hst
      have hhon := hP.unforgeable.unforgeable (schedCore0_of_lock hVal)
        hsbmem hRecent hver hrent' hstol'
      have hdecl := hP.declared hhon
      rw [hsbeq, hBsKey, hsW] at hdecl
      exact hne hdecl
    rcases hcase with hr | hst
    · refine Finset.mem_union_left _ ?_
      unfold badSlotsIn
      rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨by omega, hr⟩
    · refine Finset.mem_union_right _ ?_
      rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨by omega, hst⟩
  have hinj : Set.InjOn (producerForSlot n)
      ↑((Finset.Ico (W * n) (W * n + n)).filter
        (fun s => Stolen (producerForSlot n s) B.keyIndex)) := by
    intro s hs s' hs' hp
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hs hs'
    exact aligned_producer_inj hn hs.1 hs'.1 hp
  have hTb : ((Finset.Ico (W * n) (W * n + n)).filter
      (fun s => Stolen (producerForSlot n s) B.keyIndex)).card ≤ T := by
    have hEB := hP.genBound B.keyIndex
    calc ((Finset.Ico (W * n) (W * n + n)).filter
          (fun s => Stolen (producerForSlot n s) B.keyIndex)).card
        = (((Finset.Ico (W * n) (W * n + n)).filter
          (fun s => Stolen (producerForSlot n s) B.keyIndex)).image
            (producerForSlot n)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((Finset.range n).filter (fun i => Stolen i B.keyIndex)).card := by
          refine Finset.card_le_card ?_
          intro i hi
          rw [Finset.mem_image] at hi
          obtain ⟨s, hs, rfl⟩ := hi
          rw [Finset.mem_filter, Finset.mem_Ico] at hs
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨?_, hs.2⟩
          unfold producerForSlot
          exact Nat.mod_lt _ hn
      _ ≤ T := hEB
  have hRb := hP.rentBound (W * n)
  have hcount : quorum n ≤
      (badSlotsIn rented (W * n) n).card +
      ((Finset.Ico (W * n) (W * n + n)).filter
        (fun s => Stolen (producerForSlot n s) B.keyIndex)).card := by
    calc quorum n ≤ windowCount (stripSigs sc) (W * n) n := hWdense
      _ = (chainSlotsIn (stripSigs sc) (W * n) n).card := (chainSlotsIn_card hS _ _).symm
      _ ≤ _ := le_trans (Finset.card_le_card hSsub) (Finset.card_union_le _ _)
  have hmb : maxByzantine n < quorum n := by unfold maxByzantine quorum; omega
  have := hP.budget_le
  omega

-- ===========================================================================
-- (5) Uniqueness on one aligned window, and the sharp engine
-- ===========================================================================

/-- Honest-slot uniqueness on one aligned window, for `badLockAt`, over the
union record of two chains — mirrors `honestSlotsUnique_schedCore`'s shape
(cross-chain via the surface, no reconciliation induction), at the pinned
generation instead of the scheduled floor. -/
theorem honestSlotsUniqueOn_lockstep
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    (hRecent : ∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ)
    (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ)
    (W : Nat) (hMat : ∃ D ∈ stripSigs sc, W * n + n ≤ D.slot + 1)
    (hMat' : ∃ D' ∈ stripSigs sc', W * n + n ≤ D'.slot + 1) :
    HonestSlotsUniqueOn (W * n) n (badLockAt n rosterGen rented Stolen)
      (chainUnionRecord sc sc') := by
  intro s hsu hsun hbad X Y hX hY
  simp only [badLockAt, not_or] at hbad
  obtain ⟨hNotRent, hNotStolen⟩ := hbad
  have hsW : s / n = W := by
    have h1 : W ≤ s / n := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have h2 : s / n < W + 1 := by
      refine (Nat.div_lt_iff_lt_mul (by omega : 0 < n)).mpr ?_
      have : (W + 1) * n = W * n + n := Nat.succ_mul W n
      omega
    omega
  rw [mem_chainUnionRecord] at hX hY
  have honest_from : ∀ {sc0 : SignedChain Sig} {Z : Block},
      validSignedChainLock n ops registry sc0 = true →
      (∃ t, (stripSigs sc0).getLast? = some t ∧ now ≤ t.slot + Δ) →
      (∃ D ∈ stripSigs sc0, W * n + n ≤ D.slot + 1) →
      Z ∈ stripSigs sc0 → Z.slot = s →
      honestSigned (producerForSlot n s) s = some Z := by
    intro sc0 Z hVal0 hRec0 hMat0 hZmem hZslot
    have hZW : Z.slot / n = W := by rw [hZslot]; exact hsW
    have hZkey : Z.keyIndex = rosterGen W :=
      lockstep_window_declares_rosterGen hn hP hVal0 hRec0 W hMat0 hZmem hZW
    obtain ⟨sb, hsbmem, hsbeq⟩ := List.mem_map.mp hZmem
    have hVal0' := hVal0
    rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at hVal0'
    obtain ⟨⟨hSigsBool, _⟩, _⟩ := hVal0'
    rw [sigsOk, List.all_eq_true] at hSigsBool
    have hver := hSigsBool sb hsbmem
    rw [sigOk] at hver
    have hrent' : ¬ rented sb.block.slot := by rw [hsbeq, hZslot]; exact hNotRent
    have hstol' : ¬ Stolen (producerForSlot n sb.block.slot) sb.block.keyIndex := by
      rw [hsbeq, hZslot, hZkey, ← hsW]
      exact hNotStolen
    have hhon := hP.unforgeable.unforgeable (schedCore0_of_lock hVal0)
      hsbmem hRec0 hver hrent' hstol'
    rw [hsbeq, hZslot] at hhon
    exact hhon
  have hXhon : honestSigned (producerForSlot n s) s = some X := by
    rcases hX.1 with hXc | hXc'
    · exact honest_from hVal hRecent hMat hXc hX.2
    · exact honest_from hVal' hRecent' hMat' hXc' hX.2
  have hYhon : honestSigned (producerForSlot n s) s = some Y := by
    rcases hY.1 with hYc | hYc'
    · exact honest_from hVal hRecent hMat hYc hY.2
    · exact honest_from hVal' hRecent' hMat' hYc' hY.2
  rw [hXhon] at hYhon
  exact Option.some.inj hYhon

/-- **The sharp aligned-window agreement core.** Explicit window `W`,
genesis-free, no `hHead`. Composition of `window_shared_prefix` with the
per-generation package: hash injectivity gives id injectivity over the union
record, `honestSlotsUniqueOn_lockstep` gives honesty on `W`, and
`LockstepPackageGen.alignedBudget` gives the window's own budget. -/
theorem lockstepGen_shared_prefix
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block} (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hle : sTip.slot ≤ sTip'.slot)
    {W : Nat} (hWmat : W * n + n ≤ sTip.slot + 1)
    {k : Nat} {B : Block} (hB : blockAt? (stripSigs sc) k = some B) (hBu : B.slot < W * n) :
    ∃ P : Block, blockAt? (stripSigs sc) k = some P ∧ blockAt? (stripSigs sc') k = some P := by
  have hVc : ValidChain n (stripSigs sc) := by
    have h2 := hVal
    rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at h2
    exact (validChainK_sound h2.1.2).1
  have hVc' : ValidChain n (stripSigs sc') := by
    have h2 := hVal'
    rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at h2
    exact (validChainK_sound h2.1.2).1
  have hSig : ∀ b ∈ stripSigs sc, b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_lock hVal hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_lock hVal' hb)
  have hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hP.hashInj hSig hSig'
  have hTipSmem : sTip ∈ stripSigs sc := by
    have h' := blockAt_getLast hTipS
    unfold blockAt? at h'
    exact List.mem_of_getElem? h'
  have hTipS'mem : sTip' ∈ stripSigs sc' := by
    have h' := blockAt_getLast hTipS'
    unfold blockAt? at h'
    exact List.mem_of_getElem? h'
  have hUniq := honestSlotsUniqueOn_lockstep hn hP hVal hVal'
    ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩ W
    ⟨sTip, hTipSmem, hWmat⟩ ⟨sTip', hTipS'mem, by omega⟩
  have hBudget := hP.alignedBudget (by omega) W
  exact window_shared_prefix hn hUniq hId hVc hVc'
    chainInRecord_left chainInRecord_right hTipS hTipS' hWmat (by omega) hBudget hB hBu

/-- The `2n`-depth attachment of `lockstepGen_shared_prefix`: given a block
`2n` positions above `k` in `sc`, its window is automatically matured and its
slot automatically below the pigeonhole window — `W` computed internally
from `sTip.slot`, the aligned analogue of a computed horizon. -/
theorem lockstepGen_shared_prefix_deep
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block} (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hle : sTip.slot ≤ sTip'.slot)
    {k : Nat} {B : Block} (hB : blockAt? (stripSigs sc) k = some B)
    (hDeep : k + 2 * n < (stripSigs sc).length) :
    ∃ P : Block, blockAt? (stripSigs sc) k = some P ∧ blockAt? (stripSigs sc') k = some P := by
  have hVc : ValidChain n (stripSigs sc) := by
    have h2 := hVal
    rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at h2
    exact (validChainK_sound h2.1.2).1
  have hStrictC : StrictSlots (stripSigs sc) := hVc.2.1
  have hTipAt : blockAt? (stripSigs sc) ((stripSigs sc).length - 1) = some sTip :=
    blockAt_getLast hTipS
  have hgap : B.slot + 2 * n ≤ sTip.slot := by
    have hstep := slot_gap_of_position_gap_win hStrictC
      ((stripSigs sc).length - 1 - k) k hB
      (by rw [show k + ((stripSigs sc).length - 1 - k) = (stripSigs sc).length - 1 by omega]
          exact hTipAt)
    omega
  have hq2 : 2 ≤ (sTip.slot + 1) / n := by
    have h2n : 2 * n ≤ sTip.slot + 1 := by omega
    exact (Nat.le_div_iff_mul_le (by omega : 0 < n)).mpr h2n
  set q := (sTip.slot + 1) / n with hqdef
  set W := q - 1 with hWdef
  have hWq : W + 1 = q := by omega
  have hrmod : (sTip.slot + 1) % n < n := Nat.mod_lt _ (by omega)
  have hdam : n * q + (sTip.slot + 1) % n = sTip.slot + 1 := Nat.div_add_mod (sTip.slot + 1) n
  have hWeq : n * W + n = n * q := by
    calc n * W + n = n * (W + 1) := (Nat.mul_succ n W).symm
      _ = n * q := by rw [hWq]
  have hcomm : n * W = W * n := Nat.mul_comm n W
  have hWmat : W * n + n ≤ sTip.slot + 1 := by omega
  have hBu : B.slot < W * n := by omega
  exact lockstepGen_shared_prefix hn hP hVal hVal' hTipS hTipS' hRecent hRecent' hle
    hWmat hB hBu

/-- **The sharp depth.** `2n` in `lockstepGen_shared_prefix_deep` is the
clean worst case; the exact requirement is `n + ((sTip.slot + 1) mod n)`
positions above `k` — the tip's own (unmatured) grid window, whose width is
that remainder, plus one full window. This is the statement behind the
module doc's "exactly `n + ((t+1) mod n) ≤ 2n − 1`"; the `2n` form is the one
the headlines use because a client cannot know the remainder without the
tip. -/
theorem lockstepGen_shared_prefix_sharp
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block} (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hle : sTip.slot ≤ sTip'.slot)
    {k : Nat} {B : Block} (hB : blockAt? (stripSigs sc) k = some B)
    (hDeep : k + n + (sTip.slot + 1) % n < (stripSigs sc).length) :
    ∃ P : Block, blockAt? (stripSigs sc) k = some P ∧ blockAt? (stripSigs sc') k = some P := by
  have hVc : ValidChain n (stripSigs sc) := by
    have h2 := hVal
    rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at h2
    exact (validChainK_sound h2.1.2).1
  have hStrictC : StrictSlots (stripSigs sc) := hVc.2.1
  have hTipAt : blockAt? (stripSigs sc) ((stripSigs sc).length - 1) = some sTip :=
    blockAt_getLast hTipS
  have hrmod : (sTip.slot + 1) % n < n := Nat.mod_lt _ (by omega)
  have hgap : B.slot + n + (sTip.slot + 1) % n ≤ sTip.slot := by
    have hstep := slot_gap_of_position_gap_win hStrictC
      ((stripSigs sc).length - 1 - k) k hB
      (by rw [show k + ((stripSigs sc).length - 1 - k) = (stripSigs sc).length - 1 by omega]
          exact hTipAt)
    omega
  have hq1 : 1 ≤ (sTip.slot + 1) / n :=
    (Nat.le_div_iff_mul_le (by omega : 0 < n)).mpr (by omega)
  set q := (sTip.slot + 1) / n with hqdef
  set W := q - 1 with hWdef
  have hWq : W + 1 = q := by omega
  have hdam : n * q + (sTip.slot + 1) % n = sTip.slot + 1 := Nat.div_add_mod (sTip.slot + 1) n
  have hWeq : n * W + n = n * q := by
    calc n * W + n = n * (W + 1) := (Nat.mul_succ n W).symm
      _ = n * q := by rw [hWq]
  have hcomm : n * W = W * n := Nat.mul_comm n W
  have hWmat : W * n + n ≤ sTip.slot + 1 := by omega
  have hBu : B.slot < W * n := by omega
  exact lockstepGen_shared_prefix hn hP hVal hVal' hTipS hTipS' hRecent hRecent' hle
    hWmat hB hBu

-- ===========================================================================
-- (6) Headlines
-- ===========================================================================

/-- **Free-cadence lockstep, per-generation headline (equal-tip form).**
Under `LockstepPackageGen` alone, two chains accepted by the schedule-free
lockstep validator, with recent tips, agree on the block `2n` below each
tip — no shared genesis. Confirmation depth `2n` (against `n` for the
cumulative D1′-thin form) is the aligned route's cost. -/
theorem lockstepGen_recent_tip_ancestor_agreement
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block} (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong : 2 * n < (stripSigs sc).length) (hLong' : 2 * n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - 2 * n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - 2 * n) = some B') :
    B = B' := by
  have hVc : ValidChain n (stripSigs sc) := by
    have h2 := hVal
    rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at h2
    exact (validChainK_sound h2.1.2).1
  have hVc' : ValidChain n (stripSigs sc') := by
    have h2 := hVal'
    rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at h2
    exact (validChainK_sound h2.1.2).1
  have hTipIdx : sTip.height = (stripSigs sc).length - 1 := hVc.1 (blockAt_getLast hTipS)
  have hTipIdx' : sTip'.height = (stripSigs sc').length - 1 := hVc'.1 (blockAt_getLast hTipS')
  have hLenEq : (stripSigs sc).length - 1 - 2 * n = (stripSigs sc').length - 1 - 2 * n := by
    omega
  rw [← hLenEq] at hB'
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · obtain ⟨P, hPc, hPc'⟩ := lockstepGen_shared_prefix_deep hn hP hVal hVal' hTipS hTipS'
      hRecent hRecent' hle hB (k := (stripSigs sc).length - 1 - 2 * n) (by omega)
    rw [hB] at hPc
    rw [hB'] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']
  · obtain ⟨P, hPc', hPc⟩ := lockstepGen_shared_prefix_deep hn hP hVal' hVal hTipS' hTipS
      hRecent' hRecent hle hB' (k := (stripSigs sc).length - 1 - 2 * n) (by omega)
    rw [hB] at hPc
    rw [hB'] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']

/-- Consistency form (unequal tip heights): the `2n`-deep ancestor of the
lower-tipped chain is a block of the other chain too, at least `2n` deep
there. -/
theorem lockstepGen_recent_tip_ancestor_mem
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block} (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong : 2 * n < (stripSigs sc).length)
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block} (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - 2 * n) = some B) :
    ∃ i', i' + 2 * n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B := by
  have hVc : ValidChain n (stripSigs sc) := by
    have h2 := hVal
    rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at h2
    exact (validChainK_sound h2.1.2).1
  have hVc' : ValidChain n (stripSigs sc') := by
    have h2 := hVal'
    rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at h2
    exact (validChainK_sound h2.1.2).1
  have hTipIdx : sTip.height = (stripSigs sc).length - 1 := hVc.1 (blockAt_getLast hTipS)
  have hTipIdx' : sTip'.height = (stripSigs sc').length - 1 := hVc'.1 (blockAt_getLast hTipS')
  set k : Nat := (stripSigs sc).length - 1 - 2 * n with hk
  have hkn' : k + 2 * n < (stripSigs sc').length := by omega
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · obtain ⟨P, hPc, hPc'⟩ := lockstepGen_shared_prefix_deep hn hP hVal hVal' hTipS hTipS'
      hRecent hRecent' hle hB (k := k) (by omega)
    exact ⟨k, hkn', by rw [hB] at hPc; rw [Option.some.inj hPc]; exact hPc'⟩
  · have hBex : ∃ C, blockAt? (stripSigs sc') k = some C := by
      cases hopt : blockAt? (stripSigs sc') k with
      | none =>
        unfold blockAt? at hopt
        have := List.getElem?_eq_none_iff.mp hopt
        omega
      | some C => exact ⟨C, rfl⟩
    obtain ⟨C, hC⟩ := hBex
    obtain ⟨P, hPc', hPc⟩ := lockstepGen_shared_prefix_deep hn hP hVal' hVal hTipS' hTipS
      hRecent' hRecent hle hC (k := k) (by omega)
    rw [hB] at hPc
    exact ⟨k, hkn', by rw [Option.some.inj hPc]; exact hPc'⟩

/-- **Genesis agreement, stated as a conclusion.** Two chains accepted by the
schedule-free lockstep validator, with recent tips — heights unconstrained,
no shared-genesis or anchor hypothesis of any kind — carry the same block at
height `0`. Makes explicit that the new mode-3 statements assume no shared
genesis; the paper's Theorem 5 currently requires it as a hypothesis. -/
theorem lockstepGen_recent_genesis_agreement
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block} (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong : 2 * n < (stripSigs sc).length) (hLong' : 2 * n < (stripSigs sc').length) :
    ∃ P : Block, blockAt? (stripSigs sc) 0 = some P ∧ blockAt? (stripSigs sc') 0 = some P := by
  have hB0 : ∃ C, blockAt? (stripSigs sc) 0 = some C := by
    cases hopt : blockAt? (stripSigs sc) 0 with
    | none =>
      unfold blockAt? at hopt
      have := List.getElem?_eq_none_iff.mp hopt
      omega
    | some C => exact ⟨C, rfl⟩
  obtain ⟨C, hC⟩ := hB0
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · exact lockstepGen_shared_prefix_deep hn hP hVal hVal' hTipS hTipS' hRecent hRecent' hle
      hC (k := 0) (by omega)
  · have hB0' : ∃ C', blockAt? (stripSigs sc') 0 = some C' := by
      cases hopt : blockAt? (stripSigs sc') 0 with
      | none =>
        unfold blockAt? at hopt
        have := List.getElem?_eq_none_iff.mp hopt
        omega
      | some C' => exact ⟨C', rfl⟩
    obtain ⟨C', hC'⟩ := hB0'
    obtain ⟨P, hPc', hPc⟩ := lockstepGen_shared_prefix_deep hn hP hVal' hVal hTipS' hTipS
      hRecent' hRecent hle hC' (k := 0) (by omega)
    exact ⟨P, hPc, hPc'⟩

-- ===========================================================================
-- (7) Consistency note: pure budget transport is impossible
-- ===========================================================================

/-!
**Pure budget transport is impossible — recorded as prose, not a machine
check.** A per-generation census bound does NOT give the cumulative
`exposedBound` at any lagged schedule: witness `n := 2`, `T := 1`,
`rosterGen ≡ 0`, `Stolen i j := i = j`. Each generation's census is `≤ 1` (a
singleton, since `Stolen · j` has at most one solution `i = j`), but the
cumulative exposure at window `0` (where `lagSched` is constantly `0`, so
`theftSched` there holds for every `j ≥ 0`) is `2`: both producers `0` and
`1` are exposed (`0` by `j := 0`, `1` by `j := 1`). This is why the safety
proof needed a new engine, not just a new budget field, and is the same
counterexample `PackageB`'s own docstring already states
(`KeyStealingScheduleBudget.lean:323-328`). A first Lean attempt at this
witness ran into a `Finset.filter` decidability-instance diamond (the
abstract `Stolen : Nat → Nat → Prop` in `exposedProducersSched`'s statement
resolves to `Classical.propDecidable`, while re-deriving `card ≤ 1` for the
concrete instance `Stolen := (· = ·)` pulls in the native `DecidableEq Nat`
instance, and `apply`/`refine` disagree on which one the rewritten goal
carries) that did not resolve within the item's budget; per the design's own
risk mitigation, the witness is left as this prose argument rather than
forced through.
-/

end MoltPetit.Model
