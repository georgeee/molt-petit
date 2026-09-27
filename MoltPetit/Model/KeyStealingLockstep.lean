import MoltPetit.Model.KeyStealingScheduleBudget
import MoltPetit.Results.KeyStealingScheduleResults

/-!
# MoltPetit — free-cadence lockstep rotation (mode 3, D1′-thin)

Mode 3 as designed: the roster advances the roster-wide generation **at a
freely chosen moment** — not by slot arithmetic — and after the decision,
coordination is lockstep: no mixing of generations. The scheduled device
(`PackageA`/`PackageB`) does *not* capture this: there advancement is forced
by position, `gen(s) ≤ keyIndex` for a protocol-constant `gen`.

This module captures it, by reduction rather than re-proof (`georgeee/mini-consensus-lean: LOCKSTEP_DESIGN.md`
D1′-thin). Three ingredients:

* **The lockstep validator** `validSignedChainLock`: signatures + structure +
  the in-band monotone rule, plus the **no-mixing rule** `lockstepOk` — the
  declared generation is constant within each `n`-slot window and
  non-decreasing across windows. It takes **no schedule input**: the verifier
  never learns when the roster advanced, and the client still holds only
  genesis and a clock.
* **Lockstep as behaviour, not as a rule** (B1): an execution-level
  `rosterGen : Nat → Nat` — per *window*, monotone, **discovered rather than
  fixed** — such that every honest signature declares its window's
  `rosterGen` (the package field `declared`), and genesis declares its own
  window's (`genesis_gen`).
* **The pinning theorem** `lockstep_declares_rosterGen`: on any accepted
  recent lockstep chain, every block in a *matured* window declares exactly
  `rosterGen` of its window. The census that closes it: a matured window is
  quorum-dense with pairwise-distinct producers, all at one generation `g` by
  no-mixing; if `g ≠ rosterGen(W)` then (by the EUF-CMA surface + `declared`)
  none of those blocks is honest, so each sits at a rented slot or at a
  producer whose generation-`g` key is stolen — at most `R + T ≤ ⌊(n-1)/3⌋ <
  quorum` slots. Contradiction. This machine-checks the design narrative
  "no-mixing pins any fork to one generation".

The payoff is the **lagged-schedule transport**: pinning makes every accepted
lockstep chain pass the *scheduled* validator at
`lagSched n rosterGen = fun s => rosterGen (s/n − 1)` — the lag absorbs the one
unmatured tip window, where only monotonicity from the previous (always
matured) window is available. `LockstepPackage.toPackageA` then hands the
whole scheduled theorem set to lockstep chains: anchor-free light-client
safety with a genesis-plus-clock client, at a freely-timed cadence
(`lockstep_recent_tip_ancestor_agreement`, `lockstep_recent_tip_ancestor_mem`).

## Honest scope (what "thin" means)

The package's budget field is `exposedBound` at the lagged schedule — the
**cumulative** census, exactly `PackageA`'s shape. The distinctive
per-generation census (`erasure_freeze` as the load-bearing bound) is **not**
delivered: the agreement engine's pigeonhole runs at the sliding trailing
window, which straddles the un-pinned tip window, so the consulted census
stays cumulative (`georgeee/mini-consensus-lean: LOCKSTEP_DESIGN.md`, audit obstruction 2). Earning the
per-generation reading is the D1′-full increment. The EUF-CMA surface is
assumed at the **weakest** validator (`SchedCoreUnforgeable` at the constant-0
schedule) so that its scope covers lockstep-accepted chains without
circularity — the existing full-to-core precedent, one step further;
`schedCoreUnforgeable_mono` then delivers it wherever the transport needs it.
`rosterGen` itself is a genuine extra hypothesis relative to `PackageA` — an
assumption about honest *coordination* (all honest signers track one
generation counter), disclosed as such, and the formal content of "lockstep
coordination is necessary after that".
-/

namespace MoltPetit.Model

-- ===========================================================================
-- The lockstep validator
-- ===========================================================================

/-- The **no-mixing rule**: along the chain, the declared generation is
constant within each `n`-slot window and non-decreasing across windows —
equivalently, `keyIndex` is a monotone function of the window index
`slot / n`. Roster-wide: unlike `keyMonoOk` this compares *all* pairs, not
just same-producer pairs. -/
def lockstepOk (n : Nat) : Chain → Bool
  | [] => true
  | b :: rest =>
      rest.all (fun b' =>
        decide ((b.slot / n = b'.slot / n → b.keyIndex = b'.keyIndex) ∧
          b.keyIndex ≤ b'.keyIndex))
      && lockstepOk n rest

theorem lockstepOk_iff_pairwise {n : Nat} (c : Chain) :
    lockstepOk n c = true ↔
      c.Pairwise (fun a b => (a.slot / n = b.slot / n → a.keyIndex = b.keyIndex) ∧
        a.keyIndex ≤ b.keyIndex) := by
  induction c with
  | nil => simp [lockstepOk]
  | cons b rest ih =>
    rw [lockstepOk, Bool.and_eq_true, List.all_eq_true, List.pairwise_cons, ih]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun a ha => ?_, h2⟩
      have := h1 a ha
      rwa [decide_eq_true_eq] at this
    · rintro ⟨h1, h2⟩
      exact ⟨fun a ha => decide_eq_true_eq.mpr (h1 a ha), h2⟩

/-- The **lockstep signed validator**: versioned-registry signatures,
structural/monotone validity, and the no-mixing rule. No schedule parameter —
nothing here references `rosterGen`. -/
def validSignedChainLock {σ sk pk : Type} (n : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChainK n (stripSigs sc)
    && lockstepOk n (stripSigs sc)

/-- The lagged schedule induced by a roster-generation function: a block at
slot `s` is pinned at the *previous* window's generation. The lag is what
absorbs the one unmatured tip window. (`Nat` subtraction makes window 0 lag
to itself, which the genesis convention `genesis_gen` pins exactly.) -/
def lagSched (n : Nat) (rosterGen : Nat → Nat) (s : Nat) : Nat :=
  rosterGen (s / n - 1)

-- ===========================================================================
-- Small transports
-- ===========================================================================

/-- The scheduled pin is antitone in the schedule. -/
theorem schedPinned_mono {sched₁ sched₂ : Nat → Nat}
    (hle : ∀ s, sched₁ s ≤ sched₂ s) {c : Chain}
    (h : schedPinned sched₂ c = true) : schedPinned sched₁ c = true := by
  rw [schedPinned, List.all_eq_true] at h ⊢
  intro b hb
  have := h b hb
  rw [decide_eq_true_eq] at this ⊢
  exact le_trans (hle b.slot) this

/-- Core scheduled validity is antitone in the schedule. -/
theorem schedCore_mono {σ sk pk : Type} {n : Nat} {sched₁ sched₂ : Nat → Nat}
    {ops : SigOps σ sk pk} {registry : KeyRegistry pk} {sc : SignedChain σ}
    (hle : ∀ s, sched₁ s ≤ sched₂ s)
    (h : validSignedChainSchedCore n sched₂ ops registry sc = true) :
    validSignedChainSchedCore n sched₁ ops registry sc = true := by
  rw [validSignedChainSchedCore, Bool.and_eq_true, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, schedPinned_mono hle h.2⟩

/-- The core EUF-CMA surface is **monotone** in the schedule: a surface assumed
at a pointwise-smaller schedule quantifies over a larger accepted set, hence
covers every chain the larger schedule accepts. -/
theorem schedCoreUnforgeable_mono {n : Nat} {sched₁ sched₂ : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    (hle : ∀ s, sched₁ s ≤ sched₂ s)
    (h : SchedCoreUnforgeable n sched₁ ops registry rented Stolen honestSigned now Δ) :
    SchedCoreUnforgeable n sched₂ ops registry rented Stolen honestSigned now Δ where
  unforgeable hVal hmem hRecent hver hrent hstol :=
    h.unforgeable (schedCore_mono hle hVal) hmem hRecent hver hrent hstol

/-- An accepted lockstep chain passes the **core** scheduled validator at the
constant-0 schedule (the pin is vacuous there) — this is what scopes the
package's EUF-CMA surface over lockstep chains. -/
theorem schedCore0_of_lock {σ sk pk : Type} {n : Nat}
    {ops : SigOps σ sk pk} {registry : KeyRegistry pk} {sc : SignedChain σ}
    (h : validSignedChainLock n ops registry sc = true) :
    validSignedChainSchedCore n (fun _ => 0) ops registry sc = true := by
  rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hSigs, hVK⟩, _⟩ := h
  rw [validChainK, Bool.and_eq_true] at hVK
  rw [validSignedChainSchedCore, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hSigs, hVK.1⟩, ?_⟩
  rw [schedPinned, List.all_eq_true]
  intro b _
  exact decide_eq_true_eq.mpr (Nat.zero_le _)

-- ===========================================================================
-- Chain-order helpers for the no-mixing relation
-- ===========================================================================

/-- The lockstep relation for any slot-ordered pair of chain members. -/
private theorem lockstep_rel {n : Nat} {c : Chain} (hS : StrictSlots c)
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

/-- Same-window constancy, for an *unordered* pair of chain members. -/
private theorem lockstep_const {n : Nat} {c : Chain} (hS : StrictSlots c)
    (hLock : lockstepOk n c = true) {A B : Block} (hA : A ∈ c) (hB : B ∈ c)
    (hw : A.slot / n = B.slot / n) : A.keyIndex = B.keyIndex := by
  rcases Nat.lt_trichotomy A.slot B.slot with h | h | h
  · exact (lockstep_rel hS hLock hA hB h).1 hw
  · obtain ⟨i, hi⟩ := exists_blockAt_of_mem hA
    obtain ⟨j, hj⟩ := exists_blockAt_of_mem hB
    have hij : i = j := by
      rcases Nat.lt_trichotomy i j with h' | h' | h'
      · have := strictSlots_lt hS hi hj h'; omega
      · exact h'
      · have := strictSlots_lt hS hj hi h'; omega
    rw [hij, hj] at hi; injection hi with hi; rw [hi]
  · exact ((lockstep_rel hS hLock hB hA h).1 hw.symm).symm

/-- The head block carries the minimum slot. -/
private theorem head_slot_min {c : Chain} (hS : StrictSlots c) {G : Block}
    (hHead : blockAt? c 0 = some G) : ∀ B ∈ c, G.slot ≤ B.slot := by
  intro B hB
  obtain ⟨k, hk⟩ := exists_blockAt_of_mem hB
  cases k with
  | zero => rw [hHead] at hk; injection hk with hk; rw [hk]
  | succ k => exact Nat.le_of_lt (strictSlots_lt hS hHead hk (Nat.succ_pos k))

/-- Producer↔slot injectivity within one `n`-window. -/
private theorem window_producer_inj' {n u s s' : Nat}
    (hs : u ≤ s ∧ s < u + n) (hs' : u ≤ s' ∧ s' < u + n)
    (hp : producerForSlot n s = producerForSlot n s') : s = s' := by
  unfold producerForSlot at hp
  rcases Nat.le_total s s' with hle | hle
  · have hm : Nat.ModEq n s s' := hp
    have hdvd : n ∣ s' - s := (Nat.modEq_iff_dvd' hle).mp hm
    have h0 : s' - s = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · have hm : Nat.ModEq n s' s := hp.symm
    have hdvd : n ∣ s - s' := (Nat.modEq_iff_dvd' hle).mp hm
    have h0 : s - s' = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega

-- ===========================================================================
-- The package
-- ===========================================================================

/-- **The free-cadence lockstep package** (mode 3, D1′-thin). Fields:

* `mono` + `declared` + `genesis_gen` — **B1 as behaviour**: an
  execution-level, per-window, monotone `rosterGen` that every honest
  signature (and genesis) declares. Discovered, not fixed: no verifier is
  given it and no validator checks against it.
* `unforgeable` — the registry EUF-CMA surface at the **weakest** (constant-0)
  core validator, so its scope covers lockstep-accepted chains.
* `hashInj`, `rentBound`, `exposedBound` (at the lagged schedule — the
  cumulative census, `PackageA`'s shape), `budget_le` — as in `PackageA`.

Honest accounting: assumption-wise this is `PackageA` at `lagSched` plus the
behavioural `rosterGen` fields; what is *bought* is that the validator the
deployment runs is schedule-free. -/
structure LockstepPackage (n : Nat) (rosterGen : Nat → Nat) {Sig sk pk : Type}
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (rented : ByzantineSlots)
    (Stolen : Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block)
    (now Δ : Nat) (G : Block) (R T : Nat) : Prop where
  mono : ∀ ⦃w w' : Nat⦄, w ≤ w' → rosterGen w ≤ rosterGen w'
  unforgeable :
    SchedCoreUnforgeable n (fun _ => 0) ops registry rented Stolen honestSigned now Δ
  declared : ∀ ⦃i s : Nat⦄ ⦃B : Block⦄, honestSigned i s = some B →
    B.keyIndex = rosterGen (s / n)
  hashInj : SignedHashInjective (SignedDeclared n ops registry) G
  genesis_gen : G.keyIndex = rosterGen (G.slot / n)
  rentBound : ∀ u, (badSlotsIn rented u n).card ≤ R
  exposedBound : ∀ u, (exposedProducersSched n (lagSched n rosterGen) Stolen u).card ≤ T
  budget_le : R + T ≤ maxByzantine n

/-- A lockstep package is `PackageA` at the lagged schedule — the transport
that hands the entire scheduled theorem set to lockstep chains. -/
theorem LockstepPackage.toPackageA
    {n : Nat} {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T) :
    PackageA n (lagSched n rosterGen) ops registry rented Stolen honestSigned
      now Δ G R T where
  unforgeable := schedCoreUnforgeable_mono (fun _ => Nat.zero_le _) hP.unforgeable
  hashInj := hP.hashInj
  rentBound := hP.rentBound
  exposedBound := hP.exposedBound
  budget_le := hP.budget_le

-- ===========================================================================
-- The pinning theorem
-- ===========================================================================

/-- **The pinning theorem — "no-mixing pins any fork to one generation."**
On an accepted recent lockstep chain, every block whose window is matured
(witnessed by any chain block `D` with `W·n + n ≤ D.slot + 1`) declares
exactly `rosterGen` of its window.

Census: the window is quorum-dense with per-window-distinct producers, all at
one generation `g` (no-mixing). If `g ≠ rosterGen W`, then by the EUF-CMA
surface and the `declared` discipline none of those blocks is honest, so every
one sits at a rented slot or at a producer whose generation-`g` key is stolen:
at most `R + T ≤ ⌊(n-1)/3⌋ < quorum` slots — contradiction. The `≥ lagSched`
side condition the exposure census needs is supplied by the induction
hypothesis one window down. -/
theorem lockstep_declares_rosterGen
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hRecent : ∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) :
    ∀ W, ∀ B ∈ stripSigs sc, B.slot / n = W →
      (∃ D ∈ stripSigs sc, W * n + n ≤ D.slot + 1) →
      B.keyIndex = rosterGen W := by
  classical
  have hVal' := hVal
  rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at hVal'
  obtain ⟨⟨hSigs, hVK⟩, hLock⟩ := hVal'
  rw [sigsOk, List.all_eq_true] at hSigs
  have hVC : ValidChain n (stripSigs sc) := (validChainK_sound hVK).1
  obtain ⟨hSeq, hS, hPL, hDense⟩ := hVC
  have hGmem : G ∈ stripSigs sc := by
    unfold blockAt? at hHead
    exact List.mem_of_getElem? hHead
  have hGmin := head_slot_min hS hHead
  intro W
  induction W using Nat.strongRecOn with
  | ind W IH =>
    intro B hB hBW hMat
    obtain ⟨D, hD, hDmat⟩ := hMat
    obtain ⟨kD, hkD⟩ := exists_blockAt_of_mem hD
    have hWdense : quorum n ≤ windowCount (stripSigs sc) (W * n) n :=
      hDense hkD (W * n) (by omega)
    -- bounds of B's own window
    have hBlo : W * n ≤ B.slot := by
      have : W ≤ B.slot / n := by omega
      exact (Nat.le_div_iff_mul_le (by omega)).mp this
    rcases Nat.eq_zero_or_pos W with hW0 | hWpos
    · -- base: window 0 is genesis's window
      subst hW0
      have hBn : B.slot < n := by
        have h1 : B.slot / n < 1 := by omega
        have := (Nat.div_lt_iff_lt_mul (by omega : 0 < n)).mp h1
        omega
      have hGn : G.slot < n := lt_of_le_of_lt (hGmin B hB) hBn
      have hGW : G.slot / n = 0 := Nat.div_eq_of_lt hGn
      have hkey := lockstep_const hS hLock hB hGmem (by rw [hBW, hGW])
      rw [hkey, hP.genesis_gen, hGW]
    · -- step: W ≥ 1 — the previous window is matured (witness: B itself)
      have hWn : (W - 1) * n + n = W * n := by
        have h1 : W - 1 + 1 = W := by omega
        calc (W - 1) * n + n = (W - 1 + 1) * n := (Nat.succ_mul (W - 1) n).symm
        _ = W * n := by rw [h1]
      obtain ⟨kB, hkB⟩ := exists_blockAt_of_mem hB
      have hPrevDense : quorum n ≤ windowCount (stripSigs sc) ((W - 1) * n) n :=
        hDense hkB ((W - 1) * n) (by omega)
      -- a block A of the previous window, pinned by the induction hypothesis
      obtain ⟨A, hAf⟩ : ∃ A, A ∈ (stripSigs sc).filter (blockInWindow ((W - 1) * n) n) := by
        unfold windowCount at hPrevDense
        cases hfe : (stripSigs sc).filter (blockInWindow ((W - 1) * n) n) with
        | nil =>
          exfalso
          rw [hfe] at hPrevDense
          have hq : 1 ≤ quorum n := by unfold quorum; omega
          simp at hPrevDense
          omega
        | cons A rest => exact ⟨A, List.mem_cons_self ..⟩
      have hAmem : A ∈ stripSigs sc := (List.mem_filter.mp hAf).1
      have hAwin : (W - 1) * n ≤ A.slot ∧ A.slot < (W - 1) * n + n := by
        have := (List.mem_filter.mp hAf).2
        unfold blockInWindow at this
        exact decide_eq_true_eq.mp this
      have hAdiv : A.slot / n = W - 1 := by
        have h1 : W - 1 ≤ A.slot / n := (Nat.le_div_iff_mul_le (by omega)).mpr hAwin.1
        have h2 : A.slot / n < W := by
          refine (Nat.div_lt_iff_lt_mul (by omega : 0 < n)).mpr ?_
          omega
        omega
      have hAkey : A.keyIndex = rosterGen (W - 1) :=
        IH (W - 1) (by omega) A hAmem hAdiv ⟨B, hB, by omega⟩
      have hlow : rosterGen (W - 1) ≤ B.keyIndex := by
        have hAB : A.slot < B.slot := by omega
        have := (lockstep_rel hS hLock hAmem hB hAB).2
        omega
      -- the census
      by_contra hne
      have hSsub : chainSlotsIn (stripSigs sc) (W * n) n ⊆
          badSlotsIn rented (W * n) n ∪
            (Finset.Ico (W * n) (W * n + n)).filter
              (fun s => theftSched n (lagSched n rosterGen) Stolen s) := by
        intro s hs
        obtain ⟨Bs, hBsMem, hBsWin, hBsSlot⟩ := mem_chainSlotsIn.mp hs
        have hsW : Bs.slot / n = W := by
          have h1 : W ≤ Bs.slot / n :=
            (Nat.le_div_iff_mul_le (by omega)).mpr hBsWin.1
          have h2 : Bs.slot / n < W + 1 := by
            refine (Nat.div_lt_iff_lt_mul (by omega : 0 < n)).mpr ?_
            have : (W + 1) * n = W * n + n := Nat.succ_mul W n
            omega
          omega
        have hBsKey : Bs.keyIndex = B.keyIndex :=
          lockstep_const hS hLock hBsMem hB (by rw [hsW, hBW])
        have hcase : rented s ∨ Stolen (producerForSlot n s) B.keyIndex := by
          rcases Classical.em (rented s) with hr | hr
          · exact Or.inl hr
          rcases Classical.em (Stolen (producerForSlot n s) B.keyIndex) with hst | hst
          · exact Or.inr hst
          exfalso
          obtain ⟨sb, hsbmem, hsbeq⟩ := List.mem_map.mp hBsMem
          have hver := hSigs sb hsbmem
          rw [sigOk] at hver
          have hrent' : ¬ rented sb.block.slot := by
            rw [hsbeq, hBsSlot]; exact hr
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
          refine ⟨by omega, B.keyIndex, ?_, hst⟩
          show lagSched n rosterGen s ≤ B.keyIndex
          unfold lagSched
          have : s / n = W := by rw [← hBsSlot]; exact hsW
          rw [this]
          exact hlow
      -- counting
      have hinj : Set.InjOn (producerForSlot n)
          ↑((Finset.Ico (W * n) (W * n + n)).filter
            (fun s => theftSched n (lagSched n rosterGen) Stolen s)) := by
        intro s hs s' hs' hp
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hs hs'
        exact window_producer_inj' ⟨hs.1.1, hs.1.2⟩ ⟨hs'.1.1, hs'.1.2⟩ hp
      have hTb : ((Finset.Ico (W * n) (W * n + n)).filter
          (fun s => theftSched n (lagSched n rosterGen) Stolen s)).card ≤ T := by
        have hEB := hP.exposedBound (W * n)
        unfold exposedProducersSched at hEB
        calc ((Finset.Ico (W * n) (W * n + n)).filter
              (fun s => theftSched n (lagSched n rosterGen) Stolen s)).card
            = (((Finset.Ico (W * n) (W * n + n)).filter
              (fun s => theftSched n (lagSched n rosterGen) Stolen s)).image
                (producerForSlot n)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ T := by
            refine le_trans (le_of_eq ?_) hEB
            congr 1
        _ ≤ T := le_refl T
      have hRb := hP.rentBound (W * n)
      have hcount : quorum n ≤
          (badSlotsIn rented (W * n) n).card +
          ((Finset.Ico (W * n) (W * n + n)).filter
            (fun s => theftSched n (lagSched n rosterGen) Stolen s)).card := by
        calc quorum n ≤ windowCount (stripSigs sc) (W * n) n := hWdense
        _ = (chainSlotsIn (stripSigs sc) (W * n) n).card := (chainSlotsIn_card hS _ _).symm
        _ ≤ _ := le_trans (Finset.card_le_card hSsub) (Finset.card_union_le _ _)
      have hmb : maxByzantine n < quorum n := by
        unfold maxByzantine quorum
        omega
      have := hP.budget_le
      omega

-- ===========================================================================
-- The transport, and the headline corollaries
-- ===========================================================================

/-- **The lagged-schedule transport.** An accepted recent lockstep chain rooted
in `G` passes the *scheduled* validator at `lagSched n rosterGen`. Blocks in a
matured window declare exactly their window's `rosterGen` (pinning) — at or
above the lag; a block in the one unmatured window still clears the lag by
no-mixing monotonicity from the previous window, which is always matured. -/
theorem lockstep_validSignedChainSched
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hRecent : ∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) :
    validSignedChainSched n (lagSched n rosterGen) ops registry sc = true := by
  have hVal' := hVal
  rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at hVal'
  obtain ⟨⟨hSigs, hVK⟩, hLock⟩ := hVal'
  have hVC : ValidChain n (stripSigs sc) := (validChainK_sound hVK).1
  obtain ⟨hSeq, hS, hPL, hDense⟩ := hVC
  have hGmem : G ∈ stripSigs sc := by
    unfold blockAt? at hHead
    exact List.mem_of_getElem? hHead
  have hGmin := head_slot_min hS hHead
  rw [validSignedChainSched, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hSigs, hVK⟩, ?_⟩
  rw [schedPinned, List.all_eq_true]
  intro B hB
  rw [decide_eq_true_eq]
  set W := B.slot / n with hW
  have hBlo : W * n ≤ B.slot := Nat.div_mul_le_self B.slot n
  rcases Nat.eq_zero_or_pos W with hW0 | hWpos
  · -- window 0: constancy with genesis, which declares its own window
    have hBn : B.slot < n := by
      have h1 : B.slot / n < 1 := by omega
      have := (Nat.div_lt_iff_lt_mul (by omega : 0 < n)).mp h1
      omega
    have hGn : G.slot < n := lt_of_le_of_lt (hGmin B hB) hBn
    have hGW : G.slot / n = 0 := Nat.div_eq_of_lt hGn
    have hkey := lockstep_const hS hLock hB hGmem (by rw [← hW, hW0, hGW])
    show rosterGen (B.slot / n - 1) ≤ B.keyIndex
    rw [← hW, hW0, hkey, hP.genesis_gen, hGW]
  · -- W ≥ 1: the previous window is matured (witness: B itself) and pinned
    have hWn : (W - 1) * n + n = W * n := by
      have h1 : W - 1 + 1 = W := by omega
      calc (W - 1) * n + n = (W - 1 + 1) * n := (Nat.succ_mul (W - 1) n).symm
      _ = W * n := by rw [h1]
    obtain ⟨kB, hkB⟩ := exists_blockAt_of_mem hB
    have hPrevDense : quorum n ≤ windowCount (stripSigs sc) ((W - 1) * n) n :=
      hDense hkB ((W - 1) * n) (by omega)
    obtain ⟨A, hAf⟩ : ∃ A, A ∈ (stripSigs sc).filter (blockInWindow ((W - 1) * n) n) := by
      unfold windowCount at hPrevDense
      cases hfe : (stripSigs sc).filter (blockInWindow ((W - 1) * n) n) with
      | nil =>
        exfalso
        rw [hfe] at hPrevDense
        have hq : 1 ≤ quorum n := by unfold quorum; omega
        simp at hPrevDense
        omega
      | cons A rest => exact ⟨A, List.mem_cons_self ..⟩
    have hAmem : A ∈ stripSigs sc := (List.mem_filter.mp hAf).1
    have hAwin : (W - 1) * n ≤ A.slot ∧ A.slot < (W - 1) * n + n := by
      have := (List.mem_filter.mp hAf).2
      unfold blockInWindow at this
      exact decide_eq_true_eq.mp this
    have hAdiv : A.slot / n = W - 1 := by
      have h1 : W - 1 ≤ A.slot / n := (Nat.le_div_iff_mul_le (by omega)).mpr hAwin.1
      have h2 : A.slot / n < W := by
        refine (Nat.div_lt_iff_lt_mul (by omega : 0 < n)).mpr ?_
        omega
      omega
    have hAkey : A.keyIndex = rosterGen (W - 1) :=
      lockstep_declares_rosterGen hn hP hVal hHead hRecent (W - 1) A hAmem hAdiv
        ⟨B, hB, by omega⟩
    show rosterGen (B.slot / n - 1) ≤ B.keyIndex
    rw [← hW]
    have hAB : A.slot < B.slot := by omega
    have := (lockstep_rel hS hLock hAmem hB hAB).2
    omega

/-- **Free-cadence lockstep, headline (equal-tip form).** Under the lockstep
package alone, two chains accepted by the schedule-free lockstep validator,
rooted in one genesis, with recent equal-height tips, agree on the block `n`
below each tip — anchor-free, `Δconf`-free, at a freely-timed rotation
cadence. -/
theorem lockstep_recent_tip_ancestor_agreement
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal  : validSignedChainLock n ops registry sc  = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    (hHead  : blockAt? (stripSigs sc ) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B' :=
  packageA_recent_tip_ancestor_agreement hn hP.toPackageA
    (lockstep_validSignedChainSched hn hP hVal  hHead  ⟨sTip,  hTipS,  hRecent⟩)
    (lockstep_validSignedChainSched hn hP hVal' hHead' ⟨sTip', hTipS', hRecent'⟩)
    hHead hHead' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'

/-- **Free-cadence lockstep, membership form.** The `n`-deep ancestor of the
lower-tipped lockstep chain is a block of the other chain too, at least `n`
deep there. -/
theorem lockstep_recent_tip_ancestor_mem
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal  : validSignedChainLock n ops registry sc  = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    (hHead  : blockAt? (stripSigs sc ) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block}
    (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - n) = some B) :
    ∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B :=
  sched_recent_tip_ancestor_mem hn
    (schedUnforgeable_of_core hP.toPackageA.unforgeable)
    hP.hashInj (packageA_byzantine_bounded hP.toPackageA)
    (lockstep_validSignedChainSched hn hP hVal  hHead  ⟨sTip,  hTipS,  hRecent⟩)
    (lockstep_validSignedChainSched hn hP hVal' hHead' ⟨sTip', hTipS', hRecent'⟩)
    hHead hHead' hTipS hTipS' hRecent hRecent' hLong hLe hB

end MoltPetit.Model
