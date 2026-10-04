import MoltPetit.Model.KeyStealingScheduleHorizon
import MoltPetit.Model.KeyStealingScheduleBudget

/-!
# MoltPetit — the timed theft layer (§10.4, the temporal seam)

*Superseded for mode 2* by `SchedExposure.lean` (`sched_exposure_agreement`),
which charges early theft through the timed exposure budget directly instead
of assuming no premature theft. `NoBackdate` below names an assumption of an
earlier static model that has since been removed from the development; the
comparisons with it are historical.

`georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md` §10.4 leaves one seam open in the scheduled variant:
the packages' temporal content — A3/B3's "no theft before provisioning", B2's
"no theft after erasure" — lived in prose, and the budget hypothesis was
consumed in a timeless reading. This module gives that content a formal home
and machine-checks its consequences, for the **flagship schedule**
`schedule s = s / R` (period `R`, generation `j` provisioned just-in-time at
era start `j * R`).

What is **derived** here (each previously prose or absent):

* `theft_is_recent` — **backward theft-locality**: under `NoPrematureTheft`
  (A3, now a formal named hypothesis), a theft that poisons slot `s` occurred
  at real slot `r > s − R`. A window above the horizon is never charged for
  anything that happened more than one generation period before it opened.
* `horizon_budget_of_timed` — **the timed I3**: the horizon budget
  `ByzantineBoundedFrom H` that the `KeyStealingScheduleHorizon` theorems
  consume is derived from a rent rate and a **recent-theft census** rate
  (`recentTheftProducers`), both required only of windows from the horizon
  on. Composed with the horizon theorems, the light-client statement's
  corruption hypothesis mentions no *window* below `H` and no theft
  at-or-before `u − R` of any consulted window `u` (for windows within `R`
  of the horizon the census therefore reaches up to `R − 1` slots below
  `H`).
* `sched_forwardstamp_bounded` — **bounded forward-stamping**: a block of a
  schedule-pinned chain minted at real slot `r` bears a stamp `< r + R`,
  because the signing key for a later stamp does not exist yet
  (`NoPrematureMint`, the mint-side face of just-in-time provisioning).
  Direction-honest contrast with the static model's `NoBackdate` (the
  **two-sided** pin: an honest-stamp block's stamp *equals* its mint slot,
  which must be assumed outright — `noBackdate_independent`'s witness is a
  *back-dated* block, stamp `1` minted at bad real slot `3`): the schedule
  derives the **forward half** of that pin with `R` slack — a recent stamp
  implies a recent mint. The **back-dating half** (an old-stamped block
  minted arbitrarily late with a live stolen key of a legal generation) is
  *not* derived — `sched_backdate_consistent` machine-checks that it is
  consistent with everything this module assumes; that capability is what
  the budget accounting charges, and its per-block exclusion is the assumed
  EUF-CMA surface's business.
  `sched_recent_block_fresh` is the client-facing corollary of the forward
  half: every recency-window block of an accepted chain was minted within
  the last `Δ + R` slots — a recent-tipped fork cannot have been assembled
  in the deep past.
* `theft_during_era_of_erasure` — with `ErasureTimed` (B2, formal: retired
  generations are not stealable), every theft is confined to its generation's
  own era `[j·R, (j+1)·R)` — the "freeze" of §10.2, now a statement about
  real time.

`PackageATimed` / `PackageBTimed` bundle the surfaces and rates and deliver
the horizon light-client conclusion end to end
(`packageATimed_recent_tip_ancestor_agreement`).

## Honest scope (what remains open, precisely)

* **The census is future-inclusive.** `recentTheftProducers n R stolenAt u`
  pins every counted theft to real time `> u − R` (backward locality,
  derived), but counts qualifying thefts at *any later* real time — because
  the corruption predicate the agreement machinery consumes
  (`badSched`, via the timeless `stolenOf`) is itself timeless. The
  operational reading of the rate is therefore "at most `T` distinct
  producers are *ever*, from the horizon on, hit by a current-or-later
  generation theft" — per-window, with the victims-set bounded across the
  execution's future. Confining the census to thefts *before the client's
  validation time* requires re-plumbing the EUF-CMA surface itself with mint
  times (a `SchedTimedUnforgeable` whose conclusion keys on theft-before-mint
  rather than theft-ever) — the natural next increment, not attempted here.
* `NoPrematureTheft` / `NoPrematureMint` / `ErasureTimed` are named
  operational hypotheses (the formalizations of A3/B3 and B2), justified by
  just-in-time cold-root delegation and honest erasure; they are not further
  reduced. The EUF-CMA surface (`SchedCoreUnforgeable`) and hash injectivity
  are unchanged and still assumed.
-/

namespace MoltPetit.Model

open Classical

-- ===========================================================================
-- Timed theft and the timeless projection
-- ===========================================================================

/-- The timeless theft predicate the whole scheduled development consumes,
as the projection of a time-stamped theft relation `stolenAt i j r`
("producer `i`'s generation-`j` key is exfiltrated at real slot `r`"). -/
def stolenOf (stolenAt : Nat → Nat → Nat → Prop) (i j : Nat) : Prop :=
  ∃ r, stolenAt i j r

/-- **A3, timed (no premature exposure).** A generation-`j` key can be stolen
only from its provisioning time on: under just-in-time per-generation
delegation with period `R`, generation `j` exists only from slot `j * R`. -/
def NoPrematureTheft (R : Nat) (stolenAt : Nat → Nat → Nat → Prop) : Prop :=
  ∀ i j r, stolenAt i j r → j * R ≤ r

/-- **B2, timed (erasure).** A generation is not stealable after it retires:
honest nodes destroy generation `j`'s key material at the era boundary
`(j+1) * R`. -/
def ErasureTimed (R : Nat) (stolenAt : Nat → Nat → Nat → Prop) : Prop :=
  ∀ i j r, stolenAt i j r → r < (j + 1) * R

/-- Under A3 + erasure, every theft is confined to its generation's own era —
the §10.2 "per-generation compromise freezes" claim, in real time. -/
theorem theft_during_era_of_erasure {R : Nat}
    {stolenAt : Nat → Nat → Nat → Prop}
    (hA3 : NoPrematureTheft R stolenAt) (hEr : ErasureTimed R stolenAt)
    {i j r : Nat} (h : stolenAt i j r) :
    j * R ≤ r ∧ r < (j + 1) * R :=
  ⟨hA3 i j r h, hEr i j r h⟩

-- ===========================================================================
-- Backward theft-locality
-- ===========================================================================

/-- **Backward theft-locality.** A theft that poisons slot `s` under the
flagship schedule (a stolen generation at-or-above `s / R`) occurred at real
slot `r > s − R`: the poisoning generation was provisioned at most one period
before `s`. Nothing that happened at-or-before `s − R` can corrupt slot `s`. -/
theorem theft_is_recent {R : Nat} (hR : 0 < R)
    {stolenAt : Nat → Nat → Nat → Prop} (hA3 : NoPrematureTheft R stolenAt)
    {n s : Nat} (h : theftSched n (fun t => t / R) (stolenOf stolenAt) s) :
    ∃ j r, s / R ≤ j ∧ stolenAt (producerForSlot n s) j r ∧ s < r + R := by
  obtain ⟨j, hj, r, hr⟩ := h
  refine ⟨j, r, hj, hr, ?_⟩
  have h1 := hA3 _ _ _ hr
  have h1' : R * j ≤ r := by
    rw [Nat.mul_comm]
    exact h1
  have hdm : R * (s / R) + s % R = s := Nat.div_add_mod s R
  have hmod : s % R < R := Nat.mod_lt _ hR
  have hmul : R * (s / R) ≤ R * j := Nat.mul_le_mul_left R hj
  omega

/-- The **recent-theft census** for window `u`: producers hit — at some real
slot `r` with `u < r + R` — by a theft of a generation at-or-above the
window's opening era `u / R`. By `theft_is_recent` this census covers every
producer `badSched` can expose inside the window; unlike the timeless
`exposedProducersSched` reading, each counted theft is pinned to real time
after `u − R`. (It remains future-inclusive — module doc, honest scope.
Note the conjunct `u < r + R` is *redundant under* `NoPrematureTheft`: any
theft of a generation `≥ u / R` already happened after `u − R`, so under A3
this census coincides extensionally with the pure generation-floor census
`∃ j ≥ u / R, stolenOf stolenAt i j` — the real-time pin documents the
derived backward locality rather than adding a restriction, and the rate a
deployment asserts is extensionally a timeless one.) -/
noncomputable def recentTheftProducers (n R : Nat)
    (stolenAt : Nat → Nat → Nat → Prop) (u : Nat) : Finset Nat :=
  (Finset.range n).filter (fun i => ∃ j r, u / R ≤ j ∧ stolenAt i j r ∧ u < r + R)

/-- The scheduled exposure census of a window is covered by its recent-theft
census: exposure is only ever caused by thefts of generations provisioned at
most one period before the window. -/
theorem exposedSched_subset_recentTheft {n R : Nat} (hn : 0 < n) (hR : 0 < R)
    {stolenAt : Nat → Nat → Nat → Prop} (hA3 : NoPrematureTheft R stolenAt)
    (u : Nat) :
    exposedProducersSched n (fun s => s / R) (stolenOf stolenAt) u ⊆
      recentTheftProducers n R stolenAt u := by
  intro i hi
  unfold exposedProducersSched at hi
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hi
  rw [Finset.mem_filter] at hs
  obtain ⟨hsIco, hTheft⟩ := hs
  obtain ⟨j, r, hj, hst, hrec⟩ := theft_is_recent hR hA3 hTheft
  rw [Finset.mem_Ico] at hsIco
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, j, r, ?_, hst, ?_⟩
  · unfold producerForSlot
    exact Nat.mod_lt _ hn
  · have hdiv : u / R ≤ s / R := Nat.div_le_div_right (by omega)
    omega
  · omega

-- ===========================================================================
-- The timed I3: the horizon budget from timed rates
-- ===========================================================================

/-- **The horizon budget, derived from timed rates** (the timed I3). Under A3,
a rent rate `Rrent` and a recent-theft census rate `T` — both required only of
windows from the horizon `H` on — deliver `ByzantineBoundedFrom H` for the
flagship schedule: exactly the corruption hypothesis the
`KeyStealingScheduleHorizon` theorems consume. Composed with them, the
light-client statement's budget mentions no window below `H` and no theft
at-or-before `u − R` for any window `u` it does mention: the retroactive
charge is gone from the *derivation*, not just from the statement. -/
theorem horizon_budget_of_timed {n R H : Nat} (hn : 0 < n) (hR : 0 < R)
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop}
    {Rrent T : Nat}
    (hA3 : NoPrematureTheft R stolenAt)
    (hRent : ∀ u, H ≤ u → (badSlotsIn rented u n).card ≤ Rrent)
    (hTheft : ∀ u, H ≤ u → (recentTheftProducers n R stolenAt u).card ≤ T)
    (hRT : Rrent + T ≤ maxByzantine n) :
    ByzantineBoundedFrom H n
      (badSched n (fun s => s / R) rented (stolenOf stolenAt)) := by
  intro u hu
  have hsplit := badSlotsIn_union_le rented
    (theftSched n (fun s => s / R) (stolenOf stolenAt)) u n
  have htheft := theftSlotsSched_card_le_exposed n (fun s => s / R)
    (stolenOf stolenAt) u
  have hsub := exposedSched_subset_recentTheft hn hR hA3 (stolenAt := stolenAt) u
  have hcard := Finset.card_le_card hsub
  have hrw : (badSlotsIn
        (badSched n (fun s => s / R) rented (stolenOf stolenAt)) u n).card =
      (badSlotsIn
        (fun s => rented s ∨ theftSched n (fun t => t / R) (stolenOf stolenAt) s)
        u n).card := rfl
  rw [hrw]
  calc (badSlotsIn
        (fun s => rented s ∨ theftSched n (fun t => t / R) (stolenOf stolenAt) s)
        u n).card
      ≤ (badSlotsIn rented u n).card
        + (badSlotsIn (theftSched n (fun t => t / R) (stolenOf stolenAt)) u n).card :=
        hsplit
    _ ≤ Rrent + T :=
        Nat.add_le_add (hRent u hu)
          (le_trans htheft (le_trans hcard (hTheft u hu)))
    _ ≤ maxByzantine n := hRT

-- ===========================================================================
-- The mint side: bounded forward-stamping (the scheduled NoBackdate)
-- ===========================================================================

/-- **A3, mint side (no premature signatures).** No signature under a
generation-`j` key exists before generation `j` is provisioned: a block
carrying declared index `j` cannot appear in the real-time log before
`j * R`. This is the signing-side face of just-in-time provisioning — a key
that does not exist cannot have produced a signature — stated as a named
hypothesis exactly as `NoBackdate` is in the static model. -/
def NoPrematureMint (R : Nat) (log : TimedLog) : Prop :=
  ∀ r, ∀ B ∈ log r, B.keyIndex * R ≤ r

/-- **Forward-stamping is bounded by one generation period** — the *forward
half* of the static model's `NoBackdate` content, *derived*. A block of a
schedule-pinned chain that appears in the real-time log at slot `r` bears a
stamp `B.slot < r + R`: the pin forces `B.slot / R ≤ B.keyIndex`, and the
generation-`B.keyIndex` key did not exist before `B.keyIndex · R`.
Direction accounting: `NoBackdate` is the two-sided pin stamp = mint for
honest stamps, assumed outright in the static model
(`noBackdate_independent`'s witness is a *back-dated* block — a direction
this theorem does not touch, and which `sched_backdate_consistent` below
shows remains consistent with this module's hypotheses). What provisioning
buys is exactly the forward half, with `R` slack. -/
theorem sched_forwardstamp_bounded {R : Nat} (hR : 0 < R) {log : TimedLog}
    (hMint : NoPrematureMint R log)
    {c : Chain} (hPin : schedPinned (fun s => s / R) c = true)
    {B : Block} (hB : B ∈ c) {r : Nat} (hr : B ∈ log r) :
    B.slot < r + R := by
  rw [schedPinned, List.all_eq_true] at hPin
  have hp := hPin B hB
  rw [decide_eq_true_eq] at hp
  have hm := hMint r B hr
  have hm' : R * B.keyIndex ≤ r := by
    rw [Nat.mul_comm]
    exact hm
  have hdm : R * (B.slot / R) + B.slot % R = B.slot := Nat.div_add_mod _ _
  have hmod : B.slot % R < R := Nat.mod_lt _ hR
  have hmul : R * (B.slot / R) ≤ R * B.keyIndex := Nat.mul_le_mul_left R hp
  omega

/-- **Recent blocks are freshly minted** (client-facing corollary). A block
whose stamp passes the recency reading `now ≤ B.slot + Δ` was minted within
the last `Δ + R` slots: `now < r + Δ + R`. A recent-tipped fork cannot have
been assembled in the deep past — its recency-window content postdates
`now − (Δ + R)`. This is the formal core of "a from-scratch fork cannot have
a recent tip without fresh, budget-counted minting". -/
theorem sched_recent_block_fresh {R : Nat} (hR : 0 < R) {log : TimedLog}
    (hMint : NoPrematureMint R log)
    {c : Chain} (hPin : schedPinned (fun s => s / R) c = true)
    {B : Block} (hB : B ∈ c) {r : Nat} (hr : B ∈ log r)
    {now Δ : Nat} (hRecent : now ≤ B.slot + Δ) :
    now < r + Δ + R := by
  have := sched_forwardstamp_bounded hR hMint hPin hB hr
  omega

/-- **The back-dating half is genuinely not derived** — the scheduled mirror
of `noBackdate_independent`, making the direction split precise. For *every*
real slot `r` (arbitrarily late) there is an execution in which
`NoPrematureMint` holds and a schedule-pinned block stamped `0` is minted at
`r`: minting old-stamped blocks under a legal generation is consistent with
everything this module assumes. That capability is what the budget accounting
charges (the retroactive/future-inclusive readings), and its per-block
exclusion is the assumed EUF-CMA surface's business — not this layer's. -/
theorem sched_backdate_consistent (R r : Nat) :
    ∃ (log : TimedLog) (B : Block),
      NoPrematureMint R log ∧ B ∈ log r ∧ B.slot = 0 ∧
      schedPinned (fun s => s / R) [B] = true := by
  classical
  refine ⟨fun _ => {(⟨0, 0, none, 0, 0, 0⟩ : Block)},
    ⟨0, 0, none, 0, 0, 0⟩, ?_, ?_, rfl, ?_⟩
  · intro r' B hB
    rw [Finset.mem_singleton] at hB
    rw [hB]
    simp
  · simp
  · simp [schedPinned, Nat.zero_div]

-- ===========================================================================
-- The timed packages
-- ===========================================================================

/-- **Package A, timed** (§10.1 with its temporal content formalized): the
flagship-schedule assumption set whose budget fields are *horizon-scoped and
time-stamped*. Compared to `PackageA`: the schedule is pinned to `s / R`;
`Stolen` is the projection of a time-stamped `stolenAt`; A3 is the formal
field `notBefore` (no longer prose); and the rate fields read only windows
from `H` on and thefts pinned after `u − R` (`recentTheftProducers`) — no
*backward*-cumulative quantity remains; the census stays future-inclusive,
so its rate is still a bound across the execution's future (module doc,
honest scope). A0 (cold root) stays the instantiation-level justification
of `notBefore` and of the surface. -/
structure PackageATimed (n R H : Nat) {Sig sk pk : Type}
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk)
    (rented : ByzantineSlots) (stolenAt : Nat → Nat → Nat → Prop)
    (honestSigned : Nat → Nat → Option Block)
    (now Δ : Nat) (G : Block) (Rrent T : Nat) : Prop where
  unforgeable : SchedCoreUnforgeable n (fun s => s / R) ops registry rented
      (stolenOf stolenAt) honestSigned now Δ
  hashInj : SignedHashInjective (SignedDeclared n ops registry) G
  notBefore : NoPrematureTheft R stolenAt
  rentBound : ∀ u, H ≤ u → (badSlotsIn rented u n).card ≤ Rrent
  recentTheftBound : ∀ u, H ≤ u → (recentTheftProducers n R stolenAt u).card ≤ T
  budget_le : Rrent + T ≤ maxByzantine n

/-- Package A (timed) delivers the horizon budget. -/
theorem packageATimed_horizon_budget {n R H : Nat} (hn : 0 < n) (hR : 0 < R)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {Rrent T : Nat}
    (hA : PackageATimed n R H ops registry rented stolenAt honestSigned
      now Δ G Rrent T) :
    ByzantineBoundedFrom H n
      (badSched n (fun s => s / R) rented (stolenOf stolenAt)) :=
  horizon_budget_of_timed hn hR hA.notBefore hA.rentBound hA.recentTheftBound
    hA.budget_le

/-- **Package A (timed) ⊢ horizon light-client safety, end to end.** Under
`PackageATimed` alone, two scheduled-validated chains with recent equal-height
tips agree on the block `n` below each tip — no anchor, no `Δconf`, no shared
genesis assumed, no budget below the horizon, no theft charged at-or-before
`u − R` of any consulted window `u`. This is the §10.4 seam's deliverable in
one implication (the residuals are exactly the named fields — module doc). -/
theorem packageATimed_recent_tip_ancestor_agreement
    {n R H : Nat} (hn : 1 ≤ n) (hR : 0 < R)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {Rrent T : Nat}
    (hA : PackageATimed n R H ops registry rented stolenAt honestSigned
      now Δ G Rrent T)
    {sc sc' : SignedChain Sig}
    (hVal  : validSignedChainSched n (fun s => s / R) ops registry sc  = true)
    (hVal' : validSignedChainSched n (fun s => s / R) ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hH  : H + n ≤ sTip.slot  + 1)
    (hH' : H + n ≤ sTip'.slot + 1)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B' :=
  sched_recent_tip_ancestor_agreement_horizon hn
    (schedUnforgeable_of_core hA.unforgeable) hA.hashInj
    (packageATimed_horizon_budget (by omega) hR hA)
    hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hH hH'
    hTipHeight hB hB'

/-- **Package B, timed** (§10.2 with its temporal content formalized):
Package A (timed) plus the formal erasure field `notAfter` (`ErasureTimed`) —
under which every theft is confined to its generation's own era
(`theft_during_era_of_erasure`). As with the timeless packages, the
`extends` records the assumption-set inclusion "B assumes A plus erasure";
the erasure field is documentary for the safety chain (which A's fields
already deliver) and is what a deployment's per-era compromise accounting
instantiates. -/
structure PackageBTimed (n R H : Nat) {Sig sk pk : Type}
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk)
    (rented : ByzantineSlots) (stolenAt : Nat → Nat → Nat → Prop)
    (honestSigned : Nat → Nat → Option Block)
    (now Δ : Nat) (G : Block) (Rrent T : Nat)
    extends PackageATimed n R H ops registry rented stolenAt honestSigned
      now Δ G Rrent T : Prop where
  notAfter : ErasureTimed R stolenAt

/-- Package B (timed) delivers the same horizon conclusion through its
Package-A core. -/
theorem packageBTimed_recent_tip_ancestor_agreement
    {n R H : Nat} (hn : 1 ≤ n) (hR : 0 < R)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {Rrent T : Nat}
    (hPB : PackageBTimed n R H ops registry rented stolenAt honestSigned
      now Δ G Rrent T)
    {sc sc' : SignedChain Sig}
    (hVal  : validSignedChainSched n (fun s => s / R) ops registry sc  = true)
    (hVal' : validSignedChainSched n (fun s => s / R) ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hH  : H + n ≤ sTip.slot  + 1)
    (hH' : H + n ≤ sTip'.slot + 1)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B' :=
  packageATimed_recent_tip_ancestor_agreement hn hR hPB.toPackageATimed
    hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hH hH'
    hTipHeight hB hB'

end MoltPetit.Model
