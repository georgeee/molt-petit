import MoltPetit.Model.KeyStealingLockstepGen
import MoltPetit.Model.KeyStealingScheduleTimed
import Spec.Model

/-!
# MoltPetit — mode 3, the timed theft layer (D1′-full, real time)

The timed twin of `KeyStealingLockstepGen.lean`: a time-stamped theft
relation `stolenAt i j r`, the roster's own switch grid `rosterGen ∘ (·/n)`
in place of mode 2's flagship `j * R`, and a derivation in which
`ErasureTimedLock` is CONSUMED — the mirror image of mode 2's
`PackageBTimed`, where erasure is documentary and A3 is load-bearing. Here
A3 (`NoPrematureTheftLock`) is documentary (consumed only by
`theft_in_era_lock`) and erasure is what turns the while-live census
(`preRetirementTheftProducers`) into the timeless per-generation census
`LockstepPackageGen.genBound` needs.

Reuses `stolenOf` from `KeyStealingScheduleTimed.lean` unchanged — the
timeless projection is the same relation both modes' derivations consume.
-/

namespace MoltPetit.Model
open Classical

-- ===========================================================================
-- (1) The timed theft predicates, mode 3
-- ===========================================================================

/-- Under A3 + erasure, every theft is of the exact generation the roster is
at in the theft's own grid window — "per-generation compromise freezes" in
real time, for the free cadence. Axiom-free (`Nat.le_antisymm`). -/
theorem theft_in_era_lock {n : Nat} {rosterGen : Nat → Nat}
    {stolenAt : Nat → Nat → Nat → Prop}
    (hA3 : NoPrematureTheftLock n rosterGen stolenAt)
    (hEr : ErasureTimedLock n rosterGen stolenAt)
    {i j r : Nat} (h : stolenAt i j r) :
    rosterGen (r / n) = j :=
  Nat.le_antisymm (hEr i j r h) (hA3 i j r h)

/-- Skipped generations have empty census: a stolen generation was live at
some grid window. -/
theorem stolen_generation_was_live {n : Nat} {rosterGen : Nat → Nat}
    {stolenAt : Nat → Nat → Nat → Prop}
    (hA3 : NoPrematureTheftLock n rosterGen stolenAt)
    (hEr : ErasureTimedLock n rosterGen stolenAt)
    {i j : Nat} (h : stolenOf stolenAt i j) : ∃ W, rosterGen W = j := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r / n, theft_in_era_lock hA3 hEr hr⟩

-- ===========================================================================
-- (2) Faithfulness to the mode-2 flagship
-- ===========================================================================

/-- At `rosterGen := fun W => W` (the identity counter — the roster switches
generation once per grid window, never skipping or repeating) and `R := n`,
the lock form of A3 is exactly the flagship `NoPrematureTheft`. -/
theorem noPrematureTheftLock_iff_flagship {n : Nat} (hn : 0 < n)
    {stolenAt : Nat → Nat → Nat → Prop} :
    NoPrematureTheftLock n (fun W => W) stolenAt ↔ NoPrematureTheft n stolenAt := by
  unfold NoPrematureTheftLock NoPrematureTheft
  constructor
  · intro h i j r hr
    exact (Nat.le_div_iff_mul_le hn).mp (h i j r hr)
  · intro h i j r hr
    exact (Nat.le_div_iff_mul_le hn).mpr (h i j r hr)

/-- At `rosterGen := fun W => W` and `R := n`, the lock form of B2 is exactly
the flagship `ErasureTimed`. -/
theorem erasureTimedLock_iff_flagship {n : Nat} (hn : 0 < n)
    {stolenAt : Nat → Nat → Nat → Prop} :
    ErasureTimedLock n (fun W => W) stolenAt ↔ ErasureTimed n stolenAt := by
  unfold ErasureTimedLock ErasureTimed
  constructor
  · intro h i j r hr
    have h1 : r / n ≤ j := h i j r hr
    have h2 : r / n < j + 1 := by omega
    exact (Nat.div_lt_iff_lt_mul hn).mp h2
  · intro h i j r hr
    have h1 : r < (j + 1) * n := h i j r hr
    have h2 : r / n < j + 1 := (Nat.div_lt_iff_lt_mul hn).mpr h1
    show r / n ≤ j
    omega

-- ===========================================================================
-- (3) The while-live census and the timed mode-3 I3
-- ===========================================================================

/-- **The timed mode-3 I3 — erasure carries the weight.** Under
`ErasureTimedLock` and a while-live rate `T`, the timeless per-generation
census (the one `LockstepPackageGen.genBound` needs) is bounded by `T` too:
every timeless theft of generation `j` is, by erasure, a while-live theft of
`j`. Mirror of `horizon_budget_of_timed`/`exposedSched_subset_recentTheft`
with the roles of A3 and erasure exchanged: there A3 bounds thefts from
below in time, here erasure bounds them from above (no post-retirement
theft), and the timeless census the safety engine consumes is DERIVED,
not assumed. -/
theorem genBound_of_preRetirementBound {n : Nat} {rosterGen : Nat → Nat}
    {stolenAt : Nat → Nat → Nat → Prop} {T : Nat}
    (hEr : ErasureTimedLock n rosterGen stolenAt)
    (hLive : ∀ j, (preRetirementTheftProducers n rosterGen stolenAt j).card ≤ T) :
    ∀ j : Nat, ((Finset.range n).filter (fun i => stolenOf stolenAt i j)).card ≤ T := by
  intro j
  refine le_trans (Finset.card_le_card ?_) (hLive j)
  intro i hi
  rw [Finset.mem_filter] at hi
  obtain ⟨hin, r, hr⟩ := hi
  unfold preRetirementTheftProducers
  rw [Finset.mem_filter]
  exact ⟨hin, r, hr, hEr i j r hr⟩

-- ===========================================================================
-- (4) The timed package and end-to-end safety
-- ===========================================================================

/-- The timed package delivers the per-generation package: `notAfter` +
`preRetirementTheftBound` derive `genBound` via `genBound_of_preRetirementBound`. -/
theorem LockstepPackageTimed.toGen {n : Nat} {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {stolenAt : Nat → Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageTimed n rosterGen ops registry rented stolenAt honestSigned
      now Δ G R T) :
    LockstepPackageGen n rosterGen ops registry rented (stolenOf stolenAt) honestSigned
      now Δ G R T where
  unforgeable := hP.unforgeable
  declared := hP.declared
  hashInj := hP.hashInj
  rentBound := hP.rentBound
  budget_le := hP.budget_le
  genBound := genBound_of_preRetirementBound hP.notAfter hP.preRetirementTheftBound

/-- **Timed package ⊢ safety, end to end (equal-tip form).** The `PackageBTimed`
twin for mode 3, except that here `notAfter` is genuinely on the proof path. -/
theorem lockstepTimed_recent_tip_ancestor_agreement
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {stolenAt : Nat → Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageTimed n rosterGen ops registry rented stolenAt honestSigned
      now Δ G R T)
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
    B = B' :=
  lockstepGen_recent_tip_ancestor_agreement hn hP.toGen hVal hVal' hTipS hTipS'
    hRecent hRecent' hLong hLong' hTipHeight hB hB'

/-- **Timed package ⊢ safety, end to end (membership form).** -/
theorem lockstepTimed_recent_tip_ancestor_mem
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {stolenAt : Nat → Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageTimed n rosterGen ops registry rented stolenAt honestSigned
      now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block} (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong : 2 * n < (stripSigs sc).length)
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block} (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - 2 * n) = some B) :
    ∃ i', i' + 2 * n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B :=
  lockstepGen_recent_tip_ancestor_mem hn hP.toGen hVal hVal' hTipS hTipS'
    hRecent hRecent' hLong hLe hB

end MoltPetit.Model
