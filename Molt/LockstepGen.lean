import Molt.Rotation
import MoltPetit.Model.KeyStealingLockstepTimed
import MoltPetit.Model.KeyStealingLockstepGen
import MoltPetit.Model.KeyStealingWindowCore
import Spec.Reference

/-!
# Molt — mode 3, per-generation census (D1′-full), paper-side re-presentation

The paper-namespace re-presentation of W5: discharges the honest-scope bound
that mode 3's budget was cumulative-only. Re-export idiom of `Molt/Rotation.
lean`'s mode-3 section: `abbrev` for the Prop-valued packages, and a wrapper
theorem proved by rewriting `Molt.validSignedChainLock` to the core validator
via `validSignedChainLock_eq_core` (the idiom `lockstep_client_safety` itself
uses) rather than an `alias`, since the headline theorems here range over
`Molt.validSignedChainLock`/`SigningLog`, not core names directly.
-/

namespace Molt

/-- The per-generation corruption predicate: a slot is bad if rented, or its
producer's key of the generation the roster is at in that grid window is
stolen. -/
abbrev badLockAt := @MoltPetit.Model.badLockAt

/-- The non-inductive, genesis-free per-window pinning theorem (paper §6.3,
mode 3, per-generation form). -/
alias lockstep_window_declares_rosterGen := MoltPetit.Model.lockstep_window_declares_rosterGen

/-- **Lockstep safety, per-generation form** (mode 3, paper Theorem 5′).
Under the schedule-free lockstep validator and the per-generation package
alone: agreement at confirmation depth `2n` — no shared genesis needed, the
strengthening over Theorem 5 the aligned-window route buys. -/
theorem lockstep_client_safety_gen
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageGen n rosterGen ops registry rented Stolen
      honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal  : validSignedChainLock n ops registry sc  = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : 2 * n < (stripSigs sc ).length)
    (hLong' : 2 * n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc )
      ((stripSigs sc ).length - 1 - 2 * n) = some B)
    (hB' : blockAt? (stripSigs sc')
      ((stripSigs sc').length - 1 - 2 * n) = some B') :
    B = B' := by
  rw [validSignedChainLock_eq_core] at hVal hVal'
  exact MoltPetit.Model.lockstepGen_recent_tip_ancestor_agreement hn hP
    hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'

/-- **Lockstep safety, timed form** (mode 3, paper Theorem 5′ with real-time
theft): under the timed per-generation package — theft time-stamped, erasure
load-bearing — the same `2n`-deep, genesis-free agreement. -/
theorem lockstep_client_safety_timed
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackageTimed n rosterGen ops registry rented stolenAt
      honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal  : validSignedChainLock n ops registry sc  = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : 2 * n < (stripSigs sc ).length)
    (hLong' : 2 * n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc )
      ((stripSigs sc ).length - 1 - 2 * n) = some B)
    (hB' : blockAt? (stripSigs sc')
      ((stripSigs sc').length - 1 - 2 * n) = some B') :
    B = B' := by
  rw [validSignedChainLock_eq_core] at hVal hVal'
  exact MoltPetit.Model.lockstepTimed_recent_tip_ancestor_agreement hn hP
    hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'

/-- Operator erasure turns while-live theft into timeless per-generation theft
(paper §6.3, mode 3). -/
alias genBound_of_preRetirementBound := MoltPetit.Model.genBound_of_preRetirementBound

/-- Mode 3's per-generation agreement at unequal tip heights
(paper Theorem 5b / Thm 5′). -/
alias lockstepGen_recent_tip_ancestor_mem := MoltPetit.Model.lockstepGen_recent_tip_ancestor_mem

/-- Mode 3's per-generation genesis agreement without assuming shared genesis
(paper Theorem 5b / Thm 5′). -/
alias lockstepGen_recent_genesis_agreement := MoltPetit.Model.lockstepGen_recent_genesis_agreement

/-- Sharp depth bound for mode 3 per-generation agreement: exactly n + ((t+1) % n)
positions below lower tip slot t (paper §6.3). -/
alias lockstepGen_shared_prefix_sharp := MoltPetit.Model.lockstepGen_shared_prefix_sharp

/-- Window-aligned prefix sharing engine (paper §6.3). -/
alias window_shared_prefix := MoltPetit.Model.window_shared_prefix

/-- Package conversion: cumulative package implies per-generation package when
no generation is skipped (paper §6.3). -/
alias LockstepPackage.toGen := MoltPetit.Model.LockstepPackage.toGen

end Molt
