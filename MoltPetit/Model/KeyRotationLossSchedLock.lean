import MoltPetit.Model.KeyRotationLoss
import MoltPetit.Model.KeyStealingSchedule
import MoltPetit.Model.KeyStealingLockstepGen

/-!
# Modes 2 and 3 against key loss

The mode-2 and mode-3 analogues of `keyrot_loss_agreement`: loss changes none
of the hypotheses of the timed light-client theorem, so two chains accepted by
the scheduled validator `validSignedChainSched` (resp. the lockstep validator
`validSignedChainLock`), both recent at real slot `R`, agree at every height at
least `n` below both tips. Together with `keyrot_loss_agreement`, every
rotation mode inherits Theorem 1 when keys can be lost but not stolen.

THE STATEMENTS OF `sched_loss_agreement` AND `lockstep_loss_agreement` ARE
FIXED. Their exact types are pinned by `Molt/AxiomsRotationLoss.lean`. Prove
them; do not change them.
-/

namespace MoltPetit.Model

/-- **Mode 2 against key loss: timed agreement for the scheduled validator.** -/
theorem sched_loss_agreement {n ρ : Nat} {schedule : Nat → Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hBudget : ExposureBounded n ρ exposed)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SignedDeclared n ops registry B → ∃ r ≤ R, B ∈ log r)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainSched n schedule ops registry sc = true)
    (hVal' : validSignedChainSched n schedule ops registry sc' = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    {tip tip' : Block}
    (hTip : (stripSigs sc).getLast? = some tip)
    (hTip' : (stripSigs sc').getLast? = some tip')
    (hRecent : R ≤ tip.slot + ρ)
    (hRecent' : R ≤ tip'.slot + ρ)
    {h : Nat}
    (hDeep : h + n < (stripSigs sc).length)
    (hDeep' : h + n < (stripSigs sc').length) :
    blockAt? (stripSigs sc) h = blockAt? (stripSigs sc') h := by
  sorry

/-- **Mode 3 against key loss: timed agreement for the lockstep validator.** -/
theorem lockstep_loss_agreement {n ρ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hBudget : ExposureBounded n ρ exposed)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SignedDeclared n ops registry B → ∃ r ≤ R, B ∈ log r)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    {tip tip' : Block}
    (hTip : (stripSigs sc).getLast? = some tip)
    (hTip' : (stripSigs sc').getLast? = some tip')
    (hRecent : R ≤ tip.slot + ρ)
    (hRecent' : R ≤ tip'.slot + ρ)
    {h : Nat}
    (hDeep : h + n < (stripSigs sc).length)
    (hDeep' : h + n < (stripSigs sc').length) :
    blockAt? (stripSigs sc) h = blockAt? (stripSigs sc') h := by
  sorry

end MoltPetit.Model
