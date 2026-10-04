import MoltPetit.Model.KeyRotationLossSchedLock

/-!
# Pinned statements and axiom audit for modes 2 and 3 against key loss

Owned by the reviewer. Do not edit.
-/

open MoltPetit.Model in
example {n ρ : Nat} {schedule : Nat → Nat} (hn : 1 ≤ n)
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
    blockAt? (stripSigs sc) h = blockAt? (stripSigs sc') h :=
  sched_loss_agreement hn hexec hBudget hbridge hVal hVal' hHead hHead' hTip hTip' hRecent hRecent' hDeep hDeep'

open MoltPetit.Model in
example {n ρ : Nat} (hn : 1 ≤ n)
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
    blockAt? (stripSigs sc) h = blockAt? (stripSigs sc') h :=
  lockstep_loss_agreement hn hexec hBudget hbridge hVal hVal' hHead hHead' hTip hTip' hRecent hRecent' hDeep hDeep'

/-- info: 'MoltPetit.Model.sched_loss_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_loss_agreement

/-- info: 'MoltPetit.Model.lockstep_loss_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstep_loss_agreement
