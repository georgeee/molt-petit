import MoltPetit.Model.KeyRotationLoss

/-!
# Pinned statement and axiom audit for mode 1 against key loss

Owned by the reviewer. Do not edit.
-/

open MoltPetit.Model in
example {n Δconf σ ℓ φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {Formed : Block → Prop}
    (hexec : SigningExecutionOn (fun B => SignedDeclared n ops registry B ∧ Formed B) exposed log G)
    (hClock : HonestClockOn (fun B => SignedDeclared n ops registry B ∧ Formed B) σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SignedDeclared n ops registry B → Formed B → ∃ r ≤ R, B ∈ log r)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainK' n Δconf ops registry sc = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    (hFormed : ∀ B ∈ stripSigs sc, B ≠ G → Formed B)
    (hFormed' : ∀ B ∈ stripSigs sc', B ≠ G → Formed B)
    {tip tip' : Block}
    (hTip : (stripSigs sc).getLast? = some tip)
    (hTip' : (stripSigs sc').getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ)
    (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat}
    (hDeep : h + n < (stripSigs sc).length)
    (hDeep' : h + n < (stripSigs sc').length) :
    blockAt? (stripSigs sc) h = blockAt? (stripSigs sc') h :=
  keyrot_loss_agreement hn hexec hClock hBudget hL hL' hbridge hVal hVal' hHead hHead' hFormed hFormed' hTip hTip' hRecent hRecent' hDeep hDeep'

/-- info: 'MoltPetit.Model.keyrot_loss_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_loss_agreement
