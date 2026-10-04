import MoltPetit.Model.ExposureSafety

/-!
# Pinned statement and axiom audit for light-client safety under exposure

Owned by the reviewer. Do not edit. The `example` fixes the exact type of
`MoltPetit.Model.exposure_agreement`, and the guard fails the build if the
proof is `sorry` or uses any non-classical axiom.
-/

open MoltPetit.Model in
example {n σ ρ Λ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution n σ exposed log G)
    (hBudget : ExposureBounded n Λ exposed)
    (hΛ : 2 * n + ρ + (maxByzantine n + σ + 1 - quorum n) ≤ Λ)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    (hHead : blockAt? c 0 = some G) (hHead' : blockAt? c' 0 = some G)
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hRecent : R ≤ tip.slot + ρ) (hRecent' : R ≤ tip'.slot + ρ)
    {h : Nat} (hDeep : h + n < c.length) (hDeep' : h + n < c'.length) :
    blockAt? c h = blockAt? c' h :=
  exposure_agreement hn hexec hBudget hΛ hc hc' hHead hHead' hAvail hAvail'
    hTip hTip' hRecent hRecent' hDeep hDeep'

/-- info: 'MoltPetit.Model.exposure_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposure_agreement
