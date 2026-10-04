import MoltPetit.Model.ExposureSafety

/-!
# Pinned statement and axiom audit for light-client safety under exposure

Owned by the reviewer. Do not edit. The `example` fixes the exact type of
`MoltPetit.Model.exposure_agreement` and
`MoltPetit.Model.exposure_no_early_signing`, and the guards fail the build if a
proof is `sorry` or uses any non-classical axiom.
-/

open MoltPetit.Model in
example {n ρ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hBudget : ExposureBounded n ρ exposed)
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
  exposure_agreement hn hexec hBudget hc hc' hHead hHead' hAvail hAvail'
    hTip hTip' hRecent hRecent' hDeep hDeep'

open MoltPetit.Model in
example {n σ ρ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hClock : HonestClock σ exposed log)
    (hBudget : ExposureBounded n ρ exposed)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G) (hSlot : n - 1 ≤ B.slot)
    {r : Nat} (hr : B ∈ log r) :
    B.slot ≤ r + (n + maxByzantine n + σ + 1 - quorum n) :=
  exposure_no_early_signing hn hexec hClock hBudget hc hHead hAvail hB hBG hSlot hr

/-- info: 'MoltPetit.Model.exposure_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposure_agreement

/-- info: 'MoltPetit.Model.exposure_no_early_signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposure_no_early_signing
