import MoltPetit.Model.ExposureSafety

/-!
# Pinned statement and axiom audit for light-client safety under exposure

Owned by the reviewer. Do not edit. The `example` fixes the exact type of
`MoltPetit.Model.exposure_agreement`,
`MoltPetit.Model.exposure_no_early_signing` and their `_ever` forms, and the guards fail the build if a
proof is `sorry` or uses any non-classical axiom.
-/

open MoltPetit.Model in
example {n φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hBudget : ExposureBoundedEver n φ exposed)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    (hHead : blockAt? c 0 = some G) (hHead' : blockAt? c' 0 = some G)
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ) (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat} (hDeep : h + n < c.length) (hDeep' : h + n < c'.length) :
    blockAt? c h = blockAt? c' h :=
  exposure_agreement_ever hn hexec hBudget hc hc' hHead hHead' hAvail hAvail'
    hTip hTip' hRecent hRecent' hDeep hDeep'

open MoltPetit.Model in
example {n σ φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hClock : HonestClock σ exposed log)
    (hBudget : ExposureBoundedEver n φ exposed)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G) (hSlot : n - 1 ≤ B.slot)
    {r : Nat} (hr : B ∈ log r) :
    B.slot ≤ r + (n + maxByzantine n + σ + 1 - quorum n) :=
  exposure_no_early_signing_ever hn hexec hClock hBudget hc hHead hAvail hB hBG hSlot hr

open MoltPetit.Model in
example {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hClock : HonestClock σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    (hHead : blockAt? c 0 = some G) (hHead' : blockAt? c' 0 = some G)
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ) (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat} (hDeep : h + n < c.length) (hDeep' : h + n < c'.length) :
    blockAt? c h = blockAt? c' h :=
  exposure_agreement hn hexec hClock hBudget hL hL' hc hc' hHead hHead' hAvail hAvail'
    hTip hTip' hRecent hRecent' hDeep hDeep'

open MoltPetit.Model in
example {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hClock : HonestClock σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G)
    {r : Nat} (hr : B ∈ log r) :
    B.slot ≤ r + ℓ :=
  exposure_no_early_signing hn hexec hClock hBudget hL hL' hc hHead hAvail hB hBG hr

/-- info: 'MoltPetit.Model.exposure_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposure_agreement

/-- info: 'MoltPetit.Model.exposure_no_early_signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposure_no_early_signing

/-- info: 'MoltPetit.Model.exposure_agreement_ever' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposure_agreement_ever

/-- info: 'MoltPetit.Model.exposure_no_early_signing_ever' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposure_no_early_signing_ever
