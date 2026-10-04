import Molt.Results

/-!
# Pinned statements and axiom audit for Pass 23 (admissible signing execution)

Owned by the reviewer. Do not edit. The headline theorems move onto
`SigningExecutionOn`: custody, causal order and collision resistance are
assumed only for blocks a verifier admits, so a block signed by an exposed key
with an unformed id or a dangling parent cannot falsify the hypotheses.
-/

namespace Molt

open MoltPetit.Model (GroundedCert) in
example {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {Signed : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Signed exposed log G)
    (hClock : HonestClockOn Signed σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + faultBudget n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, Signed B → ∃ r ≤ R, B ∈ log r)
    {cl cl' : CertClaim}
    (hcl  : GroundedCert n Signed G cl)
    (hcl' : GroundedCert n Signed G cl')
    {s₁ s₁' : Block} {srest srest' : Chain}
    {sTip sTip' : Block}
    (hTipS  : (s₁  :: srest).getLast?  = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink  : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip'.slot + 1 →
        quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hSigned  : ∀ B ∈ s₁ :: srest,  Signed B)
    (hSigned' : ∀ B ∈ s₁' :: srest', Signed B)
    (hRecent  : R ≤ sTip.slot  + φ)
    (hRecent' : R ≤ sTip'.slot + φ)
    {c c' : Chain}
    (hc  : GroundedHistory n Signed G cl c)
    (hc' : GroundedHistory n Signed G cl' c')
    {h : Nat}
    (hDeep  : h + n < (c ++ s₁ :: srest).length)
    (hDeep' : h + n < (c' ++ s₁' :: srest').length) :
    blockAt? (c ++ s₁ :: srest) h = blockAt? (c' ++ s₁' :: srest') h :=
  timed_light_client_safety hn hexec hClock hBudget hL hL' hbridge hcl hcl' hTipS hTipS'
    hLink hLinks hDense hLink' hLinks' hDense' hSigned hSigned' hRecent hRecent' hc hc'
    hDeep hDeep'

example {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {Adm : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    (hClock : HonestClockOn Adm σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + faultBudget n + σ + 1 ≤ quorum n + ℓ)
    {c : Chain} (hc : MoltPetit.Model.ValidChain n c) (hHead : blockAt? c 0 = some G)
    (hAdm : ∀ B ∈ c, B ≠ G → Adm B)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G)
    {r : Nat} (hr : B ∈ log r) :
    B.slot ≤ r + ℓ :=
  no_early_signing hn hexec hClock hBudget hL hL' hc hHead hAdm hAvail hB hBG hr

end Molt

open MoltPetit.Model in
example {n φ : Nat} (hn : 1 ≤ n)
    {Adm : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    (hBudget : ExposureBoundedEver n φ exposed)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    (hHead : blockAt? c 0 = some G) (hHead' : blockAt? c' 0 = some G)
    (hAdm : ∀ B ∈ c, B ≠ G → Adm B) (hAdm' : ∀ B ∈ c', B ≠ G → Adm B)
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ) (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat} (hDeep : h + n < c.length) (hDeep' : h + n < c'.length) :
    blockAt? c h = blockAt? c' h :=
  exposure_agreement_ever_on hn hexec hBudget hc hc' hHead hHead' hAdm hAdm' hAvail hAvail'
    hTip hTip' hRecent hRecent' hDeep hDeep'

open MoltPetit.Model in
example {n σ φ : Nat} (hn : 1 ≤ n)
    {Adm : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    (hClock : HonestClockOn Adm σ exposed log)
    (hBudget : ExposureBoundedEver n φ exposed)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    (hAdm : ∀ B ∈ c, B ≠ G → Adm B)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G) (hSlot : n - 1 ≤ B.slot)
    {r : Nat} (hr : B ∈ log r) :
    B.slot ≤ r + (n + maxByzantine n + σ + 1 - quorum n) :=
  exposure_no_early_signing_ever_on hn hexec hClock hBudget hc hHead hAdm hAvail hB hBG hSlot hr

/-- info: 'Molt.timed_light_client_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.timed_light_client_safety

/-- info: 'MoltPetit.Model.exposure_agreement_ever_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposure_agreement_ever_on

/-- info: 'MoltPetit.Model.exposure_no_early_signing_ever_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposure_no_early_signing_ever_on
