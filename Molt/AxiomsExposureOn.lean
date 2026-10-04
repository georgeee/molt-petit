import MoltPetit.Model.SchedExposure

/-!
# Pinned statements and axiom audit for the admissibility-restricted core (Pass 22)

Owned by the reviewer. Do not edit. Each `example` fixes the exact type of the
named theorem, and each guard fails the build if the proof is incomplete or uses
any non-classical axiom.
-/

open MoltPetit.Model in
example {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {Adm : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    (hClock : HonestClockOn Adm σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    (hAdm : ∀ B ∈ c, B ≠ G → Adm B)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G)
    {r : Nat} (hr : B ∈ log r) :
    B.slot ≤ r + ℓ :=
  exposure_no_early_signing_on hn hexec hClock hBudget hL hL' hc hHead hAdm hAvail hB hBG hr

/-- info: 'MoltPetit.Model.exposure_no_early_signing_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposure_no_early_signing_on

open MoltPetit.Model in
example {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {Adm : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    (hClock : HonestClockOn Adm σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
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
  exposure_agreement_on hn hexec hClock hBudget hL hL'
    hc hc' hHead hHead' hAdm hAdm' hAvail hAvail' hTip hTip' hRecent hRecent' hDeep hDeep'

/-- info: 'MoltPetit.Model.exposure_agreement_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposure_agreement_on

open MoltPetit.Model in
example {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {Signed : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Signed exposed log G)
    (hClock : HonestClockOn Signed σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, Signed B → ∃ r ≤ R, B ∈ log r)
    {cl cl' : CertClaim}
    (hcl : GroundedCert n Signed G cl)
    (hcl' : GroundedCert n Signed G cl')
    {s₁ s₁' : Block} {srest srest' : Chain}
    {sTip sTip' : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip'.slot + 1 →
        quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hSigned : ∀ B ∈ s₁ :: srest, Signed B)
    (hSigned' : ∀ B ∈ s₁' :: srest', Signed B)
    (hRecent : R ≤ sTip.slot + φ)
    (hRecent' : R ≤ sTip'.slot + φ)
    {c c' : Chain}
    (hc : GroundedHistory n Signed G cl c)
    (hc' : GroundedHistory n Signed G cl' c')
    {h : Nat}
    (hDeep : h + n < (c ++ s₁ :: srest).length)
    (hDeep' : h + n < (c' ++ s₁' :: srest').length) :
    blockAt? (c ++ s₁ :: srest) h = blockAt? (c' ++ s₁' :: srest') h :=
  exposure_certified_agreement_on hn hexec hClock hBudget hL hL' hbridge hcl hcl' hTipS hTipS'
    hLink hLinks hDense hLink' hLinks' hDense' hSigned hSigned' hRecent hRecent' hc hc' hDeep hDeep'

/-- info: 'MoltPetit.Model.exposure_certified_agreement_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposure_certified_agreement_on

open MoltPetit.Model in
example {n σ ℓ φ : Nat} {schedule : Nat → Nat} (hn : 1 ≤ n)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {Controlled : Nat → Nat → Prop} {Stolen : Nat → Nat → Nat → Prop}
    {log : TimedLog} {G : Block} {Formed : Block → Prop}
    (hexec : SigningExecutionOn (fun B => SchedAdmissible n schedule ops registry B ∧ Formed B)
      (schedExposed n schedule Controlled Stolen) log G)
    (hClock : HonestClockOn (fun B => SchedAdmissible n schedule ops registry B ∧ Formed B) σ
      (schedExposed n schedule Controlled Stolen) log)
    (hBudget : ExposureBounded n ℓ φ (schedExposed n schedule Controlled Stolen))
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SchedAdmissible n schedule ops registry B → Formed B →
      ∃ r ≤ R, B ∈ log r)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainSched n schedule ops registry sc = true)
    (hVal' : validSignedChainSched n schedule ops registry sc' = true)
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
  sched_exposure_agreement hn hexec hClock hBudget hL hL'
    hbridge hVal hVal' hHead hHead' hFormed hFormed' hTip hTip' hRecent hRecent' hDeep hDeep'

/-- info: 'MoltPetit.Model.sched_exposure_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_exposure_agreement

open MoltPetit.Model in
example {n σ ℓ φ : Nat} {schedule : Nat → Nat}
    (hn : 1 ≤ n)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {Controlled : Nat → Nat → Prop} {Stolen : Nat → Nat → Nat → Prop}
    {log : TimedLog} {G : Block} {Formed : Block → Prop}
    (hexec : SigningExecutionOn (fun B => SchedAdmissible n schedule ops registry B ∧ Formed B)
      (schedExposed n schedule Controlled Stolen) log G)
    (hClock : HonestClockOn (fun B => SchedAdmissible n schedule ops registry B ∧ Formed B) σ
      (schedExposed n schedule Controlled Stolen) log)
    (hBudget : ExposureBounded n ℓ φ (schedExposed n schedule Controlled Stolen))
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SchedAdmissible n schedule ops registry B → Formed B →
      ∃ r ≤ R, B ∈ log r)
    {cl cl' : CertClaim}
    (hcl : GroundedCertSched n schedule (fun B => SignedDeclared n ops registry B ∧ Formed B) G cl)
    (hcl' : GroundedCertSched n schedule (fun B => SignedDeclared n ops registry B ∧ Formed B) G cl')
    {s₁ s₁' : Block} {srest srest' : Chain}
    {sTip sTip' : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip'.slot + 1 →
        quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hSigned : ∀ B ∈ s₁ :: srest, SchedAdmissible n schedule ops registry B ∧ Formed B)
    (hSigned' : ∀ B ∈ s₁' :: srest', SchedAdmissible n schedule ops registry B ∧ Formed B)
    (hRecent : R ≤ sTip.slot + φ)
    (hRecent' : R ≤ sTip'.slot + φ)
    {c c' : Chain}
    (hc : GroundedHistorySched n schedule (fun B => SignedDeclared n ops registry B ∧ Formed B) G cl c)
    (hc' : GroundedHistorySched n schedule (fun B => SignedDeclared n ops registry B ∧ Formed B) G cl' c')
    {h : Nat}
    (hDeep : h + n < (c ++ s₁ :: srest).length)
    (hDeep' : h + n < (c' ++ s₁' :: srest').length) :
    blockAt? (c ++ s₁ :: srest) h = blockAt? (c' ++ s₁' :: srest') h :=
  sched_exposure_certified_agreement hn hexec hClock hBudget hL hL' hbridge hcl hcl' hTipS hTipS'
    hLink hLinks hDense hLink' hLinks' hDense' hSigned hSigned' hRecent hRecent' hc hc' hDeep hDeep'

/-- info: 'MoltPetit.Model.sched_exposure_certified_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_exposure_certified_agreement
