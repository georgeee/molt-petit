import MoltPetit.TS.Results
import MoltPetit.Model.TimedSafetyCert

/-!
# Timed certified light-client safety for the TypeScript validator

The TypeScript form of `timed_certified_agreement`: two certified chains the TS
`validateCertifiedChain` accepts, checked by a verifier at real slot `R` within
`n` real slots of both tips, agree at every height at least `n` below both tips,
over every history the two certificates' groundings attest. The signature
assumption is the timed bridge `hbridge` (EUF-CMA plus causality) over `TSSigned`.

THE STATEMENT OF `ts_timed_certified_agreement` IS FIXED. Its exact type is
pinned by `Molt/AxiomsTSTimed.lean`. Prove it; do not change it.
-/

namespace MoltPetit.Model

/-- **Timed certified light-client safety, TypeScript validator.** -/
theorem ts_timed_certified_agreement
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block} {R : Nat}
    {sigOps : MoltPetit.SigOps}
    (hexec : TimedExecution n bad log G)
    (hBudget : ByzantineBounded n bad)
    (hbridge : ∀ ⦃B : Block⦄, TSSigned n sigOps B → ∃ r ≤ R, B ∈ log r)
    {certOps certOps' : MoltPetit.CertOps}
    (hUnf : ∀ hc : MoltPetit.RawCertificate, certOps.verify hc = true →
      ∃ cl : CertClaim, certOps.claim hc = toTSClaim cl ∧
        GroundedCert n (TSSigned n sigOps) G cl)
    (hUnf' : ∀ hc : MoltPetit.RawCertificate, certOps'.verify hc = true →
      ∃ cl : CertClaim, certOps'.claim hc = toTSClaim cl ∧
        GroundedCert n (TSSigned n sigOps) G cl)
    {h h' : MoltPetit.RawCertificate} {sc sc' : SignedChain MoltPetit.RawSignature}
    (hval : MoltPetit.validateCertifiedChain n sigOps certOps
              (.cc h (toTSSigned sc)) = true)
    (hval' : MoltPetit.validateCertifiedChain n sigOps certOps'
              (.cc h' (toTSSigned sc')) = true)
    {s₁ s₁' : Block} {srest srest' : Chain}
    (hsc : stripSigs sc = s₁ :: srest)
    (hsc' : stripSigs sc' = s₁' :: srest')
    {sTip sTip' : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hRecent : R ≤ sTip.slot + n)
    (hRecent' : R ≤ sTip'.slot + n)
    {cl cl' : CertClaim}
    (hcl : certOps.claim h = toTSClaim cl)
    (hcl' : certOps'.claim h' = toTSClaim cl')
    {c c' : Chain}
    (hc : GroundedHistory n (TSSigned n sigOps) G cl c)
    (hc' : GroundedHistory n (TSSigned n sigOps) G cl' c')
    {k : Nat}
    (hDeep : k + n < (c ++ s₁ :: srest).length)
    (hDeep' : k + n < (c' ++ s₁' :: srest').length) :
    blockAt? (c ++ s₁ :: srest) k = blockAt? (c' ++ s₁' :: srest') k := by
  sorry

end MoltPetit.Model
