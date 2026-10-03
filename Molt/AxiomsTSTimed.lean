import MoltPetit.TS.TimedResults
import MoltPetit.Model.KeyStealingSignatureTimed

/-!
# Pinned statement and axiom audit for the TypeScript timed certified theorem

Owned by the reviewer. Do not edit. The `example` fixes the exact type of
`MoltPetit.Model.ts_timed_certified_agreement`; the guard fails the build if the
proof is incomplete or uses any non-classical axiom.
-/

open MoltPetit.Model in
example
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
    blockAt? (c ++ s₁ :: srest) k = blockAt? (c' ++ s₁' :: srest') k :=
  ts_timed_certified_agreement hn hexec hBudget hbridge hUnf hUnf' hval hval' hsc hsc' hTipS hTipS' hRecent hRecent' hcl hcl' hc hc' hDeep hDeep'

/-- info: 'MoltPetit.Model.ts_timed_certified_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.ts_timed_certified_agreement

open MoltPetit.Model in
example {n Δconf : Nat} (hΔ : 1 ≤ Δconf)
    {c₀ : Chain} {stolenAt : Nat → Nat → Nat → Prop}
    (h : NoTheftBackdating n Δconf c₀ stolenAt)
    {i j r : Nat} (hst : stolenAt i j r) : r = 0 :=
  noTheftBackdating_degenerate hΔ h hst

-- `noTheftBackdating_degenerate` is a trivial lemma whose axiom footprint may be a
-- subset of the standard three; its `sorry`-freedom is enforced by `tools/check.sh`.
