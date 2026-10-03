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

/-- `toTSChain` is injective. -/
theorem toTSChain_injective : Function.Injective toTSChain := by
  intro c1
  induction c1 with
  | nil =>
    intro c2 h
    cases c2 with
    | nil => rfl
    | cons b rest => cases h
  | cons b1 rest1 ih =>
    intro c2 h
    cases c2 with
    | nil => cases h
    | cons b2 rest2 =>
      injection h with hslot hheight hprev hid hcontents hkey hrest
      have hrest_eq : rest1 = rest2 := ih hrest
      have hslot_eq : b1.slot = b2.slot := by exact_mod_cast hslot
      have hheight_eq : b1.height = b2.height := by exact_mod_cast hheight
      have hid_eq : b1.id = b2.id := by exact_mod_cast hid
      have hcontents_eq : b1.contentsHash = b2.contentsHash := by exact_mod_cast hcontents
      have hkey_eq : b1.keyIndex = b2.keyIndex := by exact_mod_cast hkey
      have hprev_eq : b1.prev = b2.prev := by
        match h1 : b1.prev, h2 : b2.prev with
        | none, none => rfl
        | none, some _ => rw [h1, h2] at hprev; contradiction
        | some _, none => rw [h1, h2] at hprev; contradiction
        | some p1, some p2 =>
          rw [h1, h2] at hprev
          injection hprev with hp
          injection hp with hp'
          subst hp'; rfl
      cases b1; cases b2
      dsimp at hslot_eq hheight_eq hid_eq hcontents_eq hkey_eq hprev_eq
      subst hslot_eq hheight_eq hid_eq hcontents_eq hkey_eq hprev_eq hrest_eq
      rfl

/-- `toTSClaim` is injective. -/
theorem toTSClaim_injective : Function.Injective toTSClaim := by
  intro cl1 cl2 h
  match cl1, cl2 with
  | ⟨id1, slot1, h1, tail1⟩, ⟨id2, slot2, h2, tail2⟩ =>
    simp only [toTSClaim, MoltPetit.CertClaim.mk.injEq] at h
    obtain ⟨hId, hSlot, hHeight, hTail⟩ := h
    have hTail' := toTSChain_injective hTail
    have hId' : id1 = id2 := by exact_mod_cast hId
    have hSlot' : slot1 = slot2 := by exact_mod_cast hSlot
    have hHeight' : h1 = h2 := by exact_mod_cast hHeight
    subst hId' hSlot' hHeight' hTail'
    rfl

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
  obtain ⟨hcv, hsg, hsfx⟩ := ts_validateCertifiedChain_sound hval
  obtain ⟨hcv', hsg', hsfx'⟩ := ts_validateCertifiedChain_sound hval'
  rw [hsc] at hsfx
  rw [hsc'] at hsfx'
  obtain ⟨cl0, hclEq, hG⟩ := hUnf h hcv
  obtain ⟨cl0', hclEq', hG'⟩ := hUnf' h' hcv'
  have hcl0_eq : cl0 = cl := toTSClaim_injective (hclEq.symm.trans hcl)
  subst hcl0_eq
  have hcl0'_eq : cl0' = cl' := toTSClaim_injective (hclEq'.symm.trans hcl')
  subst hcl0'_eq
  rw [hcl] at hsfx
  rw [hcl'] at hsfx'
  have hSigned : ∀ B ∈ s₁ :: srest, TSSigned n sigOps B := by
    have hs := ts_sigsOk_signed hsg
    rw [hsc] at hs
    exact hs
  have hSigned' : ∀ B ∈ s₁' :: srest', TSSigned n sigOps B := by
    have hs := ts_sigsOk_signed hsg'
    rw [hsc'] at hs
    exact hs
  obtain ⟨hLink, hLinks, hDense⟩ := ts_validateSuffix_sound hTipS hsfx
  obtain ⟨hLink', hLinks', hDense'⟩ := ts_validateSuffix_sound hTipS' hsfx'
  exact timed_certified_agreement hn hexec hBudget hbridge hG hG'
    hTipS hTipS' hLink hLinks hDense hLink' hLinks' hDense' hSigned hSigned'
    hRecent hRecent' hc hc' hDeep hDeep'

end MoltPetit.Model
