import MoltPetit.TS.Results
import MoltPetit.Model.ExposureCert
import Spec.Statements

/-!
# Timed certified light-client safety for the TypeScript validator

The TypeScript form of `exposure_certified_agreement`: two certified chains the TS
`validateCertifiedChain` accepts, checked by a verifier at real slot `R` within
`n` real slots of both tips, agree at every height at least `n` below both tips,
over every history the two certificates' groundings attest. The signature
assumption is the unforgeability assumption `hbridge` over `TSSigned`.

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
theorem ts_timed_certified_agreement {σ ℓ φ : Nat}
    {n : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block} {R : Nat}
    {sigOps : MoltPetit.SigOps} {Formed : Block → Prop}
    (hexec : SigningExecutionOn (fun B => TSSigned n sigOps B ∧ Formed B) exposed log G)
    (hClock : HonestClockOn (fun B => TSSigned n sigOps B ∧ Formed B) σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    (hbridge : ∀ ⦃B : Block⦄, TSSigned n sigOps B → Formed B → ∃ r ≤ R, B ∈ log r)
    {certOps certOps' : MoltPetit.CertOps}
    (hUnf : ∀ hc : MoltPetit.RawCertificate, certOps.verify hc = true →
      ∃ cl : CertClaim, certOps.claim hc = toTSClaim cl ∧
        GroundedCert n (fun B => TSSigned n sigOps B ∧ Formed B) G cl)
    (hUnf' : ∀ hc : MoltPetit.RawCertificate, certOps'.verify hc = true →
      ∃ cl : CertClaim, certOps'.claim hc = toTSClaim cl ∧
        GroundedCert n (fun B => TSSigned n sigOps B ∧ Formed B) G cl)
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
    (hFormedS : ∀ B ∈ s₁ :: srest, Formed B)
    (hFormedS' : ∀ B ∈ s₁' :: srest', Formed B)
    (hRecent : R ≤ sTip.slot + φ)
    (hRecent' : R ≤ sTip'.slot + φ)
    {cl cl' : CertClaim}
    (hcl : certOps.claim h = toTSClaim cl)
    (hcl' : certOps'.claim h' = toTSClaim cl')
    {c c' : Chain}
    (hc : GroundedHistory n (fun B => TSSigned n sigOps B ∧ Formed B) G cl c)
    (hc' : GroundedHistory n (fun B => TSSigned n sigOps B ∧ Formed B) G cl' c')
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
  have hSigned : ∀ B ∈ s₁ :: srest, TSSigned n sigOps B ∧ Formed B := by
    have hs := ts_sigsOk_signed hsg
    rw [hsc] at hs
    intro B hB
    exact ⟨hs B hB, hFormedS B hB⟩
  have hSigned' : ∀ B ∈ s₁' :: srest', TSSigned n sigOps B ∧ Formed B := by
    have hs := ts_sigsOk_signed hsg'
    rw [hsc'] at hs
    intro B hB
    exact ⟨hs B hB, hFormedS' B hB⟩
  obtain ⟨hLink, hLinks, hDense⟩ := ts_validateSuffix_sound hTipS hsfx
  obtain ⟨hLink', hLinks', hDense'⟩ := ts_validateSuffix_sound hTipS' hsfx'
  exact exposure_certified_agreement_on hn hexec hClock hBudget hL hL'
    (fun B ⟨h1, h2⟩ => hbridge h1 h2) hG hG'
    hTipS hTipS' hLink hLinks hDense hLink' hLinks' hDense' hSigned hSigned'
    hRecent hRecent' hc hc' hDeep hDeep'


theorem lengthOfSigned_toTSSigned (sc : SignedChain MoltPetit.RawSignature) :
    MoltPetit.lengthOfSigned (toTSSigned sc) = (sc.length : Int) := by
  induction sc with
  | nil => rfl
  | cons sb rest ih =>
    rw [show toTSSigned (sb :: rest) =
      .cons sb.block.slot sb.block.height (sb.block.prev.map Int.ofNat)
        sb.block.id sb.block.contentsHash sb.block.keyIndex sb.sig (toTSSigned rest) from rfl]
    dsimp [MoltPetit.lengthOfSigned]
    rw [ih]
    omega

theorem ts_idsOk_formed {sigOps : MoltPetit.SigOps} :
    ∀ (sc : SignedChain MoltPetit.RawSignature) (ps : MoltPetit.RawSignature),
      MoltPetit.idsOk sigOps ps (toTSSigned sc) = true →
      ∀ B ∈ stripSigs sc, TSFormed sigOps B := by
  intro sc
  induction sc with
  | nil =>
    intro ps _ B hB
    cases hB
  | cons sb rest ih =>
    intro ps hids B hB
    rw [show toTSSigned (sb :: rest) =
      .cons sb.block.slot sb.block.height (sb.block.prev.map Int.ofNat)
        sb.block.id sb.block.contentsHash sb.block.keyIndex sb.sig (toTSSigned rest) from rfl] at hids
    dsimp [MoltPetit.idsOk] at hids
    simp only [Bool.and_eq_true, beq_iff_eq] at hids
    obtain ⟨hid, hrest⟩ := hids
    simp only [stripSigs, List.map_cons, List.mem_cons] at hB
    rcases hB with rfl | hB_rest
    · exact ⟨ps, hid⟩
    · exact ih sb.sig hrest B hB_rest

private theorem getD_getLast_cons {g tip : Block} {rest : Chain}
    (f : Block → Nat) (hTip : (g :: rest).getLast? = some tip) :
    ((rest.getLast?.map f).getD (f g)) = f tip := by
  cases rest with
  | nil =>
    simp at hTip
    simp [hTip]
  | cons b2 rest2 =>
    rw [List.getLast?_cons_cons] at hTip
    simp [hTip]

/-- **Deployed certified light-client safety, TypeScript validator.** -/
theorem ts_deployed_agreement : MoltPaper.thm_ts_deployed_agreement := by
  intro σ ℓ φ δ n hn exposed log G R sigOps hexec hClock hBudget hL hL' hbridge
        Δ now now' hφ hNow hNow' certOps certOps' hUnf hUnf' h h' sc sc'
        hval hval' cl cl' hcl hcl' c c' hc hc' k hDeep hDeep'
  dsimp [MoltPetit.validateDeployed] at hval hval'
  simp only [Bool.and_eq_true] at hval hval'
  obtain ⟨⟨⟨hvalCC, hlen⟩, hids⟩, hrec⟩ := hval
  obtain ⟨⟨⟨hvalCC', hlen'⟩, hids'⟩, hrec'⟩ := hval'
  have hlen_int : 0 < MoltPetit.lengthOfSigned (toTSSigned sc) := of_decide_eq_true hlen
  rw [lengthOfSigned_toTSSigned] at hlen_int
  have hlen_sc : 0 < sc.length := by omega
  have hsc_ne : sc ≠ [] := by
    intro h_nil
    subst h_nil
    simp at hlen_sc
  obtain ⟨sb, sbrest, rfl⟩ := List.exists_cons_of_ne_nil hsc_ne
  have hlen'_int : 0 < MoltPetit.lengthOfSigned (toTSSigned sc') := of_decide_eq_true hlen'
  rw [lengthOfSigned_toTSSigned] at hlen'_int
  have hlen'_sc : 0 < sc'.length := by omega
  have hsc'_ne : sc' ≠ [] := by
    intro h_nil
    subst h_nil
    simp at hlen'_sc
  obtain ⟨sb', sbrest', rfl⟩ := List.exists_cons_of_ne_nil hsc'_ne
  let s₁ := sb.block
  let srest := stripSigs sbrest
  let s₁' := sb'.block
  let srest' := stripSigs sbrest'
  have ⟨sTip, hTipS⟩ : ∃ t, (s₁ :: srest).getLast? = some t := by
    cases h : (s₁ :: srest).getLast? with
    | some t => exact ⟨t, rfl⟩
    | none => simp at h
  have ⟨sTip', hTipS'⟩ : ∃ t, (s₁' :: srest').getLast? = some t := by
    cases h : (s₁' :: srest').getLast? with
    | some t => exact ⟨t, rfl⟩
    | none => simp at h
  have hFormedS : ∀ B ∈ s₁ :: srest, TSFormed sigOps B := by
    intro B hB
    exact ts_idsOk_formed (sb :: sbrest) (certOps.tipSig h) hids B hB
  have hFormedS' : ∀ B ∈ s₁' :: srest', TSFormed sigOps B := by
    intro B hB
    exact ts_idsOk_formed (sb' :: sbrest') (certOps'.tipSig h') hids' B hB
  have hRecent : R ≤ sTip.slot + φ := by
    simp only [MoltPetit.recentOk] at hrec
    have hrec_le : now ≤ MoltPetit.tipSlotFrom (certOps.claim h).tipSlot (MoltPetit.stripSigs (toTSSigned (sb :: sbrest))) + Δ :=
      of_decide_eq_true hrec
    rw [show toTSSigned (sb :: sbrest) =
      .cons sb.block.slot sb.block.height (sb.block.prev.map Int.ofNat)
        sb.block.id sb.block.contentsHash sb.block.keyIndex sb.sig (toTSSigned sbrest) from rfl] at hrec_le
    dsimp [MoltPetit.stripSigs, MoltPetit.tipSlotFrom] at hrec_le
    rw [ts_stripSigs, ts_tipSlotFrom, getD_getLast_cons Block.slot hTipS] at hrec_le
    omega
  have hRecent' : R ≤ sTip'.slot + φ := by
    simp only [MoltPetit.recentOk] at hrec'
    have hrec'_le : now' ≤ MoltPetit.tipSlotFrom (certOps'.claim h').tipSlot (MoltPetit.stripSigs (toTSSigned (sb' :: sbrest'))) + Δ :=
      of_decide_eq_true hrec'
    rw [show toTSSigned (sb' :: sbrest') =
      .cons sb'.block.slot sb'.block.height (sb'.block.prev.map Int.ofNat)
        sb'.block.id sb'.block.contentsHash sb'.block.keyIndex sb'.sig (toTSSigned sbrest') from rfl] at hrec'_le
    dsimp [MoltPetit.stripSigs, MoltPetit.tipSlotFrom] at hrec'_le
    rw [ts_stripSigs, ts_tipSlotFrom, getD_getLast_cons Block.slot hTipS'] at hrec'_le
    omega
  exact ts_timed_certified_agreement hn hexec hClock hBudget hL hL' hbridge
    hUnf hUnf' hvalCC hvalCC' rfl rfl hTipS hTipS' hFormedS hFormedS'
    hRecent hRecent' hcl hcl' hc hc' hDeep hDeep'

end MoltPetit.Model
