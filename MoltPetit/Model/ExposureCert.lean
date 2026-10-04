import MoltPetit.Model.ExposureSafety
import MoltPetit.Model.Grounded

/-!
# Certified light-client safety under key exposure

The certificate form of `exposure_agreement`: what a light client
actually holds is a recursive certificate claim plus a suffix of signed blocks.
Every history the certificate's grounding attests, extended by its suffix, agrees
with the other presentation's at every height that is at least `n` below both
tips. No block needs to be *exposed* in either suffix: the conclusion is about the
attested histories themselves.

The signature bridge `hbridge` is EUF-CMA plus causality: a signature the verifier
holds at real slot `R` was produced (logged) at some real slot no later than `R`.

THE STATEMENT OF `exposure_certified_agreement` IS FIXED. Its exact type is pinned by
`Molt/AxiomsExposureCert.lean`. Prove it; do not change it.
-/

namespace MoltPetit.Model

/-- **Timed certified light-client safety.** -/
theorem exposure_certified_agreement {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hClock : HonestClock σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {Signed : Block → Prop} {R : Nat}
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
    blockAt? (c ++ s₁ :: srest) h = blockAt? (c' ++ s₁' :: srest') h := by
  classical
  set full : Chain := c ++ s₁ :: srest with hfull
  set full' : Chain := c' ++ s₁' :: srest' with hfull'
  have hVS : ValidChain n full :=
    validChain_sound (grounded_suffix_history_of hc hTipS hLink hLinks hDense)
  have hVS' : ValidChain n full' :=
    validChain_sound (grounded_suffix_history_of hc' hTipS' hLink' hLinks' hDense')
  have hcLen : 0 < c.length := by
    have := hc.len_eq
    omega
  have hcLen' : 0 < c'.length := by
    have := hc'.len_eq
    omega
  have hHead : blockAt? full 0 = some G := by
    unfold blockAt?
    rw [hfull, List.getElem?_append_left hcLen]
    exact hc.head
  have hHead' : blockAt? full' 0 = some G := by
    unfold blockAt?
    rw [hfull', List.getElem?_append_left hcLen']
    exact hc'.head
  have hTip : full.getLast? = some sTip := by
    rw [hfull, List.getLast?_append, hTipS]
    rfl
  have hTip' : full'.getLast? = some sTip' := by
    rw [hfull', List.getLast?_append, hTipS']
    rfl
  have hAvail : ∀ B ∈ full, AvailableAt log G B R := by
    intro B hB
    rcases List.mem_append.mp (by exact hB) with hBc | hBs
    · rcases hc.signed B hBc with rfl | hSig
      · exact Or.inl rfl
      · obtain ⟨r, hrR, hrLog⟩ := hbridge hSig
        exact Or.inr ⟨r, hrR, hrLog⟩
    · obtain ⟨r, hrR, hrLog⟩ := hbridge (hSigned B hBs)
      exact Or.inr ⟨r, hrR, hrLog⟩
  have hAvail' : ∀ B ∈ full', AvailableAt log G B R := by
    intro B hB
    rcases List.mem_append.mp (by exact hB) with hBc' | hBs'
    · rcases hc'.signed B hBc' with rfl | hSig
      · exact Or.inl rfl
      · obtain ⟨r, hrR, hrLog⟩ := hbridge hSig
        exact Or.inr ⟨r, hrR, hrLog⟩
    · obtain ⟨r, hrR, hrLog⟩ := hbridge (hSigned' B hBs')
      exact Or.inr ⟨r, hrR, hrLog⟩
  exact exposure_agreement hn hexec hClock hBudget hL hL' hVS hVS'
    hHead hHead' hAvail hAvail' hTip hTip' hRecent hRecent' hDeep hDeep'

end MoltPetit.Model
