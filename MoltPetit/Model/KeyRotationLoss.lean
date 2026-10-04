import MoltPetit.Model.TimedSafetyCert
import MoltPetit.Model.KeyRotation
import MoltPetit.Model.KeyStealingCert

/-!
# Mode 1 (reactive rotation) against key loss

A seat that loses its delegate key (the key is destroyed; nobody holds it)
rotates by signing its next block under a higher registered version. Loss
changes none of the hypotheses of the timed light-client theorem: a lost key
simply never signs again. So two chains accepted by the mode-1 validator
`validSignedChainK'`, both recent at real slot `R`, agree at every height at
least `n` below both tips: exactly the guarantee of
`timed_tip_ancestor_agreement`, with the signature predicate taken to be
verification under the block's declared key version (`SignedDeclared`).

Nothing here concerns key *theft*: a stolen key is not a lost key, and mode 1
gives no guarantee against theft.

THE STATEMENT OF `keyrot_loss_agreement` IS FIXED. Its exact type is pinned by
`Molt/AxiomsKeyRotationLoss.lean`. Prove it; do not change it.
-/

namespace MoltPetit.Model

/-- Every block of an accepted index-pinned signed chain carries a verifying signature
under its declared registry entry. -/
theorem signedDeclared_of_mem {σ sk pk : Type} {n Δconf : Nat}
    {ops : SigOps σ sk pk} {registry : KeyRegistry pk} {sc : SignedChain σ}
    (h : validSignedChainK' n Δconf ops registry sc = true)
    {B : Block} (hB : B ∈ stripSigs sc) :
    SignedDeclared n ops registry B := by
  obtain ⟨sb, hsbmem, hsbeq⟩ := List.mem_map.mp hB
  obtain ⟨hverify, _⟩ := rotated_key_dead n Δconf ops registry h hsbmem
  exact ⟨sb.sig, by rw [hsbeq] at hverify; exact hverify⟩

/-- **Mode 1 against key loss: timed agreement for the mode-1 validator.** -/
theorem keyrot_loss_agreement {n Δconf : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    (hBudget : ByzantineBounded n bad)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SignedDeclared n ops registry B → ∃ r ≤ R, B ∈ log r)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainK' n Δconf ops registry sc = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    {tip tip' : Block}
    (hTip : (stripSigs sc).getLast? = some tip)
    (hTip' : (stripSigs sc').getLast? = some tip')
    (hRecent : R ≤ tip.slot + n)
    (hRecent' : R ≤ tip'.slot + n)
    {h : Nat}
    (hDeep : h + n < (stripSigs sc).length)
    (hDeep' : h + n < (stripSigs sc').length) :
    blockAt? (stripSigs sc) h = blockAt? (stripSigs sc') h := by
  have hVS : ValidChain n (stripSigs sc) := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal
    exact (validChainK'_sound hVal.2).1
  have hVS' : ValidChain n (stripSigs sc') := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal'
    exact (validChainK'_sound hVal'.2).1
  have hAvail : ∀ B ∈ stripSigs sc, AvailableAt log G B R := by
    intro B hB
    obtain ⟨r, hrR, hrLog⟩ := hbridge (signedDeclared_of_mem hVal hB)
    exact Or.inr ⟨r, hrR, hrLog⟩
  have hAvail' : ∀ B ∈ stripSigs sc', AvailableAt log G B R := by
    intro B hB
    obtain ⟨r, hrR, hrLog⟩ := hbridge (signedDeclared_of_mem hVal' hB)
    exact Or.inr ⟨r, hrR, hrLog⟩
  rcases le_total (stripSigs sc).length (stripSigs sc').length with hLen | hLen'
  · have hLong : n < (stripSigs sc).length := by omega
    have hAgree := timed_tip_ancestor_agreement hn hexec hBudget hVS hVS'
      hHead hHead' hAvail hAvail' hTip hTip' hRecent hRecent' hLen hLong
    set m := (stripSigs sc).length - 1 - n
    have hmLt : m < (stripSigs sc).length := by omega
    have hBm : blockAt? (stripSigs sc) m = some (getElem (stripSigs sc) m hmLt) := by
      unfold blockAt?
      exact List.getElem?_eq_getElem hmLt
    have hBm' : blockAt? (stripSigs sc') m = some (getElem (stripSigs sc) m hmLt) := by
      rw [hAgree, hBm]
    have hmLe : h ≤ m := by omega
    obtain ⟨P, hPat, hPat'⟩ :=
      same_block_same_prefix_timed hexec hVS hVS' hAvail hAvail' hBm hBm' hmLe
    rw [hPat, hPat']
  · have hLong' : n < (stripSigs sc').length := by omega
    have hAgree := timed_tip_ancestor_agreement hn hexec hBudget hVS' hVS
      hHead' hHead hAvail' hAvail hTip' hTip hRecent' hRecent hLen' hLong'
    set m := (stripSigs sc').length - 1 - n
    have hmLt : m < (stripSigs sc').length := by omega
    have hBm' : blockAt? (stripSigs sc') m = some (getElem (stripSigs sc') m hmLt) := by
      unfold blockAt?
      exact List.getElem?_eq_getElem hmLt
    have hBm : blockAt? (stripSigs sc) m = some (getElem (stripSigs sc') m hmLt) := by
      rw [hAgree, hBm']
    have hmLe : h ≤ m := by omega
    obtain ⟨P, hPat', hPat⟩ :=
      same_block_same_prefix_timed hexec hVS' hVS hAvail' hAvail hBm' hBm hmLe
    rw [hPat, hPat']

end MoltPetit.Model
