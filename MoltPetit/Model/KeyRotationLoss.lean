import MoltPetit.Model.ExposureSafety
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
`exposure_agreement`, with the signature predicate taken to be
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
theorem keyrot_loss_agreement {n Δconf σ ℓ φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {Formed : Block → Prop}
    (hexec : SigningExecutionOn (fun B => SignedDeclared n ops registry B ∧ Formed B)
      exposed log G)
    (hClock : HonestClockOn (fun B => SignedDeclared n ops registry B ∧ Formed B) σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SignedDeclared n ops registry B → Formed B → ∃ r ≤ R, B ∈ log r)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainK' n Δconf ops registry sc = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
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
    blockAt? (stripSigs sc) h = blockAt? (stripSigs sc') h := by
  have hVS : ValidChain n (stripSigs sc) := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal
    exact (validChainK'_sound hVal.2).1
  have hVS' : ValidChain n (stripSigs sc') := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal'
    exact (validChainK'_sound hVal'.2).1
  have hAdm : ∀ B ∈ stripSigs sc, B ≠ G → SignedDeclared n ops registry B ∧ Formed B :=
    fun B hB hne => ⟨signedDeclared_of_mem hVal hB, hFormed B hB hne⟩
  have hAdm' : ∀ B ∈ stripSigs sc', B ≠ G → SignedDeclared n ops registry B ∧ Formed B :=
    fun B hB hne => ⟨signedDeclared_of_mem hVal' hB, hFormed' B hB hne⟩
  have hAvail : ∀ B ∈ stripSigs sc, AvailableAt log G B R := by
    intro B hB
    by_cases hBG : B = G
    · exact Or.inl hBG
    · obtain ⟨r, hrR, hrLog⟩ := hbridge (signedDeclared_of_mem hVal hB) (hFormed B hB hBG)
      exact Or.inr ⟨r, hrR, hrLog⟩
  have hAvail' : ∀ B ∈ stripSigs sc', AvailableAt log G B R := by
    intro B hB
    by_cases hBG : B = G
    · exact Or.inl hBG
    · obtain ⟨r, hrR, hrLog⟩ := hbridge (signedDeclared_of_mem hVal' hB) (hFormed' B hB hBG)
      exact Or.inr ⟨r, hrR, hrLog⟩
  exact exposure_agreement_on hn hexec hClock hBudget hL hL' hVS hVS'
    hHead hHead' hAdm hAdm' hAvail hAvail' hTip hTip' hRecent hRecent' hDeep hDeep'

end MoltPetit.Model
