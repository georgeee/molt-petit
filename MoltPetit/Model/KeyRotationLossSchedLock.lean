import MoltPetit.Model.KeyRotationLoss
import MoltPetit.Model.KeyStealingSchedule
import MoltPetit.Model.KeyStealingLockstepGen

/-!
# Modes 2 and 3 against key loss

The mode-2 and mode-3 analogues of `keyrot_loss_agreement`: loss changes none
of the hypotheses of the timed light-client theorem, so two chains accepted by
the scheduled validator `validSignedChainSched` (resp. the lockstep validator
`validSignedChainLock`), both recent at real slot `R`, agree at every height at
least `n` below both tips. Together with `keyrot_loss_agreement`, every
rotation mode inherits Theorem 1 when keys can be lost but not stolen.

THE STATEMENTS OF `sched_loss_agreement` AND `lockstep_loss_agreement` ARE
FIXED. Their exact types are pinned by `Molt/AxiomsRotationLoss.lean`. Prove
them; do not change them.
-/

namespace MoltPetit.Model

/-- **Mode 2 against key loss: timed agreement for the scheduled validator.** -/
theorem sched_loss_agreement {n σ ℓ φ : Nat} {schedule : Nat → Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {Formed : Block → Prop}
    (hexec : SigningExecutionOn (fun B => SignedDeclared n ops registry B ∧ Formed B) exposed log G)
    (hClock : HonestClockOn (fun B => SignedDeclared n ops registry B ∧ Formed B) σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SignedDeclared n ops registry B → Formed B → ∃ r ≤ R, B ∈ log r)
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
    blockAt? (stripSigs sc) h = blockAt? (stripSigs sc') h := by
  have hVS : ValidChain n (stripSigs sc) := validChain_of_validSignedChainSched hVal
  have hVS' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSched hVal'
  have hAdm : ∀ B ∈ stripSigs sc, B ≠ G → SignedDeclared n ops registry B ∧ Formed B :=
    fun B hB hne => ⟨signedDeclared_of_mem_sched hVal hB, hFormed B hB hne⟩
  have hAdm' : ∀ B ∈ stripSigs sc', B ≠ G → SignedDeclared n ops registry B ∧ Formed B :=
    fun B hB hne => ⟨signedDeclared_of_mem_sched hVal' hB, hFormed' B hB hne⟩
  have hAvail : ∀ B ∈ stripSigs sc, AvailableAt log G B R := by
    intro B hB
    by_cases hBG : B = G
    · exact Or.inl hBG
    · obtain ⟨r, hrR, hrLog⟩ := hbridge (signedDeclared_of_mem_sched hVal hB) (hFormed B hB hBG)
      exact Or.inr ⟨r, hrR, hrLog⟩
  have hAvail' : ∀ B ∈ stripSigs sc', AvailableAt log G B R := by
    intro B hB
    by_cases hBG : B = G
    · exact Or.inl hBG
    · obtain ⟨r, hrR, hrLog⟩ := hbridge (signedDeclared_of_mem_sched hVal' hB) (hFormed' B hB hBG)
      exact Or.inr ⟨r, hrR, hrLog⟩
  exact exposure_agreement_on hn hexec hClock hBudget hL hL' hVS hVS'
    hHead hHead' hAdm hAdm' hAvail hAvail' hTip hTip' hRecent hRecent' hDeep hDeep'

/-- **Mode 3 against key loss: timed agreement for the lockstep validator.** -/
theorem lockstep_loss_agreement {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {Formed : Block → Prop}
    (hexec : SigningExecutionOn (fun B => SignedDeclared n ops registry B ∧ Formed B) exposed log G)
    (hClock : HonestClockOn (fun B => SignedDeclared n ops registry B ∧ Formed B) σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {R : Nat}
    (hbridge : ∀ ⦃B : Block⦄, SignedDeclared n ops registry B → Formed B → ∃ r ≤ R, B ∈ log r)
    {sc sc' : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
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
    have h2 := hVal
    rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at h2
    exact (validChainK_sound h2.1.2).1
  have hVS' : ValidChain n (stripSigs sc') := by
    have h2 := hVal'
    rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at h2
    exact (validChainK_sound h2.1.2).1
  have hAdm : ∀ B ∈ stripSigs sc, B ≠ G → SignedDeclared n ops registry B ∧ Formed B :=
    fun B hB hne => ⟨signedDeclared_of_mem_lock hVal hB, hFormed B hB hne⟩
  have hAdm' : ∀ B ∈ stripSigs sc', B ≠ G → SignedDeclared n ops registry B ∧ Formed B :=
    fun B hB hne => ⟨signedDeclared_of_mem_lock hVal' hB, hFormed' B hB hne⟩
  have hAvail : ∀ B ∈ stripSigs sc, AvailableAt log G B R := by
    intro B hB
    by_cases hBG : B = G
    · exact Or.inl hBG
    · obtain ⟨r, hrR, hrLog⟩ := hbridge (signedDeclared_of_mem_lock hVal hB) (hFormed B hB hBG)
      exact Or.inr ⟨r, hrR, hrLog⟩
  have hAvail' : ∀ B ∈ stripSigs sc', AvailableAt log G B R := by
    intro B hB
    by_cases hBG : B = G
    · exact Or.inl hBG
    · obtain ⟨r, hrR, hrLog⟩ := hbridge (signedDeclared_of_mem_lock hVal' hB) (hFormed' B hB hBG)
      exact Or.inr ⟨r, hrR, hrLog⟩
  exact exposure_agreement_on hn hexec hClock hBudget hL hL' hVS hVS'
    hHead hHead' hAdm hAdm' hAvail hAvail' hTip hTip' hRecent hRecent' hDeep hDeep'

end MoltPetit.Model
