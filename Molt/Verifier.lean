import Molt.Protocol
import Spec.Reference

/-!
# The rules a node runs (paper §4)

The three operations of a node's life — validate, produce, select — over
certified chains, plus the signature layer they sit on. Fresh presentation;
bridges to the `MoltPetit.Model` originals at the bottom.

The interface *types* (`SigOps`, `CertOps`, …) are re-exported, not
re-declared, for the same reason as `Block`: theorems transport only across
shared types.
-/

namespace Molt

/-! ## The signature layer -/

/-- A signed chain is valid: all signatures verify and the stripped chain
passes `validChain`. -/
def validSignedChain {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk)
    (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChain n (stripSigs sc)

/-! ## Certified chains -/

/-! ## Bridge to the core development -/

theorem stripSigs_eq_core {σ : Type} :
    (stripSigs (σ := σ)) = MoltPetit.Model.stripSigs := rfl
theorem sigOk_eq_core {σ sk pk : Type} :
    (sigOk (σ := σ) (sk := sk) (pk := pk)) = MoltPetit.Model.sigOk := rfl
theorem sigsOk_eq_core {σ sk pk : Type} :
    (sigsOk (σ := σ) (sk := sk) (pk := pk)) = MoltPetit.Model.sigsOk := rfl

theorem validSignedChain_eq_core {σ sk pk : Type} :
    (validSignedChain (σ := σ) (sk := sk) (pk := pk))
      = MoltPetit.Model.validSignedChain := by
  funext n ops registry sc
  simp only [validSignedChain, MoltPetit.Model.validSignedChain,
    sigsOk_eq_core, validChain_eq_core, stripSigs_eq_core]

theorem tipHeight_eq_core {α σ : Type} :
    (tipHeight (α := α) (σ := σ)) = MoltPetit.Model.certTipHeight := rfl

theorem validSuffix_eq_core {α σ sk pk : Type} :
    (validSuffix (α := α) (σ := σ) (sk := sk) (pk := pk))
      = MoltPetit.Model.validateSuffix := by
  funext n sigOps registry certOps cert suffix
  simp only [validSuffix, MoltPetit.Model.validateSuffix,
    sigsOk_eq_core, stripSigs_eq_core]
  rcases hc : MoltPetit.Model.stripSigs suffix with _ | ⟨first, rest⟩
  · simp only [hc]
  · simp only [hc]
    rcases hg : (first :: rest).getLast? with _ | t
    · simp only [hg, linksOk_eq_core]
    · simp only [hg, linksOk_eq_core, windowDense_eq_core]

theorem validCertifiedChain_eq_core {α σ sk pk : Type} :
    (validCertifiedChain (α := α) (σ := σ) (sk := sk) (pk := pk))
      = MoltPetit.Model.validateCertifiedChain := by
  funext n sigOps registry certOps cc
  simp only [validCertifiedChain, MoltPetit.Model.validateCertifiedChain,
    validSuffix_eq_core]

theorem produceBlock?_eq_core {α σ sk pk : Type} :
    (produceBlock? (α := α) (σ := σ) (sk := sk) (pk := pk))
      = MoltPetit.Model.produceBlockCert? := by
  funext n me slot newId contentsHash keyIndex sigOps registry myKey certOps cc
  unfold produceBlock? MoltPetit.Model.produceBlockCert?
  simp only [producer_eq_core, validSuffix_eq_core]

theorem selectChain_eq_core {α σ sk pk : Type} :
    (selectChain (α := α) (σ := σ) (sk := sk) (pk := pk))
      = MoltPetit.Model.selectCertifiedChain := by
  funext n sigOps registry certOps current candidate
  simp only [selectChain, MoltPetit.Model.selectCertifiedChain,
    validCertifiedChain_eq_core, tipHeight_eq_core]
  rfl

end Molt
