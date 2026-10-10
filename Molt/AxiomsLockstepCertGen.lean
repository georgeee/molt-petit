import Spec.Statements
import MoltPetit.Model.KeyStealingLockstepCertGen

/-!
# Pinned statement and axiom audit for per-generation mode-3 certificates

Owned by the reviewer. Do not edit. The statement is pinned in
`Spec/Statements.lean` as `thm_lockstepGen_recent_certified_suffix_agreement` (since Pass 24 it
assumes hash injectivity over formed declared-signed blocks only, review
finding N1); this file checks the development theorem has exactly that type.
-/

example : MoltPaper.thm_lockstepGen_recent_certified_suffix_agreement :=
  @MoltPetit.Model.lockstepGen_recent_certified_suffix_agreement

/-- info: 'MoltPetit.Model.lockstepGen_recent_certified_suffix_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstepGen_recent_certified_suffix_agreement
