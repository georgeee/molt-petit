import Spec.Statements
import MoltPetit.Model.KeyStealingScheduleCertHorizon

/-!
# Pinned statement and axiom audit for horizon-scoped mode-2 certificates

Owned by the reviewer. Do not edit. The statement is pinned in
`Spec/Statements.lean` as `thm_sched_recent_certified_suffix_agreement_horizon` (since Pass 24 it
assumes hash injectivity over formed declared-signed blocks only, review
finding N1); this file checks the development theorem has exactly that type.
-/

example : MoltPaper.thm_sched_recent_certified_suffix_agreement_horizon :=
  @MoltPetit.Model.sched_recent_certified_suffix_agreement_horizon

/-- info: 'MoltPetit.Model.sched_recent_certified_suffix_agreement_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_recent_certified_suffix_agreement_horizon
