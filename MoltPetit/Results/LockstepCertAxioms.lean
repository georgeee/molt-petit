import MoltPetit.Model.KeyStealingLockstepCert

/-!
# Axiom audit — W1 mode 3 (free-cadence lockstep) certificate form

Same discipline as `MoltPetit/Results/Axioms.lean`. Guards the six core
declarations `MoltPetit/Model/KeyStealingLockstepCert.lean` introduces; the
paired `Molt`-namespace aliases are guarded separately in
`Molt/LockstepCertAxioms.lean`, matching the two-file-per-library layout
used throughout `Results/Axioms.lean` / `Molt/Axioms.lean`.
-/

/-- info: 'MoltPetit.Model.groundedCertLock_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.groundedCertLock_history

/-- info: 'MoltPetit.Model.groundedCertLock_suffix_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.groundedCertLock_suffix_history

/-- info: 'MoltPetit.Model.groundedCertLock_gen_of_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.groundedCertLock_gen_of_tail

/-- info: 'MoltPetit.Model.lockstep_cert_gen_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstep_cert_gen_pinned

/-- info: 'MoltPetit.Model.lockstep_cert_declares_rosterGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstep_cert_declares_rosterGen

/-- info: 'MoltPetit.Model.lockstep_recent_certified_suffix_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstep_recent_certified_suffix_agreement
