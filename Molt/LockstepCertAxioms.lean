import Molt.LockstepCert

/-!
# Axiom audit — W1 mode 3 (free-cadence lockstep) certificate form, Molt side

Guards the three `Molt`-namespace aliases `Molt/LockstepCert.lean`
introduces; the core declarations are guarded in
`MoltPetit/Results/LockstepCertAxioms.lean`.
-/

/-- info: 'Molt.lockstep_cert_gen_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.lockstep_cert_gen_pinned

/-- info: 'Molt.lockstep_cert_declares_rosterGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.lockstep_cert_declares_rosterGen

/-- info: 'Molt.lockstep_recent_certified_suffix_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.lockstep_recent_certified_suffix_agreement
