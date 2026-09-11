import Molt.LockstepGen

/-!
# Axiom audit — W5 mode 3 per-generation census, Molt side

Guards the three `Molt`-namespace declarations `Molt/LockstepGen.lean`
introduces; the core declarations are guarded in
`MoltPetit/Results/AxiomsLockstepGen.lean`.
-/

/-- info: 'Molt.lockstep_window_declares_rosterGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.lockstep_window_declares_rosterGen

/-- info: 'Molt.lockstep_client_safety_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.lockstep_client_safety_gen

/-- info: 'Molt.lockstep_client_safety_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.lockstep_client_safety_timed
