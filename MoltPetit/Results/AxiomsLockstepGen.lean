import MoltPetit.Model.KeyStealingWindowCore
import MoltPetit.Model.KeyStealingLockstepGen
import MoltPetit.Model.KeyStealingLockstepTimed

/-!
# Axiom audit — W5 mode 3 per-generation census (D1′-full)

Same discipline as `MoltPetit/Results/Axioms.lean`. Guards the headline
declarations of `KeyStealingLockstepGen.lean` and `KeyStealingLockstepTimed.
lean`; the reusable engine (`window_shared_prefix`) from `KeyStealingWindow
Core.lean` is guarded here too since it has no other home. Intermediate
plumbing (`chain_length_le_tip_slot`, `honestSlotsUniqueOn_of_unique`,
`horizon_shared_prefix_of_window`, `LockstepPackageGen.alignedBudget`,
`lockstepGen_shared_prefix_deep`, `stolen_generation_was_live`,
`LockstepPackageTimed.toGen`) is not separately guarded, matching the
existing convention of guarding headline/consumer results, not every
private-scope-adjacent helper.
-/

/-- info: 'MoltPetit.Model.window_shared_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.window_shared_prefix

/-- info: 'MoltPetit.Model.lockstep_aligned_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstep_aligned_budget

/-- info: 'MoltPetit.Model.LockstepPackage.toGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.LockstepPackage.toGen

/-- info: 'MoltPetit.Model.lockstep_window_declares_rosterGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstep_window_declares_rosterGen

/-- info: 'MoltPetit.Model.honestSlotsUniqueOn_lockstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.honestSlotsUniqueOn_lockstep

/-- info: 'MoltPetit.Model.lockstepGen_shared_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstepGen_shared_prefix

/-- info: 'MoltPetit.Model.lockstepGen_recent_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstepGen_recent_tip_ancestor_agreement

/-- info: 'MoltPetit.Model.lockstepGen_recent_tip_ancestor_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstepGen_recent_tip_ancestor_mem

/-- info: 'MoltPetit.Model.lockstepGen_recent_genesis_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstepGen_recent_genesis_agreement

/-- info: 'MoltPetit.Model.theft_in_era_lock' does not depend on any axioms -/
#guard_msgs in
#print axioms MoltPetit.Model.theft_in_era_lock

/-- info: 'MoltPetit.Model.noPrematureTheftLock_iff_flagship' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MoltPetit.Model.noPrematureTheftLock_iff_flagship

/-- info: 'MoltPetit.Model.erasureTimedLock_iff_flagship' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.erasureTimedLock_iff_flagship

/-- info: 'MoltPetit.Model.genBound_of_preRetirementBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.genBound_of_preRetirementBound

/-- info: 'MoltPetit.Model.lockstepTimed_recent_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstepTimed_recent_tip_ancestor_agreement

/-- info: 'MoltPetit.Model.lockstepTimed_recent_tip_ancestor_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstepTimed_recent_tip_ancestor_mem
