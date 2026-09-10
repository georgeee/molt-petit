import MoltPetit.Model.KeyStealingTimed

/-!
# Axiom audit — W3a timed theft layer for mode 1

Same discipline as `MoltPetit/Results/Axioms.lean`: a guarded `#print axioms`
per headline theorem. New file, not an edit to `MoltPetit/Results/Axioms.lean`,
per the additive-only rule.
-/

/-- info: 'MoltPetit.Model.exposedProducers_subset_recentTheftK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposedProducers_subset_recentTheftK

/-- info: 'MoltPetit.Model.budget_of_reaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.budget_of_reaction

/-- info: 'MoltPetit.Model.anchored_budget_of_reaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.anchored_budget_of_reaction
