import MoltPetit.Model.KeyStealingSignatureTimed

/-!
# Axiom audit — W3b time-aware signature surface (mode 1)

Same discipline as `MoltPetit/Results/Axioms.lean`.
-/

/-- info: 'MoltPetit.Model.exposedProducers_subset_recentTheftTight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposedProducers_subset_recentTheftTight

/-- info: 'MoltPetit.Model.budget_of_reaction_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.budget_of_reaction_tight

/-- info: 'MoltPetit.Model.anchored_budget_of_reaction_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.anchored_budget_of_reaction_tight
