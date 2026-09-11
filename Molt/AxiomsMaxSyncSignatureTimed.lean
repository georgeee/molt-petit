import Molt.MaxSyncSignatureTimed

/-!
# Axiom audit — W3b time-aware signature surface, Molt side
-/

/-- info: 'Molt.recentTheftProducersTight_eq_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.recentTheftProducersTight_eq_core

/-- info: 'Molt.max_sync_period_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.max_sync_period_tight

/-- info: 'Molt.recentTheftProducersTight_card_le_one_of_paced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.recentTheftProducersTight_card_le_one_of_paced

/-- info: 'Molt.pacedStolenAt_exceeds_untimed_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.pacedStolenAt_exceeds_untimed_budget

/-- info: 'Molt.pacedStolenAt_safe_under_tight_unsafe_under_untimed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.pacedStolenAt_safe_under_tight_unsafe_under_untimed
