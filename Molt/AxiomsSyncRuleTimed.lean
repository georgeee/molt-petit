import Molt.SyncRuleTimed

/-!
# Axiom audit — W3a timed theft layer (Molt re-presentation)

Same discipline as `Molt/Axioms.lean`: a guarded `#print axioms` per new
Molt-namespace declaration. New file, not an edit to `Molt/Axioms.lean`,
per the additive-only rule.
-/

/-- info: 'Molt.recentTheftProducersK_eq_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.recentTheftProducersK_eq_core

/-- info: 'Molt.client_refresh_rule_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.client_refresh_rule_timed

/-- info: 'Molt.sync_rule_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.sync_rule_timed

/-- info: 'Molt.sync_rule_mem_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.sync_rule_mem_timed

/-- info: 'Molt.max_sync_period_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.max_sync_period_timed
