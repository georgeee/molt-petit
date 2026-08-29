import Molt.Results
import Molt.Rotation
import Molt.ClientRule
import Molt.MaxSync
import Molt.Liveness

/-!
# Axiom audit for the `Molt` headline theorems

Same discipline as `MoltPetit/Results/Axioms.lean`: a guarded
`#print axioms` per headline theorem, so `lake build Molt` fails if any
theorem ever picks up an axiom beyond the three classical ones. Extend
this file with every new headline theorem.
-/

-- Theorem 1: light-client safety (paper §6.1).
/-- info: 'Molt.light_client_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.light_client_safety

-- Theorem 2: forged chains take real time (paper §6.2).
/-- info: 'Molt.forged_time_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.forged_time_bound

-- Loss-only collapse, mode-1 census (paper mode 0).
/-- info: 'Molt.badKeyrot_lossOnly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Molt.badKeyrot_lossOnly

-- Loss-only collapse, mode-2/3 census (paper mode 0).
/-- info: 'Molt.badSched_lossOnly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Molt.badSched_lossOnly

-- Loss-only collapse, mode-3 exposure census (paper mode 0).
/-- info: 'Molt.exposedSched_lossOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.exposedSched_lossOnly

-- Theorem 3: the client refresh rule (paper §6.3, mode 1).
/-- info: 'Molt.client_refresh_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.client_refresh_rule

-- The deep anchor is nearby (paper §6.3, mode 1).
/-- info: 'Molt.deep_block_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.deep_block_span

-- Theorem 3, single-constant form: sync every n slots (paper §6.3, mode 1).
/-- info: 'Molt.stay_recent_client_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.stay_recent_client_safe

-- Theorem 3, final form: confirmation depth fixed at n, no Δconf anywhere.
/-- info: 'Molt.sync_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.sync_rule

-- Theorem 3, membership form: unequal tip heights (paper §6.3, mode 1).
/-- info: 'Molt.sync_rule_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.sync_rule_mem

-- The pinning theorem, the mode-3 route (paper §6.3).
/-- info: 'Molt.lockstep_declares_rosterGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.lockstep_declares_rosterGen

-- Retired-generation staleness (paper §6.3, mode 2).
/-- info: 'Molt.sched_oldkey_fork_stale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Molt.sched_oldkey_fork_stale

-- The maximum sync period, parametric in F (paper §6.3, mode 1).
/-- info: 'Molt.max_sync_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.max_sync_period

-- Seat-slot construction used by the census lemmas (paper §6.3, mode 1).
/-- info: 'Molt.producer_slot_in_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Molt.producer_slot_in_window

-- Floors never fall as the viewpoint advances (paper §6.3, mode 1).
/-- info: 'Molt.inForce_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Molt.inForce_mono

-- The census accumulates: healing never subtracts (paper §6.3, mode 1).
/-- info: 'Molt.census_accumulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.census_accumulates

-- A theft at-or-after a window charges the window (paper §6.3, mode 1).
/-- info: 'Molt.census_accumulates_later_thefts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.census_accumulates_later_thefts

-- Beyond the bound there is no budget to instantiate (paper §6.3, mode 1).
/-- info: 'Molt.no_budget_beyond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.no_budget_beyond

-- Certificate-level forms, modes 1-2 (paper §4 item 5, §6.3).
/-- info: 'Molt.keyrot_recent_certified_suffix_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.keyrot_recent_certified_suffix_agreement

/-- info: 'Molt.sched_recent_certified_suffix_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.sched_recent_certified_suffix_agreement

-- Mode 2, horizon-scoped and membership forms; the chaining lemma.
/-- info: 'Molt.sched_recent_tip_ancestor_agreement_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.sched_recent_tip_ancestor_agreement_horizon

/-- info: 'Molt.sched_recent_tip_ancestor_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.sched_recent_tip_ancestor_mem

/-- info: 'Molt.sched_recent_tip_ancestor_mem_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.sched_recent_tip_ancestor_mem_horizon

/-- info: 'Molt.lockstep_recent_tip_ancestor_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.lockstep_recent_tip_ancestor_mem

/-- info: 'Molt.same_block_same_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Molt.same_block_same_prefix

-- Theorem 4: scheduled safety (paper §6.3, mode 2).
/-- info: 'Molt.scheduled_client_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.scheduled_client_safety

-- Theorem 5: lockstep safety (paper §6.3, mode 3).
/-- info: 'Molt.lockstep_client_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.lockstep_client_safety

-- The appendix theorem and its independence witness.
/-- info: 'Molt.sigUnforgeableRecent_of_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.sigUnforgeableRecent_of_timed

/-- info: 'Molt.noBackdate_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Molt.noBackdate_independent

-- Theorem 6: liveness (paper §6.4).
/-- info: 'Molt.production_liveness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.production_liveness

/-- info: 'Molt.global_liveness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.global_liveness
