import Molt.SyncInduction

/-!
# Axiom audit — W4 induction over syncs

Same discipline as `Molt/Axioms.lean`: a guarded `#print axioms` per
headline declaration. New file, not an edit to `Molt/Axioms.lean`, per the
additive-only rule.
-/

-- W4: the abstract engine's invariant — pure structural recursion over
-- List membership, no crypto, no classical reasoning at all.
/-- info: 'Molt.SyncInductionData.invariant' does not depend on any axioms -/
#guard_msgs in
#print axioms Molt.SyncInductionData.invariant

-- W4: the blockAt?-to-membership helper.
/-- info: 'Molt.mem_of_blockAt?' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Molt.mem_of_blockAt?

-- W4: the full-chain instantiation, via Molt.sync_rule_mem.
/-- info: 'Molt.sync_induction_full_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.sync_induction_full_chain
