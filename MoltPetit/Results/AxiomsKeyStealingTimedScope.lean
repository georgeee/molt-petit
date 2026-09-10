import MoltPetit.Model.KeyStealingTimedScope

/-!
# Axiom audit — W6 no-back-dating obstruction witnesses

Same discipline as `MoltPetit/Results/Axioms.lean`: a guarded `#print axioms`
per headline theorem, so `lake build MoltPetit` fails if either theorem ever
picks up an axiom beyond the three classical ones — or, here, any axiom at
all, since both are closed, fully computable Nat/List/Prop existentials.
This is a new file, not an edit to `MoltPetit/Results/Axioms.lean`, per the
additive-only rule.
-/

-- W6: mode 2/3 single-key-safe-not-enough witness
/-- info: 'MoltPetit.Model.badSched_single_key_safe_not_enough' does not depend on any axioms -/
#guard_msgs in
#print axioms MoltPetit.Model.badSched_single_key_safe_not_enough

-- W6: mode 1 single-key-safe-not-enough witness
/-- info: 'MoltPetit.Model.badKeyrotOn_single_key_safe_not_enough' does not depend on any axioms -/
#guard_msgs in
#print axioms MoltPetit.Model.badKeyrotOn_single_key_safe_not_enough
