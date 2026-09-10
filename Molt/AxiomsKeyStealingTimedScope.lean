import Molt.KeyStealingTimedScope

/-!
# Axiom audit — W6 no-back-dating obstruction witnesses (Molt re-presentation)

Same discipline as `Molt/Axioms.lean`: a guarded `#print axioms` per new
Molt-namespace theorem. New file, not an edit to `Molt/Axioms.lean`, per the
additive-only rule.
-/

-- W6: mode 2/3 witness, Molt re-presentation
/-- info: 'Molt.badSched_single_key_safe_not_enough' does not depend on any axioms -/
#guard_msgs in
#print axioms Molt.badSched_single_key_safe_not_enough

-- W6: mode 1 witness, Molt re-presentation
/-- info: 'Molt.badKeyrot_single_key_safe_not_enough' does not depend on any axioms -/
#guard_msgs in
#print axioms Molt.badKeyrot_single_key_safe_not_enough
