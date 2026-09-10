import Molt.CertClientRule

/-!
# Axiom audit — W2 mode 1 anchored certificate agreement

Same discipline as `Molt/Axioms.lean`. This one file guards both the core
(`MoltPetit.Model.*`) and Molt-namespace declarations `Molt/CertClientRule.lean`
brings into scope, matching `MoltPetit/Results/Axioms.lean`/`Molt/Axioms.lean`'s
existing two-ledger layout but as a single new file for one work item's worth
of declarations. New file, not an edit to either existing `Axioms.lean`, per
the additive-only rule.
-/

/-- info: 'MoltPetit.Model.keyrot_deep_block_agreement_anchored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_deep_block_agreement_anchored

/-- info: 'MoltPetit.Model.AcceptedSuffixK.history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.AcceptedSuffixK.history

/-- info: 'MoltPetit.Model.keyrot_certified_suffix_agreement_anchored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_certified_suffix_agreement_anchored

/-- info: 'Molt.keyrot_certified_suffix_agreement_anchored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.keyrot_certified_suffix_agreement_anchored

/-- info: 'Molt.cert_client_refresh_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.cert_client_refresh_rule

/-- info: 'Molt.cert_stay_recent_client_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.cert_stay_recent_client_safe

/-- info: 'Molt.cert_sync_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.cert_sync_rule

/-- info: 'Molt.cert_max_sync_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.cert_max_sync_period
