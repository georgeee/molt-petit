import Rust.Results_rust
import Rust.Equiv
import Rust.BridgeK

/-!
# Axiom audit — Rust results

The Rust corollaries and the circuit-soundness theorem, checked against Lean's
axioms exactly as the model/TypeScript results are in `MoltPetit/Results/Axioms.lean`.
Each `#guard_msgs`-wrapped `#print axioms` fails the build if the theorem ever
depends on anything beyond `propext`, `Classical.choice`, `Quot.sound` — so the
Charon + Aeneas extraction is certified to introduce no axioms of its own.
-/

-- T1 light-client safety — Rust corollaries
/-- info: 'Rust.rust_deep_block_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rust.rust_deep_block_agreement
/-- info: 'Rust.rust_recent_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rust.rust_recent_tip_ancestor_agreement
/-- info: 'Rust.rust_recent_tip_ancestor_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rust.rust_recent_tip_ancestor_mem
/-- info: 'Rust.rust_recent_produced_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rust.rust_recent_produced_tip_ancestor_agreement


-- Verifier soundness (the hinge both safety paths transfer through)
/-- info: 'Rust.rust_valid_chain_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rust.rust_valid_chain_sound

-- Shared-source validator soundness, proved at the native U64 backend; the
-- plonky2 backend's gadget faithfulness stays a named trust assumption (paper Section 7)
/-- info: 'Rust.valid_chain_be_validChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rust.valid_chain_be_validChain
-- The indexed validator, re-extracted and bridged: Rust valid_chain_k acceptance
-- projects to the model's ValidChain ∧ KeyIndexMonotone (the ≤ in-force pin follows
-- on full chains) — no Aeneas Std `sorry` reaches the closure.
/-- info: 'Rust.rust_valid_chain_k_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rust.rust_valid_chain_k_sound

-- The certificate-boundary check, re-extracted and bridged (`Rust/BridgeK.lean`):
-- Rust validate_suffix_k acceptance yields the suffix hypotheses of the
-- certificate-level key-stealing theorem (link/structure/density + keyMonoFrom
-- at the attested floor), mirroring `ts_validateSuffixK_sound`; the extracted
-- floor accessors compute the TS wire functions on the projection (on
-- success) and the shape/mono checks are acceptance-sound for the TS ones.
/-- info: 'Rust.validate_suffix_k_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rust.validate_suffix_k_sound
/-- info: 'Rust.key_mono_from_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rust.key_mono_from_corr
