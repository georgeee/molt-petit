# Timed Certified Light-Client Safety — Progress Log

Tracking implementation of `MoltPetit.Model.timed_certified_agreement` per `docs/TIMED_CERT_SPEC.md`.

## Status Summary

- [x] **Step 1: Mechanical refactor in `MoltPetit/Model/Grounded.lean`**
  - Add `grounded_suffix_history_of` taking a given `GroundedHistory` and concluding `validChain n (c ++ s₁ :: srest) = true`.
  - Re-prove `grounded_suffix_history` from it.
- [x] **Step 2 & 3: Main proof in `MoltPetit/Model/TimedSafetyCert.lean`**
  - Reconstruct valid chains, head, tip, and availability for both presentations.
  - Apply `timed_tip_ancestor_agreement` at the shorter chain length minus $1 + n$.
  - Apply `same_block_same_prefix_timed` to conclude pointwise agreement at height $h$.
- [x] **Step 4: Paper-facing alias and axiom audit**
  - Add `Molt.timed_light_client_safety` in `Molt/Results.lean`.
  - Add `#print axioms` guard in `Molt/Axioms.lean`.
- [x] **Step 5: Full check gate & status update**
  - Run `bash tools/check.sh`.
  - Tick Pass 8 in `docs/PUBLISH_PREP_STATUS.md`.
