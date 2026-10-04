# Mode 1 Against Key Loss — Progress Log

Tracking implementation of `MoltPetit.Model.keyrot_loss_agreement` per `docs/MODE1_LOSS_SPEC.md`.

## Status Summary

- [x] **Step 1: Obtain `ValidChain` from `validSignedChainK'`**
  - Unpacked `validSignedChainK'` to extract `validChainK'` and applied `validChainK'_sound` to obtain `ValidChain n (stripSigs sc)` for both chains.
- [x] **Step 2: Show blockwise `SignedDeclared`**
  - Proved `signedDeclared_of_mem` via `rotated_key_dead` to establish that every block in `stripSigs sc` verifies under its declared registry entry.
- [x] **Step 3: Discharge `AvailableAt`**
  - Discharged availability for every block using `hbridge` applied to the declared signature witness (`Or.inr`).
- [x] **Step 4: Agreement proof**
  - Split on `le_total` of chain lengths, applied `timed_tip_ancestor_agreement`, and propagated to common prefix at height `h` via `same_block_same_prefix_timed`.
- [x] **Step 5: Axiom and tool checks**
  - Built without `sorry` or additional axioms; verified `#guard_msgs` in `Molt/AxiomsKeyRotationLoss.lean`.
  - Ran `bash tools/check.sh`: all green.
