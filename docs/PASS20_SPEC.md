# Pass 20 — consumers of the core v2 theorem

Reviewer-owned. The core v2 (`docs/CORE_V2_SPEC.md`) replaces `TimedExecution` and
`ByzantineBounded` with `SigningExecution exposed log G` and `HonestClock σ exposed log`, the windowed budget `ExposureBounded n ℓ φ exposed` and the
lookback conditions `hL : n ≤ ℓ + 1`, `hL' : n + f + σ + 1 ≤ q + ℓ`
(freshness `φ` in `hRecent` instead of `n`). This pass ports every consumer of the old
`TimedSafety`/`TimedSafetyCert` theorems, which have been deleted.

Statements are pinned. Do not change them or the guards:

| Theorem | File | Guard |
|---|---|---|
| `MoltPetit.Model.exposure_certified_agreement` | `MoltPetit/Model/ExposureCert.lean` | `Molt/AxiomsExposureCert.lean` |
| `MoltPetit.Model.keyrot_loss_agreement` | `MoltPetit/Model/KeyRotationLoss.lean` | `Molt/AxiomsKeyRotationLoss.lean` |
| `MoltPetit.Model.sched_loss_agreement`, `lockstep_loss_agreement` | `MoltPetit/Model/KeyRotationLossSchedLock.lean` | `Molt/AxiomsRotationLoss.lean` |
| `Rust.rust_timed_certified_agreement` (body already calls the new theorem) | `Rust/TimedResults_rust.lean` | `Rust/AxiomsTimed.lean` |
| `MoltPetit.Model.ts_timed_certified_agreement` (same) | `MoltPetit/TS/TimedResults.lean` | `Molt/AxiomsTSTimed.lean` |
| `Molt.timed_light_client_safety`, `Molt.no_early_signing` | `Molt/Results.lean` | `Molt/Axioms.lean` |

## Proofs

- **`exposure_certified_agreement`.** Same as the old `timed_certified_agreement` proof
  (`git show a998b02:MoltPetit/Model/TimedSafetyCert.lean`), but simpler.
  - Build `full`/`full'`, `ValidChain` (via `grounded_suffix_history_of` + `validChain_sound`),
    the heads, the tips, and `hAvail` from `hbridge`/`hSigned`/`hc.signed`, exactly as before.
  - Then a single `exact exposure_agreement hn hexec hClock hBudget hL hL' hVS hVS' hHead hHead' hAvail
    hAvail' hTip hTip' hRecent hRecent' hDeep hDeep'`. The new core theorem is already
    symmetric, so no `le_total` case split or `same_block_same_prefix` is needed.
- **The three loss theorems.** Keep the `hVS`/`hVS'`/`hAvail`/`hAvail'` derivations from the
  old proofs (`git show a998b02:<file>`), then finish with one `exact exposure_agreement …`.
- **Molt and Rust/TS.** These compile once the above are proved.

Do not touch `MoltPetit/Model/ExposureSafety.lean` beyond what Pass 19 needs.

## Gate

`bash tools/check.sh` must print `check: all green`. Then add a Pass 20 section with
`STATUS: READY FOR REVIEW` to `docs/PUBLISH_PREP_STATUS.md`.
