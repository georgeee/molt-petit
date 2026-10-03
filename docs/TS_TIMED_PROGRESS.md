# Pass 8c Progress Log: Timed Certified Safety for TypeScript Validator

Tracking implementation of `MoltPetit.Model.ts_timed_certified_agreement` in `MoltPetit/TS/TimedResults.lean` and `MoltPetit.Model.noTheftBackdating_degenerate` in `MoltPetit/Model/KeyStealingSignatureTimed.lean` per `docs/TS_TIMED_SPEC.md`.

## Summary of Implementation

- [x] **Add injectivity helpers in `MoltPetit/TS/TimedResults.lean`**
  - Proved `toTSChain_injective : Function.Injective toTSChain` by list induction and field injection.
  - Proved `toTSClaim_injective : Function.Injective toTSClaim` using `toTSChain_injective` and constructor injection.
- [x] **Prove `MoltPetit.Model.ts_timed_certified_agreement`**
  - Soundness extraction via `ts_validateCertifiedChain_sound` on `hval` and `hval'`.
  - Claim identification using `toTSClaim_injective` on `hUnf` and `hcl` (`hUnf'` and `hcl'`).
  - Suffix signatures via `ts_sigsOk_signed`.
  - Suffix links and density via `ts_validateSuffix_sound`.
  - Concluded agreement pointwise on attested histories via `timed_certified_agreement`.
- [x] **Prove `noTheftBackdating_degenerate` and update docstrings**
  - Proved `noTheftBackdating_degenerate` in `MoltPetit/Model/KeyStealingSignatureTimed.lean` showing `confirmedPrefix Δconf c₀ 0 = []` for $1 \le \Delta_{	ext{conf}}$, forcing `inForce = 0 \le j` and $r = 0$.
  - Updated docstrings for `NoTheftBackdating`, `theft_exposure_window`, `exposedProducers_subset_recentTheftTight`, `budget_of_reaction_tight`, `anchored_budget_of_reaction_tight`, `max_sync_period_tight`, `exposedProducers_card_le_one_of_paced`, and `paced_budget_holds_under_timing` documenting degeneracy.
- [x] **Axiom Audit and Gate Verification**
  - Verified `Molt.AxiomsTSTimed` guard succeeds with standard axioms `[propext, Classical.choice, Quot.sound]`.
  - Ran `bash tools/check.sh`: all Lean targets built, zero sorry, zero axiom declarations, paper built cleanly (`check: all green`).
- [x] **Status Update**
  - Ticked Pass 8c in `docs/PUBLISH_PREP_STATUS.md`.
