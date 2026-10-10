# Pass 24 Progress

- [x] Task (a): Three history theorems (`thm_lockstep_recent_certified_history_agreement`, `thm_lockstepGen_recent_certified_history_agreement`, `thm_sched_recent_certified_history_agreement_horizon`)
- [x] Task (b): Aliases in `Paper/Proofs.lean` for the 5 existing theorems in table
- [x] Task (c): `notBefore` field removal confirmation and comment updates
- [x] Task (d): TS clamp in `moltPetit.ts`, `MoltPetit.emitted.lean`, `Spec/TS.lean`, `nix/checks.nix`, TS soundness proofs, and #guard test
- [x] Task (e): N1: hash injectivity over formed blocks across development proofs and packages
- [x] Task (f): N3 binder preserved in TS emit / mirror

## Task (e) steps (recipe: docs/PASS24_N1_PLAN.md)

In progress: (none)

Modules fixed:
- [x] step 1
- [x] step 2
- [x] step 3
- [x] step 4
- [x] step 5
- [x] step 6
- [x] step 7
- [x] step 8
- [x] step 9
- [x] step 10
- [x] step 11
- [x] step 12
- [x] step 13
- [x] step 14
- [x] step 15
- [x] step 16

STOP:
(none)

Reviewer, 2026-10-10: (d) verified by `nix build .#checks.x86_64-linux.{ts-emission-golden,ts-golden-digest,ts-vendored-deviations,ts-deviation-sites,tsc}` (all rc=0; fresh thales emission == golden byte for byte); (f) by ts-vendored-deviations. Pins vs aa2a1c8 unchanged; tools/check.sh all green at 2c56100.
