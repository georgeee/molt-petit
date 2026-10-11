# Pass 26 progress (Stages A and C)

Stage A scaffold: 7a5fe4e (done). Stage C scaffold: 9a6b2c7, spec `docs/PASS26_STAGE_C.md` ("Proof steps" 11-14). Pinned: `git diff 9a6b2c7 -- Spec/ rust/ rust-keyrot/` must stay empty.

In progress: (none)

- [x] 1. Skeleton and primitives
- [x] 2. Counting (`tail_count_be_corr`)
- [x] 3. Window checks
- [x] 4. `TailRepr` and `cert_step_core_be_sound`
- [x] 5. `cert_next_tail_be_repr`
- [x] 6. Prefix claim and genesis repr
- [x] 7. Mode 2 `cert_fold_sched_sound`
- [x] 8. Mode 3 `cert_fold_lock_sound`
- [x] 9. Mode 1 floors + `cert_fold_k_sound`
- [x] 10. Aliases in `Paper/Proofs.lean`, check.sh green
- [x] 11. Final state: `Fold*Out → Fold*`, `TailRepr` of the final state, `stateView n stO = claimView (modelClaimOf …)`
- [x] 12. Mode 1 client `cert_fold_k_client`
- [ ] 13. Modes 2 and 3 clients `cert_fold_sched_client`, `cert_fold_lock_client`
- [ ] 14. Aliases in `Paper/Proofs.lean`, check.sh green

STOP:
