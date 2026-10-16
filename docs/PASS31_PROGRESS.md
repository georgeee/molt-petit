# Pass 31 progress

Spec: `docs/PASS31_SPEC.md`. Scaffold: the commit "pass31 scaffold" (`git log --grep "pass31 scaffold"`).

**Pinned:** `git diff <scaffold> -- Spec/ rust/ rust-keyrot/` must stay empty.

Build one module at a time:

    lake build <Module> > /tmp/p31.log 2>&1; echo rc=$?; grep -A8 "error" /tmp/p31.log | head -60

In progress: none

- [ ] 1. **S1** signed liveness, modes 2 and 3: `lake build MoltPetit.Model.KeyRotationLiveness`.
- [ ] 2. **S2** TypeScript two check times: `lake build MoltPetit.TS.TimedResults`.
- [ ] 3. **S3.1** rename to `FoldCoreLoose`, the `_to_coreOut` lemmas: `lake build Rust.Deployed` may still fail only at `rust_deployed_agreement*` (note which errors remain).
- [ ] 4. **S3.2** `cert_fold_core` soundness + `stateView_of_foldCoreOut`: `lake build Rust.FoldStep`.
- [ ] 5. **S3.3–S3.4** `attestsCore_history`, the theorem and its callers: `lake build Rust.Deployed`.
- [ ] 6. **Close-out:** `Paper/Proofs.lean` entries (S1 x2); `lake build Paper.Proofs`; then a full `lake build` with no sorry.
