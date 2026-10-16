# Pass 30 progress

Spec: `docs/PASS30_SPEC.md`. Scaffold: the commit "pass30 scaffold" (`git log --grep "pass30 scaffold"`).

**Pinned:** `git diff <scaffold> -- Spec/ rust/ rust-keyrot/` must stay empty.

Build one module at a time:

    lake build <Module> > /tmp/p30.log 2>&1; echo rc=$?; grep -A8 "error" /tmp/p30.log | head -60

In progress: 2. S4 two check times: Rust.Deployed agreement theorems (SPEC S4).

- [x] 1. **Definitions move builds.** `lake build MoltPetit.Model.Definitions`, then `MoltPetit.Results.Results`, `MoltPetit.Model.KeyRotationLiveness`. Fix any name clash (the defs now come from Spec.Model).
- [ ] 2. **S4** two check times: `Rust.Deployed` agreement theorems (SPEC S4).
- [ ] 3. **S2** `rust_produce_block_deployed_live_budget` in `Rust/Deployed.lean`.
- [ ] 4. **S3 sched** `rust_produce_block_deployed_sched_live`.
- [ ] 5. **S3 lock** `rust_produce_block_deployed_lock_live`.
- [ ] 6. **S3 k** `rust_produce_block_deployed_k_live`.
- [ ] 7. **Close-out:** `Paper/Proofs.lean` entries for the 6 new theorems (S1 x2, S2, S3 x3); `lake build Paper.Proofs`; then a full `lake build` with no sorry.

## STOP

Syntax error in pinned statement `Spec/Statements.lean:1791` (`thm_rust_produce_block_deployed_live_budget`), introduced in scaffold commit `a5768f7`:
Missing comma `,` at line 1791 after hypothesis `hCover` before the conclusion `∃ (suffix' : SignedChain)...`:
```lean
    (hCover : ∀ u : Nat, tipS.val + 2 ≤ u + n.val → u + n.val ≤ at_slot.val + 1 →
      ∀ s, ¬ bad s → u ≤ s → s < u + n.val →
        s = at_slot.val ∨ ∃ B ∈ (toModelClaim cl).tail ++ toModelChain tl, B.slot = s)
    ∃ (suffix' : SignedChain) (tl' : Chain) (nb : Block),
```
Because of the missing comma, `lake build Spec.Statements` fails with:
`error: Spec/Statements.lean:1791:86: unexpected token '∃'; expected ','`
Because `Spec/` is pinned (`git diff a5768f7 -- Spec/ rust/ rust-keyrot/` must stay empty; "Never edit Spec/"), `Spec/Statements.lean` cannot be edited in this pass. Since `Rust.Deployed` imports `Spec.Statements`, building `Rust.Deployed` (and all remaining pass 30 steps) is blocked until the scaffold is updated with the missing comma.
