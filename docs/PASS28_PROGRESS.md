# Pass 28 progress

Spec: `docs/PASS28_SPEC.md`. Scaffold: see the commit "pass28 scaffold" (`git log --grep "pass28 scaffold"`).

**Pinned:** `git diff <scaffold> -- Spec/ rust/ rust-keyrot/` must stay empty.

New proofs go in two places:
- `Rust/Deployed.lean`, for the Rust items. Import it from `Rust.lean`.
- `MoltPetit/Model/Pass28.lean`, for the model items. Import it where `Paper/Proofs.lean` can see it.

Each statement `MoltPaper.thm_X` gets `theorem X : MoltPaper.thm_X` and an alias in `Paper/Proofs.lean`, following the pattern there.

Build one module at a time, in the background:

    lake build Rust.Deployed > /tmp/p28.log 2>&1; echo rc=$?; grep -A8 "error" /tmp/p28.log | head -60

In progress: 3. exposure_certified_agreement_ever_on

## Stage B: model statements and circuit completeness (independent; any order)

- [x] 1. **`validChain_snoc`** (`MoltPetit/Model/Pass28.lean`).
  - Unfold `validChain` on `c ++ [b]`. `genesisOk` of the head is unchanged.
  - Linking: `linksOk (c ++ [b]) ↔ linksOk c ∧ childOk t b`.
  - Density: windows with `u + n ≤ t.slot + 1` have the same count over `c` and over `c ++ [b]`, because `b.slot > t.slot` puts `b` outside them. Windows with `t.slot + 2 ≤ u + n ≤ b.slot + 1` are the new ones.
  - Look for existing `windowCount_append` lemmas: `grep -rn "windowCount_append" MoltPetit/`.
- [x] 2. **`reference_eq_model`**. One `funext` per conjunct.
  - Most conjuncts close by `rfl`, or by `funext`, then `induction`, then `simp [Molt.X, MoltPetit.Model.X]`.
  - `Molt.validChain` is written with `denseSoFar`. Prove `denseSoFar = maturedWindowsDense` first.
  - If a conjunct is FALSE, write the counterexample under STOP and do not change the statement.
- [ ] 3. **`exposure_certified_agreement_ever_on`**. Copy the proof of `exposure_certified_agreement_on`. Find it with `grep -rn "exposure_certified_agreement_on" MoltPetit/ Paper/`.
  - Replace the timed-budget argument with the one `exposure_agreement_ever_on` uses (`ExposureBoundedEver`, no clock).
  - The history and certificate plumbing is identical.
- [ ] 4. **`lockstepGen_recent_certified_history_agreement_two_readings`** and **`sched_recent_certified_history_agreement_horizon_two_readings`**.
  - Apply the one-reading theorem at `now₀ := min now now'`.
  - The recency hypotheses follow from `min_le_left` and `min_le_right`.
- [ ] 5. **`valid_chain_be_complete`** (`Rust/Deployed.lean`). Prove the converse of `valid_chain_be_validChain`, in the same file and structure.
  - Each `_be` primitive returns `ok` (no overflow) under the bounds.
  - Its boolean result equals the model's.
  - Reuse the `*_corr` lemmas in `Rust/Equiv.lean`.
- [ ] 6. **`cert_fold_sched_complete`**. Induct on `bs`, reusing `TailRepr` from `Rust/FoldStep.lean`. Each step must show four things:
  - `cert_step_core_be` returns `ok true`. Links come from `linksOk`. Density: every window the fold checks is a window `validChain` checks; this is the converse of `fold_window_ok_be_sound` and `fold_anchors_ok_be_sound`.
  - The pin.
  - `cert_next_tail_be` returns `ok`.
  - `TailRepr` is preserved (reuse `cert_next_tail_be_repr`).
- [ ] 7. **`cert_fold_lock_complete`**. Like step 6. The generation check comes from `lockstepOk`: consecutive blocks have `g ≤ ki`, and in the same window `g = ki`.
- [ ] 8. **`cert_fold_k_complete`**. Like step 6.
  - Floors: `floorsFun` of the threaded floors is the maximum key index per producer so far. This is the invariant `cert_fold_k_sound` uses, in reverse.
  - `keyMonoOk` gives `floor ≤ ki`.

## Stage C: the deployed client (`Rust/Deployed.lean`)

- [ ] 9. **Decoding.** If `claim_of_state n st = ok cl`, then `claimView (toModelClaim cl) = stateView n.val st`, and `claim_of_state` never fails.
  - Use `suffix_lo_val` from `Rust/Bridge.lean`.
  - `tail_of_buffer` keeps the entries `tailSlots` keeps, filtered by `lo ≤ s`.
- [ ] 10. **View transport.** Suppose `validate_suffix n cl tl = ok true` and `claimView cl₀ = claimView (toModelClaim cl)`. Then the hypotheses `hLink`, `hLinks` and `hDense` of the certificate theorems hold against `cl₀` for `toModelChain tl` (non-empty).
  - Start from `validate_suffix_sound`, which gives them against `toModelClaim cl`.
  - Transport field by field: `windowCount` reads only slots, so prove `windowCount (t₁ ++ s) u n = windowCount (t₂ ++ s) u n` when `t₁.map slot = t₂.map slot`.
- [ ] 11. **Per-block checks.**
  - `ids_ok I crypto tl = ok true` gives `RustFormed` for every block of `toModelChain tl`.
  - `recent_ok now Δ tip = ok true` gives `now.val ≤ tip.val + Δ.val`.
  - `sigs_ok_signed` gives `RustSigned` (already in `Rust/Bridge.lean`).
  - `sched_pin_ok` and `lockstep_from` correspond to `schedPinned (·/era)` and `lockstepFrom`.
  - Unfold `validate_deployed*` into its conjuncts.
- [ ] 12. **History.** From `AttestsK I crypto n q G bs stO out` together with `hG` and `hSigG`, derive two facts about `cl₀ := modelClaimOf n.val (toModelBlock G) (bs.map toModelBlock)`:
  - `GroundedCert n.val (DSigned I crypto n) (toModelBlock G) cl₀`, from `cert_fold_k_sound` (`GroundedCertK`) plus a `GroundedCertK → GroundedCert` lemma that forgets the floor;
  - `GroundedHistory … cl₀ ((G :: bs).map toModelBlock)`, by the same induction.

  The twins for sched and lock follow (`GroundedCertSched`/`GroundedHistorySched`, `GroundedCertLock`/`GroundedHistoryLock`).
  - First check whether `groundedCert_history` constructs this exact history.
  - `stateView_of_foldKOut` gives `stateView n stO = claimView cl₀`.
- [ ] 13. **`rust_deployed_agreement`**. Apply `exposure_certified_agreement_on` with `Signed := DSigned I crypto n`, `cl := cl₀`, `c := (G :: bs).map toModelBlock` and `s₁ :: srest := toModelChain tl`.
  - Steps 9–12 give its hypotheses.
  - Recency: `R ≤ now + δ ≤ tip + Δ + δ ≤ tip + φ`.
  - `fullChain G bs tl` unfolds to `c ++ s₁ :: srest`.
- [ ] 14. **`rust_deployed_k_agreement`**.
  - Agreement: `validate_deployed_k` implies `validate_deployed`, then step 13.
  - Monotonicity:
    - the history is monotone (`GroundedCertK` floors);
    - the tail passes `keyMonoFrom` against `floorsFun out` (`key_mono_from_corr`, `floors_of_state`);
    - glue the two, since `floorsFun out` is the per-producer maximum over the history.
- [ ] 15. **`rust_deployed_sched_agreement`**. Apply `exposure_certified_agreement_on` with `Signed := fun B => DSigned … B ∧ B.slot / era ≤ B.keyIndex`.
  - History blocks are pinned by the fold.
  - Tail blocks are pinned by `sched_pin_ok`.
  - The genesis has slot 0, so `0 ≤ keyIndex`.
- [ ] 16. **`rustOps`.** Prove `RustSigned I crypto n B → SignedDeclared n.val (rustOps I crypto) (rustRegistry I crypto) B` (only this direction is needed).
- [ ] 17. **`rust_deployed_lock_agreement`**. Apply `lockstepGen_recent_certified_history_agreement` at `now₀ := min now now'`, with `Formed := RustFormed I crypto` and `g := gO.val`.
  - Use step 16 for `SignedFormed`.
  - Step 11 gives `lockstepFrom`.
  - `foldLockOut_gO` relates `gO` to the history.
- [ ] 18. **`rust_deployed_ks`**. Immediate from `hFold` and the first conjunct of `validate_deployed`.
- [ ] 19. **`rust_produce_block_deployed_live`**. Unfold the producer.
  - Use `signed_tip_*` and `append_signed`, as in `rust_produce_block_cert_sound` in `Rust/Results_rust.lean`.
  - Then show each conjunct of `validate_deployed`:
    - signature: `hSign`;
    - id: by construction;
    - links: `htipH` and `htipS`;
    - density: old windows from `hsuf`, new windows from `hDense`;
    - recency: `recent_ok at_slot Δ at_slot`.
- [ ] 20. **Close out.** Aliases for every Pass 28 statement in `Paper/Proofs.lean`; `#print axioms` clean; `bash tools/check.sh` green.

STOP:
