# Pass 28 progress

Spec: `docs/PASS28_SPEC.md`. Scaffold: see the commit "pass28 scaffold" (`git log --grep "pass28 scaffold"`).

**Pinned:** `git diff <scaffold> -- Spec/ rust/ rust-keyrot/` must stay empty.

New proofs go in two places:
- `Rust/Deployed.lean`, for the Rust items. Import it from `Rust.lean`.
- `MoltPetit/Model/Pass28.lean`, for the model items. Import it where `Paper/Proofs.lean` can see it.

Each statement `MoltPaper.thm_X` gets `theorem X : MoltPaper.thm_X` and an alias in `Paper/Proofs.lean`, following the pattern there.

Build one module at a time, in the background:

    lake build Rust.Deployed > /tmp/p28.log 2>&1; echo rc=$?; grep -A8 "error" /tmp/p28.log | head -60

In progress: 11b. ids repair.

**Rescaffold (reviewer, after step 18).** The scaffold moved; the pin is now the commit "pass28 rescaffold 3" (`git log --grep "pass28 rescaffold 3"`), and `git diff <that commit> -- Spec/ rust/ rust-keyrot/` must stay empty. What changed:
- Block ids hash the parent block's signature. `CryptoD.block_id` gains `parent_sig : Option Hash`; `CryptoD.cert_tip_sig` is new. `ids_ok` now walks the SIGNED chain: `ids_ok I crypto ps suffix`, passing each block's signature as the next block's `ps`. `validate_deployed` starts it at `some ts` with `I.cert_tip_sig crypto cert = ok ts`. `RustFormed I crypto B` is now `∃ b ps, toModelBlock b = B ∧ I.block_id crypto b.slot b.height b.prev ps b.contents_hash b.key_index = ok b.id`.
- `thm_rust_produce_block_deployed_live` gains `hts`, the signed form of `hids`, `hId` over six arguments, and the bounds `hsmall : n.val < 2 ^ 62`, `hS : at_slot.val < 2 ^ 62` (the STOP counterexample below is resolved by these).
- TypeScript: `validateDeployed`, `idsOk`, `recentOk` in `Spec/TS.lean`; `TSFormed` in `Spec/Model.lean`; statement `thm_ts_deployed_agreement` (step 20).

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
- [x] 3. **`exposure_certified_agreement_ever_on`**. Copy the proof of `exposure_certified_agreement_on`. Find it with `grep -rn "exposure_certified_agreement_on" MoltPetit/ Paper/`.
  - Replace the timed-budget argument with the one `exposure_agreement_ever_on` uses (`ExposureBoundedEver`, no clock).
  - The history and certificate plumbing is identical.
- [x] 4. **`lockstepGen_recent_certified_history_agreement_two_readings`** and **`sched_recent_certified_history_agreement_horizon_two_readings`**.
  - Apply the one-reading theorem at `now₀ := min now now'`.
  - The recency hypotheses follow from `min_le_left` and `min_le_right`.
- [x] 5. **`valid_chain_be_complete`** (`Rust/Deployed.lean`). Prove the converse of `valid_chain_be_validChain`, in the same file and structure.
  - Each `_be` primitive returns `ok` (no overflow) under the bounds.
  - Its boolean result equals the model's.
  - Reuse the `*_corr` lemmas in `Rust/Equiv.lean`.
- [x] 6. **`cert_fold_sched_complete`**. Induct on `bs`, reusing `TailRepr` from `Rust/FoldStep.lean`. Each step must show four things:
  - `cert_step_core_be` returns `ok true`. Links come from `linksOk`. Density: every window the fold checks is a window `validChain` checks; this is the converse of `fold_window_ok_be_sound` and `fold_anchors_ok_be_sound`.
  - The pin.
  - `cert_next_tail_be` returns `ok`.
  - `TailRepr` is preserved (reuse `cert_next_tail_be_repr`).
- [x] 7. **`cert_fold_lock_complete`**. Like step 6. The generation check comes from `lockstepOk`: consecutive blocks have `g ≤ ki`, and in the same window `g = ki`.
- [x] 8. **`cert_fold_k_complete`**. Like step 6.
  - Floors: `floorsFun` of the threaded floors is the maximum key index per producer so far. This is the invariant `cert_fold_k_sound` uses, in reverse.
  - `keyMonoOk` gives `floor ≤ ki`.

## Stage C: the deployed client (`Rust/Deployed.lean`)

- [x] 9. **Decoding.** If `claim_of_state n st = ok cl`, then `claimView (toModelClaim cl) = stateView n.val st`, and `claim_of_state` never fails.
  - Use `suffix_lo_val` from `Rust/Bridge.lean`.
  - `tail_of_buffer` keeps the entries `tailSlots` keeps, filtered by `lo ≤ s`.
- [x] 10. **View transport.** Suppose `validate_suffix n cl tl = ok true` and `claimView cl₀ = claimView (toModelClaim cl)`. Then the hypotheses `hLink`, `hLinks` and `hDense` of the certificate theorems hold against `cl₀` for `toModelChain tl` (non-empty).
  - Start from `validate_suffix_sound`, which gives them against `toModelClaim cl`.
  - Transport field by field: `windowCount` reads only slots, so prove `windowCount (t₁ ++ s) u n = windowCount (t₂ ++ s) u n` when `t₁.map slot = t₂.map slot`.
- [x] 11. **Per-block checks.**
  - `ids_ok I crypto tl = ok true` gives `RustFormed` for every block of `toModelChain tl`.
  - `recent_ok now Δ tip = ok true` gives `now.val ≤ tip.val + Δ.val`.
  - `sigs_ok_signed` gives `RustSigned` (already in `Rust/Bridge.lean`).
  - `sched_pin_ok` and `lockstep_from` correspond to `schedPinned (·/era)` and `lockstepFrom`.
  - Unfold `validate_deployed*` into its conjuncts.
- [x] 11b. **ids repair.** Re-prove `ids_ok_formed` in `Rust/Deployed.lean` for the signed `ids_ok`: `∀ ps sc tl, strip_sigs sc = ok tl → ids_ok I crypto ps sc = ok true → ∀ B ∈ toModelChain tl, RustFormed I crypto B`. Induct on `sc`, generalising `ps`; the witness for each block is the `ps` threaded to it. Then repair every use (steps 11, 13–18): `lake build` and fix each error. Change no statement.
- [x] 12. **History.** From `AttestsK I crypto n q G bs stO out` together with `hG` and `hSigG`, derive two facts about `cl₀ := modelClaimOf n.val (toModelBlock G) (bs.map toModelBlock)`:
  - `GroundedCert n.val (DSigned I crypto n) (toModelBlock G) cl₀`, from `cert_fold_k_sound` (`GroundedCertK`) plus a `GroundedCertK → GroundedCert` lemma that forgets the floor;
  - `GroundedHistory … cl₀ ((G :: bs).map toModelBlock)`, by the same induction.

  The twins for sched and lock follow (`GroundedCertSched`/`GroundedHistorySched`, `GroundedCertLock`/`GroundedHistoryLock`).
  - First check whether `groundedCert_history` constructs this exact history.
  - `stateView_of_foldKOut` gives `stateView n stO = claimView cl₀`.
- [x] 13. **`rust_deployed_agreement`**. Apply `exposure_certified_agreement_on` with `Signed := DSigned I crypto n`, `cl := cl₀`, `c := (G :: bs).map toModelBlock` and `s₁ :: srest := toModelChain tl`.
  - Steps 9–12 give its hypotheses.
  - Recency: `R ≤ now + δ ≤ tip + Δ + δ ≤ tip + φ`.
  - `fullChain G bs tl` unfolds to `c ++ s₁ :: srest`.
- [x] 14. **`rust_deployed_k_agreement`**.
  - Agreement: `validate_deployed_k` implies `validate_deployed`, then step 13.
  - Monotonicity:
    - the history is monotone (`GroundedCertK` floors);
    - the tail passes `keyMonoFrom` against `floorsFun out` (`key_mono_from_corr`, `floors_of_state`);
    - glue the two, since `floorsFun out` is the per-producer maximum over the history.
- [x] 15. **`rust_deployed_sched_agreement`**. Apply `exposure_certified_agreement_on` with `Signed := fun B => DSigned … B ∧ B.slot / era ≤ B.keyIndex`.
  - History blocks are pinned by the fold.
  - Tail blocks are pinned by `sched_pin_ok`.
  - The genesis has slot 0, so `0 ≤ keyIndex`.
- [x] 16. **`rustOps`.** Prove `RustSigned I crypto n B → SignedDeclared n.val (rustOps I crypto) (rustRegistry I crypto) B` (only this direction is needed).
- [x] 17. **`rust_deployed_lock_agreement`**. Apply `lockstepGen_recent_certified_history_agreement` at `now₀ := min now now'`, with `Formed := RustFormed I crypto` and `g := gO.val`.
  - Use step 16 for `SignedFormed`.
  - Step 11 gives `lockstepFrom`.
  - `foldLockOut_gO` relates `gO` to the history.
- [x] 18. **`rust_deployed_ks`**. Immediate from `hFold` and the first conjunct of `validate_deployed`.
- [ ] 19. **`rust_produce_block_deployed_live`**. Unfold the producer.
  - Use `signed_tip_*` and `append_signed`, as in `rust_produce_block_cert_sound` in `Rust/Results_rust.lean`.
  - Then show each conjunct of `validate_deployed`:
    - signature: `hSign`;
    - id: by construction (`ids_ok` of `suffix ++ [nb]` from `hids`, threading signatures: the new block's id was computed with `parent_sig := some (signed_tip_sig_from ts suffix)`, the last signature `ids_ok` threads); `hId` gives the id;
    - links: `htipH` and `htipS`;
    - density: old windows from `hsuf`, new windows from `hDense`;
    - recency: `recent_ok at_slot Δ at_slot`.
    - overflow: `hsmall` and `hS` bound every `+` in `matured_dense` and the links check.
- [ ] 20. **`ts_deployed_agreement`** (next to `ts_timed_certified_agreement`). Reduce to `ts_timed_certified_agreement` with `Formed := TSFormed sigOps`.
  - `validateDeployed` unfolds to `validateCertifiedChain`, a non-empty suffix (`0 < lengthOfSigned`), `idsOk`, and `recentOk`.
  - `idsOk sigOps ps (toTSSigned sc) = true` gives `TSFormed sigOps B` for every `B ∈ stripSigs sc` (induct on `sc`, generalising `ps`).
  - Recency: `recentOk now Δ (tipSlotFrom _ (toTSChain (stripSigs sc)))` is `now ≤ tip + Δ` with `tip` the last slot of the non-empty suffix, so `R ≤ now + δ ≤ tip + Δ + δ ≤ tip + φ` (over `Int`, then cast).
  - Name `s₁ :: srest := stripSigs sc` from non-emptiness.
- [ ] 21. **Close out.** Aliases for every Pass 28 statement in `Paper/Proofs.lean`; `#print axioms` clean; `bash tools/check.sh` green.

STOP:

(Resolved by the rescaffold: the earlier counterexample at `at_slot = 2^64 - 1` is excluded by `hS`.)
