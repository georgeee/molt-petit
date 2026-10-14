# Pass 28 progress

Spec: `docs/PASS28_SPEC.md`. Scaffold: see the commit "pass28 scaffold" (`git log --grep "pass28 scaffold"`).

**Pinned:** `git diff <scaffold> -- Spec/ rust/ rust-keyrot/` must stay empty.

New proofs go in two places:
- `Rust/Deployed.lean`, for the Rust items. Import it from `Rust.lean`.
- `MoltPetit/Model/Pass28.lean`, for the model items. Import it where `Paper/Proofs.lean` can see it.

Each statement `MoltPaper.thm_X` gets `theorem X : MoltPaper.thm_X` and an alias in `Paper/Proofs.lean`, following the pattern there.

Build one module at a time, in the background:

    lake build Rust.Deployed > /tmp/p28.log 2>&1; echo rc=$?; grep -A8 "error" /tmp/p28.log | head -60

In progress: 19. rust_produce_block_deployed_live.

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
    - id: by construction;
    - links: `htipH` and `htipS`;
    - density: old windows from `hsuf`, new windows from `hDense`;
    - recency: `recent_ok at_slot Δ at_slot`.
- [ ] 20. **Close out.** Aliases for every Pass 28 statement in `Paper/Proofs.lean`; `#print axioms` clean; `bash tools/check.sh` green.

STOP:
Counterexample to pinned statement `Spec/Statements.lean:1637` (`thm_rust_produce_block_deployed_live`):

The statement asserts that under honest production hypotheses, `produce_block_deployed` produces a certified chain accepted by `validate_deployed`. However, the statement does not assume an overflow bound on `at_slot` (such as `at_slot.val + 1 < 2 ^ 64`).

Concrete counterexample assignment:
- `n := 1#u64` (so `1 ≤ n.val`)
- `me := 0#u64`
- `at_slot := 18446744073709551615#u64` (`2^64 - 1`)
- `Δ := 0#u64`
- `key_index := 0#u64`
- `contents := ⟨0#u64, 0#u64, 0#u64, 0#u64⟩`
- `sk := ⟨0#u64, 0#u64, 0#u64, 0#u64⟩`
- `cert := ⟨0#u64, 0#u64, 0#u64, 0#u64⟩`
- `suffix := SignedChain.SNil`
- `tl := Chain.Nil` (so `strip_sigs suffix = ok tl`)
- `C := Unit`, `crypto := ()`
- `tipS := 18446744073709551614#u64` (`2^64 - 2`)
- `tipH := 0#u64`
- `st := { tip_slot := tipS, tip_height := tipH, tip_id := ⟨0#u64, 0#u64, 0#u64, 0#u64⟩, tail := Chain.Nil }`
- `cl := { tip_slot := tipS, tip_height := tipH, tip_id := ⟨0#u64, 0#u64, 0#u64, 0#u64⟩, tail := Chain.Nil }`
- `I`: a `CryptoD Unit` implementation returning `ok` for all operations (`cert_state _ _ = ok st`, `cert_verify _ _ = ok true`, `key_for _ _ _ = ok ⟨0,0,0,0⟩`, `sign _ _ _ = ok ⟨0,0,0,0⟩`, `verify _ _ _ _ = ok true`, `block_id _ _ _ _ _ _ = ok ⟨0,0,0,0⟩`).

Verification of all hypotheses:
- `hn : 1 ≤ n.val`: `1 ≤ 1` holds.
- `hst : I.cert_state crypto cert = ok st`: holds by definition of `I`.
- `hcl : claim_of_state n st = ok cl`: holds since `st.tail = Chain.Nil`.
- `hcv : I.CryptoInst.cert_verify crypto cert = ok true`: holds by definition of `I`.
- `hstr : strip_sigs suffix = ok tl`: `strip_sigs SignedChain.SNil = ok Chain.Nil`.
- `hsig : sigs_ok I.CryptoInst n crypto suffix = ok true`: holds for `SignedChain.SNil`.
- `hids : ids_ok I crypto tl = ok true`: holds for `Chain.Nil`.
- `hsuf : validate_suffix n cl tl = ok true`: holds for `Chain.Nil`.
- `hMine : producer_for_slot n at_slot = ok me`: `(2^64 - 1) % 1 = 0`, holds.
- `htipS : tip_slot_from cl.tip_slot tl = ok tipS`: `tip_slot_from tipS Chain.Nil = ok tipS`.
- `htipH : signed_tip_height_from cl.tip_height suffix = ok tipH`: `signed_tip_height_from tipH SignedChain.SNil = ok tipH`.
- `hLt : tipS.val < at_slot.val`: `2^64 - 2 < 2^64 - 1` holds.
- `hH : tipH.val + 1 < 2 ^ 64`: `0 + 1 < 2^64` holds.
- `hSign`: holds by definition of `I`.
- `hId`: holds by definition of `I`.
- `hDense`: For `u` with `tipS.val + 2 ≤ u + n.val ≤ at_slot.val + 1`, we have `2^64 ≤ u + 1 ≤ 2^64`, forcing `u = 2^64 - 1 = at_slot.val`. The single block has `slot = at_slot.val`, which is in window `[u, u]`, so `windowCount = 1 ≥ quorum 1 = 1`.

Failure of conclusion:
When `produce_block_deployed` runs, it appends the new block `nb` with `nb.slot = at_slot = 18446744073709551615#u64` and validates the resulting suffix via `validate_deployed`.
`validate_deployed` calls `validate_suffix`, which calls `matured_dense buf lo tip_slot n` where `tip_slot = nb.slot = 18446744073709551615#u64`.
In `matured_dense`:
```lean
let i1 ← t + 1#u64
```
with `t = 18446744073709551615#u64`. Checked addition overflows `U64` and returns `Result.fail Error.integerOverflow`.
This failure propagates up through `matured_dense`, `validate_suffix`, `validate_deployed`, and `produce_block_deployed`, so `produce_block_deployed` returns `Result.fail Error.integerOverflow` instead of `ok (CertifiedChain.CC cert suffix')`.
Hence the conclusion does not hold.
