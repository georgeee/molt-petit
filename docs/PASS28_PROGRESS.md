# Pass 28 progress

Spec: `docs/PASS28_SPEC.md`. Scaffold: see the commit "pass28 scaffold" (`git log --grep "pass28 scaffold"`).

**Pinned:** `git diff <scaffold> -- Spec/ rust/ rust-keyrot/` must stay empty.

New proofs go in two places:
- `Rust/Deployed.lean`, for the Rust items. Import it from `Rust.lean`.
- `MoltPetit/Model/Pass28.lean`, for the model items. Import it where `Paper/Proofs.lean` can see it.

Each statement `MoltPaper.thm_X` gets `theorem X : MoltPaper.thm_X` and an alias in `Paper/Proofs.lean`, following the pattern there.

Build one module at a time, in the background:

    lake build Rust.Deployed > /tmp/p28.log 2>&1; echo rc=$?; grep -A8 "error" /tmp/p28.log | head -60

In progress: 19b. validate_suffix_append.

**Rescaffold (reviewer, after step 18).** The scaffold moved; the pin is now the commit "pass28 rescaffold 4" (`git log --grep "pass28 rescaffold 4"`), and `git diff <that commit> -- Spec/ rust/ rust-keyrot/` must stay empty. What changed:
- Block ids hash the parent block's signature. `CryptoD.block_id` gains `parent_sig : Option Hash`; `CryptoD.cert_tip_sig` is new. `ids_ok` now walks the SIGNED chain: `ids_ok I crypto ps suffix`, passing each block's signature as the next block's `ps`. `validate_deployed` starts it at `some ts` with `I.cert_tip_sig crypto cert = ok ts`. `RustFormed I crypto B` is now `∃ b ps, toModelBlock b = B ∧ I.block_id crypto b.slot b.height b.prev ps b.contents_hash b.key_index = ok b.id`.
- `thm_rust_produce_block_deployed_live` gains `hts`, the signed form of `hids`, `hId` over six arguments, the bounds `hsmall : n.val < 2 ^ 62`, `hS : at_slot.val < 2 ^ 62`, and (rescaffold 4) `htail`: the decoded claim's tail lies at or below its tip slot. Both STOP counterexamples are resolved by these.
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
- [ ] 19. **`rust_produce_block_deployed_live`**.
  - [x] 19a. **`ids_ok_append_signed` and `sigs_ok_append_signed`**: signature and id chains preserved across `append_signed`.
  - [ ] 19b. **`validate_suffix_append`**: suffix links and density checks for the appended block.
  - [ ] 19c. **`rust_produce_block_deployed_live`**: unfold `produce_block_deployed` and assemble the conjuncts.
- [ ] 20. **`ts_deployed_agreement`** (next to `ts_timed_certified_agreement`). Reduce to `ts_timed_certified_agreement` with `Formed := TSFormed sigOps`.
  - `validateDeployed` unfolds to `validateCertifiedChain`, a non-empty suffix (`0 < lengthOfSigned`), `idsOk`, and `recentOk`.
  - `idsOk sigOps ps (toTSSigned sc) = true` gives `TSFormed sigOps B` for every `B ∈ stripSigs sc` (induct on `sc`, generalising `ps`).
  - Recency: `recentOk now Δ (tipSlotFrom _ (toTSChain (stripSigs sc)))` is `now ≤ tip + Δ` with `tip` the last slot of the non-empty suffix, so `R ≤ now + δ ≤ tip + Δ + δ ≤ tip + φ` (over `Int`, then cast).
  - Name `s₁ :: srest := stripSigs sc` from non-emptiness.
- [ ] 21. **Close out.** Aliases for every Pass 28 statement in `Paper/Proofs.lean`; `#print axioms` clean; `bash tools/check.sh` green.

STOP:

Counterexample to pinned statement `Spec/Statements.lean:1637` (`thm_rust_produce_block_deployed_live`):

The statement asserts that under honest production hypotheses, `produce_block_deployed` produces a certified chain accepted by `validate_deployed`. Rescaffold 4 added `htail : ∀ B ∈ toModelChain cl.tail, B.slot ≤ cl.tip_slot.val` to bound the slot numbers of `cl.tail`. However, `st : CertStateG U64` (and hence `cl.tail`) remains unconstrained in length / block count. When `suffix = SignedChain.SNil` (so `tl = Chain.Nil`), `hsuf : validate_suffix n cl tl = ok true` trivially returns `ok true` without inspecting `cl.tail`. Consequently, `st.tail` can contain `2^64` entries with `slot = 0#u64`. When `produce_block_deployed` produces the new block `nb`, it validates `new_suffix = [nb]` via `validate_deployed`, which runs `validate_suffix n cl [nb]`. This calls `matured_dense (cl.tail ++ [nb]) lo nb.slot n`, which calls `window_dense n (cl.tail ++ [nb]) lo`. In `window_dense`, `window_count (cl.tail ++ [nb]) lo n` counts blocks in `[lo, lo + n)`. Because all `2^64` blocks of `cl.tail` have `slot = 0#u64 ∈ [lo, lo + n)`, `window_count` accumulates `1#u64` across all `2^64` entries. On the `2^64`-th addition, `(2^64 - 1)#u64 + 1#u64` overflows `U64` and returns `Result.fail Error.integerOverflow`. Thus `produce_block_deployed` returns `Result.fail Error.integerOverflow` instead of `ok (CertifiedChain.CC cert suffix')`.

Concrete counterexample assignment:
- `C := Unit`, `crypto := ()`
- `n := 2#u64` (so `hn : 1 ≤ n.val` and `hsmall : n.val < 2 ^ 62` hold)
- `me := 1#u64`
- `at_slot := 1#u64` (so `hS : at_slot.val < 2 ^ 62` holds)
- `Δ := 0#u64`
- `key_index := 0#u64`
- `contents := ⟨0#u64, 0#u64, 0#u64, 0#u64⟩`
- `sk := ⟨0#u64, 0#u64, 0#u64, 0#u64⟩`
- `cert := ⟨0#u64, 0#u64, 0#u64, 0#u64⟩`
- `ts := ⟨0#u64, 0#u64, 0#u64, 0#u64⟩`
- `suffix := SignedChain.SNil`
- `tl := Chain.Nil` (so `hstr : strip_sigs suffix = ok tl` holds)
- `tipS := 0#u64`
- `tipH := 0#u64`
- Let `bigTail : Nat → TailG U64` be defined by `bigTail 0 = TailG.TNil`, `bigTail (k + 1) = TailG.TCons 1#u64 0#u64 (bigTail k)`.
- `st := { tip_slot := 0#u64, tip_height := 0#u64, tip_id := ⟨0#u64, 0#u64, 0#u64, 0#u64⟩, tail := bigTail (2 ^ 64) }`
- `I : CryptoD Unit` returning `ok` for all operations (`cert_state _ _ = ok st`, `cert_tip_sig _ _ = ok ts`, `cert_verify _ _ = ok true`, `key_for _ _ _ = ok ⟨0,0,0,0⟩`, `sign _ _ _ = ok ⟨0,0,0,0⟩`, `verify _ _ _ _ = ok true`, `block_id _ _ _ _ _ _ _ = ok ⟨0,0,0,0⟩`, `cert_floors_state _ _ = ok FloorsG.FNil`, `cert_gen _ _ = ok 0#u64`).

Verification of all hypotheses:
- `hn : 1 ≤ n.val`: `1 ≤ 2` holds.
- `hst : I.cert_state crypto cert = ok st`: holds by definition of `I`.
- `hts : I.cert_tip_sig crypto cert = ok ts`: holds by definition of `I`.
- `hcl : claim_of_state n st = ok cl`: `suffix_lo 2#u64 0#u64 = ok 0#u64` (since `0 + 2 - 2 = 0`). In `tail_of_buffer`, `0#u64 ≤ 0#u64` holds for all nodes, returning `cl` with `cl.tip_slot = 0#u64`, `cl.tip_height = 0#u64`, and `cl.tail` containing `2^64` blocks with `slot := 0#u64`.
- `hcv : I.CryptoInst.cert_verify crypto cert = ok true`: holds by definition of `I`.
- `hstr : strip_sigs suffix = ok tl`: `strip_sigs SNil = ok Nil` holds.
- `hsig : sigs_ok I.CryptoInst n crypto suffix = ok true`: holds for `SNil`.
- `hids : ids_ok I crypto (some ts) suffix = ok true`: holds for `SNil`.
- `hsuf : validate_suffix n cl tl = ok true`: holds for `Chain.Nil` by definition (`match suffix with | Nil => ok true`).
- `hMine : producer_for_slot n at_slot = ok me`: `1 % 2 = 1` holds.
- `htipS : tip_slot_from cl.tip_slot tl = ok tipS`: `tip_slot_from 0#u64 Nil = ok 0#u64`.
- `htipH : signed_tip_height_from cl.tip_height suffix = ok tipH`: `signed_tip_height_from 0#u64 SNil = ok 0#u64`.
- `hLt : tipS.val < at_slot.val`: `0 < 1` holds.
- `hH : tipH.val + 1 < 2 ^ 64`: `0 + 1 < 2^64` holds.
- `hsmall : n.val < 2 ^ 62`: `2 < 2^62` holds.
- `hS : at_slot.val < 2 ^ 62`: `1 < 2^62` holds.
- `htail : ∀ B ∈ toModelChain cl.tail, B.slot ≤ cl.tip_slot.val`: each block in `cl.tail` has `slot = 0 ≤ 0 = cl.tip_slot.val`.
- `hSign`: holds by definition of `I`.
- `hId`: holds by definition of `I`.
- `hDense`: For `u` with `0 + 2 ≤ u + 2 ≤ 1 + 1`, we have `u = 0`. In window `[0, 2)`, all `2^64` blocks from `cl.tail` (with `slot = 0`) and the appended block (with `slot = 1`) lie in `[0, 2)`. So `windowCount = 2^64 + 1 ≥ quorum 2 = 1`.

Failure of conclusion:
When `produce_block_deployed` runs, it creates `nb` with `nb.slot = 1#u64` and `new_suffix = SCons nb sig SNil`.
It then calls `validate_deployed` on `new_suffix`, which calls `validate_suffix 2#u64 cl [nb]`.
`validate_suffix` matches `Chain.Cons nb Nil` and calls `matured_dense (cl.tail ++ [nb]) 0#u64 1#u64 2#u64`.
`matured_dense` evaluates `lo + n = 0 + 2 = 2` and `t + 1 = 1 + 1 = 2`.
Since `lo + n ≤ t + 1`, it calls `window_dense 2#u64 (cl.tail ++ [nb]) 0#u64`.
`window_dense` calls `window_count (cl.tail ++ [nb]) 0#u64 2#u64`.
In `window_count`, every block of `cl.tail` satisfies `0 ≤ 0 ∧ 0 < 2`, so `here = 1#u64`.
`window_count` accumulates `1#u64` across all `2^64` entries of `cl.tail`.
On the `2^64`-th addition of `1#u64`, checked U64 addition `(2^64 - 1)#u64 + 1#u64` overflows `2^64` and returns `Result.fail Error.integerOverflow`.
This failure propagates out: `produce_block_deployed` returns `Result.fail Error.integerOverflow` instead of `ok (CertifiedChain.CC cert new_suffix)`.
Hence no `suffix'`, `tl'`, `nb` can satisfy `produce_block_deployed ... = ok (CertifiedChain.CC cert suffix')`.
