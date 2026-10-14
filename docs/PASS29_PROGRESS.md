# Pass 29 progress

Spec: `docs/PASS29_SPEC.md`. Scaffold: the commit "pass29 scaffold" (`git log --grep "pass29 scaffold"`).

**Pinned:** `git diff <scaffold> -- Spec/ rust/ rust-keyrot/` must stay empty.

Build one module at a time, in the background:

    lake build <Module> > /tmp/p29.log 2>&1; echo rc=$?; grep -A8 "error" /tmp/p29.log | head -60

At the scaffold, a full `lake build` fails first in `MoltPetit.TS.TimedResults` and `MoltPetit.Model.KeyStealingSchedule`. Modules downstream of these (including `Rust.Deployed`) were not reached and will show further errors once they build.

In progress: none (Pass 29 complete)

## Stage A: model (mode 2 without the monotone rule)

- [x] 1. **`MoltPetit.Model.KeyStealingSchedule`**. `validSignedChainSched` is now `sigsOk && validChain && schedPinned`, so `h.left.right : validChain … = true` directly.
  - Replace `validChainK_sound h.left.right` and the like by the direct fact.
  - Any argument that used `keyMonoOk` for mode 2 must be rewritten without it. Mode-2 safety rests on the schedule pin.
  - Then build every module that imports it, one at a time, and repair them the same way: `grep -rln "validSignedChainSched" MoltPetit/ Rust/ Molt/ Paper/`.
- [x] 2. **`sched_liveness_produce_block`** without `hFloor`. Delete the floor obligation from the proof; the produced block need not meet a floor.
- [x] 3. **`reference_eq_model`**. Re-close the mode-2 conjunct; Model and Reference changed in step.

## Stage B: Rust deployed client (`Rust/Deployed.lean`)

- [x] 4. **Signatures.**
  - New lemma: `sigs_ok` on `SCons b s rest` gives `SigOn I.CryptoInst crypto n b s` and `sigs_ok rest`.
  - Also: `SigOn … b s → RustSigned … (toModelBlock b)`.
- [x] 5. **Tail formedness** (replaces `ids_ok_formed`; SPEC item 2). Assume:
  - `FormedFrom I crypto n G T` and `SigOn … T ts`;
  - `strip_sigs sc = ok tl`, `sigs_ok sc = ok true` and `ids_ok I crypto (some ts) sc = ok true`;
  - the head of `tl` has `prev = some T.id`, and consecutive blocks of `tl` link (`prev = some` the previous id).

  Then every `b` in `tl` is `FormedFrom … G b`. Induct on `sc` generalising `T ts`. Then rebuild `dsigned_of_sigs_ok_ids_ok` with the new hypotheses. Its conclusion is `DSigned I crypto n G`.
- [x] 6. **History formedness** (SPEC item 1). Assume `SigOn … G sG`, `SigHist I crypto n sG bs ts` and `FoldKOut n q (genesisState n.val G) (initFloors …) (bs.map Prod.fst) stO out`. Then:
  - every block of `G :: bs.map Prod.fst` is `FormedFrom … G`;
  - there is `T`, the last block of `G :: bs.map Prod.fst`, with `FormedFrom … G T`, `SigOn … T ts`, `T.id = stO.tip_id`, `T.slot = stO.tip_slot` and `T.height = stO.tip_height`.

  The link facts come from the fold step. Look at how `cert_fold_k_sound` gets `linksOk`: `grep -n "linksOk\|childOk" Rust/FoldStep.lean | head`. Generalise the induction over the fold's input state. Repeat for `FoldSchedOut` and `FoldLockOut`; factor through `cert_step_core_be` if the three share it.
- [x] 7. **`rust_deployed_agreement`**. Repair the proof with steps 4–6:
  - every block of `fullChain G bs tl` is `DSigned … G`;
  - the claim's tip is `T`, so the suffix's head links to `T.id`.
- [x] 8. **`rust_deployed_k_agreement`**. As step 7, with the floors.
- [x] 9. **`rust_deployed_sched_agreement`**. As step 7, with the pin.
- [x] 10. **`rust_deployed_lock_agreement`**. As step 7, for `RustFormed … G` and the mode-3 packages.
- [x] 11. **`rust_deployed_ks`**, **`rust_deployed_sched_ks`**, **`rust_deployed_lock_ks`**.
  - `validate_deployed*` = `ok true` gives `cert_verify = ok true`; then apply `hFold`.
  - For `rust_deployed_ks`, case on `hval`: `validate_deployed_k` calls `validate_deployed` first.
  - Each gets `theorem X : MoltPaper.thm_X` and an alias in `Paper/Proofs.lean`, following the pattern there.
- [x] 12. Any other module that uses `RustFormed`, `DSigned`, `Attests*` or the old `ids_ok_formed`: `grep -rln "RustFormed\|DSigned\|AttestsK\|AttestsSched\|AttestsLock\|ids_ok_formed" Rust/ Molt/ Paper/`. Build each.

## Stage C: TypeScript and close-out

- [x] 13. **`ts_deployed_agreement`** (`MoltPetit/TS/TimedResults.lean`).
  - History blocks: admissible from `hUnf`'s `GroundedCert`.
  - Tail blocks: `TSTipSigned` gives the tip `T`. `idsOk` from `certOps.tipSig hc` and `sigsOk` give `TSFormed n sigOps G` by the same induction as step 5.
  - Any lemma that built the old `TSFormed` (`∃ ps`) is replaced.
- [x] 14. **Close-out.** `bash tools/check.sh` ends with "check: all green". No `sorry`; the pins are unchanged.
  - Delete any scratch `.py`/`.json` files in the repo root.
  - Write "In progress: none (Pass 29 complete)".

## STOP

(empty)
