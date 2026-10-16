# Pass 31: remove three more disclosed limits (signed liveness in modes 2 and 3, two check times for the TypeScript client, the mode-free certificate)

From review-12 (Q6 items 1, 2, 4). Scaffold: commit "pass31 scaffold".

## S1. Signed liveness, modes 2 and 3 (new statements)
`thm_sched_liveness_produce_signed_block`, `thm_lockstep_liveness_produce_signed_block`
(Spec/Statements.lean, just before `LockstepPackageTimed.thm_toGen`). The unsigned
`sched_liveness_produce_block` / `lockstep_liveness_produce_block` stay as they are.
Proof (MoltPetit/Model/KeyRotationLiveness.lean, next to them), the same pattern as
`liveness_produce_signed_blockK` (line 161): the produced block comes from
`liveness_produce_signed_block`; `SigCorrect` gives
`ops.verify (registry me keyIndex) nb (ops.sign (keyPair me keyIndex) nb) = true`;
then apply the unsigned theorem with that `sig` for the validator conjunct.

## S2. Two real check times for the TypeScript client (in place)
`thm_ts_deployed_agreement` now takes `{R R' d : Nat}`, `hbridge` at `max R R'`,
`hφ : Δ + δ + d ≤ φ`, `hNow : (R : Int) ≤ now + δ`, `hNow' : (R' : Int) ≤ now' + δ`,
`hRR : R ≤ R' + d ∧ R' ≤ R + d`.
Proof (MoltPetit/TS/TimedResults.lean:227): rename the current proof to a private
`ts_deployed_agreement_one_time` with the old statement (copy it from
`git show <scaffold>~1:Spec/Statements.lean`), then instantiate at `R* := max R R'`,
`δ* := δ + d`; side conditions by `omega` (casts: `push_cast`). Same as
`rust_deployed_agreement` in Rust/Deployed.lean:3598.

## S3. The mode-free certificate (in place)
Spec/RustBridge.lean now defines `FoldCoreOut` (core step + `cert_next_tail_be`, like
`FoldSchedOut` without the pin) and `AttestsCore`. `thm_rust_deployed_agreement` takes
`AttestsCore` instead of `AttestsK` (and no `out`, `out'`).
1. **Name clash.** Rust/Deployed.lean:2285 defines a weaker `Rust.FoldCoreOut` (no tail
   link). Rename it and every use in Rust/Deployed.lean to `FoldCoreLoose`; add
   `foldCoreOut_to_loose : FoldCoreOut n q st bs stO → FoldCoreLoose n q st bs stO`.
   Add `foldKOut_to_coreOut`, `foldSchedOut_to_coreOut` (`foldLockOut_to_coreOut` if useful)
   into the Spec `FoldCoreOut`: the same inductions as `foldKOut_to_core` etc., keeping the
   `cert_next_tail_be` conjunct.
2. **Soundness of the core fold** (Rust/FoldStep.lean, after `cert_fold_sched_sound`): copy
   the induction of the lemma right before `cert_fold_sched_sound` (line ~1195) without
   `cert_step_sched_be_sound` / the pin: from `cert_step_core_be_sound` and
   `MoltPetit.Model.GroundedCert.extend` (or the constructor `GroundedCertSched.extend`
   mirrors) get `GroundedCert`. Also `stateView_of_foldCoreOut` (mirror
   `stateView_of_foldSchedOut`, line 2025).
3. **History** (Rust/Deployed.lean): `foldCore_history_aux` (mirror `foldSched_history_aux`,
   line 3116, without the pin) and `attestsCore_history` returning
   `GroundedCert ∧ GroundedHistory ∧ stateView n.val stO = claimView cl₀`
   (mirror `attestsSched_history`, line 3185).
4. **The theorem.** Change `rust_deployed_agreement_one_time` to take `AttestsCore` and use
   `attestsCore_history` where it used `attestsK_history` (it only uses `hcert, hhist, hview`).
   Fix callers: `rust_deployed_k_agreement` (line ~3715) passes
   `⟨hA.1, foldKOut_to_coreOut hA.2⟩`; likewise any sched caller.

## Close-out
`Paper/Proofs.lean`: entries for the 2 new S1 theorems; `lake build Paper.Proofs`; then a
full `lake build` with no sorry; axioms only propext/Classical.choice/Quot.sound.
