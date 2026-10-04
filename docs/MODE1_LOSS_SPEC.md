# Pass 16 spec: mode 1 against key loss

Reviewer-owned. The pinned statement is `MoltPetit.Model.keyrot_loss_agreement` in
`MoltPetit/Model/KeyRotationLoss.lean`. `Molt/AxiomsKeyRotationLoss.lean` pins its type and
axioms; do not edit it. Replace the `sorry`, and add no new hypotheses, axioms or `sorry`.

## Proof plan

Mirror `timed_certified_agreement` (MoltPetit/Model/TimedSafetyCert.lean, from line 57 on),
with `full := stripSigs sc`.

1. Get `ValidChain n (stripSigs sc)`: `rw [validSignedChainK', Bool.and_eq_true] at hVal`, then
   `(validChainK'_sound hVal.2).1` (see KeyStealingHorizon.lean:96 for the same idiom). Do the
   same for `sc'`.
2. Show every block of `stripSigs sc` is `SignedDeclared n ops registry`, from `hVal.1 : sigsOk …`.
   `sigsOk` is `sc.all (sigOk n ops registry)`; look at how `sigOk` is defined (Definitions.lean)
   and at existing lemmas that turn `sigsOk` into per-block verification (grep `sigsOk_` and
   `SignedDeclared`). The witness `sig` is the block's own signature.
3. `hAvail : ∀ B ∈ stripSigs sc, AvailableAt log G B R` is `Or.inr (hbridge (step 2))`. Do the
   same for `sc'`.
4. Finish exactly as `timed_certified_agreement` does: case on `le_total` of the lengths, apply
   `timed_tip_ancestor_agreement`, then `same_block_same_prefix_timed` down to height `h`.

## Done when

`bash tools/check.sh` prints `check: all green`. Record progress in `docs/MODE1_LOSS_PROGRESS.md`.
Commit small steps on publish-prep. Never push, never switch branches. Do not edit
`paper/molt.tex`.
