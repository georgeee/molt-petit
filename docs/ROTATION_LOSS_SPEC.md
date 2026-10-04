# Pass 18: modes 2 and 3 against key loss

Prove `MoltPetit.Model.sched_loss_agreement` and
`MoltPetit.Model.lockstep_loss_agreement` in
`MoltPetit/Model/KeyRotationLossSchedLock.lean`. Both statements are pinned by
`Molt/AxiomsRotationLoss.lean`. Do not edit the statements, anything under `Molt/`,
`lakefile.toml` or `paper/molt.tex`.

## Plan

Copy the proof of `keyrot_loss_agreement` (MoltPetit/Model/KeyRotationLoss.lean)
verbatim, changing only the two validator facts:

- **ValidChain:**
  - mode 2: `validChain_of_validSignedChainSched hVal` (KeyStealingSchedule.lean).
  - mode 3: `rw [validSignedChainLock, Bool.and_eq_true, Bool.and_eq_true] at h2;
    exact (validChainK_sound h2.1.2).1`, as in `lockstepGen_recent_tip_ancestor_agreement`.
- **SignedDeclared membership** (replaces `signedDeclared_of_mem`):
  - mode 2: `signedDeclared_of_mem_sched hVal hB`.
  - mode 3: `signedDeclared_of_mem_lock hVal hB` (KeyStealingLockstepGen.lean).

Everything else is identical: `hAvail` from `hbridge`, `le_total` on the lengths,
`timed_tip_ancestor_agreement`, then `same_block_same_prefix_timed`.

Gate: `bash tools/check.sh` prints `check: all green`.
