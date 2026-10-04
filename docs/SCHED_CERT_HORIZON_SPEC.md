# Pass 17: mode-2 certificates under the horizon-scoped budget

Prove `MoltPetit.Model.sched_recent_certified_suffix_agreement_horizon` in
`MoltPetit/Model/KeyStealingScheduleCertHorizon.lean`. The statement is pinned by
`Molt/AxiomsSchedCertHorizon.lean` (axioms: propext, Classical.choice, Quot.sound).
Do not edit the statement, the guard, or `paper/molt.tex`.

## Plan (mirror two existing proofs)

1. Copy the first half of `sched_recent_certified_suffix_agreement`
   (KeyStealingScheduleCert.lean): `groundedCertSched_suffix_history` twice, then
   `exists_signedChain_of_covered`, giving `hVal`/`hVal'` for
   `validSignedChainSchedCore`, the full tips `hfullTip`/`hfullTip'`, the blocks
   at global index `k := c.length + i` (`hBfull`, `hB'full`), and the length
   bounds `k + n < (stripSigs sc).length` and the same for `sc'`.
2. Replace the final `sched_deep_block_agreement_core_of_length` call with the body
   of `sched_recent_tip_ancestor_agreement_horizon_core`
   (KeyStealingScheduleHorizon.lean): `validChain_of_validSignedChainSchedCore`,
   `signedDeclared_of_mem_schedCore`, `idInjective_keyrot`; split on
   `Nat.le_total sTip.slot sTip'.slot`; `honestSlotsUnique_schedCore`; then
   `horizon_shared_prefix hn hUniq hId hVc hVc' chainInRecord_left
   chainInRecord_right hTip hTip' hle (hBudget _ (by omega)) (k := k) hk`, where
   the budget index is the lower tip's `tip.slot + 1 - n ≥ H` (from `hH`/`hH'`),
   and `hk` is the length bound for the lower-slot chain. Rewrite with `hBfull` and
   `hB'full` to get `B = B'`.

No new lemma should be needed beyond small helpers. Gate: `bash tools/check.sh`
prints `check: all green`.

# Pass 17, part 2: mode-3 certificates under the per-generation census

Prove `MoltPetit.Model.lockstepGen_recent_certified_suffix_agreement` in
`MoltPetit/Model/KeyStealingLockstepCertGen.lean` (pinned by
`Molt/AxiomsLockstepCertGen.lean`). Plan: as in
`lockstep_recent_certified_suffix_agreement`, use `groundedCertLock_signedChain`
twice to get `sc`, `sc'` with `validSignedChainLock`, the full tips, and the blocks
at global index `k := c.length + i` (`hBfull`, `hB'full` after `hkEq`). Then
split on `Nat.le_total sTip.slot sTip'.slot` and close with
`lockstepGen_shared_prefix_deep hn hP hValL hValL' hfullTip hfullTip' hRecent
hRecent' hle hBfull (k := k) (by …)` (needs `k + 2 * n < length` of the
lower-slot chain, from `hDeep`/`hDeep'`), as in
`lockstepGen_recent_tip_ancestor_agreement`. No pin conversion through
`lagSched` is needed.
