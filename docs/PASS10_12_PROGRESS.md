# Passes 10, 11, 12 Progress Log: Paper Statement Fidelity

Tracking edits to `paper/molt.tex` and findings resolution per `docs/PASS10_12_SPEC.md`.

## Pass 10: Theorem 4 (`thm:sched`) under the Horizon Budget

- [x] **Primary Statement**: Reworked Theorem 4 (`thm:sched`) to make the horizon-budget theorems primary:
  - Title cites `sched_recent_tip_ancestor_agreement_horizon` and `sched_recent_tip_ancestor_mem_horizon`.
  - Hypotheses stated in prose, matching each Lean argument:
    - Scheduled validator on both chains (`validSignedChainSched`).
    - Scheduled signature surface (`SchedUnforgeable`, recency-scoped with $\mathit{now}$, $\Delta$).
    - Hash injectivity over declared-version signatures (Assumption 2, `SignedHashInjective`).
    - Corruption budget `ByzantineBoundedFrom H n (badSched …)`: at most $\fmax$ bad slots in every $n$-slot window starting at or after horizon $H$.
    - Horizon side conditions $H + n \le \mathit{tip}.\mathit{slot} + 1$ for both tips.
    - Recency $\mathit{now} \le \mathit{tip}.\mathit{slot} + \Delta$ for both tips.
    - Sufficient chain length $n < \mathit{length}$ (`hLong`, both for equal-height form, lower chain for membership form).
    - Tip height relation (equal tip heights for agreement; lower-tip height $\le$ taller for membership).
  - Conclusion stated as Lean: equal heights agree on the block $n$ below each tip; unequal heights, lower chain's $n$-deep ancestor block is a block of the taller chain at least $n$ deep.
  - Stated explicitly that there is NO shared-genesis hypothesis; genesis agreement is a consequence (`sched_recent_genesis_agreement_horizon`).
  - Stated corollary: the global-budget `scheduled_client_safety` is the corollary at any $H$ (`byzantineBoundedFrom_of_bounded`).
- [x] **Shorten Realistic Deployment Paragraph**: Shortened the later "A realistic mode-2 deployment, end to end" paragraph to avoid restating the theorem while preserving key operational context (ceremony, $T$ sizing against week-long exposure window, parent-id prefix agreement via `same_block_same_prefix`, and mode-2 certificate global budget limitation `GroundedCertSched` / `sched_recent_certified_suffix_agreement`).
- [x] **Verification**:
  - All cited Lean declarations exist in `Molt/` and `MoltPetit/`.
  - `bash paper/build.sh` built clean without overfull hbox or errors.
  - `bash tools/check.sh` prints `check: all green`.

## Pass 11: Theorem 5b (`thm:lock-gen`) Hypotheses (Audit F-07, F-09)
- [x] **Theorem 5b Statement**:
  - Title cites both `lockstep_client_safety_gen` and `lockstepGen_recent_tip_ancestor_mem`.
  - Stated `validSignedChainLock` on both chains.
  - Stated `hLong` ($2n < \mathit{length}$) explicitly for both chains at equal heights and for lower chain at unequal heights.
  - Stated `hTipHeight` (equal tip heights) for `lockstep_client_safety_gen` ($2n$-deep block agreement $B = B'$).
  - Stated unequal-height agreement via `lockstepGen_recent_tip_ancestor_mem`: the lower chain's $2n$-deep block appears on the taller chain at least $2n$ deep.
  - Retained `lockstepGen_recent_genesis_agreement` for prefix agreement and absence of shared-genesis hypothesis.
- [x] **§2 Overview Sentence (F-09)**:
  - Updated §2 overview paragraph to clarify that depth-$2n$ agreement holds at equal tip heights via `lockstep_client_safety_gen`, while unequal heights are captured by `lockstepGen_recent_tip_ancestor_mem`.
- [x] **Verification**:
  - Both Lean names exist in `Molt/` and `MoltPetit/`.
  - `bash paper/build.sh` runs with zero overfull/underfull warnings and zero errors.
  - `bash tools/check.sh` prints `check: all green`.

## Pass 12: Remaining Audit Findings F-01..F-11
- [ ] Pending.
