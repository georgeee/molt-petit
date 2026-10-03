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
- [x] **Audit Findings Resolution (F-01..F-11)**:
  - **F-01, F-03**: Qualified in the abstract and intro that circuit-backend faithfulness is a stated (audited) trust assumption rather than a Lean-verified equivalence, and that all safety claims hold under the named cryptographic and operational assumptions of §5.
  - **F-02**: In intro "machine-checked theorem about the shipped validator code", cited `Rust.rust_timed_certified_agreement` under the assumptions of Section 5. Added it to §7 among theorems carried to the shipped code.
  - **F-04**: Described `liveness_produce_blockK` in §2 as a local single-block production step taking continued density coverage as a hypothesis rather than proving dynamic protocol recovery.
  - **F-05, F-08, F-11**: Clarified across §2, §4, §6.3, and §6.3 Honest Scope that Mode 2 and Mode 3 certificate presentation theorems are proved under cumulative/global budgets at depth $n$, and that lifting certificates to per-generation erasure credit at depth $2n$ (and Mode 2 to horizon budgets) remains future work.
  - **F-06**: Verified that Pass 9 already addressed the untimed residue derivation `sigUnforgeableRecent_of_timed` in Appendix A with `NoBackdate` and slack recency.
  - **F-07, F-09**: Addressed in Pass 11 (Theorem 5b hypotheses and §2 overview sentence).
  - **F-10**: Clarified in §3.2 that the counting argument is the core combinatorial engine around which cryptographic, grounding, and rotation pin layers sit.
- [x] **Documentation**:
  - Created `docs/FINDINGS_RESOLUTION.md` documenting resolution of all findings F-01..F-11.
  - Ticked Pass 12 in `docs/PUBLISH_PREP_STATUS.md`.
- [x] **Verification**:
  - `bash paper/build.sh` runs clean with zero errors.
  - `bash tools/check.sh` prints `check: all green`.
