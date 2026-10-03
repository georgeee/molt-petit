# Audit Findings Resolution (F-01..F-11)

Resolution of audit findings from `verify-out/findings.md` per `docs/PASS10_12_SPEC.md`.

## [F-01] Circuit backend trust assumption in abstract
- **Status**: Fixed at Abstract.
- **Resolution**: Qualified in the abstract that all safety claims are machine-checked under the cryptographic and operational assumptions of Section 5, and that circuit-backend faithfulness is a stated trust assumption.

## [F-02] Shipped validator timed certified safety theorem citation
- **Status**: Fixed at Section 1 (Intro) and Section 7 (Implementation and measurements).
- **Resolution**: Cited `Rust.rust_timed_certified_agreement` under the assumptions of Section 5 in Section 1 (Introduction) where the machine-checked guarantee on shipped validator code is claimed. Added `Rust.rust_timed_certified_agreement` to the list of theorems carried to the shipped code in Section 7 under the timed model and certificate bridge.

## [F-03] Circuit backend equivalence qualification in intro
- **Status**: Fixed at Section 1 (Intro).
- **Resolution**: Clarified that circuit backend faithfulness is a stated trust assumption rather than a Lean-verified equivalence.

## [F-04] Liveness produce block lemma characterization
- **Status**: Fixed at Section 2 (Mode 0).
- **Resolution**: Clarified that `liveness_produce_blockK` is a local single-block production lemma taking continued density coverage as a hypothesis, rather than a dynamic protocol recovery theorem.

## [F-05] Mode 3 certificate presentation budget scope in overview
- **Status**: Fixed at Section 2 (Mode 3).
- **Resolution**: Clarified that Mode 3 certificate presentation guarantees hold under the cumulative budget at depth $n$ (`lockstep_recent_certified_suffix_agreement`), while per-generation credit at depth $2n$ is proved for full chains and remains future work for certificates.

## [F-06] Untimed residue derivation assumptions
- **Status**: Verified already fixed in Pass 9 at Section 6.1 and Appendix A (Theorem 8, `thm:timed-uniq`).
- **Resolution**: Not a defect in current text. Pass 9 reframed Theorem 1 to be natively timed (`timed_light_client_safety`) and moved the untimed residue derivation `sigUnforgeableRecent_of_timed` to Appendix A, where it explicitly states the requirement of `NoBackdate` (forward-secure custody) and notes that recency is slack/unused in the proof.

## [F-07] Theorem 5b (`thm:lock-gen`) hypotheses and unequal heights
- **Status**: Fixed in Pass 11 at Section 6.3 (Theorem 5b, `thm:lock-gen`).
- **Resolution**: Explicitly stated `hTipHeight` (equal tip heights) and `hLong` ($2n < \mathit{length}$) for `lockstep_client_safety_gen`, and distinguished equal-heights agreement from unequal-heights membership via `lockstepGen_recent_tip_ancestor_mem`.

## [F-08] Mode 3 certificate presentation under cumulative budget vs per-generation credit
- **Status**: Fixed at Section 6.3 and Section 6.3 Honest Scope.
- **Resolution**: Clarified that Mode 3's certificate presentation theorem is established only under the cumulative budget at depth $n$, and that lifting certificates to per-generation erasure credit at depth $2n$ (as well as Mode 2 certificates to horizon budgets) remains future work.

## [F-09] Section 2 Mode 3 overview sentence on depth-2n agreement
- **Status**: Fixed in Pass 11 at Section 2 (Mode 3).
- **Resolution**: Clarified that depth-$2n$ agreement holds at equal tip heights via `lockstep_client_safety_gen`, while unequal heights are captured by `lockstepGen_recent_tip_ancestor_mem`.

## [F-10] Counting argument role as combinatorial engine
- **Status**: Fixed at Section 3.2.
- **Resolution**: Clarified in one clause that the counting argument is the core combinatorial engine around which cryptographic unforgeability, certificate grounding, and rotation pin mechanisms are layered and machine-checked.

## [F-11] Certificate presentation fault budgets for Modes 2 and 3
- **Status**: Fixed at Section 4.
- **Resolution**: Clarified that Mode 2 and Mode 3 certificate theorems (`sched_recent_certified_suffix_agreement` and `lockstep_recent_certified_suffix_agreement`) are proved under global/cumulative budgets at depth $n$.
