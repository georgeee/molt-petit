# Passes 10, 11, 12 (+ Rust headline wiring): paper statement fidelity

Reviewer-owned; decisions final. Edit `paper/molt.tex` and docs only. No Lean edits.
Every Lean name you cite must exist (grep Molt/ MoltPetit/ Rust/). Theorem statements in
the paper must match their Lean statements: every hypothesis the Lean theorem takes
appears in the paper statement (in prose), and nothing stronger is claimed.

## Pass 10 — Theorem 4 (`thm:sched`) under the horizon budget
Primary statement: `sched_recent_tip_ancestor_agreement_horizon` (equal heights) and
`sched_recent_tip_ancestor_mem_horizon` (unequal heights), MoltPetit/Model/KeyStealingScheduleHorizon.lean.
Title cites both. Hypotheses in prose, one per Lean argument: scheduled validator
(`validSignedChainSched`) on both chains; scheduled signature surface (`SchedUnforgeable`,
recency-scoped with `now`, `Δ`); hash injectivity over declared-version signatures;
the corruption budget `ByzantineBoundedFrom H n (badSched …)` — at most `fmax` bad slots in
every `n`-slot window starting at or after a horizon `H`; the horizon side conditions
`H + n ≤ tip.slot + 1` for both tips; recency `now ≤ tip.slot + Δ`; `hLong` (both, equal
form; lower chain, membership form); tip height relation. Conclusion as Lean. State that
there is NO shared-genesis hypothesis (genesis agreement is a consequence,
`sched_recent_genesis_agreement_horizon`). Then one sentence: the global-budget
`scheduled_client_safety` is the corollary at any `H` (`byzantineBoundedFrom_of_bounded`).
Shorten the later "realistic mode-2 deployment" paragraph so it does not restate the theorem.

## Pass 11 — Theorem 5b (`thm:lock-gen`) hypotheses (audit F-07, F-09)
State `hTipHeight` (equal tip heights) and `hLong` (`2n <` length) explicitly, exactly as
`Molt.lockstep_client_safety_gen`. Unequal heights: cite
`lockstepGen_recent_tip_ancestor_mem` (check it exists and its exact conclusion) as in
`thm:lock`. Fix the §2 overview sentence (F-09) the same way.

## Pass 12 — audit findings F-01..F-11 (`verify-out/findings.md`)
Resolve each; line numbers there are stale, find by content.
- F-01, F-03: abstract and intro: circuit-backend faithfulness is a stated (audited) trust
  assumption, not a Lean theorem; the Lean results hold under the named cryptographic and
  operational assumptions of §5. Keep it to one clause each; do not weaken real claims.
- F-02: intro "machine-checked theorem about the shipped validator code": cite
  `Rust.rust_timed_certified_agreement` (Rust/TimedResults_rust.lean), the timed certified
  theorem for the Rust validator, and say "under the assumptions of Section 5".
  (If that theorem is not yet proved when you run — check `lake build Rust.AxiomsTimed` —
  cite it anyway; the reviewer gates it.) Also add it to §7 / the results table wherever
  Rust corollaries are listed.
- F-04: `liveness_produce_blockK` described as a single-block production step that takes
  density coverage as a hypothesis.
- F-05, F-08, F-11: mode-3 (and mode-2) certificate theorems are proved under the
  cumulative/global budget at depth `n`; say so wherever certificate presentation is
  claimed for modes 2/3; per-generation/horizon at certificates is future work.
- F-06: verify Pass 9 already fixed it (the residue derivation needs `NoBackdate`); fix if not.
- F-10: one clause: the counting argument is the combinatorial core; cryptographic,
  grounding and pin layers sit around it.
- F-07, F-09: Pass 11.
Write `docs/FINDINGS_RESOLUTION.md`: for each F-xx, "fixed at <section>" or why it is not a
defect.

## Done when
`bash tools/check.sh` prints `check: all green`; Passes 10, 11, 12 ticked in
`docs/PUBLISH_PREP_STATUS.md`; `docs/FINDINGS_RESOLUTION.md` covers F-01..F-11.
