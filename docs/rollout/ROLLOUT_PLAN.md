# Rollout plan — the post-annotation Lean work

Status: **planning complete, implementation starting.** Companion to `docs/rollout/ROLLOUT_NOTES.md`
(ground rules, paper-change ledger, touched-file log) and `docs/rollout/` (the full designs,
verdicts, maps, and salvage this plan is built from). This file is the single place
that says, at any moment, what order things happen in and why — update it as each
item lands.

## How this plan was built

Eight work items were identified from George's 34 PDF annotations on `paper/molt.tex`
(recorded in `docs/rollout/ROLLOUT_NOTES.md` §1). For each: a Fable-5 agent produced a full Lean
design (file layout, exact theorem statements with complete hypothesis lists, proof
sketches naming the existing lemmas they compose, dependencies, paper changes, risks,
rejected alternatives); a second pass adversarially reviewed every substantial design
against the live source on two lenses (reuse-claim accuracy; the additive-only
constraint and ordering); a third pass fixed every design that came back with a
blocking or major finding. Every design, verdict, and fixup note is preserved in
`docs/rollout/designs/*.json` (plus `.md` digests) and `docs/rollout/verdicts/*.json`. Two design
runs died mid-flight on usage limits before this final pass; their salvaged surveys
(`docs/rollout/designs-partial/*.md`) fed the successful redesign and are kept for the
record. Full blow-by-blow: `docs/rollout/journal-scan.md`.

**Two things surfaced during review that are worth knowing before reading the designs:**

- **W4's designer wrote the entire design, then actually compiled it** against the live
  repo and toolchain in a scratch file (`Molt/ZZZScratchW4.lean`, deleted before
  returning; `git status` confirmed clean). All four declarations compile with zero
  `sorry`, and the exact axiom sets were measured, not guessed. This is the
  lowest-risk item in the plan.
- **W6 was asked to derive per-mode no-back-dating from a timed model and could not** —
  not because of the owner's known rejection of `NoBackdate` on stolen keys, but for a
  structural reason independent of it: the existing EUF-CMA surfaces
  (`KeyStealingEUFCMA`, `SchedCoreUnforgeable`) are premised on a single key *version*
  being safe, while a timed custody argument only ever delivers "the whole real slot is
  safe" — and one slot can host one safe key and one stolen key at once. The design
  proves this obstruction as two small Lean theorems (a slot with a provably-safe
  key that is nonetheless bad) rather than attempting an unsound or over-strengthened
  derivation. Recommendation: a text-only paper assumption plus the two witness
  theorems, not a positive derivation. This is the right call and the plan follows it.

## Summary

| item | title | design status | size | effort | headline risk |
|---|---|---|---|---|---|
| W6 | No-back-dating: obstruction witness + text-only assumption | **landed** (2026-09-10) | 133 | 0.3 session | none — mechanical, confirmed |
| W4 | Induction over syncs (abstract engine + full-chain instance) | **landed** (2026-09-10) | 167 | 1 session | none — confirmed, matched the prior scratch-build exactly |
| W3a | Timed theft layer for mode 1 (`Reacts`, trailing budget) | **landed** (2026-09-10) | 391 | 1 session | none — confirmed |
| W2 | Mode 1 anchored/trailing-5n at certificate level | **landed** (2026-09-10) | 491 | 1-2 sessions | none — confirmed |
| W1 | Mode 3 (lockstep) at certificate level | **landed** (2026-09-10) | 712 | 2-3 sessions | none — confirmed |
| W5 | Mode 3 per-generation census (D1'-full) | **landed** (2026-09-11) | 1400 | 3-4 sessions | none — confirmed; one optional consistency witness (`exposedBound_not_of_genBound`) dropped to prose per the design's own escape hatch (Finset decidability diamond) |
| W3b | Time-aware signature surface (larger F_max) — **stretch** | **landed** (2026-09-11), full scope including the separation theorems | 363 | 2 sessions | none — confirmed |
| W7 | Multi-chain liveness — **deferred, not attempted** | sketch, SKIP recommended | — | — | — |

*W3b's own review verdict predates the fixup that wrote its final content from
scratch (the verdict's one blocking finding was "no design exists"; the fixup wrote
one). The design itself is well-grounded (cites exact file:line throughout, was
cross-checked against W3a's finalized design) but has not had a fresh accuracy/ordering
pass against its *final* content. Treated as needing extra care during implementation,
not as unreviewed.

## Implementation order

Chosen by ascending size/risk within the dependency-free set the review identified
(every item among W1/W2/W3a/W4/W5/W6 is additive purely against the existing baseline,
not against any other item's new content — confirmed by every design's own
`depends_on` and cross-checked by the ordering-lens reviews). **Strict sequential
execution, one item fully built, guarded, and committed before the next starts** —
not because the designs require it, but per George's instruction, and because
serializing `lake build` avoids any risk of two builds racing on the shared `.lake`
cache.

1. **W6** — smallest, zero dependencies, purely additive witness theorems + a paper
   assumption. Good first item: low risk, and it retires a real honesty gap early.
2. **W4** — already compiled once; pasting in verified content with docstrings.
3. **W3a** — self-contained timed layer, mirrors an existing mode-2 module closely.
4. **W2** — cert-level engine; unlocks W3b later.
5. **W1** — self-contained mode-3 cert-level engine.
6. **W5** — the deep one (new aligned-window contraction engine, non-inductive
   per-window pinning, 2n confirmation depth). Last of the core six on purpose.
7. **W3b** *(stretch, only if 1-6 land cleanly)* — hard-depends on W3a's exact
   final names (`Reacts`, `recentTheftProducersK`, `budget_of_reaction`,
   `Molt.max_sync_period_timed`), so cannot start before step 3 lands. Its own
   recommendation: land the census-tightening chain and `max_sync_period_tight`
   first as a complete sub-delivery; treat the paced-schedule separation theorems
   (the genuinely new arithmetic) as a further stretch within the stretch.
8. **W7** — **not attempted.** Every version of its own design recommends skipping
   it: the adversary-free "cheap" version is honest but nearly vacuous (it doesn't
   exercise `selectChain`'s actual discriminating behavior, so citing it against the
   paper's "future work" sentence would overstate what was proved), and the
   adversary-bearing version that would actually earn the paper change is 4-6
   sessions of new machinery with no other item depending on it. Revisit only if a
   reviewer specifically pushes on multi-chain liveness.

## Loop risks (from the review; watch for these during implementation)

- **Root-file touches.** All six core items append import lines to `MoltPetit.lean`
  and/or `Molt.lean` (the one permitted touch). Since items build in sequence, each
  item's import lines land in one commit with no merge risk — but double-check the
  anchor line each design names still exists at that point (a prior item's own import
  addition may have shifted what "after line N" means; match by content, not line
  number).
- **W3b's integration has no anchor until W3a's root-file imports actually land** —
  W3b's own `touches_existing` says "immediately after W3a's import"; do not attempt
  W3b's integration before step 3 is fully committed.
- **A future session may re-read only the original planner hypothesis for W6** (the
  three-step bridge/custody/no-back-dating sketch) without this plan's obstruction
  finding, and re-attempt a derivation that is provably unsound or silently
  over-strengthens `KeyStealingEUFCMA`/`SchedCoreUnforgeable`. W6's two witness
  theorems exist specifically so that attempt is directed to read them first.
- **W4's `enables → W2` is aspirational, not yet real**: it assumes a certificate-level
  "mem"-shaped per-sync lemma that W2's `cert_sync_rule` (equal-height only) does not
  provide. Ship W4 now against the full-chain presentation
  (`Molt.sync_rule_mem`) only; do not claim the certificate-level induction is ready.
- **W1 and W5 have soft, informational cross-links** (a possible future W1×W5 join at
  the lockstep certificate + per-generation census) — not a dependency in either
  direction for what lands now; do not let it gate scheduling.
- **Building W7's cheap version "to save time later" is exactly the redo-loop the
  no-loops rule exists to prevent** — its own design confirms the plumbing is not
  reusable once a real adversary is added. This is why W7 is skipped outright, not
  built small-then-extended.

## Missing items (named by the review; explicitly out of scope for this rollout)

- No item derives `NoTheftBackdating` (W3b's core new hypothesis) from an actual
  mint-time-aware EUF-CMA primitive — flagged by both W3a and W3b as a distinct,
  much larger follow-on (comparable in size to the whole `KeyStealing*.lean` stack).
- W3b's paced-separation theorems have no witnessed chain `c0` demonstrating its three
  hypotheses are jointly satisfiable (flagged as +100-150 lines, not in its estimate).
- No item builds the certificate-level "mem"-shaped per-sync lemma W4's `enables → W2`
  would need (see loop risks above).
- No item revisits `KeyStealingEUFCMA`/`SchedCoreUnforgeable`'s per-key-vs-per-slot
  premise shape — the one edit W6 identifies as the actual unlock for a positive
  no-back-dating derivation. Explicitly out of scope: that is an edit to an existing
  assumed structure, not an addition, and needs its own review track.
- No TS/Rust extraction-side bridge for W1's `lockstepFrom` (separate future item).
- Several cheap naming/wording open questions (Molt-side alias vs fresh-definition
  choice for W1/W5/W6, W2's anchor-reach and previous-sync-form, W4's
  Δconf-generic-vs-fixed) are listed per-item in `docs/rollout/designs/*.json`
  `open_questions_for_owner`. None block Lean engineering; worth resolving before the
  eventual paper pass so names are not re-litigated then.

## Execution protocol (per item)

1. Read the item's full design at `docs/rollout/designs/<KEY>.json`.
2. Write the new Lean file(s) exactly as specified (file layout, definitions, theorem
   statements, proof sketches as the starting point — expect to iterate against real
   compiler errors, since proof sketches are sketches, not verified scripts, except
   for W4 which was compiled once already).
3. `/etheron-pod/toolchains/lake.sh build <new module(s)>` standalone until clean.
4. Add the axiom guards: probe with a bare `#print axioms <name>` first, copy the
   emitted message into the `#guard_msgs` docstring verbatim (do not hand-write it —
   several existing guards wrap at ~100 columns or report a shorter-than-usual axiom
   list, and copying wrong fails the build or asserts an inaccurate claim).
5. Add the root-file import lines (the one permitted touch), matching each design's
   `touches_existing` entry by content.
6. `/etheron-pod/toolchains/lake.sh build MoltPetit Molt` — the full default build,
   clean, all four axiom-guard files enforced.
7. Update `docs/rollout/ROLLOUT_NOTES.md` §2 (only if an existing file was touched beyond imports —
   should not happen) and §3 (new Lean added), and this file's status table.
8. Commit, referencing the item key and the design file. Do not push unless asked.
9. Only then move to the next item.

The paper (`paper/molt.tex`) is not touched at any point in this protocol. Each
item's `paper_changes` entries stay recorded in `docs/rollout/ROLLOUT_NOTES.md` §1 for a later,
separate pass.
