# Rollout notes — the post-annotation Lean work (started 2026-09-05)

Companion to `docs/rollout/ROLLOUT_PLAN.md`. Ground rules for this arc, from George:

- **The paper is not edited until the Lean lands.** Everything that will change in
  `paper/molt.tex` is logged in §1 below as it becomes known, with the phrase to
  grep for, so the edit can be made in one targeted pass per page later.
- **New Lean only.** New modules, new definitions, new theorems. Nothing existing is
  modified. The only touches permitted to existing files are (a) one import line per
  new module in a root module (`MoltPetit.lean`, `Molt.lean`) and (b) new axiom-guard
  files rather than edits to an existing `Axioms.lean`. Every touch is logged in §2.
- Axiom hygiene as in `CLAUDE.md`: every new headline theorem gets a `#guard_msgs`
  guard; `#print axioms` must yield exactly `[propext, Classical.choice, Quot.sound]`.

Build in this container (see `/etheron-pod/toolchains/lake.sh`):

    /etheron-pod/toolchains/lake.sh build MoltPetit.Model.<NewModule>
    /etheron-pod/toolchains/lake.sh build MoltPetit Molt      # everything + guards

## 1. Paper changes pending (do NOT apply yet)

Keyed by the work item that unlocks them and the annotation that asked. Locations are
given by section and a grep-able phrase (line numbers drift).

| Unlocked by | Annotation | Where in `paper/molt.tex` | What changes |
|---|---|---|---|
| W1 | AN/9a, AN/28, AN/30 | §2 mode 3 paragraph, phrase `currently proved for full chains` | drop the parenthetical's first clause once the certified lockstep theorem exists |
| W1 | AN/28 | §6.3 "A realistic mode-3 deployment", phrase `verifying the full signed chain on wake, since the certificate presentation is future work` | replace with the certificate recipe (fetch certificate + suffix, verify, recency), cite the new Lean name |
| W1 | AN/30 | §6.3 "Honest scope", phrase `Third, mode 3's theorems are about full chains` | delete the third bound |
| W1 | — | §4 Validate, item 5, phrase `future work for mode 3` | cite the new certified lockstep theorem next to the mode 1–2 names |
| W1 | — | §6 intro sentence `keyrot_recent_certified_suffix_agreement and its scheduled twin` | add the lockstep twin |
| W2 | AN/21 | §6.3 mode 1, phrase `carrying the anchored, trailing-$5n$ form to certificates is future work` | replace with the new certified anchored theorem name; the deployment walkthrough's conclusion can then be stated for the certificate client |
| W3a | AN/20, AN/17 | §6.3 mode 1, the paragraphs `Why the cadence cannot simply be enlarged` and `The standing assumption is then` | state the budget in the derived form (theft rate + reaction bound ⇒ trailing budget), cite the derivation; possibly quote the theorem in the one-line form |
| W3a/W3b | AN/24, AN/29 | §6.3 mode 1 `theft \emph{times} inside the signature assumptions`; "Honest scope" first bound `distinguishing thefts before a block's creation` | rewrite according to what lands (W3a: theft times as a derivation layer; W3b: non-retroactive census) |
| W4 | AN/26 | §6.3 mode 1 walkthrough, phrase `argued on paper, not itself machine-checked` and `an informal argument` | cite the machine-checked induction; keep the honest-tip-recency side condition as a stated hypothesis |
| W5 | AN/9b | §2 mode 3 paragraph `erasure's per-generation credit against the budget is designed but not yet formalized`; §6.3 "Honest scope" second bound; mode 3 operator duties `(its budget credit: honest scope below)`; modes table erasure column | state the per-generation budget and cite it |
| W6 | AN/34b | Appendix `What no-back-dating is`; each mode's "What must then be true of the world" list; §Limitations "Named seams" phrase `assumed, not derived from the timed model` | either list no-back-dating per mode as a named operational assumption (text-only variant) or cite the per-mode derivation |
| W7 | AN/31 | §6.4, phrase `a fully multi-chain network model is future work` | only if W7 is done |
| — | AN/27 | none (design question) | a short design note answering the VRF-derived-key idea; not a paper change unless George wants it in Limitations |

Also carried from the annotation round (not Lean-gated, George's call):

- AN/15: the dropped sentence was the paper's only disclosure that the representability
  lemmas are production-side only; Theorem 1's "exposes that height" hypothesis now has
  no stated reason for not being proved away.
- Page count moved 17 → 18 with the annotation edits.
- AN/23: a one-clause cross-reference at the `F_max = S - 4n` formula back to "Two
  readings of the budget clause" would stop the re-read.
- `paper/build.sh` does not run in this container (see `/etheron-pod/toolchains/lake.sh`
  header and the agent memory for the derivation-based PDF build).
- `paper/molt.pdf` on disk is the pre-annotation build.

## 1b. Answers to the question-annotations (2026-09-04, not yet in the paper)

These annotations asked questions rather than requesting edits. The answers were
given to George in chat; recorded here so they are not re-derived.

**AN/23 — "would it follow from rho+T < f for F=n?"** Yes, and the paper already
says so three paragraphs above where the question was asked: a deployment keeping
rho+T within f on every window from genesis satisfies the hypothesis outright, and
`client_refresh_rule` at `A :=` genesis recovers the lifetime statement exactly.
`F_max = S - 4n` at `S = 5n` gives `F = n`, the sync rule. The point of the
trailing form is that it demands strictly *less*. A one-clause cross-reference at
the `F_max` formula would prevent the re-read (listed in the carried items below).

**AN/21 — "carrying the anchored trailing-5n form to certificates: what will it
buy us?"** Today the certified mode-1 theorem holds only under the global
all-window budget, i.e. the lifetime assumption the paper argues no deployment can
defend under key theft. So the constant-size client — the client the paper is
written for — does not get the two-minute budget; only a full-chain client does.
Closing it removes a gap between the headline claim and the certified form. This
is work item **W2**, now designed.

**AN/29 — "what would the theft-timing work buy; necessary or vain curiosity?"**
Not vain, not necessary. It removes the retroactive census, which is the one thing
forcing the n-slot cadence: with theft times a theft charges only windows at or
after it, so the budget stops being a per-stretch total and becomes closer to a
concurrency bound — far easier for an operator to attest — and `F_max` rises. It
is the single highest-leverage relaxation available, and it is the same machinery
as **W3a** (derivation layer) and **W3b** (non-retroactive census).

**AN/27 — the VRF-derived-next-key idea.** George's own diagnosis is right and it
is fatal: if `SK_{j+1} = KDF(SK_j, seed)` then a thief of `SK_j` owns every future
generation, so rotation buys nothing and healing — which mode 1's entire budget
rests on — disappears. A public seed does not help; the secret input is `SK_j`.
The nearest workable neighbour is forward security (evolve, then erase `SK_j`),
which fixes back-dating but not forward theft, and the paper already cites it in
the long-range-residual paragraph. Capping forward theft requires that the cold
root not be derivable from the live key — which is the current design. If the
motivation is fewer cold-root ceremonies, the dial that actually moves is the era
length R in mode 2. This is a design judgement, not a proved statement; it is not
a paper change unless George wants it in Limitations.

## 2. Existing Lean touched

Policy: none, except the two kinds of touch listed at the top. Log every one here.

| Date | File | Touch | Why |
|---|---|---|---|
| — | — | — | — |

## 3. New Lean added

| Date | Module | Headline names | Guard file | Status |
|---|---|---|---|---|
| 2026-09-10 | `MoltPetit/Model/KeyStealingTimedScope.lean` | `badSched_single_key_safe_not_enough`, `badKeyrotOn_single_key_safe_not_enough` (W6) | `MoltPetit/Results/AxiomsKeyStealingTimedScope.lean` | landed; `lake build MoltPetit Molt` clean; both axiom-free (`#print axioms` measured, not guessed) |
| 2026-09-10 | `Molt/KeyStealingTimedScope.lean` | `Molt.badSched_single_key_safe_not_enough`, `Molt.badKeyrot_single_key_safe_not_enough` (W6, paper-namespace re-presentation) | `Molt/AxiomsKeyStealingTimedScope.lean` | landed; same build; both axiom-free |
| 2026-09-10 | `Molt/SyncInduction.lean` | `SyncInductionData`, `SyncInductionData.invariant` (axiom-free), `mem_of_blockAt?` (`[propext]`), `sync_induction_full_chain` (W4, the machine-checked induction over syncs) | `Molt/AxiomsSyncInduction.lean` | landed; `lake build MoltPetit Molt` clean; all three axiom sets measured, matched the design's own prior scratch-build exactly |
| 2026-09-10 | `MoltPetit/Model/KeyStealingTimed.lean` | `Reacts`, `recentTheftProducersK`, `exposedProducers_subset_recentTheftK`, `budget_of_reaction`, `anchored_budget_of_reaction` (W3a, the timed theft layer for mode 1) | `MoltPetit/Results/AxiomsKeyStealingTimed.lean` | landed; `lake build MoltPetit Molt` clean; all `[propext, Classical.choice, Quot.sound]` |
| 2026-09-10 | `Molt/SyncRuleTimed.lean` | `Molt.Reacts`, `Molt.recentTheftProducersK`, `client_refresh_rule_timed`, `sync_rule_timed`, `sync_rule_mem_timed`, `max_sync_period_timed` (W3a, Molt re-presentation) | `Molt/AxiomsSyncRuleTimed.lean` | landed; same build; all `[propext, Classical.choice, Quot.sound]` |
| 2026-09-10 | `MoltPetit/Model/KeyStealingCertAnchored.lean` | `keyrot_deep_block_agreement_anchored`, `AcceptedSuffixK`, `AcceptedSuffixK.history`, `keyrot_certified_suffix_agreement_anchored` (W2, mode 1 anchored/trailing-5n client rule reconstructed at the certificate presentation, generic over `Signed`) | `Molt/AxiomsCertAnchored.lean` | landed; `lake build MoltPetit Molt` clean; all `[propext, Classical.choice, Quot.sound]`; one build-time fix (an `unfold blockAt?` target had been stated with the fully-qualified `MoltPetit.Model.blockAt?` name inside `namespace Molt`, where unqualified `unfold` resolves to `Molt.blockAt?` — dropped the qualifier so the tactic name lookup matches the goal it is unfolding) |
| 2026-09-10 | `Molt/CertClientRule.lean` | `Molt.keyrot_certified_suffix_agreement_anchored`, `cert_client_refresh_rule`, `cert_stay_recent_client_safe`, `cert_sync_rule`, `cert_max_sync_period` (W2, Molt re-presentation of the four client-facing certificate rules) | `Molt/AxiomsCertAnchored.lean` (single file, guards both the core and Molt declarations for this item, per the design's own layout choice) | landed; same build; all `[propext, Classical.choice, Quot.sound]` |
| 2026-09-10 | `MoltPetit/Model/KeyStealingLockstepCert.lean` | `lockstepOk_append_iff`, `keyMonoOk_of_lockstepOk`, `lockstepFrom`, `GroundedCertLock`, `GroundedHistoryLock`, `groundedCertLock_history`, `groundedCertLock_gen_of_tail`, `groundedCertLock_suffix_history`, `groundedCertLock_signedChain`, `lockstep_cert_gen_pinned`, `lockstep_cert_declares_rosterGen`, `lockstep_recent_certified_suffix_agreement` (W1, mode 3 free-cadence lockstep at the certificate presentation, discharging the honest-scope bound that mode-3 theorems were full-chains-only) | `MoltPetit/Results/LockstepCertAxioms.lean` | landed; `lake build MoltPetit Molt` clean; all six guarded theorems measured `[propext, Classical.choice, Quot.sound]` |
| 2026-09-10 | `Molt/LockstepCert.lean` | `Molt.GroundedCertLock`, `Molt.lockstepFrom`, `Molt.lockstep_cert_gen_pinned`, `Molt.lockstep_cert_declares_rosterGen`, `Molt.lockstep_recent_certified_suffix_agreement` (W1, Molt re-presentation, abbrev+alias idiom matching the mode-2 certificate precedent at `Molt/Rotation.lean:321,352`) | `Molt/LockstepCertAxioms.lean` | landed; same build; all three aliased theorems measured `[propext, Classical.choice, Quot.sound]` |

## 3b. Provisional effort and ordering (NOT yet verified)

The sequencing agent never ran, so this is the planner's provisional reading, not
a checked result. Effort for W1/W2/W5 is each design's own estimate; the rest are
rough. Nothing here should be treated as settled until a sequencing pass runs
over the verified designs.

| item | effort | note |
|---|---|---|
| W2 | 1-2 sessions | cheapest of the three designed; no dependencies; adds a generic-Signed anchored engine that W4 can also use |
| W1 | 2-3 sessions | self-contained; consumes the lockstep package opaquely, so W5 does not invalidate it |
| W4 | 1-2 sessions | abstract over the per-sync step, so it instantiates at both the full-chain and (later) certificate presentations |
| W3a | 1-2 sessions | mirrors the mode-2 timed layer; the survey is salvaged |
| W5 | 3-4 sessions | the deep one (the D1-prime-full census); do after W1 |
| W6 | text-only, or 1-2 sessions | a text-only variant exists and may be the right call |
| W3b | 4-6 sessions | subsumes W3a's relaxation; never before W3a |
| W7 | 4-6 sessions | lowest priority; buys a liveness hypothesis discharge, not safety |

Two loop risks the designs flag and a sequencer must settle: who owns the shared
timed structure carrying theft times (W3a vs W5 vs W6), and whether W3b's surface
change would force any W3a result to be restated.

## 4. Recovery record

The planning workflow's first run died on a usage limit; recovery notes and the
recorded module maps live outside the repo at `/etheron-pod/rollout-work/`
(`journal-scan.md`, `maps/`, `designs-partial/`) **and, committed, at
`docs/rollout/`** in this repo (the canonical copy going forward — see `docs/rollout/README.md`).

## 5. Plan-completion phase (started 2026-09-10)

George's instruction: process every Fable finding (finished and killed mid-run),
finish the plan, adversarially review and fix it, then implement strictly in
plan order — one item fully done before the next starts — documenting every
stage and committing often. Not touching the paper remains absolute.

**Workflow `molt-rollout-plan2`** (run id `wf_d51a02f7-018`), launched to close
every gap left by §3b: loads the three existing designs (W1, W2, W5) from
`docs/rollout/designs/`, designs W3a/W4/W6 in full and sketches W3b/W7 (using the
`docs/rollout/designs-partial/*-run2.md` salvage as the starting evidence so nothing
already verified gets re-derived), runs a REAL two-lens adversarial review on
every substantial item to completion (the six-verifier partial results in
`docs/rollout/verdicts/*-partial.md` never reached a verdict last time — this run's
prompts point reviewers at that evidence and instruct them to build on it, not
repeat it), fixes any design carrying a blocking/major finding, and sequences
the final sequence agent produces the implementation order this plan follows.
Every agent writes its own JSON output directly into `docs/rollout/designs/` and
`docs/rollout/verdicts/` as it finishes, so a partial run loses nothing.

Once this workflow returns: reconcile its output into `docs/rollout/ROLLOUT_PLAN.md` (the
deliverable), commit the plan and every design/verdict file, and **only then**
start Lean implementation, one work item at a time, in the sequenced order —
each item's cycle is: write the Lean, `lake build` it clean, guard its axioms,
`lake build MoltPetit Molt` clean, update §2/§3 of this file, commit, and only
then move to the next item. If the workflow's own review turns up a design
that is not implementable as specified, that is logged here and the item is
either fixed again or explicitly deferred — never implemented against advice
silently.
