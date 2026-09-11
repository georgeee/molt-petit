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
| W3a/W3b | AN/24, AN/29 | §6.3 mode 1 `theft \emph{times} inside the signature assumptions`; "Honest scope" first bound `distinguishing thefts before a block's creation` | rewrite according to what lands (W3a: theft times as a derivation layer; W3b: non-retroactive census). Cite `MoltPetit.Model.theft_exposure_window` for "a theft at `r` exposes only `[r, r+d)`" and `Molt.paced_tight_census_bound_all_F` for "the census no longer constrains `F`". **Do NOT write** "there are executions the untimed budget gets wrong that the timed one gets right" — `Molt.paced_budget_holds_under_timing` proves there are none; the gain is in which hypotheses a deployment can defend, not in which executions are safe |
| W4 | AN/26 | §6.3 mode 1 walkthrough, phrase `argued on paper, not itself machine-checked` and `an informal argument` | cite the machine-checked induction (`Molt.sync_induction_full_chain`). **Careful:** the side condition that absorbs the paper's informal *density* argument is `hRLe` (the reference tip is at least as tall at every sync), not tip-recency — recency is a separate hypothesis (`hRRecent`). The paper sentence must say the induction is machine-checked *conditional on `hRLe`*, which is what the density remark was arguing for; claiming the density argument itself is now machine-checked would overstate it. The module docstring states this correctly |
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
| 2026-09-11 | `MoltPetit/Model/KeyStealingWindowCore.lean` | `HonestSlotsUniqueOn`, `honestSlotsUniqueOn_of_unique`, `exists_honest_shared_slot_at_win`, `slot_gap_of_position_gap_win`, `window_shared_prefix`, `chain_length_le_tip_slot`, `horizon_shared_prefix_of_window` (W5, the validator-agnostic aligned-window contraction engine, the generalisation of `horizon_shared_prefix` to an arbitrary matured window) | `MoltPetit/Results/AxiomsLockstepGen.lean` (engine's headline `window_shared_prefix` only; helpers not separately guarded, matching convention) | landed; `lake build MoltPetit Molt` clean; `window_shared_prefix` measured `[propext, Classical.choice, Quot.sound]` |
| 2026-09-11 | `MoltPetit/Model/KeyStealingLockstepGen.lean` | `badLockAt`, `AlignedBounded`, `lockstep_aligned_budget`, `LockstepPackageGen`, `LockstepPackage.toGen`, `lockstep_window_declares_rosterGen` (non-inductive, genesis-free per-window pinning), `honestSlotsUniqueOn_lockstep`, `lockstepGen_shared_prefix`, `lockstepGen_shared_prefix_deep`, `lockstepGen_recent_tip_ancestor_agreement`, `lockstepGen_recent_tip_ancestor_mem`, `lockstepGen_recent_genesis_agreement` (W5, mode 3 per-generation census (D1'-full), confirmation depth `2n`, no shared genesis) | `MoltPetit/Results/AxiomsLockstepGen.lean` | landed; `lake build MoltPetit Molt` clean; all nine guarded headline theorems measured `[propext, Classical.choice, Quot.sound]`; `exposedBound_not_of_genBound` (the optional pure-budget-transport-is-impossible consistency witness) hit a Finset decidability-instance diamond that did not resolve within budget and was left as a prose argument in the module doc, per the design's own explicit risk mitigation — the mathematical content is unaffected, this is documentation-only, matching `PackageB`'s own prior-art docstring precedent for the same counterexample |
| 2026-09-11 | `MoltPetit/Model/KeyStealingLockstepTimed.lean` | `NoPrematureTheftLock`, `ErasureTimedLock`, `theft_in_era_lock` (axiom-free), `stolen_generation_was_live`, `noPrematureTheftLock_iff_flagship` (`[propext]`), `erasureTimedLock_iff_flagship` (`[propext, Quot.sound]`), `preRetirementTheftProducers`, `genBound_of_preRetirementBound`, `LockstepPackageTimed`, `LockstepPackageTimed.toGen`, `lockstepTimed_recent_tip_ancestor_agreement`, `lockstepTimed_recent_tip_ancestor_mem` (W5, the timed theft layer where erasure is load-bearing, the mirror image of mode 2's documentary erasure) | `MoltPetit/Results/AxiomsLockstepGen.lean` | landed; same build; all measured exactly as predicted by the mode-2 `_iff_flagship` precedent |
| 2026-09-11 | `Molt/LockstepGen.lean` | `Molt.LockstepPackageGen`, `Molt.LockstepPackageTimed`, `Molt.badLockAt` (abbrevs), `Molt.lockstep_window_declares_rosterGen` (alias), `Molt.lockstep_client_safety_gen`, `Molt.lockstep_client_safety_timed` (W5, Molt re-presentation, `validSignedChainLock_eq_core`-rewrite idiom matching `Molt.lockstep_client_safety`) | `Molt/AxiomsLockstepGen.lean` | landed; same build; all three guarded theorems measured `[propext, Classical.choice, Quot.sound]` |
| 2026-09-11 | `MoltPetit/Model/KeyStealingSignatureTimed.lean` | `NoTheftBackdating` (new named crypto-adjacent hypothesis, the time-aware signature surface), `recentTheftProducersTight`, `exposedProducers_subset_recentTheftTight`, `budget_of_reaction_tight`, `anchored_budget_of_reaction_tight` (W3b, mode 1 two-sided-bounded theft census, closing the gap that W3a's `recentTheftProducersK` was not actually F-independent) | `MoltPetit/Results/AxiomsKeyStealingSignatureTimed.lean` | landed; `lake build MoltPetit Molt` clean; all three guarded theorems measured `[propext, Classical.choice, Quot.sound]` |
| 2026-09-11 | `Molt/MaxSyncSignatureTimed.lean` | `Molt.NoTheftBackdating` (abbrev), `Molt.recentTheftProducersTight` (+`_eq_core`), `Molt.max_sync_period_tight` (the headline consumer, W3b's cash-out of "larger F_max"), `Molt.pacedStolenAt` (the witnessed paced multi-victim adversary), `Molt.recentTheftProducersTight_card_le_one_of_paced`, `Molt.pacedStolenAt_exceeds_untimed_budget`, `Molt.pacedStolenAt_safe_under_tight_unsafe_under_untimed` (the machine-checked separation: the tight census stays bounded by 1 for every window regardless of the sync period, while the same schedule defeats the untimed census's budget at window 0 — the stretch goal within W3b, landed in full, not deferred) | `Molt/AxiomsMaxSyncSignatureTimed.lean` | landed; same build; all five guarded theorems measured `[propext, Classical.choice, Quot.sound]` (the `_eq_core` bridge measured `Classical.choice`-dependent, not the `[propext, Quot.sound]` the design predicted by analogy — measured, not guessed, per protocol) |

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

## 6. Post-review corrections (2026-09-11, second pass)

A review pass over the landed arc, checking the English claims against the
Lean statements rather than re-checking the proofs, found one real defect and
two overclaims. All three are now fixed in Lean, not just in prose:

| Finding | Status |
|---|---|
| `Molt.pacedStolenAt_safe_under_tight_unsafe_under_untimed` was **vacuous**: it carried `hReacts`/`hNoBack` alongside `hFloor0`, and those are jointly contradictory (the paced schedule's first theft is at real slot `0`, so `Reacts` forces the victim's floor up by slot `d` while `hFloor0` pins it to `0` across `[0, n)` — contradictory whenever `d < n`, i.e. exactly the attractive fast-reaction regime) | **fixed**: the two timing hypotheses are dropped (neither conjunct ever needed them), so the theorem is now non-vacuous, and `Molt.paced_separation_witnessed` discharges every remaining hypothesis at concrete parameters (`n = 4, d = 1, P = 5, ι = id, c₀ = []`) — a separation with no hypotheses at all, closing the "never shown jointly satisfiable" gap the design left open |
| "larger `F_max`" was asserted in prose but was not a theorem — `max_sync_period_tight` is F-parametric with exactly the same guard as the untimed form | **fixed**: `Molt.paced_tight_census_bound_all_F` states the actual formal residue (the census hypothesis discharges at `T := 1` for every `F`), and the module doc now says explicitly that this is not a proof that a larger `F` is safe, since rent still has to be bounded over the stretch |
| the intended "timed hypotheses hold, untimed budget fails" separation is **impossible**, not merely unwitnessed | **proved**: `Molt.paced_budget_holds_under_timing` shows that under `Reacts` + `NoTheftBackdating` the paced adversary *satisfies* the old budget, via `Molt.exposedProducers_card_le_one_of_paced`. Recorded as positive content rather than left as a gap |

Also added, closing smaller English-vs-Lean gaps found in the same pass:

- `MoltPetit.Model.theft_exposure_window` — the sharp statement of
  non-retroactivity (a theft at `r` exposes chain-slots only in `[r, r+d)`),
  which is what a paper sentence about theft times should actually cite.
  Measured `[propext, Quot.sound]`.
- `MoltPetit.Model.groundedCertLock_gen_unique` — W1's module doc claimed the
  threaded generation is "a function of the claim alone", but
  `groundedCertLock_gen_of_tail` only gave existence; this supplies the
  determinacy (any tail block at the tip slot carries exactly `g`), so the
  claim is now a theorem rather than a reading.

All six new declarations are axiom-guarded; `lake build MoltPetit Molt` clean.

### Second review round (2026-09-11): the annotation-round paper edits, and the Lean again

The 2026-09-04 paper edits (commits `e21376d..8b8b766`, 129 changed lines) were
read against the Lean; the new Lean was re-read for unused hypotheses, unproved
remarks, and docstring precision. Proposed paper wording for every ledger row now
lives in **`docs/review/PAPER_WORDING_PROPOSED.md`** (repo root; the paper itself is still
untouched). Findings:

| Finding | Where | Status |
|---|---|---|
| "a theft of a **then-live** key" undercounts the census: `badKeyrot` charges any version *at or above* the one in force (`∃ j, inForce ≤ j ∧ Stolen i j`), so later, not-yet-used versions count too | Theorem 3's one-sentence form and the mode-1 walkthrough (both from the AN/18–19 edit) | wording proposed (`docs/review/PAPER_WORDING_PROPOSED.md` §0a) |
| AN/15's edit dropped the only disclosure that the representability lemmas are production-side; Theorem 1's "exposes that height" hypothesis now has no stated reason to remain | Theorem 1 paragraph | re-flagged, one restoring clause proposed (§0b); George's call, as before |
| "clients of the other two modes obey no rule at all" — they still pass the recency check at each sync | §1 intro | "no *cadence* rule" proposed (§0c) |
| W5's module doc asserted "exact worst case `n + ((t+1) mod n)`" without a proof | `KeyStealingLockstepGen.lean` | **proved**: `lockstepGen_shared_prefix_sharp`, guarded; the doc now cites it |
| `LockstepPackage.toGen` docstring said "exactly when" surjective; only the forward direction is proved | `KeyStealingLockstepGen.lean` | docstring corrected to "when", converse explicitly not claimed |
| unused hypotheses across all 14 new modules | build replay | none remain (only the pre-existing `open Classical` style note, matching `KeyStealingScheduleTimed.lean`) |

Everything else in the annotation-round edits checked out against the Lean
(abstract's audit claim, the TS-soundness sentence, `keyFor` as a model
parameter, the timed model's "stamped with any slot" clause, the floor gloss,
the F-max paragraph's "charged from the moment it is stolen" — which is now
literally `theft_exposure_window`). The sentences those edits left as "future
work" are exactly the ones the landed items retire; the wording file handles them
row by row, with a "do not say" guard wherever a natural sentence would outrun
the Lean (notably: no execution-level separation between the timed and untimed
budgets exists, `paced_budget_holds_under_timing`).

**Closed 2026-09-11.** All seven scoped items (W6, W4, W3a, W2, W1, W5, W3b)
landed in that order, one per commit, each preceded by a clean standalone
build of the new module and followed by a clean `lake build MoltPetit Molt`.
W7 was not attempted, per its own design's firm skip recommendation — the
plan's own `docs/rollout/ROLLOUT_PLAN.md` records this as a deliberate, reasoned omission,
not an oversight. A final full-library build (`lake build`, all four default
targets) completed clean (8667/8667 jobs), confirming the Rust/Thales
extraction paths this rollout never touched are unaffected. `paper/molt.tex`
was not opened for editing at any point; §1 above remains the record of every
paper change each item's design proposes, for the separate pass the owner
controls.
