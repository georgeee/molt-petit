# W3b salvage, run 3 — Time-aware signature surface (non-retroactive census, larger F_max), sketch

## Header

| | |
|---|---|
| Agent id | `a8b20f7aa718e3de4` (workflow `wf_dba98d3b-916`, `molt-rollout-design2`) |
| Transcript | `/run/claude/agent/projects/-etheron-pod/c28ff38c-0cb1-500d-8726-22cd73943085/subagents/workflows/wf_dba98d3b-916/agent-a8b20f7aa718e3de4.jsonl` (19 lines; line 19 empty) |
| Expected item (indexer) | **W3b** — Time-aware signature surface (non-retroactive census, larger F_max) — sketch — for `/etheron-pod/mini-consensus-lean`, additive-only new modules |
| Confirmed item | **NOT CONFIRMED from transcript content.** See "Item confirmation" below. Nothing in the transcript names any work item, and the only assistant prose is two generic sentences. |
| Role | DESIGNER (batch of five: W3a, W4, W6, W7, W3b) |
| Model | `claude-fable-5-1`, effort `medium`; cwd `/etheron-pod`; sessionId `c28ff38c-...`; gitBranch `HEAD` |
| Started | 2026-09-05T09:44:11.080Z |
| Killed | 2026-09-05T09:44:20.925Z — HTTP 429 `rate_limit`, `"You've hit your session limit · resets 2pm (UTC)"`, `rateLimitType: five_hour`, `overageStatus: rejected`, `overageDisabledReason: org_level_disabled` |
| Wall-clock lifetime | **≈ 9.8 seconds**, 4 tool calls, all Bash |
| Lines seen | offsets 4–18 (15 lines) |
| Lines skipped (read failure) | none — every line read on the first attempt at `limit=8`/`limit=3` |
| Lines not read (protocol) | offsets 0–3 (oversized prompt + harness attachments) |
| Thinking blocks | all empty (`"thinking": ""`, signature only) — no reasoning text recoverable |
| Where it stopped | Immediately after the 4th tool result (line 17, 09:44:20.186Z, the W2/W5/W1 design digests). The next model turn (line 18) is the 429. No 5th tool call, no design text. |

### Note on `W3b-run2.md`

The salvage brief anticipated that `/etheron-pod/rollout-work/designs-partial/W3b-run2.md` might already exist from a longer earlier attempt at the same item. **It does not exist**, and neither does a run-1 `W3b.md`. Per `/etheron-pod/rollout-work/journal-scan.md:79`, the second design run (`wf_6b051052-ec7`) recorded `design:W3b | 0 | never started`. `designs-partial/` currently holds `W1.md, W2.md, W3a.md, W4.md, W5.md` (run-1 salvages) and `W3a-run2.md, W4-run2.md, W6-run2.md, W7-run2.md` (run-2 salvages) — **no W3b artifact of any kind**. This file therefore records everything W3b has ever produced across three design runs, and it is a survey, not a design. Nothing has been copied from any other item's salvage file.

---

## Item confirmation (asked for explicitly; answered honestly)

**The transcript contains zero content-internal evidence for the W3b label.** There is no mention of W3b, of "time-aware signature surface", of "non-retroactive census", of "F_max", of any work-item number, or of the planner working hypothesis. The complete assistant prose is two sentences (lines 5 and 9), reproduced verbatim in full below:

> "I'll start with the maps for this item."

> "Reading the three primary maps and the existing designs in parallel."

Evidence bearing on the label, ranked:

1. **External attribution (strongest available).** `/etheron-pod/rollout-work/journal-scan.md:108` records `a8b20f7aa718e3de4 | design2:W3b | 19 (weakest label; never opened a -run2.md partial)`. The indexer's normal signal for this batch is the run-2 partial each designer opens first; this agent opened none, so the label rests on elimination against the other four agents in the same workflow (`a4cd8772fbe5855fd` = W3a, `a106047acc40a13bf` = W4, `ad424c9c6dc77ce98` = W6, `a39a6e30ae161a695` = W7).
2. **The absence of a partial read is itself consistent with W3b.** W3b is the only one of the five batch items with no `-run2.md` briefing to open, and this is the only one of the five agents that opened no partial. The missing signal is exactly what W3b predicts.
3. **Weak topical consistency of the chosen maps.** The three maps it selected — `mode1-chain.md`, `mode2-horizon-timed.md`, `timed-core-liveness.md` — match a time-aware-signature item: `timed-core-liveness` is the map covering `MoltPetit/Model/TimedSig.lean` (the timed-signature bridge) and `Timed.lean`; `mode2-horizon-timed` defines `ByzantineBoundedFrom H n bad`, whose one-sided horizon leaves "windows below H unconstrained" (i.e. a non-retroactive census); `mode1-chain` supplies the key-index/key-floor machinery a larger F_max would sit on.
4. **Counter-evidence / ambiguity.** The same map triple fits **W3a** (mode-1 timed theft layer deriving the trailing budget) at least as well — `mode1-chain` was read *first*, and `mode2-horizon-timed` also covers `KeyStealingScheduleTimed`. W3a is separately attributed to another agent, so this does not overturn the label, but it means the map choice alone does not discriminate.

**Verdict: the W3b label is plausible and unrefuted, but unconfirmed from this transcript's content.** A downstream reader should not treat any part of this file as W3b-specific design intent.

---

## 1. Files examined, in order

All four tool calls were `Bash`; the "why" column quotes the subagent's own `description` field (it wrote no other rationale). **Every `cat` of a map exceeded the inline limit, so the subagent received only a 2 KB preview of each** — the full text it asked for was written to a `tool-results/` file it never read back before dying.

| # | Line | Command | Ranges actually seen | Why (its own description) |
|---|---|---|---|---|
| 1 | 6 | `cd /etheron-pod/rollout-work/maps && wc -c *.md && ls /etheron-pod/rollout-work/designs/` | full output (small) | "List map sizes and designs" |
| 2 | 10 | `cat /etheron-pod/rollout-work/maps/mode1-chain.md` | first 2 KB only (56 KB persisted to `tool-results/bezk4q855.txt`) | "Read mode1-chain map" |
| 3 | 12 | `cat /etheron-pod/rollout-work/maps/mode2-horizon-timed.md` | first 2 KB only (40 KB persisted to `tool-results/btczh7iwy.txt`) | "Read mode2-horizon-timed map" |
| 4 | 14 | `cat /etheron-pod/rollout-work/maps/timed-core-liveness.md` | first 2 KB only (48.5 KB persisted to `tool-results/b8em94x7j.txt`) | "Read timed-core-liveness map" |
| 5 | 16 | `cat designs/W2.md; echo ======W5; cat designs/W5.md; echo =====W1; head -c 6000 designs/W1.md` | first 2 KB only, i.e. the W2 header and part of its goal statement (106.8 KB persisted to `tool-results/bjqas0r7b.txt`); **W5 and W1 never seen at all** | "Read W1/W2/W5 design digests" |

Calls 2–5 were issued as one parallel block (single assistant message `msg_011Cek5QHvQJQYw7uUe5RaMp`, apiBlockIndex 2–5), which is why all four landed within 3 seconds.

**No Lean source file was opened.** No file under `/etheron-pod/mini-consensus-lean` was read; no `git` command was run; no repo HEAD was observed.

### Process gotcha worth carrying forward

Four of its five tool calls returned only a 2 KB preview because `cat` of a 40–107 KB map overflows the inline tool-result budget. A fresh W3b designer should read the maps with the `Read` tool (or `sed -n`/`head -c` in sub-40 KB slices) rather than `cat`, and should read the originals in `/etheron-pod/rollout-work/maps/` and `/etheron-pod/rollout-work/designs/` rather than the `tool-results/*.txt` copies (which are byte-identical to the on-disk originals and are owned by the agent account).

---

## 2. Facts it verified

Everything below is what the subagent actually had in context. It is map-digest content, not directly-read Lean source; the subagent did no independent verification against the repository.

### 2.1 Workspace state (line 7, 09:44:13Z)

- Map digest sizes in `/etheron-pod/rollout-work/maps/`: `core-grounded-cert1.md` 44708, `design-docs.md` 58756, `mode1-chain.md` 57298, `mode2-cert-budget.md` 43042, `mode2-horizon-timed.md` 41007, `mode3-lockstep.md` 45729, `results-molt.md` 59902, `timed-core-liveness.md` 49688 — total 400130 bytes.
- `/etheron-pod/rollout-work/designs/` contained exactly `W1.json W1.md W2.json W2.md W5.json W5.md` — i.e. the three completed designs and their digests, nothing for W3a/W3b/W4/W6/W7.

### 2.2 From `mode1-chain.md` (2 KB preview, line 11)

- Map scope line: sourced from `mode1-chain.json`, **22 modules, 61 defs, 90 theorems**. Scope: key index / in-band key rotation / key-stealing adversary (mode 1) core modules, plus the Molt/ paper re-presentation and the downstream Results/Horizon/Cert modules where the focus identifiers live.
- File `/etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyIndex.lean` — imports `MoltPetit.Model.Safety`, `MoltPetit.Model.Soundness`. Purpose: consensus-maintained per-producer delegate-key index — the in-band monotone rule `keyMonoOk`, the indexed validator `validChainK`, the per-producer floor `keyFloor` (foldl max over the producer's blocks), soundness of the rule (`KeyIndexMonotone`), no-rollback across extension, `keyIndex` agreement on finalized blocks, and the static-registry reduction `pinAt`.
- Declarations (name, kind, line, meaning as given):
  - `keyMonoOk` — def, **line 54** — validator's in-band monotone-index rule: no earlier block of a producer carries a higher `keyIndex` than a later block of the same producer.
  - `KeyIndexMonotone` — def, **line 64** — semantic counterpart of `keyMonoOk` over chain positions.
  - `validChainK` — def, **line 71** — indexed validator: structural validity plus monotone-index rule.
  - `keyFloor` — def, **line 77** — participant `i`'s floor: highest `keyIndex` it used anywhere in `c` (0 if none).
  - `pinAt` — def, **line 223** — static index-blind directory pinning producer `i` at index `e i`.
  - `le_foldl_max` / `mem_le_foldl_max` / `foldl_max_append` — private theorems, **line 84** — **PRIVATE, not importable; every downstream module re-proves its own copies** (`KeyRotation.lean` 150–178, `KeyStealingCert.lean` 55–79, `Molt/MaxSync.lean` 45–72).
  - `keyFloor_le_extend` — theorem, **line 113** — hypotheses `(n : Nat) (c d : Chain) (i : Nat)` explicit, **no Prop hypotheses**; conclusion `keyFloor n c i ≤ keyFloor n (c ++ d) i`; note "No rollback across chain growth."
- (The preview was truncated after `keyFloor_le_extend`; the remaining 89 theorems were never in context.)

### 2.3 From `mode2-horizon-timed.md` (2 KB preview, line 13)

- Map scope: `MoltPetit/Model/{KeyStealingScheduleHorizon, KeyStealingScheduleTimed, KeyStealingHorizonCore, KeyStealingHorizon}`.
- File `/etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingScheduleHorizon.lean` — imports `MoltPetit.Model.KeyStealingScheduleCert`. Purpose (verbatim): mode-2 (scheduled) horizon-scoped budget: defines `ByzantineBoundedFrom H n bad`, proves the validator-agnostic top-window contraction `horizon_shared_prefix` (pigeonhole at the trailing matured window `u = tip.slot + 1 - n` of the **LOWER** tip, then `same_block_same_prefix` drags agreement down to any n-deep height), and re-states the scheduled light-client headlines (full validator + core validator twins, agreement / membership / genesis forms) **consuming only `ByzantineBoundedFrom H` with `H + n ≤ tip.slot + 1` and NO shared-genesis hypothesis**. Purely combinatorial: no new model, same `SchedUnforgeable` / `SchedCoreUnforgeable` surfaces.
- Declarations:
  - `ByzantineBoundedFrom` — def, **line 70** — budget required only of n-windows `[u, u+n)` with `u ≥ H` (**one-sided horizon: later windows, including future ones, remain budgeted; windows below H unconstrained**).
  - `exists_honest_shared_slot_at` — private theorem, **line 86** — single-window pigeonhole (`2q > n + f`): budget consumed at exactly window `u`. **PRIVATE — a new module cannot import it; it must copy it (both this file and `KeyStealingHorizonCore.lean` carry identical private copies) or call the public global-budget `exists_honest_shared_slot` (`Safety.lean:45`).**
  - `slot_gap_of_position_gap` — private theorem, **line 116** — along a strict-slot chain, `d` positions apart ⇒ at least `d` slots apart. **PRIVATE — must be copied if a new module needs it.**
- (Preview truncated at the start of the theorem table; no theorem rows were seen.)

### 2.4 From `timed-core-liveness.md` (2 KB preview, line 15)

- Map scope: timed model, timed-signature bridge, liveness, and core definitions — `MoltPetit/Model/{Timed,TimedSig,Liveness,Definitions}.lean` — plus the out-of-file declarations the brief names (`Results.lean` forged bounds, `Molt/` re-presentation, `KeyIndex`/`KeyRotationLiveness`, `Model/Soundness` helper lemmas).
- File `/etheron-pod/mini-consensus-lean/MoltPetit/Model/Timed.lean`. Purpose: timed signing model proofs — signing-time monotonicity along parent-linked chains (from `TimedExecution.chain_order` + `id_inj`), the "one real slot, one chain block" lemma, and the counting lemmas (`belowCount` / windows / Byzantine budget over `Ico`) that `Results.lean` assembles into `forged_suffix_time_bound` / `forged_chain_time_bound`. Namespace `MoltPetit.Model`. **Contains ONE definition (`belowCount`); the model structures (`TimedLog`, `TimedExecution`, `AvailableAt`, `SignedEver`) live in `Definitions.lean`.**
- Imports: `MoltPetit.Model.Grounded` (transitively: `MoltPetit.TS.Bridge`, `MoltPetit.Model.Liveness`, `Soundness`, `Safety`, `Model`, `KeyIndex`, `Definitions`, `Mathlib`, `MoltPetit.TS.Emitted`).
- Defs (1): `belowCount` — def, **line 254** — number of chain blocks whose stamp is strictly below `k`.
- Theorems (12 total; two rows seen):
  - `block_signed` — **line 47** — hypotheses `hGprev, hPL, hAvail, hk, hB` ⇒ `B ≠ G ∧ ∃ r, r ≤ R ∧ B ∈ log r`. Notes: **needs NO `TimedExecution`**; index `k ≥ 1` is essential (index 0 has `prev = none` by `ParentLinked`; blocks at index ≥ 1 have `prev = some _`, hence `≠ G`); **does not require `c[0] = G`**.
  - `sigTime_mono_step` — **line 67** — hypotheses `hexec, hPne, hprev, hPsig, hBsig` ⇒ `Nat.find hPsig ≤ Nat.find hBsig`. Notes: uses `hexec.chain_order` and `hexec.id_inj` only; first-signing time is `Nat.find` over `∃ r, B ∈ log r` (**needs `DecidablePred` — classical instance available since `Finset` membership on `Block` with `DecidableEq`**).
- (Preview truncated after `sigTime_mono_step`; the other 10 theorems and all of `TimedSig.lean` were never in context.)

### 2.5 From `designs/W2.md` (2 KB preview, line 17)

Only the W2 header and the opening of its goal statement arrived; **W5.md and W1.md were requested in the same command but never reached the subagent's context.** What it saw:

- W2 title: "Mode 1 anchored / trailing-5n client rule at the certificate presentation (`GroundedCertK` + suffix), as a corollary of a generic-`Signed` anchored deep-block engine applied to the reconstructed chains"; source of record `/etheron-pod/rollout-work/designs/W2.json`.
- W2 goal statement (truncated mid-word at the end): prove additively and axiom-clean that two verifying `GroundedCertK` certificates each extended by a validated recent suffix agree on every block at the same global height that is n-deep in both suffixes, with the corruption budget consulted ONLY on windows ending after a client anchor `A` (core form); derive the Molt-level refresh-rule family at the certificate presentation — an H-parametric form (mirror of `Molt.client_refresh_rule`), the trailing-5n form with the previous sync itself in certificate form (mirror of `Molt.stay_recent_client_safe`), and the `Δconf := n` sync rule (mirror of `Molt.sync_rule`). Its three recorded answers: (1) the anchor enters as membership in the **exposed suffix** (`hA : A ∈ s₁ :: srest`, `hA' : A ∈ s₁' :: srest'`), lifted to the reconstructed chain by `List.mem_append_right` — it need not and cannot usefully be located inside the certified prefix (the verifier cannot check that); protocol reading is "the prover starts the suffix at or before the client's anchor" (≤ 4n slots back under the sync rule, so still O(n) blocks); (2) confirmed floors are read as `inForce` over the **reconstructed** chain inside `badKeyrotOn c`, exactly as in `keyrot_recent_certified_suffix_agreement`, with the budget quantified over `AttestedHistoryK`; the floor snapshot `fl` enters only through `GroundedCertK`/`keyMonoFrom` and is never consulted by the budget (a verifier-visible floor-based budget predicate is sound only for slots `s ≥ cl.tipSlot + Δconf` and is left as a refinement); (3) the trailing window is measured from the **verifier clock**: "window…" *[cut off here]*.

---

## 3. Design direction

**None was stated.** No planned module names, no definitions, no theorem statements, no proof sketches, no lemma-composition list, no dependency list, no effort estimate. The subagent died with its survey one call old.

The only thing inferable — and it is inference from tool inputs, not from anything the subagent wrote — is its intended grounding: it treated `mode1-chain`, `mode2-horizon-timed` and `timed-core-liveness` as "the three primary maps" for this item (its phrase, line 9), and intended to read the three already-completed designs (W1, W2, W5) alongside them, presumably to align with or avoid duplicating recorded work. **Marked partial/inferred; do not treat as a design decision.**

---

## 4. Decisions and rejected alternatives

**None.** No alternative was named, weighed or rejected anywhere in the transcript.

---

## 5. Structured output / drafted JSON

**None.** The subagent made **no `Write` call** — in particular it never wrote `/etheron-pod/rollout-work/designs/W3b.json`, and that file does not exist (the `designs/` directory holds only W1/W2/W5 artifacts). It made **no `StructuredOutput` call** and drafted no JSON in prose. `partial_output` is empty.

---

## 6. Open questions it raised

**None stated.** It never reacted to the planner working hypothesis — the prompt's proposed shape for the definitions and the derivation is nowhere addressed in any assistant text, because the run ended before the survey finished.

---

## 7. What a fresh W3b designer gains from this run

1. W3b has produced **no design content in any of the three runs**; there is no prior partial to build on. This file is the entire history.
2. The four map/design digests this agent wanted are on disk and unread: `maps/mode1-chain.md`, `maps/mode2-horizon-timed.md`, `maps/timed-core-liveness.md`, and `designs/{W1,W2,W5}.md`. Read them with `Read`, not `cat`.
3. Three concrete importability gotchas surfaced in the previews and are worth carrying into the design: `KeyIndex.lean:84` (`le_foldl_max` family), `KeyStealingScheduleHorizon.lean:86` (`exists_honest_shared_slot_at`) and `:116` (`slot_gap_of_position_gap`) are **private**; a new additive module must copy them or route through the public `exists_honest_shared_slot` at `Safety.lean:45`.
4. `ByzantineBoundedFrom` (`KeyStealingScheduleHorizon.lean:70`) already implements a one-sided, non-retroactive budget for mode 2 (windows below `H` unconstrained), and the headline theorems consume it with `H + n ≤ tip.slot + 1` and no shared-genesis hypothesis. Whatever W3b's non-retroactive census turns out to be, this is the existing precedent to compare against.
5. The label itself is the weakest in the batch — a fresh designer should re-read the item statement from the orchestrator's plan rather than inherit "W3b" from this file.
