# W7 salvage (run 3) — Multi-chain network model for liveness (statement sketch)

| | |
|---|---|
| Agent id | `a39a6e30ae161a695` (workflow `wf_dba98d3b-916`) |
| Transcript | `/run/claude/agent/projects/-etheron-pod/c28ff38c-0cb1-500d-8726-22cd73943085/subagents/workflows/wf_dba98d3b-916/agent-a39a6e30ae161a695.jsonl` (13 lines; line 13 is empty) |
| Item expected (indexer-inferred) | W7 — Multi-chain network model for liveness (statement sketch) |
| Item confirmed | **YES — W7.** See "Confirmation evidence" below. |
| Lines seen | 4–12 (line 13 is blank). Lines 1–3 not read per protocol (prompt + harness attachments). |
| Lines skipped | **None.** Line 7 (the 203-line `W7-run2.md` tool result) read at `limit=1`; the initial `limit=8` read failed on size and was retried at `limit=3`. |
| Run duration | 09:44:10.258Z → 09:44:23.554Z (**13 seconds**). |
| Where it stopped | Immediately after the single Bash tool result (line 11, 09:44:22.969Z). Line 12 is the kill: `You've hit your session limit · resets 2pm (UTC)` — HTTP 429, `rateLimitType: five_hour`, `overageStatus: rejected`. It had announced it would read "the primary maps" next and never got there. |
| Design text emitted | **None.** Two assistant text tokens total: one sentence of prose and one Bash `description`. No theorem statements, no file plan, no effort estimate, no reaction to the planner hypothesis, no `StructuredOutput`, no `Write`. |
| Relation to run 2 | `/etheron-pod/rollout-work/designs-partial/W7-run2.md` exists (agent `a431ae8c991ced3fe`, workflow `wf_6b051052-ec7`, 203 lines, also killed by a 429). **This file records only what run 3 adds.** Nothing from run-2 is reproduced here; run 3's one Bash call was a re-confirmation pass over run-2's facts, so only the deltas are listed in §2. |

---

## Confirmation evidence (item = W7)

1. **Line 6** — first tool call of the run is `Read` of `/etheron-pod/rollout-work/designs-partial/W7-run2.md`.
2. **Line 7** — that file's first line is `# W7 salvage (run 2) — Multi-chain network model for liveness (statement sketch)`, and its header row reads `| Work item | W7 — multi-chain network model for liveness, additive-only new Lean modules in /etheron-pod/mini-consensus-lean |`. The subagent consumed this as its own briefing.
3. **Line 10** — the Bash `description` is `Confirm liveness_global, selectChain, HonestBlocksCover, Model.lean lemmas`. All four are the multi-chain-liveness surface; none of them belongs to the other four items in the batch (W3a timed theft budget, W4 induction over syncs, W6 per-mode no-back-dating, W3b time-aware signature surface).

The label was therefore inferred correctly by the indexer, and it is confirmed from content rather than from the opened-file heuristic alone.

---

## 1. Files examined (complete — there were two tool calls)

| # | Line | Tool | Path(s) and ranges | Stated reason |
|---|---|---|---|---|
| 1 | 6 | Read | `/etheron-pod/rollout-work/designs-partial/W7-run2.md` (whole file, 203 lines) | assistant prose at line 5: "I'll start with the salvage briefing, then the primary maps." |
| 2 | 10 | Bash | `/etheron-pod/mini-consensus-lean`: `git log --oneline -1`; `git status --short \| head -3`; `MoltPetit/Model/Liveness.lean` **286–300** and **355–372**; `MoltPetit/Model/Definitions.lean` **136–146** and **748–760**; `grep -rn "selectChain" --include=*.lean MoltPetit Molt \| grep -v "^.lake" \| head -20`; `grep -n "theorem\|def " MoltPetit/Model/Model.lean \| head -30` | Bash `description`: "Confirm liveness_global, selectChain, HonestBlocksCover, Model.lean lemmas" |

Verbatim command (line 10):

```
git log --oneline -1 && git status --short | head -3; echo ---; sed -n 286,300p MoltPetit/Model/Liveness.lean; echo ---; sed -n 355,372p MoltPetit/Model/Liveness.lean; echo ---; sed -n 136,146p MoltPetit/Model/Definitions.lean; echo ---; sed -n 748,760p MoltPetit/Model/Definitions.lean; echo ---; grep -rn "selectChain" --include=*.lean MoltPetit Molt | grep -v "^.lake" | head -20; echo ---; grep -n "theorem\|def " MoltPetit/Model/Model.lean | head -30
```

The maps it named ("the primary maps") were never opened in this run.

---

## 2. Verified facts — what run 3 ADDS

Everything below comes from the single tool result at line 11. Facts that merely re-confirm run 2 are marked *(re-confirm)*; the rest are new to this run.

### 2.1 Repo state — one delta

- Commit `8b8b766` — "paper2 p16: appendix -- recency window, no-back-dating scope (AN/33, AN/34)" *(re-confirm)*.
- **`git status --short` is no longer clean: `?? docs/rollout/ROLLOUT_NOTES.md`** (untracked, at the repo root). Run 2 observed an empty `git status --short`. This is the only repo-state change between the two runs.

### 2.2 `MoltPetit/Model/Liveness.lean` 286–300 — source text, previously only summarized

Exact bytes returned (docstrings included; run 2 had the signatures but not the docstrings or the `buildFrom_map_slot` proof):

```lean
/-- Extend `tip` by one honest block at each schedule slot, each built on
the previous block. -/
def buildFrom (tip : Block) : List Nat → Chain
  | [] => []
  | s :: ss => nextBlock s s 0 0 tip :: buildFrom (nextBlock s s 0 0 tip) ss

/-- A synchronous honest run from genesis `g` over honest schedule `ss`. -/
def buildChain (g : Block) (ss : List Nat) : Chain := g :: buildFrom g ss

theorem buildFrom_map_slot (tip : Block) (ss : List Nat) :
    (buildFrom tip ss).map Block.slot = ss := by
  induction ss generalizing tip with
  | nil => rfl
  | cons s rest ih => simp only [buildFrom, List.map_cons, nextBlock, ih]
```

- Confirms `nextBlock s s 0 0 tip` — **id := slot, contentsHash := 0, keyIndex := 0** *(re-confirm)*.
- New: the `buildChain` docstring is the repo's own phrase for the object W7 must generalize — "**A synchronous honest run from genesis `g` over honest schedule `ss`**" — and `buildFrom`'s docstring states the single-chain baking-in explicitly: "each built on the previous block".
- New: `buildFrom_map_slot`'s proof is a two-case `induction ss generalizing tip`, single `simp only` — the template for any analogous per-node-run lemma.

### 2.3 `MoltPetit/Model/Liveness.lean` 355–372 — `liveness_global` statement + proof head

Statement (bytes as printed) — matches run 2 exactly:

```lean
theorem liveness_global
    {n : Nat} {g : Block} {ss : List Nat}
    (hGen : genesisOk g = true)
    (hChain : List.IsChain (· < ·) (g.slot :: ss))
    (hBudget : ∀ u, u + n ≤ (g.slot :: ss).getLast (List.cons_ne_nil _ _) + 1 →
        (badSlotsIn (fun s => s ∉ g.slot :: ss) u n).card ≤ maxByzantine n) :
    validChain n (buildChain g ss) = true ∧
      (buildChain g ss).length = ss.length + 1 := by
```

New (first four proof lines, verbatim):

```lean
  classical
  refine ⟨?_, buildChain_length g ss⟩
  have hStrict : StrictSlots (buildChain g ss) := strictSlots_buildChain g ss hChain
  have hLinks : linksOk (buildChain g ss) = true := linksOk_buildFrom g ss hChain
```

- New: the length conjunct is discharged outright by `buildChain_length g ss` — it carries no hypotheses, so any multi-chain restatement can keep a height/length conjunct for free.
- New: `linksOk_buildFrom g ss hChain` typechecks directly at `linksOk (buildChain g ss) = true` (i.e. `buildChain g ss` reduces to `g :: buildFrom g ss` definitionally for this lemma's statement `linksOk (tip :: buildFrom tip ss) = true`).
- New: the doc block immediately preceding the theorem (lines ~355–360) reads: "`quorum n` slots per window). / Then the run is validator-accepted and has `ss.length + 1` blocks. Since `ss` can be arbitrarily long, the chain reaches any height — production never stalls, and every block eventually becomes `n`-deep."

### 2.4 `MoltPetit/Model/Definitions.lean` 136–146 — `selectChain` *(re-confirm, now from source)*

```lean
/--
Chain selection: adopt `candidate` over `cur` only if it validates and is
strictly higher. Safety does not depend on this rule (the safety theorem
quantifies over arbitrary valid chains); it only affects liveness.
-/
def selectChain (n : Nat) (cur candidate : Chain) : Chain :=
  if validChain n candidate && candidate.length > cur.length then candidate
  else cur
```

at `Definitions.lean:141`, followed by the `Honest block production for slot `slot`.` docstring (i.e. `produceBlock?`).

### 2.5 `MoltPetit/Model/Definitions.lean` 748–760 — `HonestBlocksCover` *(re-confirm, now from source)*

```lean
def HonestBlocksCover (bad : ByzantineSlots) (record : SlotRecord)
    (c : Chain) (u n : Nat) : Prop :=
  ∀ s, ¬ bad s → u ≤ s → s < u + n → ∃ B : Block, B ∈ record s ∧ B ∈ c
```

- Docstring tail seen: "slots (they produced), and the network delivered their blocks in time for the current producer to have built on them (synchrony). The Byzantine budget then guarantees the window is quorum-dense (`window_dense_of_honest_cover`)."
- Immediately after it: a `---` rule and the section header "`-- 9. The prover-throughput model (slot duration)`" — so `HonestBlocksCover` is the **last declaration of section 8**, and a new section-8-adjacent definition has a natural home there (but W7 is additive-only, so this is orientation, not a plan).

### 2.6 `grep -rn "selectChain"` over `MoltPetit Molt` — two NEW hits

| Hit | Status |
|---|---|
| `MoltPetit/Model/Definitions.lean:141: def selectChain (n : Nat) (cur candidate : Chain) : Chain :=` | re-confirm |
| **`MoltPetit/Model/Definitions.lean:307: def selectChainExport (n : Nat) (cur candidate : Chain) : Chain :=`** / `:308: selectChain n cur candidate` | **NEW** — an export wrapper for the plain `selectChain`, not recorded in run 2 |
| **`MoltPetit/TS/Emitted.lean:209: def selectChain (n : Int) (cur : Chain) (candidate : Chain) : Chain :=`** | **NEW** — a TS-emitted `selectChain` over `Int`, a third name collision surface |
| `Molt/Verifier.lean:136: def selectChain {α σ sk pk : Type} (n : Nat)` | re-confirm |
| `Molt/Verifier.lean:191–195: theorem selectChain_eq_core ... simp only [selectChain, MoltPetit.Model.selectCertifiedChain, ...]` | re-confirm — `Molt.selectChain` bridges to `selectCertifiedChain`, not to the plain `selectChain` |

The grep was capped at `head -20` and returned 8 lines, so it was **not** truncated: these are all `selectChain` occurrences outside `.lake`. Consequence, unchanged from run 2 and now independently established: **no theorem anywhere mentions `MoltPetit.Model.selectChain`** (the only theorem hit is `selectChain_eq_core`, which is about `Molt.selectChain`).

### 2.7 `MoltPetit/Model/Model.lean` declaration list (first 30 `theorem`/`def` grep hits) — two NEW entries

```
8:`MoltPetit.Model.Impl`. The safety theorem in `Model/Safety.lean` is stated
35:theorem mem_chainSlotsIn {c : Chain} {u len s : Nat} :
40:theorem chainSlotsIn_subset_Ico {c : Chain} {u len : Nat} :
47:theorem strictSlots_lt {c : Chain} (hS : StrictSlots c)
60:theorem chainSlotsIn_card {c : Chain} (hS : StrictSlots c) (u len : Nat) :
71:theorem exists_blockAt_of_mem {c : Chain} {B : Block} (hB : B ∈ c) :
79:theorem exists_blockAt_of_le {c : Chain} {k m : Nat} (hk : k ≤ m)
88:theorem LastCommonHeight.symm {c c' : Chain} {h : Nat}
95:theorem quorum_overlap {n : Nat} (hn : 1 ≤ n) :
```

- `:35, :40, :47, :60, :71, :79` — re-confirm run 2's map-derived list, now direct from source.
- **`:88 theorem LastCommonHeight.symm {c c' : Chain} {h : Nat}` — NEW.** Symmetry of `LastCommonHeight`, i.e. the two-chain relation `no_deep_fork` consumes is symmetric; relevant to any statement quantifying over an unordered pair of node chains.
- **`:95 theorem quorum_overlap {n : Nat} (hn : 1 ≤ n) : ...` — NEW.** The quorum-intersection lemma, gated on `1 ≤ n`; run 2 never recorded it. This is the classic ingredient for "two chains accepted in the same window share an honest slot".
- The grep hit `:8` is a module-doc line, not a declaration: "`MoltPetit.Model.Impl`. The safety theorem in `Model/Safety.lean` is stated".
- The output stopped at `:95` although `head -30` allowed more lines — the `grep -n "theorem\|def "` pattern returned only these 9 lines, so **`Model.lean` has no further `theorem `/`def ` lines matched by that pattern** (note the pattern requires a trailing space after `def`, and matches `theorem` anywhere on the line).

---

## 3. Design direction

**Not reached.** This run emitted no design prose whatsoever. Its entire output is:

- line 5 (assistant text, verbatim, in full): `I'll start with the salvage briefing, then the primary maps.`
- line 10 (Bash `description`, verbatim): `Confirm liveness_global, selectChain, HonestBlocksCover, Model.lean lemmas`

The only inferable intent is the ordering it announced — salvage briefing first, primary maps second, design third — and the four re-confirmation targets in the `description`. Note it did **not** re-run run 2's name-clash grep (`netRun`/`netStep`/`Adversary`/`Views`/`honestSlots`/`adoptAll`/`Network`), so this run adds no evidence about the intended vocabulary; run 2 remains the only source for that.

Planned files, definitions, theorem statements, proof sketches, lemma composition, dependencies on W1–W6, effort estimate: **none stated in this run.**

---

## 4. Decisions and rejected alternatives

**None recorded.** No decision text exists in the transcript. The two observable process choices:

1. It opened the run-2 salvage file **before** anything else, i.e. it treated the prior partial as its starting point rather than re-surveying from scratch.
2. It batched all four re-confirmation targets into **one** Bash call with `sed`/`grep` rather than issuing separate `Read`s — a deliberate token economy, and the reason a 13-second run still produced usable deltas.

---

## 5. Structured JSON

**None.** No `StructuredOutput` call and no drafted JSON appear anywhere in lines 4–12.

**Write to `/etheron-pod/rollout-work/designs/W7.json`: NOT MADE.** There is no `Write` tool call in the transcript, and `/etheron-pod/rollout-work/designs/` currently contains only `W1.json`, `W1.md`, `W2.json`, `W2.md`, `W5.json`, `W5.md` — no `W7.json`, no `W7.md`.

---

## 6. Planner working hypothesis — reaction

**It never got there.** The prompt (line 1, unread per protocol) contained a planner working hypothesis for W7, but no assistant text in lines 4–12 mentions, confirms, corrects or refutes it. The run died two tool calls in, before any design reasoning was emitted. All thinking blocks in this transcript are signature-only with `"thinking": ""` (lines 4, 8, 9 — line 9's signature is of the `narration` kind), so no reasoning text is recoverable either.

---

## 7. Open questions

**None raised by this run.** It stated no questions. Run 2's open questions are unchanged and unanswered by this run, except that its four re-confirmation targets can be read as an implicit checklist of what it wanted nailed down before designing: the exact `liveness_global` statement and proof head, the exact `selectChain` definition and its (absent) theorem surface, the exact `HonestBlocksCover` definition, and the reusable lemma inventory in `Model.lean`.

Two questions this run's *results* newly raise for the planner (raised here as consequences of the deltas, not asked by the subagent):

- A new multi-chain module must avoid three existing `selectChain` names, not one: `MoltPetit.Model.selectChain` (:141), `MoltPetit.Model.selectChainExport` (:307), and `MoltPetit.TS.Emitted.selectChain` (Int-typed, :209), plus `Molt.selectChain` (Verifier :136).
- `Model.lean:95 quorum_overlap (hn : 1 ≤ n)` and `Model.lean:88 LastCommonHeight.symm` are available and were absent from run 2's inventory; whether the W7 statement wants them is unanswered.
