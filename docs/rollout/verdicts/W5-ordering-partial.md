# W5 / ordering — PARTIAL verification salvage

> **WARNING — THIS IS A PARTIAL VERIFICATION. The verifier never returned a
> verdict.** It was killed by an HTTP 429 usage limit after 18 tool calls, having
> written exactly one sentence of prose and having stated no confirmation, no
> refutation, no severity and no conclusion. Everything below is *evidence it
> gathered*, reproduced faithfully. Nothing below is the verifier's judgement,
> and nothing below is the salvager's judgement either.

## Header

| | |
|---|---|
| Agent id | `ac2445934a3cd7c7d` |
| Workflow run | `wf_6b051052-ec7` (Verify phase, run 2) |
| Transcript | `/run/claude/agent/projects/-etheron-pod/c28ff38c-0cb1-500d-8726-22cd73943085/subagents/workflows/wf_6b051052-ec7/agent-ac2445934a3cd7c7d.jsonl` |
| Role | ADVERSARIAL VERIFIER of a Lean design proposal for `/etheron-pod/mini-consensus-lean` |
| Expected label (indexer-inferred) | **W5-ordering** |
| Confirmed label | **W5-ordering** — confirmed from transcript content (evidence below) |
| Transcript size | ~56 lines; line 55 is the rate-limit record, line 56 is empty |
| Lines seen by salvager | 52 (displayed lines 4–55 inclusive) |
| Lines skipped (read failure) | none |
| Lines not read by protocol | 1–3 (prompt + harness attachments) |
| Termination | Line 55: synthetic assistant message `"You've hit your session limit · resets 2pm (UTC)"`, `error: rate_limit`, `apiErrorStatus: 429`, `rateLimitType: five_hour`, `requestId: req_011Cek5RSGEEE59jcLtiDhTU`, timestamp `2026-09-05T09:44:29.944Z` |
| Wall-clock span of work | `09:42:07Z` → `09:44:29Z` (about 2m22s) |
| cwd / branch | `/etheron-pod` (Bash calls `cd /etheron-pod/mini-consensus-lean`), `gitBranch: HEAD` |
| Prompt size | first API call reports `cache_creation_input_tokens: 47205` |
| Assistant prose in the whole transcript | one sentence, line 5: *"I'll start by inspecting the repository layout and the files the design leans on."* All thinking blocks are signature-only (empty). |

### Label confirmation — the evidence

The prompt was not read (salvage protocol), so the label is inferred from the
files the verifier reached for and the tool descriptions it wrote.

**Work item = W5** (mode 3 per-generation census / erasure credit), not W1, W2,
W3a/b, W4, W6 or W7:

1. It read `MoltPetit/Model/KeyStealingLockstep.lean` **in full** (614 lines, via
   `cat -n` + a follow-up `Read` of the persisted 34.8 KB output) — mode 3.
2. It read `LOCKSTEP_DESIGN.md` lines **120–251**, i.e. precisely the
   *"⚠ Audit result (2026-08-01): PARTIAL — the factor-2 claim above is WRONG"*
   section, the three obstructions, the **D1′-thin vs D1′-full** recommendation
   and the H1–H5 phasing. D1′-full *is* the W5 topic.
3. It read `MoltPetit/Model/KeyStealingScheduleTimed.lean` for exactly the W5
   vocabulary: `NoPrematureTheft` (:96), `ErasureTimed` (:102),
   `theft_during_era_of_erasure` (:107), `recentTheftProducers` (:149),
   `PackageATimed` (:312) / `PackageBTimed` (:383).
4. It read `MoltPetit/Model/KeyStealingScheduleBudget.lean` at the
   `erasure_freeze` field of `PackageB` (:337) and
   `erasure_freeze_of_exposedBound` (:364) — the per-generation census /
   erasure-credit machinery.
5. It read `horizon_shared_prefix` (`KeyStealingScheduleHorizon.lean:161`) and
   its σ-localised sibling `sigma_shared_prefix`
   (`KeyStealingHorizonCore.lean:91`) in full — the "generalise
   `horizon_shared_prefix` to an arbitrary window" increment named by the audit
   as what D1′-full costs.
6. It `cat`-ed the first-run salvages `W1.md` and `W5.md` side by side —
   the two mode-3 items — and no other pair.

None of W2's (`AcceptedSuffixK`, trailing-5n, `cert_client_refresh_rule`), W4's
(`sync_rule`, client cadence) or W7's (multi-chain) subject matter was opened
for its own sake.

**Lens = ordering** (additive-only constraint + depends_on/enables + file-layout
idioms), not accuracy:

1. Its **second** command `cat docs/rollout/ROLLOUT_NOTES.md` in full — the file whose §
   "Ground rules" states the additive-only policy verbatim (reproduced in §3.1
   below) and whose §2 is the "Existing Lean touched" log. That is the ordering
   lens's governing document.
2. Its **first** command dumped `MoltPetit.lean`, `Molt.lean`, `lakefile.toml`
   and the directory listings of `MoltPetit/Model`, `MoltPetit/Results`, `Molt`
   — i.e. where a new module must be registered and what the file layout is.
3. It read `MoltPetit/Results/Axioms.lean` (import block + two guard regions)
   and `Molt/Axioms.lean` + `Molt/Rotation.lean` — the axiom-guard-file idiom and
   the `Molt` re-presentation idiom (fresh `def` + `_eq_core` rfl-bridge +
   `abbrev` alias + transported theorem).
4. It listed `/etheron-pod/rollout-work/designs-partial/` and `maps/`, then
   grepped **all six sibling designs** (`W1.md W2.md W3a-run2.md W4-run2.md
   W6-run2.md W7-run2.md`) for the identifiers this design would share with
   them — the depends_on/enables cross-check.
5. Its final two commands tried to extract the sibling designs' declared
   `new_files` / `"path"` / `"name"` / `touches_existing` keys — i.e. a
   file-collision / touch-collision check across work items. Both returned no
   output.

**Residual uncertainty:** the verifier never named the item or the lens in
prose, and the design text itself (in the prompt) was never quoted by it, so no
individual design *claim* can be quoted here. The label is inferred from tool
selection alone, at the same standard the indexer used.

---

## 1. Files examined, in order, with the reason

The reason column is the verifier's own Bash `description` field, verbatim,
except for the first row where the reason is its one line of prose.

| # | Line | Tool | Input (verbatim) | Why |
|---|---|---|---|---|
| 1 | 6 | Bash | `cd /etheron-pod/mini-consensus-lean && ls && cat MoltPetit.lean && echo ---- && cat Molt.lean && echo ---- && cat lakefile.toml && ls MoltPetit/Model MoltPetit/Results Molt` | "List repo root modules and layout" — and the prose at line 5: "I'll start by inspecting the repository layout and the files the design leans on." |
| 2 | 9 | Bash | `wc -l MoltPetit/Model/KeyStealingLockstep.lean MoltPetit/Model/KeyStealingScheduleHorizon.lean MoltPetit/Model/KeyStealingHorizonCore.lean MoltPetit/Model/KeyStealingHorizon.lean MoltPetit/Model/KeyStealingScheduleTimed.lean MoltPetit/Model/KeyStealingScheduleBudget.lean MoltPetit/Results/Axioms.lean Molt/Rotation.lean Molt/Axioms.lean docs/rollout/ROLLOUT_NOTES.md LOCKSTEP_DESIGN.md && cat docs/rollout/ROLLOUT_NOTES.md` | "Line counts and rollout ground rules" |
| 3 | 12 | Bash | `cat -n MoltPetit/Model/KeyStealingLockstep.lean` | "Read KeyStealingLockstep.lean in full" (output too large; persisted to `/run/claude/agent/projects/-etheron-pod/c28ff38c-0cb1-500d-8726-22cd73943085/tool-results/b1ukcovqc.txt`, 34.8 KB) |
| 4 | 15 | Read | `/run/claude/agent/.../tool-results/b1ukcovqc.txt` | retrieval of the persisted full text of `KeyStealingLockstep.lean` (all 614 lines seen) |
| 5 | 18 | Bash | `sed -n 1,60p MoltPetit/Model/KeyStealingHorizonCore.lean && echo ==== && grep -n "theorem\|^def\|^structure\|^private\|^noncomputable def\|^abbrev" MoltPetit/Model/KeyStealingHorizonCore.lean MoltPetit/Model/KeyStealingHorizon.lean` | "Inspect HorizonCore module header and declarations" |
| 6 | 21 | Bash | `sed -n 58,182p MoltPetit/Model/KeyStealingHorizonCore.lean` | "Read sigma_shared_prefix engine in HorizonCore" |
| 7 | 24 | Bash | `sed -n 60,260p MoltPetit/Model/KeyStealingScheduleHorizon.lean` | "Read horizon_shared_prefix and helpers" |
| 8 | 26 | Bash | `sed -n 260,400p MoltPetit/Model/KeyStealingScheduleHorizon.lean` | "Read horizon headlines" |
| 9 | 28 | Bash | `sed -n 80,230p MoltPetit/Model/KeyStealingScheduleTimed.lean` | "Read timed layer definitions" |
| 10 | 30 | Bash | `sed -n 230,423p MoltPetit/Model/KeyStealingScheduleTimed.lean` | "Read timed packages and headlines" |
| 11 | 32 | Bash | `sed -n 95,215p MoltPetit/Model/KeyStealingScheduleBudget.lean && echo ==== && sed -n 300,400p MoltPetit/Model/KeyStealingScheduleBudget.lean` | "Read schedule budget definitions and PackageB" |
| 12 | 34 | Bash | `grep -n "MaturedWindowsDense\|def HonestSlotsUnique\|def sigOk\|def sigsOk\|def ValidChain\|def IdInjective\|def ChainInRecord\|def badSlotsIn\|def maxByzantine\|def quorum\|def producerForSlot\|def windowCount\|def blockInWindow\|structure ValidChain" MoltPetit/Model/Definitions.lean && sed -n 484,510p MoltPetit/Model/Definitions.lean && sed -n 40,90p MoltPetit/Model/KeyStealingUnique.lean && sed -n 195,262p MoltPetit/Model/KeyStealingScheduleCert.lean && sed -n 80,100p MoltPetit/Model/KeyStealingSchedule.lean && sed -n 228,250p MoltPetit/Model/KeyStealingCert.lean && sed -n 45,62p MoltPetit/Model/KeyStealingBudget.lean` | "Read vocabulary definitions across model files" |
| 13 | 36 | Bash | `grep -n "theorem chainSlotsIn_card\|theorem chainSlotsIn_subset_Ico\|theorem mem_chainSlotsIn\|theorem exists_blockAt_of_mem\|def chainSlotsIn" MoltPetit/Model/Model.lean && grep -n "theorem same_block_same_prefix\|theorem height_gt_of_slot_gt\|theorem strictSlots_lt" MoltPetit/Model/Safety.lean MoltPetit/Model/*.lean && grep -n "theorem blockAt_getLast" MoltPetit/Model/Soundness.lean && grep -n "theorem validChainK_sound" MoltPetit/Model/KeyIndex.lean && sed -n 1,30p MoltPetit/Results/Axioms.lean && sed -n 470,530p MoltPetit/Results/Axioms.lean && sed -n 550,603p MoltPetit/Results/Axioms.lean` | "Confirm lemma locations and read axiom guard file" |
| 14 | 38 | Bash | `sed -n 1,20p Molt/Axioms.lean && grep -n "lockstep" Molt/Axioms.lean && sed -n 1,12p Molt/Rotation.lean && sed -n 125,170p Molt/Rotation.lean && sed -n 205,225p Molt/Rotation.lean && sed -n 380,437p Molt/Rotation.lean` | "Read Molt-side lockstep re-presentation and guards" |
| 15 | 40 | Bash | `ls -la /etheron-pod/rollout-work/designs-partial/ /etheron-pod/rollout-work/maps/ 2>&1; wc -l /etheron-pod/rollout-work/designs-partial/* 2>&1` | "List sibling designs and maps" |
| 16 | 42 | Bash | `sed -n 120,251p LOCKSTEP_DESIGN.md` | "Read LOCKSTEP_DESIGN audit and recommendation" |
| 17 | 45 | Bash | a 12-part `grep -n` over `KeyStealingScheduleHorizon.lean`, `KeyStealingScheduleBudget.lean`, `KeyStealingScheduleTimed.lean`, `KeyStealingScheduleCert.lean`, `KeyStealingSchedule.lean`, `KeyStealingCert.lean`, `KeyStealingUnique.lean`, `Results/Axioms.lean`, `Molt/Rotation.lean`, plus `sed -n 224,236p MoltPetit/Model/Definitions.lean` | "Verify all cited line numbers" |
| 18 | 47 | Bash | `cd /etheron-pod/rollout-work/designs-partial && grep -n -i "signedDeclared_of_mem_lock\|lockstep_const\|lockstep_rel\|window_producer_inj\|HonestSlotsUniqueOn\|window_shared_prefix\|sigma_shared_prefix\|horizon_shared_prefix\|NoPrematureTheftLock\|NoPrematureMintLock\|ErasureTimedLock\|badLockAt\|AlignedBounded\|LockstepPackageGen\|LockstepPackageTimed\|stolenAt\|depth\|2 \* n\|2n\|exists_honest_shared_slot_at\|slot_gap_of_position_gap\|lockstep_window_declares\|lockstep_declares_rosterGen\|rosterGen" W1.md W2.md W3a-run2.md W4-run2.md W6-run2.md W7-run2.md \| cut -c1-260` | "Grep sibling designs for shared identifiers" |
| 19 | 49 | Bash | `cat /etheron-pod/rollout-work/designs-partial/W1.md; echo ======; cat /etheron-pod/rollout-work/designs-partial/W5.md` | "Read W1 and W5 partial designs" |
| 20 | 51 | Bash | `cd /etheron-pod/rollout-work/designs-partial && grep -n "new_files\|\"path\"\|touches_existing\|\"name\"" W6-run2.md \| cut -c1-200 \| head -80` | "List W6 new files and defs" → **`(Bash completed with no output)`** |
| 21 | 53 | Bash | `cd /etheron-pod/rollout-work/designs-partial && grep -n "\"path\"\|\"name\"\|\"key\"" W4-run2.md W3a-run2.md W7-run2.md \| cut -c1-220 \| head -120` | "List W4, W3a, W7 new files and defs" → **`(Bash completed with no output)`** |

Distinct files it actually read bytes of, with the ranges seen:

| Path (relative to `/etheron-pod/mini-consensus-lean` unless absolute) | Ranges seen |
|---|---|
| `MoltPetit.lean` | whole file (32 import lines) |
| `Molt.lean` | whole file (9 imports + module doc) |
| `lakefile.toml` | whole file |
| `docs/rollout/ROLLOUT_NOTES.md` | whole file (71 lines) |
| `LOCKSTEP_DESIGN.md` | 120–251 (of 251) |
| `MoltPetit/Model/KeyStealingLockstep.lean` | 1–614 (whole) |
| `MoltPetit/Model/KeyStealingHorizonCore.lean` | 1–60, 58–182; declaration index of whole file |
| `MoltPetit/Model/KeyStealingHorizon.lean` | declaration index only (grep) |
| `MoltPetit/Model/KeyStealingScheduleHorizon.lean` | 60–260, 260–400; declaration index of whole file |
| `MoltPetit/Model/KeyStealingScheduleTimed.lean` | 80–230, 230–423; declaration index |
| `MoltPetit/Model/KeyStealingScheduleBudget.lean` | 95–215, 300–400; declaration index |
| `MoltPetit/Model/Definitions.lean` | 224–236, 484–510; declaration index |
| `MoltPetit/Model/KeyStealingUnique.lean` | 40–90; `chainUnionRecord`/`idInjective_keyrot` line numbers |
| `MoltPetit/Model/KeyStealingScheduleCert.lean` | 195–262; `SchedCoreUnforgeable`/`honestSlotsUnique_schedCore` line numbers |
| `MoltPetit/Model/KeyStealingSchedule.lean` | 80–100; `rotated_key_dead_sched`/`signedDeclared_of_mem_sched` line numbers |
| `MoltPetit/Model/KeyStealingCert.lean` | 228–250; `SignedDeclared`/`exists_signedChain_of_covered` line numbers |
| `MoltPetit/Model/KeyStealingBudget.lean` | 45–62 |
| `MoltPetit/Model/Model.lean` | line numbers only (grep) |
| `MoltPetit/Model/Safety.lean` | line numbers only (grep) |
| `MoltPetit/Model/Soundness.lean` | line number only (grep) |
| `MoltPetit/Model/KeyIndex.lean` | line number only (grep) |
| `MoltPetit/Results/Axioms.lean` | 1–30, 470–530, 550–603; plus greps |
| `Molt/Axioms.lean` | 1–20 + all `lockstep` lines |
| `Molt/Rotation.lean` | 1–12, 125–170, 205–225, 380–437; plus greps |
| `/etheron-pod/rollout-work/designs-partial/W1.md` | whole (105 lines) |
| `/etheron-pod/rollout-work/designs-partial/W5.md` | whole (78 lines) |
| `/etheron-pod/rollout-work/designs-partial/{W2,W3a-run2,W4-run2,W6-run2,W7-run2}.md` | grep hits only |
| `/etheron-pod/rollout-work/designs-partial/`, `/etheron-pod/rollout-work/maps/` | `ls -la` + `wc -l` |

Files it deliberately sized but never opened: `MoltPetit/Model/KeyStealingHorizon.lean` (339 lines — only the declaration index was taken).

---

## 2. Verdicts stated by the verifier

**None.** Not one confirmation, refutation, doubt, severity, or summary sentence
exists in the transcript after line 5. Sections 3 and 4 below therefore record
*what the tool results established* — the expensive part — and mark clearly that
the mapping from these facts to design claims was never made.

---

## 3. Ground truth established (evidence the verifier saw)

### 3.1 The additive-only constraint — `docs/rollout/ROLLOUT_NOTES.md`, read in full (71 lines)

Verbatim, the governing rule for the ordering lens:

> - **The paper is not edited until the Lean lands.** Everything that will change in
>   `paper/molt.tex` is logged in §1 below as it becomes known, with the phrase to
>   grep for, so the edit can be made in one targeted pass per page later.
> - **New Lean only.** New modules, new definitions, new theorems. Nothing existing is
>   modified. The only touches permitted to existing files are (a) one import line per
>   new module in a root module (`MoltPetit.lean`, `Molt.lean`) and (b) new axiom-guard
>   files rather than edits to an existing `Axioms.lean`. Every touch is logged in §2.
> - Axiom hygiene as in `CLAUDE.md`: every new headline theorem gets a `#guard_msgs`
>   guard; `#print axioms` must yield exactly `[propext, Classical.choice, Quot.sound]`.

Build commands recorded there:

    /etheron-pod/toolchains/lake.sh build MoltPetit.Model.<NewModule>
    /etheron-pod/toolchains/lake.sh build MoltPetit Molt      # everything + guards

The W5 row of §1 ("Paper changes pending — do NOT apply yet"), verbatim:

> | W5 | AN/9b | §2 mode 3 paragraph `erasure's per-generation credit against the budget is designed but not yet formalized`; §6.3 "Honest scope" second bound; mode 3 operator duties `(its budget credit: honest scope below)`; modes table erasure column | state the per-generation budget and cite it |

§2 **"Existing Lean touched"** — policy line and table, verbatim:

> Policy: none, except the two kinds of touch listed at the top. Log every one here.
>
> | Date | File | Touch | Why |
> |---|---|---|---|
> | — | — | — | — |

§3 **"New Lean added"** is likewise empty (`| — | — | — | — |`). §4 records that
the planning workflow's first run died on a usage limit and that recovery notes
live at `/etheron-pod/rollout-work/` (`journal-scan.md`, `maps/`,
`designs-partial/`).

### 3.2 File layout / registration idioms

`lakefile.toml` (whole): `name = "MoltPetit"`, `version = "0.1.0"`,
`defaultTargets = ["MoltPetit", "Rust", "Thales", "Molt"]`;
`[leanOptions]` `pp.unicode.fun = true`, `relaxedAutoImplicit = false`,
`weak.linter.mathlibStandardSet = true`, `maxSynthPendingDepth = 3`;
mathlib `scope = "leanprover-community"`, `rev = "v4.30.0-rc2"`; aeneas
`rev = "bf13c42e7c34d07fc396baffad39c93023b12914"`, `subDir = "backends/lean"`;
`lean_lib` targets `MoltPetit`, `Rust`, `Thales`, `Molt`; `lean_exe
moltpetit-demo` rooted at `Main`.

`MoltPetit.lean` — 32 import lines, in this order (the "current frontier" is the
tail): `MoltPetit.TS.Emitted`, `Model.Definitions`, `Model.Model`,
`Model.Safety`, `Model.Soundness`, `Model.Liveness`, `TS.Bridge`,
`Model.Grounded`, `Model.Timed`, `Results.Results`, `TS.Results`,
`Model.TimedSig`, `Model.KeyIndex`, `Model.KeyRotation`, `Model.KeyStealing`,
`Model.KeyStealingSafety`, `Model.KeyStealingUnique`,
`Results.KeyStealingResults`, `Model.KeyStealingCert`,
`Model.KeyRotationLiveness`, `Model.KeyStealingBudget`,
`Model.KeyStealingLongRange`, `TS.BridgeK`, `Model.KeyStealingSchedule`,
`Results.KeyStealingScheduleResults`, `Model.KeyStealingScheduleCert`,
`Model.KeyStealingScheduleBudget`, `Model.KeyStealingScheduleHorizon`,
`Model.KeyStealingLockstep`, `Model.KeyStealingHorizonCore`,
`Model.KeyStealingHorizon`, `Model.KeyStealingScheduleTimed`,
`Model.KeyRotationTests`, `Results.Axioms`, `MoltPetit.Custody`.

`Molt.lean` — imports `Molt.Protocol`, `Molt.Verifier`, `Molt.Assumptions`,
`Molt.Results`, `Molt.Rotation`, `Molt.ClientRule`, `Molt.MaxSync`,
`Molt.Liveness`, `Molt.Axioms`; module doc states the idiom verbatim:

> Proof engine: each fresh definition is bridged to its counterpart in the
> original `MoltPetit` development by a `rfl`-lemma, and every theorem is
> transported across those bridges — so everything here is machine-checked
> against the same core, and the axiom guards apply unchanged.
> Modules grow section by section with the paper; the imports above are the
> current frontier.

Directory listings seen: `Molt/` = Assumptions, Axioms, ClientRule, Liveness,
MaxSync, Protocol, Results, Rotation, Verifier (9 files).
`MoltPetit/Model/` = Definitions, Grounded, KeyIndex, KeyRotation,
KeyRotationLiveness, KeyRotationTests, KeyStealing, KeyStealingBudget,
KeyStealingCert, KeyStealingHorizon, KeyStealingHorizonCore,
KeyStealingLockstep, KeyStealingLongRange, KeyStealingSafety,
KeyStealingSchedule, KeyStealingScheduleBudget, KeyStealingScheduleCert,
KeyStealingScheduleHorizon, KeyStealingScheduleTimed, KeyStealingUnique,
Liveness, Model, Safety, Soundness, Timed, TimedSig (26 files).
`MoltPetit/Results/` = Axioms, KeyStealingResults, KeyStealingScheduleResults,
Results (4 files).

Line counts (`wc -l`, tool result at line 10):

    614 MoltPetit/Model/KeyStealingLockstep.lean
    523 MoltPetit/Model/KeyStealingScheduleHorizon.lean
    365 MoltPetit/Model/KeyStealingHorizonCore.lean
    339 MoltPetit/Model/KeyStealingHorizon.lean
    423 MoltPetit/Model/KeyStealingScheduleTimed.lean
    473 MoltPetit/Model/KeyStealingScheduleBudget.lean
    603 MoltPetit/Results/Axioms.lean
    437 Molt/Rotation.lean
    162 Molt/Axioms.lean
     71 docs/rollout/ROLLOUT_NOTES.md
    251 LOCKSTEP_DESIGN.md

### 3.3 Import DAG relevant to a new mode-3 module (all from the file headers it read)

- `MoltPetit/Model/KeyStealingLockstep.lean:1-2` — `import
  MoltPetit.Model.KeyStealingScheduleBudget`, `import
  MoltPetit.Results.KeyStealingScheduleResults`. **It does not import the
  horizon or the timed modules.**
- `MoltPetit/Model/KeyStealingScheduleHorizon.lean:1` — `import
  MoltPetit.Model.KeyStealingScheduleCert` (its only import).
- `MoltPetit/Model/KeyStealingScheduleBudget.lean:1-2` — `import
  MoltPetit.Model.KeyStealingScheduleCert`, `import
  MoltPetit.Model.KeyStealingBudget`.
- `MoltPetit/Model/KeyStealingScheduleTimed.lean:1-2` — `import
  MoltPetit.Model.KeyStealingScheduleHorizon`, `import
  MoltPetit.Model.KeyStealingScheduleBudget`.
- `MoltPetit/Model/KeyStealingHorizonCore.lean:1-2` — `import
  MoltPetit.Model.KeyStealingSafety`, `import MoltPetit.Model.KeyStealingUnique`.
- `Molt/Rotation.lean:1-7` — `import Molt.Results`, `MoltPetit.Results.KeyStealingResults`,
  `MoltPetit.Results.KeyStealingScheduleResults`, `MoltPetit.Model.KeyStealingHorizon`,
  `MoltPetit.Model.KeyStealingLockstep`, `MoltPetit.Model.KeyStealingCert`,
  `MoltPetit.Model.KeyStealingScheduleCert`.
- `Molt/Axioms.lean:1-5` — `import Molt.Results`, `Molt.Rotation`,
  `Molt.ClientRule`, `Molt.MaxSync`, `Molt.Liveness`.

### 3.4 `MoltPetit/Model/KeyStealingLockstep.lean` — read in full, 614 lines

Declarations, with the line numbers the `cat -n` output gave:

| Line | Declaration | Notes seen |
|---|---|---|
| 76 | `def lockstepOk (n : Nat) : Chain → Bool` | `\| [] => true \| b :: rest => rest.all (fun b' => decide ((b.slot / n = b'.slot / n → b.keyIndex = b'.keyIndex) ∧ b.keyIndex ≤ b'.keyIndex)) && lockstepOk n rest` |
| 84 | `theorem lockstepOk_iff_pairwise {n : Nat} (c : Chain)` | `lockstepOk n c = true ↔ c.Pairwise (…)` |
| 103 | `def validSignedChainLock {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool` | `sigsOk n ops registry sc && validChainK n (stripSigs sc) && lockstepOk n (stripSigs sc)` — "No schedule parameter — nothing here references `rosterGen`." |
| 112 | `def lagSched (n : Nat) (rosterGen : Nat → Nat) (s : Nat) : Nat := rosterGen (s / n - 1)` | "the lag is what absorbs the one unmatured tip window" |
| 120 | `theorem schedPinned_mono {sched₁ sched₂} (hle : ∀ s, sched₁ s ≤ sched₂ s) {c} (h : schedPinned sched₂ c = true) : schedPinned sched₁ c = true` | |
| 130 | `theorem schedCore_mono … (hle : ∀ s, sched₁ s ≤ sched₂ s) (h : validSignedChainSchedCore n sched₂ … = true) : validSignedChainSchedCore n sched₁ … = true` | |
| 141 | `theorem schedCoreUnforgeable_mono … (hle : ∀ s, sched₁ s ≤ sched₂ s) (h : SchedCoreUnforgeable n sched₁ …) : SchedCoreUnforgeable n sched₂ …` | |
| 154 | `theorem schedCore0_of_lock … (h : validSignedChainLock n ops registry sc = true) : validSignedChainSchedCore n (fun _ => 0) ops registry sc = true` | |
| 172 | `private theorem lockstep_rel` | PRIVATE |
| 195 | `private theorem lockstep_const` | PRIVATE |
| 211 | `private theorem head_slot_min` | PRIVATE |
| 220 | `private theorem window_producer_inj'` | PRIVATE; a **local copy** — the `KeyStealingScheduleBudget` original `window_producer_inj` (:~123) is itself private |
| 252 | `structure LockstepPackage (n : Nat) (rosterGen : Nat → Nat) {Sig sk pk : Type} (ops) (registry) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block) (now Δ : Nat) (G : Block) (R T : Nat) : Prop` | fields at 256–265, listed below |
| 269 | `theorem LockstepPackage.toPackageA … : PackageA n (lagSched n rosterGen) ops registry rented Stolen honestSigned now Δ G R T` | built `where unforgeable := schedCoreUnforgeable_mono (fun _ => Nat.zero_le _) hP.unforgeable; hashInj := hP.hashInj; rentBound := hP.rentBound; exposedBound := hP.exposedBound; budget_le := hP.budget_le` |
| 299 | `theorem lockstep_declares_rosterGen` | the pinning theorem; full signature below |
| 474 | `theorem lockstep_validSignedChainSched … : validSignedChainSched n (lagSched n rosterGen) ops registry sc = true` | the lagged-schedule transport |
| 555 | `theorem lockstep_recent_tip_ancestor_agreement` | headline, equal-tip form; proved by `packageA_recent_tip_ancestor_agreement hn hP.toPackageA …` |
| 586 | `theorem lockstep_recent_tip_ancestor_mem` | headline, membership form; proved by `sched_recent_tip_ancestor_mem hn (schedUnforgeable_of_core hP.toPackageA.unforgeable) hP.hashInj (packageA_byzantine_bounded hP.toPackageA) …` |

`LockstepPackage` fields, verbatim (lines 256–265):

```
  mono : ∀ ⦃w w' : Nat⦄, w ≤ w' → rosterGen w ≤ rosterGen w'
  unforgeable :
    SchedCoreUnforgeable n (fun _ => 0) ops registry rented Stolen honestSigned now Δ
  declared : ∀ ⦃i s : Nat⦄ ⦃B : Block⦄, honestSigned i s = some B →
    B.keyIndex = rosterGen (s / n)
  hashInj : SignedHashInjective (SignedDeclared n ops registry) G
  genesis_gen : G.keyIndex = rosterGen (G.slot / n)
  rentBound : ∀ u, (badSlotsIn rented u n).card ≤ R
  exposedBound : ∀ u, (exposedProducersSched n (lagSched n rosterGen) Stolen u).card ≤ T
  budget_le : R + T ≤ maxByzantine n
```

`lockstep_declares_rosterGen`, verbatim signature (lines 299–311):

```
theorem lockstep_declares_rosterGen
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hRecent : ∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) :
    ∀ W, ∀ B ∈ stripSigs sc, B.slot / n = W →
      (∃ D ∈ stripSigs sc, W * n + n ≤ D.slot + 1) →
      B.keyIndex = rosterGen W
```

Its proof (seen in full) is `induction W using Nat.strongRecOn`, base case window
0 discharged via `lockstep_const` against genesis + `hP.genesis_gen`; the step
uses `hDense` (`MaturedWindowsDense`) twice, extracts a previous-window block `A`
pinned by the IH, derives `hlow : rosterGen (W - 1) ≤ B.keyIndex` from
`lockstep_rel`, then the census `hSsub : chainSlotsIn … ⊆ badSlotsIn rented (W*n) n ∪
(Finset.Ico (W*n) (W*n+n)).filter (fun s => theftSched n (lagSched n rosterGen) Stolen s)`,
`hinj` via `window_producer_inj'`, `hTb ≤ T` via `hP.exposedBound (W * n)`,
`hRb := hP.rentBound (W * n)`, `hmb : maxByzantine n < quorum n`, `hP.budget_le`,
`omega`.

**Module doc, "Honest scope (what 'thin' means)" — the passage that names the
W5 gap, verbatim (lines 46–62):**

> The package's budget field is `exposedBound` at the lagged schedule — the
> **cumulative** census, exactly `PackageA`'s shape. The distinctive
> per-generation census (`erasure_freeze` as the load-bearing bound) is **not**
> delivered: the agreement engine's pigeonhole runs at the sliding trailing
> window, which straddles the un-pinned tip window, so the consulted census
> stays cumulative (`LOCKSTEP_DESIGN.md`, audit obstruction 2). Earning the
> per-generation reading is the D1′-full increment. The EUF-CMA surface is
> assumed at the **weakest** validator (`SchedCoreUnforgeable` at the constant-0
> schedule) so that its scope covers lockstep-accepted chains without
> circularity — the existing full-to-core precedent, one step further;
> `schedCoreUnforgeable_mono` then delivers it wherever the transport needs it.
> `rosterGen` itself is a genuine extra hypothesis relative to `PackageA` — an
> assumption about honest *coordination* (all honest signers track one
> generation counter), disclosed as such, and the formal content of "lockstep
> coordination is necessary after that".

### 3.5 `MoltPetit/Model/KeyStealingScheduleHorizon.lean` (523 lines)

Declaration index (grep, tool result at line 46):

    1:import MoltPetit.Model.KeyStealingScheduleCert
     86: private theorem exists_honest_shared_slot_at
    116: private theorem slot_gap_of_position_gap
    161: theorem horizon_shared_prefix
    247: theorem sched_recent_tip_ancestor_agreement_horizon
    308: theorem sched_recent_tip_ancestor_mem_horizon
    365: theorem sched_recent_genesis_agreement_horizon
    414: theorem sched_recent_tip_ancestor_agreement_horizon_core
    471: theorem sched_recent_tip_ancestor_mem_horizon_core

`ByzantineBoundedFrom`, verbatim:

```
def ByzantineBoundedFrom (H n : Nat) (bad : ByzantineSlots) : Prop :=
  ∀ u, H ≤ u → (badSlotsIn bad u n).card ≤ maxByzantine n

theorem byzantineBoundedFrom_of_bounded {H n : Nat} {bad : ByzantineSlots}
    (h : ByzantineBounded n bad) : ByzantineBoundedFrom H n bad :=
  fun u _ => h u
```

`horizon_shared_prefix`, verbatim signature (161–…):

```
theorem horizon_shared_prefix
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hHonest : HonestSlotsUnique bad record)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hle : tip.slot ≤ tip'.slot)
    (hBudgetU : (badSlotsIn bad (tip.slot + 1 - n) n).card ≤ maxByzantine n)
    {k : Nat} (hkdeep : k + n < c.length) :
    ∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P
```

Docstring, verbatim: "**Top-window shared prefix (the horizon core).** …
Validator-agnostic — consumed below by both the full and the core scheduled
validators. The proof runs the `2q > n + f` pigeonhole at `u = tip.slot + 1 − n`
(matured in both chains, since `tip.slot ≤ tip'.slot`): the shared non-corrupt
slot's two blocks are equal by honest-slot uniqueness, sit strictly above height
`k` (their slot exceeds `B`'s, and slots order heights), and
`same_block_same_prefix` carries the agreement down to `k`. No hypothesis touches
any window below `u`, and no shared genesis is assumed."

The window is fixed in the body by `set u := tip.slot + 1 - n with hu` — there is
no window parameter. The chain of steps inside: `blockAt_getLast`,
`slot_gap_of_position_gap hS (c.length - 1 - k) k hB …` giving
`hgap : B.slot + n ≤ tip.slot`, `chainSlotsIn_card hS` + `hDense hTipAt u`,
`exists_honest_shared_slot_at hn hBudgetU chainSlotsIn_subset_Ico
chainSlotsIn_subset_Ico hq hq'`, `mem_chainSlotsIn.mp`, `hHonest s hsHonest`,
`height_gt_of_slot_gt`, `same_block_same_prefix`.

The three consumers all follow the same shape (seen in full): a
`rcases Nat.le_total sTip.slot sTip'.slot` case split that rebuilds
`hId := idInjective_keyrot hHash hSig hSig'` and
`hUniq := honestSlotsUnique_sched hUnf hVal hVal' …` **with the arguments
swapped** in the second branch, then calls `horizon_shared_prefix … (hBudget _ (by
omega)) (k := …)`. Their extra hypotheses over the non-horizon forms are
`hH : H + n ≤ sTip.slot + 1` and `hH' : H + n ≤ sTip'.slot + 1`, and their budget
hypothesis is `hBudget : ByzantineBoundedFrom H n (badSched n schedule rented
Stolen)`. `sched_recent_genesis_agreement_horizon` instantiates `(k := 0)`.

### 3.6 `MoltPetit/Model/KeyStealingHorizonCore.lean` (365 lines)

Declaration index:

     58: private theorem exists_honest_shared_slot_at      (a SECOND private copy — HorizonCore has its own)
     91: theorem sigma_shared_prefix
    151: theorem confirmed_mem_iff_horizon
    183: theorem honestSlotsUnique_keyrot_horizon
    258: theorem honestSlotsUnique_keyrot_anchored

`sigma_shared_prefix` is the σ-localised variant: pigeonhole at `[σ-n, σ)`,
budget hypothesis `hBudgetU : (badSlotsIn bad (σ - n) n).card ≤ maxByzantine n`,
uniqueness only strictly below σ
(`hHonestLt : ∀ τ, τ < σ → ¬ bad τ → ∀ ⦃B B'⦄, B ∈ record τ → B' ∈ record τ → B = B'`),
coexistence blocks `Bσ ∈ c`, `Bσ' ∈ c'` with `.slot = σ`, conclusion
`blockAt? c k = some b → b.slot + n ≤ σ → blockAt? c' k = some b`. No genesis
hypothesis.

Module doc, the transport caveat, verbatim:

> What does **not** transport from the scheduled variant is the budget
> contraction `ByzantineBoundedFrom`: mode 1's `badKeyrotOn` is chain-relative, so
> the slot-induction must still reconcile `inForce` across the two chains, and
> that induction consults windows all the way down. Chain-independence of
> `badSched` is load-bearing upstream in `honestSlotsUnique_sched`, not inside the
> horizon core — which is why the core transports here verbatim and the budget
> contraction does not.

and: "`n ≤ Δconf` is also the *semantic* floor, independently of this proof:
`inForce_agreement` (`KeyRotation.lean`) needs `n ≤ Δconf` to make `inForce`
execution-global, hence `badKeyrotOn` a genuine slot predicate."

### 3.7 `MoltPetit/Model/KeyStealingScheduleTimed.lean` (423 lines) — the W5 timed vocabulary

```
 90: def stolenOf (stolenAt : Nat → Nat → Nat → Prop) (i j : Nat) : Prop := ∃ r, stolenAt i j r
 96: def NoPrematureTheft (R : Nat) (stolenAt : Nat → Nat → Nat → Prop) : Prop :=
       ∀ i j r, stolenAt i j r → j * R ≤ r
102: def ErasureTimed (R : Nat) (stolenAt : Nat → Nat → Nat → Prop) : Prop :=
       ∀ i j r, stolenAt i j r → r < (j + 1) * R
107: theorem theft_during_era_of_erasure {R} {stolenAt}
       (hA3 : NoPrematureTheft R stolenAt) (hEr : ErasureTimed R stolenAt)
       {i j r : Nat} (h : stolenAt i j r) : j * R ≤ r ∧ r < (j + 1) * R
       := ⟨hA3 i j r h, hEr i j r h⟩
122: theorem theft_is_recent {R : Nat} (hR : 0 < R) {stolenAt}
       (hA3 : NoPrematureTheft R stolenAt) {n s : Nat}
       (h : theftSched n (fun t => t / R) (stolenOf stolenAt) s) :
       ∃ j r, s / R ≤ j ∧ stolenAt (producerForSlot n s) j r ∧ s < r + R
149: noncomputable def recentTheftProducers (n R : Nat)
       (stolenAt : Nat → Nat → Nat → Prop) (u : Nat) : Finset Nat :=
       (Finset.range n).filter (fun i => ∃ j r, u / R ≤ j ∧ stolenAt i j r ∧ u < r + R)
156: theorem exposedSched_subset_recentTheft {n R} (hn : 0 < n) (hR : 0 < R) {stolenAt}
       (hA3 : NoPrematureTheft R stolenAt) (u : Nat) :
       exposedProducersSched n (fun s => s / R) (stolenOf stolenAt) u
         ⊆ recentTheftProducers n R stolenAt u
187: theorem horizon_budget_of_timed {n R H : Nat} (hn : 0 < n) (hR : 0 < R)
       {rented} {stolenAt} {Rrent T : Nat}
       (hA3 : NoPrematureTheft R stolenAt)
       (hRent  : ∀ u, H ≤ u → (badSlotsIn rented u n).card ≤ Rrent)
       (hTheft : ∀ u, H ≤ u → (recentTheftProducers n R stolenAt u).card ≤ T)
       (hRT : Rrent + T ≤ maxByzantine n) :
       ByzantineBoundedFrom H n (badSched n (fun s => s / R) rented (stolenOf stolenAt))
231: def NoPrematureMint (R : Nat) (log : TimedLog) : Prop :=
       ∀ r, ∀ B ∈ log r, B.keyIndex * R ≤ r
     theorem sched_forwardstamp_bounded {R} (hR : 0 < R) {log} (hMint : NoPrematureMint R log)
       {c} (hPin : schedPinned (fun s => s / R) c = true) {B} (hB : B ∈ c) {r} (hr : B ∈ log r) :
       B.slot < r + R
     theorem sched_recent_block_fresh … : now < r + Δ + R
284: theorem sched_backdate_consistent (R r : Nat) :
       ∃ (log : TimedLog) (B : Block), NoPrematureMint R log ∧ B ∈ log r ∧ B.slot = 0 ∧
         schedPinned (fun s => s / R) [B] = true
312: structure PackageATimed (n R H : Nat) … (Rrent T : Nat) : Prop where
       unforgeable : SchedCoreUnforgeable n (fun s => s / R) ops registry rented
           (stolenOf stolenAt) honestSigned now Δ
       hashInj : SignedHashInjective (SignedDeclared n ops registry) G
       notBefore : NoPrematureTheft R stolenAt
       rentBound : ∀ u, H ≤ u → (badSlotsIn rented u n).card ≤ Rrent
       recentTheftBound : ∀ u, H ≤ u → (recentTheftProducers n R stolenAt u).card ≤ T
       budget_le : Rrent + T ≤ maxByzantine n
326: theorem packageATimed_horizon_budget …
     theorem packageATimed_recent_tip_ancestor_agreement …
383: structure PackageBTimed (n R H : Nat) … extends PackageATimed … : Prop where
       notAfter : ErasureTimed R stolenAt
394: theorem packageBTimed_recent_tip_ancestor_agreement … :=
       packageATimed_recent_tip_ancestor_agreement hn hR hPB.toPackageATimed …
```

Note the whole timed layer is stated at the **flagship schedule `fun s => s / R`**,
not an arbitrary `schedule : Nat → Nat`.

`recentTheftProducers`' docstring carries a self-limiting remark, verbatim:

> (It remains future-inclusive — module doc, honest scope. Note the conjunct
> `u < r + R` is *redundant under* `NoPrematureTheft`: any theft of a generation
> `≥ u / R` already happened after `u − R`, so under A3 this census coincides
> extensionally with the pure generation-floor census
> `∃ j ≥ u / R, stolenOf stolenAt i j` — the real-time pin documents the
> derived backward locality rather than adding a restriction, and the rate a
> deployment asserts is extensionally a timeless one.)

`PackageBTimed`'s docstring, verbatim: "…the `extends` records the
assumption-set inclusion 'B assumes A plus erasure'; the erasure field is
documentary for the safety chain (which A's fields already deliver) and is what
a deployment's per-era compromise accounting instantiates."

### 3.8 `MoltPetit/Model/KeyStealingScheduleBudget.lean` (473 lines) — `erasure_freeze`

```
101: def theftSched (n : Nat) (schedule : Nat → Nat) (Stolen : Nat → Nat → Prop) (s : Nat) : Prop :=
       ∃ j, schedule s ≤ j ∧ Stolen (producerForSlot n s) j
     theorem badSched_iff_or … := Iff.rfl
117: noncomputable def exposedProducersSched (n : Nat) (schedule : Nat → Nat)
       (Stolen : Nat → Nat → Prop) (u : Nat) : Finset Nat :=
       (Finset.Ico u (u + n)).filter (fun s => theftSched n schedule Stolen s) |>.image
         (producerForSlot n)
123: private theorem window_producer_inj   -- PRIVATE ("Local copy of the KeyStealingBudget lemma,
                                            -- which is private there.")
148: theorem theftSlotsSched_card_le_exposed (n) (schedule) (Stolen) (u) :
       (badSlotsIn (theftSched n schedule Stolen) u n).card ≤
         (exposedProducersSched n schedule Stolen u).card
164: theorem induced_byzantine_bounded_sched {n} {schedule} {rented} {Stolen} {R T}
       (hRent : ∀ u, (badSlotsIn rented u n).card ≤ R)
       (hExposed : ∀ u, (exposedProducersSched n schedule Stolen u).card ≤ T)
       (hRT : R + T ≤ maxByzantine n) :
       ByzantineBounded n (badSched n schedule rented Stolen)
     structure PackageA … : Prop where
       unforgeable : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ
       hashInj : SignedHashInjective (SignedDeclared n ops registry) G
       rentBound : ∀ u, (badSlotsIn rented u n).card ≤ R
       exposedBound : ∀ u, (exposedProducersSched n schedule Stolen u).card ≤ T
       budget_le : R + T ≤ maxByzantine n
331: structure PackageB … extends PackageA … : Prop where
337:   erasure_freeze : ∀ j : Nat, ((Finset.range n).filter (fun i => Stolen i j)).card ≤ T
338: theorem schedule_div_full_window {n R : Nat} (hR : n ≤ R) (hR0 : 0 < R) :
       ∀ j : Nat, ∃ u, ∀ s, u ≤ s → s < u + n → s / R = j
364: theorem erasure_freeze_of_exposedBound {n} {schedule} {Stolen} {T}
       (hExposed : ∀ u, (exposedProducersSched n schedule Stolen u).card ≤ T)
       (hFull : ∀ j : Nat, ∃ u, ∀ s, u ≤ s → s < u + n → schedule s = j) :
       ∀ j : Nat, ((Finset.range n).filter (fun i => Stolen i j)).card ≤ T
```

**`PackageB`'s docstring — the paragraph directly about the W5 target, verbatim
(lines ~313–330):**

> **Honest weight of the field (review-driven).** `erasure_freeze` is consumed
> by no proof — and for schedules in which every generation contains a full
> `n`-window (the flagship `s / R` with `R ≥ n`) it is **implied** by
> `exposedBound` (proven: `erasure_freeze_of_exposedBound`), so there `PackageB`
> is logically `PackageA`. `PackageB.toPackageA` therefore records an
> **assumption-set inclusion** (B assumes at least A) — documentary, not a
> nontrivial reduction; its value is stating B's mechanism. The genuinely-B
> discharge of §10.2 — no-mixing forces any fork to a single generation, so a
> per-generation census suffices *without* the cumulative reading — is a
> different proof shape requiring the unmodeled B1 no-mixing rule (validator
> scope note). Nor would a timed model derive the current `exposedBound` from
> `erasure_freeze`: even in a faithful-B world (thefts only while live), letting
> *different* producers lose keys in *different* generations satisfies
> `erasure_freeze` yet falsifies the cumulative `exposedBound` at genesis-era
> windows; a timed model would instead replace the budget's *shape* by a
> horizon-scoped one — the §10.4 seam. Both packages, like the default model,
> assume the budget in its cumulative reading. B3/B0 are as A3/A0: prose-level
> instantiation justifications.

`schedule_div_full_window`'s docstring adds: "(For `R < n` the premise genuinely
fails — a generation has fewer than `n` slots, so some producer never produces in
it.)"

### 3.9 Shared vocabulary — exact locations confirmed by grep

| Name | File:line |
|---|---|
| `quorum` (`(2 * n + 2) / 3`) | `Model/Definitions.lean:44` |
| `maxByzantine` (`(n - 1) / 3`) | `Model/Definitions.lean:47` |
| `producerForSlot` (`slot % n`) | `Model/Definitions.lean:50` |
| `blockInWindow` | `Model/Definitions.lean:78` |
| `windowCount` | `Model/Definitions.lean:82` |
| `sigOk` | `Model/Definitions.lean:226` |
| `sigsOk` | `Model/Definitions.lean:231` |
| `MaturedWindowsDense` | `Model/Definitions.lean:484` |
| `ValidChain` | `Model/Definitions.lean:490` |
| `ChainInRecord` | `Model/Definitions.lean:494` |
| `HonestSlotsUnique` | `Model/Definitions.lean:498` |
| `IdInjective` | `Model/Definitions.lean:503` |
| `badSlotsIn` (noncomputable) | `Model/Definitions.lean:509` |
| `mem_chainSlotsIn` | `Model/Model.lean:35` |
| `chainSlotsIn_subset_Ico` | `Model/Model.lean:40` |
| `strictSlots_lt` | `Model/Model.lean:47` |
| `chainSlotsIn_card` | `Model/Model.lean:60` |
| `exists_blockAt_of_mem` | `Model/Model.lean:71` |
| `height_gt_of_slot_gt` | `Model/Safety.lean:29` |
| `same_block_same_prefix` | `Model/Safety.lean:189` |
| `blockAt_getLast` | `Model/Soundness.lean:97` |
| `validChainK_sound` | `Model/KeyIndex.lean:215` |
| `chainUnionRecord` | `Model/KeyStealingUnique.lean:45` |
| `mem_chainUnionRecord` | `Model/KeyStealingUnique.lean:48` |
| `chainInRecord_left` / `_right` | `Model/KeyStealingUnique.lean:~54/~60` |
| `idInjective_keyrot` | `Model/KeyStealingUnique.lean:70` |
| `badKeyrotOn_iff_or` | `Model/KeyStealingBudget.lean:45` |
| `badSlotsIn_union_le` | `Model/KeyStealingBudget.lean:52` |
| `exposedProducers` (noncomputable) | `Model/KeyStealingBudget.lean:62` |
| `rotated_key_dead_sched` | `Model/KeyStealingSchedule.lean:67` |
| `signedDeclared_of_mem_sched` | `Model/KeyStealingSchedule.lean:88` |
| `SignedDeclared` | `Model/KeyStealingCert.lean:234` |
| `exists_signedChain_of_covered` | `Model/KeyStealingCert.lean:247` |
| `validChain_of_validSignedChainSchedCore` | `Model/KeyStealingScheduleCert.lean:125` |
| `rotated_key_dead_schedCore` | `Model/KeyStealingScheduleCert.lean:135` |
| `SchedCoreUnforgeable` (structure) | `Model/KeyStealingScheduleCert.lean:200` |
| `schedUnforgeable_of_core` | `Model/KeyStealingScheduleCert.lean` (just after `SchedCoreUnforgeable`) |
| `honestSlotsUnique_schedCore` | `Model/KeyStealingScheduleCert.lean:231` |

`SchedCoreUnforgeable`'s single field, verbatim:

```
  unforgeable :
    ∀ {sc : SignedChain Sig} {sb : SignedBlock Sig} {j : Nat},
      validSignedChainSchedCore n schedule ops registry sc = true →
      sb ∈ sc →
      (∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) →
      ops.verify (registry (producerForSlot n sb.block.slot) j) sb.block sb.sig = true →
      ¬ rented sb.block.slot →
      ¬ Stolen (producerForSlot n sb.block.slot) j →
      honestSigned (producerForSlot n sb.block.slot) sb.block.slot = some sb.block
```

### 3.10 Axiom-guard idiom — `MoltPetit/Results/Axioms.lean` (603 lines) and `Molt/Axioms.lean` (162 lines)

`Results/Axioms.lean` opens with 25 imports (`MoltPetit.Results.Results`,
`MoltPetit.TS.Results`, … through `MoltPetit.Model.KeyStealingScheduleTimed`) and
a doc "# Axiom audit — model and TypeScript results / Every headline theorem the
paper states is checked here against Lean's axioms."

Guard blocks the verifier read verbatim, in file order (470–530, 550–603):

- horizon set: `horizon_shared_prefix`, `sched_recent_tip_ancestor_agreement_horizon`,
  `sched_recent_tip_ancestor_mem_horizon`,
  `sched_recent_tip_ancestor_agreement_horizon_core` (`whitespace := lax`),
  `byzantineBoundedFrom_of_bounded` — all `[propext, Classical.choice, Quot.sound]`.
- timed set, preceded by an eight-line `--` comment block describing the seam
  ("the timed theft layer (seam §10.4 part 2) … Residual (module doc): the
  census is future-inclusive; confining it to thefts before the client's
  validation time needs a timed EUF-CMA surface keying on theft-before-mint
  (next increment)"): `theft_is_recent` **`[propext, Quot.sound]`**,
  `exposedSched_subset_recentTheft`, `horizon_budget_of_timed`,
  `sched_forwardstamp_bounded` **`[propext, Quot.sound]`**,
  `sched_recent_block_fresh` **`[propext, Quot.sound]`**,
  `theft_during_era_of_erasure` **"does not depend on any axioms"** (line 512),
  `packageATimed_recent_tip_ancestor_agreement` (lax),
  `packageBTimed_recent_tip_ancestor_agreement` (lax),
  `sched_recent_genesis_agreement_horizon` (lax),
  `sched_recent_tip_ancestor_mem_horizon_core` (lax),
  `sched_backdate_consistent` **`[propext, Quot.sound]`**.
- mode-3 block, preceded by an eight-line `--` comment ("Free-cadence lockstep
  rotation (mode 3, D1'-thin) … Assumption-wise the package is PackageA at the
  lagged schedule plus the behavioural rosterGen fields"):
  `lockstep_declares_rosterGen`, `lockstep_validSignedChainSched`,
  `lockstep_recent_tip_ancestor_agreement`, `lockstep_recent_tip_ancestor_mem`.
- anchored-horizon block: `honestSlotsUnique_keyrot_anchored`,
  `keyrot_recent_tip_ancestor_agreement_anchored`,
  `keyrot_recent_tip_ancestor_mem_anchored`,
  `keyrot_recent_tip_ancestor_agreement_horizon`,
  `keyrot_recent_tip_ancestor_agreement_horizon_of_valid`.

Idiom details: each guard is `/-- info: '<FullName>' depends on axioms: [propext,
Classical.choice, Quot.sound] -/` + `#guard_msgs in` + `#print axioms <FullName>`;
`#guard_msgs (whitespace := lax) in` is used where the expected message wraps
(observed at lines 480, 516, 519 and elsewhere); the only two "does not depend on
any axioms" guards in the file are at lines 365 (`keyMonoFrom_congr_lt`) and 512
(`theft_during_era_of_erasure`).

`Molt/Axioms.lean` doc: "Same discipline as `MoltPetit/Results/Axioms.lean`: a
guarded `#print axioms` per headline theorem, so `lake build Molt` fails if any
theorem ever picks up an axiom beyond the three classical ones. **Extend this file
with every new headline theorem.**" Existing lockstep guards: line 67/69
`Molt.lockstep_declares_rosterGen`; 128/130 `Molt.lockstep_recent_tip_ancestor_mem`;
141–144 `-- Theorem 5: lockstep safety (paper §6.3, mode 3).` +
`Molt.lockstep_client_safety`.

### 3.11 The `Molt` re-presentation idiom — `Molt/Rotation.lean` (437 lines)

Fresh definitions restated in paper vocabulary, then bridged:

```
def noMixing (n : Nat) : Chain → Bool                        -- mode 3's "no-mixing rule"
def validSignedChainLock {σ sk pk : Type} (n : Nat) (ops) (registry) (sc) : Bool :=
  sigsOk n ops registry sc && validChainK n (stripSigs sc) && noMixing n (stripSigs sc)
164: abbrev LockstepPackage := @MoltPetit.Model.LockstepPackage
     abbrev SchedUnforgeable := @MoltPetit.Model.SchedUnforgeable
     abbrev badSched := @MoltPetit.Model.badSched
     abbrev SignedDeclared := @MoltPetit.Model.SignedDeclared
     theorem noMixing_eq_core : noMixing = MoltPetit.Model.lockstepOk := by
       funext n c; induction c with | nil => rfl
       | cons b rest ih => simp only [noMixing, MoltPetit.Model.lockstepOk, ih]
217: theorem validSignedChainLock_eq_core {σ sk pk : Type} :
       (validSignedChainLock (σ := σ) (sk := sk) (pk := pk)) = MoltPetit.Model.validSignedChainLock
406: theorem lockstep_client_safety … : B = B' := by
432:   rw [validSignedChainLock_eq_core] at hVal hVal'
       exact MoltPetit.Model.lockstep_recent_tip_ancestor_agreement hn hP
         hVal hVal' hHead hHead' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'
```

`lockstep_client_safety`'s docstring, verbatim: "**Lockstep safety** (mode 3,
paper Theorem 5). Under the schedule-free lockstep validator and the lockstep
package alone: the same anchor-free agreement, at a freely-timed rotation cadence.
The client holds even less than mode 2's — genesis and a clock, with no schedule
constant to pin." Note `Molt` uses `honestSigned : SigningLog` where the core uses
`Nat → Nat → Option Block`. The file ends `end Molt` at 437.

### 3.12 `LOCKSTEP_DESIGN.md` 120–251 — the audit that defines D1′-full

The three obstructions, verbatim:

> 1. **`schedPinned` is a whole-chain `c.all`, while pinning only reaches
>    *matured* windows.** The tip's own aligned window is never matured, and the
>    lockstep validator's monotonicity bounds its generation below only by the
>    *previous* window's — so a lock-valid chain may declare a **stale**
>    generation there and fail `schedPinned (rosterGen ∘ windowOf)`. Fixable by
>    instantiating at the one-window-lagged schedule
>    `rosterGen ∘ (windowOf · − 1)`.
> 2. **That fix is not free, and it kills the factor-2 saving.** The agreement
>    engine's pigeonhole always runs at the sliding window
>    `[tip.slot+1−n, tip.slot+1)` (`Safety.lean:97`, `KeyStealingScheduleHorizon`
>    :191), which straddles exactly the un-pinned tip window. So the census over
>    the consulted window is again the `≥`/cumulative one, **`erasure_freeze`
>    stays non-load-bearing**, and D1's factor-2 wrinkle is *not* removed by the
>    pinning lemma. Recovering the per-generation census requires generalizing
>    `horizon_shared_prefix` to an arbitrary window — which costs confirmation
>    depth `2n` instead of `n`.
> 3. **The EUF-CMA surface is contravariant in the validator**, and the pinning
>    lemma needs it, so a lockstep-scoped surface is circular. The clean fix is to
>    assume `SchedCoreUnforgeable` at a pointwise-smaller schedule (e.g. constant
>    `0`), which is legitimate and follows the existing full-to-core precedent —
>    but it means the lockstep package's crypto field is literally `PackageA`'s,
>    so the lockstep validator's extra rules buy nothing on the crypto surface.

The two-way fork, verbatim:

> * **D1′-thin** — instantiate the scheduled machinery at the lagged schedule.
>   Roughly one module plus corollaries. Delivers free-cadence lockstep as a
>   machine-checked mode with `PackageA`'s assumptions. Does **not** make
>   `erasure_freeze` load-bearing, so the paper's per-generation-census narrative
>   stays design-level, exactly as today.
> * **D1′-full** — additionally generalize `horizon_shared_prefix` to an
>   arbitrary window so the pigeonhole can run inside a pinned region. This is
>   what earns the per-generation census and makes `erasure_freeze` carry weight,
>   at the cost of confirmation depth `2n` rather than `n` for this mode, plus
>   real proof work.

Also verbatim, and load-bearing for the ordering lens:

> The one genuinely new hypothesis either way is B1-as-behaviour: honest
> signatures declare their window's `rosterGen`. That is not a smuggled schedule —
> it is execution-determined and never reaches a verifier — but it *is* an
> assumption about honest coordination, and it should be disclosed in the paper
> alongside A3/A0/B2 rather than buried.

Phasing H1–H5 (verbatim headings): H1 `MoltPetit/Model/KeyStealingLockstep.lean`
(`genOf`, `validSignedChainLock`, window-constancy/monotonicity lemmas, D2-only
fork-pinning lemma); H2 recency-scoped EUF-CMA surface, honest-slot uniqueness,
`lockstep_recent_tip_ancestor_agreement` and `_mem`; **H3 `PackageC` (or
`LockstepPackage`): `rentBound`, `erasure_freeze` now load-bearing, `budget_le`,
and the derived `ByzantineBounded`**; H4 `MoltPetit/Results/`, every headline into
`Results/Axioms.lean`; H5 paper edits (mode 3 body paragraph, Table 2 row,
appendix mode-3 section, the "event- or governance-triggered cadence" sentence,
"**B1's no-mixing rule leaves the unmodeled list** in both Honest-scope
paragraphs", and re-auditing the abstract's "of which the scheduled two are
proved safe").

Closing line, verbatim: "`PackageA`/`PackageB` stay exactly as they are:
position-forced advancement remains mode 2's device and a legitimate mode-3
deployment choice. The new package is an *alternative* mode-3 realization, not a
replacement."

### 3.13 Cross-work-item state (`ls -la` at line 41)

`/etheron-pod/rollout-work/designs-partial/` contents and sizes at
2026-09-05 09:43:

| File | lines | mtime | owner |
|---|---|---|---|
| W1.md | 105 | Sep 5 07:03 | cage-exec |
| W2.md | 78 | Sep 5 07:05 | cage-agent |
| W3a-run2.md | 267 | Sep 5 09:32 | cage-exec |
| W3a.md | 114 | Sep 5 07:03 | cage-exec |
| W4-run2.md | 660 | Sep 5 09:31 | cage-agent |
| W4.md | 131 | Sep 5 07:06 | cage-exec |
| W5.md | 78 | Sep 5 07:04 | cage-exec |
| W6-run2.md | 475 | Sep 5 09:35 | cage-exec |
| W7-run2.md | 202 | Sep 5 09:30 | cage-exec |

There is **no `W5-run2.md`** (nor `W1-run2.md`, `W2-run2.md`) in that directory —
the run-2 W5 design existed only in this verifier's prompt.

`/etheron-pod/rollout-work/maps/` (all Sep 5 07:04–07:12): `core-grounded-cert1`,
`design-docs`, `mode1-chain`, `mode2-cert-budget`, `mode2-horizon-timed`,
`mode3-lockstep`, `results-molt`, `timed-core-liveness` — each as `.json` +
`.md` (16 files; `mode3-lockstep.json` 78334 B, `mode3-lockstep.md` 45729 B).

### 3.14 What the sibling-design grep returned (depends_on / enables evidence)

Selected hits, verbatim from the tool result at line 48 (truncated by the
verifier's own `cut -c1-260`):

- `W6-run2.md:404` — "MODE 3 COMPOSITION POINTS: `KeyStealingLockstep.lean`
  imports ScheduleBudget + Results.KeyStealingScheduleResults, NOT the
  horizon/timed files -- a mode-3 timed module can import both Lockstep and
  ScheduleTimed without cycles. `lockstep_validS…"
- `W6-run2.md:416` — "`LockstepPackage.mono` and `hashInj` are NOT consumed by
  the pinning theorem or the transport; `mono` is consumed by nothing in the
  module. Private helpers `lockstep_rel` (172), `lockstep_const` (195),
  `head_slot_min` (211), `window_producer_i…"
- `W6-run2.md:398` — "`KeyStealingScheduleHorizon.lean`: `ByzantineBoundedFrom`
  (70), `byzantineBoundedFrom_of_bounded` (75), `horizon_shared_prefix` (161;
  validator-agnostic; budget at the single window `u = tip.slot + 1 - n` of the
  LOWER-tipped chain), `sched_rec…"
- `W6-run2.md:400` — "`KeyStealingHorizonCore.lean`: `sigma_shared_prefix` (91),
  `confirmed_mem_iff_horizon` (151; n ≤ Δconf, no genesis),
  `honestSlotsUnique_keyrot_horizon` (183), `honestSlotsUnique_keyrot_anchored`
  (258; budget shape `∀ u, A.slot + 1 ≤ u + …`"
- `W6-run2.md:474` — "Mode 1 has no `theft_is_recent` analogue because `inForce`
  is chain-local with no real-time relation (digest); **mode 3's theft floor is
  `lagSched`, needing a provisioning hypothesis against `rosterGen` windows.**"
- `W3a-run2.md:164` — "mode2-horizon-timed.md gotchas (numbered): (1)
  `exists_honest_shared_slot_at` and `slot_gap_of_position_gap` are PRIVATE (copy
  or route through `horizon_shared_prefix`); (2) tip-order case split: the sched
  proofs rebuild hId/hUniq with argu…"
- `W3a-run2.md:193` — "Line 247 GOTCHAS (design-docs): (2) 'Mode-1 budget is read
  off a SPECIFIC chain: `badKeyrotOn … (stripSigs sc)` — the first chain `sc` —
  whereas `badSched` takes no chain; **do not introduce a chain into a
  scheduled/lockstep budget** or the…"
- `W3a-run2.md:160` — "mode2-horizon-timed.md, 'WHAT DOES / DOES NOT TRANSPORT TO
  MODE 1' (the crux): 'ByzantineBoundedFrom does NOT transport to mode 1 because
  badKeyrotOn is chain-relative (keyed to stripSigs sc — always the FIRST chain,
  and honestSlotsUnique…"
- `W4-run2.md:409` — "### 2.7 `MoltPetit/Model/KeyStealingScheduleHorizon.lean`
  140–200 [src] — `horizon_shared_prefix`" (W4 also builds on it), and
  `W4-run2.md:413` reproduces its signature.
- `W7-run2.md:116` — "`Molt/Axioms.lean` (lines 1–140 seen): imports
  `Molt.Results`, `Molt.Rotation`, `Molt.ClientRule`, `Molt.MaxSync`,
  `Molt.Liveness`; no namespace; doc: 'Same discipline as
  `MoltPetit/Results/Axioms.lean` …'"
- `W6-run2.md:293-314` reproduce `validSignedChainLock` (L103-106), `lagSched`
  (L112-113), the whole `LockstepPackage` structure, `LockstepPackage.toPackageA`
  (L269-283) and `lockstep_declares_rosterGen` (L299-300) verbatim — i.e. W6's
  designer had already recorded the same mode-3 signatures.
- W1.md and W2.md produced **no hits** for any of the 23 grep patterns.

### 3.15 The two first-run salvages it read in full

- `W1.md` — "W1 salvage — mode 3 (lockstep) at certificate level"; agent
  `a8b6d9f655e212aa8`; "**Status: near-empty salvage.** The subagent was killed
  by the usage limit after its first tool call." Repo state recorded there: HEAD
  `8b8b766` "paper2 p16: appendix -- recency window, no-back-dating scope (AN/33,
  AN/34)", clean tree; sizes `KeyStealingLockstep.lean` 614,
  `KeyStealingScheduleCert.lean` 702, `KeyStealingScheduleBudget.lean` 473,
  `Grounded.lean` 622, `KeyStealingCert.lean` 685.
- `W5.md` — "Salvage: designer transcript for W5 (mode 3 per-generation census /
  erasure credit)"; agent `ab9cd6418be45fd3c`; also near-empty. Contains the
  salvager-established pointers: `LOCKSTEP_DESIGN.md` is 251 lines, titled
  "Free-cadence lockstep rotation: design note (H0)"; its status line 3–9 reads
  "**Status: D1′-thin IMPLEMENTED** — Lean `8593455`
  (`Model/KeyStealingLockstep.lean`: `validSignedChainLock`, the pinning theorem
  `lockstep_declares_rosterGen`, transport `LockstepPackage.toPackageA`, headline
  corollaries, 4 axiom guards), paper `55b9709`. **D1′-full (the per-generation
  census) remains open** — see the audit section below for what it takes."; and
  the fact that **no `.md` file anywhere in `mini-consensus-lean` mentions `W5`,
  `W3a` or `W3b`** — the work-item labels live only in the orchestrator's plan.

---

## 4. Claims refuted or doubted

**None stated.** The verifier issued no refutation, no doubt, and no severity.

The only negative results it obtained are the two empty greps:

| Line | Command | Result |
|---|---|---|
| 51 | `grep -n "new_files\|\"path\"\|touches_existing\|\"name\"" W6-run2.md` | `(Bash completed with no output)` |
| 53 | `grep -n "\"path\"\|\"name\"\|\"key\"" W4-run2.md W3a-run2.md W7-run2.md` | `(Bash completed with no output)` |

i.e. the sibling run-2 design files contain no JSON-shaped `new_files` /
`"path"` / `"name"` / `touches_existing` keys, so a machine-readable
file-collision check across work items was not available from them. The verifier
was killed immediately after the second of these, with no follow-up.

---

## 5. Structured output / drafted JSON

**None.** No `StructuredOutput` call was attempted and no JSON appears anywhere in
the verifier's assistant text. `partial_output` is empty.

---

## 6. Where it stopped

- **Last tool result** (line 54): `(Bash completed with no output)` — the grep of
  `W4-run2.md W3a-run2.md W7-run2.md` for `"path"` / `"name"` / `"key"`.
- **Last assistant sentence**: line 5, "I'll start by inspecting the repository
  layout and the files the design leans on." (There is no later prose; every
  subsequent assistant block is an empty thinking block plus a `tool_use`.)
- **Rate-limit record**: transcript **line 55** — synthetic assistant message
  `"You've hit your session limit · resets 2pm (UTC)"`, `stop_reason:
  "stop_sequence"`, `error: "rate_limit"`, `isApiErrorMessage: true`,
  `apiErrorStatus: 429`, `rateLimitType: "five_hour"`, `overageStatus:
  "rejected"`, `overageDisabledReason: "org_level_disabled"`,
  `resetsAt: 1788616800`, `requestId: req_011Cek5RSGEEE59jcLtiDhTU`, timestamp
  `2026-09-05T09:44:29.944Z`. Line 56 is empty; the file ends there.

Sequencing note: the sweep was emitted as two large multi-tool turns, not as a
step-by-step loop. Tool calls 7–16 (transcript lines 24–42) all belong to one
assistant message, `msg_011Cek5HeeeLQb6p9iXSkNa3` / `req_011Cek5Hc7baXtj2fUwvHQRL`,
`apiBlockIndex` 1–10; tool calls 17–21 (lines 45–53) all belong to the next,
`msg_011Cek5LrnEKU2Xy7DNv4Wgh` / `req_011Cek5Lo4jkhhbzTEaDx94q`, `apiBlockIndex`
1–5. The 429 landed on the request that would have followed the second batch, so
no synthesis turn ever ran: the verifier had finished its evidence-gathering
sweep and had produced no analysis of it whatsoever.
