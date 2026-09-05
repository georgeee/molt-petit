# Salvage: adversarial-verifier transcript for W5 — lens "accuracy" (PARTIAL)

> **WARNING — PARTIAL VERIFICATION. The verifier never returned a verdict.**
> It was killed by a usage limit (HTTP 429) mid-run, after evidence gathering
> and before writing a single word of assessment. Nothing below is a pass or a
> fail; everything below is *evidence it had on record* at the moment it died.
> Its only assistant prose in the whole transcript is one sentence (offset 5).

| | |
|---|---|
| Agent id | `a5601039f915c0f63` |
| Workflow run | `wf_6b051052-ec7` |
| Transcript | `/run/claude/agent/projects/-etheron-pod/c28ff38c-0cb1-500d-8726-22cd73943085/subagents/workflows/wf_6b051052-ec7/agent-a5601039f915c0f63.jsonl` |
| Expected label (indexer-inferred) | **W5-accuracy** |
| Confirmed label (from transcript content) | **W5-accuracy** — CONFIRMED, high confidence. See §0. |
| Transcript size | 47 lines (line 47 is the empty trailing line) |
| Lines seen | 4–38, 40–46 (42 lines) |
| Lines skipped | **39** — a single assistant record of 27,934 tokens, over the Read cap at `limit=1`. From the surrounding records it is the thinking block (`apiBlockIndex 0`) of request `req_011Cek5LphiHDTizSmephPdV`, whose `apiBlockIndex 1` and `2` (the tool calls) are lines 40 and 42; the model thought for ~2 minutes there (09:43:26 → 09:45:33). All thinking in this transcript is signature-only, so no prose was lost. |
| Lines deliberately not read | 1–3 (prompt + harness attachments), per salvage protocol |
| Wall clock | 2026-09-05 09:42:08Z → 09:45:40Z (3 min 32 s) |
| Where it stopped | line 46: synthetic assistant message `"You've hit your session limit · resets 2pm (UTC)"`, `apiErrorStatus: 429`, `rateLimitType: "five_hour"`, `requestId req_011Cek5WeXZRmccfx3NcLBRH` |
| Tool calls made | 12 Bash calls, 0 Read/Grep/Write, 0 StructuredOutput |
| Structured output produced | **none** — no `StructuredOutput` call, no drafted JSON anywhere in assistant text |

---

## 0. Work-item and lens confirmation

**Work item = W5** (mode 3 per-generation census / erasure credit). Evidence, in
descending strength:

1. **The last thing it did** (line 43, tool result line 45) was
   `head -60 /etheron-pod/rollout-work/designs-partial/W5.md`, whose first line
   is `# Salvage: designer transcript for W5 (mode 3 per-generation census / erasure credit)`.
   The verifier was reading the W5 design lineage directly.
2. Its reading targets are exactly the W5 vocabulary: `ErasureTimed`,
   `NoPrematureTheft`, `stolenOf`, `PackageB.erasure_freeze`,
   `erasure_freeze_of_exposedBound`, `recentTheftProducers`,
   `horizon_budget_of_timed`, and the full text of `horizon_shared_prefix`
   (the lemma D1′-full must generalise).
3. It read `LOCKSTEP_DESIGN.md` lines 1–12 and 120–251 — i.e. the audit section
   and the **D1′-thin vs D1′-full** fork, where line 7 reads
   "**D1′-full (the per-generation census) remains open**" and lines 214–218
   define D1′-full as "additionally generalize `horizon_shared_prefix` to an
   arbitrary window so the pigeonhole can run inside a pinned region … earns the
   per-generation census and makes `erasure_freeze` carry weight, at the cost of
   confirmation depth `2n` rather than `n`".
4. It read `docs/rollout/ROLLOUT_NOTES.md`, whose §1 table contains the row
   `| W5 | AN/9b | §2 mode 3 paragraph 'erasure's per-generation credit against the budget is designed but not yet formalized'; §6.3 "Honest scope" second bound; mode 3 operator duties '(its budget credit: honest scope below)'; modes table erasure column | state the per-generation budget and cite it |`.
5. It grepped `ROTATION_MODES.md`, surfacing
   `| X-2 | Per-generation census as the budget (D1′-full): pigeonhole moved inside the pinned region so erasure carries the count. | 3 |`.

**Lens = accuracy** (every reused Lean name exists with the assumed hypotheses
and is usable as the sketch uses it; no new theorem duplicates an existing one).
Evidence:

1. Its only prose, offset 5, verbatim:
   > "I'll start by locating the key declarations the design relies on."
2. Its second command is a single repo-wide `grep -rnE` over `--include=*.lean`
   for a **75-name alternation** anchored at
   `^(private |noncomputable |protected )*(theorem|lemma|def|structure|abbrev|opaque) +<NAME>\b`
   — an existence-plus-form-plus-privacy sweep of every reused name, described
   in its own words as *"Locate all declarations referenced by the design"*.
3. Every subsequent read pulls **full binder lists** of those declarations
   (not proofs-for-review, but hypothesis lists) — the "assumed hypotheses"
   half of the lens.
4. Line 40 contains the duplicate half: a grep for names that look like the
   design's *proposed new* names (`UniqueOn|AlignedBounded|badLockAt|aligned_|length_le_tip|tip_slot_ge|slot_ge_length|chain_length_le|window_shared|shared_prefix`),
   described as *"Verify remaining declarations, names, and file headers"*.

No ordering-lens artefacts (depends_on/enables cross-checks against W1/W2) appear
anywhere in the transcript.

---

## 1. Every file it examined, with ranges and why

All paths relative to `/etheron-pod/mini-consensus-lean` unless absolute.
"Why" is taken from the tool `description` field or the command shape.

| # | Line | File / target | Range | Why (verbatim description where available) |
|---|---|---|---|---|
| 1 | 6 | `MoltPetit/Model/`, `MoltPetit/Results/`, `Molt/` (dir listings) + `wc -l` of `KeyStealingLockstep.lean`, `KeyStealingScheduleHorizon.lean`, `KeyStealingScheduleTimed.lean`, `KeyStealingScheduleBudget.lean` | — | "List model files and line counts" |
| 2 | 9 | repo-wide `grep -rnE` over `--include=*.lean .` for 75 declaration names | whole repo | "Locate all declarations referenced by the design" |
| 3 | 12 | `MoltPetit/Model/KeyStealingHorizonCore.lean` | **1–365 (whole file)** | "Read KeyStealingHorizonCore.lean fully" |
| 4 | 15 | `MoltPetit/Model/KeyStealingScheduleHorizon.lean` | **60–400** | "Read KeyStealingScheduleHorizon.lean lines 60-400" |
| 5 | 18 | `MoltPetit/Model/KeyStealingLockstep.lean` | whole file attempted | "Read KeyStealingLockstep.lean fully" — **output too large (34.8 KB), persisted to `/run/claude/.../tool-results/blff7fup9.txt`; only the first 2 KB preview (lines 1–31, the module docstring) entered context** |
| 6 | 20 | `MoltPetit/Model/KeyStealingScheduleBudget.lean` | **95–215** and **300–400** | "Read KeyStealingScheduleBudget.lean sections" |
| 7 | 22 | `MoltPetit/Model/KeyStealingScheduleTimed.lean` | **80–200** and **280–423** | "Read KeyStealingScheduleTimed.lean sections" |
| 8 | 24 | `MoltPetit/Model/Definitions.lean` | **40–55, 76–100, 221–236, 456–530, 640–662** | "Read Definitions.lean sections" |
| 9 | 26 | `MoltPetit/Model/Model.lean` **30–80**; `MoltPetit/Model/Safety.lean` **20–60** and **180–215**; `MoltPetit/Model/Soundness.lean` **95–105** | as listed | "Read Model, Safety, Soundness sections" |
| 10 | 28 | `MoltPetit/Model/KeyStealingUnique.lean` **40–85**; `MoltPetit/Model/KeyStealingScheduleCert.lean` **195–262**; `MoltPetit/Model/KeyStealingSchedule.lean` **85–100**; `MoltPetit/Model/KeyIndex.lean` **210–225**; `MoltPetit/Model/KeyStealingCert.lean` **230–250** | as listed | "Read Unique, ScheduleCert, Schedule, KeyIndex, Cert sections" |
| 11 | 30 | `MoltPetit/Results/Axioms.lean` **470–520**; `Molt/Rotation.lean` **150–230** and **395–425**; `MoltPetit.lean` (whole, 35 lines); `Molt.lean` (whole, 26 lines); `lakefile.toml` (whole) | as listed | "Read Axioms, Rotation, root modules, lakefile" |
| 12 | 32 | `docs/rollout/ROLLOUT_NOTES.md` **1–71 (whole)**; `LOCKSTEP_DESIGN.md` **120–251**; `ls /etheron-pod/rollout-work/maps/` | as listed | "Read ROLLOUT_NOTES, LOCKSTEP_DESIGN, list maps" |
| 13 | 35 | `MoltPetit/Model/KeyStealingLockstep.lean` | **60–300** | "Read KeyStealingLockstep.lean 60-300" (re-read after the persisted-output truncation) |
| 14 | 37 | `MoltPetit/Model/KeyStealingLockstep.lean` | **300–614** | "Read KeyStealingLockstep.lean 300-614" |
| 15 | 40 | `MoltPetit/Model/KeyStealingBudget.lean` **45–62**; `grep def badSched -A3` in `KeyStealingSchedule.lean`; `grep SigningLog Molt/*.lean`; `grep theorem quorum_overlap MoltPetit/`; the "existing names" duplicate grep; `MoltPetit/Results/Axioms.lean` **1–30**; `grep lockstep Molt/Axioms.lean`; `head -3` of `KeyStealingScheduleHorizon/ScheduleTimed/Unique/Safety.lean`; `ls /etheron-pod/toolchains/lake.sh` | as listed | "Verify remaining declarations, names, and file headers" |
| 16 | 42 | `paper/molt.tex` (11-alternative phrase grep); `LOCKSTEP_DESIGN.md` **1–12**; `ROTATION_MODES.md` **195–230**; `KEY_ROTATION_SOUND.md` **750–765** | as listed | "Verify paper and doc anchors referenced by the design" |
| 17 | 43 | `/etheron-pod/rollout-work/maps/mode3-lockstep.md` (`grep -iE "gotcha\|private\|reuse"`); `/etheron-pod/rollout-work/designs-partial/W5.md` **1–60** | as listed | "Read map gotchas and partial design notes" — **last tool call; its result (line 45) is the last thing the verifier ever saw** |

Files it *listed* but never opened: `Molt/{Assumptions,Axioms,ClientRule,Liveness,MaxSync,Protocol,Results,Verifier}.lean` (except the greps above), `MoltPetit/Model/{Grounded,KeyRotation,KeyRotationLiveness,KeyRotationTests,KeyStealing,KeyStealingHorizon,KeyStealingLongRange,KeyStealingSafety,Liveness,Timed,TimedSig}.lean`, `MoltPetit/Results/{KeyStealingResults,KeyStealingScheduleResults,Results}.lean`.

---

## 2. Facts established (the expensive part) — evidence on record

**Read this section as "what the verifier proved to itself about the repo",
not as "what the verifier approved".** It never wrote an approval. Everything
here is a verbatim/near-verbatim reproduction of what its tool results printed.

### 2.1 Existence sweep — all 75 reused names, located

From line 9's grep (output at line 10). Every name below **exists** at the given
`file:line` with the given form. `private` marks a declaration that **cannot be
imported**.

**Model core — `MoltPetit/Model/Definitions.lean`**

| Name | Line | Form |
|---|---|---|
| `quorum` | 44 | `def quorum (n : Nat) : Nat := (2 * n + 2) / 3` |
| `maxByzantine` | 47 | `def maxByzantine (n : Nat) : Nat := (n - 1) / 3` |
| `producerForSlot` | 50 | `def producerForSlot (n slot : Nat) : Nat := slot % n` |
| `blockInWindow` | 78 | `def blockInWindow (u len : Nat) (b : Block) : Bool := decide (u ≤ b.slot ∧ b.slot < u + len)` |
| `windowCount` | 82 | `def windowCount (c : Chain) (u len : Nat) : Nat := (c.filter (blockInWindow u len)).length` |
| `windowDense` | 86 | `def windowDense (n : Nat) (c : Chain) (u : Nat) : Bool := decide (quorum n ≤ windowCount c u n)` |
| `maturedWindowsDense` | 95 | `(List.range (t + 2 - n)).all fun u => windowDense n c u` |
| `stripSigs` | 221 | `def stripSigs {σ} (sc : SignedChain σ) : Chain := sc.map SignedBlock.block` |
| `sigOk` | 226 | `ops.verify (registry (producerForSlot n sb.block.slot) sb.block.keyIndex) sb.block sb.sig` |
| `sigsOk` | 231 | `sc.all (sigOk n ops registry)` |
| `SlotRecord` | 456 | `abbrev SlotRecord := Nat → Finset Block` |
| `ByzantineSlots` | 459 | `abbrev ByzantineSlots := Nat → Prop` |
| `blockAt?` | 462 | `def blockAt? (c : Chain) (h : Nat) : Option Block := getElem? c h` |
| `SequentialHeights` | 465 | `∀ ⦃h⦄ ⦃B⦄, blockAt? c h = some B → B.height = h` |
| `StrictSlots` | 469 | `c.Pairwise fun a b => a.slot < b.slot` |
| `ParentLinked` | 473 | genesis `prev = none`; `k+1` points at predecessor's `id` |
| `MaturedWindowsDense` | 484 | `∀ ⦃m⦄ ⦃D⦄, blockAt? c m = some D → ∀ u, u + n ≤ D.slot + 1 → quorum n ≤ windowCount c u n` |
| `ValidChain` | 490 | `SequentialHeights c ∧ StrictSlots c ∧ ParentLinked c ∧ MaturedWindowsDense n c` |
| `ChainInRecord` | 494 | `∀ ⦃k⦄ ⦃B⦄, blockAt? c k = some B → B ∈ record B.slot` |
| `HonestSlotsUnique` | 498 | `∀ s, ¬ bad s → ∀ ⦃B B'⦄, B ∈ record s → B' ∈ record s → B = B'` |
| `IdInjective` | 503 | `∀ s t, ∀ ⦃B B'⦄, B ∈ record s → B' ∈ record t → B.id = B'.id → B = B'` |
| `badSlotsIn` | 509 | `noncomputable def … := (Finset.Ico u (u + n)).filter fun s => bad s` |
| `ByzantineBounded` | 513 | `∀ u, (badSlotsIn bad u n).card ≤ maxByzantine n` |
| `CommonPrefixUpTo` | 517 | — |
| `LastCommonHeight` | 521 | — |
| `chainSlotsIn` | 527 | `((c.filter (blockInWindow u len)).map Block.slot).toFinset` |
| `SignedHashInjective` | 656 | `∀ ⦃B B'⦄, (B = G ∨ Signed B) → (B' = G ∨ Signed B') → B.id = B'.id → B = B'` |

**Model lemmas**

| Name | file:line | Statement / note |
|---|---|---|
| `mem_chainSlotsIn` | `Model.lean:35` | `s ∈ chainSlotsIn c u len ↔ ∃ B, B ∈ c ∧ (u ≤ B.slot ∧ B.slot < u + len) ∧ B.slot = s` |
| `chainSlotsIn_subset_Ico` | `Model.lean:40` | `chainSlotsIn c u len ⊆ Finset.Ico u (u + len)` |
| `strictSlots_lt` | `Model.lean:47` | index form of strict slot monotonicity |
| `chainSlotsIn_card` | `Model.lean:60` | `(hS : StrictSlots c) → (chainSlotsIn c u len).card = windowCount c u len` |
| `exists_blockAt_of_mem` | `Model.lean:71` | `B ∈ c → ∃ k, blockAt? c k = some B` |
| `exists_blockAt_of_le` | `Model.lean:79` | earlier heights exist |
| `quorum_overlap` | `Model.lean:95` | `(hn : 1 ≤ n)` (statement body not printed) |
| `height_gt_of_slot_gt` | `Safety.lean:29` | `(hS : StrictSlots c) (hF : blockAt? c h = some F) (hB : blockAt? c k = some B) (hSlot : F.slot < B.slot) : h < k` |
| `exists_honest_shared_slot` | `Safety.lean:45` | **public**, takes the *global* `(hBudget : ByzantineBounded n bad)` |
| `same_block_same_prefix` | `Safety.lean:189` | `(hId : IdInjective record) (hRec …) (hRec' …) (hP : ParentLinked c) (hP' : ParentLinked c') : ∀ {m B}, blockAt? c m = some B → blockAt? c' m = some B → ∀ {k}, k ≤ m → ∃ P, blockAt? c k = some P ∧ blockAt? c' k = some P` |
| `blockAt_getLast` | `Soundness.lean:97` | `ch.getLast? = some tip → blockAt? ch (ch.length - 1) = some tip` |

**Record / certificate plumbing**

| Name | file:line | Note |
|---|---|---|
| `chainUnionRecord` | `KeyStealingUnique.lean:45` | `fun s => ((stripSigs sc ++ stripSigs sc').filter (fun b => b.slot == s)).toFinset` |
| `mem_chainUnionRecord` | `KeyStealingUnique.lean:48` | `x ∈ … ↔ (x ∈ stripSigs sc ∨ x ∈ stripSigs sc') ∧ x.slot = s` |
| `chainInRecord_left` / `_right` | `KeyStealingUnique.lean:54` / `60` | no hypotheses |
| `idInjective_keyrot` | `KeyStealingUnique.lean:70` | `(hHash : SignedHashInjective Signed G) (hSig : ∀ B ∈ stripSigs sc, B = G ∨ Signed B) (hSig' : …) : IdInjective (chainUnionRecord sc sc')` |
| `SignedDeclared` | `KeyStealingCert.lean:234` | `∃ sig, ops.verify (registry (producerForSlot n B.slot) B.keyIndex) B sig = true` |
| `keyStealingSigned_of_declared` | `KeyStealingCert.lean:239` | `SignedDeclared → KeyStealingSigned` (one direction only) |
| `exists_signedChain_of_covered` | `KeyStealingCert.lean:247` | — |
| `signedDeclared_of_mem_sched` | `KeyStealingSchedule.lean:88` | from `validSignedChainSched … = true` and `B ∈ stripSigs sc` |
| `badSched` | `KeyStealingSchedule.lean:124` | `rented s ∨ ∃ j, schedule s ≤ j ∧ Stolen (producerForSlot n s) j` |
| `SchedCoreUnforgeable` | `KeyStealingScheduleCert.lean:200` | structure; single field `unforgeable`, scoped to `validSignedChainSchedCore` |
| `schedUnforgeable_of_core` | `KeyStealingScheduleCert.lean:216` | core surface ⇒ full surface |
| `honestSlotsUnique_schedCore` | `KeyStealingScheduleCert.lean:231` | `HonestSlotsUnique (badSched …) (chainUnionRecord sc sc')` from the core validator + recency |
| `validChainK_sound` | `KeyIndex.lean:215` | `validChainK n c = true → ValidChain n c ∧ KeyIndexMonotone n c` |
| `pinAt` | `KeyIndex.lean:223` | — |
| `SigningLog` | `Molt/Assumptions.lean:29` | `abbrev SigningLog := MoltPetit.Model.SigningLog` |

**Budget layer**

| Name | file:line | Note |
|---|---|---|
| `badKeyrotOn_iff_or` | `KeyStealingBudget.lean:45` | `badKeyrotOn … s ↔ rented s ∨ theftOn n Δconf Stolen c₀ s` (`Iff.rfl`) |
| `badSlotsIn_union_le` | `KeyStealingBudget.lean:52` | `(badSlotsIn (fun s => A s ∨ B s) u n).card ≤ (badSlotsIn A u n).card + (badSlotsIn B u n).card` |
| `exposedProducers` | `KeyStealingBudget.lean:62` | `noncomputable def … (n Δconf : Nat) (Stolen …)` — the *chain-reading* default form |
| `window_producer_inj` | `KeyStealingBudget.lean:69` | **private** |
| `theftSched` | `KeyStealingScheduleBudget.lean:104` | `∃ j, schedule s ≤ j ∧ Stolen (producerForSlot n s) j` |
| `badSched_iff_or` | `KeyStealingScheduleBudget.lean:108` | `Iff.rfl` |
| `exposedProducersSched` | `KeyStealingScheduleBudget.lean:117` | `(Finset.Ico u (u+n)).filter (theftSched n schedule Stolen) \|>.image (producerForSlot n)` — reads no chain |
| `window_producer_inj` | `KeyStealingScheduleBudget.lean:125` | **private** (local copy of the Budget one) |
| `theftSlotsSched_card_le_exposed` | `KeyStealingScheduleBudget.lean:148` | `(badSlotsIn (theftSched n schedule Stolen) u n).card ≤ (exposedProducersSched n schedule Stolen u).card` |
| `induced_byzantine_bounded_sched` | `KeyStealingScheduleBudget.lean:164` | `(hRent : ∀ u, (badSlotsIn rented u n).card ≤ R) (hExposed : ∀ u, (exposedProducersSched …).card ≤ T) (hRT : R + T ≤ maxByzantine n) : ByzantineBounded n (badSched …)` |
| `PackageA` | `KeyStealingScheduleBudget.lean:204` | fields `unforgeable, hashInj, rentBound, exposedBound, budget_le` |
| `PackageB` | `KeyStealingScheduleBudget.lean:331` | `extends PackageA …` + one field |
| `PackageB.erasure_freeze` | `KeyStealingScheduleBudget.lean:337` | **`∀ j : Nat, ((Finset.range n).filter (fun i => Stolen i j)).card ≤ T`** |
| `schedule_div_full_window` | `KeyStealingScheduleBudget.lean:344` | `(hR : n ≤ R) (hR0 : 0 < R) : ∀ j, ∃ u, ∀ s, u ≤ s → s < u + n → s / R = j` |
| `erasure_freeze_of_exposedBound` | `KeyStealingScheduleBudget.lean:364` | `(hExposed : ∀ u, (exposedProducersSched n schedule Stolen u).card ≤ T) (hFull : ∀ j, ∃ u, ∀ s, u ≤ s → s < u + n → schedule s = j) : ∀ j, ((Finset.range n).filter (fun i => Stolen i j)).card ≤ T` |
| `packageB_byzantine_bounded` | `KeyStealingScheduleBudget.lean:396` | via the Package-A core |

`PackageB`'s docstring (read verbatim, lines 303–330) states: **"`erasure_freeze` is consumed by no proof"**, that for full-window schedules it is *implied* by `exposedBound`, that `PackageB.toPackageA` therefore records an assumption-set inclusion and is "documentary, not a nontrivial reduction", and that "the genuinely-B discharge of §10.2 — no-mixing forces any fork to a single generation, so a per-generation census suffices *without* the cumulative reading — is a different proof shape requiring the unmodeled B1 no-mixing rule (validator scope note)."

**Horizon layer — `MoltPetit/Model/KeyStealingScheduleHorizon.lean`**

| Name | line | Statement |
|---|---|---|
| `ByzantineBoundedFrom` | 70 | `def ByzantineBoundedFrom (H n : Nat) (bad : ByzantineSlots) : Prop := ∀ u, H ≤ u → (badSlotsIn bad u n).card ≤ maxByzantine n` |
| `byzantineBoundedFrom_of_bounded` | 75 | `ByzantineBounded n bad → ByzantineBoundedFrom H n bad`, `fun u _ => h u` |
| `exists_honest_shared_slot_at` | 86 | **private** — single-window pigeonhole; `(hn : 1 ≤ n) (hBudgetU : (badSlotsIn bad u n).card ≤ maxByzantine n) (hS : S ⊆ Finset.Ico u (u+n)) (hS' : …) (hCard : quorum n ≤ S.card) (hCard' : …) : ∃ s, s ∈ S ∧ s ∈ S' ∧ ¬ bad s` |
| `slot_gap_of_position_gap` | 116 | **private** — `(hS : StrictSlots c) : ∀ d p {X Y}, blockAt? c p = some X → blockAt? c (p+d) = some Y → X.slot + d ≤ Y.slot` |
| `horizon_shared_prefix` | 161 | see §2.2 — the lemma D1′-full must generalise |
| `sched_recent_tip_ancestor_agreement_horizon` | 247 | consumes `ByzantineBoundedFrom H n (badSched n schedule rented Stolen)` + `hH : H + n ≤ sTip.slot + 1`, `hH' : H + n ≤ sTip'.slot + 1`; **no `hHead`/`hHead'`** |
| `sched_recent_tip_ancestor_mem_horizon` | 308 | same budget shape, unequal tip heights |
| `sched_recent_genesis_agreement_horizon` | 365 | genesis agreement as a *conclusion*, no anchor hypothesis of any kind |

**Timed layer — `MoltPetit/Model/KeyStealingScheduleTimed.lean`**

| Name | line | Statement |
|---|---|---|
| `stolenOf` | 90 | `def stolenOf (stolenAt : Nat → Nat → Nat → Prop) (i j : Nat) : Prop := ∃ r, stolenAt i j r` |
| `NoPrematureTheft` | 96 | `∀ i j r, stolenAt i j r → j * R ≤ r` |
| `ErasureTimed` | 102 | **`∀ i j r, stolenAt i j r → r < (j + 1) * R`** |
| `theft_during_era_of_erasure` | 107 | `(hA3 : NoPrematureTheft R stolenAt) (hEr : ErasureTimed R stolenAt) (h : stolenAt i j r) : j * R ≤ r ∧ r < (j + 1) * R` — **axiom-free** (`Results/Axioms.lean:512`: "does not depend on any axioms") |
| `theft_is_recent` | 122 | `(hR : 0 < R) (hA3 …) (h : theftSched n (fun t => t / R) (stolenOf stolenAt) s) : ∃ j r, s / R ≤ j ∧ stolenAt (producerForSlot n s) j r ∧ s < r + R` |
| `recentTheftProducers` | 149 | `(Finset.range n).filter (fun i => ∃ j r, u / R ≤ j ∧ stolenAt i j r ∧ u < r + R)` |
| `exposedSched_subset_recentTheft` | 156 | `(hn : 0 < n) (hR : 0 < R) (hA3 …) (u) : exposedProducersSched n (fun s => s / R) (stolenOf stolenAt) u ⊆ recentTheftProducers n R stolenAt u` |
| `horizon_budget_of_timed` | 187 | `(hn : 0 < n) (hR : 0 < R) (hA3) (hRent : ∀ u, H ≤ u → …≤ Rrent) (hTheft : ∀ u, H ≤ u → (recentTheftProducers n R stolenAt u).card ≤ T) (hRT : Rrent + T ≤ maxByzantine n) : ByzantineBoundedFrom H n (badSched n (fun s => s / R) rented (stolenOf stolenAt))` |
| `sched_backdate_consistent` | 284 | a consistency (non-derivation) witness |
| `PackageATimed` | 312 | fields `unforgeable, hashInj, notBefore (NoPrematureTheft), rentBound, recentTheftBound, budget_le` — schedule **pinned to `s / R`** |
| `packageATimed_horizon_budget` | 326 | — |
| `packageATimed_recent_tip_ancestor_agreement` | 344 | end-to-end horizon light-client safety from `PackageATimed` alone |
| `PackageBTimed` | 383 | `extends PackageATimed …` + `notAfter : ErasureTimed R stolenAt` |
| `packageBTimed_recent_tip_ancestor_agreement` | 394 | delegates through `hPB.toPackageATimed` — **`notAfter` unused** |

**Lockstep (mode 3) — `MoltPetit/Model/KeyStealingLockstep.lean`**

| Name | line | Note |
|---|---|---|
| `lockstepOk` | 76 | declared generation constant within each `n`-window, non-decreasing across |
| `lockstepOk_iff_pairwise` | 84 | **public** — `lockstepOk n c = true ↔ c.Pairwise (fun a b => (a.slot / n = b.slot / n → a.keyIndex = b.keyIndex) ∧ a.keyIndex ≤ b.keyIndex)` |
| `validSignedChainLock` | 103 | `sigsOk … && validChainK n (stripSigs sc) && lockstepOk n (stripSigs sc)` |
| `lagSched` | 112 | `def lagSched (n : Nat) (rosterGen : Nat → Nat) (s : Nat) : Nat := rosterGen (s / n - 1)` |
| `schedPinned_mono` | 120 | pin antitone in the schedule |
| `schedCore_mono` | 130 | core validity antitone in the schedule |
| `schedCoreUnforgeable_mono` | 141 | surface **monotone** in the schedule |
| `schedCore0_of_lock` | 154 | lock-valid ⇒ `validSignedChainSchedCore n (fun _ => 0) …= true` |
| `lockstep_rel` | 172 | **private** |
| `lockstep_const` | 195 | **private** |
| `head_slot_min` | 211 | **private** |
| `window_producer_inj'` | 220 | **private** (`Nat.ModEq` form) |
| `LockstepPackage` | 252 | fields `mono, unforgeable (at const-0), declared, hashInj, genesis_gen, rentBound, exposedBound (at lagSched n rosterGen), budget_le` |
| `LockstepPackage.toPackageA` | 269 | `PackageA n (lagSched n rosterGen) …` |
| `lockstep_declares_rosterGen` | 299 | the pinning theorem — see §2.3 |
| `lockstep_validSignedChainSched` | 474 | lock-valid + `hHead` + recency ⇒ `validSignedChainSched n (lagSched n rosterGen) … = true` |
| `lockstep_recent_tip_ancestor_agreement` | 555 | headline, via `packageA_recent_tip_ancestor_agreement` |
| `lockstep_recent_tip_ancestor_mem` | 586 | via `sched_recent_tip_ancestor_mem` |

**`MoltPetit/Model/KeyStealingHorizonCore.lean` (read whole, 365 lines)** — the
mode-1 σ-localized route, already in the tree: `exists_honest_shared_slot_at`
(58, **private**, a *verbatim duplicate* of the ScheduleHorizon one at 86),
`sigma_shared_prefix` (91), `confirmed_mem_iff_horizon` (151),
`honestSlotsUnique_keyrot_horizon` (183), `honestSlotsUnique_keyrot_anchored` (258).

**`Molt/` paper-aligned layer** — `SlotRecord` (Assumptions:19), `ByzantineSlots` (22),
`ValidChain` (25), `SigningLog` (29), `badSlotsIn` (33), `SignedHashInjective` (50),
`HonestSlotsUnique` (70), `IdInjective` (75), `quorum` (Protocol:23),
`windowCount` (Protocol:78), `SignedDeclared` (Rotation:137, abbrev),
`validSignedChainLock` (Rotation:155), `LockstepPackage` (Rotation:164, abbrev),
`validSignedChainLock_eq_core` (Rotation:217), `lockstep_client_safety` (Rotation:406),
`stripSigs`/`sigOk`/`sigsOk` (Verifier:35/40/46). The `Molt` layer is bridged to
the core by `rfl`-lemmas (`keyMonoOk_eq_core`, `noMixing_eq_core = lockstepOk`,
`badKeyrot_eq_core = badKeyrotOn`, …, Rotation:168–222).

### 2.2 `horizon_shared_prefix` — the exact signature D1′-full must generalise

`MoltPetit/Model/KeyStealingScheduleHorizon.lean:161` (read verbatim):

```lean
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

Proof shape it read (lines 175–223 of the file): `set u := tip.slot + 1 - n`;
`hgap : B.slot + n ≤ tip.slot` via `slot_gap_of_position_gap`; density in **both**
chains at `u` via `hDense hTipAt u` / `hDense' hTipAt' u`;
`exists_honest_shared_slot_at hn hBudgetU chainSlotsIn_subset_Ico chainSlotsIn_subset_Ico hq hq'`;
`hBeq := hHonest s hsHonest hB₁rec hB₂rec`; `hk_lt := height_gt_of_slot_gt`;
close with `same_block_same_prefix hId hRec hRec' hPL hPL' hk₁ hk₂' (Nat.le_of_lt hk_lt)`.
It is consumed at **12 call sites** across `KeyStealingHorizon.lean` (108, 114, 203,
210, 289, 297) and `KeyStealingScheduleHorizon.lean` (288, 297, 346, 354, 398, 404,
454, 463, 509, 517) — i.e. any *edit* to it is a many-caller change; an additive
aligned-window sibling is not.

### 2.3 `lockstep_declares_rosterGen` — pinning, and its census

`MoltPetit/Model/KeyStealingLockstep.lean:299`:

```lean
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

The census inside (lines 384–463), read verbatim — **this is the per-generation
counting template W5 needs**:

* `hSsub : chainSlotsIn (stripSigs sc) (W*n) n ⊆ badSlotsIn rented (W*n) n ∪ (Finset.Ico (W*n) (W*n+n)).filter (fun s => theftSched n (lagSched n rosterGen) Stolen s)`
* every theft slot in the aligned window is at the **single** generation
  `g = B.keyIndex` (by `lockstep_const`), with witness `j := g` and side
  condition `rosterGen (W-1) ≤ g` (`hlow`, from the previous window's pin plus
  `lockstep_rel … .2`)
* `hTb : (…filter…).card ≤ T` via `Finset.card_image_of_injOn hinj` with
  `hinj` from the **private** `window_producer_inj'`, then `hP.exposedBound (W*n)`
* `hcount : quorum n ≤ (badSlotsIn rented (W*n) n).card + (…).card`, via
  `hWdense`, `chainSlotsIn_card`, `Finset.card_union_le`
* `hmb : maxByzantine n < quorum n := by unfold maxByzantine quorum; omega`
* closes with `hP.budget_le` and `omega`.

### 2.4 Additive-only rule and file layout (context it loaded)

`docs/rollout/ROLLOUT_NOTES.md` (whole file, 71 lines) — ground rules from George, verbatim:

> **New Lean only.** New modules, new definitions, new theorems. Nothing existing is
> modified. The only touches permitted to existing files are (a) one import line per
> new module in a root module (`MoltPetit.lean`, `Molt.lean`) and (b) new axiom-guard
> files rather than edits to an existing `Axioms.lean`. Every touch is logged in §2.
> … Axiom hygiene …: every new headline theorem gets a `#guard_msgs` guard;
> `#print axioms` must yield exactly `[propext, Classical.choice, Quot.sound]`.

Build command: `/etheron-pod/toolchains/lake.sh build MoltPetit.Model.<NewModule>`
then `… build MoltPetit Molt` (verified present: `ls` returned the path).
§2 ("Existing Lean touched") and §3 ("New Lean added") tables are **both still
empty** (`| — | — | — |`).

`MoltPetit.lean` import order (35 lines) ends `… KeyStealingScheduleBudget,
KeyStealingScheduleHorizon, KeyStealingLockstep, KeyStealingHorizonCore,
KeyStealingHorizon, KeyStealingScheduleTimed, KeyRotationTests, Results.Axioms,
Custody`. `Molt.lean` has 9 imports. `lakefile.toml`: libs `MoltPetit`, `Rust`,
`Thales`, `Molt`; mathlib `v4.30.0-rc2`; `relaxedAutoImplicit = false`.
Module import headers: `KeyStealingScheduleHorizon` ← `KeyStealingScheduleCert`;
`KeyStealingScheduleTimed` ← `KeyStealingScheduleHorizon` + `KeyStealingScheduleBudget`;
`KeyStealingUnique` ← `KeyStealing` + `KeyStealingSafety`; `KeyStealingSafety` ← `KeyRotation`.
Existing guards: `Results/Axioms.lean:470–520` (incl. `horizon_shared_prefix`,
`horizon_budget_of_timed`, `theft_during_era_of_erasure`, `packageBTimed_*`),
`:543` (`sigma_shared_prefix`); `Molt/Axioms.lean:67–69, 128–130, 141–144`
(`lockstep_declares_rosterGen`, `lockstep_recent_tip_ancestor_mem`,
`lockstep_client_safety`).

### 2.5 Design-note and paper anchors it verified exist

* `LOCKSTEP_DESIGN.md:1–12` — "**Status: D1′-thin IMPLEMENTED** — Lean `8593455` …
  paper `55b9709`. **D1′-full (the per-generation census) remains open**".
* `LOCKSTEP_DESIGN.md:135–178` — the 2026-08-01 audit, three obstructions,
  verbatim key sentence: "Recovering the per-generation census requires
  generalizing `horizon_shared_prefix` to an arbitrary window — which costs
  confirmation depth `2n` instead of `n`." Obstruction 2 cites
  `Safety.lean:97` and `KeyStealingScheduleHorizon:191` as the sliding window.
* `LOCKSTEP_DESIGN.md:209–218` — D1′-thin vs D1′-full definitions;
  `:226–251` — phasing H1–H5, and "`PackageA`/`PackageB` stay exactly as they are".
* `ROTATION_MODES.md:195–230` — honest-scope bullet ("the sharper per-generation
  census, where erasure itself carries the count (B2 load-bearing), is 📐
  design-level (**D1′-full**…)"), the modes table, and the not-yet-modeled table
  rows X-1…X-4 (X-2 = D1′-full, X-4 = lockstep certificate wrapper).
* `KEY_ROTATION_SOUND.md:750–765` — the packages summary, "Honest weight: the
  field is consumed by no proof".
* `paper/molt.tex` phrase hits at lines **215, 981, 1071, 1092, 1098, 1105,
  1111, 1136, 1137, 1159, 1178, 1400, 1418** (see §3 for the alternatives that
  produced no line).
* `/etheron-pod/rollout-work/maps/` exists with 8 map pairs (`core-grounded-cert1`,
  `design-docs`, `mode1-chain`, `mode2-cert-budget`, `mode2-horizon-timed`,
  `mode3-lockstep`, `results-molt`, `timed-core-liveness`), `.json` + `.md` each.

### 2.6 The map's GOTCHAS (loaded into its context at the very end, line 45)

From `/etheron-pod/rollout-work/maps/mode3-lockstep.md` — 11 numbered notes.
Reproduced because they were the last thing the verifier read and are directly
about the W5 accuracy question. Condensed to the load-bearing clauses:

1. `lockstep_declares_rosterGen`, `lockstep_validSignedChainSched` and both
   corollaries **all need `hHead : blockAt? (stripSigs sc) 0 = some G`** and
   validity/recency of the **whole chain**; none can be applied to a suffix.
2. The pinning theorem consumes `exposedBound`/`rentBound` at `u := W * n`
   (aligned starts) at `lagSched n rosterGen`; **"an `erasure_freeze`-shaped
   bound `((Finset.range n).filter (fun i => Stolen i g)).card ≤ T` would close
   the same counting"** — "the obstruction is only in the agreement engine's
   sliding window, not in pinning".
3. `LockstepPackage.mono` and `hashInj` are **not** consumed by the pinning
   theorem or the transport; `mono` is consumed by nothing in the module.
4. `erasure_freeze_of_exposedBound` needs a full-window premise;
   **`lagSched n rosterGen` is not full-window in general**, so a
   `LockstepPackage` does not yield `erasure_freeze`.
5. `hashInj` in `PackageA`/`LockstepPackage` is at `SignedDeclared`; the
   `KeyStealingHorizon.lean` theorems use `SignedHashInjective (KeyStealingSigned …) G`.
   `SignedDeclared → KeyStealingSigned` only; **not conversely**.
6. The surface is assumed at the constant-0 schedule and is monotone
   (`schedCoreUnforgeable_mono`); a lockstep-scoped surface is circular.
7. `lockstep_rel`, `lockstep_const`, `head_slot_min`, `window_producer_inj'`
   (and ScheduleBudget's `window_producer_inj`) are `private` — **not importable**;
   re-prove (~20 lines each) from public `lockstepOk_iff_pairwise` +
   `List.pairwise_iff_getElem` + `exists_blockAt_of_mem` + `strictSlots_lt`.
8. `lagSched` at window 0 is `rosterGen 0`; the matured-window witness form is
   `∃ D ∈ stripSigs sc, W * n + n ≤ D.slot + 1` for the **aligned** window, while
   `MaturedWindowsDense` quantifies over every `u`. **The tip's aligned window is
   never pinned** — only `rosterGen (W−1) ≤ keyIndex` holds there.
9. `maxByzantine n < quorum n` is discharged inline; the design's
   `quorum > 2·maxByzantine` **has no named lemma** in the files read.
10. `hLong : n < length` is what makes window 0 matured.
11. The scheduled engine's pigeonhole runs at `u := tip.slot + 1 − n`;
    **"D1′-full means an aligned-window variant of this lemma with a
    per-generation census there (confirmation depth 2n)."**

---

## 3. Refutations / doubts

**The verifier stated none.** It never wrote an assessment sentence. What
follows are the *mechanically negative results visible in its tool output* —
salvager's factual read of what the greps returned, not the verifier's stated
findings. Severity: none stated, because no verdict was ever rendered.

| # | Searched for (by the verifier) | What the output actually showed |
|---|---|---|
| 1 | `theftSlotsSched` as a declaration (in the 75-name sweep, line 9) | **No hit.** Only `theftSlotsSched_card_le_exposed` (`KeyStealingScheduleBudget.lean:148`) exists; there is no standalone `theftSlotsSched` def — the theft-slot set is spelled `badSlotsIn (theftSched n schedule Stolen) u n`. |
| 2 | `UniqueOn`, `AlignedBounded`, `badLockAt`, `aligned_*`, `length_le_tip`, `tip_slot_ge`, `slot_ge_length`, `chain_length_le`, `window_shared`, `shared_prefix` (line 40, case-insensitive, over `MoltPetit` + `Molt`) | Only `shared_prefix` matched: `sigma_shared_prefix` (`KeyStealingHorizonCore.lean:91`, plus its two internal uses and its guard at `Results/Axioms.lean:543`) and `horizon_shared_prefix` (`KeyStealingScheduleHorizon.lean:161` plus 16 call sites). **None of `UniqueOn`, `AlignedBounded`, `badLockAt`, `aligned_…`, `length_le_tip`, `tip_slot_ge`, `slot_ge_length`, `chain_length_le`, `window_shared` exists anywhere.** (These name shapes are presumably the design's *proposed new* names; on this evidence they do not collide — but the verifier never said so.) |
| 3 | 11 `paper/molt.tex` phrase alternatives (line 42) | 13 lines matched. Three alternatives are not represented among the matched lines: `its budget credit: honest scope below`, `counts thefts across all generations together`, and the `\rho + T` one (whose shell/regex escaping was `share the \$\\rho \+ T`, so a no-match there may be an escaping artefact rather than an absence). |
| 4 | `theorem quorum_overlap` (line 40) | Found at `Model.lean:95`, but **only the first line printed** — the verifier never saw its conclusion (relevant to gotcha 9's `quorum > 2·maxByzantine`). |
| 5 | `MoltPetit/Model/KeyStealingLockstep.lean` full read (line 18) | **Truncated**: "Output too large (34.8KB). Full output saved to `/run/claude/.../tool-results/blff7fup9.txt`". Only lines 1–31 entered context on that call; it recovered by re-reading 60–300 and 300–614 (lines 35, 37). **Lines 32–59 of that file (the tail of the module docstring) were never read.** |

---

## 4. Structured JSON assembled

**None.** No `StructuredOutput` tool call appears in the transcript, and no
drafted JSON appears in any assistant text block. The verifier's entire prose
output for the run is the single sentence at offset 5:

> I'll start by locating the key declarations the design relies on.

---

## 5. Where it stopped, precisely

* **Last tool call** (line 43, `toolu_01J6X1onCVz2TF17knigReoA`, 09:45:39Z):
  `grep -n -iE "gotcha|private|reuse" mode3-lockstep.md | head -40` plus
  `head -60 /etheron-pod/rollout-work/designs-partial/W5.md`.
* **Last tool result** (line 45, 09:45:40Z): the 11 GOTCHAS of §2.6 plus the
  first 60 lines of the W5 partial design note.
* **Last assistant sentence**: still the one at offset 5 — it produced no prose
  after the opening line.
* **Rate-limit record**: **line 46**, synthetic assistant message,
  `"You've hit your session limit · resets 2pm (UTC)"`, `error: "rate_limit"`,
  `apiErrorStatus: 429`, `rateLimitType: "five_hour"`,
  `overageStatus: "rejected"`, `resetsAt: 1788616800`, timestamp
  `2026-09-05T09:45:40.730Z`.
* Line 47 is empty (trailing newline).

**Net for the planner:** the accuracy sweep's *evidence gathering was
essentially complete* — every reused name located, every relevant signature
read, the duplicate-name check run, the paper/doc anchors checked, the module
map's gotchas loaded — and then it died before turning any of it into a
judgement. A re-run should not repeat §§1–2; it should start from §2 and write
the assessment.
