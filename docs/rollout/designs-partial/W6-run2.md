# W6 salvage (run 2) -- No-back-dating derivation per mode (rescoped surfaces from a timed model)

## Header

| | |
|---|---|
| Agent id | `a80804cf76f9ae257` |
| Workflow run | `wf_6b051052-ec7` (second run, Design phase) |
| Transcript | `/run/claude/agent/projects/-etheron-pod/c28ff38c-0cb1-500d-8726-22cd73943085/subagents/workflows/wf_6b051052-ec7/agent-a80804cf76f9ae257.jsonl` (91 lines) |
| Work item | **W6** -- per-mode no-back-dating derivation for `/etheron-pod/mini-consensus-lean` (additive-only new modules). Confirmed by the reading pattern (see section 3); the task prompt itself (offsets 0-3) was not read, per protocol. |
| Repo state seen | HEAD `8b8b766` "paper2 p16: appendix -- recency window, no-back-dating scope (AN/33, AN/34)"; `git status --short` printed nothing (clean). |
| Model / effort | claude-fable-5-1, effort high; cwd `/etheron-pod/rollout-work/designs-partial` |
| Started | 2026-09-05T07:10:14Z |
| Killed | 2026-09-05T07:16:56Z by HTTP 429 `rate_limit` -- "You've hit your session limit · resets 9am (UTC)" (rateLimitType `five_hour`, overage disabled at org level) -- line 90 of the transcript. |
| Lines seen | offsets 4-91 except 80: **87 lines** (offsets 0-3 = prompt + harness attachments, not read per protocol; offset 91 is an empty trailing line). |
| Lines skipped as too large | **offset 80** (73,909 tokens; Read refuses it even with limit=1). Its uuid is `22b0cf10-f6f8-4a54-a8c2-ff68b0f672f7` (parent of line 81). Lines 84/85/87/89 (user tool-results after it) carry a NEW `promptId` `0fe07ea6-1e6b-400c-925b-5542a527cfb5` (earlier user lines carry `ef278b43-3899-4810-8eda-28bc4d3753ed`), so line 80 is almost certainly a **user-role message** (a new/mid-task prompt from the orchestrator, possibly with large attachments) rather than assistant output. Its content is unknown. |
| Where it stopped | Still in the fact-gathering phase. 36 tool calls, all reads/greps; **no file was written, no StructuredOutput call was made, no design text was emitted.** All thinking blocks are redacted (empty `thinking` with signature only); the message at lines 81-88 spent 23,630 thinking tokens whose content is not in the transcript. The only assistant prose in the whole transcript is two sentences (quoted in section 3). |

**Extent of the salvage, honestly:** everything of value is the set of *facts the subagent verified* (section 2) -- it read the actual Lean source for every surface a per-mode no-back-dating derivation would touch, plus the owner's recorded rejection of `NoBackdate` for the key-stealing adversary, plus the paper's appendix on the residue. No design direction, definition, theorem statement, proof sketch, decision, or open question was ever written down by the subagent. Section 3 reconstructs the *thread of investigation* from its own tool-call descriptions (its words), clearly marked as inferred.

---

## 1. Files examined (in order), with the subagent's stated reason

Tool-call "description" strings are the subagent's own words and are quoted. Where the subagent wrote prose, it is quoted too.

| # | Line | Tool | Target (path, range) | Why (subagent's words / context) |
|---|---|---|---|---|
| 1 | 6 | Bash | `ls -la /etheron-pod/rollout-work/maps/`; `ls designs-partial`; `git log --oneline -1 && git status --short` in the repo | "List map files and check repo state". Preceded by: "I'll start by reading the primary digests for this item." |
| 2 | 10 | Bash | `/etheron-pod/rollout-work/maps/timed-core-liveness.md` lines 1-400 (persisted to tool-results `b3ibp3vao.txt`, 32.1KB) | "Read timed-core-liveness digest part 1". Preceded by: "Next I need the four primary digests plus the existing sibling designs (W3a, W5) since W6 must share a timed structure with them. All are independent, so I'll fetch them together." |
| 3 | 12 | Bash | same digest lines 400-900 (the tail: Model.lean/Soundness/Bridge tables, reuse_notes, open_items_found) | "Read timed-core-liveness digest part 2" |
| 4 | 14 | Bash | `/etheron-pod/rollout-work/maps/mode2-horizon-timed.md` lines 1-450 (persisted to `bf0xr3kci.txt`, 40KB) | "Read mode2-horizon-timed digest part 1" |
| 5 | 16 | Bash | same digest lines 450-900 (empty -- file is 130 lines) | "Read mode2-horizon-timed digest part 2" |
| 6 | 18 | Bash | `/etheron-pod/rollout-work/designs-partial/W3a.md` (full) | "Read sibling design W3a" |
| 7 | 20 | Bash | `/etheron-pod/rollout-work/designs-partial/W5.md` (full) | "Read sibling design W5" |
| 8 | 24 | Read | tool-results `b3ibp3vao.txt` lines 1-200 (timed-core-liveness digest: Timed.lean, TimedSig.lean, Liveness.lean, Definitions.lean, Results.lean tables) | re-reading the persisted digest in full |
| 9 | 26 | Read | same, lines 200-450 (Results.lean ProverTiming, Molt/Results, Molt/Liveness, Molt/Protocol, Molt/Assumptions, Molt/Verifier, Molt/Rotation, KeyIndex, KeyRotationLiveness, Model.lean tables) | continuation |
| 10 | 28 | Read | tool-results `bf0xr3kci.txt` lines 1-220 (whole mode2-horizon-timed digest: 130 lines) | re-reading the persisted digest in full |
| 11 | 30 | Read | same, offset 220 (past EOF; file has 130 lines) | continuation attempt |
| 12 | 34 | Read | `/etheron-pod/rollout-work/maps/mode1-chain.md` lines 1-160 (KeyIndex, KeyRotation, KeyStealing, KeyStealingSafety, KeyStealingUnique, KeyStealingBudget tables) | mode-1 surface |
| 13 | 36 | Read | same, lines 160-360 (KeyStealingLongRange, KeyStealingCert, Results/KeyStealingResults, HorizonCore, Horizon, ScheduleHorizon, Molt/Rotation, Molt/ClientRule, Molt/MaxSync tables) | continuation |
| 14 | 38 | Read | `/etheron-pod/rollout-work/maps/mode3-lockstep.md` lines 1-160 (KeyStealingLockstep, LOCKSTEP_DESIGN.md, ScheduleBudget, ScheduleCert, Schedule, Cert tables) | mode-3 surface |
| 15 | 40 | Read | same, lines 160-360 (KeyStealingResults, ScheduleResults, ScheduleHorizon, Definitions, Model, KeyIndex, Molt/Rotation, Axioms tables; reuse_notes; open_items_found) | continuation |
| 16 | 42 | Bash | `cat -n MoltPetit/Model/TimedSig.lean` (full, 162 lines) | "Read TimedSig.lean in full" |
| 17 | 44 | Bash | `MoltPetit/Model/Definitions.lean` lines 540-560 and 640-760 (with relative line refs) + grep for `structure SigUnforgeableRecent`, `structure TimedExecution`, `abbrev TimedLog`, `def SignedEver`, `def AvailableAt`, `abbrev SigningLog`, `def HonestSlotsUnique`, `abbrev ByzantineSlots` | "Read Definitions.lean signing-model region with line refs" |
| 18 | 48 | Bash | `MoltPetit/Model/KeyStealingUnique.lean` lines 120-200 | "Read KeyStealingEUFCMA and VersionedUnforgeable definitions" |
| 19 | 50 | Bash | `MoltPetit/Model/KeyStealingSchedule.lean` lines 40-60 and 85-135 | "Read schedPinned, validSignedChainSched, SchedUnforgeable, badSched" |
| 20 | 52 | Bash | `MoltPetit/Model/KeyStealingScheduleCert.lean` lines 100-120 and 180-260 | "Read validSignedChainSchedCore, SchedCoreUnforgeable, schedUnforgeable_of_core, honestSlotsUnique_schedCore" |
| 21 | 54 | Bash | `MoltPetit/Model/KeyStealing.lean` lines 1-134 (full) | "Read KeyStealing.lean in full (badKeyrotOn, KeyStealingExecution)" |
| 22 | 56 | Bash | `MoltPetit/Model/KeyStealingScheduleTimed.lean` lines 1-110, 225-245, 300-330 | "Read mode-2 timed layer header, stolenOf/NoPrematureTheft/ErasureTimed, NoPrematureMint, PackageATimed" |
| 23 | 58 | Bash | `MoltPetit/Model/KeyStealingLockstep.lean` lines 95-115, 150-170, 240-300 | "Read validSignedChainLock, lagSched, schedCore0_of_lock, LockstepPackage" |
| 24 | 60 | Bash | grep `-i "forward.secur\|back.dat\|backdat\|NoBackdate\|stolen keys sign"` over `memory/*.md KEY_ROTATION_SOUND.md ROTATION_MODES.md HANDOFF_SCHEDULE_VARIANT.md CLAUDE.md`; `ls memory/` | "Search repo docs and memory for forward-security / back-dating rejection" |
| 25 | 62 | Bash | grep `-i "back-dat\|backdat\|no-back\|NoBackdate\|forward-secure\|forward secur\|AN/33\|AN/34\|Assumption 2\|2(c)\|recency window"` in `paper/molt.tex` | "Locate no-back-dating and Assumption 2(c) passages in the paper" |
| 26 | 64 | Bash | `cat MoltPetit.lean`; `cat Molt.lean`; `MoltPetit/Results/Axioms.lean` lines 1-40; grep `-B3 "sigUnforgeableRecent_of_timed\|noBackdate_independent"` in both Axioms files | "Read root import lists and the axiom-guard idiom" |
| 27 | 68 | Bash | `memory/key-rotation-mission.md` lines 10-32, 280-296, 445-456; `KEY_ROTATION_SOUND.md` lines 76-90, 160-220 | "Read owner's rejection of NoBackdate and the v3 re-derivation text" |
| 28 | 70 | Bash | `paper/molt.tex` lines 700-740 and 1400-1510 | "Read paper Assumption 2(c) context and the no-back-dating appendix" |
| 29 | 72 | Bash | grep `"X-3\|mint time\|theft-before-mint\|Not yet modeled\|^## \|^### "` in `ROTATION_MODES.md`; grep `-A6 "X-3"`; grep in `/etheron-pod/rollout-work/maps/design-docs.md` (file does not exist) | "Locate the mint-times / not-yet-modeled items in ROTATION_MODES and the design-docs digest" |
| 30 | 74 | Bash | `MoltPetit/Model/KeyStealingSchedule.lean` lines 136-206; grep `-A8 "theorem rotated_key_dead"` in KeyStealingSchedule.lean, KeyStealingScheduleCert.lean, KeyRotation.lean | "Read honestSlotsUnique_sched proof and rotated_key_dead variants" |
| 31 | 76 | Bash | `MoltPetit/Model/KeyStealingScheduleTimed.lean` lines 110-160, 240-300, 375-423 | "Read theft_is_recent, recentTheftProducers, forwardstamp theorems, PackageBTimed" |
| 32 | 78 | Bash | `Definitions.lean` lines 204-236 and 590-606; `Molt/Results.lean` lines 128-150; `KeyStealingHorizonCore.lean` lines 176-200; `KeyStealingCert.lean` lines 228-246 | "Read sigOk/SignedBlock/TSSigned, Molt NoBackdate re-export, honestSlotsUnique_keyrot_horizon statement, SignedDeclared" |
| -- | 80 | (unreadable, 73,909 tokens; user-role, new promptId) | -- | -- |
| 33 | 82 | Bash | `Definitions.lean` lines 56-76; `cat lakefile.toml`; grep `"EUF-CMA\|ass:sig\|thm:refresh\|sec:timed\|label{sec:rotation}\|not-before\|cold-root\|erasure discipline\|assumed, not derived"` in `paper/molt.tex` | "Check Block deriving, lakefile, and paper anchor lines" |
| 34 | 83 | Bash | `paper/molt.tex` lines 1385-1400; grep `"begin{assumption}"` | "Read trusted-base paragraph and locate assumption environments" |
| 35 | 86 | Bash | `ROTATION_MODES.md` lines 74-90, 120-135, 171-185, 223-232; `KEY_ROTATION_SOUND.md` lines 24-36 | "Read ROTATION_MODES operator duties and not-yet-modeled table, KEY_ROTATION_SOUND provenance lines" |
| 36 | 88 | Bash | `Molt/Rotation.lean` lines 104-135; `Molt/Axioms.lean` lines 120-160; `tail -30 MoltPetit/Results/Axioms.lean`; `head -20 MoltPetit/Model/KeyRotationTests.lean` | "Read Molt abbrev idiom, both axiom-file tails, and the tests module header" |

Not examined: `MoltPetit/Model/Timed.lean` source (only via digest), `Results/Results.lean` source, `KeyStealingBudget.lean` source, `KeyStealingHorizon.lean` source, `Molt/ClientRule.lean`, `Molt/MaxSync.lean`, `LOCKSTEP_DESIGN.md`, `PHASE2_DESIGN.md`, `KEY_INDEX_DESIGN.md`, the maps `core-grounded-cert1.md`, `mode2-cert-budget.md`, `results-molt.md`, and the sibling designs W1/W2/W4.

---

## 2. Verified facts

### 2A. From Lean source, read directly (exact declarations)

All paths relative to `/etheron-pod/mini-consensus-lean`. All in `namespace MoltPetit.Model` unless noted.

#### `MoltPetit/Model/TimedSig.lean` (162 lines, `import MoltPetit.Model.Timed`)

- Module doc L13-26 ("What the timed model alone does *not* give"): "`TimedExecution` carries plain per-real-slot uniqueness (`honest_once`: one block per honest real slot) but it deliberately lets a *bad* real slot `r` sign a block with any stamp in that producer's residue class (`key_match`: `B.slot % n = r % n`). So a block stamped at an **honest** slot `s` can be first-signed at a *different*, *bad* real slot `r ≡ s (mod n)` — the honest slot `s` is never even exercised. `honest_stamp` does not forbid this (it constrains only honest real slots), and neither recency nor the forged-time bound rules it out for a *single* block ... Hence the per-block pinning that `SigUnforgeableRecent` asserts does **not** follow from recency alone — contrary to a tempting reading."
- Module doc L28-40 ("The residue that does suffice"): "`NoBackdate` is the missing content: a block whose stamp is honest was signed at the real slot equal to its stamp. Operationally this is honest key custody re-anchored to the *stamp* ... It is guaranteed by *forward-secure / key-evolving* signatures (the per-period key cannot sign for a different period — exactly the upgrade the limitations section recommends), or by a signing oracle that stamps its own real slot. With it, `sigUnforgeableRecent_of_timed` derives `SigUnforgeableRecent` for the projected log, with no recency or chain hypotheses left over — the scoping in `SigUnforgeableRecent` is then slack".
- L45-56:
  ```lean
  open Classical in
  noncomputable def projectSigned (n : Nat) (log : TimedLog) : SigningLog :=
    fun p s =>
      if h : p = producerForSlot n s ∧ ∃ B, B ∈ log s ∧ B.slot = s
      then some h.2.choose else none
  ```
- L65-66:
  ```lean
  def NoBackdate (bad : ByzantineSlots) (log : TimedLog) : Prop :=
    ∀ ⦃r : Nat⦄ ⦃B : Block⦄, B ∈ log r → ¬ bad B.slot → B.slot = r
  ```
  (`bad` is applied to the STAMP `B.slot`; `TimedExecution` applies `bad` to the REAL slot `r`.)
- L79-84:
  ```lean
  theorem sigUnforgeableRecent_of_timed {n : Nat} {bad : ByzantineSlots}
      {log : TimedLog} {G : Block} {Signed : Block → Prop} {now Δ : Nat}
      (hexec : TimedExecution n bad log G)
      (hNB : NoBackdate bad log)
      (hbridge : ∀ ⦃B : Block⦄, Signed B → ∃ r, B ∈ log r) :
      SigUnforgeableRecent n bad Signed (projectSigned n log) now Δ
  ```
  Proof (L85-102): `constructor; intro B c _hVC _hBc _hrec hbadB hSB` (ValidChain, membership and recency hypotheses discarded); `obtain ⟨r, hBr⟩ := hbridge hSB`; `have hrEq : B.slot = r := hNB hBr hbadB`; `have hBlog : B ∈ log B.slot := hrEq ▸ hBr`; build `hcond : producerForSlot n B.slot = producerForSlot n B.slot ∧ ∃ B', B' ∈ log B.slot ∧ B'.slot = B.slot := ⟨rfl, B, hBlog, rfl⟩`; `change projectSigned n log (producerForSlot n B.slot) B.slot = some B; unfold projectSigned; rw [dif_pos hcond]`; `have hspec := hcond.2.choose_spec`; `have hchoose : hcond.2.choose = B := hexec.honest_once hbadB hspec.1 hBlog; rw [hchoose]`. Uses ONLY `hexec.honest_once` from the timed model.
- L119-121:
  ```lean
  theorem noBackdate_independent :
      ∃ (bad : ByzantineSlots) (log : TimedLog) (G : Block),
        TimedExecution 2 bad log G ∧ ¬ NoBackdate bad log
  ```
  Proof: `classical`; witness `bad := fun r => r = 3`, `log := fun r => if r = 3 then {(⟨1, 1, some 100, 101, 0, 0⟩ : Block)} else ∅`, `G := ⟨0, 0, none, 100, 0, 0⟩`; helper `hlog : ∀ r B, B ∈ (if r = 3 then {…} else ∅) ↔ (r = 3 ∧ B = ⟨1,1,some 100,101,0,0⟩)` by `by_cases hr : r = 3 <;> simp [hr]`; all five fields via `refine { key_match := ?_, honest_stamp := ?_, honest_once := ?_, chain_order := ?_, id_inj := ?_ }`; chain_order witness `⟨⟨0, 0, none, 100, 0, 0⟩, ?_, Or.inl rfl⟩` + `simpa using hi`; id_inj by a `key` lemma enumerating `SignedEver` then `rcases … <;> first | rfl | (simp at hid)`; the ¬NoBackdate half: `hmem` by `simp`, `hbad : ¬ ((⟨1,1,some 100,101,0,0⟩ : Block).slot = 3) := by decide`, `exact absurd (hNB (r := 3) hmem hbad) hbad`.
- Docstring L104-117 of `noBackdate_independent`: "the per-block pinning that `sigUnforgeableRecent_of_timed` delivers genuinely requires `NoBackdate`: it does not follow from `key_match`/`honest_stamp`/`honest_once`/`chain_order`/`id_inj`, nor from recency. (The forged block could moreover sit at an arbitrarily recent tip — an operational remark, not part of this statement ...) This is the back-dating attack the forward-secure custody residue rules out."

#### `MoltPetit/Model/Definitions.lean` (grep-confirmed line numbers)

- L58-74: `structure Block where slot : Nat; height : Nat; prev : Option Nat; id : Nat; contentsHash : Nat; keyIndex : Nat` `deriving Repr, DecidableEq`. L75 `abbrev Chain := List Block`. Anonymous-constructor order ⟨slot, height, prev, id, contentsHash, keyIndex⟩.
- L204 `abbrev KeyRegistry (pk : Type) := Nat → Nat → pk`.
- L212 `structure SignedBlock (σ : Type) where block : Block; sig : σ` `deriving Repr`. L218 `abbrev SignedChain (σ : Type) := List (SignedBlock σ)`. L221 `def stripSigs {σ : Type} (sc : SignedChain σ) : Chain := sc.map SignedBlock.block`.
- L226: `def sigOk {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (sb : SignedBlock σ) : Bool := ops.verify (registry (producerForSlot n sb.block.slot) sb.block.keyIndex) sb.block sb.sig` -- verifies under the DECLARED in-band keyIndex. L231 `def sigsOk … : Bool := sc.all (sigOk n ops registry)`.
- L459 `abbrev ByzantineSlots := Nat → Prop`. L498 `def HonestSlotsUnique (bad : ByzantineSlots) (record : SlotRecord) : Prop := …`.
- L541-548: `structure SigCorrect {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (keyPair : Nat → Nat → sk) : Prop where verify_sign : ∀ (i j : Nat) (b : Block), producerForSlot n b.slot = i → b.keyIndex = j → ops.verify (registry i j) b (ops.sign (keyPair i j) b) = true`.
- L558 `abbrev SigningLog := Nat → Nat → Option Block` (docstring: "That this is a partial *function* (at most one block per participant per slot) is precisely the honest behaviour of the implementation: the node's outer loop calls production at most once per slot."). Same type as `honestSigned : Nat → Nat → Option Block` in every keyrot/sched surface.
- L597-600: `def TSSigned (n : Nat) (sigOps : MoltPetit.SigOps) (B : Block) : Prop := ∃ sig : MoltPetit.RawSignature, sigOps.verify (sigOps.keyFor (producerForSlot n B.slot) B.keyIndex) B.slot B.height (B.prev.map Int.ofNat) B.id sig = true`.
- L656-659: `def SignedHashInjective (Signed : Block → Prop) (G : Block) : Prop := ∀ ⦃B B' : Block⦄, (B = G ∨ Signed B) → (B' = G ∨ Signed B') → B.id = B'.id → B = B'`.
- L677-684:
  ```lean
  structure SigUnforgeableRecent (n : Nat) (bad : ByzantineSlots)
      (Signed : Block → Prop) (signed : SigningLog)
      (now Δ : Nat) : Prop where
    verified_was_signed :
      ∀ ⦃B : Block⦄ ⦃c : Chain⦄, ValidChain n c → B ∈ c →
        (∃ t : Block, c.getLast? = some t ∧ now ≤ t.slot + Δ) →
        ¬ bad B.slot → Signed B →
        signed (producerForSlot n B.slot) B.slot = some B
  ```
  Docstring L661-676: "This is the assumption the timed model justifies for the tight rule `Δ = n` (`Model/Timed.lean`): `forged_suffix_time_bound` proves that harvesting coerced signatures into a fork is rate-limited to `maxByzantine` blocks per `n` real slots, so a fork meeting the recency bar caps out around `2·maxByzantine ≈ 2n/3` harvested blocks — short of the `n + 1` needed ... (breakeven at `Δ ≈ 1.5n`, so `Δ = n` keeps ~50% margin)."
- L694 `abbrev TimedLog := Nat → Finset Block` ("What was signed at each **real** slot. The blocks in `log r` carry signatures under the key of `r`'s designated producer").
- L698 `def SignedEver (log : TimedLog) (G : Block) (B : Block) : Prop := B = G ∨ ∃ r, B ∈ log r`.
- L703 `def AvailableAt (log : TimedLog) (G : Block) (B : Block) (R : Nat) : Prop := B = G ∨ ∃ r ≤ R, B ∈ log r`.
- L719-737:
  ```lean
  structure TimedExecution (n : Nat) (bad : ByzantineSlots) (log : TimedLog)
      (G : Block) : Prop where
    key_match : ∀ ⦃r : Nat⦄ ⦃B : Block⦄, B ∈ log r → B.slot % n = r % n
    honest_stamp : ∀ ⦃r : Nat⦄, ¬ bad r → ∀ ⦃B : Block⦄, B ∈ log r → B.slot = r
    honest_once : ∀ ⦃r : Nat⦄, ¬ bad r →
      ∀ ⦃B B' : Block⦄, B ∈ log r → B' ∈ log r → B = B'
    chain_order : ∀ ⦃r : Nat⦄ ⦃B : Block⦄, B ∈ log r →
      ∀ ⦃i : Nat⦄, B.prev = some i →
        ∃ P : Block, P.id = i ∧ AvailableAt log G P r
    id_inj : ∀ ⦃B B' : Block⦄, SignedEver log G B → SignedEver log G B' →
      B.id = B'.id → B = B'
  ```
  Docstring L706-717: "Corruption is per real slot: at a bad real slot `r` the adversary may extract arbitrarily many signatures from `r`'s producer (blocks with any stamp in that producer's residue class); at an honest real slot the node signs at most its own current block. `chain_order` is the formal residue of the id-formation contract (`id = H(slot, height, prev, parentSig, contentsHash, keyIndex)`)".
- L753-755: `def HonestBlocksCover (bad : ByzantineSlots) (record : SlotRecord) (c : Chain) (u n : Nat) : Prop := ∀ s, ¬ bad s → u ≤ s → s < u + n → ∃ B : Block, B ∈ record s ∧ B ∈ c`.

#### `MoltPetit/Model/KeyStealingUnique.lean` (lines 120-200)

- Provenance docstring (L~124-135, immediately above `KeyStealingEUFCMA`): "**Provenance — the exact boundary of trust.** This surface is **assumed**, not reduced to the timed model. The classical-adversary analogue `SigUnforgeableRecent` is *derived* (`sigUnforgeableRecent_of_timed`) from a `TimedExecution` plus `NoBackdate`, with `noBackdate_independent` witnessing that the extra assumption has real content. The key-stealing adversary deliberately **refuses** `NoBackdate`/forward security (`KEY_ROTATION_SOUND.md` §1–2), so that derivation is unavailable by design; `KeyStealingEUFCMA` is therefore taken as a named primitive. What the development **does** prove on top of it is the index-pin half: `versionedUnforgeable_of_keyStealingEUFCMA` discharges the "the verifying version is never rotated-out" step via the proven `rotated_key_dead`, so *only* the bare recency-scoped registry EUF-CMA is assumed, never the pin."
- L136-147:
  ```lean
  structure KeyStealingEUFCMA (n Δconf : Nat) {Sig sk pk : Type} (ops : SigOps Sig sk pk)
      (registry : KeyRegistry pk) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop)
      (honestSigned : Nat → Nat → Option Block) (now Δ : Nat) : Prop where
    unforgeable :
      ∀ {sc : SignedChain Sig} {sb : SignedBlock Sig} {j : Nat},
        validSignedChainK' n Δconf ops registry sc = true →
        sb ∈ sc →
        (∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) →
        ops.verify (registry (producerForSlot n sb.block.slot) j) sb.block sb.sig = true →
        ¬ rented sb.block.slot →
        ¬ Stolen (producerForSlot n sb.block.slot) j →
        honestSigned (producerForSlot n sb.block.slot) sb.block.slot = some sb.block
  ```
- L161-173 `structure VersionedUnforgeable (n Δconf : Nat) … : Prop where verified_was_signed : ∀ {sc} {sb}, validSignedChainK' n Δconf ops registry sc = true → sb ∈ sc → (∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) → ¬ rented sb.block.slot → (∀ j, inForce n Δconf (stripSigs sc) (producerForSlot n sb.block.slot) sb.block.slot ≤ j → ¬ Stolen (producerForSlot n sb.block.slot) j) → honestSigned (producerForSlot n sb.block.slot) sb.block.slot = some sb.block` -- "an *intermediate* — it is **derived** from the primitive `KeyStealingEUFCMA` ... not assumed independently"; no explicit `ops.verify` premise.
- L184-192 `theorem versionedUnforgeable_of_keyStealingEUFCMA … (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ) : VersionedUnforgeable n Δconf ops registry rented Stolen honestSigned now Δ where verified_was_signed hVal hmem hRecent hNotRent hNotStolen := have hDead := rotated_key_dead _ _ _ _ hVal hmem; hEUF.unforgeable hVal hmem hRecent hDead.1 hNotRent (hNotStolen _ hDead.2)`.
- L~194-200 docstring of `honestSlotsUnique_keyrot` (P2-B): strong induction on the slot; reconciles the sc'-side in-force index via `confirmed_mem_iff_le` (`Δconf ≥ 2n`).

#### `MoltPetit/Model/KeyRotation.lean`

- L401-409 `theorem rotated_key_dead {σ sk pk : Type} (n Δconf : Nat) (ops : SigOps σ sk pk) (registry : KeyRegistry pk) {sc : SignedChain σ} (h : validSignedChainK' n Δconf ops registry sc = true) {sb : SignedBlock σ} (hmem : sb ∈ sc) : ops.verify (registry (producerForSlot n sb.block.slot) sb.block.keyIndex) sb.block sb.sig = true ∧ inForce n Δconf (stripSigs sc) (producerForSlot n sb.block.slot) sb.block.slot ≤ sb.block.keyIndex` (n, Δconf, ops, registry EXPLICIT).

#### `MoltPetit/Model/KeyStealingSchedule.lean`

- L46-47 `def schedPinned (schedule : Nat → Nat) (c : Chain) : Bool := c.all (fun b => decide (schedule b.slot ≤ b.keyIndex))`.
- L51-54 `def validSignedChainSched {σ sk pk : Type} (n : Nat) (schedule : Nat → Nat) (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool := sigsOk n ops registry sc && validChainK n (stripSigs sc) && schedPinned schedule (stripSigs sc)`.
- L56 `theorem validChain_of_validSignedChainSched … (h : validSignedChainSched n schedule ops registry sc = true) : ValidChain n (stripSigs sc)` (proof: `rw [validSignedChainSched, Bool.and_eq_true, Bool.and_eq_true] at h` …).
- L67-73 `theorem rotated_key_dead_sched {σ sk pk} {n} {schedule} {ops} {registry} {sc} (h : validSignedChainSched n schedule ops registry sc = true) {sb} (hmem : sb ∈ sc) : ops.verify (registry (producerForSlot n sb.block.slot) sb.block.keyIndex) sb.block sb.sig = true ∧ schedule sb.block.slot ≤ sb.block.keyIndex` (all implicit; proof `rw [validSignedChainSched, Bool.and_eq_true, Bool.and_eq_true] at h; obtain ⟨⟨hSig, _hK⟩, hPin⟩ := h` …).
- L88-96 `theorem signedDeclared_of_mem_sched … (h : validSignedChainSched … = true) {B : Block} (hB : B ∈ stripSigs sc) : SignedDeclared n ops registry B` (proof via `List.mem_map.mp hB` and `rotated_key_dead_sched`).
- L105-116 `structure SchedUnforgeable (n : Nat) (schedule : Nat → Nat) {Sig sk pk : Type} (ops) (registry) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block) (now Δ : Nat) : Prop where unforgeable : ∀ {sc sb j}, validSignedChainSched n schedule ops registry sc = true → sb ∈ sc → (∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) → ops.verify (registry (producerForSlot n sb.block.slot) j) sb.block sb.sig = true → ¬ rented sb.block.slot → ¬ Stolen (producerForSlot n sb.block.slot) j → honestSigned (producerForSlot n sb.block.slot) sb.block.slot = some sb.block` -- identical shape to `KeyStealingEUFCMA` with the validator swapped.
- L124-126 `def badSched (n : Nat) (schedule : Nat → Nat) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop) (s : Nat) : Prop := rented s ∨ ∃ j, schedule s ≤ j ∧ Stolen (producerForSlot n s) j`.
- L140-190 `theorem honestSlotsUnique_sched {n} {schedule} {Sig sk pk} {ops} {registry} {rented} {Stolen} {honestSigned} {now Δ} (hUnf : SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ) {sc sc' : SignedChain Sig} (hVal : validSignedChainSched n schedule ops registry sc = true) (hVal' : … sc' = true) (hRecent : ∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ) : HonestSlotsUnique (badSched n schedule rented Stolen) (chainUnionRecord sc sc')`. Proof template: `hVc/hVc'` via `validChain_of_validSignedChainSched`; `intro s hbad B B' hB hB'`; `rw [mem_chainUnionRecord] at hB hB'`; `simp only [badSched, not_or] at hbad`; `obtain ⟨hNotRent, hNotStolen⟩ := hbad`; `push Not at hNotStolen` (gives `∀ j, schedule s ≤ j → ¬ Stolen (producerForSlot n s) j`); a `cross` lemma `∀ X Y, X ∈ stripSigs sc → Y ∈ stripSigs sc' → X.slot = s → Y.slot = s → X = Y` built from `List.mem_map.mp`, `rotated_key_dead_sched hVal hsbxmem` (hDx), `hUnf.unforgeable hVal hsbxmem hRecent hDx.1 (by rw [hsbxslot]; exact hNotRent) (by rw [hsbxslot]; exact hNotStolen sbx.block.keyIndex (by rw [← hsbxslot]; exact hDx.2))`, then `rwa [hsbxslot, hsbxeq] at this`; `rw [h1] at h2; exact Option.some.inj h2`; final `rcases hBmem with hBc | hBc' <;> rcases hB'mem with hB'c | hB'c'` closing same-chain cases with `strictSlots_unique hVc.2.1 hBc hB'c (hBs.trans hB's.symm)`. "No `hAgree`, no induction, **no `Δconf ≥ 2n`**."

#### `MoltPetit/Model/KeyStealingScheduleCert.lean`

- L109-112 `def validSignedChainSchedCore {σ sk pk : Type} (n : Nat) (schedule : Nat → Nat) (ops) (registry) (sc) : Bool := sigsOk n ops registry sc && validChain n (stripSigs sc) && schedPinned schedule (stripSigs sc)` (drops `keyMonoOk`).
- L115 `theorem schedCore_of_validSignedChainSched (h : validSignedChainSched … = true) : validSignedChainSchedCore … = true`.
- L135-141 `theorem rotated_key_dead_schedCore … (h : validSignedChainSchedCore n schedule ops registry sc = true) {sb} (hmem : sb ∈ sc) : ops.verify (registry (producerForSlot n sb.block.slot) sb.block.keyIndex) sb.block sb.sig = true ∧ schedule sb.block.slot ≤ sb.block.keyIndex`.
- L180-188 `theorem signedDeclared_of_mem_schedCore … : SignedDeclared n ops registry B`.
- L200-211 `structure SchedCoreUnforgeable (n : Nat) (schedule : Nat → Nat) {Sig sk pk : Type} (ops) (registry) (rented) (Stolen) (honestSigned) (now Δ : Nat) : Prop where unforgeable : ∀ {sc sb j}, validSignedChainSchedCore n schedule ops registry sc = true → sb ∈ sc → (∃ t, …) → ops.verify (registry (producerForSlot n sb.block.slot) j) sb.block sb.sig = true → ¬ rented sb.block.slot → ¬ Stolen (producerForSlot n sb.block.slot) j → honestSigned … = some sb.block`.
- L216-223 `theorem schedUnforgeable_of_core {n} {schedule} {Sig sk pk} {ops} {registry} {rented} {Stolen} {honestSigned} {now Δ} (h : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ) : SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ := ⟨fun hVal hmem hRecent hverify hrent hstolen => h.unforgeable (schedCore_of_validSignedChainSched hVal) hmem hRecent hverify hrent hstolen⟩`.
- L231-260 `theorem honestSlotsUnique_schedCore … (hUnf : SchedCoreUnforgeable …) {sc sc'} (hVal hVal' : validSignedChainSchedCore … = true) (hRecent hRecent' : ∃ t, …) : HonestSlotsUnique (badSched n schedule rented Stolen) (chainUnionRecord sc sc')` -- verbatim mirror of `honestSlotsUnique_sched` using `validChain_of_validSignedChainSchedCore` and `rotated_key_dead_schedCore`.

#### `MoltPetit/Model/KeyStealing.lean` (134 lines, `import MoltPetit.Model.KeyRotation`)

- Module doc L3-24: "The strong adversary of `KEY_ROTATION_SOUND.md` (v3): a stolen delegate key `dk(i,j)` signs **anything, at any slot, forever** — no forward security." Lists `badKeyrotOn`, `timedExecution_of_bad_iff`, `KeyStealingExecution` ("the timed core over the enriched `badKeyrotOn`, **plus** the bridge that a stolen-key block consumes a bad real slot. The signed registry lives on the `SignedChain` side; the timed (bare-`Block`) layer sees only the abstract `StolenMint : Block → Prop` predicate, exactly as `TimedSig` bridges the timed and signed worlds through an abstract `Signed`."), `keyStealing_refines_timed`.
- L47-50:
  ```lean
  def badKeyrotOn (n Δconf : Nat) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop)
      (c₀ : Chain) (s : Nat) : Prop :=
    rented s ∨ ∃ j, inForce n Δconf c₀ (producerForSlot n s) s ≤ j ∧
      Stolen (producerForSlot n s) j
  ```
- L67-70 `theorem badKeyrotOn_lossOnly (n Δconf : Nat) (rented : ByzantineSlots) (c₀ : Chain) : badKeyrotOn n Δconf rented (fun _ _ => False) c₀ = rented := by funext s; simp [badKeyrotOn]`.
- L79-88:
  ```lean
  theorem timedExecution_of_bad_iff {n : Nat} {bad bad' : ByzantineSlots}
      {log : TimedLog} {G : Block}
      (hiff : ∀ s, bad s ↔ bad' s)
      (h : TimedExecution n bad log G) :
      TimedExecution n bad' log G := by
    refine ⟨h.key_match, ?_, ?_, h.chain_order, h.id_inj⟩
    · intro r hr B hB
      exact h.honest_stamp (fun hb => hr ((hiff r).mp hb)) hB
    · intro r hr B B' hB hB'
      exact h.honest_once (fun hb => hr ((hiff r).mp hb)) hB hB'
  ```
  ("`TimedExecution` depends on `bad` only through the negated guards of `honest_stamp`/`honest_once`".)
- L101-108:
  ```lean
  structure KeyStealingExecution (n Δconf : Nat)
      (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop) (StolenMint : Block → Prop)
      (c₀ : Chain) (log : TimedLog) (G : Block) : Prop where
    toTimed : TimedExecution n (badKeyrotOn n Δconf rented Stolen c₀) log G
    steal_bad : ∀ ⦃r : Nat⦄ ⦃B : Block⦄, B ∈ log r → StolenMint B →
      badKeyrotOn n Δconf rented Stolen c₀ r
  ```
  Docstring L93-100: "`StolenMint : Block → Prop` is the unsigned image of "verifies under a stolen registry version"; the actual `ops`/`registry`/`sig` content lives on the `SignedChain` side (where `VersionedUnforgeable` is stated) and is connected to this predicate by a separate bridge hypothesis in Phase 3 — keeping the timed and signed encodings disjoint but bridged (cf. `TimedSig`)." (Digest: the only consumer of `KeyStealingExecution` in the repo is `keyStealing_refines_timed`.)
- L117-133 `theorem keyStealing_refines_timed {n Δconf} {rented} {Stolen} {StolenMint} {c₀} {log} {G} (hNoStealLive : ∀ s j, inForce n Δconf c₀ (producerForSlot n s) s ≤ j → ¬ Stolen (producerForSlot n s) j) (h : KeyStealingExecution n Δconf rented Stolen StolenMint c₀ log G) : TimedExecution n rented log G` -- proof `refine timedExecution_of_bad_iff ?_ h.toTimed; intro s; unfold badKeyrotOn; constructor; · rintro (hr | ⟨j, hj, hst⟩) …; · exact Or.inl`.

#### `MoltPetit/Model/KeyStealingScheduleTimed.lean` (423 lines; imports `KeyStealingScheduleHorizon`, `KeyStealingScheduleBudget`; `open Classical` at L81 right after `namespace MoltPetit.Model`)

- Module doc L5-13: for "the **flagship schedule** `schedule s = s / R` (period `R`, generation `j` provisioned just-in-time at era start `j * R`)".
- Module doc L30-44 (verbatim, the direction accounting): "`sched_forwardstamp_bounded` — **bounded forward-stamping**: a block of a schedule-pinned chain minted at real slot `r` bears a stamp `< r + R`, because the signing key for a later stamp does not exist yet (`NoPrematureMint`, the mint-side face of just-in-time provisioning). Direction-honest contrast with the static model's `NoBackdate` (the **two-sided** pin: an honest-stamp block's stamp *equals* its mint slot, which must be assumed outright — `noBackdate_independent`'s witness is a *back-dated* block, stamp `1` minted at bad real slot `3`): the schedule derives the **forward half** of that pin with `R` slack — a recent stamp implies a recent mint. The **back-dating half** (an old-stamped block minted arbitrarily late with a live stolen key of a legal generation) is *not* derived — `sched_backdate_consistent` machine-checks that it is consistent with everything this module assumes; that capability is what the budget accounting charges, and its per-block exclusion is the assumed EUF-CMA surface's business."
- Module doc L58-77 ("Honest scope"): "**The census is future-inclusive.** ... Confining the census to thefts *before the client's validation time* requires re-plumbing the EUF-CMA surface itself with mint times (a `SchedTimedUnforgeable` whose conclusion keys on theft-before-mint rather than theft-ever) — the natural next increment, not attempted here." and "`NoPrematureTheft` / `NoPrematureMint` / `ErasureTimed` are named operational hypotheses (the formalizations of A3/B3 and B2), justified by just-in-time cold-root delegation and honest erasure; they are not further reduced. The EUF-CMA surface (`SchedCoreUnforgeable`) and hash injectivity are unchanged and still assumed."
- L90-91 `def stolenOf (stolenAt : Nat → Nat → Nat → Prop) (i j : Nat) : Prop := ∃ r, stolenAt i j r`.
- L96-97 `def NoPrematureTheft (R : Nat) (stolenAt : Nat → Nat → Nat → Prop) : Prop := ∀ i j r, stolenAt i j r → j * R ≤ r`.
- L102-103 `def ErasureTimed (R : Nat) (stolenAt : Nat → Nat → Nat → Prop) : Prop := ∀ i j r, stolenAt i j r → r < (j + 1) * R`.
- L107-112 `theorem theft_during_era_of_erasure {R} {stolenAt} (hA3 : NoPrematureTheft R stolenAt) (hEr : ErasureTimed R stolenAt) {i j r : Nat} (h : stolenAt i j r) : j * R ≤ r ∧ r < (j + 1) * R := ⟨hA3 i j r h, hEr i j r h⟩`.
- L122-136 `theorem theft_is_recent {R : Nat} (hR : 0 < R) {stolenAt} (hA3 : NoPrematureTheft R stolenAt) {n s : Nat} (h : theftSched n (fun t => t / R) (stolenOf stolenAt) s) : ∃ j r, s / R ≤ j ∧ stolenAt (producerForSlot n s) j r ∧ s < r + R` -- proof: `obtain ⟨j, hj, r, hr⟩ := h; refine ⟨j, r, hj, hr, ?_⟩; have h1 := hA3 _ _ _ hr; have h1' : R * j ≤ r := by rw [Nat.mul_comm]; exact h1; have hdm : R * (s / R) + s % R = s := Nat.div_add_mod s R; have hmod : s % R < R := Nat.mod_lt _ hR; have hmul : R * (s / R) ≤ R * j := Nat.mul_le_mul_left R hj; omega`.
- L149-151 `noncomputable def recentTheftProducers (n R : Nat) (stolenAt : Nat → Nat → Nat → Prop) (u : Nat) : Finset Nat := (Finset.range n).filter (fun i => ∃ j r, u / R ≤ j ∧ stolenAt i j r ∧ u < r + R)`. Docstring L137-148: "Note the conjunct `u < r + R` is *redundant under* `NoPrematureTheft` ... under A3 this census coincides extensionally with the pure generation-floor census `∃ j ≥ u / R, stolenOf stolenAt i j`".
- L156-160 `theorem exposedSched_subset_recentTheft {n R : Nat} (hn : 0 < n) (hR : 0 < R) {stolenAt} (hA3 : NoPrematureTheft R stolenAt) (u : Nat) : exposedProducersSched n (fun s => s / R) (stolenOf stolenAt) u ⊆ recentTheftProducers n R stolenAt u`.
- L230-231 `def NoPrematureMint (R : Nat) (log : TimedLog) : Prop := ∀ r, ∀ B ∈ log r, B.keyIndex * R ≤ r` (docstring: "stated as a named hypothesis exactly as `NoBackdate` is in the static model").
- L244-260:
  ```lean
  theorem sched_forwardstamp_bounded {R : Nat} (hR : 0 < R) {log : TimedLog}
      (hMint : NoPrematureMint R log)
      {c : Chain} (hPin : schedPinned (fun s => s / R) c = true)
      {B : Block} (hB : B ∈ c) {r : Nat} (hr : B ∈ log r) :
      B.slot < r + R
  ```
  Proof: `rw [schedPinned, List.all_eq_true] at hPin; have hp := hPin B hB; rw [decide_eq_true_eq] at hp; have hm := hMint r B hr; have hm' : R * B.keyIndex ≤ r := by rw [Nat.mul_comm]; exact hm; have hdm : R * (B.slot / R) + B.slot % R = B.slot := Nat.div_add_mod _ _; have hmod : B.slot % R < R := Nat.mod_lt _ hR; have hmul : R * (B.slot / R) ≤ R * B.keyIndex := Nat.mul_le_mul_left R hp; omega`.
- L267-274 `theorem sched_recent_block_fresh {R} (hR : 0 < R) {log} (hMint : NoPrematureMint R log) {c} (hPin : schedPinned (fun s => s / R) c = true) {B} (hB : B ∈ c) {r} (hr : B ∈ log r) {now Δ : Nat} (hRecent : now ≤ B.slot + Δ) : now < r + Δ + R` (`have := sched_forwardstamp_bounded hR hMint hPin hB hr; omega`).
- L284-297:
  ```lean
  theorem sched_backdate_consistent (R r : Nat) :
      ∃ (log : TimedLog) (B : Block),
        NoPrematureMint R log ∧ B ∈ log r ∧ B.slot = 0 ∧
        schedPinned (fun s => s / R) [B] = true
  ```
  Proof: `classical; refine ⟨fun _ => {(⟨0, 0, none, 0, 0, 0⟩ : Block)}, ⟨0, 0, none, 0, 0, 0⟩, ?_, ?_, rfl, ?_⟩` with `Finset.mem_singleton`, `simp`, `simp [schedPinned, Nat.zero_div]`. Docstring L276-283: "**The back-dating half is genuinely not derived** — the scheduled mirror of `noBackdate_independent` ... For *every* real slot `r` (arbitrarily late) there is an execution in which `NoPrematureMint` holds and a schedule-pinned block stamped `0` is minted at `r`".
- L312-324:
  ```lean
  structure PackageATimed (n R H : Nat) {Sig sk pk : Type}
      (ops : SigOps Sig sk pk) (registry : KeyRegistry pk)
      (rented : ByzantineSlots) (stolenAt : Nat → Nat → Nat → Prop)
      (honestSigned : Nat → Nat → Option Block)
      (now Δ : Nat) (G : Block) (Rrent T : Nat) : Prop where
    unforgeable : SchedCoreUnforgeable n (fun s => s / R) ops registry rented
        (stolenOf stolenAt) honestSigned now Δ
    hashInj : SignedHashInjective (SignedDeclared n ops registry) G
    notBefore : NoPrematureTheft R stolenAt
    rentBound : ∀ u, H ≤ u → (badSlotsIn rented u n).card ≤ Rrent
    recentTheftBound : ∀ u, H ≤ u → (recentTheftProducers n R stolenAt u).card ≤ T
    budget_le : Rrent + T ≤ maxByzantine n
  ```
- L326-330 `theorem packageATimed_horizon_budget {n R H : Nat} (hn : 0 < n) (hR : 0 < R) {Sig sk pk} {ops} {registry} {rented} {stolenAt} {honestSigned} {now Δ} {G} {Rrent T} …`.
- L383-390 `structure PackageBTimed (n R H : Nat) {Sig sk pk} (ops) (registry) (rented) (stolenAt) (honestSigned) (now Δ : Nat) (G : Block) (Rrent T : Nat) extends PackageATimed n R H ops registry rented stolenAt honestSigned now Δ G Rrent T : Prop where notAfter : ErasureTimed R stolenAt`.
- L394-421 `theorem packageBTimed_recent_tip_ancestor_agreement {n R H : Nat} (hn : 1 ≤ n) (hR : 0 < R) … (hPB : PackageBTimed …) {sc sc' : SignedChain Sig} (hVal : validSignedChainSched n (fun s => s / R) ops registry sc = true) (hVal' …) {sTip sTip' : Block} (hTipS : (stripSigs sc).getLast? = some sTip) (hTipS' …) (hRecent : now ≤ sTip.slot + Δ) (hRecent' …) (hLong : n < (stripSigs sc).length) (hLong' …) (hH : H + n ≤ sTip.slot + 1) (hH' …) (hTipHeight : sTip.height = sTip'.height) {B B' : Block} (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - n) = some B) (hB' …) : B = B' := packageATimed_recent_tip_ancestor_agreement hn hR hPB.toPackageATimed hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hH hH' hTipHeight hB hB'`. File ends `end MoltPetit.Model` at L423.

#### `MoltPetit/Model/KeyStealingLockstep.lean`

- L103-106 `def validSignedChainLock {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool := sigsOk n ops registry sc && validChainK n (stripSigs sc) && lockstepOk n (stripSigs sc)` ("No schedule parameter — nothing here references `rosterGen`").
- L112-113 `def lagSched (n : Nat) (rosterGen : Nat → Nat) (s : Nat) : Nat := rosterGen (s / n - 1)`.
- L154-165 `theorem schedCore0_of_lock {σ sk pk} {n} {ops} {registry} {sc} (h : validSignedChainLock n ops registry sc = true) : validSignedChainSchedCore n (fun _ => 0) ops registry sc = true` (proof drops keyMonoOk/lockstepOk; `rw [schedPinned, List.all_eq_true]; intro b _; exact decide_eq_true_eq.mpr (Nat.zero_le _)`).
- L252-265:
  ```lean
  structure LockstepPackage (n : Nat) (rosterGen : Nat → Nat) {Sig sk pk : Type}
      (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (rented : ByzantineSlots)
      (Stolen : Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block)
      (now Δ : Nat) (G : Block) (R T : Nat) : Prop where
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
- L269-283 `theorem LockstepPackage.toPackageA … (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T) : PackageA n (lagSched n rosterGen) ops registry rented Stolen honestSigned now Δ G R T where unforgeable := schedCoreUnforgeable_mono (fun _ => Nat.zero_le _) hP.unforgeable; hashInj := hP.hashInj; rentBound := hP.rentBound; exposedBound := hP.exposedBound; budget_le := hP.budget_le`.
- L299-300 `theorem lockstep_declares_rosterGen {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat} …` (docstring L286-298: census argument; "The `≥ lagSched` side condition the exposure census needs is supplied by the induction hypothesis one window down").

#### `MoltPetit/Model/KeyStealingCert.lean`

- L234-237 `def SignedDeclared {Sig sk pk : Type} (n : Nat) (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (B : Block) : Prop := ∃ sig : Sig, ops.verify (registry (producerForSlot n B.slot) B.keyIndex) B sig = true`.
- L239-243 `theorem keyStealingSigned_of_declared … (h : SignedDeclared n ops registry B) : KeyStealingSigned n ops registry B := by obtain ⟨sig, hsig⟩ := h; exact ⟨sig, B.keyIndex, hsig⟩` -- so `KeyStealingSigned n ops registry B` unfolds to `∃ sig j, ops.verify (registry (producerForSlot n B.slot) j) B sig = true`.

#### `MoltPetit/Model/KeyStealingHorizonCore.lean`

- L183-196:
  ```lean
  theorem honestSlotsUnique_keyrot_horizon
      {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
      {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
      {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
      {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
      (hUnf : VersionedUnforgeable n Δconf ops registry rented Stolen honestSigned now Δ)
      {sc sc' : SignedChain Sig}
      (hBudget : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc)))
      (hId : IdInjective (chainUnionRecord sc sc'))
      (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
      (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
      (hRecent  : ∃ t,  (stripSigs sc ).getLast? = some t ∧ now ≤ t.slot + Δ)
      (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ) :
      HonestSlotsUnique (badKeyrotOn n Δconf rented Stolen (stripSigs sc))
        (chainUnionRecord sc sc')
  ```
  Proof opens `have hVc : ValidChain n (stripSigs sc) := by rw [validSignedChainK', Bool.and_eq_true] at hVal; exact (validChainK'_sound hVal.2).1`.

#### `Molt/Results.lean` L128-150 (namespace Molt)

`alias forged_chain_time_bound := MoltPetit.Model.forged_chain_time_bound`; `alias forged_suffix_lag := …`; `alias sigUnforgeableRecent_of_timed := MoltPetit.Model.sigUnforgeableRecent_of_timed` (docstring: "Assumption 2(c) derived in the timed model from plain EUF-CMA plus the no-back-dating residue (paper §6.2 and the appendix)"); L140 `abbrev NoBackdate := MoltPetit.Model.NoBackdate`; L143 `noncomputable abbrev projectSigned := MoltPetit.Model.projectSigned`; `alias noBackdate_independent := MoltPetit.Model.noBackdate_independent`; `end Molt`.

#### `Molt/Rotation.lean` L104-135

`abbrev KeyStealingEUFCMA := @MoltPetit.Model.KeyStealingEUFCMA`; `abbrev KeyStealingSigned := @MoltPetit.Model.KeyStealingSigned`; `def schedPin (schedule : Nat → Nat) (c : Chain) : Bool := c.all (fun b => decide (schedule b.slot ≤ b.keyIndex))`; `def validSignedChainSched … := sigsOk n ops registry sc && validChainK n (stripSigs sc) && schedPin schedule (stripSigs sc)`; `abbrev SchedUnforgeable := @MoltPetit.Model.SchedUnforgeable`; `abbrev badSched := @MoltPetit.Model.badSched`. (Prop-structures and predicates are re-exported via `abbrev X := @MoltPetit.Model.X`; Bool validators are re-declared fresh and bridged.)

#### Build / registration / audit idioms

- `MoltPetit.lean` (lib root) imports, in order: TS.Emitted, Model.Definitions, Model.Model, Model.Safety, Model.Soundness, Model.Liveness, TS.Bridge, Model.Grounded, Model.Timed, Results.Results, TS.Results, Model.TimedSig, Model.KeyIndex, Model.KeyRotation, Model.KeyStealing, Model.KeyStealingSafety, Model.KeyStealingUnique, Results.KeyStealingResults, Model.KeyStealingCert, Model.KeyRotationLiveness, Model.KeyStealingBudget, Model.KeyStealingLongRange, TS.BridgeK, Model.KeyStealingSchedule, Results.KeyStealingScheduleResults, Model.KeyStealingScheduleCert, Model.KeyStealingScheduleBudget, Model.KeyStealingScheduleHorizon, Model.KeyStealingLockstep, Model.KeyStealingHorizonCore, Model.KeyStealingHorizon, Model.KeyStealingScheduleTimed, Model.KeyRotationTests, Results.Axioms, Custody.
- `Molt.lean` imports: Molt.Protocol, Molt.Verifier, Molt.Assumptions, Molt.Results, Molt.Rotation, Molt.ClientRule, Molt.MaxSync, Molt.Liveness, Molt.Axioms.
- `MoltPetit/Results/Axioms.lean` header imports 25 modules (Results.Results … Model.KeyStealingScheduleTimed); docstring: guards make the build fail if a theorem "ever comes to depend on anything beyond the three classical axioms `propext`, `Classical.choice`, `Quot.sound`". Guards at L93-98:
  ```
  /-- info: 'MoltPetit.Model.sigUnforgeableRecent_of_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
  #guard_msgs in
  #print axioms MoltPetit.Model.sigUnforgeableRecent_of_timed
  /-- info: 'MoltPetit.Model.noBackdate_independent' depends on axioms: [propext, Quot.sound] -/
  #guard_msgs in
  #print axioms MoltPetit.Model.noBackdate_independent
  ```
  `Molt/Axioms.lean` L147-153 guards `Molt.sigUnforgeableRecent_of_timed` and `Molt.noBackdate_independent` identically. Axioms.lean tail (last 30 lines): guards for `lockstep_validSignedChainSched`, `lockstep_recent_tip_ancestor_agreement`, `lockstep_recent_tip_ancestor_mem`, then "The anchored horizon" block guarding `honestSlotsUnique_keyrot_anchored`, `keyrot_recent_tip_ancestor_agreement_anchored` (its info string is WRAPPED across three lines: `[propext,\n Classical.choice,\n Quot.sound]`), `keyrot_recent_tip_ancestor_mem_anchored`. Axioms.lean L490-493 comment mentions `PackageATimed`.
- `lakefile.toml`: `name = "MoltPetit"`, `defaultTargets = ["MoltPetit", "Rust", "Thales", "Molt"]`; `[leanOptions] pp.unicode.fun = true, relaxedAutoImplicit = false, weak.linter.mathlibStandardSet = true, maxSynthPendingDepth = 3`; mathlib `v4.30.0-rc2`; aeneas backend rev `bf13c42e7c34d07fc396baffad39c93023b12914` subDir `backends/lean`; `[[lean_lib]]` MoltPetit, Rust, Thales, Molt (no `globs`); `[[lean_exe]] moltpetit-demo root = "Main"`.
- `MoltPetit/Model/KeyRotationTests.lean` imports `MoltPetit.Model.KeyRotation`; `#guard`-based executable regression tests (`rot_accepted`, `inforce_rises`) encoding the intended operational model.

### 2B. From design docs, memory and the paper, read directly

- **Owner decision (recorded, binding):** `memory/key-rotation-mission.md:15-29`: "**DECISIVE CLARIFICATION (overrides the committed design note `KEY_ROTATION_SOUND.md` v2):** George **rejected** the forward-secure / `NoBackdate` framing. The correct model: a stolen key `dk(i,j)` signs **anything, at any slot, forever** — NO forward security, NO `NoBackdate`. The defense is moved entirely onto the **validator-enforced index pin** (`validChainK'`) **+ recency**, not the signature scheme. `HonestSlotsUnique` is re-derived directly from the pin: the corruption is a chain-independent slot predicate `badKeyrot s := rented s ∨ Stolen(producerForSlot n s, inForceIdx(producerForSlot n s, s))` where `inForceIdx` reads the in-force index off the **finalized** prefix ... so a back-dating witness always lands on a by-definition-bad slot, never an honest one. Old keys (`j` no longer in force) only pin-validate OLD slots ⇒ long-range forks, defeated by the recency anchor `H-ANCHOR` ... KEEP `H-IND` ... and `H-ANCHOR`; keep `Δ = n` and `Δconf ∈ [n,2n]` separate."
- `memory/key-rotation-mission.md:288-293` (DIRECTION GOTCHA): "NoBackdate is the TWO-SIDED stamp=mint pin; noBackdate_independent's witness is a BACK-DATED block. The schedule derives only the FORWARD half (stamp < mint + R); the back-dating half (late minting of old stamps with a live stolen key) is NOT derived — sched_backdate_consistent machine-checks its consistency — and is what the budget charges. Frame as "the forward half of the NoBackdate pin"." `:294-296` RESIDUAL: "the recent-theft census is future-inclusive (badSched consumes timeless stolenOf; under A3 the census is extensionally the timeless generation-floor census)."
- `memory/key-rotation-mission.md:450-455` (CRYPTO-PRECISION GOTCHAS): "NoBackdate is TWO-SIDED — forward security supplies only the back-dating half (period-locked oracle = forward half; KES = both); (2b) is MULTI-KEY EUF-CMA with bad slots as the oracle; clock is the ONE assumption with no Lean counterpart (say "all but one")". `memory/paper-editing-playbook.md:77`: ""Forward security supplies the back-dating half" — correct". `memory/annotations-2026-07-work-order.md:399-414` (E22): under `NoBackdate` the bad-slot/honest-stamp answer is **no**, definitionally; "forward-security direction text (:2477–2485) is CORRECT — do not "fix" it."
- `KEY_ROTATION_SOUND.md:24-36`: "The crypto trust surface is reduced to a single transparent primitive: `KeyStealingEUFCMA` (recency-scoped registry EUF-CMA, no forward security), from which the index pin is **proven** (`rotated_key_dead` → `versionedUnforgeable_of_keyStealingEUFCMA`) ... Boundary of trust, stated honestly: `KeyStealingEUFCMA` is *assumed*, not reduced to the timed model (the strong adversary refuses `NoBackdate`, so the classical `sigUnforgeableRecent_of_timed` route is unavailable by design)."
- `KEY_ROTATION_SOUND.md:78-90` ("What changed in v3"): v2 used `H-FS`/`NoBackdate`; "**George rejected that framing.** ... `dk(i,j)` signs **anything, at any slot, forever** — no forward security, no `NoBackdate`. ... Net effect: **fewer assumptions** (no FS crypto), more proof work in Phase 2".
- `KEY_ROTATION_SOUND.md:168-176` (v3 re-derivation, replaces v2's `NoBackdate` reuse `[P9]`): "we can **no longer** borrow `TimedSig.lean:sigUnforgeableRecent_of_timed` (it needs `NoBackdate`, which we now refuse to assume). Instead `HonestSlotsUnique` is re-proved **directly from the index pin** over the right `bad` (§2.1)".
- `KEY_ROTATION_SOUND.md:180-217` (§2 "The adversary, granted in full `[B4][P10]`"): extend `TimedExecution` (`Definitions.lean:719`); "Its real residue invariant is **`key_match`** (`:724`) ... We **preserve `key_match`** (the whole forged-time count rests on it)." Rent unchanged; **Steal**: "holding `dk(i,j)` lets the adversary, **at any real slot `r ≡ i (mod n)`, mint one block per real slot** stamped at **any** slot of `i` and **declaring any `keyIndex`** the forged signature verifies for ... That real slot `r` is marked **bad**." "There is **no** `H-FS` bound on which slot the key signs". `keyStealing_refines_timed` witnesses the strict superset. Well-founded order `[P10]`: "each stolen use consumes a distinct real slot (`key_match` + one-block-per-real-slot), the first-signing-slot measure (`sigTime`, `Timed.lean`) is preserved and `chain_order` (`:732`) still forces a back-dated block's parent to be `AvailableAt` its (late) signing slot."
- `KEY_ROTATION_SOUND.md:791-794, 815-818` (grep hits): the forward half of the `NoBackdate` pin is DERIVED in the schedule module; the back-dating half is NOT derived (`sched_backdate_consistent`).
- `HANDOFF_SCHEDULE_VARIANT.md:174-175`: "delegate key `dk(i,j)` signs anything, any slot, FOREVER — NO forward security, NO `NoBackdate`. Defense = the validator's **index pin** + **recency**".
- `ROTATION_MODES.md` §5 "Not yet modeled" table (L223-232): X-1 composed emergency floor (modes 2,3); X-2 per-generation census D1′-full (3); **X-3 "Mint times in the EUF-CMA surface: theft-before-mint instead of theft-ever." (modes 1, 2, 3)**; X-4 lockstep certificate wrapper (3). `:148-150` (mode-2 guarantees): "(theft-ever, not theft-before-mint); the horizon form (M2-G3) confines it to ... theft-before-mint — 📐 design-level, the natural next increment." Operator duties: M1-O1..O4 (M1-O2 healing via `badKeyrotOn` `Model/KeyStealing.lean:47`; M1-O3 H-IND; M1-O4 key-leak horizon), M2-O1..O4 (M2-O1 cold root A0; M2-O2 not-before A3 "a `PackageA` field"; M2-O3 no erasure required, `sched_oldkey_fork_stale` at `Results/KeyStealingScheduleResults.lean:242`; M2-O4 size T to era length), M3-O1..O3 (M3-O1 lockstep B1 = `LockstepPackage` fields `declared`, `genesis_gen`, `mono`; M3-O2 erasure B2; M3-O3 B3 = A3, B0 = A0). Client profiles M1-C1 (rolling anchor H-ANCHOR) / M1-C2, M2-C1 (schedule constant `gen`, no anchor, no Δconf), M3-C1 (S-C1 only). Section headings: 0 Shared base; 1 Mode 1; 2 Mode 2; 3 Mode 3; 4 comparison; 5 Not yet modeled.
- `paper/molt.tex` (HEAD 8b8b766): assumption environments at L493 `[Fault budget] ass:budget`, L503 `[Signatures] ass:sig`, L537 `[Hash collision resistance…]`, L559 `[Certificate grounding] ass:cert`, L570 `[Clock] ass:clock`, L580 `[Honest delivery — liveness only] ass:delivery`. L526: "Section sec:timed shows that (c) is derived, not …". L658 `\label{sec:timed}`. L722-729: "This is also why Assumption ass:sig(c) is derived rather than primitive: in the timed model it follows from plain EUF-CMA plus a \emph{no-back-dating} residue --- a signature bearing an honest slot's stamp was produced at that slot exactly, never stockpiled earlier and never minted later (\code{sigUnforgeableRecent\_of\_timed}; Appendix app:timed-uniq gives the derivation, the residue's exact content, and its machine-checked independence)." L731 `\label{sec:rotation}` (pin: "a floor in modes 1--2, exact per grid window in mode 3"). L1385-1408 "Named seams": "the key-stealing signature surface (assumed, not derived from the timed model); version independence of keys under theft (instantiable with key-insulated signatures); ... the recency check itself, which lives in the unverified node loop since the pure validators carry no clock; and the per-mode operational assumptions of Section sec:rotation (not-before and cold-root custody; lockstep coordination and erasure)." L1410-1421 "The long-range residual, and options against it": three options -- forward-secure signatures (stateful signer); monotone once-corrupt-always-corrupt accounting; running modes 2--3. L1438-1500 Appendix `app:timed-uniq` "The honest-slot uniqueness assumption, derived": projection `projectSigned`; two hypotheses (EUF-CMA bridge; no back-dating); Theorem `thm:timed-uniq` (Lean `sigUnforgeableRecent_of_timed`); "recency is not even consumed"; "What no-back-dating is, and why it is not free": "an honest producer's slot-$s$ signature can only be its genuine slot-$s$ call, \emph{and no bad slot of the same producer may mint a block bearing that honest stamp}. The constraint is on the \emph{stamp}, not on the signer"; `noBackdate_independent` at n = 2; "this stamp-to-slot binding is two-sided: forward security proper supplies the back-dating half (an evolved key cannot sign earlier periods), while the forward half --- no pre-signing of future honest stamps --- rests on the signing path's period being locked to real slots; a key-evolving scheme under a one-period-per-slot schedule, honestly updated, provides both halves --- provided a bad slot yields signatures but never the key itself".
- `/etheron-pod/rollout-work/maps/design-docs.md` does NOT exist (grep error at line 73).
- Sibling designs: `W3a.md` and `W5.md` are both near-empty salvages (each subagent killed within seconds after one shell command; no Lean facts, no design). W3a intended to mirror `KeyStealingScheduleTimed.lean` for a mode-1 timed theft layer deriving the trailing (anchored) budget; W5 intended to start from `KeyStealingLockstep.lean` and `LOCKSTEP_DESIGN.md:135-200`.

### 2C. From the reader digests (maps) -- items most relevant to W6

(Full digests remain on disk under `/etheron-pod/rollout-work/maps/`; only W6-relevant items are reproduced.)

From `timed-core-liveness.md`:
- `Timed.lean` (namespace MoltPetit.Model, imports Grounded): one def `belowCount` (254); theorems `block_signed` (47; needs NO TimedExecution; index k ≥ 1 essential; needs `hGprev : G.prev = none`, ParentLinked, hAvail), `sigTime_mono_step` (67; uses `hexec.chain_order` + `hexec.id_inj`; first-signing time is `Nat.find (h : ∃ r, B ∈ log r)`), `sigTime_mono_chain` (87), `one_real_slot_one_block` (136; hypotheses hn, hexec, hGprev, hValid, hAvail, hk, hkk, hB, hB', hBr, hBmin, hB'r, hB'min ⊢ False; uses `hexec.key_match`, MaturedWindowsDense, `2 ≤ quorum n`, StrictSlots; minimality phrased `∀ r' < r, B ∉ log r'`), `belowCount_*` (257-320), `le_div_succ_mul` (342), `bad_budget_Ico` (355, `open Classical in`).
- `Results/Results.lean`: `forged_suffix_time_bound` (102; hn, hexec, hBudget, hValid, hGprev, hAvail, hk₀, hF, hFr, hFmin, hForged, hTip ⊢ `quorum n * ((tip.slot - F.slot) / n) ≤ maxByzantine n * ((R - r₀) / n + 1)`; budget over REAL slots, density over c's own matured windows), `forged_suffix_lag` (231), `forged_chain_time_bound` (285), `forged_chain_lag` (386). Results.lean imports Grounded + Timed, NOT TimedSig.
- IMPORT GRAPH: "a new core module wanting TimedExecution + liveness + forged bounds + NoBackdate should `import MoltPetit.Results.Results` and `import MoltPetit.Model.TimedSig`; a new Molt-side module should `import Molt.Results`".
- BUILD REGISTRATION GOTCHA: no `globs` in lakefile, so a purely additive file must be built explicitly (`lake build MoltPetit.Model.<New>`) and is not covered by the existing axiom audit; replicate `#guard_msgs in #print axioms` locally. `relaxedAutoImplicit = false` (bind every variable).
- BAD-SLOT READINGS: "TimedExecution applies `bad` to REAL slots r (honest_stamp/honest_once, and hForged in the forged bounds quantify `bad r` over signing slots); NoBackdate, SigUnforgeableRecent.verified_was_signed, HonestBlocksCover, HonestSlotsUnique apply `bad` to the STAMP B.slot / record slot s; ByzantineBounded n bad is one budget used for both readings. They coincide only under NoBackdate/honest_stamp. A new module mixing timed and stamped statements must pick one `bad` and prove the crossover explicitly."
- SIGNED PREDICATE: "`sigUnforgeableRecent_of_timed` takes an abstract `Signed : Block → Prop` plus the EUF-CMA bridge `hbridge : Signed B → ∃ r, B ∈ log r` (this bridge is the only place the crypto enters; nothing in the repo proves it for TSSigned) ... The result ... is for `signed := projectSigned n log` (noncomputable, Classical.choose; canonical only at honest real slots) and holds for every now and Δ — the recency scoping is slack there."
- open_items: TimedSig.lean:30-36 (operational justification only, no formal model of forward-secure signatures); TimedSig.lean:74-77 (recency→pinning route explicitly NOT a theorem); TimedSig.lean:83 (hbridge undischarged for TSSigned).

From `mode2-horizon-timed.md`:
- `KeyStealingScheduleHorizon.lean`: `ByzantineBoundedFrom` (70), `byzantineBoundedFrom_of_bounded` (75), `horizon_shared_prefix` (161; validator-agnostic; budget at the single window `u = tip.slot + 1 - n` of the LOWER-tipped chain), `sched_recent_tip_ancestor_agreement_horizon` (247) / `_mem_horizon` (308) / `_genesis_agreement_horizon` (365) / `_core` twins (414, 471). Private (non-importable) `exists_honest_shared_slot_at` (86; also HorizonCore:58) and `slot_gap_of_position_gap` (116).
- `KeyStealingScheduleTimed.lean` theorem table (lines as in 2A) plus `packageATimed_recent_tip_ancestor_agreement` (344; = `sched_recent_tip_ancestor_agreement_horizon hn (schedUnforgeable_of_core hA.unforgeable) hA.hashInj (packageATimed_horizon_budget (by omega) hR hA) …`).
- `KeyStealingHorizonCore.lean`: `sigma_shared_prefix` (91), `confirmed_mem_iff_horizon` (151; n ≤ Δconf, no genesis), `honestSlotsUnique_keyrot_horizon` (183), `honestSlotsUnique_keyrot_anchored` (258; budget shape `∀ u, A.slot + 1 ≤ u + n → …`). `KeyStealingHorizon.lean`: `keyrot_recent_tip_ancestor_agreement_horizon` (69), `_anchored` (134; wrapped by `Molt.client_refresh_rule` Molt/Rotation.lean:267), `_mem_anchored` (222), `_horizon_of_valid` (310).
- NAMESPACE/FILE IDIOMS: single `namespace MoltPetit.Model … end MoltPetit.Model`; long `/-! # MoltPetit — … -/` module doc with an explicit "Honest scope" section; `-- ====` banners; `open Classical` after the namespace where Finset filters over Prop; any def filtering on a Prop must be `noncomputable`. New modules must be added to `MoltPetit.lean` and guarded in `Results/Axioms.lean` (or locally). Long theorem names wrap the axiom list -- copy the wrapped form or use `#guard_msgs (whitespace := lax) in`. Tactics: `omega`; `push Not at h` (not `push_neg`); `rcases Nat.le_total … with hle | hle`.
- HOW THE TIMED LAYER DERIVES THE HORIZON BUDGET: `badSched_iff_or` (Iff.rfl) → `badSlotsIn_union_le` (KeyStealingBudget.lean:52) → `theftSlotsSched_card_le_exposed` (ScheduleBudget:148) → `exposedSched_subset_recentTheft` (timed novelty, via `theft_is_recent`) → rate hypotheses guarded by `H ≤ u` + `hRT` → `ByzantineBoundedFrom H n (badSched n (fun s => s / R) rented (stolenOf stolenAt))`, applied as `hBudget _ (by omega)` at `u = sTip.slot + 1 − n` using `hH : H + n ≤ sTip.slot + 1`.
- WHAT DOES / DOES NOT TRANSPORT TO MODE 1: `ByzantineBoundedFrom` does NOT transport (badKeyrotOn is chain-relative, keyed to `stripSigs sc`, the FIRST chain; the slot-induction consults windows all the way down); the mode-1 substitute is the ANCHORED budget; "the mode-1 theft floor is inForce (chain-local, Δconf-lagged), so a theft_is_recent analogue needs a relation between inForce and real time that does not exist yet." Gate in every mode-1 horizon theorem is `hΔ : n ≤ Δconf`.
- MODE 3 COMPOSITION POINTS: `KeyStealingLockstep.lean` imports ScheduleBudget + Results.KeyStealingScheduleResults, NOT the horizon/timed files -- a mode-3 timed module can import both Lockstep and ScheduleTimed without cycles. `lockstep_validSignedChainSched` (474) CONSUMES `hHead : blockAt? (stripSigs sc) 0 = some G` and hRecent (∃-form). "The mode-3 theft floor is lagSched (not s / R): a mode-3 theft_is_recent analogue needs a real-time provisioning hypothesis phrased against rosterGen windows (e.g. stolenAt i j r → j is ≤ rosterGen of some window ≤ r / n), and recentTheftProducers's `u / R ≤ j` becomes `lagSched n rosterGen u ≤ j`."
- GOTCHAS (1)-(10), notably: (3) Signed predicate differs by mode: sched uses `SignedDeclared` with `SignedHashInjective (SignedDeclared n ops registry) G`; mode 1 uses `KeyStealingSigned` (∃ j) via `keyStealingSigned_of_mem` from `validSignedChainK'`; (4) `horizon_budget_of_timed` takes `hn : 0 < n`, headlines take `hn : 1 ≤ n`; (5) `theft_is_recent` / `exposedSched_subset_recentTheft` / `horizon_budget_of_timed` are stated at the literal lambda `fun s => s / R` (`theftSched`'s binder appears as `fun t => t / R`, defeq); generalising needs a schedule-to-real-time hypothesis; (6) hRecent in `honestSlotsUnique_*` is the ∃-form; (9) `PackageBTimed.notAfter` and `PackageB.erasure_freeze` are consumed by no proof.
- open_items: ScheduleTimed.lean:58-71 (census future-inclusive; `SchedTimedUnforgeable` keyed on theft-before-mint is "the natural next increment, not attempted here"); :72-76 (A3/B3/B2 not further reduced; EUF-CMA surface + hash injectivity still assumed); :39-44 (back-dating half not derived); Molt has NO re-presentation of `ByzantineBoundedFrom`, `stolenOf`, `NoPrematureTheft`, `recentTheftProducers`, `PackageATimed`, or the timed theorems.

From `mode1-chain.md`:
- `KeyStealingEUFCMA` (KeyStealingUnique.lean:136) "ONE field, `unforgeable`, with 6 premises ... No inForce baked in; no forward security (Stolen not time-indexed)." `VersionedUnforgeable` (161) "Derived from KeyStealingEUFCMA, never assumed independently. Consumed by honestSlotsUnique_keyrot / _horizon / _anchored."
- `KeyStealingExecution` (KeyStealing.lean:101): "Only consumer in repo: keyStealing_refines_timed."
- `KeyStealingBudget.lean`: `theftOn` (42), `badKeyrotOn_iff_or` (45, Iff.rfl), `badSlotsIn_union_le` (52), `exposedProducers` (62, noncomputable), `theftSlots_card_le_exposed` (92), `induced_byzantine_bounded` (107; c₀ arbitrary witness chain, instantiate `c₀ := stripSigs sc`), private `window_producer_inj` (69).
- `Results/KeyStealingResults.lean`: `KeyStealingSigned` (158), `keyStealingSigned_of_mem` (169), `keyrot_deep_block_agreement` (204), `keyrot_recent_tip_ancestor_agreement` (328; needs hHead/hHead'), `_mem` (393), loss-only forms (483, 518; idiom `rw [badKeyrotOn_lossOnly]; exact hBudget`).
- `Molt/ClientRule.lean`: `stay_recent_client_safe` (174; trailing < 5n windows budget), `sync_rule` (238; Δconf := n), `sync_rule_mem` (284). `Molt/MaxSync.lean`: `inForce_mono` (79), census lemmas, `max_sync_period`.

From `mode3-lockstep.md`:
- `LockstepPackage.mono` and `hashInj` are NOT consumed by the pinning theorem or the transport; `mono` is consumed by nothing in the module. Private helpers `lockstep_rel` (172), `lockstep_const` (195), `head_slot_min` (211), `window_producer_inj'` (220) are not importable.
- "The surface is assumed at the constant-0 schedule and is monotone in the schedule (`schedCoreUnforgeable_mono`, :141); do not try to state a lockstep-scoped surface (circular, audit obstruction 3)." `schedCore0_of_lock` (154) is the validity argument to feed `hP.unforgeable.unforgeable` on a lockstep chain.
- `LOCKSTEP_DESIGN.md:173-178` (Net): "The timed layer does not transport at all." `ROTATION_MODES.md:228-230`: X-2 and X-4 for mode 3.

---

## 3. Design direction

**None was stated.** The subagent produced no definitions, theorem statements, proof sketches, file plans, dependency notes or effort estimates. Its only prose:

1. Line 5: "I'll start by reading the primary digests for this item."
2. Line 9: "Next I need the four primary digests plus the existing sibling designs (W3a, W5) since W6 must share a timed structure with them. All are independent, so I'll fetch them together."

Statement 2 is the only design-relevant assertion it made: **W6 must share a timed structure with W3a (mode-1 timed theft layer) and W5 (mode-3 per-generation census).**

**Evident thread of investigation (INFERRED from the subagent's own tool-call descriptions, in order; not a stated plan):**

1. Establish the static-model derivation it would be generalising: read `TimedSig.lean` in full (`projectSigned`, `NoBackdate`, `sigUnforgeableRecent_of_timed`, `noBackdate_independent`) and the `Definitions.lean` signing-model region (`SigUnforgeableRecent`, `TimedLog`, `SignedEver`, `AvailableAt`, `TimedExecution`, `SigningLog`, `HonestSlotsUnique`, `ByzantineSlots`).
2. Establish the three per-mode EUF-CMA surfaces that a "rescoped surface from a timed model" would have to target: mode 1 `KeyStealingEUFCMA` / `VersionedUnforgeable` (+ `rotated_key_dead`), mode 2 `SchedUnforgeable` / `SchedCoreUnforgeable` (+ `rotated_key_dead_sched` / `_schedCore`, `schedUnforgeable_of_core`, `honestSlotsUnique_sched` / `_schedCore` proofs), mode 3 `LockstepPackage.unforgeable` at the constant-0 schedule (+ `schedCore0_of_lock`, `lagSched`, `toPackageA`).
3. Establish the existing timed-side objects per mode: mode 1 `KeyStealingExecution` (`toTimed`, `steal_bad`, abstract `StolenMint`) and `timedExecution_of_bad_iff`; mode 2 `KeyStealingScheduleTimed` (`stolenOf`, `NoPrematureTheft`, `ErasureTimed`, `NoPrematureMint`, `theft_is_recent`, `recentTheftProducers`, `sched_forwardstamp_bounded`, `sched_recent_block_fresh`, `sched_backdate_consistent`, `PackageATimed`/`PackageBTimed`); mode 3 none (LOCKSTEP_DESIGN: "The timed layer does not transport at all").
4. Establish the owner's constraint: "Search repo docs and memory for forward-security / back-dating rejection" and "Read owner's rejection of NoBackdate and the v3 re-derivation text" -- i.e. that `NoBackdate`/forward security is REFUSED for the key-stealing adversary and `KeyStealingEUFCMA` is deliberately a named primitive.
5. Establish the paper's framing of the residue (Assumption 2(c) derived; appendix `app:timed-uniq`; "two-sided" pin; long-range residual options) and the assumption environment anchors.
6. Establish the documented open item that names the target: `ROTATION_MODES.md` X-3 "Mint times in the EUF-CMA surface: theft-before-mint instead of theft-ever" (modes 1, 2, 3) and ScheduleTimed's "`SchedTimedUnforgeable` whose conclusion keys on theft-before-mint rather than theft-ever — the natural next increment".
7. Establish build/presentation mechanics: root import lists, axiom-guard idiom and wrapped-info gotcha, `Molt` abbrev/alias idiom, `Block` deriving `DecidableEq`, lakefile options, `KeyRotationTests` `#guard` idiom, `sigOk`/`SignedBlock`/`TSSigned`, `SignedDeclared` vs `KeyStealingSigned`.

What it did NOT get to (so a fresh designer must do it): naming the new module(s); stating per-mode `NoBackdate`-analogue definitions; stating per-mode derived surfaces (theorem shapes); deciding which `bad` reading (real vs stamped) each mode's statement uses and proving the crossover; deciding how `StolenMint`/`stolenAt` bridge to the signed side; effort estimates; dependencies on W3a/W3b/W5.

---

## 4. Decisions and rejected alternatives

**Recorded by the subagent: none.**

Owner/repo decisions the subagent *found* and that constrain W6 (from section 2B, not the subagent's own):

- `NoBackdate` / forward security is REJECTED as an assumption for the key-stealing adversary (memory/key-rotation-mission.md:15-19; KEY_ROTATION_SOUND.md:78-90, 168-176; HANDOFF_SCHEDULE_VARIANT.md:174-175). `KeyStealingEUFCMA` is assumed, not reduced to the timed model (KeyStealingUnique.lean provenance docstring; KEY_ROTATION_SOUND.md:33-35; paper L1400).
- The mode-2 timed layer derives only the FORWARD half of the stamp/mint pin (`sched_forwardstamp_bounded`); the back-dating half is deliberately NOT derived and is shown consistent (`sched_backdate_consistent`); "its per-block exclusion is the assumed EUF-CMA surface's business" (ScheduleTimed.lean:39-44; memory :288-293).
- `KeyStealingScheduleTimed` explicitly declined to re-plumb the EUF-CMA surface with mint times ("not attempted here", :58-71); ROTATION_MODES lists it as X-3 for all three modes.
- Do not state a lockstep-scoped EUF-CMA surface (circular; LOCKSTEP audit obstruction 3) -- mode-3 surface is `SchedCoreUnforgeable n (fun _ => 0)` lifted by `schedCoreUnforgeable_mono`.

---

## 5. Partial structured output

**None.** No `StructuredOutput` call, no `Write`, no JSON drafted in assistant text anywhere in lines 4-91. (Line 80 is unreadable but is a user-role line by its position and the promptId change, so it cannot contain assistant output.)

---

## 6. Open questions

**Raised by the subagent: none** (no prose beyond the two sentences above).

Questions implied by where it stopped (for the next designer; not the subagent's):

- What is in transcript line 80 (a 74K-token user-role message with new promptId `0fe07ea6…`)? If it was a mid-task course correction from the orchestrator, the subagent's subsequent reads (lines 82-88: `Block` deriving, lakefile, paper anchors, `ROTATION_MODES` operator duties, `Molt` abbrev idiom, axiom-file tails, tests header) were shaped by it.
- Given the owner refuses `NoBackdate` for the key-stealing adversary, what exactly is a "no-back-dating derivation per mode" allowed to assume? The repo's precedent is: derive the *forward* half from provisioning (`NoPrematureMint` + pin) and charge the back-dating half to the budget/EUF-CMA surface.
- Which `bad` reading (real slot vs stamp) does each mode's statement use, and how is the crossover proved (digest BAD-SLOT READINGS note)?
- How does the unsigned timed layer (`TimedLog`, `StolenMint : Block → Prop`, `stolenAt`) bridge to the signed surfaces (`ops`/`registry`/`sig`, `honestSigned`)? `KeyStealing.lean` says "connected to this predicate by a separate bridge hypothesis in Phase 3" -- no such bridge exists in the repo (digest: `KeyStealingExecution`'s only consumer is `keyStealing_refines_timed`).
- Mode 1 has no `theft_is_recent` analogue because `inForce` is chain-local with no real-time relation (digest); mode 3's theft floor is `lagSched`, needing a provisioning hypothesis against `rosterGen` windows.
- Dependency on W3a (mode-1 timed theft layer) and W5: the subagent asserted W6 "must share a timed structure with them", but both sibling designs are empty salvages.
