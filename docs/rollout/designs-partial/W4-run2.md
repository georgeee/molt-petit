# Salvage: designer transcript `agent-a907c024cdc0c990c` — work item W4, run 2

| | |
|---|---|
| Agent id | `a907c024cdc0c990c` (workflow run `wf_6b051052-ec7`) |
| Transcript | `/run/claude/agent/projects/-etheron-pod/c28ff38c-0cb1-500d-8726-22cd73943085/subagents/workflows/wf_6b051052-ec7/agent-a907c024cdc0c990c.jsonl` (74 lines) |
| Work item | **W4 — machine-check the induction over syncs (mode 1 client)**, for `/etheron-pod/mini-consensus-lean` (additive-only new modules). Assigned by the orchestrator; consistent with the transcript (its first action was reading the run-1 salvage `W4.md`, and every later read targets the mode-1 sync-rule family and the paper's induction-over-syncs passage). |
| Repo state at the time | `/etheron-pod/mini-consensus-lean` HEAD `8b8b766` ("paper2 p16: appendix -- recency window, no-back-dating scope (AN/33, AN/34)"), `git status --short` empty (clean tree). Branch `feature/key-rotation-sound` per the maps. |
| Lines seen | offsets 4–74 (71 lines), minus offset 55 = **70 lines read**. Offset 74 is the empty trailing line. Offsets 0–3 (prompt + harness attachments) deliberately not read per protocol. |
| Lines skipped for size | **offset 55** (74,053 tokens; refused at limit=3 and limit=1). Context: the `promptId` on tool results changes from `ef278b43-…` (offsets 7–54) to `0fe07ea6-…` (offsets 58–72), and there is a ~5-minute wall-clock gap between offset 54 (`07:11:01Z`) and offset 56 (`07:15:59Z`). Offset 55 is therefore almost certainly a second user-role message injected mid-task (a course correction or a re-sent prompt). Its content is unknown. |
| Where it stopped | **28 tool calls, zero design text.** Timeline: first assistant message `2026-09-05T07:10:13Z`; last tool result (paper passages on checkpoints / max sync period) `07:17:03Z`; offset 73 is the synthetic assistant record `"You've hit your session limit · resets 9am (UTC)"` (HTTP 429, `rateLimitType: five_hour`, `resetsAt: 1788598800`, overage disabled at org level) at `07:17:04Z`. No StructuredOutput call, no drafted JSON, no theorem statements of its own, no file plan, no effort estimate. All thinking blocks in the transcript are empty (redacted signatures only). |

The subagent's only prose, verbatim, in order:

1. offset 5: *"I'll start by reading the salvage file and the primary maps."*
2. offset 11: *"Next I need the four primary map digests. They're independent of each other, so I'll fetch the first halves of all four at once."*
3. offset 21: *"The digests were persisted to scratch files. I'll read them with the in-process Read tool (all four at once, first chunks)."*
4. offset 32: *"I need the tails of two digests, the W2 salvage (for interface alignment), and the paper's own statement of the induction. All independent; requesting together."*
5. offset 40: *"Now I need the paper passages and the Lean sources themselves. All independent; requesting together."*

Everything below in §2 is what those tool calls returned. §3 records the direction only as far as the tool-call trajectory evidences it, explicitly labelled as inference.

---

## 1. Files examined (complete list, in transcript order)

| # | Offset | Tool | Input | Why (from its own text / `description`) |
|---|---|---|---|---|
| 1 | 6 | Read | `/etheron-pod/rollout-work/designs-partial/W4.md` (run-1 salvage of designer `ab9a3fba02babc59e`, 132 lines) | "reading the salvage file" |
| 2 | 8 | Bash | `ls -la /etheron-pod/rollout-work/maps/ /etheron-pod/rollout-work/designs-partial/; cd /etheron-pod/mini-consensus-lean && git log --oneline -1 && git status --short \| head` | "List maps and check repo state" |
| 3 | 12 | Bash | `sed -n 1,400p /etheron-pod/rollout-work/maps/results-molt.md` (persisted: 58.5KB → `tool-results/bp3k30nx7.txt`) | "Read results-molt digest part 1" |
| 4 | 14 | Bash | `sed -n 1,400p /etheron-pod/rollout-work/maps/mode1-chain.md` (34.8KB → `bphyke1q6.txt`) | "Read mode1-chain digest part 1" |
| 5 | 16 | Bash | `sed -n 1,400p /etheron-pod/rollout-work/maps/core-grounded-cert1.md` (43.7KB → `bwz899o6i.txt`) | "Read core-grounded-cert1 digest part 1" |
| 6 | 18 | Bash | `sed -n 1,400p /etheron-pod/rollout-work/maps/timed-core-liveness.md` (32.1KB → `bsadw1v3u.txt`) | "Read timed-core-liveness digest part 1" |
| 7 | 22 | Read | `…/tool-results/bp3k30nx7.txt` (results-molt; got lines 1–266 of 379, truncated) | "read them with the in-process Read tool" |
| 8 | 25 | Read | `…/tool-results/bphyke1q6.txt` (mode1-chain; full, 401 lines) | same |
| 9 | 27 | Read | `…/tool-results/bwz899o6i.txt` (core-grounded-cert1; full) | same |
| 10 | 29 | Read | `…/tool-results/bsadw1v3u.txt` (timed-core-liveness; full, 401 lines) | same |
| 11 | 33 | Read | `bp3k30nx7.txt` offset 267 limit 120 (results-molt tail: `reuse_notes`, `open_items_found`) | "tails of two digests" |
| 12 | 35 | Read | `bphyke1q6.txt` offset 401 limit 200 → empty (already fully read) | same |
| 13 | 37 | Bash | `cat /etheron-pod/rollout-work/designs-partial/W2.md; grep -n -i "induction\|sync\b\|syncs\|anchor lies\|honest chain\|reference chain\|diverge\|density" /etheron-pod/mini-consensus-lean/paper2/molt.tex \| head -80` | "the W2 salvage (for interface alignment), and the paper's own statement of the induction" |
| 14 | 41 | Bash | `sed -n 805,870p paper/molt.tex; sed -n 975,1000p paper/molt.tex` | "Read paper Theorem 3 and induction-over-syncs passage" |
| 15 | 43 | Bash | `sed -n 118,341p Molt/ClientRule.lean` | "Read ClientRule.lean theorems in full" |
| 16 | 45 | Bash | `sed -n 255,300p Molt/Rotation.lean; sed -n 170,215p MoltPetit/Model/Safety.lean; sed -n 456,530p MoltPetit/Model/Definitions.lean` | "Read client_refresh_rule, same_block_same_prefix, core definitions" |
| 17 | 47 | Bash | `sed -n 200,310p MoltPetit/Model/KeyStealingHorizon.lean; cat Molt.lean; cat MoltPetit.lean \| head -60; cat lakefile.toml` | "Read mem_anchored theorem, root modules, lakefile" |
| 18 | 49 | Bash | grep for `blockAt_getLast`, `exists_blockAt_of_mem`, `strictSlots_lt`, `exists_blockAt_of_le`, `mem_of_blockAt`, `blockAt_lt_length`, `blockAt?_` across `MoltPetit/Model/{Soundness,Model,Safety,Liveness,KeyStealingSafety}.lean`, then `-A6` bodies of `blockAt_getLast`, `exists_blockAt_of_mem`, `strictSlots_lt`, `exists_blockAt_of_le`, `strictSlots_unique` | "Locate index/membership helper lemmas" |
| 19 | 51 | Bash | `grep -n "^## \|^### " KEY_ROTATION_SOUND.md \| head -60; awk '/^## 10/,/^## 11/' KEY_ROTATION_SOUND.md \| head -150` | "Read KEY_ROTATION_SOUND.md section 10" |
| 20 | 52 | Bash | `cat /etheron-pod/rollout-work/maps/design-docs.md \| head -300` → **no output (file does not exist)** | "Read design-docs map" |
| — | 55 | (unread) | 74K-token record; see header | — |
| 21 | 57 | Bash | `sed -n 140,200p MoltPetit/Model/KeyStealingScheduleHorizon.lean; sed -n 120,165p MoltPetit/Model/KeyStealingUnique.lean; sed -n 650,665p MoltPetit/Model/Definitions.lean` | "Read horizon_shared_prefix, KeyStealingEUFCMA, SignedHashInjective" |
| 22 | 59 | Bash | `sed -n 1,66p Molt/Axioms.lean; sed -n 590,602p MoltPetit/Results/Axioms.lean; sed -n 20,45p Molt/Results.lean; sed -n 15,32p Molt/Assumptions.lean` | "Read guard idiom and Molt.blockAt? / ValidChain definitions" |
| 23 | 61 | Bash | `grep -n -i "checkpoint" paper/molt.tex \| head -40; grep -n -i "induction\|honest chain\|reference chain" ROTATION_MODES.md KEY_ROTATION_SOUND.md PHASE2_DESIGN.md README.md memory/*.md \| head -30` | "Locate checkpoint and induction mentions in paper and design docs" |
| 24 | 63 | Bash | `which lake lean elan; ls ~/.elan/bin; cat lean-toolchain; ls .lake/build/lib/lean/Molt \| head -20; ls /etheron-pod/toolchains; grep -n "lake\|lean\|elan" /etheron-pod/toolchains/BUILD-NOTES.md` | "Check for Lean toolchain availability and build artifacts" |
| 25 | 65 | Bash | grep for `mem_of_getElem?`, `getElem?_eq_some_iff`, `IsPrefix.subset`, `getElem?_eq_getElem` in `.lake/packages/*/src/lean/Init/Data/List/*.lean` and Mathlib; `ls .lake/packages`; `find / -name Lemmas.lean -path "*Init/Data/List*"` | "Verify list lemma names in the toolchain sources" |
| 26 | 69 | Bash | `ls /work/.cage-exec/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/`; grep the same List lemma names plus `getElem?_eq_none_iff`, `IsPrefix.mem` in that toolchain's `Init/Data/List/{Lemmas,Sublist,TakeDrop,Basic}.lean` | "Locate lake binary and verify list lemma names" |
| 27 | 70 | Bash | `sed -n 168,182p paper/molt.tex; sed -n 962,975p paper/molt.tex; sed -n 895,940p paper/molt.tex` | "Read paper checkpoint and max-sync passages" |
| 28 | 73 | — | killed (429) | — |

No Grep-tool or Edit/Write calls. Files it never opened despite locating them: `PHASE2_DESIGN.md`, `ROTATION_MODES.md`, `README.md`, `memory/paper-rewrite-plan.md`, `memory/key-rotation-mission.md`, `Molt/MaxSync.lean` source (only via map), `MoltPetit/Model/KeyStealingHorizonCore.lean` source.

---

## 2. Verified facts

Legend: **[src]** = read directly from the Lean/TeX/MD source by this subagent; **[map]** = read from a map digest produced by an earlier mapper (map-verified, not re-verified from source in this transcript); **[run1]** = re-read from the run-1 salvage `W4.md`.

### 2.1 Repo, build, toolchain

* **[src]** HEAD `8b8b766 paper2 p16: appendix -- recency window, no-back-dating scope (AN/33, AN/34)`; clean tree (offset 9).
* **[src]** `/etheron-pod/rollout-work/maps/` contains, each as `.json` + `.md`: `core-grounded-cert1`, `mode1-chain`, `mode2-cert-budget`, `mode2-horizon-timed`, `mode3-lockstep`, `results-molt`, `timed-core-liveness`. **There is no `design-docs.md` map** (offset 54: `cat` produced no output). `designs-partial/` held `W1.md`, `W2.md`, `W3a.md`, `W4.md`, `W5.md` at 07:10Z.
* **[src]** `Molt.lean` (the `Molt` library root) imports exactly: `Molt.Protocol`, `Molt.Verifier`, `Molt.Assumptions`, `Molt.Results`, `Molt.Rotation`, `Molt.ClientRule`, `Molt.MaxSync`, `Molt.Liveness`, `Molt.Axioms`. Its docstring: "one module per paper section … each fresh definition is bridged to its counterpart in the original `MoltPetit` development by a `rfl`-lemma, and every theorem is transported across those bridges … Modules grow section by section with the paper; the imports above are the current frontier."
* **[src]** `MoltPetit.lean` root import list (first 60 lines): `MoltPetit.TS.Emitted`, `Model.Definitions`, `Model.Model`, `Model.Safety`, `Model.Soundness`, `Model.Liveness`, `TS.Bridge`, `Model.Grounded`, `Model.Timed`, `Results.Results`, `TS.Results`, `Model.TimedSig`, `Model.KeyIndex`, `Model.KeyRotation`, `Model.KeyStealing`, `Model.KeyStealingSafety`, `Model.KeyStealingUnique`, `Results.KeyStealingResults`, `Model.KeyStealingCert`, `Model.KeyRotationLiveness`, `Model.KeyStealingBudget`, `Model.KeyStealingLongRange`, `TS.BridgeK`, `Model.KeyStealingSchedule`, `Results.KeyStealingScheduleResults`, `Model.KeyStealingScheduleCert`, `Model.KeyStealingScheduleBudget`, `Model.KeyStealingScheduleHorizon`, `Model.KeyStealingLockstep`, `Model.KeyStealingHorizonCore`, `Model.KeyStealingHorizon`, `Model.KeyStealingScheduleTimed`, `Model.KeyRotationTests`, `Results.Axioms`, `MoltPetit.Custody`.
* **[src]** `lakefile.toml`: `name = "MoltPetit"`, `defaultTargets = ["MoltPetit", "Rust", "Thales", "Molt"]`; `[leanOptions]` `pp.unicode.fun = true`, `relaxedAutoImplicit = false`, `weak.linter.mathlibStandardSet = true`, `maxSynthPendingDepth = 3`; requires `mathlib` rev `v4.30.0-rc2` and `aeneas` (git `https://github.com/AeneasVerif/aeneas.git`, rev `bf13c42e7c34d07fc396baffad39c93023b12914`, subDir `backends/lean`); `[[lean_lib]]` `MoltPetit`, `Rust`, `Thales`, `Molt` (none with `roots`/`globs`); `[[lean_exe]] name = "moltpetit-demo" root = "Main"`.
* **[src]** `lean-toolchain` = `leanprover/lean4:v4.30.0-rc2`. `which lake lean elan` finds nothing on PATH (`/bin:/usr/bin`); `~/.elan/bin` for the executor (`/work/.cage-exec/.elan/bin`) does not exist. **But the toolchain IS present** at `/work/.cage-exec/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/` containing `cadical cc clang lake lake.orig ld.lld lean leanc leanc.orig leanchecker leanir leanmake leantar llvm-ar`. Sources at `/work/.cage-exec/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Data/List/…`.
* **[src]** `.lake/packages/` = `Cli LeanSearchClient Qq aeneas aesop batteries importGraph mathlib plausible proofwidgets`. `.lake/build/lib/lean/Molt/` already holds `.olean/.ilean/.trace` for at least `Assumptions`, `Axioms`, `ClientRule`, `Liveness` (listing cut at `head -20`).
* **[src]** `/etheron-pod/toolchains/` contains `BUILD-NOTES.md`, `MoltPetit.fresh-emission.lean`, `aeneas`, `cargo`, `cargo-nix-probe`, `cargocheck`, `charon`, diff files — the Rust-extraction toolchain, not a Lean install; `BUILD-NOTES.md` mentions lean only in the context of `Rust/Extracted.lean` faithfulness.
* **[src]** Lean core List lemmas confirmed to exist in this toolchain: `theorem getElem?_eq_some_iff {l : List α} : l[i]? = some a ↔ ∃ h : i < l.length, l[i] = a` (`Init/Data/List/Lemmas.lean:229`); `theorem mem_of_getElem? {l : List α} {i : Nat} {a : α} (e : l[i]? = some a) : a ∈ l` (`Lemmas.lean:479`); `protected theorem IsPrefix.subset (hl : l₁ <+: l₂) : l₁ ⊆ l₂` (`Init/Data/List/Sublist.lean:763`); `@[grind →] theorem IsPrefix.mem (hx : a ∈ l₁) (hl : l₁ <+: l₂) : a ∈ l₂` (`Sublist.lean:816`). (`getElem?_eq_getElem`, `getElem?_eq_none_iff` were grepped but the grep output shows no hit for them in those four files — not confirmed absent; the pattern may simply not have matched.)

### 2.2 `Molt/ClientRule.lean` lines 118–341 [src] — verbatim statements

```lean
/-- **The deep anchor is nearby.** In a valid chain, the block `n` deep
below a block `D` is fewer than `2n` slots below it: were the gap `2n` or
more, the two matured `n`-slot windows inside it would each need `quorum`
chain blocks — more than the `n` blocks that exist between them. -/
theorem deep_block_span {n : Nat} (hn : 1 ≤ n) {c : Chain}
    (hV : ValidChain n c) {m : Nat} {A D : Block}
    (hA : blockAt? c m = some A) (hD : blockAt? c (m + n) = some D) :
    D.slot < A.slot + 2 * n := by
  rw [blockAt?_eq_core] at hA hD
  by_contra hcon
  obtain ⟨hSeq, hS, hPL, hMat⟩ := hV
  have hq₁ : MoltPetit.Model.quorum n
      ≤ MoltPetit.Model.windowCount c (A.slot + 1) n :=
    hMat hD (A.slot + 1) (by omega)
  have hq₂ : MoltPetit.Model.quorum n
      ≤ MoltPetit.Model.windowCount c (A.slot + 1 + n) n :=
    hMat hD (A.slot + 1 + n) (by omega)
  have hwc : ∀ u, MoltPetit.Model.windowCount c u n
      = c.countP (MoltPetit.Model.blockInWindow u n) := by
    intro u
    unfold MoltPetit.Model.windowCount
    rw [List.countP_eq_length_filter]
  have hsum := countP_add_le_countP
    (p₁ := MoltPetit.Model.blockInWindow (A.slot + 1) n)
    (p₂ := MoltPetit.Model.blockInWindow (A.slot + 1 + n) n)
    (q := fun b => decide (A.slot < b.slot ∧ b.slot ≤ D.slot))
    (fun b h₁ h₂ => by
      simp only [MoltPetit.Model.blockInWindow, decide_eq_true_eq] at h₁ h₂
      omega)
    (fun b h => by
      simp only [MoltPetit.Model.blockInWindow, decide_eq_true_eq] at h ⊢
      omega)
    (fun b h => by
      simp only [MoltPetit.Model.blockInWindow, decide_eq_true_eq] at h ⊢
      omega)
    c
  have hbetween := countP_between_le hS hA hD
  have hquorum : MoltPetit.Model.quorum n = (2 * n + 2) / 3 := rfl
  rw [hwc] at hq₁ hq₂
  omega
```

```lean
theorem stay_recent_client_safe
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block}
    {sc sc' scPrev : SignedChain Sig} {A : Block}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen
      honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    -- the previous sync, at clock time t
    {t : Nat} {tipPrev : Block}
    (hVPrev : validSignedChainK' n Δconf ops registry scPrev = true)
    (hTipPrev : (stripSigs scPrev).getLast? = some tipPrev)
    (hRecPrev : t ≤ tipPrev.slot + n)
    (hLongPrev : n < (stripSigs scPrev).length)
    (hAnchor : blockAt? (stripSigs scPrev)
      ((stripSigs scPrev).length - 1 - n) = some A)
    -- the cadence
    (hCadence : now ≤ t + n)
    -- the anchor is honoured
    (hA : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    -- the standing budget, trailing < 5n slots
    (hBudget : ∀ u, now < u + 5 * n →
      (badSlotsIn (badKeyrot n Δconf rented Stolen (stripSigs sc)) u n).card
        ≤ faultBudget n)
    (hVal : validSignedChainK' n Δconf ops registry sc = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc )
      ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc')
      ((stripSigs sc').length - 1 - n) = some B') :
    B = B' := by
  -- the anchor's age is under 4n
  have hVPrev' := hVPrev
  rw [validSignedChainK'_eq_core] at hVPrev'
  rw [MoltPetit.Model.validSignedChainK', Bool.and_eq_true] at hVPrev'
  have hVc : MoltPetit.Model.ValidChain n (stripSigs scPrev) :=
    (MoltPetit.Model.validChainK'_sound hVPrev'.2).1
  have hTipIdx : MoltPetit.Model.blockAt? (stripSigs scPrev)
      ((stripSigs scPrev).length - 1) = some tipPrev :=
    MoltPetit.Model.blockAt_getLast hTipPrev
  have hidx : ((stripSigs scPrev).length - 1 - n) + n
      = (stripSigs scPrev).length - 1 := by omega
  have hspan : tipPrev.slot < A.slot + 2 * n :=
    deep_block_span hn hVc hAnchor (by rw [hidx]; exact hTipIdx)
  have hFresh : now ≤ A.slot + (4 * n - 1) := by omega
  exact client_refresh_rule hn hΔ hEUF hHash hA hA' hFresh
    (fun u hu => hBudget u (by omega)) hVal hVal' hTipS hTipS'
    hRecent hRecent' hLong hLong' hTipHeight hB hB'
```

Its docstring (verbatim): "**The single-constant client rule** (paper Theorem 3). No horizon parameter: the client re-verifies a chain at least once every `n` slots (`hCadence`, against the sync time `t` of the previously accepted chain `scPrev`), each time anchoring the block `n` deep below the verified tip (`hAnchor`), and refuses chains not containing its anchor. The corruption budget is consulted only on windows meeting the trailing `< 5n` slots (`hBudget`) — nothing is assumed about older history. Then two accepted, recent, equal-height chains containing the anchor agree on the block `n` below each tip. Derivation: `tipPrev.slot ≥ t - n` (recency at sync), `A.slot > tipPrev.slot - 2n` (`deep_block_span`), `now ≤ t + n` (cadence) — so `now ≤ A.slot + (4n - 1)`, and `client_refresh_rule` applies at `H := 4n - 1`."

`sync_rule` (line 238): identical binder list to `stay_recent_client_safe` with `{n : Nat} (hn : 1 ≤ n)` only (no `Δconf`, no `hΔ`), and `Δconf := n` everywhere: `KeyStealingEUFCMA n n …`, `validSignedChainK' n n ops registry scPrev/sc/sc'`, `badKeyrot n n rented Stolen (stripSigs sc)`. Conclusion `B = B'`. Proof is term-mode:
```lean
  stay_recent_client_safe hn (Nat.le_refl n) hEUF hHash hVPrev hTipPrev
    hRecPrev hLongPrev hAnchor hCadence hA hA' hBudget hVal hVal'
    hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'
```
Docstring: "the confirmation depth fixed at its provable minimum `n`, so the statement carries no `Δconf` — the protocol has exactly one timing constant. A rotation takes force once its announcing block is `n` slots deep".

`sync_rule_mem` (line 284): same binders as `sync_rule` through `hLong'`, then
```lean
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block}
    (hB : blockAt? (stripSigs sc)
      ((stripSigs sc).length - 1 - n) = some B) :
    ∃ i', i' + n < (stripSigs sc').length ∧
      blockAt? (stripSigs sc') i' = some B := by
  have hVPrev' := hVPrev
  rw [validSignedChainK'_eq_core] at hVPrev'
  rw [MoltPetit.Model.validSignedChainK', Bool.and_eq_true] at hVPrev'
  have hVc : MoltPetit.Model.ValidChain n (stripSigs scPrev) :=
    (MoltPetit.Model.validChainK'_sound hVPrev'.2).1
  have hTipIdx : MoltPetit.Model.blockAt? (stripSigs scPrev)
      ((stripSigs scPrev).length - 1) = some tipPrev :=
    MoltPetit.Model.blockAt_getLast hTipPrev
  have hidx : ((stripSigs scPrev).length - 1 - n) + n
      = (stripSigs scPrev).length - 1 := by omega
  have hspan : tipPrev.slot < A.slot + 2 * n :=
    deep_block_span hn hVc hAnchor (by rw [hidx]; exact hTipIdx)
  have hFresh : now ≤ A.slot + (4 * n - 1) := by omega
  have hVal₁ := hVal
  have hVal₁' := hVal'
  rw [validSignedChainK'_eq_core] at hVal₁ hVal₁'
  exact MoltPetit.Model.keyrot_recent_tip_ancestor_mem_anchored hn
    (Nat.le_refl n) hEUF hHash hA hA'
    (fun u hu => hBudget u (by omega))
    hVal₁ hVal₁' hTipS hTipS' hRecent hRecent' hLong hLong' hLe hB

end Molt
```
Docstring: "under the same cadence, anchor, and trailing-`5n` budget as `sync_rule`, the `n`-deep block of the lower-tipped accepted chain is a block of every taller accepted chain too, at least `n` deep there. Together the two forms cover any pair of accepted chains."

Gotchas visible in these statements (facts): the budget is keyed to `stripSigs sc` only, and in `sync_rule_mem` `sc` is the lower-or-equal-tipped chain; `hEUF`, `hHash`, `hRecent/hRecent'`, `hBudget` are all stated at one fixed `now`; the previous sync is the triple `(scPrev, t, tipPrev)` with `hRecPrev : t ≤ tipPrev.slot + n` and cadence `hCadence : now ≤ t + n`; `A` is required only as a member (`A ∈ stripSigs sc`), not at an index; `hFresh : now ≤ A.slot + (4 * n - 1)` is derived by `omega` inside both proofs and is not a standalone lemma; the private helpers `countP_add_le_countP` / `countP_between_le` (lines 27/55) are not importable.

### 2.3 `Molt/Rotation.lean` 255–300 [src] — `client_refresh_rule`, verbatim

Docstring: "**The client refresh rule** (paper Theorem 3). Pick a horizon `H` — a deployment choice. A light client that refreshes at least every `H` slots (its anchor block `A` satisfies `now ≤ A.slot + H`, and it accepts only chains containing `A`) is safe with the corruption budget consulted **only on windows overlapping the trailing `H + n` slots**: for all older history nothing is assumed — no budget, no key secrecy, nothing. Wrapper over `keyrot_recent_tip_ancestor_agreement_anchored` with the anchor's age made explicit: `now < u + n + H` follows from `now ≤ A.slot + H` and the core's guard `A.slot + 1 ≤ u + n`, so the H-guarded budget covers every window the anchored core consults."

```lean
theorem client_refresh_rule
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig} {A : Block} {H : Nat}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen
      honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    (hA : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    (hFresh : now ≤ A.slot + H)
    (hBudget : ∀ u, now < u + n + H →
      (badSlotsIn (badKeyrot n Δconf rented Stolen (stripSigs sc)) u n).card
        ≤ faultBudget n)
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc )
      ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc')
      ((stripSigs sc').length - 1 - n) = some B') :
    B = B' := by
  rw [validSignedChainK'_eq_core] at hVal hVal'
  exact MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored hn hΔ
    hEUF hHash hA hA'
    (fun u hu => hBudget u (by omega))
    -- (rest of the argument list beyond line 300 not shown in the read)
```

### 2.4 `MoltPetit/Model/Safety.lean` 170–215 [src] — verbatim

```lean
/-- A block shared at height `k + 1` forces a shared parent at height `k`. -/
theorem same_block_same_parent
    {record : SlotRecord} (hId : IdInjective record)
    {c c' : Chain}
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hP : ParentLinked c) (hP' : ParentLinked c')
    {k : Nat} {B : Block}
    (hAt : blockAt? c (k + 1) = some B) (hAt' : blockAt? c' (k + 1) = some B) :
    ∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P := by
  obtain ⟨P, hPc, hPrev⟩ := parentLinked_at_succ hP hAt
  obtain ⟨P', hPc', hPrev'⟩ := parentLinked_at_succ hP' hAt'
  have hIdEq : P.id = P'.id := by
    rw [hPrev] at hPrev'
    exact Option.some.inj hPrev'
  have hPP : P = P' := hId P.slot P'.slot (hRec hPc) (hRec' hPc') hIdEq
  exact ⟨P, hPc, hPP ▸ hPc'⟩

/-- A shared block forces agreement at every earlier height. -/
theorem same_block_same_prefix
    {record : SlotRecord} (hId : IdInjective record)
    {c c' : Chain}
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hP : ParentLinked c) (hP' : ParentLinked c') :
    ∀ {m : Nat} {B : Block},
      blockAt? c m = some B →
      blockAt? c' m = some B →
      ∀ {k : Nat}, k ≤ m →
      ∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P := by
  intro m
  induction m with
  | zero =>
      intro B hAt hAt' k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      exact ⟨B, hAt, hAt'⟩
  | succ m ih =>
      intro B hAt hAt' k hk
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · exact ⟨B, hAt, hAt'⟩
      · have hkLe : k ≤ m := Nat.lt_succ_iff.mp hlt
        obtain ⟨P, hPc, hPc'⟩ :=
          same_block_same_parent hId hRec hRec' hP hP' hAt hAt'
        exact ih hPc hPc' hkLe
```
(`same_block_same_prefix` is at Safety.lean:189 per the map; aliased as `Molt.same_block_same_prefix` at Rotation.lean:348; axioms `[propext, Quot.sound]`. `parentLinked_at_succ` is used but its location was not looked up.)

### 2.5 `MoltPetit/Model/Definitions.lean` 456–530 [src] — verbatim core predicates

```lean
abbrev SlotRecord := Nat → Finset Block
abbrev ByzantineSlots := Nat → Prop
def blockAt? (c : Chain) (h : Nat) : Option Block := getElem? c h
def SequentialHeights (c : Chain) : Prop :=
  ∀ ⦃h⦄ ⦃B : Block⦄, blockAt? c h = some B → B.height = h
def StrictSlots (c : Chain) : Prop :=
  c.Pairwise fun a b => a.slot < b.slot
def ParentLinked (c : Chain) : Prop :=
  ∀ ⦃h⦄ ⦃B : Block⦄, blockAt? c h = some B →
    match h with
    | 0 => B.prev = none
    | k + 1 => ∃ P : Block, blockAt? c k = some P ∧ B.prev = some P.id
def MaturedWindowsDense (n : Nat) (c : Chain) : Prop :=
  ∀ ⦃m⦄ ⦃D : Block⦄, blockAt? c m = some D →
    ∀ u, u + n ≤ D.slot + 1 →
      quorum n ≤ windowCount c u n
def ValidChain (n : Nat) (c : Chain) : Prop :=
  SequentialHeights c ∧ StrictSlots c ∧ ParentLinked c ∧ MaturedWindowsDense n c
def ChainInRecord (record : SlotRecord) (c : Chain) : Prop :=
  ∀ ⦃k⦄ ⦃B : Block⦄, blockAt? c k = some B → B ∈ record B.slot
def HonestSlotsUnique (bad : ByzantineSlots) (record : SlotRecord) : Prop :=
  ∀ s, ¬ bad s →
    ∀ ⦃B B' : Block⦄, B ∈ record s → B' ∈ record s → B = B'
def IdInjective (record : SlotRecord) : Prop :=
  ∀ s t, ∀ ⦃B B' : Block⦄,
    B ∈ record s → B' ∈ record t → B.id = B'.id → B = B'
open Classical in
noncomputable def badSlotsIn (bad : ByzantineSlots) (u n : Nat) : Finset Nat :=
  (Finset.Ico u (u + n)).filter fun s => bad s
def ByzantineBounded (n : Nat) (bad : ByzantineSlots) : Prop :=
  ∀ u, (badSlotsIn bad u n).card ≤ maxByzantine n
def CommonPrefixUpTo (c c' : Chain) (h : Nat) : Prop :=
  ∀ k, k ≤ h → ∃ B : Block, blockAt? c k = some B ∧ blockAt? c' k = some B
def LastCommonHeight (c c' : Chain) (h : Nat) : Prop :=
  CommonPrefixUpTo c c' h ∧
  ∀ k, h < k → ∀ B : Block,
    ¬ (blockAt? c k = some B ∧ blockAt? c' k = some B)
def chainSlotsIn (c : Chain) (u len : Nat) : Finset Nat :=
  ((c.filter (blockInWindow u len)).map Block.slot).toFinset
```
Also `Definitions.lean:656`:
```lean
def SignedHashInjective (Signed : Block → Prop) (G : Block) : Prop :=
  ∀ ⦃B B' : Block⦄,
    (B = G ∨ Signed B) → (B' = G ∨ Signed B') →
    B.id = B'.id → B = B'
```

### 2.6 `MoltPetit/Model/KeyStealingHorizon.lean` 200–310 [src]

Tail of `keyrot_recent_tip_ancestor_agreement_anchored` (lines 200–216): after `hLenEq : (stripSigs sc).length - 1 - n = (stripSigs sc').length - 1 - n := by omega` and `rw [← hLenEq] at hB'`, it case-splits `Nat.le_total sTip.slot sTip'.slot` and in each branch calls `horizon_shared_prefix hn hUniq hId hVc hVc' chainInRecord_left chainInRecord_right hTipS hTipS' hle (hBudgetFrom (sTip.slot + 1 - n) (by omega)) (k := (stripSigs sc).length - 1 - n) (by omega)` (mirrored with `hVc' hVc`, `chainInRecord_right chainInRecord_left`, `hTipS' hTipS`, `hBudgetFrom (sTip'.slot + 1 - n)`), then `rw [hB] at hPc; rw [hB'] at hPc'; rw [Option.some.inj hPc, Option.some.inj hPc']`.

`keyrot_recent_tip_ancestor_mem_anchored` (line 222), verbatim statement:
```lean
theorem keyrot_recent_tip_ancestor_mem_anchored
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig} {A : Block}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    (hA  : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    (hBudgetFrom : ∀ u, A.slot + 1 ≤ u + n →
      (badSlotsIn (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) u n).card
        ≤ maxByzantine n)
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block}
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B) :
    ∃ i', i' + n < (stripSigs sc').length ∧
      blockAt? (stripSigs sc') i' = some B := by
```
Proof skeleton (verbatim pieces): `hVc : ValidChain n (stripSigs sc) := by rw [validSignedChainK', Bool.and_eq_true] at hVal; exact (validChainK'_sound hVal.2).1` (same for `hVc'`); `hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hHash (fun b hb => Or.inr (keyStealingSigned_of_mem hVal hb)) (fun b hb => Or.inr (keyStealingSigned_of_mem hVal' hb))`; `hUniq := honestSlotsUnique_keyrot_anchored hn hΔ (versionedUnforgeable_of_keyStealingEUFCMA hEUF) hA hA' hBudgetFrom hId hVal hVal' ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩`; `hAle : A.slot ≤ sTip.slot` proved via `exists_blockAt_of_mem hA`, `blockAt_getLast hTipS`, `List.getElem?_eq_some_iff` (after `unfold blockAt?`), `Nat.lt_or_ge`, `strictSlots_lt hVc.2.1 hi hTipAt h`, else `injection hi with hi; rw [hi]` (same for `hAle'`); `hTipIdx : sTip.height = (stripSigs sc).length - 1 := hVc.1 (blockAt_getLast hTipS)` (and primed); `hkn' : ((stripSigs sc).length - 1 - n) + n < (stripSigs sc').length := by omega`; then the same `Nat.le_total` / `horizon_shared_prefix` split as the agreement form, ending `exact ⟨(stripSigs sc).length - 1 - n, hkn', by rw [hBP]; exact hPc'⟩` where `hBP : B = P` from `rw [hB] at hPc; exact Option.some.inj hPc`. **Note the witness index returned is `(stripSigs sc).length - 1 - n` — the same index in `sc'` as in `sc`.**

Following it (line ~305): `keyrot_recent_tip_ancestor_agreement_horizon_of_valid` — docstring "Same conclusion as `keyrot_recent_tip_ancestor_agreement`, and from strictly fewer hypotheses: no `hHead`/`hHead'`."

### 2.7 `MoltPetit/Model/KeyStealingScheduleHorizon.lean` 140–200 [src] — `horizon_shared_prefix`

Docstring: "**Top-window shared prefix (the horizon core).** Two valid chains from one execution record, with the lower tip's trailing matured window within budget: they share their block at every height that is `n`-deep in the *lower-tipped* chain. Validator-agnostic … The proof runs the `2q > n + f` pigeonhole at `u = tip.slot + 1 − n` (matured in both chains, since `tip.slot ≤ tip'.slot`): the shared non-corrupt slot's two blocks are equal by honest-slot uniqueness, sit strictly above height `k` (their slot exceeds `B`'s, and slots order heights), and `same_block_same_prefix` carries the agreement down to `k`. No hypothesis touches any window below `u`, and no shared genesis is assumed."
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
    ∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P := by
```
Proof start uses `blockAt_getLast`, a `cases hopt : blockAt? c k` with `List.getElem?_eq_none_iff`, `slot_gap_of_position_gap hS (c.length - 1 - k) k hB …` giving `hgap : B.slot + n ≤ tip.slot`, `set u := tip.slot + 1 - n`, `chainSlotsIn_card hS` and `hDense hTipAt u (by omega)`. (The read also caught the end of a preceding private/helper induction using `strictSlots_lt` at lines 140–144.)

### 2.8 `MoltPetit/Model/KeyStealingUnique.lean` 120–165 [src] — the crypto surface

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
Provenance docstring (verbatim excerpt): "This surface is **assumed**, not reduced to the timed model. … `KeyStealingEUFCMA` is therefore taken as a named primitive. What the development **does** prove on top of it is the index-pin half: `versionedUnforgeable_of_keyStealingEUFCMA` discharges the 'the verifying version is never rotated-out' step via the proven `rotated_key_dead`, so *only* the bare recency-scoped registry EUF-CMA is assumed, never the pin." `VersionedUnforgeable` (same file, next declaration) has one field `verified_was_signed` and is derived, never assumed. **Gotcha for an induction: `now` and `Δ` are parameters of the structure; `hEUF` at one `now` says nothing about another `now`.**

### 2.9 Helper lemmas [src] — verbatim

```lean
-- MoltPetit/Model/Soundness.lean:97
theorem blockAt_getLast {ch : Chain} {tip : Block}
    (hTip : ch.getLast? = some tip) :
    blockAt? ch (ch.length - 1) = some tip := by
  unfold blockAt?
  rw [← List.getLast?_eq_getElem?]
  exact hTip

-- MoltPetit/Model/Model.lean:47
theorem strictSlots_lt {c : Chain} (hS : StrictSlots c)
    {i j : Nat} {Bi Bj : Block}
    (hi : blockAt? c i = some Bi) (hj : blockAt? c j = some Bj)
    (hij : i < j) : Bi.slot < Bj.slot := by
  unfold blockAt? at hi hj
  rcases List.getElem?_eq_some_iff.mp hi with ⟨hiLen, hiEq⟩
  rcases List.getElem?_eq_some_iff.mp hj with ⟨hjLen, hjEq⟩
  …

-- MoltPetit/Model/Model.lean:71
theorem exists_blockAt_of_mem {c : Chain} {B : Block} (hB : B ∈ c) :
    ∃ k, blockAt? c k = some B := by
  rcases List.mem_iff_getElem.mp hB with ⟨k, hk, hEq⟩
  refine ⟨k, ?_⟩
  unfold blockAt?
  rw [List.getElem?_eq_getElem hk, hEq]

-- MoltPetit/Model/Model.lean:79
theorem exists_blockAt_of_le {c : Chain} {k m : Nat} (hk : k ≤ m)
    {D : Block} (hAt : blockAt? c m = some D) :
    ∃ C : Block, blockAt? c k = some C := by
  unfold blockAt? at hAt ⊢
  rcases List.getElem?_eq_some_iff.mp hAt with ⟨hmLen, _⟩
  have hkLen : k < c.length := lt_of_le_of_lt hk hmLen
  exact ⟨_, List.getElem?_eq_getElem hkLen⟩

-- MoltPetit/Model/KeyStealingSafety.lean:86 (public; mem_of_blockAt' at :40 is PRIVATE)
theorem strictSlots_unique {c : Chain} (hS : StrictSlots c) {B B' : Block}
    (hB : B ∈ c) (hB' : B' ∈ c) (hslot : B.slot = B'.slot) : B = B' := by
  obtain ⟨i, hi⟩ := exists_blockAt_of_mem hB
  obtain ⟨j, hj⟩ := exists_blockAt_of_mem hB'
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd (strictSlots_lt hS hi hj h) (by omega)
  · subst h; rw [hi] at hj; exact Option.some.inj hj
  · exact absurd (strictSlots_lt hS hj hi h) (by omega)
```
No `blockAt_lt_length` or `blockAt?_*` lemma matched the grep in those five files (i.e. no public "index < length" lemma was found; the idiom used in the repo is `unfold blockAt?` + `List.getElem?_eq_some_iff`).

### 2.10 `Molt/Axioms.lean` 1–66 [src] — guard idiom, verbatim

```lean
import Molt.Results
import Molt.Rotation
import Molt.ClientRule
import Molt.MaxSync
import Molt.Liveness

/-!
# Axiom audit for the `Molt` headline theorems

Same discipline as `MoltPetit/Results/Axioms.lean`: a guarded
`#print axioms` per headline theorem, so `lake build Molt` fails if any
theorem ever picks up an axiom beyond the three classical ones. Extend
this file with every new headline theorem.
-/

-- Theorem 1: light-client safety (paper §6.1).
/-- info: 'Molt.light_client_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.light_client_safety
…
-- Theorem 3: the client refresh rule (paper §6.3, mode 1).
/-- info: 'Molt.client_refresh_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.client_refresh_rule

-- The deep anchor is nearby (paper §6.3, mode 1).
/-- info: 'Molt.deep_block_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.deep_block_span

-- Theorem 3, single-constant form: sync every n slots (paper §6.3, mode 1).
/-- info: 'Molt.stay_recent_client_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.stay_recent_client_safe

-- Theorem 3, final form: confirmation depth fixed at n, no Δconf anywhere.
/-- info: 'Molt.sync_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.sync_rule

-- Theorem 3, membership form: unequal tip heights (paper §6.3, mode 1).
/-- info: 'Molt.sync_rule_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Molt.sync_rule_mem
```
Two-axiom guards in the same file: `Molt.badKeyrot_lossOnly` and `Molt.badSched_lossOnly` report `[propext, Quot.sound]`. Wrap example (`MoltPetit/Results/Axioms.lean:595–599`, verbatim):
```
/-- info: 'MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored
```
whereas `'MoltPetit.Model.keyrot_recent_tip_ancestor_mem_anchored' depends on axioms: [propext, Classical.choice, Quot.sound]` fits on one line.

### 2.11 `Molt/Results.lean` 20–45, `Molt/Assumptions.lean` 15–32 [src]

* `abbrev TimedLog := MoltPetit.Model.TimedLog`; `def AvailableAt (log : TimedLog) (G : Block) (B : Block) (R : Nat) : Prop := B = G ∨ ∃ r ≤ R, B ∈ log r`; `abbrev TimedExecution := MoltPetit.Model.TimedExecution`; **`def blockAt? (c : Chain) (h : Nat) : Option Block := getElem? c h`** (Results.lean:39); `theorem availableAt_eq_core : AvailableAt = MoltPetit.Model.AvailableAt := rfl`; `theorem blockAt?_eq_core : blockAt? = MoltPetit.Model.blockAt? := rfl` (line 42).
* `namespace Molt`: `abbrev SlotRecord := MoltPetit.Model.SlotRecord`; `abbrev ByzantineSlots := MoltPetit.Model.ByzantineSlots`; **`abbrev ValidChain := MoltPetit.Model.ValidChain`**; `abbrev SigningLog := MoltPetit.Model.SigningLog`; then `open Classical in` … `badSlotsIn`.

### 2.12 Paper `paper/molt.tex` [src] — verbatim passages

**Lines 805–815 (anchor rationale):** "No validator rule can reject such a fork from the inside; it can only be excluded by the client knowing one thing the fork cannot contain: a sufficiently recent block of the real chain. That is the \emph{anchor} --- a block from the client's trusted region, i.e.\ at least $n$ deep below its last verified tip, or a checkpoint --- with chains not containing it refused. (Anchoring the literal tip would be a mistake: only $n$-deep blocks are guaranteed shared, and a tip the network never adopts would wedge the client against the real chain.) This is a weak-subjectivity assumption~\cite{weaksubj}, but a narrow one, and Theorem~\ref{thm:refresh} is its exact price tag."

**Lines 816–828 (Theorem 3 / `thm:refresh`):** "\begin{theorem}[The client sync rule; Lean \code{sync\_rule}, \code{sync\_rule\_mem}]\label{thm:refresh} Let a light client re-verify a chain \emph{at least once every $n$ slots}, each time taking as its anchor the block $n$ deep below the newly verified tip. Suppose the key-stealing surface and hash injectivity hold, and the $\rho$/$T$ budget --- read off the lower accepted chain's confirmed floors --- holds on every $n$-slot window starting in the trailing $5n$ slots, or later. Then any two accepted, recent chains longer than $n$ blocks that both contain the anchor agree: at equal tip heights, on the block $n$ below each tip; at unequal heights, the lower chain's $n$-deep block is a block of the taller chain, at least $n$ deep there. \end{theorem}"

**Lines 837–847 (the 5n):** "The $5n$ is the reach of that assumption: how far back the anchor can sit, plus the one window the counting needs. Each summand is one fact. At sync time the freshly verified tip passed the recency rule, so it is at most $n$ slots old. The anchor sits fewer than $2n$ \emph{slots} below that tip although it is $n$ \emph{blocks} deep --- density leaves no room for more (two full windows in the gap would demand $2\quorum > n$ blocks where only $n$ exist; Lean \code{deep\_block\_span}). And the client returns within $n$ slots of the sync. Total anchor age: under $4n$; plus the one window the budget's counting needs: $5n$. (The ``or later'' in the budget clause matters only against chains dated beyond the verifier's clock, which a real clock rejects; nothing at all is assumed about windows starting earlier.)"

**Lines 849–866:** "…taking the anchor to be the genesis block recovers the lifetime-budget statement exactly (\code{client\_refresh\_rule} at $A :=$ genesis). … Second, the trailing $5n$ slots are not a bootstrap condition: the window slides with the verifier's clock, re-anchored at every sync --- it measures the client's own recency of state, not the chain's age, and an old chain is exactly as protected as a young one."

**Lines 982–997 — THE W4 TARGET, verbatim:** "Conclusion, machine-checked (\code{sync\_rule}, \code{sync\_rule\_mem}): any two chains such a client accepts at a sync --- both, by its rule, containing its anchor --- agree: at equal heights on the block $n$ below each tip, and the lower tip's $n$-deep block lies on every taller one --- hence, block by block through the parent-id chain (\code{same\_block\_same\_prefix}), on the lower chain's whole confirmed prefix. **Agreement with the honest chain itself follows by an induction over syncs argued on paper, not itself machine-checked. Each sync's agreement keeps the next anchor on the honest chain while the honest tip is at least as tall as the accepted one (density keeps a recent taller fork's $n$-deep block below its divergence, hence on the honest chain --- an informal argument). The join checkpoint starts the induction as the op-model's fresh trust event: a checkpoint no older than ${\approx}\,4n$ slots satisfies the general Lean form \code{client\_refresh\_rule}. And the honest tip staying recent is a liveness-style side condition, outside the safety hypotheses.** At the full-chain presentation this is the complete story."

**Lines 168–182 (mode 1 paragraph):** "\paragraph{Mode 1: reactive rotation --- for clients that stay current.} … The client's whole duty: \textbf{re-verify a chain at least once every $n$ slots} --- the same $n$ as the recency rule --- keeping as its anchor the block $n$ deep below the last verified tip, and refusing chains that do not contain it. A client that misses its cadence must stop acting and re-join from a fresh trusted checkpoint, exactly as if it were new --- operational discipline the theorems force rather than state: past the cadence the theorems' fault-budget assumption becomes one no deployment can stand behind --- quiet thefts accumulate until nothing satisfies it (\code{no\_budget\_beyond}), and re-joining is a fresh trust event outside the formal development."

**Lines 965–975 (realistic deployment):** "Seven seats ($n = 7$, $\tau \approx 4$\,s; $\fmax = 2$, $\quorum = 5$) … Clients are services acting on the chain continuously: each joins from a deployment-published checkpoint (its first anchor), then re-verifies at least every $28$\,s, anchoring the $n$-deep block of each verified chain."

**Lines 895–940 (max sync period):** "\emph{Upward} (\code{max\_sync\_period}): safety holds whenever rented slots plus the theft census stay within $\fmax$ on every window starting in the trailing $F + 4n$ slots or later. … $F_{\max} = S - 4n$. \emph{Downward} (\code{census\_accumulates}, \code{census\_accumulates\_later\_thefts}, \code{no\_budget\_beyond}) … The smallest $F$ at which a full forged execution is \emph{known} to exist lies somewhat higher --- by ${\approx}\,n$ slots of span, and in victims. Density binds every fork window, so if honest producers only ever extend the real chain, an accepted fork needs ${\approx}\,\quorum \approx 2\fmax$ victims whose retirements postdate the divergence (pre-divergence rotations are inherited through the anchor and stay dead); in the bare model, where nothing constrains which branch honest producers extend, the count falls toward $\fmax + 1$. Certifying one such execution end-to-end in Lean is future work. A deployment prepared to assume strictly more --- honest producers never extending adversarial branches, and theft \emph{times} inside the signature assumptions … --- could in principle support a larger $F$; that stronger model is outside the present development (future work; honest scope below). The sync rule is the $F = n$, $S = 5n$ instance. (Engine: \code{client\_refresh\_rule}, parametric in the anchor's age; \code{stay\_recent\_client\_safe} derives the age bound.)"

**"checkpoint" occurrences in the paper:** lines 177, 809, 971, 993–994 only.

**grep hits for induction/sync in the paper (offset 38):** 41, 76, 78, 97, 201, 253, 270–271, 311, 314, 322, 324, 334, 346, 385, 396, 550, 562, 703, 706, 797, 816–817, 830, 838, 841, 844, 864, 900–901, 922, 925, 936, 942, 957, 961–962, 982–993, 1018, 1060, 1155, 1308–1350, 1412.

### 2.13 Design docs [src]

* `KEY_ROTATION_SOUND.md` section headers: `## 0. Principal's instructions` (100), `### 0.1 Load-bearing named hypotheses` (124), `## 1. Where the current proof breaks` (154), `## 2. The adversary, granted in full` (181), `## 3. The induced budget as a clean slot predicate` (218), `## 4. Why old keys don't inflate the recent budget — the pin + recency` (263), `## 5. The index pin, and what it is *for*` (306), `## 6. Two depth parameters, kept separate` (343), `## 7. Target theorem` (356), `## 8. Proof DAG` (382), `## 9. Risk register (post-review, v3)` (514), `## 10. Discharging the recency anchor: two operational packages for a stateless light client` (536), `### 10.0 The unifying device: generation as a function of position` (564), `### 10.1 Package A` (601), `### 10.2 Package B` (650), `### 10.3 Bounded jumps` (692), `### 10.4 Formalization status` (716).
* `KEY_ROTATION_SOUND.md` §10 (read through 10.2): mode 1 = "the default in-band rotation of this note's base sections (no explicit schedule; chain-local floor) — the anchor is necessary, and the client profile is the rolling anchor / continuously-online client"; "The base results (§7) take the light client's recency premise (`H-ANCHOR`) as a named assumption … a patient adversary who steals **one key per producer, one at a time** … eventually holds a quorum of producer identities across history and fabricates a deep-past fork. The default model contains this by weak subjectivity, not by refutation (`recent_oldkey_fork_is_longrange`, §8)." §10.0: `badKeyrotOn s := rented s ∨ ∃ j ≥ inForce(c₀, i, s). Stolen i j` with `inForce` chain-local; "That chain-locality is the entire reason the anchor is needed … and the reason the hardest proof node exists (the `confirmed_mem_iff_le` strong induction, present only to reconcile the two chains' schedules)."
* grep for `induction|honest chain|reference chain` in design docs & memory (offset 62): `KEY_ROTATION_SOUND.md:8,335,399,570,585,725`; `PHASE2_DESIGN.md:282,288,293,302,311-312,338-339` ("by strong induction on `s`", "a naïve slot-induction does not close", "(opt-B) Combined induction … by induction on chain height/length", "the naïve slot-induction was refuted"); `memory/annotations-2026-07-work-order.md:487,516`; `memory/dconf-2n-tightness-finding.md:30`; `memory/key-rotation-mission.md:53,59,61,63,79-81,129` (":79–81: `honestSlotsUnique_keyrot` by `induction s using Nat.strongRecOn with | ind s IH =>` … is the correct eliminator name in this Mathlib (NOT `Nat.strong_induction_on`)"); `memory/paper-rewrite-plan.md:59` ("induction as a Lean composition"). **No hit for "honest chain" or "reference chain" in any design doc** — the induction over syncs is documented only in the paper (lines 988–997) and in `memory/paper-rewrite-plan.md:55–59`.

### 2.14 Map-digest facts relevant to W4 [map]

From `results-molt.md` (offsets 23, 34):

* Theorem table for `Molt/ClientRule.lean`, `Molt/Rotation.lean`, `Molt/MaxSync.lean`, `MoltPetit/Results/KeyStealingResults.lean`, `MoltPetit/Model/KeyStealingHorizon.lean`, `KeyStealingScheduleHorizon.lean` — line numbers: `deep_block_span` 123, `stay_recent_client_safe` 174, `sync_rule` 238, `sync_rule_mem` 284; `client_refresh_rule` 267; `max_sync_period` 176 (hCadence `now ≤ t + F`, guard `now < u + F + 4 * n`, `hFresh : now ≤ A.slot + (F + 3 * n - 1)`; **no `_mem` form exists**); `producer_slot_in_window` 30, `inForce_mono` 79 (Molt-only; not in core), `census_accumulates` 95, `census_accumulates_later_thefts` 135, `no_budget_beyond` 156; `keyrot_recent_tip_ancestor_agreement_anchored` 134, `keyrot_recent_tip_ancestor_mem_anchored` 222, `keyrot_recent_tip_ancestor_agreement_horizon` 69, `_horizon_of_valid` 310; `honestSlotsUnique_keyrot_anchored` (HorizonCore.lean:258); `horizon_shared_prefix` 161; `same_block_same_prefix` (Safety.lean:189). `Molt/Axioms.lean` has 31 guard blocks (lines 17–160), imports `Molt.Results, Molt.Rotation, Molt.ClientRule, Molt.MaxSync, Molt.Liveness`.
* `reuse_notes` (verbatim, the parts a new Molt module needs):
  * "IMPORTS FOR A NEW ADDITIVE Molt MODULE. `import Molt.MaxSync` transitively brings Molt.Protocol, Molt.Verifier, Molt.Assumptions, Molt.Results, Molt.Rotation, Molt.ClientRule and (through Molt.Rotation) MoltPetit.Results.KeyStealingResults, MoltPetit.Results.KeyStealingScheduleResults, MoltPetit.Model.KeyStealingHorizon (anchored forms), KeyStealingLockstep, KeyStealingCert, KeyStealingScheduleCert, and through those KeyStealingHorizonCore, KeyStealingScheduleHorizon (ByzantineBoundedFrom, horizon_shared_prefix), KeyStealingUnique (chainUnionRecord, chainInRecord_left/right, idInjective_keyrot, versionedUnforgeable_of_keyStealingEUFCMA, KeyStealingEUFCMA), KeyStealingSchedule, Safety (same_block_same_prefix), Soundness (blockAt_getLast), Model (exists_blockAt_of_mem, strictSlots_lt, exists_blockAt_of_le), Liveness (slot_le_tip_of_mem), KeyStealingSafety (strictSlots_unique). Only Molt.Liveness … is outside that cone".
  * "NAMESPACE / NAME-RESOLUTION IDIOM. Every Molt file is `namespace Molt … end Molt`; core names are always written fully qualified `MoltPetit.Model.X` — no Molt file does `open MoltPetit.Model`. Inside `namespace Molt`, unqualified `blockAt?`, `stripSigs`, `badSlotsIn`, `faultBudget`, `producer`, `validChain`, `validChainK'`, `validSignedChainK'`, `badKeyrot`, `inForce`, `FaultBounded`, `SignedHashInjective`, `KeyStealingSigned`, `KeyStealingEUFCMA`, `Block`, `Chain`, `ValidChain`, `SigOps`, `KeyRegistry`, `SignedChain`, `ByzantineSlots`, `SigningLog` resolve to the Molt versions. … honestSigned is declared as `{honestSigned : SigningLog}` in Molt files and `Nat → Nat → Option Block` in core; identical."
  * "THE *_eq_core BRIDGE IDIOM … (a) rfl-bridges … badKeyrot, keyFloor, confirmedPrefix, inForce, inForcePinned, schedPin, blockAt?, stripSigs, sigOk, sigsOk, badSlotsIn, FaultBounded(=ByzantineBounded), SignedHashInjective, quorum, faultBudget(=maxByzantine), producer(=producerForSlot), genesisOk, childOk, windowDense, denseSoFar, AvailableAt, HonestSlotsUnique, IdInjective. These are DEFEQ, so a hypothesis stated with the Molt name can be passed to a core theorem by `exact` with no rewrite … (b) NON-rfl bridges (funext + induction/simp): keyMonoOk, noMixing, linksOk, validChain, validChainK, validChainK', validSignedChainK', validSignedChainSched, validSignedChainLock, validSignedChain, validSuffix, validCertifiedChain, produceBlock?, selectChain. … Consumption idiom, used in EVERY Molt mode-1 theorem: `rw [validSignedChainK'_eq_core] at hVal hVal'` then `exact MoltPetit.Model.<core theorem> …`. … Keep a copy if the original is still needed (`have hVal₁ := hVal; rw [...] at hVal₁`, ClientRule.lean:333-335). Note `rw`/`simp` matching is syntactic even for rfl-bridges — deep_block_span does `rw [blockAt?_eq_core] at hA hD` before feeding core `MaturedWindowsDense` — while `exact`/application works up to defeq."
  * "EXTRACTING ValidChain FROM A Molt VALIDATOR HYPOTHESIS (ClientRule.lean:216-220, verbatim): `have hVPrev' := hVPrev; rw [validSignedChainK'_eq_core] at hVPrev'; rw [MoltPetit.Model.validSignedChainK', Bool.and_eq_true] at hVPrev'; have hVc : MoltPetit.Model.ValidChain n (stripSigs scPrev) := (MoltPetit.Model.validChainK'_sound hVPrev'.2).1`. Tip at index length−1: `MoltPetit.Model.blockAt_getLast hTipPrev`. Height = index: `hVc.1 (blockAt_getLast hTipS)`."
  * "BUDGET FORMS … (2) Anchored core: `hBudgetFrom : ∀ u, A.slot + 1 ≤ u + n → …` — windows whose last slot u+n−1 is ≥ A.slot; anchor A of ARBITRARY age … The proof consults only u = sTip.slot + 1 − n (lower tip's top window) via horizon_shared_prefix, then same_block_same_prefix propagates down. (3) Trailing/age forms in Molt: client_refresh_rule takes `hFresh : now ≤ A.slot + H` and `hBudget : ∀ u, now < u + n + H → …`; the wrapper derives the anchored guard by omega … In all mode-1 forms the budget predicate is keyed to `stripSigs sc` — the FIRST chain, which in membership forms must be the lower-or-equal-tipped one (hLe : sTip.height ≤ sTip'.height); never sc'. A new trailing-window theorem for a new cadence/anchor rule should follow the pattern: prove `hFresh : now ≤ A.slot + H` by omega from its own timing hypotheses, then call `client_refresh_rule hn hΔ hEUF hHash hA hA' hFresh (fun u hu => hBudget u (by omega)) hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'` (no eq_core rewriting needed at all …); for a membership form there is no Molt-level anchored-mem wrapper with explicit H — go to MoltPetit.Model.keyrot_recent_tip_ancestor_mem_anchored after `rw [validSignedChainK'_eq_core]` exactly as sync_rule_mem does (it needs hLong' too)."
  * "GENESIS-AT-INDEX-0 GOTCHA. hHead/hHead' … NOT required by the anchored/horizon core forms nor by any Molt mode-1 rule (client_refresh_rule, stay_recent_client_safe, sync_rule, sync_rule_mem, max_sync_period). In the genesis-free forms G is still an implicit argument fixed only by hHash's genesis exemption."
  * "SIGNED PREDICATE GOTCHA. Mode-1 (validSignedChainK') theorems need hHash over `KeyStealingSigned n ops registry` … KeyStealingEUFCMA's field is stated at core validSignedChainK' (no bridge needed for hEUF); its recency premise is `∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ` — build it as ⟨sTip, hTipS, hRecent⟩."
  * "MISC. `badSlotsIn` is noncomputable and classical … The private helpers in ClientRule/MaxSync (countP_add_le_countP, countP_between_le, foldl_max_*) are `private` and cannot be reused from a new file. Re-export idioms: `alias name := MoltPetit.Model.name` for theorems (with a docstring), `abbrev X := @MoltPetit.Model.X` for structures/props. `#print axioms` on an alias works".
  * "NEW GUARD FILE … (c) BUILD DISCOVERY: lakefile.toml declares `[[lean_lib]] name = \"Molt\"` with no `roots`/`globs`, so Lake builds only `Molt.lean` and its transitive imports; Molt/Axioms.lean is enforced only because Molt.lean imports it. A NEW file that no existing module imports is NOT elaborated by `lake build`, `lake build Molt`, or `nix run .#verify-lean` (`lake build MoltPetit Rust Thales Molt`, nix/apps.nix:59). To check it without touching existing files: `lake build Molt.<NewFile>` explicitly; to have the default build enforce it, one `import Molt.<NewFile>` line must be added to Molt.lean (a one-line edit to an existing file — the planner must choose). CLAUDE.md rule: 'Add a new headline theorem → add its guard'".
* `open_items_found` (results-molt): `memory/paper-rewrite-plan.md:55-58`: "only mode-2's CERTIFICATE form remains global-budget (future work: horizon at certificates; also trailing-5n cert form for mode 1, lockstep cert wrapper, the honest-chain induction as a Lean composition)"; `Molt/MaxSync.lean:8-13,22-23`: F_max = S − 4n identity stated only in prose; `Molt/ClientRule.lean:16-17/170-173`: anchor-age bound proven inline by omega, no standalone lemma; `MoltPetit/Model/KeyStealingHorizon.lean:48-54`: "mode 1's `badKeyrotOn` is chain-relative, so the slot-induction must still reconcile `inForce` across the two chains, and that induction consults windows all the way down" (mode 1 has NO `ByzantineBoundedFrom`-style horizon theorem; the anchored form is the substitute).

From `mode1-chain.md` (offset 26): `KeyStealingUnique.lean` — `chainUnionRecord` 45, `mem_chainUnionRecord` 48 (`x ∈ chainUnionRecord sc sc' s ↔ (x ∈ stripSigs sc ∨ x ∈ stripSigs sc') ∧ x.slot = s`), `chainInRecord_left` 54, `chainInRecord_right` 60, `idInjective_keyrot` 70, `KeyStealingEUFCMA` 136, `VersionedUnforgeable` 161, `versionedUnforgeable_of_keyStealingEUFCMA` 184, `honestSlotsUnique_keyrot` 201 (`induction s using Nat.strongRecOn with | ind s IH =>`). `KeyRotation.lean`: `validChainK'_sound` 122, `validChainK'_pinned` 130, `inForce_agreement_of_confirmed_eq` 201, `deep_block_shared` 245, `confirmed_mem_iff` 305, `inForce_agreement` 349 ("NOT usable directly inside the key-stealing uniqueness induction (circular)"), `rotated_key_dead` 401. `KeyStealing.lean`: `badKeyrotOn` 47, `badKeyrotOn_lossOnly` 67. `KeyStealingHorizonCore.lean`: `sigma_shared_prefix` 91, `confirmed_mem_iff_horizon` 151, `honestSlotsUnique_keyrot_horizon` 183, `honestSlotsUnique_keyrot_anchored` 258 ("below the anchor both chains are the same list (same_block_same_prefix)"). `Molt/Rotation.lean` bridges: `keyMonoOk_eq_core` 168 (induction), `keyFloor_eq_core` 176 rfl, `confirmedPrefix_eq_core` 177, `inForce_eq_core` 179, `inForcePinned_eq_core` 180, `badKeyrot_eq_core` 182 rfl, `validChainK_eq_core` 185, `validChainK'_eq_core` 190, `validSignedChainK'_eq_core` 196 (funext+simp), `badKeyrot_lossOnly` 230, `client_refresh_rule` 267, alias `keyrot_recent_certified_suffix_agreement` 308.

From `timed-core-liveness.md` (offset 30): `Definitions.lean` `Block` structure 58 (anonymous-constructor order `⟨slot, height, prev, id, contentsHash, keyIndex⟩`), `Chain` abbrev 75, `windowCount` 82, `maturedWindowsDense` 95, `validChain` 122, `blockAt?` 462, `ValidChain` 490, `HonestBlocksCover` 753, `TimedExecution` 719 (five fields `key_match, honest_stamp, honest_once, chain_order, id_inj`). `Liveness.lean`: `slot_le_tip_of_mem` 63 (`hS, hTip, hx ⊢ x.slot ≤ tip.slot`), `validChain_append_one` 123, `liveness_valid_extension` 232, `liveness_global` 361 (single-chain `buildChain g ss`, bad := unscheduled slots; aliased `Molt.global_liveness` at Molt/Liveness.lean:33). `Model.lean`: `mem_chainSlotsIn` 35, `chainSlotsIn_subset_Ico` 40. `Results/Results.lean`: `liveness_produce_block` 429, `liveness_produce_signed_block` 455. `KeyRotationLiveness.lean`: `liveness_produce_blockK` 130 (aliased `Molt.liveness_produce_blockK` at Molt/Liveness.lean:27). `Molt/Liveness.lean` is pure aliases (45 lines): `production_liveness` 19, `signed_production_liveness` 22, `liveness_produce_blockK` 27, `global_liveness` 33.

From `core-grounded-cert1.md` (offset 28): certificate-level material (`GroundedCert`, `GroundedCertK`, `recent_certified_suffix_agreement` Grounded.lean:371, `keyrot_recent_certified_suffix_agreement` KeyStealingCert.lean:583 with budget quantified over `AttestedHistoryK`) — W2/W1 territory; the only W4-relevant items are the build gotcha (same as above, for `MoltPetit` lib) and toolchain facts (`leanprover/lean4:v4.30.0-rc2`, mathlib `v4.30.0-rc2`, `relaxedAutoImplicit = false`).

### 2.15 Sibling salvage `W2.md` [src, offset 38]

Designer `a71b5bdcf1ae9fdee` (run 1, "W2 UNCONFIRMED; could be W4") was killed after one Bash call at `2026-09-04T21:16:57Z`; it verified only: HEAD `8b8b766`, clean tree, **no markdown file in the repo mentions `W3a`, `W3b` or `W7`**, and the repo-root markdown files are `CLAUDE.md, HANDOFF_SCHEDULE_VARIANT.md, KEY_INDEX_DESIGN.md, KEY_ROTATION_SOUND.md, LOCKSTEP_DESIGN.md, NIX.md, PHASE2_DESIGN.md, README.md, ROTATION_MODES.md`. No design content.

### 2.16 Run-1 salvage `W4.md` [run1, offset 7]

Fully read. It records that designer `ab9a3fba02babc59e` made one tool call (`sed -n 1,60p Molt/ClientRule.lean`) and verified only the module header and the two private counting lemmas; the salvager appended (post-mortem) the remaining ClientRule declarations — all of which this run re-verified from source (§2.2). Its open questions: (1) W4 label was inferred; (2) whether "the theorems this work item composes" meant `sync_rule`/`sync_rule_mem` or the core `keyrot_recent_tip_ancestor_mem_anchored`/`client_refresh_rule`.

---

## 3. Design direction

**No design was stated.** The subagent produced no theorem statements, definitions, file names, proof sketches, dependency list, or effort estimate. The only planned-step statements are the five sentences quoted at the top.

What the tool-call trajectory evidences (inference from the reads, NOT the subagent's words — a fresh designer should treat this as "what it had assembled on the desk", not as a decision):

1. It treated **`sync_rule` / `sync_rule_mem` (Molt/ClientRule.lean:238/284)** as the per-sync step, and read them in full together with the engine they wrap (`client_refresh_rule`, `keyrot_recent_tip_ancestor_mem_anchored`, `horizon_shared_prefix`) and `same_block_same_prefix` — consistent with the paper's line 988–992 framing (per-sync agreement + parent-id chaining ⇒ next anchor on the honest chain).
2. It pulled the **record-level predicates** (`SlotRecord`, `ChainInRecord`, `HonestSlotsUnique`, `IdInjective`, `ParentLinked`, `CommonPrefixUpTo`) and `KeyStealingEUFCMA` / `SignedHashInjective` in full — the hypotheses one would need to restate per sync (each carries its own `now`).
3. It located the **index/membership helper lemmas** (`blockAt_getLast`, `exists_blockAt_of_mem`, `exists_blockAt_of_le`, `strictSlots_lt`, `strictSlots_unique`) and checked the **Lean-core List lemma names** `getElem?_eq_some_iff`, `mem_of_getElem?`, `IsPrefix.subset`, `IsPrefix.mem` — the last two suggest it was considering expressing "the honest chain extends the accepted chain's confirmed prefix" via `List.IsPrefix` (`<+:`). Unconfirmed.
4. It read the **guard idiom, Molt.lean root imports, lakefile, and toolchain location** — i.e. it was preparing to specify a new `Molt/<X>.lean` module plus guard entries and the build/discovery caveat (new file not built unless imported from `Molt.lean` or built explicitly with `lake build Molt.<X>` using `/work/.cage-exec/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake`).
5. It read the paper's **checkpoint** passages (177, 809, 971, 993–994) and the **max-sync-period** passage — presumably for the base case ("the join checkpoint starts the induction … a checkpoint no older than ≈4n slots satisfies `client_refresh_rule`") and for scoping (the "honest tip staying recent is a liveness-style side condition, outside the safety hypotheses").
6. It grepped for "honest chain"/"reference chain" in every design doc and memory file and found **no prior formal design** of the induction anywhere but the paper and `memory/paper-rewrite-plan.md:55–59`.

Dependencies on other work items: none stated. (Its read of `W2.md` was labelled "for interface alignment", but W2.md contained no interface to align with.)

Effort estimate: none.

---

## 4. Decisions and rejected alternatives

**None recorded.**

---

## 5. Partial structured output

**None.** No `StructuredOutput` call and no drafted JSON anywhere in the transcript.

---

## 6. Open questions

1. **Content of transcript offset 55** (74K tokens, unreadable under the salvage protocol). It sits exactly at the `promptId` change and a 5-minute gap, so it is very likely a mid-task message from the orchestrator (course correction or re-prompt). If the planner has it, it may redefine the item's scope.
2. (Inherited from run 1, still unanswered) Which per-sync theorem the induction should compose: the Molt-level `sync_rule`/`sync_rule_mem` (Δconf := n, trailing-5n budget) or the parametric `client_refresh_rule` (explicit `H`, which the paper says the join checkpoint satisfies at ≈4n).
3. How the per-sync hypotheses that are stated at a single `now` (`hEUF : KeyStealingEUFCMA … now Δ`, `hHash`, `hRecent`, `hBudget : ∀ u, now < u + 5n → …`) are to be quantified across syncs — the subagent read these definitions but did not say.
4. How the "honest chain" is to be represented (the paper's induction needs "the honest tip is at least as tall as the accepted one" and "density keeps a recent taller fork's n-deep block below its divergence, hence on the honest chain — an informal argument"); nothing in the repo formalises an honest chain for mode 1 (`liveness_global`'s `buildChain` is unsigned, single-chain, and outside the key-stealing model).
5. Whether the new module should be `Molt/`-side (namespace `Molt`, importing `Molt.MaxSync` or `Molt.ClientRule`) or core-side; and whether the planner permits the one-line `import` edit to `Molt.lean` needed for `lake build` to elaborate it (otherwise `lake build Molt.<NewFile>` must be used explicitly).
6. Whether `List.IsPrefix` (`<+:`) is the intended representation of "accepted chain's confirmed prefix lies on the honest chain" (the subagent verified the lemma names exist but never said why).
