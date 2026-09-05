# W1-ordering — PARTIAL verification salvage

> **WARNING — THIS IS A PARTIAL VERIFICATION.** The verifier subagent was killed by
> an HTTP 429 session limit during its reconnaissance phase. It never reached the
> analysis phase, never stated a single confirmation or refutation, and **never
> returned a verdict**. What follows is the raw ground truth it had paid for at the
> moment it died, salvaged so a fresh verifier does not re-establish it.

| | |
|---|---|
| **Agent id** | `aca2d452765aa1db9` |
| **Transcript** | `/run/claude/agent/projects/-etheron-pod/c28ff38c-0cb1-500d-8726-22cd73943085/subagents/workflows/wf_6b051052-ec7/agent-aca2d452765aa1db9.jsonl` |
| **Workflow** | `wf_6b051052-ec7`, session `c28ff38c-0cb1-500d-8726-22cd73943085`, cwd `/etheron-pod`, model `claude-fable-5-1`, effort `high` |
| **Expected label** (indexer-inferred) | `W1-ordering` |
| **Confirmed label** | **Work item W1 — CONFIRMED from transcript content.** Lens `ordering` — **consistent with, but not positively evidenced by, the transcript**; the run died before any lens-specific reasoning was emitted. See "Label confirmation" below. |
| **Lines seen** | 4–19 (line 20 is an empty terminator) |
| **Lines skipped** | 1 (oversized prompt, per instruction), 2, 3 (harness attachments, per instruction) |
| **Wall clock** | first assistant token `2026-09-05T09:43:42.464Z` → 429 at `2026-09-05T09:44:17.912Z` (~35 seconds; 5 Bash calls, 0 Read/Grep calls) |
| **Where it stopped** | Line 19 — synthetic assistant message `"You've hit your session limit · resets 2pm (UTC)"`, `apiErrorStatus: 429`, `rateLimitType: "five_hour"`, `requestId req_011Cek5QY1yhbX5G2WF4M9Zn` |
| **Structured output** | **None.** No `StructuredOutput` call, no drafted JSON anywhere in the transcript. |

---

## 0. Label confirmation

**Work item = W1 (mode 3 lockstep at certificate level). CONFIRMED.** Evidence:

- Of the five shell calls, calls 2 and 3 target `MoltPetit/Model/KeyStealingLockstep.lean`
  exclusively — the mode-3 lockstep engine (`lockstepOk`, `validSignedChainLock`,
  `LockstepPackage`, `lockstep_declares_rosterGen`, `lockstep_validSignedChainSched`).
  That file is W1's stated substrate and nothing in W2 (mode 1 anchored trailing-5n)
  or W5 (per-generation census / erasure credit) touches it.
- Calls 4 and 5 read `MoltPetit/Model/KeyStealingScheduleCert.lean` end to end
  (`GroundedCertSched`, `GroundedHistorySched`, `groundedCertSched_history`,
  `groundedCertSched_suffix_history`, `sched_recent_certified_suffix_agreement`) —
  the mode-2 certificate module that W1's `GroundedCertLock` / `GroundedHistoryLock` /
  `groundedCertLock_history` / `groundedCertLock_suffix_history` /
  `lockstep_recent_certified_suffix_agreement` are declared to mirror. It read no
  mode-1 anchored file (`KeyStealing*Anchored*`, `AcceptedSuffixK`, `Molt/ClientRule`)
  and no census/erasure file (`ErasureTimed`, `KeyStealingHorizon*`), so W2 and W5
  are excluded.
- Corroboration outside the transcript: the design under review is
  `/etheron-pod/rollout-work/designs/W1.md`, whose title is
  *"W1 — Mode 3 (free-cadence lockstep) at certificate level: GroundedCertLock with a
  one-counter threaded state, history reconstruction, certificate-level pinning, and
  lockstep_recent_certified_suffix_agreement by transport through the existing
  full-chain lockstep engine"*, mtime `09:43` — the same minute the subagent started.

**Lens = `ordering`: not confirmable from content.** The one line of assistant prose
("I'll start by inspecting the repository layout and the key files the design
references.") and all five commands are lens-neutral reconnaissance that either lens
would open with. Two weak pointers toward `ordering` and none against it:

- Call 1 dumped `lakefile.toml`, the full `MoltPetit.lean` and `Molt.lean` import
  frontiers, and the `MoltPetit/Model`, `MoltPetit/Results`, `Molt` directory
  listings — that is the **file-layout idiom** material specific to the ordering lens,
  and it is not what an accuracy-lens run needs first.
- No `grep` for existence of individual reused names (the accuracy-lens move) was
  ever issued; the single grep was a whole-file declaration *index*, which serves the
  additive-only / no-duplication check.

Treat the lens as **unconfirmed but uncontradicted**.

---

## 1. Files examined (complete — 5 tool calls, all Bash)

| # | line | command (verbatim) | stated purpose (`description` field) |
|---|---|---|---|
| 1 | 6 | `cd /etheron-pod/mini-consensus-lean && ls && cat lakefile.toml && cat MoltPetit.lean && cat Molt.lean && ls MoltPetit/Model MoltPetit/Results Molt` | "List repo layout and root modules" |
| 2 | 9 | `cd /etheron-pod/mini-consensus-lean && grep -n "theorem\|lemma\|^def\|^abbrev\|^structure\|^inductive\|^private\|^namespace\|^open\|^section\|^end\|^import\|^  toPackageA\|^  [a-zA-Z_]* *:" MoltPetit/Model/KeyStealingLockstep.lean \| head -150` | "Index declarations in KeyStealingLockstep.lean" |
| 3 | 11 | `cd /etheron-pod/mini-consensus-lean && sed -n 65,120p MoltPetit/Model/KeyStealingLockstep.lean && echo ------ && sed -n 245,330p MoltPetit/Model/KeyStealingLockstep.lean && echo ------ && sed -n 470,500p MoltPetit/Model/KeyStealingLockstep.lean` | "Read lockstep defs, package, pinning theorem, transport statement" |
| 4 | 14 | `cd /etheron-pod/mini-consensus-lean && sed -n 195,235p MoltPetit/Model/KeyStealingScheduleCert.lean && echo ---- && sed -n 340,470p MoltPetit/Model/KeyStealingScheduleCert.lean` | "Read ScheduleCert core surface and GroundedCertSched" |
| 5 | 17 | `cd /etheron-pod/mini-consensus-lean && sed -n 470,702p MoltPetit/Model/KeyStealingScheduleCert.lean` | "Read rest of ScheduleCert: suffix history and cert agreement theorem" |

Files/ranges actually seen:

- `/etheron-pod/mini-consensus-lean/lakefile.toml` — whole file
- `/etheron-pod/mini-consensus-lean/MoltPetit.lean` — whole file (import frontier)
- `/etheron-pod/mini-consensus-lean/Molt.lean` — whole file (imports + module doc)
- repo root `ls`, plus `ls` of `MoltPetit/Model`, `MoltPetit/Results`, `Molt`
- `/etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingLockstep.lean` — grep index of the whole file (file ends at 614), then lines **65–120**, **245–330**, **470–500**
- `/etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingScheduleCert.lean` — lines **195–235**, **340–470**, **470–702** (file ends inside this last window with `end MoltPetit.Model`)

**Never opened** (present in the `ls` but unread): `LOCKSTEP_DESIGN.md`,
`ROTATION_MODES.md`, `HANDOFF_SCHEDULE_VARIANT.md`, `docs/rollout/ROLLOUT_NOTES.md`,
`KEY_INDEX_DESIGN.md`, `KEY_ROTATION_SOUND.md`, `PHASE2_DESIGN.md`,
`MoltPetit/Model/KeyStealingCert.lean`, `MoltPetit/Results/KeyStealingScheduleResults.lean`,
`MoltPetit/Results/Axioms.lean`, `Molt/Rotation.lean`, `Molt/Axioms.lean`, and every
other `Molt/*` module. Anything the design asserts about those files is **untouched**
by this run.

---

## 2. Claims POSITIVELY CONFIRMED by the verifier

**None.** The verifier emitted exactly one sentence of prose in the whole run and it
was a plan, not a finding. It never asserted, endorsed or ratified any design claim
before the 429.

Section 3 below is therefore **not** a list of verifier confirmations; it is the
verbatim ground truth its five commands returned, recorded so the cost is not paid
twice. No verdict attaches to any of it.

---

## 3. Ground truth the run had already paid for (raw tool output, no verdict attached)

### 3.1 Repo layout (call 1)

Repo root of `/etheron-pod/mini-consensus-lean`:

```
CLAUDE.md  HANDOFF_SCHEDULE_VARIANT.md  KEY_INDEX_DESIGN.md  KEY_ROTATION_SOUND.md
LOCKSTEP_DESIGN.md  Main.lean  Molt  Molt.lean  MoltPetit  MoltPetit.lean  NIX.md
PHASE2_DESIGN.md  README.md  docs/rollout/ROLLOUT_NOTES.md  ROTATION_MODES.md  Rust  Rust.lean
Thales  Thales.lean  custody-p3  flake.lock  flake.nix  lake-manifest.json
lakefile.toml  lean-toolchain  memory  moltPetit.ts  nix  paper  paper-custody
paper-p3  paper2  rust  rust-keyrot  rust-keyrot-p3  tools
```

`lakefile.toml` (verbatim, load-bearing parts):

```toml
name = "MoltPetit"
version = "0.1.0"
keywords = ["math"]
defaultTargets = ["MoltPetit", "Rust", "Thales", "Molt"]

[leanOptions]
pp.unicode.fun = true # pretty-prints `fun a ↦ b`
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.30.0-rc2"

[[require]]
name = "aeneas"
git = "https://github.com/AeneasVerif/aeneas.git"
rev = "bf13c42e7c34d07fc396baffad39c93023b12914"
subDir = "backends/lean"

[[lean_lib]] name = "MoltPetit"
[[lean_lib]] name = "Rust"
[[lean_exe]] name = "moltpetit-demo"  root = "Main"
[[lean_lib]] name = "Thales"
[[lean_lib]] name = "Molt"
```

`MoltPetit.lean` — the import frontier, **in order**, verbatim:

```
MoltPetit.TS.Emitted, MoltPetit.Model.Definitions, MoltPetit.Model.Model,
MoltPetit.Model.Safety, MoltPetit.Model.Soundness, MoltPetit.Model.Liveness,
MoltPetit.TS.Bridge, MoltPetit.Model.Grounded, MoltPetit.Model.Timed,
MoltPetit.Results.Results, MoltPetit.TS.Results, MoltPetit.Model.TimedSig,
MoltPetit.Model.KeyIndex, MoltPetit.Model.KeyRotation, MoltPetit.Model.KeyStealing,
MoltPetit.Model.KeyStealingSafety, MoltPetit.Model.KeyStealingUnique,
MoltPetit.Results.KeyStealingResults, MoltPetit.Model.KeyStealingCert,
MoltPetit.Model.KeyRotationLiveness, MoltPetit.Model.KeyStealingBudget,
MoltPetit.Model.KeyStealingLongRange, MoltPetit.TS.BridgeK,
MoltPetit.Model.KeyStealingSchedule, MoltPetit.Results.KeyStealingScheduleResults,
MoltPetit.Model.KeyStealingScheduleCert, MoltPetit.Model.KeyStealingScheduleBudget,
MoltPetit.Model.KeyStealingScheduleHorizon, MoltPetit.Model.KeyStealingLockstep,
MoltPetit.Model.KeyStealingHorizonCore, MoltPetit.Model.KeyStealingHorizon,
MoltPetit.Model.KeyStealingScheduleTimed, MoltPetit.Model.KeyRotationTests,
MoltPetit.Results.Axioms, MoltPetit.Custody
```

`Molt.lean` — imports in order, then its module doc verbatim:

```
Molt.Protocol, Molt.Verifier, Molt.Assumptions, Molt.Results, Molt.Rotation,
Molt.ClientRule, Molt.MaxSync, Molt.Liveness, Molt.Axioms
```

> `# Molt — the paper-aligned codebase`
> `This library re-presents the Molt Petit development in the order and vocabulary of
> the rewritten paper (`paper/molt.tex`): one module per paper section, definitions
> written out fresh so the paper can quote them, and the headline theorems restated in
> the paper's terms.`
> `Proof engine: each fresh definition is bridged to its counterpart in the original
> `MoltPetit` development by a `rfl`-lemma, and every theorem is transported across
> those bridges — so everything here is machine-checked against the same core, and the
> axiom guards apply unchanged.`
> `Modules grow section by section with the paper; the imports above are the current
> frontier.`

Directory contents:

- `Molt/`: `Assumptions.lean  Axioms.lean  ClientRule.lean  Liveness.lean  MaxSync.lean  Protocol.lean  Results.lean  Rotation.lean  Verifier.lean`
- `MoltPetit/Model/`: `Definitions.lean  Grounded.lean  KeyIndex.lean  KeyRotation.lean  KeyRotationLiveness.lean  KeyRotationTests.lean  KeyStealing.lean  KeyStealingBudget.lean  KeyStealingCert.lean  KeyStealingHorizon.lean  KeyStealingHorizonCore.lean  KeyStealingLockstep.lean  KeyStealingLongRange.lean  KeyStealingSafety.lean  KeyStealingSchedule.lean  KeyStealingScheduleBudget.lean  KeyStealingScheduleCert.lean  KeyStealingScheduleHorizon.lean  KeyStealingScheduleTimed.lean  KeyStealingUnique.lean  Liveness.lean  Model.lean  Safety.lean  Soundness.lean  Timed.lean  TimedSig.lean`
- `MoltPetit/Results/`: `Axioms.lean  KeyStealingResults.lean  KeyStealingScheduleResults.lean  Results.lean`

Neither `MoltPetit/Model/KeyStealingLockstepCert.lean`, nor
`MoltPetit/Results/LockstepCertAxioms.lean`, nor `Molt/LockstepCert.lean`, nor
`Molt/LockstepCertAxioms.lean` (W1's four proposed new files) appear in these
listings.

### 3.2 `MoltPetit/Model/KeyStealingLockstep.lean` — full declaration index (call 2, verbatim grep output)

```
1:import MoltPetit.Model.KeyStealingScheduleBudget
2:import MoltPetit.Results.KeyStealingScheduleResults
27:* **The pinning theorem** `lockstep_declares_rosterGen`: on any accepted
42:whole scheduled theorem set to lockstep chains: anchor-free light-client
65:namespace MoltPetit.Model
76:def lockstepOk (n : Nat) : Chain → Bool
84:theorem lockstepOk_iff_pairwise {n : Nat} (c : Chain) :
103:def validSignedChainLock {σ sk pk : Type} (n : Nat)
112:def lagSched (n : Nat) (rosterGen : Nat → Nat) (s : Nat) : Nat :=
120:theorem schedPinned_mono {sched₁ sched₂ : Nat → Nat}
125:  have := h b hb
130:theorem schedCore_mono {σ sk pk : Type} {n : Nat} {sched₁ sched₂ : Nat → Nat}
141:theorem schedCoreUnforgeable_mono {n : Nat} {sched₁ sched₂ : Nat → Nat}
154:theorem schedCore0_of_lock {σ sk pk : Type} {n : Nat}
172:private theorem lockstep_rel {n : Nat} {c : Chain} (hS : StrictSlots c)
190:  have := hPairIdx i j hiLen hjLen hij
195:private theorem lockstep_const {n : Nat} {c : Chain} (hS : StrictSlots c)
211:private theorem head_slot_min {c : Chain} (hS : StrictSlots c) {G : Block}
220:private theorem window_producer_inj' {n u s s' : Nat}
252:structure LockstepPackage (n : Nat) (rosterGen : Nat → Nat) {Sig sk pk : Type}
256:  mono : ∀ ⦃w w' : Nat⦄, w ≤ w' → rosterGen w ≤ rosterGen w'
257:  unforgeable :
259:  declared : ∀ ⦃i s : Nat⦄ ⦃B : Block⦄, honestSigned i s = some B →
261:  hashInj : SignedHashInjective (SignedDeclared n ops registry) G
262:  genesis_gen : G.keyIndex = rosterGen (G.slot / n)
263:  rentBound : ∀ u, (badSlotsIn rented u n).card ≤ R
264:  exposedBound : ∀ u, (exposedProducersSched n (lagSched n rosterGen) Stolen u).card ≤ T
265:  budget_le : R + T ≤ maxByzantine n
268:that hands the entire scheduled theorem set to lockstep chains. -/
269:theorem LockstepPackage.toPackageA
277:  unforgeable := schedCoreUnforgeable_mono (fun _ => Nat.zero_le _) hP.unforgeable
278:  hashInj := hP.hashInj
279:  rentBound := hP.rentBound
280:  exposedBound := hP.exposedBound
281:  budget_le := hP.budget_le
284:-- The pinning theorem
287:/-- **The pinning theorem — "no-mixing pins any fork to one generation."**
299:theorem lockstep_declares_rosterGen
474:theorem lockstep_validSignedChainSched
555:theorem lockstep_recent_tip_ancestor_agreement
586:theorem lockstep_recent_tip_ancestor_mem
614:end MoltPetit.Model
```

Facts readable directly off this index (stated as facts, not as verdicts):

- The file's public declaration set is exactly: `lockstepOk` (76), `lockstepOk_iff_pairwise`
  (84), `validSignedChainLock` (103), `lagSched` (112), `schedPinned_mono` (120),
  `schedCore_mono` (130), `schedCoreUnforgeable_mono` (141), `schedCore0_of_lock` (154),
  `LockstepPackage` (252), `LockstepPackage.toPackageA` (269),
  `lockstep_declares_rosterGen` (299), `lockstep_validSignedChainSched` (474),
  `lockstep_recent_tip_ancestor_agreement` (555), `lockstep_recent_tip_ancestor_mem` (586).
- `lockstep_rel` (172), `lockstep_const` (195), `head_slot_min` (211) and
  `window_producer_inj'` (220) are **`private`**.
- There is **no** `GroundedCertLock`, `GroundedHistoryLock`, `lockstepFrom`,
  `lockstepOk_append_iff`, `keyMonoOk_of_lockstepOk`, `groundedCertLock_history`,
  `groundedCertLock_suffix_history`, `groundedCertLock_gen_of_tail`,
  `lockstep_cert_gen_pinned`, `lockstep_cert_declares_rosterGen` or
  `lockstep_recent_certified_suffix_agreement` anywhere in the file.
- The file imports only `MoltPetit.Model.KeyStealingScheduleBudget` and
  `MoltPetit.Results.KeyStealingScheduleResults`; single namespace
  `MoltPetit.Model` (65 → 614); no `open` line appears in the index.

### 3.3 `KeyStealingLockstep.lean` lines 65–120 (call 3, verbatim)

```lean
namespace MoltPetit.Model

/-- The **no-mixing rule**: along the chain, the declared generation is
constant within each `n`-slot window and non-decreasing across windows —
equivalently, `keyIndex` is a monotone function of the window index
`slot / n`. Roster-wide: unlike `keyMonoOk` this compares *all* pairs, not
just same-producer pairs. -/
def lockstepOk (n : Nat) : Chain → Bool
  | [] => true
  | b :: rest =>
      rest.all (fun b' =>
        decide ((b.slot / n = b'.slot / n → b.keyIndex = b'.keyIndex) ∧
          b.keyIndex ≤ b'.keyIndex))
      && lockstepOk n rest

theorem lockstepOk_iff_pairwise {n : Nat} (c : Chain) :
    lockstepOk n c = true ↔
      c.Pairwise (fun a b => (a.slot / n = b.slot / n → a.keyIndex = b.keyIndex) ∧
        a.keyIndex ≤ b.keyIndex) := by
  induction c with
  | nil => simp [lockstepOk]
  | cons b rest ih =>
    rw [lockstepOk, Bool.and_eq_true, List.all_eq_true, List.pairwise_cons, ih]
    ...

/-- The **lockstep signed validator**: versioned-registry signatures,
structural/monotone validity, and the no-mixing rule. No schedule parameter —
nothing here references `rosterGen`. -/
def validSignedChainLock {σ sk pk : Type} (n : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChainK n (stripSigs sc)
    && lockstepOk n (stripSigs sc)

/-- The lagged schedule induced by a roster-generation function: a block at
slot `s` is pinned at the *previous* window's generation. The lag is what
absorbs the one unmatured tip window. (`Nat` subtraction makes window 0 lag
to itself, which the genesis convention `genesis_gen` pins exactly.) -/
def lagSched (n : Nat) (rosterGen : Nat → Nat) (s : Nat) : Nat :=
  rosterGen (s / n - 1)
```

### 3.4 `KeyStealingLockstep.lean` lines 245–330 (call 3, verbatim)

Tail of the `LockstepPackage` docstring:

> `core validator, so its scope covers lockstep-accepted chains.`
> `* `hashInj`, `rentBound`, `exposedBound` (at the lagged schedule — the cumulative
> census, `PackageA`'s shape), `budget_le` — as in `PackageA`.`
> `Honest accounting: assumption-wise this is `PackageA` at `lagSched` plus the
> behavioural `rosterGen` fields; what is *bought* is that the validator the deployment
> runs is schedule-free.`

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

/-- A lockstep package is `PackageA` at the lagged schedule — the transport
that hands the entire scheduled theorem set to lockstep chains. -/
theorem LockstepPackage.toPackageA
    {n : Nat} {rosterGen : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block}
    {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T) :
    PackageA n (lagSched n rosterGen) ops registry rented Stolen honestSigned
      now Δ G R T where
  unforgeable := schedCoreUnforgeable_mono (fun _ => Nat.zero_le _) hP.unforgeable
  hashInj := hP.hashInj
  rentBound := hP.rentBound
  exposedBound := hP.exposedBound
  budget_le := hP.budget_le
```

Note the `LockstepPackage.unforgeable` field is `SchedCoreUnforgeable n (fun _ => 0) …`
— the **zero** schedule, lifted to `lagSched` in `toPackageA` by
`schedCoreUnforgeable_mono (fun _ => Nat.zero_le _)`.

`lockstep_declares_rosterGen` (line 299) docstring + full signature, verbatim:

> `/-- **The pinning theorem — "no-mixing pins any fork to one generation."**
> On an accepted recent lockstep chain, every block whose window is matured (witnessed
> by any chain block `D` with `W·n + n ≤ D.slot + 1`) declares exactly `rosterGen` of
> its window.`
> `Census: the window is quorum-dense with per-window-distinct producers, all at one
> generation `g` (no-mixing). If `g ≠ rosterGen W`, then by the EUF-CMA surface and the
> `declared` discipline none of those blocks is honest, so every one sits at a rented
> slot or at a producer whose generation-`g` key is stolen: at most
> `R + T ≤ ⌊(n-1)/3⌋ < quorum` slots — contradiction. The `≥ lagSched` side condition
> the exposure census needs is supplied by the induction hypothesis one window down. -/`

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

Proof opening seen: `classical`; destructures `validSignedChainLock` by
`Bool.and_eq_true` twice into `⟨⟨hSigs, hVK⟩, hLock⟩`; `hVC : ValidChain n (stripSigs sc)
:= (validChainK_sound hVK).1`; `hGmem` by `List.mem_of_getElem? hHead`; `hGmin :=
head_slot_min hS hHead`; then `induction W using Nat.strongRecOn`.

### 3.5 `KeyStealingLockstep.lean` lines 470–500 (call 3, verbatim)

Docstring tail + signature of the transport:

> `in `G` passes the *scheduled* validator at `lagSched n rosterGen`. Blocks in a matured
> window declare exactly their window's `rosterGen` (pinning) — at or above the lag; a
> block in the one unmatured window still clears the lag by no-mixing monotonicity from
> the previous window, which is always matured. -/`

```lean
theorem lockstep_validSignedChainSched
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T)
    {sc : SignedChain Sig}
    (hVal : validSignedChainLock n ops registry sc = true)
    (hHead : blockAt? (stripSigs sc) 0 = some G)
    (hRecent : ∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) :
    validSignedChainSched n (lagSched n rosterGen) ops registry sc = true
```

Proof shape seen: same `Bool.and_eq_true` destructuring, `validChainK_sound`,
`head_slot_min`, then `rw [validSignedChainSched, …]`, `refine ⟨⟨hSigs, hVK⟩, ?_⟩`,
`rw [schedPinned, List.all_eq_true]`, `set W := B.slot / n`, `hBlo : W * n ≤ B.slot :=
Nat.div_mul_le_self B.slot n`.

### 3.6 `KeyStealingScheduleCert.lean` lines 195–235 (call 4, verbatim)

```lean
structure SchedCoreUnforgeable (n : Nat) (schedule : Nat → Nat) {Sig sk pk : Type}
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (rented : ByzantineSlots)
    (Stolen : Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block)
    (now Δ : Nat) : Prop where
  unforgeable :
    ∀ {sc : SignedChain Sig} {sb : SignedBlock Sig} {j : Nat},
      validSignedChainSchedCore n schedule ops registry sc = true →
      sb ∈ sc →
      (∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) →
      ops.verify (registry (producerForSlot n sb.block.slot) j) sb.block sb.sig = true →
      ¬ rented sb.block.slot →
      ¬ Stolen (producerForSlot n sb.block.slot) j →
      honestSigned (producerForSlot n sb.block.slot) sb.block.slot = some sb.block

/-- The core surface delivers the full-validator surface (full validity implies
core validity, so the core assumption's scope covers every fully-valid chain). -/
theorem schedUnforgeable_of_core {n : Nat} {schedule : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    (h : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ) :
    SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ :=
  ⟨fun hVal hmem hRecent hverify hrent hstolen =>
    h.unforgeable (schedCore_of_validSignedChainSched hVal) hmem hRecent hverify
      hrent hstolen⟩
```

Followed by a section header `-- The scheduled safety chain at core level (verbatim
mirrors)` and the start of `theorem honestSlotsUnique_schedCore` (cut off at 235 with
its implicit binders `{n} {schedule} {Sig sk pk} {ops} {registry} {rented} {Stolen}
{honestSigned} {now Δ}`), docstring: *"`honestSlotsUnique_sched` at core level — the
direct contraction proof, unchanged: it never consulted `keyMonoOk`."*

### 3.7 `KeyStealingScheduleCert.lean` lines 340–470 (call 4, verbatim)

Opens mid-proof of a `…_of_length` deep-block-agreement wrapper (name above line 340,
never seen) whose visible conclusion is `B = B'` and whose closing call is
`sched_deep_block_agreement_core hn hUnf hHash hBudget hVal hVal' hHead hHead' hRecent
hRecent' hB hB' hD hD' (Nat.le_refl _) (Nat.le_refl _)`, from hypotheses
`(hB : blockAt? (stripSigs sc) k = some B)`, `(hB' : blockAt? (stripSigs sc') k = some B')`,
`(hLen : k + n < (stripSigs sc).length)`, `(hLen' : k + n < (stripSigs sc').length)`.

Then, under the header `-- The scheduled certificate derivation — no threaded floor`:

> `/-- A certificate claim is **grounded-sched in genesis `G`** when it arose from the
> genesis claim by folding in one signed block at a time, each fold checking link +
> signature + density + **the scheduled pin** `schedule b.slot ≤ b.keyIndex`. Every check
> is a pure function of `(claim, block)` — the fold threads **no floor**: the pin is
> computed from the block's own slot. The certificate state is exactly the plain
> (`GroundedCert`) state; contrast `GroundedCertK`, whose folds gate on (and step) a
> per-producer floor vector.`
> `Deployment note (as in `GroundedCertK`): the genesis constructor requires `Signed G`
> and the slot-0 pin `schedule G.slot ≤ G.keyIndex` — the deployment genesis must carry a
> verifying registry signature at its declared version (`sigsOk` has no genesis
> exemption). -/`

```lean
inductive GroundedCertSched (n : Nat) (schedule : Nat → Nat) (Signed : Block → Prop)
    (G : Block) : CertClaim → Prop
  | genesis :
      genesisOk G = true →
      G.slot = 0 →
      Signed G →
      schedule G.slot ≤ G.keyIndex →
      GroundedCertSched n schedule Signed G
        { tipId := G.id, tipSlot := G.slot, tipHeight := G.height
        , tail := [G].filter fun x => decide (G.slot + 2 - n ≤ x.slot) }
  | extend (cl : CertClaim) (b : Block) :
      GroundedCertSched n schedule Signed G cl →
      b.height = cl.tipHeight + 1 →
      cl.tipSlot < b.slot →
      b.prev = some cl.tipId →
      Signed b →
      schedule b.slot ≤ b.keyIndex →
      (∀ u : Nat, cl.tipSlot + 2 ≤ u + n → u + n ≤ b.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ [b]) u n) →
      GroundedCertSched n schedule Signed G
        { tipId := b.id, tipSlot := b.slot, tipHeight := b.height
        , tail := (cl.tail ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot) }

/-- What the grounded-sched derivation reconstructs: a `validChain`-accepted,
**schedule-pinned** prefix matching the claim, with every block signed. -/
structure GroundedHistorySched (n : Nat) (schedule : Nat → Nat) (Signed : Block → Prop)
    (G : Block) (cl : CertClaim) (c : Chain) : Prop where
  valid   : validChain n c = true
  pinned  : schedPinned schedule c = true
  head    : blockAt? c 0 = some G
  tip     : ∃ t : Block, c.getLast? = some t ∧
              t.id = cl.tipId ∧ t.slot = cl.tipSlot ∧ t.height = cl.tipHeight
  tail_eq : cl.tail = c.filter fun x => decide (cl.tipSlot + 2 - n ≤ x.slot)
  len_eq  : c.length = cl.tipHeight + 1
  signed  : ∀ B ∈ c, Signed B

/-- **History reconstruction for the scheduled certificate** (mirrors
`groundedCertK_history` minus every floor step, plus pin propagation). -/
theorem groundedCertSched_history {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Signed : Block → Prop} {G : Block} {cl : CertClaim}
    (h : GroundedCertSched n schedule Signed G cl) :
    ∃ c : Chain, GroundedHistorySched n schedule Signed G cl c
```

Proof structure seen in full for the `genesis` case (`refine ⟨[G], …⟩`; `validChain n [G]`
discharged via `maturedWindowsDense`/`windowDense`/`quorum` with `n = 1 ∧ u = 0` by
`omega`; `schedPinned` by `simp [schedPinned, hPin]`; length from `genesisOk`) and for
the `extend` case up to the `hAllDense` sub-proof (`windowCount_mono
(List.sublist_append_left c [b])`, `windowCount_append`, `hist.tail_eq`,
`windowCount_filter_low`), then `validChain_append_one hist.valid hTipEq hChild hAllDense`
and pin propagation by `rw [schedPinned, List.all_append, Bool.and_eq_true]`.

### 3.8 `KeyStealingScheduleCert.lean` lines 470–702 (call 5, verbatim)

Rest of `groundedCertSched_history` (head preservation via `List.getElem?_append_left`;
tail re-filtering via `List.filter_append` + `List.filter_filter` + `List.filter_congr`
with the `omega` step `b.slot + 2 - n ≤ x.slot → cl.tipSlot + 2 - n ≤ x.slot`), then:

> `/-- **Grounded-sched prefix + validated suffix = full core-accepted chain.**
> Mirrors `groundedCertK_suffix_history`; the suffix-side rotation check is the **pin
> alone** (`schedPinned` over the suffix — computable from each block's own slot),
> replacing the default certificate's `keyMonoFrom` against a carried floor snapshot. -/`

```lean
theorem groundedCertSched_suffix_history {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Signed : Block → Prop} {G : Block} {cl : CertClaim}
    (hG : GroundedCertSched n schedule Signed G cl)
    {s₁ : Block} {srest : Chain} {sTip : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
      quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hPinS : schedPinned schedule (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, Signed B) :
    ∃ c : Chain,
      validChain n (c ++ s₁ :: srest) = true ∧
      schedPinned schedule (c ++ s₁ :: srest) = true ∧
      blockAt? (c ++ s₁ :: srest) 0 = some G ∧
      c.length = cl.tipHeight + 1 ∧
      (∀ B ∈ c ++ s₁ :: srest, Signed B)
```

Proof reuses seen: `groundedCertSched_history`, `validChain_sound`, `blockAt_getLast`,
`strictSlots_of_checks (linksOk_isChain hLinks)`, `slot_le_tip_of_mem`,
`windowCount_mono`, `windowCount_append`, `windowCount_filter_low`,
`validChain_append_suffix hFullDense (s₁ :: srest) c t rfl hist.valid hTipEq hLinksT hSlotsLe`.

The headline, under header `-- The certificate-level headline — no floor, global budget,
no anchor`. Docstring verbatim (this is the paragraph W1's own docstring is modelled on):

> `/-- **Certificate-level light-client safety under the scheduled adversary** (the
> scheduled analogue of `keyrot_recent_certified_suffix_agreement` — and strictly
> simpler, in all three of the promised ways):`
>
> `1. **No floor snapshot.** The certificate carries the claim alone (tip data + tail
> buffer); the suffix rotation check is `schedPinned` — the verifier computes
> `schedule b.slot` from each block's own slot. The default certificate's
> `(claim, floors)` wire-authentication contract **disappears**: there is no floor to
> authenticate, hence no unauthenticated-floor attack surface.`
> `2. **Global budget.** `hBudget` is a single chain-independent hypothesis — `badSched`
> reads no chain, so the default theorem's quantification over every attestable history
> (`AttestedHistoryK`) has nothing to range over.`
> `3. **No `Δconf`.** The scheduled uniqueness proof needs no confirmation gate.`
>
> `A light client runs this from `O(n)` blocks: claim (tip data + tail of `≤ n−1`
> blocks), suffix, and a clock — with `schedule` a public protocol parameter (e.g.
> `fun s => s / R`), not wire data.`
>
> `**Residual static contract (the dynamic one is gone, this one is not).** In this
> statement one `schedule` binder couples the certificate derivation (`hcl`), the suffix
> pin (`hPinS`), the EUF-CMA surface (`hUnf`), and the budget (`hBudget`). At the wire
> level that means: `schedule` is a deployment constant baked into the verifier alongside
> `n`, `G`, and the registry — a verifier that let a certificate or peer *supply*
> `schedule*` would reintroduce exactly the attack this theorem removes (with
> `schedule* ≡ 0`, a suffix block signed with a stolen retired-generation key passes the
> pin, and the budget hypothesis silently becomes near-unsatisfiable). What disappeared
> is the **per-certificate dynamic** authentication contract (the floor vector); the
> static parameter contract is the same one every deployment already has for `n` and `G`.`
>
> `Budget read retroactively — see the honest-scope note in
> `KeyStealingScheduleResults.lean` (early windows accumulate later-generation thefts; the
> anchor *hypothesis* is what is removed).`
>
> `Crypto surface: `SchedCoreUnforgeable` (registry EUF-CMA over the **core** scheduled
> validator — see the module doc for the honest accounting of core vs full) + collision
> resistance over the `SignedDeclared` domain. The corruption predicate is `badSched` — a
> pure function of the slot; the two certificates' histories and both suffixes are judged
> by the *same* predicate, which is the anchor-removal device in certificate form. -/`

```lean
theorem sched_recent_certified_suffix_agreement
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    (hUnf : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    (hBudget : ByzantineBounded n (badSched n schedule rented Stolen))
    {cl cl' : CertClaim}
    (hcl  : GroundedCertSched n schedule (SignedDeclared n ops registry) G cl)
    (hcl' : GroundedCertSched n schedule (SignedDeclared n ops registry) G cl')
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hTipS  : (s₁  :: srest ).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink  : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧
        s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hPinS : schedPinned schedule (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip'.slot + 1 → quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hPinS' : schedPinned schedule (s₁' :: srest') = true)
    (hSigned' : ∀ B ∈ s₁' :: srest', SignedDeclared n ops registry B)
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    {i i' : Nat} {B B' : Block}
    (hB  : blockAt? (s₁  :: srest ) i  = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep  : i  + n < (s₁  :: srest ).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B'
```

Its proof route, verbatim in outline (this is the route W1 says it mirrors):
`groundedCertSched_suffix_history` ×2 → `exists_signedChain_of_covered` ×2 →
`validSignedChainSchedCore` reassembly by `rw [validSignedChainSchedCore,
Bool.and_eq_true, Bool.and_eq_true]` ×2 → `List.getLast?_append` for the full-chain tips
→ `List.getElem?_append_right` to relocate `blockAt?` at `c.length + i` →
`hkEq : c'.length + i' = c.length + i := by omega` → close with
`sched_deep_block_agreement_core_of_length hn hUnf hHash hBudget hVal hVal' … (k := c.length + i) …`,
final two goals `rw [hstrip, List.length_append]; omega`.

File ends `end MoltPetit.Model`.

---

## 4. Claims REFUTED or doubted

**None.** The verifier stated no refutation, no doubt, no severity, no caveat. It had
not written a single evaluative sentence when the 429 arrived.

---

## 5. Structured JSON being assembled

**None.** There is no `StructuredOutput` tool_use block in the transcript and no JSON
drafted in assistant text. `partial_output` is empty.

---

## 6. Where it stopped — exact

- **Last tool result** (line 18, `toolu_01NJhgyxJ2fFBVxTCC4HQDUS`): the output of
  `sed -n 470,702p MoltPetit/Model/KeyStealingScheduleCert.lean`, i.e. the remainder of
  `groundedCertSched_history`, all of `groundedCertSched_suffix_history`, and all of
  `sched_recent_certified_suffix_agreement` including its docstring, ending with the
  literal text `end MoltPetit.Model`.
- **Last assistant sentence** (line 5, the only prose in the run):
  *"I'll start by inspecting the repository layout and the key files the design
  references."*
- **Rate-limit record: line 19.** `"type":"assistant"`, `"model":"<synthetic>"`,
  `"content":[{"type":"text","text":"You've hit your session limit · resets 2pm (UTC)"}]`,
  `"error":"rate_limit"`, `"isApiErrorMessage":true`, `"apiErrorStatus":429`,
  `"quotaLimits":{"status":"rejected","resetsAt":1788616800,"rateLimitType":"five_hour",
  "overageStatus":"rejected","overageDisabledReason":"org_level_disabled"}`.
  Line 20 is empty (file terminator).

All four thinking blocks in the transcript (lines 4, 8, 13, 16) are signature-only with
`"thinking":""` — no reasoning text exists to recover.
