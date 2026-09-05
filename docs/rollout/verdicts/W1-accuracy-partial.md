# W1-accuracy — PARTIAL verification (salvaged from a killed subagent)

> **WARNING — PARTIAL.** The verifier was killed by a usage limit (HTTP 429) before it
> emitted any verdict. It produced **no** judgements, **no** confirmations in prose, and
> **no** structured output. Everything below is *evidence it gathered* (tool inputs and
> tool results), transcribed faithfully. Nothing here is a verdict on the design.

| | |
|---|---|
| Agent id | `a8e88b94f9f6d0dde` |
| Transcript | `/run/claude/agent/projects/-etheron-pod/c28ff38c-0cb1-500d-8726-22cd73943085/subagents/workflows/wf_6b051052-ec7/agent-a8e88b94f9f6d0dde.jsonl` |
| Session / workflow | `c28ff38c-0cb1-500d-8726-22cd73943085` / `wf_6b051052-ec7` |
| Model / effort | `claude-fable-5-1`, effort `high` |
| Wall clock | 2026-09-05T09:43:43Z → 09:44:23Z (≈40 s of work) |
| Expected label | **W1-accuracy** |
| Confirmed label | **W1-accuracy** (confirmed from content — see below) |
| Lines seen | 4–25 (22 records); line 26 is empty EOF |
| Lines skipped | 1 (prompt, oversized — not read by instruction), 2, 3 (harness attachments) |
| Where it stopped | after tool result #8 (Soundness/Liveness/Grounded signature check); rate-limit record at **line 25** |
| Structured output | none — no `StructuredOutput` call, no drafted JSON anywhere |

## Label confirmation

The label could not be read off the prompt (line 1 was not read, per instruction), so it is
confirmed from the *content* of the eight tool calls:

* **Work item = W1 (mode 3 lockstep at certificate level).** The only two files opened in
  depth are exactly W1's two ingredients: `MoltPetit/Model/KeyStealingLockstep.lean`
  (mode 3 free-cadence lockstep: `lockstepOk`, `validSignedChainLock`, `lagSched`,
  `LockstepPackage`, `lockstep_declares_rosterGen`, `lockstep_validSignedChainSched`,
  `lockstep_recent_tip_ancestor_agreement/_mem`) and
  `MoltPetit/Model/KeyStealingScheduleCert.lean` (the certificate level it must be lifted
  to: `GroundedCertSched`, `GroundedHistorySched`, `groundedCertSched_history`,
  `groundedCertSched_suffix_history`, `sched_recent_certified_suffix_agreement`), plus the
  shared helper lemmas those two proofs consume.
* **Not W2:** no `keyrot_*_anchored`, no `AcceptedSuffixK`, no `Molt/ClientRule.lean`
  (`Molt/` appears only in the `ls` output, never opened).
* **Not W5:** no `ErasureTimed`, no `NoPrematureTheft`, no per-generation census, no
  `horizon_shared_prefix`; `KeyStealingScheduleTimed.lean` and `KeyStealingHorizon*.lean`
  appear only in the `ls` output.
* **Lens = accuracy.** The single line of assistant prose in the whole transcript is
  *"I'll start by checking the referenced declarations in the repository."*, and every tool
  description is a name/signature existence check ("List declarations in
  KeyStealingLockstep.lean", "Read schedUnforgeable_of_core and GroundedCertSched
  definitions", "Verify Soundness, Liveness, Grounded lemma signatures").
* **Not ordering.** Zero `git` / diff / history commands; no reading of the design
  document's `depends_on` / `enables` claims; no additive-only or file-layout comparison.

## 1. Files examined (in order), with why

| # | Tool | Target and range | Stated purpose |
|---|---|---|---|
| 1 | Bash | `ls` repo root; `ls MoltPetit/Model MoltPetit/Results Molt`; `cat lakefile.toml MoltPetit.lean Molt.lean` | "List repo layout and root modules" (preceded by: *"I'll start by checking the referenced declarations in the repository."*) |
| 2 | Bash | `grep -n "lockstepOk_iff_pairwise\|^theorem\|^lemma\|^def\|^private\|^structure\|^inductive\|^abbrev\|^noncomputable" MoltPetit/Model/KeyStealingLockstep.lean` | "List declarations in KeyStealingLockstep.lean" |
| 3 | Bash | `sed -n 1,120p MoltPetit/Model/KeyStealingLockstep.lean` | "Read lockstep header, lockstepOk, pairwise lemma, validator" |
| 4 | Bash | `sed -n 245,330p` + `sed -n 465,500p` + `sed -n 550,614p` of `MoltPetit/Model/KeyStealingLockstep.lean` | "Read LockstepPackage, pinning theorem, transport, and results statements" |
| 5 | Bash | `sed -n 195,235p` + `sed -n 340,420p` of `MoltPetit/Model/KeyStealingScheduleCert.lean` | "Read schedUnforgeable_of_core and GroundedCertSched definitions" |
| 6 | Bash | `sed -n 420,505p MoltPetit/Model/KeyStealingScheduleCert.lean` | "Read groundedCertSched_history proof body" |
| 7 | Bash | `sed -n 505,702p MoltPetit/Model/KeyStealingScheduleCert.lean` | "Read suffix history and sched cert agreement theorem" |
| 8 | Bash | `grep -n "theorem linksOk_isChain\|theorem strictSlots_of_checks\|theorem blockAt_getLast\|theorem validChain_sound\|theorem exists_blockAt_of_mem\|theorem validChainK_sound" MoltPetit/Model/*.lean`; then `sed -n 30,45p` + `sed -n 70,110p` + `grep -n "theorem validChain_sound" -A 8` of `Soundness.lean`; `sed -n 55,70p` + `sed -n 120,132p` of `Liveness.lean`; `sed -n 50,70p` + `sed -n 215,240p` of `Grounded.lean` | "Verify Soundness, Liveness, Grounded lemma signatures" |

All paths relative to `/etheron-pod/mini-consensus-lean`. Files whose contents were read:

* `MoltPetit/Model/KeyStealingLockstep.lean` — lines 1–120, 245–330, 465–500, 550–614 (whole-file declaration index also obtained)
* `MoltPetit/Model/KeyStealingScheduleCert.lean` — lines 195–235, 340–702
* `MoltPetit/Model/Soundness.lean` — lines 30–45, 70–110, 130–138
* `MoltPetit/Model/Liveness.lean` — lines 55–70, 120–132
* `MoltPetit/Model/Grounded.lean` — lines 50–70, 215–240
* `lakefile.toml`, `MoltPetit.lean`, `Molt.lean` — in full
* Directory listings only: repo root, `MoltPetit/Model/`, `MoltPetit/Results/`, `Molt/`

## 2. Evidence established (would-be confirmations)

The verifier recorded **no** explicit "confirmed" statement. The following are the facts its
tool results put on the record; a fresh verifier can take these as already paid for.

### 2.1 `MoltPetit/Model/KeyStealingLockstep.lean` — complete top-level declaration index

Obtained by grep (exact `file:line`):

```
76:def lockstepOk (n : Nat) : Chain → Bool
84:theorem lockstepOk_iff_pairwise {n : Nat} (c : Chain) :
103:def validSignedChainLock {σ sk pk : Type} (n : Nat)
112:def lagSched (n : Nat) (rosterGen : Nat → Nat) (s : Nat) : Nat :=
120:theorem schedPinned_mono {sched₁ sched₂ : Nat → Nat}
130:theorem schedCore_mono {σ sk pk : Type} {n : Nat} {sched₁ sched₂ : Nat → Nat}
141:theorem schedCoreUnforgeable_mono {n : Nat} {sched₁ sched₂ : Nat → Nat}
154:theorem schedCore0_of_lock {σ sk pk : Type} {n : Nat}
172:private theorem lockstep_rel {n : Nat} {c : Chain} (hS : StrictSlots c)
195:private theorem lockstep_const {n : Nat} {c : Chain} (hS : StrictSlots c)
211:private theorem head_slot_min {c : Chain} (hS : StrictSlots c) {G : Block}
220:private theorem window_producer_inj' {n u s s' : Nat}
252:structure LockstepPackage (n : Nat) (rosterGen : Nat → Nat) {Sig sk pk : Type}
269:theorem LockstepPackage.toPackageA
299:theorem lockstep_declares_rosterGen
474:theorem lockstep_validSignedChainSched
555:theorem lockstep_recent_tip_ancestor_agreement
586:theorem lockstep_recent_tip_ancestor_mem
```

Two facts follow directly from that index (neither was commented on by the verifier):

* `lockstep_rel` (172), `lockstep_const` (195), `head_slot_min` (211) and
  `window_producer_inj'` (220) are declared **`private`**.
* The names W1 proposes to add — `GroundedCertLock`, `lockstepFrom`, `groundedCertLock_*`,
  `lockstep_recent_certified_suffix_agreement` — **do not occur** in this index. No
  repo-wide grep for those names was ever run (see §5 gaps).

### 2.2 Exact declarations read out of `KeyStealingLockstep.lean`

`lockstepOk` (line 76) — the no-mixing rule, verbatim:

```lean
def lockstepOk (n : Nat) : Chain → Bool
  | [] => true
  | b :: rest =>
      rest.all (fun b' =>
        decide ((b.slot / n = b'.slot / n → b.keyIndex = b'.keyIndex) ∧
          b.keyIndex ≤ b'.keyIndex))
      && lockstepOk n rest
```

`lockstepOk_iff_pairwise` (line 84):

```lean
theorem lockstepOk_iff_pairwise {n : Nat} (c : Chain) :
    lockstepOk n c = true ↔
      c.Pairwise (fun a b => (a.slot / n = b.slot / n → a.keyIndex = b.keyIndex) ∧
        a.keyIndex ≤ b.keyIndex)
```

`validSignedChainLock` (line 103) — note the type binders are `{σ sk pk : Type}` (not
`Sig`), and the structural component is `validChainK`, not `validChain`:

```lean
def validSignedChainLock {σ sk pk : Type} (n : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChainK n (stripSigs sc)
    && lockstepOk n (stripSigs sc)
```

`lagSched` (line 112):

```lean
def lagSched (n : Nat) (rosterGen : Nat → Nat) (s : Nat) : Nat :=
  rosterGen (s / n - 1)
```

`LockstepPackage` (line 252) — full field list:

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

`LockstepPackage.toPackageA` (line 269) — conclusion `PackageA n (lagSched n rosterGen) ops
registry rented Stolen honestSigned now Δ G R T`; body shows `PackageA` has exactly the five
fields `unforgeable, hashInj, rentBound, exposedBound, budget_le`, with
`unforgeable := schedCoreUnforgeable_mono (fun _ => Nat.zero_le _) hP.unforgeable`.

`lockstep_declares_rosterGen` (line 299) — the pinning theorem, full hypothesis list:

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

Proof shape seen: `classical`; destructures `validSignedChainLock` into
`⟨⟨hSigs, hVK⟩, hLock⟩`; `hVC : ValidChain n (stripSigs sc) := (validChainK_sound hVK).1`;
`obtain ⟨hSeq, hS, hPL, hDense⟩ := hVC`; `head_slot_min`; `induction W using Nat.strongRecOn`.

`lockstep_validSignedChainSched` (line 474) — same hypotheses (`hn`, `hP`, `hVal`, `hHead`,
`hRecent`), conclusion `validSignedChainSched n (lagSched n rosterGen) ops registry sc = true`.

`lockstep_recent_tip_ancestor_agreement` (line 555) — hypotheses `hn`, `hP`, `hVal`, `hVal'`,
`hHead`, `hHead'`, `hTipS`, `hTipS'`, `hRecent`, `hRecent'`, `hLong : n < (stripSigs sc).length`,
`hLong'`, `hTipHeight : sTip.height = sTip'.height`, `hB`, `hB'` at index
`(stripSigs sc).length - 1 - n`; conclusion `B = B'`; proved by
`packageA_recent_tip_ancestor_agreement hn hP.toPackageA (lockstep_validSignedChainSched …) …`.

`lockstep_recent_tip_ancestor_mem` (line 586) — same but `hLe : sTip.height ≤ sTip'.height`,
conclusion `∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B`;
proved by `sched_recent_tip_ancestor_mem hn (schedUnforgeable_of_core hP.toPackageA.unforgeable)
hP.hashInj (packageA_byzantine_bounded hP.toPackageA) …`. File ends `end MoltPetit.Model`.

Module docstring (lines 1–70) states its own honest scope, verbatim excerpts:

* "The package's budget field is `exposedBound` at the lagged schedule — the **cumulative**
  census, exactly `PackageA`'s shape. The distinctive per-generation census
  (`erasure_freeze` as the load-bearing bound) is **not** delivered … Earning the
  per-generation reading is the D1′-full increment."
* "The EUF-CMA surface is assumed at the **weakest** validator (`SchedCoreUnforgeable` at the
  constant-0 schedule) so that its scope covers lockstep-accepted chains without
  circularity … `schedCoreUnforgeable_mono` then delivers it wherever the transport needs it."
* "`rosterGen` itself is a genuine extra hypothesis relative to `PackageA`."
* The validator "takes **no schedule input**: the verifier never learns when the roster
  advanced, and the client still holds only genesis and a clock."

### 2.3 Exact declarations read out of `KeyStealingScheduleCert.lean`

(Line numbers marked ≈ are derived from the `sed` windows, ±2.)

`SchedCoreUnforgeable` (≈ line 200):

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
```

`schedUnforgeable_of_core` (≈ line 216): `SchedCoreUnforgeable … → SchedUnforgeable n schedule
ops registry rented Stolen honestSigned now Δ`, body
`⟨fun hVal hmem hRecent hverify hrent hstolen => h.unforgeable (schedCore_of_validSignedChainSched hVal) …⟩`.
`honestSlotsUnique_schedCore` exists at ≈ line 231.

A `_of_length` deep-agreement wrapper ends at ≈ line 353 with conclusion `B = B'` from
`{k : Nat} {B B'} (hB) (hB') (hLen : k + n < (stripSigs sc).length) (hLen')`, proved by
`sched_deep_block_agreement_core hn hUnf hHash hBudget hVal hVal' hHead hHead' hRecent hRecent'
hB hB' hD hD' (Nat.le_refl _) (Nat.le_refl _)`. Its name is confirmed by the call site in
`sched_recent_certified_suffix_agreement`: **`sched_deep_block_agreement_core_of_length`**.

`GroundedCertSched` (≈ line 371) — the certificate inductive, verbatim:

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
```

Its docstring: "the fold threads **no floor**: the pin is computed from the block's own slot.
The certificate state is exactly the plain (`GroundedCert`) state; contrast `GroundedCertK`,
whose folds gate on (and step) a per-producer floor vector." Deployment note: "the genesis
constructor requires `Signed G` and the slot-0 pin `schedule G.slot ≤ G.keyIndex` — the
deployment genesis must carry a verifying registry signature at its declared version
(`sigsOk` has no genesis exemption)."

`GroundedHistorySched` (≈ line 396) — fields `valid : validChain n c = true`,
`pinned : schedPinned schedule c = true`, `head : blockAt? c 0 = some G`,
`tip : ∃ t : Block, c.getLast? = some t ∧ t.id = cl.tipId ∧ t.slot = cl.tipSlot ∧ t.height = cl.tipHeight`,
`tail_eq : cl.tail = c.filter fun x => decide (cl.tipSlot + 2 - n ≤ x.slot)`,
`len_eq : c.length = cl.tipHeight + 1`, `signed : ∀ B ∈ c, Signed B`.

`groundedCertSched_history` (≈ line 409):
`{n : Nat} (hn : 1 ≤ n) {schedule} {Signed} {G} {cl} (h : GroundedCertSched n schedule Signed G cl)
: ∃ c : Chain, GroundedHistorySched n schedule Signed G cl c`. Proof body read in full
(lines 420–497): genesis case discharges `maturedWindowsDense n [G] G.slot`, `schedPinned`,
and `length` from `genesisOk → G.height = 0`; extend case uses `childOk`, `validChain_sound`,
`blockAt_getLast`, `windowCount_mono`, `windowCount_append`, `windowCount_filter_low`,
`validChain_append_one`, `List.all_append` (pin propagation), `List.getElem?_append_left`
(head preservation), `List.filter_append`/`filter_filter`/`filter_congr` (tail re-filtering).

`groundedCertSched_suffix_history` (≈ lines 501–573):

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

Docstring: "the suffix-side rotation check is the **pin alone** (`schedPinned` over the suffix
— computable from each block's own slot), replacing the default certificate's `keyMonoFrom`
against a carried floor snapshot." Proof uses `groundedCertSched_history`, `validChain_sound`,
`blockAt_getLast`, `strictSlots_of_checks (linksOk_isChain hLinks)`, `slot_le_tip_of_mem`,
`windowCount_mono/_append/_filter_low`, `validChain_append_suffix`.

`sched_recent_certified_suffix_agreement` (within lines 505–702; last theorem in the file,
followed by `end MoltPetit.Model`) — the certificate-level headline whose lockstep analogue
W1 proposes. Full hypothesis list as read:

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
    (hLink  : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hPinS : schedPinned schedule (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B)
    (hLink' …) (hLinks' …) (hDense' …) (hPinS' …) (hSigned' …)
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

Proof skeleton (the template a lockstep analogue would mirror): two calls to
`groundedCertSched_suffix_history`; two calls to `exists_signedChain_of_covered`; assemble
`validSignedChainSchedCore` from `⟨⟨hsigs, hV⟩, hPin⟩`; `List.getLast?_append` for recent tips;
`List.getElem?_append_right` to re-index blocks at global height; finish with
`sched_deep_block_agreement_core_of_length hn hUnf hHash hBudget hVal hVal' … (k := c.length + i)`.

Its docstring records the three promised simplifications ("No floor snapshot", "Global budget
— `hBudget` is a single chain-independent hypothesis; `badSched` reads no chain, so the default
theorem's quantification over every attestable history (`AttestedHistoryK`) has nothing to range
over", "No `Δconf`"), the light-client cost ("`O(n)` blocks: claim (tip data + tail of `≤ n−1`
blocks), suffix, and a clock — with `schedule` a public protocol parameter (e.g. `fun s => s / R`),
not wire data"), and the **residual static contract**: "one `schedule` binder couples the
certificate derivation (`hcl`), the suffix pin (`hPinS`), the EUF-CMA surface (`hUnf`), and the
budget (`hBudget`) … a verifier that let a certificate or peer *supply* `schedule*` would
reintroduce exactly the attack this theorem removes (with `schedule* ≡ 0`, a suffix block signed
with a stolen retired-generation key passes the pin, and the budget hypothesis silently becomes
near-unsatisfiable)."

### 2.4 Reused helper lemmas — existence, exact `file:line`, exact signature

Grep over `MoltPetit/Model/*.lean` returned exactly one hit per name (no duplicates):

```
MoltPetit/Model/KeyIndex.lean:215:theorem validChainK_sound {n : Nat} {c : Chain} (h : validChainK n c = true) :
MoltPetit/Model/Model.lean:71:theorem exists_blockAt_of_mem {c : Chain} {B : Block} (hB : B ∈ c) :
MoltPetit/Model/Soundness.lean:36:theorem linksOk_isChain :
MoltPetit/Model/Soundness.lean:74:theorem strictSlots_of_checks {ch : Chain}
MoltPetit/Model/Soundness.lean:97:theorem blockAt_getLast {ch : Chain} {tip : Block}
MoltPetit/Model/Soundness.lean:130:theorem validChain_sound {n : Nat} :
```

Full statements as read:

* `Soundness.lean:36` — `theorem linksOk_isChain : ∀ {ch : Chain}, linksOk ch = true → List.IsChain (fun a b => childOk a b = true) ch`
* `Soundness.lean:74` — `theorem strictSlots_of_checks {ch : Chain} (hChain : List.IsChain (fun a b => childOk a b = true) ch) : StrictSlots ch`
* `Soundness.lean:97` — `theorem blockAt_getLast {ch : Chain} {tip : Block} (hTip : ch.getLast? = some tip) : blockAt? ch (ch.length - 1) = some tip`
* `Soundness.lean:130` — `theorem validChain_sound {n : Nat} : ∀ {ch : Chain}, validChain n ch = true → ValidChain n ch`
* also seen nearby: `childOk_iff {p b : Block} : childOk p b = true ↔ b.height = p.height + 1 ∧ p.slot < b.slot ∧ b.prev = some p.id`; `parentLinked_of_checks`; `maturedDense_of_check {n} {ch} (hS : StrictSlots ch) {tip} (hTip : ch.getLast? = some tip) (hCheck : maturedWindowsDense n ch tip.slot = true) : MaturedWindowsDense n ch`
* `Liveness.lean` ≈58 — `theorem windowCount_mono {u len : Nat} {c c' : Chain} (h : c.Sublist c') : windowCount c u len ≤ windowCount c' u len`
* `Liveness.lean` ≈63 — `theorem slot_le_tip_of_mem {c : Chain} (hS : StrictSlots c) {tip : Block} (hTip : c.getLast? = some tip) {x : Block} (hx : x ∈ c) : x.slot ≤ tip.slot`
* `Liveness.lean` ≈123 — `theorem validChain_append_one {n : Nat} {c : Chain} {b tip : Block} (hValid : validChain n c = true) (hTipEq : c.getLast? = some tip) (hChild : childOk tip b = true) (hAllDense : ∀ u : Nat, u + n ≤ b.slot + 1 → windowDense n (c ++ [b]) u = true) : validChain n (c ++ [b]) = true`
* `Grounded.lean` ≈55 — `theorem windowCount_append (a b : Chain) (u len : Nat) : windowCount (a ++ b) u len = windowCount a u len + windowCount b u len`
* `Grounded.lean` ≈60 — `theorem windowCount_filter_low {lo u : Nat} (hlo : lo ≤ u) (c : Chain) (len : Nat) : windowCount (c.filter fun x => decide (lo ≤ x.slot)) u len = windowCount c u len`
* `Grounded.lean` ≈222 — `theorem validChain_append_suffix {n : Nat} {sTipSlot : Nat} {full : Chain} (hDense : ∀ u, u + n ≤ sTipSlot + 1 → quorum n ≤ windowCount full u n) : ∀ (suffix c : Chain) (t : Block), full = c ++ suffix → validChain n c = true → c.getLast? = some t → linksOk (t :: suffix) = true → (∀ x ∈ suffix, x.slot ≤ sTipSlot) → validChain n full = true`

### 2.5 Repository layout and build facts

* `MoltPetit/Model/` contains: `Definitions, Grounded, KeyIndex, KeyRotation,
  KeyRotationLiveness, KeyRotationTests, KeyStealing, KeyStealingBudget, KeyStealingCert,
  KeyStealingHorizon, KeyStealingHorizonCore, KeyStealingLockstep, KeyStealingLongRange,
  KeyStealingSafety, KeyStealingSchedule, KeyStealingScheduleBudget, KeyStealingScheduleCert,
  KeyStealingScheduleHorizon, KeyStealingScheduleTimed, KeyStealingUnique, Liveness, Model,
  Safety, Soundness, Timed, TimedSig` (`.lean`).
* `MoltPetit/Results/`: `Axioms, KeyStealingResults, KeyStealingScheduleResults, Results`.
* `Molt/`: `Assumptions, Axioms, ClientRule, Liveness, MaxSync, Protocol, Results, Rotation, Verifier`.
* Repo-root design docs present: `LOCKSTEP_DESIGN.md`, `KEY_INDEX_DESIGN.md`,
  `KEY_ROTATION_SOUND.md`, `HANDOFF_SCHEDULE_VARIANT.md`, `PHASE2_DESIGN.md`,
  `ROTATION_MODES.md`, `docs/rollout/ROLLOUT_NOTES.md`.
* `MoltPetit.lean` import frontier (order matters for any new module): `… KeyStealingSchedule,
  Results.KeyStealingScheduleResults, KeyStealingScheduleCert, KeyStealingScheduleBudget,
  KeyStealingScheduleHorizon, KeyStealingLockstep, KeyStealingHorizonCore, KeyStealingHorizon,
  KeyStealingScheduleTimed, KeyRotationTests, Results.Axioms, MoltPetit.Custody`.
* `KeyStealingLockstep.lean` imports only `MoltPetit.Model.KeyStealingScheduleBudget` and
  `MoltPetit.Results.KeyStealingScheduleResults`.
* `lakefile.toml`: `name = "MoltPetit"`, `defaultTargets = ["MoltPetit", "Rust", "Thales", "Molt"]`,
  `relaxedAutoImplicit = false`, `weak.linter.mathlibStandardSet = true`,
  `maxSynthPendingDepth = 3`, mathlib `v4.30.0-rc2`, aeneas pinned at
  `bf13c42e7c34d07fc396baffad39c93023b12914`, `lean_exe moltpetit-demo` root `Main`.

## 3. Claims refuted or doubted

**None recorded.** The verifier wrote no prose after its opening sentence and left no
thinking text (all thinking blocks are signature-only). No severity was ever stated.

## 4. Structured JSON in progress

**None.** No `StructuredOutput` tool call was made and no JSON was drafted in assistant text.

## 5. Where it stopped, and what was left undone

* Last successful tool result: **line 24**, the `Soundness` / `Liveness` / `Grounded`
  signature check (tool call #8, `toolu_01JV68brfUohnAYQnwA1rnSC`).
* Last assistant prose in the whole transcript: **"I'll start by checking the referenced
  declarations in the repository."** (line 5) — nothing after it but tool calls.
* Rate-limit record: **line 25**, synthetic assistant message
  `"You've hit your session limit · resets 2pm (UTC)"`, `error: "rate_limit"`,
  `apiErrorStatus: 429`, `rateLimitType: "five_hour"`, `resetsAt: 1788616800`,
  timestamp `2026-09-05T09:44:23.224Z`. Line 26 is empty.

Not done (offered as a to-do list, not as findings):

1. The design document itself was **never opened** — `LOCKSTEP_DESIGN.md` was seen only in the
   `ls` output. Every check so far is repo-side; none is design-side.
2. No repo-wide grep for the W1 new names (`GroundedCertLock`, `lockstepFrom`,
   `groundedCertLock_*`, `lockstep_recent_certified_suffix_agreement`), so the
   "no new theorem duplicates an existing one" half of the accuracy lens is unstarted
   outside `KeyStealingLockstep.lean`'s own declaration index.
3. `KeyStealingCert.lean` (the default/floor certificate — `GroundedCertK`,
   `groundedCertK_history`, `groundedCertK_suffix_history`,
   `keyrot_recent_certified_suffix_agreement`) was never opened, though the ScheduleCert
   docstrings repeatedly cite it as the thing being mirrored.
4. `KeyStealingLockstep.lean` lines 120–245, 330–465, 500–550 were not read — i.e.
   `schedPinned_mono`, `schedCore_mono`, `schedCoreUnforgeable_mono`, `schedCore0_of_lock`
   and the four `private` helpers were seen only as grep headers, never as statements.
5. `Results/KeyStealingScheduleResults.lean` (the "honest-scope note" on the retroactive
   budget read, cited by the headline docstring) was never opened.
