# W2 / "ordering" — PARTIAL verification salvage (no verdict was ever returned)

> **WARNING — PARTIAL.** The verifier was killed by a usage limit (HTTP 429) after 8 tool
> calls and before it wrote a single word of judgement. It never returned a verdict, never
> called `StructuredOutput`, and never drafted JSON. Everything below is *evidence it
> gathered*, reproduced from its tool results. **Nothing below is an adjudication** — the
> salvage agent added no judgements of its own.

| | |
|---|---|
| Agent id | `a2b07dddf4e929a26` |
| Transcript | `/run/claude/agent/projects/-etheron-pod/c28ff38c-0cb1-500d-8726-22cd73943085/subagents/workflows/wf_6b051052-ec7/agent-a2b07dddf4e929a26.jsonl` |
| Workflow | `wf_6b051052-ec7`, session `c28ff38c-0cb1-500d-8726-22cd73943085`, cwd `/etheron-pod` |
| Expected label | **W2-ordering** |
| Confirmed label | **W2 — confirmed from content. Lens: NOT confirmable** (see below) |
| Lines seen | 4–29 (26 lines) |
| Lines skipped | 1, 2, 3 (per instruction: prompt + harness attachments; not read) |
| Wall clock | first assistant message 2026-09-05T09:43:08Z → rate limit 2026-09-05T09:44:38Z (~90 s) |
| Where it stopped | line 29, synthetic assistant message `"You've hit your session limit · resets 2pm (UTC)"`, `"error":"rate_limit"`, `"apiErrorStatus":429`, `requestId req_011Cek5S6gHW3f2bfoH6JWZS`, `rateLimitType: five_hour`, `resetsAt 1788616800` |
| Assistant prose in the entire transcript | one sentence, line 5: *"I'll start by opening the key files the design cites."* |
| Thinking blocks | all empty (signature-only) — no recoverable reasoning |

## Label confirmation

**Work item W2: CONFIRMED** by the file selection and the greps. The eight Bash calls target
exactly the W2 surface — mode 1 anchored trailing-5n, at the certificate level — and nothing
of W1 (`GroundedCertLock` / `lockstepFrom`) or W5 (`ErasureTimed` / `NoPrematureTheft` /
per-generation census) was opened for its own sake:

- `MoltPetit/Model/KeyStealingCert.lean` read three times (header, 240–260, 440–700, 300–360):
  `GroundedCertK`, `groundedCertK_history`, `groundedCertK_suffix_history`, `AttestedHistoryK`,
  `SignedDeclared`, `exists_signedChain_of_covered`, `keyrot_recent_certified_suffix_agreement`
  — the mode-1 **certificate** layer.
- `MoltPetit/Model/KeyStealingHorizon.lean` 1–320: `keyrot_recent_tip_ancestor_agreement_anchored`,
  `keyrot_recent_tip_ancestor_mem_anchored` — the mode-1 **anchored** layer.
- `Molt/ClientRule.lean` (whole file) and `Molt/MaxSync.lean`: `stay_recent_client_safe`,
  `sync_rule`, `sync_rule_mem`, `max_sync_period` — the **trailing-5n** client rules that W2's
  `cert_stay_recent_client_safe` / `cert_sync_rule` mirror.
- Two greps aimed at W2's proposed *new* names: `grep -rn "keyStealingSigned_of_declared\|AttestedHistoryK\|AcceptedSuffix"`
  (i.e. `AcceptedSuffixK`) and `grep -rn "anchored" ... | grep "theorem\|def \|alias\|abbrev"`.

The single most on-the-nose corroboration is a docstring it pulled out of `Molt/Rotation.lean`
(≈ line 305), which states the exact gap W2 proposes to close:

> "Mode 1's certificate-level safety: the agreement of `client_refresh_rule`'s family at the
> certificate presentation, with the floor carried as a snapshot in the claim — **under the
> global, all-window budget (the anchored, trailing-window form is future work at this
> presentation).**"

**Lens: not confirmable from the transcript.** No assistant prose, no thinking text, and no
verdict text ever states the lens. The observed activity is compatible with both lenses and is,
if anything, weighted toward *accuracy*-flavoured work (it read full hypothesis lists of every
reused lemma and grepped their `file:line`). Ordering-lens-specific work is nonetheless present:
the two "does this name already exist anywhere else" greps (no-duplication / additive check), the
reading of both axiom-guard files (`Molt/Axioms.lean`, `MoltPetit/Results/Axioms.lean`) whose
idiom is *"Extend this file with every new headline theorem"*, and the enumeration of the whole
`Molt` `abbrev`/`alias`/`_eq_core` bridging layer (file-layout idiom). Treat the lens as
**unverified but not contradicted**.

*(Context, not from the transcript: the design under review is presumably
`/etheron-pod/rollout-work/designs/W2.md` + `W2.json`, 2026-09-05 09:39–09:42.)*

---

## 1. Files examined, in order

All commands ran with `cd /etheron-pod/mini-consensus-lean`. Descriptions are the verifier's own
`description` field, verbatim.

| # | Line | Files / ranges | Description (verbatim) |
|---|------|----------------|------------------------|
| 1 | 6→7 | `MoltPetit.lean` (whole), `Molt.lean` (whole), `lakefile.toml` (whole), `ls MoltPetit/Model MoltPetit/Results Molt` | "Show root modules, lakefile, and directory listings" |
| 2 | 9→10 | `MoltPetit/Model/KeyStealingCert.lean` 1–60, 240–260, 440–700 | "Read KeyStealingCert header, reconstruction lemma, and certificate theorem" |
| 3 | 12→13 | `MoltPetit/Model/KeyStealingHorizon.lean` 1–210 | "Read KeyStealingHorizon anchored theorem" |
| 4 | 15→16 | `KeyStealingHorizon.lean` 210–320; `KeyStealingHorizonCore.lean` 225–335; `KeyStealingScheduleHorizon.lean` 130–200; `KeyStealingUnique.lean` 40–80 and 180–200 | "Read anchored core lemmas and horizon_shared_prefix" |
| 5 | 18→19 | `grep -n` for 21 declaration names over `MoltPetit/Model/*.lean` + `MoltPetit/Results/*.lean`; `Model/Liveness.lean` 58–72; `Model/Soundness.lean` 92–104; `Model/KeyRotation.lean` (`validChainK'_sound` +8, `validSignedChainK'` +5) | "Locate cited lemma line numbers and read small helpers" |
| 6 | 21→22 | `Molt/ClientRule.lean` (whole, `cat -n`, 341 lines); `Molt/Rotation.lean` 170–330 | "Read Molt ClientRule and Rotation" |
| 7 | 24→25 | `Molt/Axioms.lean` (whole, `cat -n`, 162 lines); `MoltPetit/Results/Axioms.lean` 1–20, 285–312, 588–602; `grep -n` for `abbrev`/`alias`/`_eq_core`/etc. over `Molt/Results.lean Molt/Assumptions.lean Molt/Verifier.lean Molt/Protocol.lean Molt/Rotation.lean` | "Read guard files and Molt bridging abbrevs" |
| 8 | 27→28 | `Molt/MaxSync.lean` 1–60, 90–260; `MoltPetit/Results/KeyStealingResults.lean` 240–300; `MoltPetit/TS/Bridge.lean` 490–530; `Molt/Assumptions.lean` 60–92; `grep -rn "anchored"` (excluding the two Horizon files); `grep -rn "keyStealingSigned_of_declared\|AttestedHistoryK\|AcceptedSuffix"` (excluding `KeyStealingCert.lean`); `KeyStealingCert.lean` 300–360 | "Read MaxSync, deep_block_agreement_of_length, TS bridge, and grep for existing anchored/attested names" |

Never opened: `KeyStealingLockstep.lean`, `KeyStealingScheduleTimed.lean`, `Molt/Liveness.lean`,
`Molt/Protocol.lean`/`Verifier.lean`/`Results.lean` beyond the grep, `KeyStealingBudget.lean`,
`KeyStealingScheduleCert.lean` (only surfaced via grep), any `Rust/` or `Thales/` target.

---

## 2. Facts established (the expensive part) — evidence in hand, no verdict attached

The verifier issued **no** positive confirmations in prose. What follows is the raw material it
had assembled at the moment it died, reproduced near-verbatim from its tool results. A fresh
verifier can take these as already paid for.

### 2.1 Name/`file:line` index (from the call-5 grep, verbatim output)

```
MoltPetit/Model/KeyRotation.lean:122:theorem validChainK'_sound {n Δconf : Nat} {c : Chain}
MoltPetit/Model/KeyRotation.lean:385:def validSignedChainK' {σ sk pk : Type} (n Δconf : Nat)
MoltPetit/Model/KeyStealingCert.lean:234:def SignedDeclared {Sig sk pk : Type} (n : Nat) (ops : SigOps Sig sk pk)
MoltPetit/Model/KeyStealingCert.lean:247:theorem exists_signedChain_of_covered {Sig sk pk : Type} {n : Nat}
MoltPetit/Model/KeyStealingCert.lean:315:inductive GroundedCertK (n : Nat) (Signed : Block → Prop) (G : Block) :
MoltPetit/Model/KeyStealingCert.lean:462:theorem groundedCertK_suffix_history {n : Nat} (Δconf : Nat) (hn : 1 ≤ n)
MoltPetit/Model/KeyStealingCert.lean:541:def AttestedHistoryK {Sig sk pk : Type} (n Δconf : Nat) (ops : SigOps Sig sk pk)
MoltPetit/Model/KeyStealingCert.lean:583:theorem keyrot_recent_certified_suffix_agreement
MoltPetit/Model/KeyStealingHorizon.lean:134:theorem keyrot_recent_tip_ancestor_agreement_anchored
MoltPetit/Model/KeyStealingHorizonCore.lean:258:theorem honestSlotsUnique_keyrot_anchored
MoltPetit/Model/KeyStealingScheduleHorizon.lean:161:theorem horizon_shared_prefix
MoltPetit/Model/KeyStealingUnique.lean:54:theorem chainInRecord_left {σ : Type} {sc sc' : SignedChain σ} :
MoltPetit/Model/KeyStealingUnique.lean:70:theorem idInjective_keyrot {σ : Type} {sc sc' : SignedChain σ}
MoltPetit/Model/KeyStealingUnique.lean:184:theorem versionedUnforgeable_of_keyStealingEUFCMA
MoltPetit/Model/Liveness.lean:63:theorem slot_le_tip_of_mem {c : Chain} (hS : StrictSlots c) {tip : Block}
MoltPetit/Model/Model.lean:47:theorem strictSlots_lt {c : Chain} (hS : StrictSlots c)
MoltPetit/Model/Model.lean:71:theorem exists_blockAt_of_mem {c : Chain} {B : Block} (hB : B ∈ c) :
MoltPetit/Model/Soundness.lean:97:theorem blockAt_getLast {ch : Chain} {tip : Block}
MoltPetit/Results/KeyStealingResults.lean:250:theorem keyrot_deep_block_agreement_of_length
```

Every one of the 21 names the verifier grepped for that could exist, did — with the exception of
names it deliberately expected to be absent (§2.6). Also located in the same call:
`MoltPetit/Model/Liveness.lean:58 windowCount_mono`, `MoltPetit/Model/KeyRotation.lean:19`
(docstring mentioning `validChainK'_sound`), and `KeyRotation.lean` `validChainK'_pinned`
immediately after `validSignedChainK'`.

Additional `file:line` from the call-7 grep over `Molt/`:

```
Molt/Protocol.lean:27:def faultBudget (n : Nat) : Nat := (n - 1) / 3
Molt/Protocol.lean:111:theorem faultBudget_eq_core : faultBudget = MoltPetit.Model.maxByzantine := rfl
Molt/Results.lean:39:def blockAt? (c : Chain) (h : Nat) : Option Block := getElem? c h
Molt/Results.lean:42:theorem blockAt?_eq_core : blockAt? = MoltPetit.Model.blockAt? := rfl
Molt/Verifier.lean:35:def stripSigs {σ : Type} (sc : SignedChain σ) : Chain :=
Molt/Verifier.lean:61:abbrev CertClaim := MoltPetit.Model.CertClaim
Molt/Verifier.lean:147:theorem stripSigs_eq_core {σ : Type} :
Molt/Verifier.lean:164:theorem validSuffix_eq_core {α σ sk pk : Type} :
Molt/Verifier.lean:177:theorem validCertifiedChain_eq_core {α σ sk pk : Type} :
Molt/Assumptions.lean:59:abbrev GroundedCert := @MoltPetit.Model.GroundedCert
Molt/Rotation.lean:108:abbrev KeyStealingEUFCMA := @MoltPetit.Model.KeyStealingEUFCMA
Molt/Rotation.lean:112:abbrev KeyStealingSigned := @MoltPetit.Model.KeyStealingSigned
Molt/Rotation.lean:137:abbrev SignedDeclared := @MoltPetit.Model.SignedDeclared
Molt/Rotation.lean:196:theorem validSignedChainK'_eq_core {σ sk pk : Type} :
Molt/Rotation.lean:308:alias keyrot_recent_certified_suffix_agreement :=
Molt/Rotation.lean:314:abbrev GroundedCertK := @MoltPetit.Model.GroundedCertK
Molt/Rotation.lean:343:alias lockstep_recent_tip_ancestor_mem :=
Molt/Rotation.lean:348:alias same_block_same_prefix := MoltPetit.Model.same_block_same_prefix
```

### 2.2 The anchored core (mode 1) — full hypothesis lists, verbatim

`MoltPetit/Model/KeyStealingHorizon.lean:134` — the anchored budget shape W2 must reuse:

```lean
theorem keyrot_recent_tip_ancestor_agreement_anchored
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
    (hRecent  : now ≤ sTip.slot  + Δ)  (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)  (hLong' : n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B'
```

Note: the `hHash` domain here is `KeyStealingSigned n ops registry` (**not** `SignedDeclared`),
and blockwise genesis-or-signed coverage is discharged internally by
`keyStealingSigned_of_mem hVal` — i.e. from the validator, not from a hypothesis.

Companion, same file (≈ line 218, statement read in call 4):
`keyrot_recent_tip_ancestor_mem_anchored` — identical hypotheses except `hLe : sTip.height ≤
sTip'.height` replaces `hTipHeight`, only `hB` is supplied, conclusion
`∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B`.

`MoltPetit/Model/KeyStealingHorizonCore.lean:258` — the uniqueness engine underneath:

```lean
theorem honestSlotsUnique_keyrot_anchored
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    … (hUnf : VersionedUnforgeable n Δconf ops registry rented Stolen honestSigned now Δ)
    {sc sc' : SignedChain Sig} {A : Block}
    (hA  : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    (hBudgetFrom : ∀ u, A.slot + 1 ≤ u + n →
      (badSlotsIn (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) u n).card
        ≤ maxByzantine n)
    (hId : IdInjective (chainUnionRecord sc sc'))
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    (hRecent  : ∃ t,  (stripSigs sc ).getLast? = some t ∧ now ≤ t.slot + Δ)
    (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ) :
    HonestSlotsUnique (badKeyrotOn n Δconf rented Stolen (stripSigs sc))
      (chainUnionRecord sc sc')
```

Its docstring: *"If both chains carry one shared block `A` … honest-slot uniqueness holds with the
corruption budget consulted **only on windows ending after `A.slot`**: for slots at or below the
anchor, the two chains are literally the same list (`same_block_same_prefix` from `A`), so no
budget, no crypto, and no honesty is consumed there. … the anchor may be **arbitrarily old** …
With `A :=` genesis it degenerates to the global-budget form."*

`MoltPetit/Model/KeyStealingScheduleHorizon.lean:161` — the shared contraction both anchored forms
call, validator-agnostic:

```lean
theorem horizon_shared_prefix
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hHonest : HonestSlotsUnique bad record) (hId : IdInjective record)
    {c c' : Chain} (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hle : tip.slot ≤ tip'.slot)
    (hBudgetU : (badSlotsIn bad (tip.slot + 1 - n) n).card ≤ maxByzantine n)
    {k : Nat} (hkdeep : k + n < c.length) :
    ∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P
```

Docstring: *"No hypothesis touches any window below `u`, and no shared genesis is assumed."*

`KeyStealingHorizon.lean` header, on what does and does not transport (relevant to any
depends_on/enables claim): *"What does **not** transport from the scheduled variant is the budget
contraction `ByzantineBoundedFrom`: mode 1's `badKeyrotOn` is chain-relative, so the
slot-induction must still reconcile `inForce` across the two chains … Chain-independence of
`badSched` is load-bearing upstream in `honestSlotsUnique_sched`, not inside the horizon core —
which is why the core transports here verbatim and the budget contraction does not."* Also:
*"these statements are strictly **stronger** than their `KeyStealingSafety`/`KeyStealingResults`
counterparts, which they therefore subsume rather than replace (the `2n` forms remain true and are
kept)."*

### 2.3 The certificate layer (mode 1) — full statements

`MoltPetit/Model/KeyStealingCert.lean:315` — `GroundedCertK`, two constructors, verbatim:

```lean
inductive GroundedCertK (n : Nat) (Signed : Block → Prop) (G : Block) :
    CertClaim → (Nat → Nat) → Prop
  | genesis :
      genesisOk G = true → G.slot = 0 → Signed G →
      GroundedCertK n Signed G
        { tipId := G.id, tipSlot := G.slot, tipHeight := G.height
        , tail := [G].filter fun x => decide (G.slot + 2 - n ≤ x.slot) }
        (fun i => if producerForSlot n G.slot = i then max 0 G.keyIndex else 0)
  | extend (cl : CertClaim) (fl : Nat → Nat) (b : Block) :
      GroundedCertK n Signed G cl fl →
      b.height = cl.tipHeight + 1 → cl.tipSlot < b.slot → b.prev = some cl.tipId →
      Signed b →
      fl (producerForSlot n b.slot) ≤ b.keyIndex →
      (∀ u : Nat, cl.tipSlot + 2 ≤ u + n → u + n ≤ b.slot + 1 →
        quorum n ≤ windowCount (cl.tail ++ [b]) u n) →
      GroundedCertK n Signed G
        { tipId := b.id, tipSlot := b.slot, tipHeight := b.height
        , tail := (cl.tail ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot) }
        (fun i => if producerForSlot n b.slot = i then max (fl i) b.keyIndex else fl i)
```

`GroundedHistoryK` (structure, immediately after): fields `valid : validChainK n c = true`,
`head : blockAt? c 0 = some G`, `tip : ∃ t, c.getLast? = some t ∧ t.id = cl.tipId ∧ t.slot =
cl.tipSlot ∧ t.height = cl.tipHeight`, `tail_eq`, `len_eq : c.length = cl.tipHeight + 1`,
`signed : ∀ B ∈ c, Signed B`, `floors : ∀ i, keyFloor n c i = fl i`.
`groundedCertK_history {n} (hn : 1 ≤ n) … (h : GroundedCertK n Signed G cl fl) : ∃ c : Chain,
GroundedHistoryK n Signed G cl fl c`.

`KeyStealingCert.lean:462` — `groundedCertK_suffix_history`, the prefix+suffix bridge, hypotheses
verbatim: `(Δconf : Nat) (hn : 1 ≤ n)`, `hG : GroundedCertK n Signed G cl fl`,
`hTipS : (s₁ :: srest).getLast? = some sTip`,
`hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId`,
`hLinks : linksOk (s₁ :: srest) = true`,
`hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n`,
`hMono : keyMonoFrom n fl (s₁ :: srest) = true`, `hSigned : ∀ B ∈ s₁ :: srest, Signed B`;
conclusion `∃ c, validChainK' n Δconf (c ++ s₁ :: srest) = true ∧ blockAt? (c ++ s₁ :: srest) 0 =
some G ∧ c.length = cl.tipHeight + 1 ∧ (∀ B ∈ c ++ s₁ :: srest, Signed B)`.
**Note: no `hΔ : n ≤ Δconf` is consumed here** — `Δconf` is an explicit argument and the `≤`-pin
is obtained via `validChainK'_of_validChainK` / `inForcePinned_of_validChainK`.

`KeyStealingCert.lean:541`:

```lean
def AttestedHistoryK {Sig sk pk : Type} (n Δconf : Nat) (ops : SigOps Sig sk pk)
    (registry : KeyRegistry pk) (G : Block) (tipHeight : Nat)
    (suffix c : Chain) : Prop :=
  validChainK' n Δconf c = true ∧
  blockAt? c 0 = some G ∧
  (∀ B ∈ c, SignedDeclared n ops registry B) ∧
  ∃ p : Chain, c = p ++ suffix ∧ p.length = tipHeight + 1
```

`KeyStealingCert.lean:583` — `keyrot_recent_certified_suffix_agreement`. Hypotheses, verbatim
order: `(hn : 1 ≤ n) (hΔ : n ≤ Δconf)`, `hEUF : KeyStealingEUFCMA …`,
`hHash : SignedHashInjective (SignedDeclared n ops registry) G`,
`hcl : GroundedCertK n (SignedDeclared n ops registry) G cl fl`, `hcl'` (primed),
`hTipS`, `hTipS'`, `hLink`, `hLinks`, `hDense`, `hMono : keyMonoFrom n fl (s₁ :: srest) = true`,
`hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B`, the four primed analogues,
`hRecent`, `hRecent'`,
`hBudget : ∀ c : Chain, AttestedHistoryK n Δconf ops registry G cl.tipHeight (s₁ :: srest) c → ByzantineBounded n (badKeyrotOn n Δconf rented Stolen c)`,
`hB`, `hB'`, `hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i'`,
`hDeep : i + n < (s₁ :: srest).length`, `hDeep'`; conclusion `B = B'`.
Its proof route, verbatim from the body: `groundedCertK_suffix_history` ×2 →
`exists_signedChain_of_covered` ×2 → `validSignedChainK'` ×2 → `hBudget _ ⟨hK, hHead, hCov, c, rfl,
hLen⟩` → `List.getLast?_append` for the recent tips → `CommonPrefixUpTo … 0` for shared genesis →
`keyrot_deep_block_agreement_of_length hn hΔ hEUF hHash hBud hVal hVal' hSig hSig' … hGenesis (k :=
c.length + i) …`.

**The wire-contract docstring on that theorem** (read in full; load-bearing for any W2 restatement
that carries `fl`):

> "In this statement the claim `cl` and the floor snapshot `fl` are coupled by the shared binder of
> `hcl : GroundedCertK … cl fl` and `hMono : keyMonoFrom n fl …`. At the wire level that coupling is
> a contract: the certificate must **carry and authenticate the pair `(cl, fl)` together** — a
> TS-level certificate-unforgeability hypothesis must read `∀ hc, verify hc = true → ∃ cl fl, claim
> hc = cl ∧ floors hc = fl ∧ GroundedCertK n Signed G cl fl` (note the plain path's `hUnf` attests
> only `cl`; a naive port would leave `fl` unauthenticated). Feeding `keyMonoFrom` an
> **unauthenticated** floor is a real attack, not a formality: present a genuine certificate for
> `(cl, fl)` but claim `fl* := 0`; a suffix block signed with a stolen *rotated-out* key `dk(i,
> j_old)` is `SignedDeclared` (verification is at the declared version) and passes `keyMonoFrom n
> fl*` — the verifier accepts a chain this theorem promises nothing about. The floor snapshot is
> exactly as security-critical as the tip hash."

`KeyStealingCert.lean:247` `exists_signedChain_of_covered`:
`(h : ∀ B ∈ c, SignedDeclared n ops registry B) : ∃ sc : SignedChain Sig, stripSigs sc = c ∧ sigsOk
n ops registry sc = true`. `KeyStealingCert.lean:234` `def SignedDeclared`; at 240–246 a lemma
converting `SignedDeclared n ops registry B → KeyStealingSigned n ops registry B` via
`⟨sig, B.keyIndex, hsig⟩` (name not captured in the visible window; body verbatim in the
transcript).

Module docstring, "Honest accounting" paragraph: *"The corruption budget cannot be stated over
verifier-visible data (it quantifies over the whole execution), so it is assumed over **every
history the certificate could be attesting** (`AttestedHistoryK`) … In a real execution the
certificate attests the one real history, so this is the natural reading of P2-A at the certificate
level."* The `keyrot_recent_certified_suffix_agreement` docstring also records that its hash
assumption is over the `SignedDeclared` domain — *"a subset of the full-chain theorems'
`KeyStealingSigned` domain, so a strictly weaker hash assumption"*.

### 2.4 Reused helper lemmas — statements as seen

- `MoltPetit/Results/KeyStealingResults.lean:250` `keyrot_deep_block_agreement_of_length` —
  hypotheses `(hn : 1 ≤ n) (hΔ : n ≤ Δconf)`, `hEUF`, `hHash : SignedHashInjective Signed G`,
  `hBudget : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc))`, `hVal`,
  `hVal'`, `hSig : ∀ B ∈ stripSigs sc, B = G ∨ Signed B`, `hSig'`, `hRecent`, `hRecent'`,
  `hGenesis : CommonPrefixUpTo (stripSigs sc) (stripSigs sc') 0`, `hB`, `hB'`,
  `hLen : k + n < (stripSigs sc).length`, `hLen'`; conclusion `B = B'`. **Takes a whole-execution
  `ByzantineBounded`, and requires shared genesis (`hGenesis`).**
- `MoltPetit/Model/KeyRotation.lean:122` `validChainK'_sound (h : validChainK' n Δconf c = true) :
  ValidChain n c ∧ KeyIndexMonotone n c`.
- `MoltPetit/Model/KeyRotation.lean:385` `def validSignedChainK' … : Bool := sigsOk n ops registry
  sc && validChainK' n Δconf (stripSigs sc)`.
- `MoltPetit/Model/Soundness.lean:97` `blockAt_getLast (hTip : ch.getLast? = some tip) : blockAt? ch
  (ch.length - 1) = some tip`.
- `MoltPetit/Model/Liveness.lean:63` `slot_le_tip_of_mem (hS : StrictSlots c) (hTip : c.getLast? =
  some tip) (hx : x ∈ c) : x.slot ≤ tip.slot`; `Liveness.lean:58` `windowCount_mono (h : c.Sublist
  c') : windowCount c u len ≤ windowCount c' u len`.
- `MoltPetit/Model/Model.lean:47 strictSlots_lt`, `Model.lean:71 exists_blockAt_of_mem`.
- `MoltPetit/Model/KeyStealingUnique.lean:44 def chainUnionRecord`, `:54 chainInRecord_left`,
  `:~62 chainInRecord_right`, `:70 idInjective_keyrot (hHash) (hSig) (hSig') : IdInjective
  (chainUnionRecord sc sc')`, `:184 versionedUnforgeable_of_keyStealingEUFCMA (hEUF) :
  VersionedUnforgeable …`.
- `MoltPetit/TS/Bridge.lean` ≈491 `ts_validChainK_sound`, ≈508 `ts_validateSuffix_sound`, and the
  in-file note *"(… the certificate-boundary form — suffix vs claim-carried floor snapshot —
  awaits the claim-format extension; see `GroundedCertK`.)"*; `TS/Bridge.lean:262
  anchored_density_sound`.
- `Molt/Assumptions.lean` 60–92: `HonestBlocksCover`, `HonestSlotsUnique`, `IdInjective` defined
  fresh, then `badSlotsIn_eq_core`, `faultBounded_eq_core (FaultBounded = ByzantineBounded)`,
  `signedHashInjective_eq_core`, `honestBlocksCover_eq_core`, `honestSlotsUnique_eq_core`,
  `idInjective_eq_core`, all `:= rfl`.

### 2.5 The `Molt` presentation layer — layout idioms as seen

- `Molt.lean` import frontier, in order: `Protocol, Verifier, Assumptions, Results, Rotation,
  ClientRule, MaxSync, Liveness, Axioms`. Docstring: *"one module per paper section, definitions
  written out fresh so the paper can quote them … each fresh definition is bridged to its
  counterpart in the original `MoltPetit` development by a `rfl`-lemma, and every theorem is
  transported across those bridges … Modules grow section by section with the paper; the imports
  above are the current frontier."*
- `MoltPetit.lean` import order ends: `… KeyStealingLockstep, KeyStealingHorizonCore,
  KeyStealingHorizon, KeyStealingScheduleTimed, KeyRotationTests, Results.Axioms, Custody`.
- `lakefile.toml`: `defaultTargets = ["MoltPetit", "Rust", "Thales", "Molt"]`; mathlib
  `v4.30.0-rc2`; `relaxedAutoImplicit = false`; `weak.linter.mathlibStandardSet = true`.
- `Molt/ClientRule.lean` (341 lines) shape: two `private theorem`s
  (`countP_add_le_countP` @27, `countP_between_le` @55) then `deep_block_span` @123,
  `stay_recent_client_safe` @174, `sync_rule` @238, `sync_rule_mem` @284, `end Molt` @341.
  `stay_recent_client_safe` budget hypothesis verbatim:
  `(hBudget : ∀ u, now < u + 5 * n → (badSlotsIn (badKeyrot n Δconf rented Stolen (stripSigs sc)) u n).card ≤ faultBudget n)`;
  it derives `hFresh : now ≤ A.slot + (4 * n - 1)` and calls `client_refresh_rule … (H := 4n-1)`.
  `sync_rule` is `stay_recent_client_safe hn (Nat.le_refl n) …` with `Δconf := n` everywhere.
  `sync_rule_mem` calls `MoltPetit.Model.keyrot_recent_tip_ancestor_mem_anchored`.
- `Molt/Rotation.lean` 170–330: the `_eq_core` rfl-bridge block (`keyFloor`, `confirmedPrefix`,
  `inForce`, `inForcePinned`, `badKeyrot = badKeyrotOn`, `schedPin`, `validChainK`, `validChainK'`,
  `validSignedChainK'`, `validSignedChainSched`, `noMixing = lockstepOk`, `validSignedChainLock`),
  then mode-0 collapses (`badKeyrot_lossOnly`, `badSched_lossOnly`, `exposedSched_lossOnly`), then
  `client_refresh_rule` @≈270 with
  `(hBudget : ∀ u, now < u + n + H → (badSlotsIn (badKeyrot n Δconf rented Stolen (stripSigs sc)) u n).card ≤ faultBudget n)`
  and body `rw [validSignedChainK'_eq_core] at hVal hVal'; exact
  MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored hn hΔ hEUF hHash hA hA' (fun u hu =>
  hBudget u (by omega)) …`; then `alias keyrot_recent_certified_suffix_agreement := …` @308 and
  `abbrev GroundedCertK := @MoltPetit.Model.GroundedCertK` @314; then the mode-2/3 aliases.
- `Molt/MaxSync.lean`: docstring *"`F_max = S - 4n`, and with the minimal credible cap-span of a
  reactive deployment (`S = 5n`), the sync rule `F = n`."* Contains `producer_slot_in_window`,
  two `private` foldl-max helpers, `census_accumulates`, `census_accumulates_later_thefts`,
  `no_budget_beyond`, `max_sync_period` (budget `∀ u, now < u + F + 4 * n → …`, derives `hFresh :
  now ≤ A.slot + (F + 3 * n - 1)`, calls `client_refresh_rule`).
- `Molt/Axioms.lean` (162 lines): header *"Same discipline as `MoltPetit/Results/Axioms.lean`: a
  guarded `#print axioms` per headline theorem, so `lake build Molt` fails if any theorem ever picks
  up an axiom beyond the three classical ones. **Extend this file with every new headline
  theorem.**"* Existing mode-1 entries: `client_refresh_rule` @42, `deep_block_span` @47,
  `stay_recent_client_safe` @52, `sync_rule` @57, `sync_rule_mem` @62, `max_sync_period` @77,
  `producer_slot_in_window` @82, `inForce_mono` @87, `census_accumulates` @92,
  `census_accumulates_later_thefts` @97, `no_budget_beyond` @102,
  `keyrot_recent_certified_suffix_agreement` @107. All expect `[propext, Classical.choice,
  Quot.sound]` except `badKeyrot_lossOnly`, `badSched_lossOnly`, `sched_oldkey_fork_stale`,
  `producer_slot_in_window`, `inForce_mono`, `noBackdate_independent`, `same_block_same_prefix`
  which expect `[propext, Quot.sound]`.
- `MoltPetit/Results/Axioms.lean`: guards at 285–312 for `inForcePinned_of_validChainK`,
  `keyMonoOk_append_of_from`, `exists_signedChain_of_covered` (**`[propext]` only**),
  `groundedCertK_history`, `groundedCertK_suffix_history`,
  `keyrot_recent_certified_suffix_agreement`; guards at 588–602 for
  `honestSlotsUnique_keyrot_anchored`, `keyrot_recent_tip_ancestor_agreement_anchored` (multi-line
  `/-- info: … -/` form), `keyrot_recent_tip_ancestor_mem_anchored`, under the comment at 584
  *"The anchored horizon: the key-leak horizon as a theorem"*.

### 2.6 Absence checks (the no-duplication greps) — results verbatim

```
=== grep anchored across repo        (excluding KeyStealingHorizon.lean / KeyStealingHorizonCore.lean,
                                      filtered to theorem|def |alias|abbrev)
MoltPetit/TS/Bridge.lean:262:theorem anchored_density_sound {c : Chain} {lo t n : Nat}
MoltPetit/Results/Axioms.lean:584:-- The anchored horizon: the key-leak horizon as a theorem

=== grep keyStealingSigned_of_declared / AttestedHistoryK / AcceptedSuffix   (excluding KeyStealingCert.lean)
./MoltPetit/Model/KeyStealingScheduleCert.lean:25:had to quantify the budget over every attestable history (`AttestedHistoryK`)
./MoltPetit/Model/KeyStealingScheduleCert.lean:587:   every attestable history (`AttestedHistoryK`) has nothing to range over.
./MoltPetit/Results/Axioms.lean:399:-- (no AttestedHistoryK). The safety chain is mirrored over the core validator
```

I.e. as of this reading: **no `AcceptedSuffix*` anywhere in the tree; no
`keyStealingSigned_of_declared` anywhere; `AttestedHistoryK` exists only at
`KeyStealingCert.lean:541` plus three comment references; no `*_anchored` name exists outside
`KeyStealingHorizon.lean` / `KeyStealingHorizonCore.lean` except the unrelated
`TS/Bridge.lean:262 anchored_density_sound`.** The verifier gathered this and died before saying
what it meant.

---

## 3. Refutations / doubts

**None recorded.** The verifier wrote no evaluative text at any point. Its only prose is line 5,
*"I'll start by opening the key files the design cites."* Every thinking block is signature-only.
Do not read anything in §2 as a finding against the design.

## 4. Structured output in progress

**None.** No `StructuredOutput` tool_use block appears anywhere in the transcript, and no JSON was
drafted in assistant text. `partial_output` is empty.

## 5. Exact stopping point

- **Last tool call** — line 27, `toolu_013uk8LfX5wqMxREueVriCcs`, the batch described as
  *"Read MaxSync, deep_block_agreement_of_length, TS bridge, and grep for existing anchored/attested
  names"*.
- **Last tool result** — line 28, `is_error: false`, ending mid-way through
  `MoltPetit/Model/KeyStealingCert.lean` 300–360, whose final visible lines are the start of
  `groundedCertK_history`'s proof: `induction h with` / `| genesis hG hSlot hSig =>`.
- **Rate-limit record** — **line 29**: synthetic assistant message, content
  `"You've hit your session limit · resets 2pm (UTC)"`, `"error":"rate_limit"`,
  `"isApiErrorMessage":true`, `"apiErrorStatus":429`, `requestId req_011Cek5S6gHW3f2bfoH6JWZS`,
  `"rateLimitType":"five_hour"`, `"resetsAt":1788616800`, `"overageStatus":"rejected"`,
  timestamp `2026-09-05T09:44:38.945Z`. The file ends at line 29.
