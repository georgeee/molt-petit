# W2 — accuracy lens — PARTIAL verification (salvaged transcript)

> **WARNING — THIS IS A PARTIAL VERIFICATION.** The verifier was killed by a usage
> limit (HTTP 429) before it wrote a single word of prose analysis, any finding, or
> any verdict. Everything below is *evidence it gathered*, not conclusions it drew.
> No claim in this file was accepted or rejected by the verifier. Treat every
> "confirmed" entry as **a fact its tool results returned**, which a fresh verifier
> may reuse without re-establishing, and nothing more.

| field | value |
|---|---|
| agent id | `a8a1dd1d6e965042e` |
| transcript | `/run/claude/agent/projects/-etheron-pod/c28ff38c-0cb1-500d-8726-22cd73943085/subagents/workflows/wf_6b051052-ec7/agent-a8a1dd1d6e965042e.jsonl` |
| workflow | `wf_6b051052-ec7` |
| parent session | `c28ff38c-0cb1-500d-8726-22cd73943085` |
| expected label (from indexer) | **W2-accuracy** |
| confirmed label (from content) | **W2-accuracy** — matches, see "Label confirmation" |
| design under review | `/etheron-pod/rollout-work/designs/W2.md` (+ `W2.json`) |
| repo under review | `/etheron-pod/mini-consensus-lean` |
| lines seen | 4–39 (line 39 is blank/EOF); lines 0–3 not read per salvage instruction (0–1 = oversized prompt, 3–4 = harness attachments) |
| lines skipped | none (no read failed) |
| tool calls issued | 11 Bash calls (no Read/Grep tool calls; everything via `Bash`) |
| model turns | 4 assistant API blocks; 1 line of assistant prose in total |
| stopped at | line **38**, synthetic assistant message `"You've hit your session limit · resets 2pm (UTC)"`, `apiErrorStatus: 429`, `rateLimitType: five_hour`, `requestId req_011Cek5QZM6t2j3WewaxztMi`, timestamp `2026-09-05T09:44:18.011Z` |
| elapsed before death | 09:43:09Z → 09:44:18Z (69 s) |
| StructuredOutput / drafted JSON | **none** — no partial output of any kind exists |

---

## Label confirmation

Expected label **W2-accuracy** is confirmed from transcript content. Evidence:

1. **Work item = W2 (mode 1 anchored trailing-5n at certificate level).** The very
   first tool call (line 6) greps for exactly the W2 declaration set and nothing from
   W1 or W5: `keyrot_recent_certified_suffix_agreement`, `AttestedHistoryK`,
   `keyrot_recent_tip_ancestor_agreement_anchored`, `honestSlotsUnique_keyrot_anchored`,
   `client_refresh_rule`, `stay_recent_client_safe`, `sync_rule`, `max_sync_period`,
   `GroundedCertK`, `keyMonoFrom`, `SignedDeclared`, `groundedCertK_suffix_history`,
   `exists_signedChain_of_covered`. There is **no** grep for `GroundedCertLock`,
   `lockstepFrom`, `lockstep_recent_certified_suffix_agreement` (W1) or for
   `ErasureTimed` / `NoPrematureTheft` / census (W5).
2. **The last tool call (line 36) resolves the W2 rollout row by name.** It ran
   `grep -n "W2" docs/rollout/ROLLOUT_NOTES.md`, whose result (line 37) is:
   `32:| W2 | AN/21 | §6.3 mode 1, phrase `carrying the anchored, trailing-$5n$ form to certificates is future work` | replace with the new certified anchored theorem name; the deployment walkthrough's conclusion can then be stated for the certificate client |`
3. **Lens = accuracy.** All eleven calls are name-existence + exact-hypothesis-shape
   reads of *reused* declarations, plus explicit duplicate hunting. Two Bash
   `description` fields say so outright: *"Locate all declarations referenced by the
   design"* (line 6), *"Search for pre-existing anchored cert theorems and key
   definitions"* (line 25), *"Check for existing anchored cert theorems and imports"*
   (line 30), *"Verify paper and docstring locations cited by the design"* (line 36).
   It never diffed for smuggled edits to existing proofs and never examined the
   W1/W5 designs to test `depends_on`/`enables` — i.e. it did **not** run the
   ordering lens.

---

## 1. Files examined

Every call was `Bash` from `cd /etheron-pod/mini-consensus-lean`. Paths below are
repo-relative to that directory.

| # | line | file(s) / ranges | why (from the call's own `description`, or the command) |
|---|---|---|---|
| 1 | 6 | `MoltPetit/**/*.lean`, `Molt/**/*.lean` — recursive `grep -n` for ~30 declaration names | "Locate all declarations referenced by the design" |
| 2 | 9 | `MoltPetit/Model/KeyStealingHorizon.lean` **40–200** | "Read anchored and horizon tip-ancestor theorems" |
| 3 | 11 | `MoltPetit/Model/KeyStealingHorizonCore.lean` **225–330** | "Read `honestSlotsUnique_keyrot_anchored`" |
| 4 | 13 | `MoltPetit/Model/KeyStealingScheduleHorizon.lean` **130–200** | "Read `horizon_shared_prefix`" |
| 5 | 15 | `MoltPetit/Model/KeyStealingUnique.lean` **40–80** and **180–200**; `MoltPetit/Model/KeyRotation.lean` **118–135** and **380–395**; `MoltPetit/Model/Liveness.lean` **60–70**; `MoltPetit/Model/Soundness.lean` **95–103** | "Read unique/record lemmas, validators, `slot_le_tip_of_mem`, `blockAt_getLast`" |
| 6 | 17 | `MoltPetit/Model/KeyStealingCert.lean` **225–260** and **440–690** | "Read cert reconstruction, `AttestedHistoryK`, certified suffix theorem" |
| 7 | 19 | `Molt/ClientRule.lean` **100–300**; `Molt/MaxSync.lean` **170–200** | "Read Molt client rule theorems and `max_sync_period`" |
| 8 | 21 | `Molt/Rotation.lean` **170–190** and **250–330**; `grep -n "abbrev\|SigningLog"` over `Molt/{Rotation,Assumptions,Verifier,Protocol,Results}.lean` | "Read Molt Rotation wrapper and abbrevs" |
| 9 | 23 | `MoltPetit.lean` (whole), `Molt.lean` (whole), `lakefile.toml` (whole); `Molt/Axioms.lean` **1–60** and **100–115**; `MoltPetit/Results/Axioms.lean` **295–305** and **590–602** | "Read root modules, lakefile, axiom guard files" |
| 10 | 25 | repo-wide `grep -rn "anchored" -l`; `grep -rn "theorem .*anchored\|theorem .*cert.*sync\|AcceptedSuffix\|CertClientRule\|KeyStealingCertAnchored"`; `grep -n "def KeyStealingEUFCMA\|structure KeyStealingEUFCMA" -r MoltPetit`; `MoltPetit/Model/KeyStealingCert.lean` `SignedDeclared` +6; `MoltPetit/Model/Definitions.lean` `SignedHashInjective` +4 and `blockAt?` +2; `ls MoltPetit/Model/` | "Search for pre-existing anchored cert theorems and key definitions" |
| 11 | 28 | `MoltPetit/Model/KeyStealingHorizon.lean` imports (1–40) and **196–320** | "Read remainder of anchored theorem and the `mem_anchored` form" |
| 12 | 30 | repo-wide `grep -rn "hBudgetFrom\|keyrot_deep_block_agreement"`; `MoltPetit/Custody/Anchor.lean` decl list; `grep -n "^import"` over `MoltPetit/Custody.lean`, `MoltPetit/Custody/Anchor.lean`, `MoltPetit/Model/KeyStealingCert.lean`, `Molt/ClientRule.lean`, `Molt/Rotation.lean`, `Molt/MaxSync.lean` | "Check for existing anchored cert theorems and imports" |
| 13 | 32 | `Molt/ClientRule.lean` **1–60** + its `private` decls; `Molt/Results.lean` **36–48**; `grep -n` census/`no_budget_beyond` in `Molt/MaxSync.lean` | "Read ClientRule header, Molt `blockAt?` def, MaxSync census lemma names" |
| 14 | 34 | `grep -n "theorem keyrot_deep_block_agreement_of_length" -A30` over `MoltPetit/Model/*.lean MoltPetit/Results/*.lean`; `grep -n` for `exists_blockAt_of_mem` / `strictSlots_lt` / `def ValidChain` / `def StrictSlots`; `MoltPetit/TS/Bridge.lean` **495–520**; `grep -n "structure GroundedCertK" -A12 MoltPetit/Model/KeyStealingCert.lean` | "Check existing deep-block engine, helper lemmas, TS bridge triple, `GroundedCertK`" |
| 15 | 36 | `paper/molt.tex` (grep for the "future work" / `sync_rule_mem` phrases); `MoltPetit/Model/KeyStealingCert.lean` **36–48** and **530–542**; `memory/paper-rewrite-plan.md` **50–60**; `grep -n "W2" docs/rollout/ROLLOUT_NOTES.md` | "Verify paper and docstring locations cited by the design" — **last call; its result (line 37) arrived, then the 429** |

---

## 2. Facts the tool results established (the reusable part)

The verifier wrote no verdicts. What follows is the raw evidence it paid for,
grouped by the design claim it bears on. **Everything in a code block is verbatim
from a tool result in the transcript.**

### 2.1 Master name/location index (line 6 → line 7)

Every one of these existed at the stated `file:line`:

```
MoltPetit/Model/KeyRotation.lean:122:theorem validChainK'_sound {n Δconf : Nat} {c : Chain}
MoltPetit/Model/KeyRotation.lean:385:def validSignedChainK' {σ sk pk : Type} (n Δconf : Nat)
MoltPetit/Model/Soundness.lean:97:theorem blockAt_getLast {ch : Chain} {tip : Block}
MoltPetit/Model/KeyStealing.lean:47:def badKeyrotOn (n Δconf : Nat) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop)
MoltPetit/Model/KeyStealingHorizonCore.lean:258:theorem honestSlotsUnique_keyrot_anchored
MoltPetit/Model/Liveness.lean:63:theorem slot_le_tip_of_mem {c : Chain} (hS : StrictSlots c) {tip : Block}
MoltPetit/Model/KeyStealingHorizon.lean:69:theorem keyrot_recent_tip_ancestor_agreement_horizon
MoltPetit/Model/KeyStealingHorizon.lean:134:theorem keyrot_recent_tip_ancestor_agreement_anchored
MoltPetit/Model/KeyStealingHorizon.lean:310:theorem keyrot_recent_tip_ancestor_agreement_horizon_of_valid
MoltPetit/Model/KeyStealingCert.lean:159:def keyMonoFrom (n : Nat) : (Nat → Nat) → Chain → Bool
MoltPetit/Model/KeyStealingCert.lean:234:def SignedDeclared {Sig sk pk : Type} (n : Nat) (ops : SigOps Sig sk pk)
MoltPetit/Model/KeyStealingCert.lean:247:theorem exists_signedChain_of_covered {Sig sk pk : Type} {n : Nat}
MoltPetit/Model/KeyStealingCert.lean:462:theorem groundedCertK_suffix_history {n : Nat} (Δconf : Nat) (hn : 1 ≤ n)
MoltPetit/Model/KeyStealingCert.lean:541:def AttestedHistoryK {Sig sk pk : Type} (n Δconf : Nat) (ops : SigOps Sig sk pk)
MoltPetit/Model/KeyStealingCert.lean:583:theorem keyrot_recent_certified_suffix_agreement
MoltPetit/Model/KeyStealingUnique.lean:54:theorem chainInRecord_left {σ : Type} {sc sc' : SignedChain σ} :
MoltPetit/Model/KeyStealingUnique.lean:60:theorem chainInRecord_right {σ : Type} {sc sc' : SignedChain σ} :
MoltPetit/Model/KeyStealingUnique.lean:70:theorem idInjective_keyrot {σ : Type} {sc sc' : SignedChain σ}
MoltPetit/Model/KeyStealingUnique.lean:184:theorem versionedUnforgeable_of_keyStealingEUFCMA
MoltPetit/Model/Definitions.lean:656:def SignedHashInjective (Signed : Block → Prop) (G : Block) : Prop :=
MoltPetit/Model/KeyStealingScheduleHorizon.lean:161:theorem horizon_shared_prefix
MoltPetit/TS/Emitted.lean:191:def keyMonoFromTs (n : Int) (fl : FloorList) (c : Chain) : Bool :=
Molt/Rotation.lean:89:def validSignedChainK' {σ sk pk : Type} (n Δconf : Nat)
Molt/Rotation.lean:182:theorem badKeyrot_eq_core : badKeyrot = MoltPetit.Model.badKeyrotOn := rfl
Molt/Rotation.lean:267:theorem client_refresh_rule
Molt/ClientRule.lean:123:theorem deep_block_span {n : Nat} (hn : 1 ≤ n) {c : Chain}
Molt/ClientRule.lean:174:theorem stay_recent_client_safe
Molt/ClientRule.lean:238:theorem sync_rule
Molt/ClientRule.lean:284:theorem sync_rule_mem
Molt/Protocol.lean:111:theorem faultBudget_eq_core : faultBudget = MoltPetit.Model.maxByzantine := rfl
Molt/Results.lean:42:theorem blockAt?_eq_core : blockAt? = MoltPetit.Model.blockAt? := rfl
Molt/MaxSync.lean:176:theorem max_sync_period
Molt/Assumptions.lean:50:def SignedHashInjective (Signed : Block → Prop) (G : Block) : Prop :=
Molt/Assumptions.lean:81:theorem badSlotsIn_eq_core : badSlotsIn = MoltPetit.Model.badSlotsIn := rfl
```

Note two patterns in that same grep produced **no** hit: `structure GroundedCertK`
and `def KeyStealingEUFCMA`. `KeyStealingEUFCMA` was located on the next pass
(§2.7); `GroundedCertK`'s declaration form was never located — see §4, open thread A.

### 2.2 The anchored engine the design builds on — full hypothesis lists

`MoltPetit/Model/KeyStealingHorizon.lean:134` `keyrot_recent_tip_ancestor_agreement_anchored`,
recovered verbatim (this is the shape the design's new theorem #1
`keyrot_deep_block_agreement_anchored` is the generic-`Signed`, arbitrary-depth
analogue of):

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
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B'
```

Key structural facts read out of its proof body and its sibling
`keyrot_recent_tip_ancestor_mem_anchored` (`KeyStealingHorizon.lean:222`):

* It is `hHash`-specialised to `SignedHashInjective (KeyStealingSigned n ops registry) G`
  and discharges the genesis-or-signed side conditions internally via
  `idInjective_keyrot hHash (fun b hb => Or.inr (keyStealingSigned_of_mem hVal hb)) …`
  — i.e. **it is not generic in `Signed`**. (The generic-`Signed` variant with an
  explicit `hSig`/`hSig'` pair is `keyrot_recent_tip_ancestor_agreement_horizon`,
  `KeyStealingHorizon.lean:69`, and `keyrot_deep_block_agreement_of_length`, §2.6.)
* Its anchor-position lemma is **hand-rolled** in both anchored theorems
  (`obtain ⟨i, hi⟩ := exists_blockAt_of_mem hA … strictSlots_lt … injection hi`),
  ~11 lines each, repeated for `sc` and `sc'`. The design proposes replacing this
  with `slot_le_tip_of_mem`; the hand-rolled form is what exists today.
* It calls `horizon_shared_prefix … (hBudgetFrom (sTip.slot + 1 - n) (by omega))`
  in both `Nat.le_total` branches (`KeyStealingHorizon.lean:205` and `:212`), and the
  membership form does the same at `:291` / `:299`.
* `hBudgetFrom` occurs **nowhere else in the repo**: the line-30 grep returned hits
  only in `MoltPetit/Model/KeyStealingHorizon.lean` at `205, 212, 231, 257, 291, 299`.

`MoltPetit/Model/KeyStealingHorizonCore.lean:258` `honestSlotsUnique_keyrot_anchored`
verbatim head:

```lean
theorem honestSlotsUnique_keyrot_anchored
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    (hUnf : VersionedUnforgeable n Δconf ops registry rented Stolen honestSigned now Δ)
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

Notable: it takes `hUnf : VersionedUnforgeable …` (not `KeyStealingEUFCMA`), is
generic in nothing (no `Signed` parameter — it consumes `hId` instead), and its
`hVal`/`hVal'` are the **core** `validSignedChainK'`.

`MoltPetit/Model/KeyStealingScheduleHorizon.lean:161` `horizon_shared_prefix` verbatim head:

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

It is validator-agnostic and takes an **arbitrary depth `k`** — which is what the
design's arbitrary-`k` new theorem needs. Its docstring states "No hypothesis
touches any window below `u`, and no shared genesis is assumed."

Supporting lemmas, verbatim, all present with the shapes the design assumes:

```lean
theorem chainInRecord_left  {σ : Type} {sc sc' : SignedChain σ} :
    ChainInRecord (chainUnionRecord sc sc') (stripSigs sc)      -- KeyStealingUnique.lean:54
theorem chainInRecord_right {σ : Type} {sc sc' : SignedChain σ} :
    ChainInRecord (chainUnionRecord sc sc') (stripSigs sc')     -- :60
theorem idInjective_keyrot {σ : Type} {sc sc' : SignedChain σ}  -- :70
    {Signed : Block → Prop} {G : Block}
    (hHash : SignedHashInjective Signed G)
    (hSig  : ∀ B ∈ stripSigs sc,  B = G ∨ Signed B)
    (hSig' : ∀ B ∈ stripSigs sc', B = G ∨ Signed B) :
    IdInjective (chainUnionRecord sc sc')
theorem versionedUnforgeable_of_keyStealingEUFCMA               -- :184
    … (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ) :
    VersionedUnforgeable n Δconf ops registry rented Stolen honestSigned now Δ
theorem blockAt_getLast {ch : Chain} {tip : Block}              -- Soundness.lean:97
    (hTip : ch.getLast? = some tip) : blockAt? ch (ch.length - 1) = some tip
theorem slot_le_tip_of_mem {c : Chain} (hS : StrictSlots c) {tip : Block}  -- Liveness.lean:63
    (hTip : c.getLast? = some tip) {x : Block} (hx : x ∈ c) : x.slot ≤ tip.slot
theorem validChainK'_sound {n Δconf : Nat} {c : Chain}          -- KeyRotation.lean:122
    (h : validChainK' n Δconf c = true) : ValidChain n c ∧ KeyIndexMonotone n c
def validSignedChainK' {σ sk pk : Type} (n Δconf : Nat)         -- KeyRotation.lean:385
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChainK' n Δconf (stripSigs sc)
```

`idInjective_keyrot` **is** generic in `Signed`/`G` — relevant because the design's
new theorem #1 is to be generic-`Signed`. Also present in the same file:
`chainUnionRecord` (def) and `mem_chainUnionRecord`.
`exists_blockAt_of_mem` is at `MoltPetit/Model/Model.lean:71`; `strictSlots_lt` at
`Model.lean:47`; `def StrictSlots` at `Definitions.lean:469`; `def ValidChain` at
`Definitions.lean:490`; `def blockAt? (c : Chain) (h : Nat) : Option Block := getElem? c h`
at `Definitions.lean:462`.

### 2.3 The certificate plumbing the design reuses

`MoltPetit/Model/KeyStealingCert.lean:462` `groundedCertK_suffix_history` verbatim:

```lean
theorem groundedCertK_suffix_history {n : Nat} (Δconf : Nat) (hn : 1 ≤ n)
    {Signed : Block → Prop} {G : Block} {cl : CertClaim} {fl : Nat → Nat}
    (hG : GroundedCertK n Signed G cl fl)
    {s₁ : Block} {srest : Chain} {sTip : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
      quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hMono : keyMonoFrom n fl (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, Signed B) :
    ∃ c : Chain,
      validChainK' n Δconf (c ++ s₁ :: srest) = true ∧
      blockAt? (c ++ s₁ :: srest) 0 = some G ∧
      c.length = cl.tipHeight + 1 ∧
      (∀ B ∈ c ++ s₁ :: srest, Signed B)
```

Counting from the calibrated grep anchor (`:462` = the `theorem` line), the
hypotheses land at: `hG` **:464**, `hTipS` **:466**, `hLink` **:467**, `hLinks`
**:468**, `hDense` **:469–470**, `hMono` **:471**, `hSigned` **:472**, conclusion
**:473–477**. The design cites "KeyStealingCert.lean:462-475" for the seven
`AcceptedSuffixK` field shapes; the seven hypotheses do lie inside that window
(the window's tail also covers the first conclusion lines). The argument order the
design's `AcceptedSuffixK.history` projection uses —
`groundedCertK_suffix_history Δconf hn h.cert h.tip h.link h.links h.dense h.mono h.signed`
— matches the binder order above exactly, with `Δconf` explicit and preceding `hn`.

```lean
def SignedDeclared {Sig sk pk : Type} (n : Nat) (ops : SigOps Sig sk pk)   -- :234
    (registry : KeyRegistry pk) (B : Block) : Prop :=
  ∃ sig : Sig,
    ops.verify (registry (producerForSlot n B.slot) B.keyIndex) B sig = true

theorem keyStealingSigned_of_declared … (h : SignedDeclared n ops registry B) :  -- :239
    KeyStealingSigned n ops registry B

theorem exists_signedChain_of_covered {Sig sk pk : Type} {n : Nat}         -- :247
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {c : Chain}
    (h : ∀ B ∈ c, SignedDeclared n ops registry B) :
    ∃ sc : SignedChain Sig, stripSigs sc = c ∧ sigsOk n ops registry sc = true

def AttestedHistoryK {Sig sk pk : Type} (n Δconf : Nat) (ops : SigOps Sig sk pk)  -- :541
    (registry : KeyRegistry pk) (G : Block) (tipHeight : Nat)
    (suffix c : Chain) : Prop :=
  validChainK' n Δconf c = true ∧
  blockAt? c 0 = some G ∧
  (∀ B ∈ c, SignedDeclared n ops registry B) ∧
  ∃ p : Chain, c = p ++ suffix ∧ p.length = tipHeight + 1
```

`MoltPetit/Model/KeyStealingCert.lean:583` `keyrot_recent_certified_suffix_agreement`
was recovered **in full**, statement *and* proof body — this is the theorem the
design's new #2 is to mirror "hypothesis-for-hypothesis". Its hypothesis list, in
order: `hn`, `hΔ`, `hEUF : KeyStealingEUFCMA n Δconf …`,
`hHash : SignedHashInjective (SignedDeclared n ops registry) G`,
`hcl`/`hcl' : GroundedCertK n (SignedDeclared n ops registry) G cl fl`,
`hTipS`, `hTipS'`, `hLink`, `hLinks`, `hDense`, `hMono`, `hSigned`,
`hLink'`, `hLinks'`, `hDense'`, `hMono'`, `hSigned'`, `hRecent`, `hRecent'`,

```lean
    (hBudget : ∀ c : Chain,
        AttestedHistoryK n Δconf ops registry G cl.tipHeight (s₁ :: srest) c →
        ByzantineBounded n (badKeyrotOn n Δconf rented Stolen c))
    {i i' : Nat} {B B' : Block}
    (hB  : blockAt? (s₁  :: srest ) i  = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep  : i  + n < (s₁  :: srest ).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B'
```

Its proof is the exact recipe the design proposes to re-run under an anchored
budget: `groundedCertK_suffix_history` ×2 → `exists_signedChain_of_covered` ×2 →
assemble `validSignedChainK'` ×2 → instantiate `hBudget` at the attested history
(`hBudget _ ⟨hK, hHead, hCov, c, rfl, hLen⟩`) → `List.getLast?_append` for the full
tips → `hGenesis : CommonPrefixUpTo … 0` → close with
`keyrot_deep_block_agreement_of_length hn hΔ hEUF hHash hBud hVal hVal' hSig hSig' … (k := c.length + i) …`
(use site at `KeyStealingCert.lean:672`). Its docstring carries the **wire contract**
warning that `(cl, fl)` must be authenticated together (unauthenticated `fl* := 0`
is a real attack) — reproduced in full in the transcript.

### 2.4 The `Molt` (paper-namespace) layer the design extends

`Molt/Rotation.lean:267` `client_refresh_rule` verbatim (the H-parametric idiom the
design's `cert_client_refresh_rule` mirrors), including its body:

```lean
theorem client_refresh_rule
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig} {A : Block} {H : Nat}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    (hA : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    (hFresh : now ≤ A.slot + H)
    (hBudget : ∀ u, now < u + n + H →
      (badSlotsIn (badKeyrot n Δconf rented Stolen (stripSigs sc)) u n).card
        ≤ faultBudget n)
    … : B = B' := by
  rw [validSignedChainK'_eq_core] at hVal hVal'
  exact MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored hn hΔ
    hEUF hHash hA hA'
    (fun u hu => hBudget u (by omega))
    hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'
```

Confirms the design's stated idiom: Molt-side `badKeyrot`/`badSlotsIn`/`faultBudget`/
`blockAt?` are passed to the core **by defeq**, with only `validSignedChainK'` needing
an explicit `rw [validSignedChainK'_eq_core]`. The rfl-bridges exist:
`badKeyrot_eq_core` (`Rotation.lean:182`), `badSlotsIn_eq_core` (`Assumptions.lean:81`),
`faultBudget_eq_core` (`Protocol.lean:111`), `blockAt?_eq_core` (`Results.lean:42`),
plus `keyFloor_eq_core`, `confirmedPrefix_eq_core`, `inForce_eq_core`,
`inForcePinned_eq_core`, `schedPin_eq_core`, `validChainK_eq_core`,
`validChainK'_eq_core` in `Molt/Rotation.lean:176-190`.
`Molt.blockAt?` is a fresh def: `def blockAt? (c : Chain) (h : Nat) : Option Block := getElem? c h`
at `Molt/Results.lean:39`, bridged at `:42`.

**The design's cited "future work" remark is exactly where the design says it is.**
Counting from the calibrated anchors `Rotation.lean:267` and `:271` (both matched
independently by the line-6 grep), the alias docstring occupies **303–307** and the
alias itself 308–309:

```lean
/-- Mode 1's certificate-level safety: the agreement of                      -- :303
`client_refresh_rule`'s family at the certificate presentation, with the
floor carried as a snapshot in the claim — under the global, all-window
budget (the anchored, trailing-window form is future work at this
presentation). -/                                                            -- :307
alias keyrot_recent_certified_suffix_agreement :=                            -- :308
  MoltPetit.Model.keyrot_recent_certified_suffix_agreement
```

and the abbrev idiom the design cites as "Rotation.lean:314" is:

```lean
/-- The strengthened certificate grounding for mode 1: each fold also         -- :311
checks the per-producer floor, and the certificate must attest claim and
floor together (paper §6.3). -/
abbrev GroundedCertK := @MoltPetit.Model.GroundedCertK                        -- :314
```

Both citations line up exactly.

`Molt/ClientRule.lean` was read in full over 1–300. Confirmed present:
`deep_block_span` (**:123**, `(hV : ValidChain n c) {m : Nat} {A D : Block}
(hA : blockAt? c m = some A) (hD : blockAt? c (m + n) = some D) : D.slot < A.slot + 2 * n`),
`stay_recent_client_safe` (**:174**, budget `∀ u, now < u + 5 * n → … ≤ faultBudget n`,
derivation `hspan → hFresh : now ≤ A.slot + (4 * n - 1) → client_refresh_rule … at H := 4n-1`),
`sync_rule` (**:238**, `Δconf := n`, term-mode `stay_recent_client_safe hn (Nat.le_refl n) …`),
`sync_rule_mem` (**:284**). The file's only `private` decls are
`countP_add_le_countP` (**:27**) and `countP_between_le` (**:55**) — i.e. the
"private helpers at the top of the file, before the public theorems" layout idiom.
`Molt/ClientRule.lean:1` is `import Molt.Rotation` (single import).

`Molt/MaxSync.lean:176` `max_sync_period` exists with cadence `hCadence : now ≤ t + F`
and budget `∀ u, now < u + F + 4 * n → …`; the same file has `census_accumulates`
(**:95**), `census_accumulates_later_thefts` (**:135**), `no_budget_beyond` (**:156**).
`Molt/MaxSync.lean:1` is `import Molt.ClientRule`.

`Molt/Rotation.lean` abbrev inventory (line-21 grep), verbatim:

```
Molt/Rotation.lean:108:abbrev KeyStealingEUFCMA := @MoltPetit.Model.KeyStealingEUFCMA
Molt/Rotation.lean:112:abbrev KeyStealingSigned := @MoltPetit.Model.KeyStealingSigned
Molt/Rotation.lean:131:abbrev SchedUnforgeable := @MoltPetit.Model.SchedUnforgeable
Molt/Rotation.lean:134:abbrev badSched := @MoltPetit.Model.badSched
Molt/Rotation.lean:137:abbrev SignedDeclared := @MoltPetit.Model.SignedDeclared
Molt/Rotation.lean:164:abbrev LockstepPackage := @MoltPetit.Model.LockstepPackage
Molt/Rotation.lean:314:abbrev GroundedCertK := @MoltPetit.Model.GroundedCertK
Molt/Rotation.lean:352:abbrev GroundedCertSched := @MoltPetit.Model.GroundedCertSched
```

**No `abbrev AttestedHistoryK` and no `AcceptedSuffix*` anywhere in `Molt/`** — so the
design's "no Molt abbrev exists yet" for `AttestedHistoryK` holds. `SigningLog` is
`abbrev SigningLog := MoltPetit.Model.SigningLog` at `Molt/Assumptions.lean:29`;
`Molt.SignedHashInjective` is a *fresh def* at `Molt/Assumptions.lean:50`, not an abbrev.

### 2.5 Duplicate check — no pre-existing anchored certificate theorem

Repo-wide (`.lake` excluded), the only declarations matching
`theorem .*anchored | theorem .*cert.*sync | AcceptedSuffix | CertClientRule | KeyStealingCertAnchored`:

```
./MoltPetit/Model/KeyStealingHorizonCore.lean:258:theorem honestSlotsUnique_keyrot_anchored
./MoltPetit/Model/KeyStealingHorizon.lean:134:theorem keyrot_recent_tip_ancestor_agreement_anchored
./MoltPetit/Model/KeyStealingHorizon.lean:222:theorem keyrot_recent_tip_ancestor_mem_anchored
./MoltPetit/TS/Bridge.lean:262:theorem anchored_density_sound {c : Chain} {lo t n : Nat}
```

Zero hits for `AcceptedSuffix`, `CertClientRule`, `KeyStealingCertAnchored`. Files
mentioning "anchored" at all: `Molt/Rotation.lean`, `Molt/ClientRule.lean`,
`MoltPetit/Model/{KeyStealingLongRange,KeyStealingHorizonCore,KeyStealingHorizon,TimedSig}.lean`,
`MoltPetit/Custody/{Anchor,Axioms}.lean`, `MoltPetit/TS/Bridge.lean`,
`MoltPetit/Results/Axioms.lean`, `MoltPetit/Custody.lean`, `Rust/{Equiv,Bridge}.lean`.
`MoltPetit/Custody/Anchor.lean` is an unrelated module (`AnchoredSig` structure at :42,
`anchor_le_produced` :58, `production_window` :70, `no_retroactive_forgery` :82;
it imports only `MoltPetit.Model.Definitions`).

`ls MoltPetit/Model/` returned 27 files; **`KeyStealingCertAnchored.lean` is not among
them**. `MoltPetit.lean` and `Molt.lean` root import lists were read in full:
`Molt.lean` imports exactly `Molt.{Protocol,Verifier,Assumptions,Results,Rotation,ClientRule,MaxSync,Liveness,Axioms}`
— no `Molt.CertClientRule`, no `Molt.AxiomsCertAnchored`. `lakefile.toml` declares
`defaultTargets = ["MoltPetit", "Rust", "Thales", "Molt"]`, `lean_lib Molt`, mathlib
`v4.30.0-rc2`, and aeneas at rev `bf13c42e…`.

Import chains relevant to the design's two new files:
`MoltPetit/Model/KeyStealingCert.lean` imports `MoltPetit.Model.Grounded` +
`MoltPetit.Results.KeyStealingResults`; `Molt/Rotation.lean` imports `Molt.Results`,
`MoltPetit.Results.KeyStealingResults`, `MoltPetit.Results.KeyStealingScheduleResults`,
`MoltPetit.Model.KeyStealingHorizon`, `MoltPetit.Model.KeyStealingLockstep`,
`MoltPetit.Model.KeyStealingCert`, `MoltPetit.Model.KeyStealingScheduleCert`;
`Molt/ClientRule.lean` imports `Molt.Rotation`; `Molt/MaxSync.lean` imports
`Molt.ClientRule`. `MoltPetit/Model/KeyStealingHorizon.lean` imports
`KeyStealingSafety`, `KeyStealingUnique`, `KeyStealingHorizonCore`,
`Results.KeyStealingResults`, `KeyStealingScheduleHorizon`.

### 2.6 The generic-`Signed` deep-block engine (design's #1 is its anchored analogue)

`MoltPetit/Results/KeyStealingResults.lean:250` `keyrot_deep_block_agreement_of_length`,
verbatim:

```lean
theorem keyrot_deep_block_agreement_of_length
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    {Signed : Block → Prop} {G : Block}
    {sc sc' : SignedChain Sig}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective Signed G)
    (hBudget : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc)))
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    (hSig  : ∀ B ∈ stripSigs sc,  B = G ∨ Signed B)
    (hSig' : ∀ B ∈ stripSigs sc', B = G ∨ Signed B)
    (hRecent  : ∃ t,  (stripSigs sc ).getLast? = some t ∧ now ≤ t.slot + Δ)
    (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ)
    (hGenesis : CommonPrefixUpTo (stripSigs sc) (stripSigs sc') 0)
    {k : Nat} {B B' : Block}
    (hB  : blockAt? (stripSigs sc)  k = some B)
    (hB' : blockAt? (stripSigs sc') k = some B')
    (hLen  : k + n < (stripSigs sc ).length)
    (hLen' : k + n < (stripSigs sc').length) :
    B = B'
```

Base theorem `keyrot_deep_block_agreement` is at
`MoltPetit/Results/KeyStealingResults.lean:204`; `_of_length` closes by materialising
`D`/`D'` at `k + n` and calling it with `(Nat.le_refl _) (Nat.le_refl _)`. Other use
sites: `KeyStealingResults.lean:279, 374, 438`, `KeyStealingCert.lean:672`.
Note it is **global-budget** (`ByzantineBounded`) and takes `hGenesis` — the two
things the anchored form is meant to drop.

### 2.7 Crypto / hash surface

```
MoltPetit/Model/KeyStealingUnique.lean:136:structure KeyStealingEUFCMA (n Δconf : Nat) {Sig sk pk : Type} (ops : SigOps Sig sk pk)
MoltPetit/Model/Definitions.lean:656:def SignedHashInjective (Signed : Block → Prop) (G : Block) : Prop :=
  ∀ ⦃B B' : Block⦄,
    (B = G ∨ Signed B) → (B' = G ∨ Signed B') →
    B.id = B'.id → B = B'
MoltPetit/Model/KeyStealing.lean:47:def badKeyrotOn (n Δconf : Nat) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop)
```

### 2.8 Axiom-guard file idioms the design must copy

`Molt/Axioms.lean` (read 1–60, 100–115). Its imports are `Molt.{Results,Rotation,ClientRule,MaxSync,Liveness}`
and its docstring says: *"a guarded `#print axioms` per headline theorem, so
`lake build Molt` fails if any theorem ever picks up an axiom beyond the three
classical ones. Extend this file with every new headline theorem."* Line
arithmetic (the 1–60 window is contiguous, so numbering is exact):

```
:41  -- Theorem 3: the client refresh rule (paper §6.3, mode 1).
:42  /-- info: 'Molt.client_refresh_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
:43  #guard_msgs in
:44  #print axioms Molt.client_refresh_rule
:46  -- The deep anchor is nearby (paper §6.3, mode 1).
:47  /-- info: 'Molt.deep_block_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
:52  /-- info: 'Molt.stay_recent_client_safe' … -/
:57  /-- info: 'Molt.sync_rule' … -/
```

and in the 100–115 window:

```
:101 -- Beyond the bound there is no budget to instantiate (paper §6.3, mode 1).
:102 /-- info: 'Molt.no_budget_beyond' … -/
:106 -- Certificate-level forms, modes 1-2 (paper §4 item 5, §6.3).
:107 /-- info: 'Molt.keyrot_recent_certified_suffix_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
:108 #guard_msgs in
:109 #print axioms Molt.keyrot_recent_certified_suffix_agreement
:111 /-- info: 'Molt.sched_recent_certified_suffix_agreement' … -/
:115 -- Mode 2, horizon-scoped and membership forms; the chaining lemma.
```

So the design's citations "**Molt/Axioms.lean:41-44** format" (= the
`client_refresh_rule` guard block, comment + info + `#guard_msgs in` + `#print axioms`),
"**deep_block_span at Molt/Axioms.lean:47**", and "**alias; cf. Molt/Axioms.lean:107**"
(= the guard for the existing `Molt.keyrot_recent_certified_suffix_agreement` alias)
all land on exactly the lines claimed.

`MoltPetit/Results/Axioms.lean` (295–305 and 590–602 windows, both contiguous):

```
:295 #guard_msgs in
:296 #print axioms MoltPetit.Model.exists_signedChain_of_covered
:297 /-- info: 'MoltPetit.Model.groundedCertK_history' … -/
:300 /-- info: 'MoltPetit.Model.groundedCertK_suffix_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
:301 #guard_msgs in
:302 #print axioms MoltPetit.Model.groundedCertK_suffix_history
:303 /-- info: 'MoltPetit.Model.keyrot_recent_certified_suffix_agreement' … -/
```
```
:590 -- just means more windows must satisfy the budget -- and A := genesis recovers
:591 -- the global-budget theorem. This is the paper's "key-leak horizon", formal.
:592 /-- info: 'MoltPetit.Model.honestSlotsUnique_keyrot_anchored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
:593 #guard_msgs in
:594 #print axioms MoltPetit.Model.honestSlotsUnique_keyrot_anchored
:595 /-- info: 'MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored' depends on axioms: [propext,
:596  Classical.choice,
:597  Quot.sound] -/
:598 #guard_msgs in
:599 #print axioms MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored
:600 -- anchored membership form (unequal tip heights), same trailing budget
:601 /-- info: 'MoltPetit.Model.keyrot_recent_tip_ancestor_mem_anchored' … -/
:602 #guard_msgs in
```

The design's "**groundedCertK_suffix_history guarded at Results/Axioms.lean:300**"
matches exactly. Its two other citations in the same clause do **not** line up under
this arithmetic — see §4, open thread B. The 3-line wrap phenomenon the design warns
about is real and visible at :595–597.

### 2.9 TS bridge triple (design cites it as the field-by-field source for `AcceptedSuffixK`)

`MoltPetit/TS/Bridge.lean` 495–520 (contiguous window; `theorem` line computes to **:506**,
exactly the design's citation):

```lean
theorem ts_validateSuffix_sound {n : Nat} {cl : CertClaim}          -- :506
    {s₁ : Block} {srest : Chain} {sTip : Block}
    (hTip : (s₁ :: srest).getLast? = some sTip)
    (h : MoltPetit.validateSuffix n (toTSClaim cl) (toTSChain (s₁ :: srest)) = true) :
    (s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId) ∧
    linksOk (s₁ :: srest) = true ∧
    (∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
      quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
```

The emitted triple is `link ∧ links ∧ dense` — three of the seven proposed
`AcceptedSuffixK` fields, in the same shapes.

### 2.10 Paper + planning citations (last call before death)

`paper/molt.tex` grep hits:

```
217:without erasure; both are future work,
429:  pins); at certificate level they are proved for modes 1--2
432:  future work for mode 3 (see the ``honest scope'' discussion in
817:\code{sync\_rule\_mem}]\label{thm:refresh}
897:all-window budget: carrying the anchored, trailing-$5n$ form to
898:certificates is future work.
982:(\code{sync\_rule}, \code{sync\_rule\_mem}): any two chains such a
997:hypotheses. At the full-chain presentation this is the complete story.
```

So the exact phrase W2 is meant to delete lives at **molt.tex:897–898**, and
`docs/rollout/ROLLOUT_NOTES.md:32` is the W2 row quoting it. `memory/paper-rewrite-plan.md`
50–60 independently records the gap as known future work:
*"only mode-2's CERTIFICATE form remains global-budget (future work: horizon at
certificates; also trailing-5n cert form for mode 1, lockstep cert wrapper, the
honest-chain induction as a Lean composition)."* `KeyStealingCert.lean` 36–48
contains the module docstring's "Honest accounting" paragraph explaining the
`AttestedHistoryK` budget reading, and 530–542 the `AttestedHistoryK` docstring —
both of which the design cites as the source of its own docstring language.

---

## 3. Claims REFUTED or doubted

**None.** The verifier died before writing any prose beyond its opening sentence.
It recorded no refutation, no doubt, no severity, and no verdict of any kind.

---

## 4. Open threads visible in the evidence (NO verdict was written — salvager's flags)

These are arithmetic/absence observations derivable from the tool results already in
the transcript. **The killed verifier never commented on any of them.** They are
listed so a fresh verifier knows where the thread was cut, not as findings.

**A. `structure GroundedCertK` was searched for twice and never located.**
The line-6 repo-wide grep included the pattern `structure GroundedCertK` and returned
no matching line. The line-34 call ran
`grep -n "structure GroundedCertK" -A12 MoltPetit/Model/KeyStealingCert.lean`
and that sub-command produced **empty output** (the tool result ends with a bare
`----` separator and nothing after it). What *is* confirmed: `GroundedCertK` is used
as a type in `groundedCertK_suffix_history`'s `hG` (`KeyStealingCert.lean:464`) and
re-exported as `abbrev GroundedCertK := @MoltPetit.Model.GroundedCertK` at
`Molt/Rotation.lean:314`. Its declaration form (structure? def? where?) is unresolved
in this transcript. The design's `AcceptedSuffixK` is proposed as a `structure … : Prop`
with seven fields and its Molt re-export is justified by the "Rotation.lean:314 idiom
(abbrev for Prop structures / predicates)" — so a fresh verifier should locate
`GroundedCertK`'s actual declaration before relying on that idiom argument.

**B. Two of the design's `Results/Axioms.lean` line citations do not match the
arithmetic of the returned `sed -n 590,602p` window.** The design says
"honestSlotsUnique_keyrot_anchored at **:595**" and "reproduce Lean's 3-line wrap
exactly as Results/Axioms.lean:**596-598**". Under the contiguous 13-line window
returned (§2.8), the `honestSlotsUnique_keyrot_anchored` guard block is at
**592–594**, and the 3-line wrapped info comment is at **595–597** (598 is
`#guard_msgs in`). Both citations appear shifted, though the substance the design
relies on (that guard exists; that 3-line wrapping occurs and must be copied from
Lean's emitted message rather than hand-written) is present in the evidence.
Not adjudicated by the verifier.

**C. The design's characterisation "Rotation.lean only abbrevs GroundedCertK and
SignedDeclared".** The line-21 grep (§2.4) shows `Molt/Rotation.lean` carries eight
abbrevs: `KeyStealingEUFCMA`, `KeyStealingSigned`, `SchedUnforgeable`, `badSched`,
`SignedDeclared`, `LockstepPackage`, `GroundedCertK`, `GroundedCertSched`. The
narrower proposition the design actually needs — that **no** `AttestedHistoryK` or
`AcceptedSuffixK` abbrev exists yet — is supported by the same grep. Not adjudicated.

**D. `keyrot_recent_tip_ancestor_agreement_anchored` is not generic in `Signed`.**
Established in §2.2: its `hHash` is fixed to `KeyStealingSigned n ops registry` and
it builds `hId` internally from `keyStealingSigned_of_mem`. The design's new #1 is to
be generic-`Signed` (needed because the certificate path carries
`SignedDeclared`, a *subset* domain). The generic ingredients all exist
(`idInjective_keyrot`, `horizon_shared_prefix`, `honestSlotsUnique_keyrot_anchored`
— the last takes `hId` as a hypothesis rather than constructing it), so the
generic-`Signed` anchored variant is not obtainable by direct reuse of `:134` and
must be re-derived. The verifier had assembled all of these pieces and wrote nothing.

---

## 5. Structured output / drafted JSON

**None exists.** No `StructuredOutput` tool call was made. No JSON appears in any
assistant text block. The only assistant prose in the entire transcript is line 5:

> "I'll start by locating the key declarations the design relies on."

All four assistant thinking blocks are signature-only (empty `thinking` strings), so
no reasoning text is recoverable.

---

## 6. Where it stopped

* **Last tool call:** line 36, `Bash`, description *"Verify paper and docstring
  locations cited by the design"* — `grep` over `paper/molt.tex`; `sed -n 36,48p`
  and `sed -n 530,542p MoltPetit/Model/KeyStealingCert.lean`; `sed -n 50,60p
  memory/paper-rewrite-plan.md`; `grep -n "W2" docs/rollout/ROLLOUT_NOTES.md`.
* **Last tool result:** line 37 — it succeeded and returned (contents in §2.10).
* **Last assistant sentence:** line 5, *"I'll start by locating the key declarations
  the design relies on."* (nothing after it).
* **Rate-limit record:** **line 38** — synthetic `<synthetic>` assistant message,
  `content: "You've hit your session limit · resets 2pm (UTC)"`, `error: "rate_limit"`,
  `isApiErrorMessage: true`, `apiErrorStatus: 429`,
  `quotaLimits: {status: "rejected", resetsAt: 1788616800, rateLimitType: "five_hour",
  overageStatus: "rejected", overageDisabledReason: "org_level_disabled"}`,
  `requestId: req_011Cek5QZM6t2j3WewaxztMi`, timestamp `2026-09-05T09:44:18.011Z`.
* Line 39 is blank (EOF).

The verifier had finished its evidence-gathering sweep — every declaration in the
design's reuse set had been located and read, the duplicate search had run, the
file-layout and axiom-guard idioms had been read, and the paper/ROLLOUT_NOTES
citations had been resolved — and was killed at exactly the point where it would
have begun writing its analysis.
