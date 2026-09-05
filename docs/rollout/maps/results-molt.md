# results-molt — Client rules, key-stealing headline results, and the Molt/ bridge + axiom-guard idiom (mini-consensus-lean, branch feature/key-rotation-sound @ 8b8b766)

## /etheron-pod/mini-consensus-lean/MoltPetit/Results/KeyStealingResults.lean

**Purpose:** Mode-1 (reactive, in-band rotation) headline light-client safety under the strong key-stealing adversary, over the index-pinned signed validator validSignedChainK' with confirmation gate n ≤ Δconf and a GLOBAL budget keyed to the first chain (badKeyrotOn … (stripSigs sc)). Also the loss-only (Stolen := ⊥) specialisations. Namespace MoltPetit.Model. Header doc (lines 48-142) is the full assumptions ledger for keyrot_recent_tip_ancestor_agreement.

**Imports:** `MoltPetit.Model.KeyStealingUnique`, `MoltPetit.Model.KeyStealingHorizonCore`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `MoltPetit.Model.KeyStealingSigned` | def | 158 | Block B carries a signature verifying under its slot-producer's registered key at SOME version j (existential version) — the Signed-domain of hash injectivity for all mode-1 (validSignedChainK') theorems. Weaker than SignedDeclared (declared version B.keyIndex). |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `MoltPetit.Model.keyStealingSigned_of_mem` | 169 | hVal:validSignedChainK'; hB:B ∈ stripSigs sc | `KeyStealingSigned n ops registry B` | Discharges genesis-or-signed coverage from validator acceptance (sigsOk half); used as `fun b hb => Or.inr (keyStealingSigned_of_mem hVal hb)` to build hSig : ∀ b ∈ stripSigs sc, b = G ∨ KeyStealingSigned n ops registry b. |
| `MoltPetit.Model.keyrot_deep_block_agreement` | 204 | hn:1 ≤ n; hΔ:n ≤ Δconf; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hBudget:ByzantineBounded; hVal:validSignedChainK'; hVal':validSignedChainK'; hSig:∀; hSig':∀; hRecent:∃; hRecent':∃; hGenesis:CommonPrefixUpTo; hB:blockAt?; hB':blockAt?; hD:blockAt?; hD':blockAt?; hDeep:k + n ≤ m; hDeep':k + n ≤ m' | `B = B'` | Deep-block core with explicit n-deep descendant witnesses. Proof: validChainK'_sound → ValidChain; idInjective_keyrot hHash hSig hSig'; honestSlotsUnique_keyrot_horizon hn hΔ (versionedUnforgeable_of_keyStealingEUFCMA hEUF) hBudget hId hVal hVal' hRecent hRecent'; deep_block_agreement_of_height_depth. honestSigned typed Nat → Nat → Option Block (= SigningLog). |
| `MoltPetit.Model.keyrot_deep_block_agreement_of_length` | 250 | hn:1 ≤ n; hΔ:n ≤ Δconf; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective Signed G; hBudget:ByzantineBounded; hVal:validSignedChainK'; hVal':validSignedChainK'; hSig:∀; hSig':∀; hRecent:∃; hRecent':∃; hGenesis:CommonPrefixUpTo; hB:blockAt?; hB':blockAt?; hLen:k; hLen':k | `B = B'` | Depth from length; builds descendants (stripSigs sc)[k+n] and calls keyrot_deep_block_agreement. |
| `MoltPetit.Model.keyrot_recent_tip_ancestor_agreement` | 328 | hn:1 ≤ n; hΔ:n ≤ Δconf; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hBudget:ByzantineBounded; hVal:validSignedChainK'; hVal':validSignedChainK'; hHead:blockAt?; hHead':blockAt?; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hTipHeight:sTip.height = sTip'.height; hB:blockAt?; hB':blockAt? | `B = B'` | Mode-1 headline, GLOBAL budget, genesis at index 0 REQUIRED (hHead/hHead'). hSig discharged internally via keyStealingSigned_of_mem; hGenesis built from hHead/hHead'. Equal tip heights ⇒ equal lengths via ValidChain.1 (SequentialHeights) + blockAt_getLast. |
| `MoltPetit.Model.keyrot_recent_tip_ancestor_mem` | 393 | hn:1 ≤ n; hΔ:n ≤ Δconf; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hBudget:ByzantineBounded; hVal:validSignedChainK'; hVal':validSignedChainK'; hHead:blockAt?; hHead':blockAt?; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLe:sTip.height ≤ sTip'.height; hB:blockAt? | `∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B` | Membership (unequal heights) form; sc must be the lower-or-equal-tipped chain and the budget is keyed to stripSigs sc. No hLong'/hTipHeight/hB'. |
| `MoltPetit.Model.keyrot_lossonly_recent_tip_ancestor_agreement` | 483 | hn:1 ≤ n; hΔ:n ≤ Δconf; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hBudget:ByzantineBounded n rented; hVal:validSignedChainK'; hVal':validSignedChainK'; hHead:blockAt?; hHead':blockAt?; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hTipHeight:sTip.height = sTip'.height; hB:blockAt?; hB':blockAt? | `B = B'` | Stolen := ⊥ specialisation; budget is plain rent (chain-independent) via `by rw [badKeyrotOn_lossOnly]; exact hBudget`. |
| `MoltPetit.Model.keyrot_lossonly_recent_tip_ancestor_mem` | 518 | hn:1 ≤ n; hΔ:n ≤ Δconf; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hBudget:ByzantineBounded n rented; hVal:validSignedChainK'; hVal':validSignedChainK'; hHead:blockAt?; hHead':blockAt?; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLe:sTip.height ≤ sTip'.height; hB:blockAt? | `∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B` | Loss-only membership form. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Results/KeyStealingScheduleResults.lean

**Purpose:** Mode-2 (scheduled rotation) main-theorem set over validSignedChainSched/badSched: anchor-free (only shared genesis + recency), chain-INDEPENDENT global budget, no Δconf. Plus the tip-only staleness theorem sched_oldkey_fork_stale. Namespace MoltPetit.Model.

**Imports:** `MoltPetit.Model.KeyStealingSchedule`

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `MoltPetit.Model.sched_deep_block_agreement_of_length` | 83 | hn:1 ≤ n; hUnf:SchedUnforgeable; hHash:SignedHashInjective; hBudget:ByzantineBounded; hVal:validSignedChainSched; hVal':validSignedChainSched; hHead:blockAt?; hHead':blockAt?; hRecent:∃; hRecent':∃; hB:blockAt?; hB':blockAt?; hLen:k; hLen':k | `B = B'` | Wraps sched_deep_block_agreement (KeyStealingSchedule.lean). schedule : Nat → Nat is unconstrained. |
| `MoltPetit.Model.sched_recent_tip_ancestor_agreement` | 137 | hn:1 ≤ n; hUnf:SchedUnforgeable; hHash:SignedHashInjective; hBudget:ByzantineBounded; hVal:validSignedChainSched; hVal':validSignedChainSched; hHead:blockAt?; hHead':blockAt?; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hTipHeight:sTip.height = sTip'.height; hB:blockAt?; hB':blockAt? | `B = B'` | Uses validChain_of_validSignedChainSched for ValidChain. Genesis at index 0 required. |
| `MoltPetit.Model.sched_recent_tip_ancestor_mem` | 179 | hn:1 ≤ n; hUnf:SchedUnforgeable; hHash:SignedHashInjective; hBudget:ByzantineBounded; hVal:validSignedChainSched; hVal':validSignedChainSched; hHead:blockAt?; hHead':blockAt?; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLe:sTip.height ≤ sTip'.height; hB:blockAt? | `∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B` | Aliased into Molt as Molt.sched_recent_tip_ancestor_mem (Rotation.lean:334). |
| `MoltPetit.Model.sched_oldkey_fork_stale` | 242 | hVal:validSignedChainSched; hEraOver:schedule; hTip:(stripSigs; hJt:t.keyIndex ≤ J | `¬ now ≤ t.slot + Δ` | Implicit binders named {σ sk pk : Type} {n : Nat} {schedule} {ops} {registry} {sc} {J now Δ : Nat} {t : Block}; no hn. Proof: rotated_key_dead_sched hVal hsbmem gives schedule t.slot ≤ t.keyIndex. Axioms: [propext, Quot.sound] only. |

## /etheron-pod/mini-consensus-lean/Molt/Rotation.lean

**Purpose:** Paper §6.3 presentation of key rotation: fresh Molt-namespace definitions for the three modes' validators and corruption predicates, *_eq_core bridges to MoltPetit.Model, loss-only collapses, the mode-1 client refresh rule (anchor age explicit, trailing-window budget), mode-2/3 anchor-free safety wrappers, and aliases/abbrevs re-exporting core results. Namespace Molt; core names always fully qualified (no `open MoltPetit.Model`).

**Imports:** `Molt.Results`, `MoltPetit.Results.KeyStealingResults`, `MoltPetit.Results.KeyStealingScheduleResults`, `MoltPetit.Model.KeyStealingHorizon`, `MoltPetit.Model.KeyStealingLockstep`, `MoltPetit.Model.KeyStealingCert`, `MoltPetit.Model.KeyStealingScheduleCert`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `Molt.keyMonoOk` | def (structural recursion) | 33 | In-band monotone rule: same-producer key versions never decrease along the chain. Bridged by induction (NOT rfl). |
| `Molt.validChainK` | def | 44 | Indexed validator: structural validity + monotone rule. |
| `Molt.keyFloor` | def | 57 | Seat i's floor: highest key version it has used anywhere in c (rfl-bridged). |
| `Molt.confirmedPrefix` | def | 66 | Blocks at least Δconf slots before s (rfl-bridged). |
| `Molt.inForce` | def | 72 | Version in force for seat i at slot s: floor over the confirmed prefix (rfl-bridged). |
| `Molt.inForcePinned` | def | 80 | The ≤-pin: no block declares a version below the in-force one (rfl-bridged). |
| `Molt.validChainK'` | def | 85 | Mode-1 unsigned validator (bridged by simp, not rfl). |
| `Molt.validSignedChainK'` | def | 89 | Mode-1 signed validator (bridged by simp, not rfl — must `rw [validSignedChainK'_eq_core]` before passing to core). |
| `Molt.badKeyrot` | def | 100 | Mode-1 corruption predicate, keyed to witness chain c₀ (rfl = MoltPetit.Model.badKeyrotOn). |
| `Molt.KeyStealingEUFCMA` | abbrev | 108 | Mode-1 unforgeability surface (core structure; its field is stated at MoltPetit.Model.validSignedChainK'). |
| `Molt.KeyStealingSigned` | abbrev | 112 | Mode-1 Signed domain for hash injectivity. |
| `Molt.schedPin` | def | 119 | Mode-2 pin (rfl = MoltPetit.Model.schedPinned). |
| `Molt.validSignedChainSched` | def | 124 | Mode-2 signed validator (simp-bridged, not rfl). |
| `Molt.SchedUnforgeable` | abbrev | 131 | Mode-2 unforgeability surface. |
| `Molt.badSched` | abbrev | 134 | Mode-2 chain-independent corruption predicate: rented s ∨ ∃ j, schedule s ≤ j ∧ Stolen (producerForSlot n s) j. |
| `Molt.SignedDeclared` | abbrev | 137 | Signed domain at the DECLARED version (modes 2/3): ∃ sig, ops.verify (registry (producerForSlot n B.slot) B.keyIndex) B sig = true. |
| `Molt.noMixing` | def (structural recursion) | 144 | Mode-3 roster-wide no-mixing rule (induction-bridged = MoltPetit.Model.lockstepOk). |
| `Molt.validSignedChainLock` | def | 155 | Mode-3 signed validator (simp-bridged). |
| `Molt.LockstepPackage` | abbrev | 164 | Mode-3 hypothesis package (fields: mono, unforgeable : SchedCoreUnforgeable n (fun _ => 0) …, declared, hashInj : SignedHashInjective (SignedDeclared n ops registry) G, genesis_gen, rentBound R, exposedBound T, budget_le : R + T ≤ maxByzantine n). |
| `Molt.keyrot_recent_certified_suffix_agreement` | alias | 308 | Mode-1 certificate-level agreement under the GLOBAL budget (docstring: anchored/trailing form is future work). |
| `Molt.GroundedCertK` | abbrev | 314 | Mode-1 certificate grounding with floor snapshot. |
| `Molt.sched_recent_certified_suffix_agreement` | alias | 321 | Mode-2 certificate-level agreement. |
| `Molt.sched_recent_tip_ancestor_agreement_horizon` | alias | 329 | Mode-2 horizon-scoped (ByzantineBoundedFrom H) equal-height agreement, no genesis hypothesis. |
| `Molt.sched_recent_tip_ancestor_mem` | alias | 334 | Mode-2 membership form, global budget. |
| `Molt.sched_recent_tip_ancestor_mem_horizon` | alias | 339 | Mode-2 membership form, horizon budget. |
| `Molt.lockstep_recent_tip_ancestor_mem` | alias | 343 | Mode-3 membership form. |
| `Molt.same_block_same_prefix` | alias | 348 | Shared block at index m ⇒ shared block at every k ≤ m (parent-id chaining); see Safety.lean entry for the full statement. |
| `Molt.GroundedCertSched` | abbrev | 352 | Mode-2 certificate grounding. |
| `Molt.sched_oldkey_fork_stale` | alias | 356 | Retired-generation tip fails recency. |
| `Molt.lockstep_declares_rosterGen` | alias | 361 | Mode-3 pinning theorem. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `Molt.validChainK_structural` | 50 | h:validChainK n c = true | `validChain n c = true` |  |
| `Molt.keyMonoOk_eq_core` | 168 | — | `keyMonoOk = MoltPetit.Model.keyMonoOk` | Proved by funext + induction + simp [producer_eq_core]; NOT rfl. |
| `Molt.keyFloor_eq_core` | 176 | — | `keyFloor = MoltPetit.Model.keyFloor` | rfl |
| `Molt.confirmedPrefix_eq_core` | 177 | — | `confirmedPrefix = MoltPetit.Model.confirmedPrefix` | rfl |
| `Molt.inForce_eq_core` | 179 | — | `inForce = MoltPetit.Model.inForce` | rfl |
| `Molt.inForcePinned_eq_core` | 180 | — | `inForcePinned = MoltPetit.Model.inForcePinned` | rfl |
| `Molt.badKeyrot_eq_core` | 182 | — | `badKeyrot = MoltPetit.Model.badKeyrotOn` | VERBATIM: `theorem badKeyrot_eq_core : badKeyrot = MoltPetit.Model.badKeyrotOn := rfl` — the canonical rfl-bridge example. |
| `Molt.schedPin_eq_core` | 183 | — | `schedPin = MoltPetit.Model.schedPinned` | rfl |
| `Molt.validChainK_eq_core` | 185 | — | `validChainK = MoltPetit.Model.validChainK` | funext n c; simp only [validChainK, MoltPetit.Model.validChainK, validChain_eq_core, keyMonoOk_eq_core] |
| `Molt.validChainK'_eq_core` | 190 | — | `validChainK' = MoltPetit.Model.validChainK'` | simp-bridge. |
| `Molt.validSignedChainK'_eq_core` | 196 | — | `(validSignedChainK' (σ := σ) (sk := sk) (pk := pk)) = MoltPetit.Model.validSignedChainK'` | VERBATIM non-rfl bridge: `theorem validSignedChainK'_eq_core {σ sk pk : Type} :\n    (validSignedChainK' (σ := σ) (sk := sk) (pk := pk))\n      = MoltPetit.Model.validSignedChainK' := by\n  funext n Δconf ops registry sc\n  simp only [validSignedChainK', MoltPetit.Model.validSignedChainK',\n    sigsOk_eq_core, validChainK'_eq_core, stripSigs_eq_core]`. Used as `rw [validSignedChainK'_eq_core] at hVal hVal'` in every Molt mode-1 theorem. |
| `Molt.validSignedChainSched_eq_core` | 203 | — | `(validSignedChainSched (σ := σ) (sk := sk) (pk := pk)) = MoltPetit.Model.validSignedChainSched` | simp-bridge. |
| `Molt.noMixing_eq_core` | 210 | — | `noMixing = MoltPetit.Model.lockstepOk` | induction-bridge. |
| `Molt.validSignedChainLock_eq_core` | 217 | — | `(validSignedChainLock (σ := σ) (sk := sk) (pk := pk)) = MoltPetit.Model.validSignedChainLock` | simp-bridge. |
| `Molt.badKeyrot_lossOnly` | 230 | (explicit args) n Δconf : Nat, rented… | `badKeyrot n Δconf rented (fun _ _ => False) c₀ = rented` | = MoltPetit.Model.badKeyrotOn_lossOnly. Axioms [propext, Quot.sound]. |
| `Molt.badSched_lossOnly` | 239 | (explicit args) n : Nat, schedule : N… | `badSched n schedule rented (fun _ _ => False) = rented` | Axioms [propext, Quot.sound]. |
| `Molt.exposedSched_lossOnly` | 248 | (explicit args) n : Nat, schedule : N… | `MoltPetit.Model.exposedProducersSched n schedule (fun _ _ => False) u = ∅` |  |
| `Molt.client_refresh_rule` | 267 | hn:1 ≤ n; hΔ:n ≤ Δconf; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hA:A ∈ stripSigs sc; hA':A ∈ stripSigs sc'; hFresh:now ≤ A.slot + H; hBudget:now; hVal:validSignedChainK'; hVal':validSignedChainK'; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hTipHeight:sTip.height = sTip'.height; hB:blockAt?; hB':blockAt? | `B = B'` | Paper Theorem 3 (horizon form). NO hHead/hHead' (genesis-free; anchor A of arbitrary age replaces it). Implicit {A : Block} {H : Nat} {G : Block}. Proof: `rw [validSignedChainK'_eq_core] at hVal hVal'` then `exact MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored hn hΔ hEUF hHash hA hA' (fun u hu => hBudget u (by omega)) hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'`. The anchored core's guard `A.slot + 1 ≤ u + n` plus hFresh gives `now < u + n + H` by omega; hBudget's body is defeq to the core's (badSlotsIn, badKeyrot, faultBudget are rfl-bridges), so no rewrite needed on it. |
| `Molt.scheduled_client_safety` | 369 | hn:1 ≤ n; hUnf:SchedUnforgeable; hHash:SignedHashInjective; hBudget:FaultBounded; hVal:validSignedChainSched; hVal':validSignedChainSched; hHead:blockAt?; hHead':blockAt?; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hTipHeight:sTip.height = sTip'.height; hB:blockAt?; hB':blockAt? | `B = B'` | Paper Theorem 4. `rw [validSignedChainSched_eq_core] at hVal hVal'` then exact MoltPetit.Model.sched_recent_tip_ancestor_agreement. FaultBounded passes directly (rfl = ByzantineBounded). |
| `Molt.lockstep_client_safety` | 406 | hn:1 ≤ n; hP:LockstepPackage; hVal:validSignedChainLock; hVal':validSignedChainLock; hHead:blockAt?; hHead':blockAt?; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hTipHeight:sTip.height = sTip'.height; hB:blockAt?; hB':blockAt? | `B = B'` | Paper Theorem 5; wraps MoltPetit.Model.lockstep_recent_tip_ancestor_agreement hn hP … |

## /etheron-pod/mini-consensus-lean/Molt/ClientRule.lean

**Purpose:** Mode-1 single-constant client contract: deep_block_span (the n-deep anchor is < 2n slots below the tip), stay_recent_client_safe (client_refresh_rule at H := 4n−1, budget on trailing < 5n slots), sync_rule (Δconf := n, no Δconf in statement) and sync_rule_mem (membership form). Namespace Molt.

**Imports:** `Molt.Rotation`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `Molt.countP_add_le_countP` | private theorem | 27 | Disjoint refinements' counts sum below q's count. PRIVATE — not reusable from a new file. |
| `Molt.countP_between_le` | private theorem | 55 | At most k chain blocks with slots in (A.slot, D.slot] when A, D are k indices apart. PRIVATE. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `Molt.deep_block_span` | 123 | hn:1 ≤ n; hV:ValidChain n c; hA:blockAt? c m = some A; hD:blockAt? c (m + n) = some D | `D.slot < A.slot + 2 * n` | Public. Uses Molt.blockAt? (rewrites via blockAt?_eq_core), core quorum = (2n+2)/3 by rfl, MaturedWindowsDense at u = A.slot+1 and A.slot+1+n. ValidChain here is the Molt abbrev (= core). |
| `Molt.stay_recent_client_safe` | 174 | hn:1 ≤ n; hΔ:n ≤ Δconf; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hVPrev:validSignedChainK'; hTipPrev:(stripSigs; hRecPrev:t ≤ tipPrev.slot + n; hLongPrev:n; hAnchor:blockAt?; hCadence:now ≤ t + n; hA:A ∈ stripSigs sc; hA':A ∈ stripSigs sc'; hBudget:now; hVal:validSignedChainK'; hVal':validSignedChainK'; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hTipHeight:sTip.height = sTip'.height; hB:blockAt?; hB':blockAt? | `B = B'` | Implicit {sc sc' scPrev : SignedChain Sig} {A : Block} {t : Nat} {tipPrev : Block} {G : Block}. Derivation: ValidChain of scPrev via rw [validSignedChainK'_eq_core]; rw [MoltPetit.Model.validSignedChainK', Bool.and_eq_true]; (MoltPetit.Model.validChainK'_sound h.2).1; tipPrev at index length−1 via MoltPetit.Model.blockAt_getLast; deep_block_span ⇒ tipPrev.slot < A.slot + 2n; omega ⇒ hFresh : now ≤ A.slot + (4 * n - 1); client_refresh_rule with (fun u hu => hBudget u (by omega)). |
| `Molt.sync_rule` | 238 | hn:1 ≤ n; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hVPrev:validSignedChainK'; hTipPrev:(stripSigs; hRecPrev:t ≤ tipPrev.slot + n; hLongPrev:n; hAnchor:blockAt?; hCadence:now ≤ t + n; hA:A ∈ stripSigs sc; hA':A ∈ stripSigs sc'; hBudget:now; hVal:validSignedChainK'; hVal':validSignedChainK'; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hTipHeight:sTip.height = sTip'.height; hB:blockAt?; hB':blockAt? | `B = B'` | Paper Theorem 3 final form: Δconf fixed to n everywhere (KeyStealingEUFCMA n n, validSignedChainK' n n, badKeyrot n n). Term-mode: stay_recent_client_safe hn (Nat.le_refl n) … |
| `Molt.sync_rule_mem` | 284 | hn:1 ≤ n; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hVPrev:validSignedChainK'; hTipPrev:(stripSigs; hRecPrev:t ≤ tipPrev.slot + n; hLongPrev:n; hAnchor:blockAt?; hCadence:now ≤ t + n; hA:A ∈ stripSigs sc; hA':A ∈ stripSigs sc'; hBudget:now; hVal:validSignedChainK'; hVal':validSignedChainK'; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hLe:sTip.height ≤ sTip'.height; hB:blockAt? | `∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B` | Membership form; NOTE it keeps hLong' (unlike the core mem forms) because keyrot_recent_tip_ancestor_mem_anchored requires hLong'. Goes directly to MoltPetit.Model.keyrot_recent_tip_ancestor_mem_anchored hn (Nat.le_refl n) hEUF hHash hA hA' (fun u hu => hBudget u (by omega)) hVal₁ hVal₁' hTipS hTipS' hRecent hRecent' hLong hLong' hLe hB after rw [validSignedChainK'_eq_core] on copies of hVal/hVal'. |

## /etheron-pod/mini-consensus-lean/Molt/MaxSync.lean

**Purpose:** Both directions of the maximum sync period: max_sync_period (parametric cadence F, budget on windows with now < u + F + 4n) and the accumulation lemmas (inForce_mono, census_accumulates, census_accumulates_later_thefts, no_budget_beyond) showing a longer cadence is no assumption at all. Namespace Molt.

**Imports:** `Molt.ClientRule`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `Molt.foldl_max_le'` | private theorem | 45 | PRIVATE foldl-max helper. |
| `Molt.acc_le_foldl_max` | private theorem | 54 | PRIVATE. |
| `Molt.mem_le_foldl_max'` | private theorem | 60 | PRIVATE. |
| `Molt.foldl_max_zero_mono'` | private theorem | 69 | PRIVATE — a new module needing these must re-prove them (or use core KeyIndex.lean helpers, which are also private there). |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `Molt.producer_slot_in_window` | 30 | hn:1 ≤ n; hi:i < n; (u:Nat) explicit | `∃ s, u ≤ s ∧ s < u + n ∧ producer n s = i` | Axioms [propext, Quot.sound]. |
| `Molt.inForce_mono` | 79 | h:s ≤ s' | `inForce n Δconf c i s ≤ inForce n Δconf c i s'` | Implicit {n Δconf : Nat} {c : Chain} {i : Nat} {s s' : Nat}. Axioms [propext, Quot.sound]. |
| `Molt.census_accumulates` | 95 | hP:∀ | `P.card ≤ (badSlotsIn (badKeyrot n Δconf rented Stolen c₀) u n).card` | Implicit {n Δconf} {rented} {Stolen} {c₀ : Chain} {u : Nat} {P : Finset Nat}. Uses `classical` and Finset.card_le_card_of_injOn with choose. |
| `Molt.census_accumulates_later_thefts` | 135 | hn:1 ≤ n; hP:∀ | `P.card ≤ (badSlotsIn (badKeyrot n Δconf rented Stolen c₀) u n).card` | Theft at-or-after the window's last slot charges the window (via inForce_mono + producer_slot_in_window). |
| `Molt.no_budget_beyond` | 156 | hP:∀; hbig:faultBudget n < P.card | `¬ (badSlotsIn (badKeyrot n Δconf rented Stolen c₀) u n).card ≤ faultBudget n` | For any rented. |
| `Molt.max_sync_period` | 176 | hn:1 ≤ n; hΔ:n ≤ Δconf; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hVPrev:validSignedChainK'; hTipPrev:(stripSigs; hRecPrev:t ≤ tipPrev.slot + n; hLongPrev:n; hAnchor:blockAt?; hCadence:now ≤ t + F; hA:A ∈ stripSigs sc; hA':A ∈ stripSigs sc'; hBudget:now; hVal:validSignedChainK'; hVal':validSignedChainK'; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hTipHeight:sTip.height = sTip'.height; hB:blockAt?; hB':blockAt? | `B = B'` | Implicit {n Δconf F : Nat}. hFresh : now ≤ A.slot + (F + 3 * n - 1) then client_refresh_rule with H := F + 3n − 1. No membership (_mem) form of max_sync_period exists. |

## /etheron-pod/mini-consensus-lean/Molt/Results.lean

**Purpose:** Paper §6.1–6.2 static-key headline theorems transported (light_client_safety, forged_time_bound), the timed-model abbrevs, and the fresh Molt.blockAt? definition that every later Molt module uses. Namespace Molt.

**Imports:** `Molt.Assumptions`, `MoltPetit.Results.Results`, `MoltPetit.Model.TimedSig`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `Molt.TimedLog` | abbrev | 25 | Real-slot signing log. |
| `Molt.AvailableAt` | def | 29 | B exists by real slot R (rfl-bridged). |
| `Molt.TimedExecution` | abbrev | 36 | Timed execution model. |
| `Molt.blockAt?` | def | 39 | Block at list index h; rfl-bridged (blockAt?_eq_core). Inside namespace Molt, unqualified `blockAt?` is THIS one. |
| `Molt.NoBackdate` | abbrev | 140 | No back-dating onto an honest stamp. |
| `Molt.projectSigned` | noncomputable abbrev | 143 | Stamped signing log from a real-time log. |
| `Molt.forged_chain_time_bound` | alias | 128 | From-genesis forged-time form. |
| `Molt.forged_suffix_lag` | alias | 131 | Lag reading. |
| `Molt.sigUnforgeableRecent_of_timed` | alias | 135 | Assumption 2(c) derived in the timed model. |
| `Molt.noBackdate_independent` | alias | 148 | n = 2 independence witness. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `Molt.availableAt_eq_core` | 41 | — | `AvailableAt = MoltPetit.Model.AvailableAt` | rfl |
| `Molt.blockAt?_eq_core` | 42 | — | `blockAt? = MoltPetit.Model.blockAt?` | rfl |
| `Molt.light_client_safety` | 54 | hn:1 ≤ n; hBudget:FaultBounded n bad; hSig:SigUnforgeableRecent; hHash:SignedHashInjective Signed G; hcl:GroundedCert n Signed G cl; hcl':GroundedCert n Signed G cl'; hTipS:(s₁; hTipS':(s₁'; hLink:s₁.height; hLinks:linksOk (s₁ :: srest) = true; hDense:∀; hLink':s₁'.height; hLinks':linksOk; hDense':∀; hSigned:∀ B ∈ s₁ :: srest, Signed B; hSigned':∀; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hB:blockAt?; hB':blockAt?; hHeight:cl.tipHeight; hDeep:i + n < (s₁ :: srest).length; hDeep':i' | `B = B'` | Paper Theorem 1; rw [linksOk_eq_core] then MoltPetit.Model.recent_certified_suffix_agreement. |
| `Molt.forged_time_bound` | 110 | hn:2 ≤ n; hexec:TimedExecution n bad log G; hBudget:FaultBounded n bad; hValid:ValidChain n c; hGprev:G.prev = none; hAvail:∀; hk₀:1 ≤ k₀; hF:blockAt? c k₀ = some F; hFr:F ∈ log r₀; hFmin:∀ r < r₀, F ∉ log r; hForged:∀; hTip:c.getLast? = some tip | `quorum n * ((tip.slot - F.slot) / n) ≤ faultBudget n * ((rNow - r₀) / n + 1)` | Paper Theorem 2; term-mode call of MoltPetit.Model.forged_suffix_time_bound (all rfl-bridged names pass directly). |

## /etheron-pod/mini-consensus-lean/Molt/Axioms.lean

**Purpose:** Axiom audit for every Molt headline theorem: 31 `#guard_msgs in #print axioms` blocks. Docstring: 'Same discipline as MoltPetit/Results/Axioms.lean: a guarded #print axioms per headline theorem, so lake build Molt fails if any theorem ever picks up an axiom beyond the three classical ones. Extend this file with every new headline theorem.' No namespace, no defs.

**Imports:** `Molt.Results`, `Molt.Rotation`, `Molt.ClientRule`, `Molt.MaxSync`, `Molt.Liveness`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `guard: Molt.client_refresh_rule` | guard block (VERBATIM lines 41-44) | 41 | The guard idiom: a `--` comment line, a `/-- info: '<fully.qualified.name>' depends on axioms: [<list>] -/` docstring, `#guard_msgs in`, `#print axioms <name>`. Docstring must match the emitted message byte-for-byte. |
| `guard: Molt.light_client_safety` | guard | 17 |  |
| `guard: Molt.forged_time_bound` | guard | 22 |  |
| `guard: Molt.badKeyrot_lossOnly` | guard | 27 | NOTE two-axiom set. |
| `guard: Molt.badSched_lossOnly` | guard | 32 | two-axiom set |
| `guard: Molt.exposedSched_lossOnly` | guard | 37 |  |
| `guard: Molt.deep_block_span` | guard | 47 |  |
| `guard: Molt.stay_recent_client_safe` | guard | 52 |  |
| `guard: Molt.sync_rule` | guard | 57 |  |
| `guard: Molt.sync_rule_mem` | guard | 62 |  |
| `guard: Molt.lockstep_declares_rosterGen` | guard | 67 | guard on an alias works |
| `guard: Molt.sched_oldkey_fork_stale` | guard | 72 | two-axiom set (alias) |
| `guard: Molt.max_sync_period` | guard | 77 |  |
| `guard: Molt.producer_slot_in_window` | guard | 82 | two-axiom set |
| `guard: Molt.inForce_mono` | guard | 87 | two-axiom set |
| `guard: Molt.census_accumulates` | guard | 92 |  |
| `guard: Molt.census_accumulates_later_thefts` | guard | 97 |  |
| `guard: Molt.no_budget_beyond` | guard | 102 |  |
| `guard: Molt.keyrot_recent_certified_suffix_agreement` | guard | 107 |  |
| `guard: Molt.sched_recent_certified_suffix_agreement` | guard | 111 |  |
| `guard: Molt.sched_recent_tip_ancestor_agreement_horizon` | guard | 116 | single-line message even at this length (Molt. prefix short) |
| `guard: Molt.sched_recent_tip_ancestor_mem` | guard | 120 |  |
| `guard: Molt.sched_recent_tip_ancestor_mem_horizon` | guard | 124 |  |
| `guard: Molt.lockstep_recent_tip_ancestor_mem` | guard | 128 |  |
| `guard: Molt.same_block_same_prefix` | guard | 132 | two-axiom set (alias) |
| `guard: Molt.scheduled_client_safety` | guard | 137 |  |
| `guard: Molt.lockstep_client_safety` | guard | 142 |  |
| `guard: Molt.sigUnforgeableRecent_of_timed` | guard | 147 |  |
| `guard: Molt.noBackdate_independent` | guard | 151 | two-axiom set |
| `guard: Molt.production_liveness` | guard | 156 |  |
| `guard: Molt.global_liveness` | guard | 160 |  |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingHorizon.lean

**Purpose:** SUPPORTING (partial map, read for the anchored forms Molt/ consumes). Mode-1 genesis-free forms: horizon (global budget, no hHead) and ANCHORED (budget only on windows ending after the anchor's slot). Namespace MoltPetit.Model. Already imported by Molt.Rotation.

**Imports:** `MoltPetit.Model.KeyStealingSafety`, `MoltPetit.Model.KeyStealingUnique`, `MoltPetit.Model.KeyStealingHorizonCore`, `MoltPetit.Results.KeyStealingResults`, `MoltPetit.Model.KeyStealingScheduleHorizon`

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_horizon` | 69 | hn:1 ≤ n; hΔ:n ≤ Δconf; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hSig:∀; hSig':∀; hBudget:ByzantineBounded; hVal:validSignedChainK'; hVal':validSignedChainK'; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hTipHeight:sTip.height = sTip'.height; hB:blockAt?; hB':blockAt? | `B = B'` | No hHead/hHead'. Uses horizon_shared_prefix with (hBudget _). |
| `MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored` | 134 | hn:1 ≤ n; hΔ:n ≤ Δconf; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hA:A ∈ stripSigs sc; hA':A ∈ stripSigs sc'; hBudgetFrom:A.slot; hVal:validSignedChainK'; hVal':validSignedChainK'; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hTipHeight:sTip.height = sTip'.height; hB:blockAt?; hB':blockAt? | `B = B'` | THE anchored form Molt.client_refresh_rule wraps. Budget guard `A.slot + 1 ≤ u + n` = window [u,u+n) ends after A.slot (its last slot u+n−1 ≥ A.slot). Only windows actually consulted: u = sTip.slot + 1 − n (lower tip). Genesis-free; G appears only as the exemption in hHash. Guarded message in MoltPetit/Results/Axioms.lean WRAPS over 3 lines. |
| `MoltPetit.Model.keyrot_recent_tip_ancestor_mem_anchored` | 222 | hn:1 ≤ n; hΔ:n ≤ Δconf; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hA:A ∈ stripSigs sc; hA':A ∈ stripSigs sc'; hBudgetFrom:A.slot; hVal:validSignedChainK'; hVal':validSignedChainK'; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hLe:sTip.height ≤ sTip'.height; hB:blockAt? | `∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B` | Note hLong' IS required here (unlike keyrot_recent_tip_ancestor_mem). Wrapped by Molt.sync_rule_mem. |
| `MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_horizon_of_valid` | 310 | hn:1 ≤ n; hΔ:n ≤ Δconf; hEUF:KeyStealingEUFCMA; hHash:SignedHashInjective; hBudget:ByzantineBounded; hVal:validSignedChainK'; hVal':validSignedChainK'; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hTipHeight:sTip.height = sTip'.height; hB:blockAt?; hB':blockAt? | `B = B'` | Global budget, genesis-free, validator-discharged coverage. Not aliased in Molt/. |
| `MoltPetit.Model.honestSlotsUnique_keyrot_anchored (KeyStealingHorizonCore.lean:258)` | 258 | hn:1 ≤ n; hΔ:n ≤ Δconf; hUnf:VersionedUnforgeable; hA:A ∈ stripSigs sc; hA':A ∈ stripSigs sc'; hBudgetFrom:A.slot; hId:IdInjective; hVal:validSignedChainK'; hVal':validSignedChainK'; hRecent:∃; hRecent':∃ | `HonestSlotsUnique (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) (chainUnionRecord sc sc')` | Lives in MoltPetit/Model/KeyStealingHorizonCore.lean (line 258), listed here because it is the engine behind the anchored budget guard. hUnf obtained via versionedUnforgeable_of_keyStealingEUFCMA hEUF (KeyStealingUnique.lean:184). |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingScheduleHorizon.lean

**Purpose:** SUPPORTING (partial map). The horizon-scoped budget ByzantineBoundedFrom, the validator-agnostic top-window engine horizon_shared_prefix, and the mode-2 horizon theorems Molt/ aliases. Namespace MoltPetit.Model.

**Imports:** `(not read in full)`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `MoltPetit.Model.ByzantineBoundedFrom` | def | 70 | Budget required only of windows starting at or after H. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `MoltPetit.Model.byzantineBoundedFrom_of_bounded` | 75 | h:ByzantineBounded n bad | `ByzantineBoundedFrom H n bad` |  |
| `MoltPetit.Model.horizon_shared_prefix` | 161 | hn:1 ≤ n; hHonest:HonestSlotsUnique bad record; hId:IdInjective record; hValid:ValidChain n c; hValid':ValidChain n c'; hRec:ChainInRecord record c; hRec':ChainInRecord record c'; hTip:c.getLast? = some tip; hTip':c'.getLast? = some tip'; hle:tip.slot ≤ tip'.slot; hBudgetU:(badSlotsIn; hkdeep:k + n < c.length | `∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P` | Validator-agnostic engine: ONE window's budget (the lower tip's top window) + honest-slot uniqueness ⇒ shared block at every k that is n-deep in the lower chain. This is why anchored/trailing budgets suffice. |
| `MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon` | 247 | hn:1 ≤ n; hUnf:SchedUnforgeable; hHash:SignedHashInjective; hBudget:ByzantineBoundedFrom; hVal:validSignedChainSched; hVal':validSignedChainSched; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hLong':n < (stripSigs sc').length; hH:H + n ≤ sTip.slot + 1; hH':H + n ≤ sTip'.slot + 1; hTipHeight:sTip.height = sTip'.height; hB:blockAt?; hB':blockAt? | `B = B'` | No hHead/hHead'. Implicit {H : Nat}. |
| `MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon` | 308 | hn:1 ≤ n; hUnf:SchedUnforgeable; hHash:SignedHashInjective; hBudget:ByzantineBoundedFrom; hVal:validSignedChainSched; hVal':validSignedChainSched; hTipS:(stripSigs; hTipS':(stripSigs; hRecent:now ≤ sTip.slot + Δ; hRecent':now ≤ sTip'.slot + Δ; hLong:n < (stripSigs sc).length; hH:H + n ≤ sTip.slot + 1; hH':H + n ≤ sTip'.slot + 1; hLe:sTip.height ≤ sTip'.height; hB:blockAt? | `∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B` |  |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/Safety.lean

**Purpose:** SUPPORTING (partial map): the parent-id chaining lemma aliased as Molt.same_block_same_prefix.

**Imports:** `(not read in full)`

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `MoltPetit.Model.same_block_same_prefix` | 189 | hId:IdInjective record; hRec:ChainInRecord record c; hRec':ChainInRecord record c'; hP:ParentLinked c; hP':ParentLinked c'; (then ∀ {m : Nat} {B : Block}) blockA…; blockAt? c' m = some B; (∀ {k : Nat}) k ≤ m | `∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P` | Statement: `∀ {m : Nat} {B : Block}, blockAt? c m = some B → blockAt? c' m = some B → ∀ {k : Nat}, k ≤ m → ∃ P, …`. For signed chains instantiate record := chainUnionRecord sc sc' (KeyStealingUnique.lean:45), hRec := chainInRecord_left (:54), hRec' := chainInRecord_right (:60), hId := idInjective_keyrot hHash hSig hSig' (:70), hP := (ValidChain).2.2.1. Axioms [propext, Quot.sound]. |

## /etheron-pod/mini-consensus-lean/Molt/Assumptions.lean

**Purpose:** SUPPORTING: paper §5 assumption vocabulary in namespace Molt — the names a new Molt module writes budgets and hash injectivity with. All rfl-bridged.

**Imports:** `Molt.Verifier`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `Molt.SlotRecord` | abbrev | 19 | Nat → Finset Block |
| `Molt.ByzantineSlots` | abbrev | 22 | Nat → Prop |
| `Molt.ValidChain` | abbrev | 25 | Semantic validity: SequentialHeights ∧ StrictSlots ∧ ParentLinked ∧ MaturedWindowsDense n c (components .1, .2.1, .2.2.1, .2.2.2). |
| `Molt.SigningLog` | abbrev | 29 | = Nat → Nat → Option Block (the honestSigned type). |
| `Molt.badSlotsIn` | noncomputable def | 33 | Bad slots in [u, u+n) (rfl = core). |
| `Molt.FaultBounded` | def | 38 | Assumption 1 (rfl = MoltPetit.Model.ByzantineBounded). |
| `Molt.SigUnforgeableRecent` | abbrev | 45 | Static-key recency-scoped uniqueness. |
| `Molt.SignedHashInjective` | def | 50 | Assumption 3 (rfl = core). |
| `Molt.GroundedCert` | abbrev | 59 | Assumption 4. |
| `Molt.HonestBlocksCover` | def | 63 | Assumption 6 (liveness). |
| `Molt.HonestSlotsUnique` | def | 70 | rfl = core |
| `Molt.IdInjective` | def | 75 | rfl = core |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `Molt.badSlotsIn_eq_core / faultBounded_eq_core / signedHashInjective_eq_core / honestBlocksCover_eq_core / honestSlotsUnique_eq_core / idInjective_eq_core` | 81 | — | `badSlotsIn = MoltPetit.Model.badSlotsIn; FaultBounded = MoltPetit.Model.ByzantineBounded; SignedHashInjective = MoltPetit.Model.SignedHashInjective; HonestBlocksCover = …; HonestSlotsUnique = …; IdInjective = …` | all rfl (lines 81-90) |

## /etheron-pod/mini-consensus-lean/Molt/Protocol.lean

**Purpose:** SUPPORTING: paper §3 vocabulary (Block/Chain re-exported types; quorum, faultBudget, producer, validChain fresh) with bridges.

**Imports:** `MoltPetit.Model.Definitions`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `Molt.quorum` | def | 23 | rfl = MoltPetit.Model.quorum |
| `Molt.faultBudget` | def | 27 | rfl = MoltPetit.Model.maxByzantine |
| `Molt.producer` | def | 31 | rfl = MoltPetit.Model.producerForSlot |
| `Molt.Block` | abbrev | 44 | fields slot, height, prev, id, contentsHash, keyIndex |
| `Molt.Chain` | abbrev | 47 | List Block |
| `Molt.linksOk` | def (recursive) | 66 | induction-bridged (linksOk_eq_core, line 119) |
| `Molt.blockInWindow / windowCount / windowDense / denseSoFar` | def | 74 | density rule pieces (lines 74-89); windowDense/denseSoFar rfl-bridged; NOTE no windowCount_eq_core/blockInWindow_eq_core lemma exists (deep_block_span uses the core names directly). |
| `Molt.validChain` | def | 94 | simp-bridged (validChain_eq_core, line 129), NOT rfl. |

## /etheron-pod/mini-consensus-lean/Molt/Verifier.lean

**Purpose:** SUPPORTING: signature layer and certified-chain vocabulary in namespace Molt.

**Imports:** `Molt.Protocol`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `Molt.SigOps / KeyRegistry / SignedBlock / SignedChain` | abbrev | 21 | re-exported types (lines 21-32) |
| `Molt.stripSigs` | def | 35 | rfl-bridged (stripSigs_eq_core, line 147) |
| `Molt.sigOk / sigsOk` | def | 40 | rfl-bridged (sigOk_eq_core line 149, sigsOk_eq_core line 151) |
| `Molt.CertClaim / CertOps / CertifiedChain` | abbrev | 61 | certificate types |

## reuse_notes

IMPORTS FOR A NEW ADDITIVE Molt MODULE. `import Molt.MaxSync` transitively brings Molt.Protocol, Molt.Verifier, Molt.Assumptions, Molt.Results, Molt.Rotation, Molt.ClientRule and (through Molt.Rotation) MoltPetit.Results.KeyStealingResults, MoltPetit.Results.KeyStealingScheduleResults, MoltPetit.Model.KeyStealingHorizon (anchored forms), KeyStealingLockstep, KeyStealingCert, KeyStealingScheduleCert, and through those KeyStealingHorizonCore, KeyStealingScheduleHorizon (ByzantineBoundedFrom, horizon_shared_prefix), KeyStealingUnique (chainUnionRecord, chainInRecord_left/right, idInjective_keyrot, versionedUnforgeable_of_keyStealingEUFCMA, KeyStealingEUFCMA), KeyStealingSchedule, Safety (same_block_same_prefix), Soundness (blockAt_getLast), Model (exists_blockAt_of_mem, strictSlots_lt, exists_blockAt_of_le), Liveness (slot_le_tip_of_mem), KeyStealingSafety (strictSlots_unique). Only Molt.Liveness (aliases production_liveness, global_liveness, etc.) is outside that cone; a guard file for liveness names must `import Molt.Liveness`.

NAMESPACE / NAME-RESOLUTION IDIOM. Every Molt file is `namespace Molt … end Molt`; core names are always written fully qualified `MoltPetit.Model.X` — no Molt file does `open MoltPetit.Model`. Inside `namespace Molt`, unqualified `blockAt?`, `stripSigs`, `badSlotsIn`, `faultBudget`, `producer`, `validChain`, `validChainK'`, `validSignedChainK'`, `badKeyrot`, `inForce`, `FaultBounded`, `SignedHashInjective`, `KeyStealingSigned`, `KeyStealingEUFCMA`, `Block`, `Chain`, `ValidChain`, `SigOps`, `KeyRegistry`, `SignedChain`, `ByzantineSlots`, `SigningLog` resolve to the Molt versions. Type-level names (Block, Chain, ValidChain, SigOps, KeyRegistry, SignedChain, SigningLog, ByzantineSlots) and Prop-structures (KeyStealingEUFCMA, SchedUnforgeable, LockstepPackage, KeyStealingSigned, SignedDeclared, badSched) are `abbrev`s of the core — literally the same terms, no bridging needed. honestSigned is declared as `{honestSigned : SigningLog}` in Molt files and `Nat → Nat → Option Block` in core; identical.

THE *_eq_core BRIDGE IDIOM (two flavours; which one matters). Fresh computational definitions are re-declared in Molt and proven equal to the core original by a lemma named `<name>_eq_core`. (a) rfl-bridges — verbatim example: `theorem badKeyrot_eq_core : badKeyrot = MoltPetit.Model.badKeyrotOn := rfl` (Molt/Rotation.lean:182). Others: keyFloor, confirmedPrefix, inForce, inForcePinned, schedPin(=schedPinned), blockAt?, stripSigs, sigOk, sigsOk, badSlotsIn, FaultBounded(=ByzantineBounded), SignedHashInjective, quorum, faultBudget(=maxByzantine), producer(=producerForSlot), genesisOk, childOk, windowDense, denseSoFar, AvailableAt, HonestSlotsUnique, IdInjective. These are DEFEQ, so a hypothesis stated with the Molt name can be passed to a core theorem by `exact` with no rewrite — e.g. client_refresh_rule feeds `hBudget : ∀ u, now < u + n + H → (badSlotsIn (badKeyrot …) u n).card ≤ faultBudget n` as `(fun u hu => hBudget u (by omega))` straight into the core's `hBudgetFrom : ∀ u, A.slot + 1 ≤ u + n → (MoltPetit.Model.badSlotsIn (badKeyrotOn …) u n).card ≤ maxByzantine n`; and FaultBounded is passed where ByzantineBounded is expected. (b) NON-rfl bridges (funext + induction/simp): keyMonoOk, noMixing(=lockstepOk), linksOk, validChain, validChainK, validChainK', validSignedChainK', validSignedChainSched, validSignedChainLock, validSignedChain, validSuffix, validCertifiedChain, produceBlock?, selectChain. These are NOT defeq (separate structurally-recursive constants). Verbatim non-rfl example (Molt/Rotation.lean:196-201): `theorem validSignedChainK'_eq_core {σ sk pk : Type} : (validSignedChainK' (σ := σ) (sk := sk) (pk := pk)) = MoltPetit.Model.validSignedChainK' := by funext n Δconf ops registry sc; simp only [validSignedChainK', MoltPetit.Model.validSignedChainK', sigsOk_eq_core, validChainK'_eq_core, stripSigs_eq_core]`. Consumption idiom, used in EVERY Molt mode-1 theorem: `rw [validSignedChainK'_eq_core] at hVal hVal'` then `exact MoltPetit.Model.<core theorem> …`. Mode 2: `rw [validSignedChainSched_eq_core] at hVal hVal'`; mode 3: `rw [validSignedChainLock_eq_core]`. Keep a copy if the original is still needed (`have hVal₁ := hVal; rw [...] at hVal₁`, ClientRule.lean:333-335). Note `rw`/`simp` matching is syntactic even for rfl-bridges — deep_block_span does `rw [blockAt?_eq_core] at hA hD` before feeding core `MaturedWindowsDense` — while `exact`/application works up to defeq. Explicit universe-polymorphic-free `(σ := σ) (sk := sk) (pk := pk)` binder instantiation is required in the LHS of eq_core lemmas for definitions with implicit type args.

EXTRACTING ValidChain FROM A Molt VALIDATOR HYPOTHESIS (ClientRule.lean:216-220, verbatim): `have hVPrev' := hVPrev; rw [validSignedChainK'_eq_core] at hVPrev'; rw [MoltPetit.Model.validSignedChainK', Bool.and_eq_true] at hVPrev'; have hVc : MoltPetit.Model.ValidChain n (stripSigs scPrev) := (MoltPetit.Model.validChainK'_sound hVPrev'.2).1`. Tip at index length−1: `MoltPetit.Model.blockAt_getLast hTipPrev`. Height = index: `hVc.1 (blockAt_getLast hTipS)`. Mode 2: `MoltPetit.Model.validChain_of_validSignedChainSched hVal`.

BUDGET FORMS AND HOW THE ANCHOR AGE / TRAILING WINDOW ENTER. (1) Global: `ByzantineBounded n bad := ∀ u, (badSlotsIn bad u n).card ≤ maxByzantine n` (Molt: FaultBounded). Used by keyrot_recent_tip_ancestor_agreement/_mem, keyrot_lossonly_*, sched_* (Results files), scheduled_client_safety, lockstep (inside LockstepPackage as R+T ≤ maxByzantine n). (2) Anchored core: `hBudgetFrom : ∀ u, A.slot + 1 ≤ u + n → (badSlotsIn (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) u n).card ≤ maxByzantine n` — windows whose last slot u+n−1 is ≥ A.slot; anchor A of ARBITRARY age, hA : A ∈ stripSigs sc, hA' : A ∈ stripSigs sc'. The proof consults only u = sTip.slot + 1 − n (lower tip's top window) via horizon_shared_prefix, then same_block_same_prefix propagates down. (3) Trailing/age forms in Molt: client_refresh_rule takes `hFresh : now ≤ A.slot + H` and `hBudget : ∀ u, now < u + n + H → …≤ faultBudget n`; the wrapper derives the anchored guard by omega: A.slot + 1 ≤ u + n and now ≤ A.slot + H ⇒ now < u + n + H. stay_recent_client_safe: H := 4n−1, guard `now < u + 5 * n`, from hRecPrev : t ≤ tipPrev.slot + n, deep_block_span (tipPrev.slot < A.slot + 2n) and hCadence : now ≤ t + n ⇒ hFresh : now ≤ A.slot + (4 * n - 1). max_sync_period: hCadence : now ≤ t + F, guard `now < u + F + 4 * n`, hFresh : now ≤ A.slot + (F + 3 * n - 1). sync_rule/sync_rule_mem are stay_recent_client_safe / keyrot_recent_tip_ancestor_mem_anchored at Δconf := n (every occurrence: KeyStealingEUFCMA n n, validSignedChainK' n n, badKeyrot n n; hΔ := Nat.le_refl n). (4) Scheduled horizon: `ByzantineBoundedFrom H n bad := ∀ u, H ≤ u → …` with side conditions hH : H + n ≤ sTip.slot + 1, hH'. In all mode-1 forms the budget predicate is keyed to `stripSigs sc` — the FIRST chain, which in membership forms must be the lower-or-equal-tipped one (hLe : sTip.height ≤ sTip'.height); never sc'. A new trailing-window theorem for a new cadence/anchor rule should follow the pattern: prove `hFresh : now ≤ A.slot + H` by omega from its own timing hypotheses, then call `client_refresh_rule hn hΔ hEUF hHash hA hA' hFresh (fun u hu => hBudget u (by omega)) hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'` (no eq_core rewriting needed at all, since client_refresh_rule is already stated in Molt names); for a membership form there is no Molt-level anchored-mem wrapper with explicit H — go to MoltPetit.Model.keyrot_recent_tip_ancestor_mem_anchored after `rw [validSignedChainK'_eq_core]` exactly as sync_rule_mem does (it needs hLong' too).

GENESIS-AT-INDEX-0 GOTCHA. hHead/hHead' : blockAt? (stripSigs sc) 0 = some G are REQUIRED by keyrot_recent_tip_ancestor_agreement/_mem, keyrot_lossonly_*, sched_deep_block_agreement_of_length, sched_recent_tip_ancestor_agreement/_mem, scheduled_client_safety, lockstep_client_safety; NOT required by the anchored/horizon core forms nor by any Molt mode-1 rule (client_refresh_rule, stay_recent_client_safe, sync_rule, sync_rule_mem, max_sync_period). In the genesis-free forms G is still an implicit argument fixed only by hHash's genesis exemption.

SIGNED PREDICATE GOTCHA. Mode-1 (validSignedChainK') theorems need hHash over `KeyStealingSigned n ops registry` (verifies at SOME version j); modes 2/3 need hHash over `SignedDeclared n ops registry` (verifies at the DECLARED B.keyIndex). SignedHashInjective is antitone in Signed and `keyStealingSigned_of_declared : SignedDeclared → KeyStealingSigned`, so a KeyStealingSigned-domain hHash implies a SignedDeclared-domain one, not vice versa. The lower-level cores (keyrot_deep_block_agreement, keyrot_recent_tip_ancestor_agreement_horizon) take an abstract Signed plus hSig/hSig' coverage; coverage is discharged by keyStealingSigned_of_mem hVal (mode 1) / signedDeclared_of_mem_sched hVal (mode 2). KeyStealingEUFCMA's field is stated at core validSignedChainK' (no bridge needed for hEUF); its recency premise is `∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ` — build it as ⟨sTip, hTipS, hRecent⟩.

MISC. `badSlotsIn` is noncomputable and classical — Finset.card arguments need `classical` (census_accumulates). Structural hypotheses common to every tip-ancestor theorem: hLong : n < (stripSigs sc).length, tips via `.getLast?`, ancestor at index `(stripSigs sc).length - 1 - n`, hTipHeight (equal-height) or hLe (membership). The private helpers in ClientRule/MaxSync (countP_add_le_countP, countP_between_le, foldl_max_*) are `private` and cannot be reused from a new file. Re-export idioms: `alias name := MoltPetit.Model.name` for theorems (with a docstring), `abbrev X := @MoltPetit.Model.X` for structures/props. `#print axioms` on an alias works (Molt/Axioms.lean guards several aliases).

NEW GUARD FILE. Format per theorem (verbatim from Molt/Axioms.lean:41-44): `-- Theorem 3: the client refresh rule (paper §6.3, mode 1).` / `/-- info: 'Molt.client_refresh_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/` / `#guard_msgs in` / `#print axioms Molt.client_refresh_rule`. The file has no namespace; it imports the modules declaring the guarded names. Gotchas: (a) the axiom set varies — some theorems report `[propext, Quot.sound]` only (badKeyrot_lossOnly, badSched_lossOnly, sched_oldkey_fork_stale, producer_slot_in_window, inForce_mono, same_block_same_prefix, noBackdate_independent); run `#print axioms` first and copy the exact list. (b) Lean wraps the info message at ~100 columns; the docstring must reproduce the wrap exactly — for long names the shape (MoltPetit/Results/Axioms.lean:595-599) is `/-- info: 'MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored' depends on axioms: [propext,` newline ` Classical.choice,` newline ` Quot.sound] -/` (continuation lines start with one space). All current `Molt.`-prefixed names fit on one line; a new long name (e.g. Molt.keyrot_recent_tip_ancestor_agreement_anchored) will wrap. (c) BUILD DISCOVERY: lakefile.toml declares `[[lean_lib]] name = "Molt"` with no `roots`/`globs`, so Lake builds only `Molt.lean` and its transitive imports; Molt/Axioms.lean is enforced only because Molt.lean imports it. A NEW file that no existing module imports is NOT elaborated by `lake build`, `lake build Molt`, or `nix run .#verify-lean` (`lake build MoltPetit Rust Thales Molt`, nix/apps.nix:59). To check it without touching existing files: `lake build Molt.<NewFile>` explicitly; to have the default build enforce it, one `import Molt.<NewFile>` line must be added to Molt.lean (a one-line edit to an existing file — the planner must choose). CLAUDE.md rule: 'Add a new headline theorem → add its guard'; Molt/Axioms.lean docstring: 'Extend this file with every new headline theorem.' Repo state: branch feature/key-rotation-sound at 8b8b766, clean tree; .lake/build already contains Molt oleans (Assumptions, Axioms, …). Toolchain: Lean v4.30.0-rc2 + Mathlib per lean-toolchain; build via `lake exe cache get && lake build`.

## open_items_found

- Molt/Rotation.lean:303-307 (docstring of alias keyrot_recent_certified_suffix_agreement): "Mode 1's certificate-level safety: the agreement of `client_refresh_rule`'s family at the certificate presentation, with the floor carried as a snapshot in the claim — under the global, all-window budget (the anchored, trailing-window form is future work at this presentation)."
- memory/paper-rewrite-plan.md:55-58 (repo memory, corroborating): "only mode-2's CERTIFICATE form remains global-budget (future work: horizon at certificates; also trailing-5n cert form for mode 1, lockstep cert wrapper, the honest-chain induction as a Lean composition)."
- MoltPetit/Results/KeyStealingResults.lean:21-23: "**P2-A** the induced Byzantine budget `ByzantineBounded n (badKeyrotOn …)` — a named hypothesis here (its rent-budget + per-window-theft-rate justification is off the light-client critical path; see `PHASE2_DESIGN.md` increment I3);" (later, lines 98-103, declares "**I3 is closed**: `hBudget` need not be assumed jointly — `induced_byzantine_bounded` (`KeyStealingBudget.lean`) derives it from a rent budget `R` … plus a theft rate `T`").
- MoltPetit/Results/KeyStealingResults.lean:31-46: "(Historical note: the certificate suffix wrapper this header once recorded as future work has since landed — `keyrot_recent_certified_suffix_agreement` in `Model/KeyStealingCert.lean` — so seam (i) below is CLOSED; it is kept for the record.) Two seams were isolated as named hypotheses / future work: (i) [closed, see above] the constant-size-certificate *suffix* wrapper … and (ii) the Role-B long-range / old-key-fork exclusion from the weak-subjectivity anchor `H-ANCHOR` (increment I4), which is what makes the strong-model story honest beyond the confirmed/recent zone and is **not** derivable from uniqueness. Neither is folded in silently: … long-range old-key forks are excluded only by the named `H-ANCHOR` seam, not proved here."
- MoltPetit/Results/KeyStealingResults.lean:63-69: "**Provenance:** this surface is *assumed* (a named primitive), **not** reduced to the timed model the way the classical `SigUnforgeableRecent` is (`sigUnforgeableRecent_of_timed`) — because the strong adversary refuses `NoBackdate`/forward security, that reduction is unavailable by design. The index-pin half *is* proven (`rotated_key_dead`); only the bare recency-scoped registry EUF-CMA is assumed."
- MoltPetit/Results/KeyStealingResults.lean:86-92: "theft of *future* keys is excluded in practice by the named `H-IND` instantiation property (a theft of `dk(i,j)` yields no `dk(i,j')` for `j' > j`), which is exactly what keeps `hBudget` satisfiable. `H-IND` appears in the Lean only through this hypothesis — it is the instantiation-level justification of `hBudget`, not a formalized premise."
- MoltPetit/Results/KeyStealingResults.lean:109-115: "Recency *scopes* the crypto bundle to a `Δ`-fresh window — it does not by itself make the bundle derivable (see the `KeyStealingEUFCMA` provenance note: the honest-signing-discipline half is assumed, and the repo's own `noBackdate_independent` shows such discipline is not free)"
- MoltPetit/Results/KeyStealingResults.lean:325-327: "Remaining named seams (not folded in, see the module doc): the induced budget `hBudget` (I3), and the `H-ANCHOR`/I4 long-range exclusion above — so this is recent/confirmed-zone safety, exactly as its hypotheses state."
- MoltPetit/Results/KeyStealingScheduleResults.lean:37-50: "**The budget's retroactive reading.** `Stolen` has no time index, so `ByzantineBounded n (badSched …)` must hold in the same retroactive reading … A genesis-only stateless client is covered exactly when the deployment can assert the budget in this cumulative reading; one that cannot keeps the default model's rolling re-anchor. What the schedule removes is the **anchor hypothesis** … not the budget's reading."
- MoltPetit/Results/KeyStealingScheduleResults.lean:52-55: "for a *monotone* schedule that reads 'no window at-or-after the generation's retirement' (nothing constrains `schedule` in the statements, so the per-slot form is the precise one)"
- MoltPetit/Results/KeyStealingScheduleResults.lean:60-64: "**Recency.** `hRecent`/`hRecent'` are consumed *only* as the domain scope of `SchedUnforgeable` (verified: no other use); the recency premise itself is assumed, not derived from a timed model — the §10.4 seam, same as the default development."
- MoltPetit/Results/KeyStealingScheduleResults.lean:65-71: "**Instantiation obligations** (transfer verbatim from `KeyStealingEUFCMA`, `KeyStealingUnique.lean`): the `SchedUnforgeable` conclusion must hold for every version `j` the total registry reaches (a registry reusing key material across versions makes the surface unsatisfiable — silently vacating the theorems), and block ids must commit `keyIndex` (else `SignedHashInjective` is uninstantiable once a producer has two live versions)."
- MoltPetit/Results/KeyStealingScheduleResults.lean:229-232 (sched_oldkey_fork_stale docstring): "for a schedule that stops advancing it is unsatisfiable, correctly: no staleness argument exists then"
- Molt/MaxSync.lean:8-13 (module doc, informal reading of the F_max claim): "So a deployment able to cap `ρ + T` per window over every such stretch of `S` slots supports `F ≤ S - 4n`." and lines 22-23: "Together: `F_max = S - 4n`, and with the minimal credible cap-span of a reactive deployment (`S = 5n`), the sync rule `F = n`." — the F_max = S − 4n identity itself is stated only in prose (max_sync_period + no_budget_beyond are the formal halves; no theorem states F_max).
- Molt/ClientRule.lean:16-17 / 170-173 (derivation in prose then formal): the anchor-age bound `now ≤ A.slot + (4n - 1)` is proven inside stay_recent_client_safe by omega; no standalone lemma names it.
- Molt/Axioms.lean:12-13: "Extend this file with every new headline theorem." (the existing guard file expects to be edited; a separate new guard file is not the documented practice)
- MoltPetit/Model/KeyStealingHorizon.lean:48-54: "What does **not** transport from the scheduled variant is the budget contraction `ByzantineBoundedFrom`: mode 1's `badKeyrotOn` is chain-relative, so the slot-induction must still reconcile `inForce` across the two chains, and that induction consults windows all the way down." (i.e., mode 1 has NO ByzantineBoundedFrom-style horizon theorem; the anchored form is the mode-1 substitute)
