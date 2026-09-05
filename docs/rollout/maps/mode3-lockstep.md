# mode3-lockstep — lockstep-mode3 (MoltPetit/Model/KeyStealingLockstep.lean + LOCKSTEP_DESIGN.md, with the imported surface it consumes)

Source JSON: /etheron-pod/rollout-work/maps/mode3-lockstep.json — 14 modules, 60 defs, 40 theorems.

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingLockstep.lean

**Purpose:** Mode 3 free-cadence lockstep rotation, D1'-thin: a schedule-free validator (signatures + validChainK + no-mixing), an execution-level behavioural roster counter rosterGen packaged in LockstepPackage, the pinning theorem (matured windows declare exactly rosterGen), and a lagged-schedule transport (lagSched n rosterGen = fun s => rosterGen (s/n - 1)) that makes every accepted lockstep chain pass validSignedChainSched, so PackageA's scheduled theorem set is inherited. 614 lines, namespace MoltPetit.Model, no `open`, proofs use `classical` tactic. Budget is the CUMULATIVE exposedBound at lagSched (PackageA's shape); the per-generation census (erasure_freeze load-bearing) is explicitly NOT delivered.

**Imports:** `MoltPetit.Model.KeyStealingScheduleBudget`, `MoltPetit.Results.KeyStealingScheduleResults`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `lockstepOk` | def | 76 | The no-mixing rule: keyIndex constant within each n-slot window (slot / n) and non-decreasing along the chain; compares ALL pairs (roster-wide), unlike keyMonoOk which compares only same-producer pairs. |
| `validSignedChainLock` | def | 103 | The lockstep signed validator: versioned-registry signatures at the DECLARED keyIndex (sigOk), full indexed validity (validChain Bool + keyMonoOk), and no-mixing. No schedule parameter anywhere. |
| `lagSched` | def | 112 | One-window-lagged schedule induced by rosterGen; Nat subtraction makes window 0 lag to itself (0 - 1 = 0), pinned by genesis_gen. This is the schedule at which every scheduled theorem is instantiated for lockstep chains. |
| `LockstepPackage` | structure (Prop) | 252 | Field meanings: `mono` = rosterGen is monotone per window (B1 as behaviour; NOT consumed by any proof in this module — chain-level monotonicity from lockstepOk is used instead); `unforgeable` = registry EUF-CMA surface at the WEAKEST core validator (constant-0 schedule, pin vacuous) so its scope covers lockstep-accepted chains without circularity (audit obstruction 3); `declared` = every honest signature (entry of honestSigned) declares its window's rosterGen — the genuinely new coordination hypothesis; `hashInj` = collision resistance on the declared-signed-or-genesis domain (consumed only via toPackageA by the scheduled engine); `genesis_gen` = genesis declares its own window's rosterGen (pins window 0, needed because lagSched lags window 0 to itself); `rentBound` = ≤ R rented slots per any n-window; `exposedBound` = ≤ T exposed producers per window at the LAGGED schedule — cumulative census: theftSched n (lagSched n rosterGen) Stolen s = ∃ j, rosterGen (s/n - 1) ≤ j ∧ Stolen (s % n) j; `budget_le` = R + T ≤ ⌊(n-1)/3⌋. Assumption-wise = PackageA at lagSched + {mono, declared, genesis_gen}. |
| `lockstep_rel` | private theorem (NOT importable) | 172 | Slot-ordered pair of chain members satisfy the no-mixing relation. Private; a new module must re-prove (via lockstepOk_iff_pairwise + List.pairwise_iff_getElem + exists_blockAt_of_mem + strictSlots_lt). |
| `lockstep_const` | private theorem (NOT importable) | 195 | Same-window constancy for an unordered pair. Private. |
| `head_slot_min` | private theorem (NOT importable) | 211 | The head block has the minimum slot. Private. |
| `window_producer_inj'` | private theorem (NOT importable) | 220 | Producer↔slot injectivity within one n-window (Nat.ModEq form). Private; a same-named private copy also lives in KeyStealingScheduleBudget.lean:125 (`window_producer_inj`, Finset.mem_Ico form). Neither is importable. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `lockstepOk_iff_pairwise` | 84 | binders: {n : Nat}, binders: (c : Chain) | lockstepOk n c = true ↔ c.Pairwise (fun a b => (a.slot / n = b.slot / n → a.keyIndex = b.keyIndex) ∧ a.keyIndex ≤ b.keyIndex) | Public entry point to the no-mixing relation; the only public helper about lockstepOk. |
| `schedPinned_mono` | 120 | binders: {sched₁ sched₂ : Nat → Nat}, hle, binders: {c : Chain}, h | schedPinned sched₁ c = true | Pin is antitone in the schedule. |
| `schedCore_mono` | 130 | binders, hle, h | validSignedChainSchedCore n sched₁ ops registry sc = true | Core scheduled validity is antitone in the schedule. |
| `schedCoreUnforgeable_mono` | 141 | binders, hle, h | SchedCoreUnforgeable n sched₂ ops registry rented Stolen honestSigned now Δ | EUF-CMA surface is MONOTONE in the schedule (assumed at a smaller schedule ⇒ holds at a larger). Used with hle := fun _ => Nat.zero_le _ to lift the package's constant-0 surface to lagSched. |
| `schedCore0_of_lock` | 154 | binders, h | validSignedChainSchedCore n (fun _ => 0) ops registry sc = true | Drops keyMonoOk and lockstepOk; the constant-0 pin is vacuous. This is the validity argument to feed hP.unforgeable.unforgeable on a lockstep chain. |
| `LockstepPackage.toPackageA` | 269 | binders, hP | PackageA n (lagSched n rosterGen) ops registry rented Stolen honestSigned now Δ G R T | Fields: unforgeable := schedCoreUnforgeable_mono (fun _ => Nat.zero_le _) hP.unforgeable; hashInj, rentBound, exposedBound, budget_le copied. Drops mono/declared/genesis_gen. Built with `where` anonymous-structure syntax. |
| `lockstep_declares_rosterGen` | 299 | binders: {n : Nat}, hn, binders, hP, binders: {sc : SignedChain Sig}, hVal, hHead, hRecent | ∀ W, ∀ B ∈ stripSigs sc, B.slot / n = W → (∃ D ∈ stripSigs sc, W * n + n ≤ D.slot + 1) → B.keyIndex = rosterGen W | THE PINNING THEOREM. Matured-window witness is any chain block D with W*n + n ≤ D.slot + 1 (aligned window [W*n, W*n+n)). Proof: strong induction on W. Base W=0: head_slot_min from hHead puts G in window 0, lockstep_const gives B.keyIndex = G.keyIndex, then hP.genesis_gen (needs G.slot / n = 0). Step W ≥ 1: previous window is matured (witness B itself), density (hDense from validChainK_sound hVK).1 = MaturedWindowsDense) yields a block A there, IH pins A.keyIndex = rosterGen (W-1), chain monotonicity (lockstep_rel .2) gives hlow : rosterGen (W-1) ≤ B.keyIndex; by_contra: chainSlotsIn (stripSigs sc) (W*n) n ⊆ badSlotsIn rented (W*n) n ∪ (Finset.Ico (W*n) (W*n+n)).filter (theftSched n (lagSched n rosterGen) Stolen) — for each chain slot s, either rented, or Stolen (s%n) B.keyIndex (witness j := B.keyIndex, side-condition lagSched … s ≤ B.keyIndex from hlow), else hP.unforgeable.unforgeable (schedCore0_of_lock hVal) hsbmem hRecent hver hrent' hstol' gives honestSigned … = some sb.block and hP.declared forces B.keyIndex = rosterGen W, contradiction. Count: theft-filter card ≤ T via Set.InjOn (producerForSlot n) (window_producer_inj') + hP.exposedBound (W*n); rent ≤ R via hP.rentBound (W*n); quorum n ≤ windowCount = (chainSlotsIn …).card (chainSlotsIn_card hS) ≤ R + T ≤ maxByzantine n < quorum n (unfold maxByzantine quorum; omega). Package fields CONSUMED: genesis_gen, unforgeable, declared, exposedBound (at u = W*n, at lagSched), rentBound (at u = W*n), budget_le. NOT consumed: mono, hashInj. Needs the genesis (hHead) for the base case AND the full chain (hVal over all of sc; the EUF-CMA surface quantifies over whole-chain core validity + tip recency); cannot be applied to a suffix. Every theft slot in the window is at the SINGLE generation g = B.keyIndex, so the count would equally follow from an erasure_freeze-shaped bound at j := g (the D1'-full census) — the cumulative exposedBound is used only to match PackageA's shape. |
| `lockstep_validSignedChainSched` | 474 | binders: {n : Nat}, hn, binders, hP, binders: {sc : SignedChain Sig}, hVal, hHead, hRecent | validSignedChainSched n (lagSched n rosterGen) ops registry sc = true | THE TRANSPORT. sigsOk and validChainK are copied from hVal; schedPinned (lagSched n rosterGen) is proved blockwise: window 0 by constancy with G + genesis_gen; window W ≥ 1 by pinning the previous (always matured, witness B) window via lockstep_declares_rosterGen and chain monotonicity rosterGen (W-1) ≤ B.keyIndex. Consumes hP.genesis_gen directly and the pinning theorem (hence all its fields). The tip's own window is never pinned — only lower-bounded — which is why the lag is needed (audit obstruction 1). |
| `lockstep_recent_tip_ancestor_agreement` | 555 | binders: {n : Nat}, hn, binders, hP, binders: {sc sc' : SignedChain Sig}, hVal, hVal', hHead, hHead', binders: {sTip sTip' : Block}, hTipS, hTipS', hRecent, hRecent', hLong, hLong', hTipHeight, binders: {B B' : Block}, hB, hB' | B = B' | Headline (equal-tip form). Proof term: packageA_recent_tip_ancestor_agreement hn hP.toPackageA (lockstep_validSignedChainSched hn hP hVal hHead ⟨sTip, hTipS, hRecent⟩) (lockstep_validSignedChainSched hn hP hVal' hHead' ⟨sTip', hTipS', hRecent'⟩) hHead hHead' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'. Scheduled theorem invoked: packageA_recent_tip_ancestor_agreement (KeyStealingScheduleBudget.lean:228), at schedule lagSched n rosterGen; it in turn calls sched_recent_tip_ancestor_agreement (KeyStealingScheduleResults.lean:137) with SchedUnforgeable via schedUnforgeable_of_core and budget ByzantineBounded n (badSched n (lagSched n rosterGen) rented Stolen) via packageA_byzantine_bounded. Re-presented in Molt/Rotation.lean:406 as Molt.lockstep_client_safety. |
| `lockstep_recent_tip_ancestor_mem` | 586 | binders: {n : Nat}, hn, binders, hP, binders: {sc sc' : SignedChain Sig}, hVal, hVal', hHead, hHead', binders: {sTip sTip' : Block}, hTipS, hTipS', hRecent, hRecent', hLong, hLe, binders: {B : Block}, hB | ∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B | Membership form. Proof term: sched_recent_tip_ancestor_mem hn (schedUnforgeable_of_core hP.toPackageA.unforgeable) hP.hashInj (packageA_byzantine_bounded hP.toPackageA) (lockstep_validSignedChainSched hn hP hVal hHead ⟨sTip, hTipS, hRecent⟩) (lockstep_validSignedChainSched hn hP hVal' hHead' ⟨sTip', hTipS', hRecent'⟩) hHead hHead' hTipS hTipS' hRecent hRecent' hLong hLe hB. Scheduled theorem invoked: sched_recent_tip_ancestor_mem (KeyStealingScheduleResults.lean:179) at schedule lagSched n rosterGen, surface SchedUnforgeable n (lagSched n rosterGen) …, budget ByzantineBounded n (badSched n (lagSched n rosterGen) rented Stolen). Aliased in Molt/Rotation.lean:343. |

## /etheron-pod/mini-consensus-lean/LOCKSTEP_DESIGN.md

**Purpose:** Design note (H0) for free-cadence lockstep. Status header: D1'-thin IMPLEMENTED (Lean 8593455, paper 55b9709); D1'-full (per-generation census) REMAINS OPEN. Records the rule choice (D1 → D2 superseded → D1' recommended), the 2026-08-01 reduction audit with three obstructions (which found the factor-2 claim WRONG), the revised recommendation (D1'-thin vs D1'-full fork), and the H1–H5 phasing. 251 lines.

**Imports:** (none)

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `badLock (design-level, not in Lean)` | design-definition | 29 | The per-generation corruption predicate, chain-relative through genOf c s (the generation the chain declares at slot s). Not formalized anywhere; `genOf` is listed under H1 (line 228) but the landed module has no genOf. |
| `erasure_freeze reading (design)` | design-note | 32 | The bound on badLock need not be chain-relative: whichever generation a chain is at, its per-window stolen census is ≤ T. 'Chain-relative predicate, chain-independent bound. That is the whole trick.' Corollary (line 42): this makes erasure_freeze load-bearing; today it is documentary (consumed by no proof; implied by exposedBound for full-window schedules via erasure_freeze_of_exposedBound). |
| `D1 — window-granular no-mixing` | design-section | 54 | First candidate rule; its factor-2 wrinkle SURVIVES the audit. |
| `D2 — quorum-gated advancement (superseded)` | design-section | 84 | George's objection 2026-07-31; density already supplies the backing. |
| `D1' — window-constancy + lockstep-honest behaviour (RECOMMENDED)` | design-section | 105 | The shape that landed; its selling point (no factor 2) was corrected by the audit. |
| `Audit result (2026-08-01): PARTIAL — the factor-2 claim above is WRONG` | design-section | 135 | What the audit found wrong and why erasure_freeze is still not load-bearing after D1'-thin. |
| `Recommendation (revised twice — post-audit)` | design-section | 198 | George's call; D1'-thin is what landed. |
| `Phasing H1–H5` | design-section | 226 | The recommended H3 package = {rentBound, erasure_freeze (load-bearing), budget_le} deriving ByzantineBounded. What landed as LockstepPackage differs: it carries exposedBound at lagSched instead of erasure_freeze, and the lockstep-scoped surface of H2 was replaced by the constant-0 SchedCoreUnforgeable (obstruction 3). Line 249: PackageA/PackageB stay exactly as they are; the new package is an alternative mode-3 realization. |

### Theorems

(none)

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingScheduleBudget.lean

**Purpose:** Scheduled budget decomposition and the two operational packages PackageA / PackageB (PackageB extends PackageA with erasure_freeze). Imported by the lockstep module; source of PackageA, exposedProducersSched, theftSched, erasure_freeze. 473 lines, namespace MoltPetit.Model, `open Classical`.

**Imports:** `MoltPetit.Model.KeyStealingScheduleCert`, `MoltPetit.Model.KeyStealingBudget`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `theftSched` | def | 104 | Theft half of badSched: producer holds a stolen key of the scheduled-current-OR-LATER generation (cumulative ≥ reading). |
| `exposedProducersSched` | noncomputable def | 117 | Exposed producers of window [u, u+n) — the image under producerForSlot of the theft-corrupt slots. |
| `PackageA` | structure (Prop) | 204 | Mode-2 package (fixed scheduled rotation, no erasure). LockstepPackage.toPackageA lands here at schedule := lagSched n rosterGen. |
| `PackageB` | structure (Prop) extends PackageA | 331 | erasure_freeze (line 337) = per-generation frozen census: for every generation j at most T producers ever have their generation-j key stolen. Docstring (313-330): 'consumed by no proof'; implied by exposedBound for full-window schedules; the genuinely-B discharge needs the unmodeled B1 no-mixing rule. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `badSched_iff_or` | 108 | binders, binders: (s : Nat) | badSched n schedule rented Stolen s ↔ rented s ∨ theftSched n schedule Stolen s | Iff.rfl. |
| `theftSlotsSched_card_le_exposed` | 148 | binders | (badSlotsIn (theftSched n schedule Stolen) u n).card ≤ (exposedProducersSched n schedule Stolen u).card | Producer↔slot injection per window (uses private window_producer_inj). |
| `induced_byzantine_bounded_sched` | 164 | binders, hRent, hExposed, hRT | ByzantineBounded n (badSched n schedule rented Stolen) | The scheduled I3; uses badSlotsIn_union_le (KeyStealingBudget). Template for an H3-style 'derived ByzantineBounded' from a per-generation bound. |
| `packageA_byzantine_bounded` | 216 | implicits as PackageA, hA | ByzantineBounded n (badSched n schedule rented Stolen) |  |
| `packageA_recent_tip_ancestor_agreement` | 228 | binders: {n : Nat}, hn, binders, hA, binders: {sc sc' : SignedChain Sig}, hVal, hVal', hHead, hHead', binders: {sTip sTip' : Block}, hTipS, hTipS', hRecent, hRecent', hLong, hLong', hTipHeight, binders: {B B' : Block}, hB, hB' | B = B' | Proof: sched_recent_tip_ancestor_agreement hn (schedUnforgeable_of_core hA.unforgeable) hA.hashInj (packageA_byzantine_bounded hA) …. This is what lockstep_recent_tip_ancestor_agreement calls with hA := hP.toPackageA. |
| `schedule_div_full_window` | 344 | binders: {n R : Nat}, hR, hR0 | ∀ j : Nat, ∃ u, ∀ s, u ≤ s → s < u + n → s / R = j | Flagship schedule satisfies the full-window premise. |
| `erasure_freeze_of_exposedBound` | 364 | binders, hExposed, hFull | ∀ j : Nat, ((Finset.range n).filter (fun i => Stolen i j)).card ≤ T | erasure_freeze is implied by exposedBound for full-window schedules — the reason PackageB is 'logically PackageA'. Note: the converse is false (docstring 323-328) and lagSched n rosterGen is NOT full-window in general (rosterGen may skip generations), so this lemma does not turn a LockstepPackage into an erasure_freeze. |
| `packageB_byzantine_bounded` | 396 | hPB | ByzantineBounded n (badSched n schedule rented Stolen) | Via hPB.toPackageA. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingScheduleCert.lean

**Purpose:** Core scheduled validator (drops keyMonoOk) and the core EUF-CMA surface SchedCoreUnforgeable, which is the crypto field of both PackageA and LockstepPackage.

**Imports:** `(not read; transitively below KeyStealingScheduleBudget)`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `validSignedChainSchedCore` | def | 109 | Core validity: signatures + Bool validChain + pin, no keyMonoOk. |
| `SchedCoreUnforgeable` | structure (Prop) | 200 | Registry EUF-CMA over core acceptance: a verifying signature at version j of a non-rented slot whose version-j key is not stolen, on a recent core-valid chain, is the honest producer's logged block. The version j is universally quantified — the lockstep proof instantiates it at sb.block.keyIndex (the declared version, from sigOk). |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `schedCore_of_validSignedChainSched` | 115 | h | validSignedChainSchedCore n schedule ops registry sc = true |  |
| `schedUnforgeable_of_core` | 216 | binders, h | SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ | Core surface delivers the full-validator surface; used by lockstep_recent_tip_ancestor_mem. |
| `honestSlotsUnique_schedCore` | 231 | hUnf, binders: {sc sc' : SignedChain Sig}, hVal, hVal', hRecent, binders | (not read in full) | Core-level honest-slot uniqueness; the record-level bridge a per-generation engine would need. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingSchedule.lean

**Purpose:** Mode-2 scheduled validator, pin, SchedUnforgeable, badSched; the target of the lockstep transport.

**Imports:** `(not read)`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `schedPinned` | def | 46 | Whole-chain pin (audit obstruction 1: c.all, not matured-only). |
| `validSignedChainSched` | def | 51 | Mode-2 full validator; lockstep_validSignedChainSched proves it at lagSched. |
| `SchedUnforgeable` | structure (Prop) | 105 | Full-validator EUF-CMA surface (weaker assumption than core). |
| `badSched` | def | 124 | Chain-independent corruption predicate; the budget the scheduled engine consumes is ByzantineBounded n (badSched …). |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `validChain_of_validSignedChainSched` | 56 | h | ValidChain n (stripSigs sc) |  |
| `honestSlotsUnique_sched` | 140 | binders: (not read in full) | (not read) | Direct contraction proof; no Δconf. |
| `sched_deep_block_agreement` | 206 | binders: (not read in full) | (not read) | Agreement engine consumed by sched_recent_tip_ancestor_*. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingCert.lean

**Purpose:** Source of SignedDeclared (declared-version signature predicate) used in hashInj.

**Imports:** `(not read)`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `SignedDeclared` | def | 234 | Carries a verifying signature under its DECLARED registry version B.keyIndex — exactly sigOk's content blockwise. Strictly stronger than KeyStealingSigned. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `keyStealingSigned_of_declared` | 239 | h | KeyStealingSigned n ops registry B | Declared ⇒ registered-at-some-version. Consequently SignedHashInjective (KeyStealingSigned …) G → SignedHashInjective (SignedDeclared …) G (domain shrinks), not conversely. |
| `exists_signedChain_of_covered` | 247 | h | ∃ sc : SignedChain Sig, stripSigs sc = c ∧ sigsOk n ops registry sc = true |  |

## /etheron-pod/mini-consensus-lean/MoltPetit/Results/KeyStealingResults.lean

**Purpose:** Source of KeyStealingSigned (registered-at-some-version predicate).

**Imports:** `(not read)`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `KeyStealingSigned` | def | 158 | Verifies under SOME registry version j (existential) — the horizon theorems' hash domain (KeyStealingHorizon.lean:141,229,317 take SignedHashInjective (KeyStealingSigned …) G); scheduled/lockstep packages take SignedDeclared instead. |

### Theorems

(none)

## /etheron-pod/mini-consensus-lean/MoltPetit/Results/KeyStealingScheduleResults.lean

**Purpose:** Scheduled headline theorems that the lockstep corollaries invoke.

**Imports:** `(not read)`

### Defs

(none)

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `sched_recent_tip_ancestor_agreement` | 137 | binders: {n : Nat}, hn, binders, hUnf, hHash, hBudget, hVal, hVal', hHead, hHead', binders: {sTip sTip' : Block}, hTipS / hTipS', hRecent, hRecent', hLong, hLong', hTipHeight, binders: {B B' : Block}, hB, hB' | B = B' | Calls sched_deep_block_agreement_of_length. |
| `sched_recent_tip_ancestor_mem` | 179 | binders: {n : Nat}, hn, binders, hUnf, hHash, hBudget, hVal, hVal', hHead, hHead', binders: {sTip sTip' : Block}, hTipS / hTipS', hRecent, hRecent', hLong, hLe, binders: {B : Block}, hB | ∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B | Invoked directly by lockstep_recent_tip_ancestor_mem at schedule lagSched n rosterGen. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingScheduleHorizon.lean

**Purpose:** Horizon-scoped budget engine; horizon_shared_prefix is the lemma the design says must be generalized to an arbitrary window for D1'-full. Module doc lines 13-23: the pigeonhole runs at the trailing matured window below the lower tip (u = tip.slot + 1 − n), and disagreement propagates upward via same_block_same_prefix. NOT imported by KeyStealingLockstep.lean (imports only KeyStealingScheduleCert).

**Imports:** `MoltPetit.Model.KeyStealingScheduleCert`

### Defs

(none)

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `horizon_shared_prefix` | 161 | binders: {n : Nat}, hn, binders: {bad : ByzantineSlots} {record : SlotRecord}, hHonest, hId, binders: {c c' : Chain}, hValid, hValid', hRec, hRec', binders: {tip tip' : Block}, hTip, hTip', hle, hBudgetU, binders: {k : Nat}, hkdeep | ∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P | Record-level, validator-agnostic. The window u := tip.slot + 1 − n (line 191) straddles the un-pinned tip window — audit obstruction 2. A D1'-full variant would run the pigeonhole at an aligned matured window fully below the tip window (hence 2n depth) so that hBudgetU can be discharged from a per-generation census. No shared genesis assumed here. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/Definitions.lean

**Purpose:** Core model vocabulary the lockstep module uses (all in namespace MoltPetit.Model).

**Imports:** `(not read)`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `quorum` | def | 44 | ⌈2n/3⌉. |
| `maxByzantine` | def | 47 | ⌊(n-1)/3⌋; maxByzantine n < quorum n is discharged inline by `unfold maxByzantine quorum; omega`. |
| `producerForSlot` | def | 50 | Round-robin producer. |
| `Block` | structure | 58 | keyIndex = declared delegate-key version (the 'generation' in mode 3). |
| `Chain` | abbrev | 75 | Lowest height first. |
| `blockInWindow` | def | 78 |  |
| `windowCount` | def | 82 |  |
| `maturedWindowsDense` | def (Bool) | 95 | Bool density check; matured means u + n ≤ t + 1. |
| `SigOps` | structure | 187 |  |
| `KeyRegistry` | abbrev | 204 | registry i j = participant i's delegate key at version j. |
| `SignedBlock` | structure | 212 |  |
| `SignedChain` | abbrev | 218 |  |
| `stripSigs` | def | 221 | B ∈ stripSigs sc unpacks via List.mem_map.mp to ⟨sb, sb ∈ sc, sb.block = B⟩. |
| `sigOk` | def | 226 | Verify at the DECLARED version. |
| `sigsOk` | def | 231 |  |
| `ByzantineSlots` | abbrev | 459 |  |
| `blockAt?` | def | 462 | List indexing by height. |
| `StrictSlots` | def | 469 |  |
| `MaturedWindowsDense` | def (Prop) | 484 | Semantic density; the pinning proof applies it as hDense hkD (W * n) (by omega). |
| `ValidChain` | def (Prop) | 490 | Destructured as ⟨hSeq, hS, hPL, hDense⟩. |
| `badSlotsIn` | noncomputable def | 509 | open Classical in. |
| `ByzantineBounded` | def | 513 | Molt.FaultBounded = this by rfl. |
| `chainSlotsIn` | def | 527 |  |
| `SigningLog` | abbrev | 558 | Molt's name for honestSigned's type. |
| `SignedHashInjective` | def | 656 | Collision resistance on the genesis-or-Signed domain. |

### Theorems

(none)

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/Model.lean

**Purpose:** Basic chain lemmas the lockstep proofs use.

**Imports:** `(not read)`

### Defs

(none)

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `mem_chainSlotsIn` | 35 | binders: {c : Chain} {u len s : Nat} | s ∈ chainSlotsIn c u len ↔ ∃ B : Block, B ∈ c ∧ (u ≤ B.slot ∧ B.slot < u + len) ∧ B.slot = s |  |
| `chainSlotsIn_subset_Ico` | 40 | binders: {c : Chain} {u len : Nat} | chainSlotsIn c u len ⊆ Finset.Ico u (u + len) |  |
| `strictSlots_lt` | 47 | hS, binders: {i j : Nat} {Bi Bj : Block}, hi, hj, hij | Bi.slot < Bj.slot |  |
| `chainSlotsIn_card` | 60 | hS, binders: (u len : Nat) | (chainSlotsIn c u len).card = windowCount c u len |  |
| `exists_blockAt_of_mem` | 71 | hB | ∃ k, blockAt? c k = some B |  |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyIndex.lean

**Purpose:** In-band key index validator validChainK used inside validSignedChainLock.

**Imports:** `(not read)`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `keyMonoOk` | def | 54 | Same-producer monotone rule (lockstepOk is the roster-wide strengthening). |
| `validChainK` | def | 71 | Bool validChain (structural incl. genesis shape and density) + keyMonoOk. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `validChainK_sound` | 215 | h | ValidChain n c ∧ KeyIndexMonotone n c | Lockstep proofs use (validChainK_sound hVK).1. |

## /etheron-pod/mini-consensus-lean/Molt/Rotation.lean

**Purpose:** Paper-aligned re-presentation (paper §6.3). Fresh defs in namespace Molt mirroring the core verbatim, bridged by *_eq_core lemmas; the mode-3 headline is restated as Molt.lockstep_client_safety (paper Theorem 5). Imports MoltPetit.Model.KeyStealingLockstep directly.

**Imports:** `Molt.Results`, `MoltPetit.Results.KeyStealingResults`, `MoltPetit.Results.KeyStealingScheduleResults`, `MoltPetit.Model.KeyStealingHorizon`, `MoltPetit.Model.KeyStealingLockstep`, `MoltPetit.Model.KeyStealingCert`, `MoltPetit.Model.KeyStealingScheduleCert`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `Molt.noMixing` | def | 144 | Paper name for lockstepOk. |
| `Molt.validSignedChainLock` | def | 155 | Fresh Molt-namespace def over Molt.sigsOk/Molt.validChainK/Molt.stripSigs. |
| `Molt.LockstepPackage` | abbrev | 164 | Packages are re-exported by abbrev, not redefined. |
| `Molt.SchedUnforgeable / badSched / SignedDeclared / KeyStealingEUFCMA / KeyStealingSigned` | abbrev | 131 | Re-export idiom for Prop-structures and predicates. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `noMixing_eq_core` | 210 | (none) | noMixing = MoltPetit.Model.lockstepOk | funext + induction + simp only. |
| `validSignedChainLock_eq_core` | 217 | binders: {σ sk pk : Type} | (validSignedChainLock (σ := σ) (sk := sk) (pk := pk)) = MoltPetit.Model.validSignedChainLock | simp only [validSignedChainLock, MoltPetit.Model.validSignedChainLock, sigsOk_eq_core, validChainK_eq_core, noMixing_eq_core, stripSigs_eq_core]. |
| `lockstep_recent_tip_ancestor_mem (alias)` | 343 | as core | as core | alias lockstep_recent_tip_ancestor_mem := MoltPetit.Model.lockstep_recent_tip_ancestor_mem — alias is used when the statement mentions only re-exported names. |
| `lockstep_declares_rosterGen (alias)` | 361 | as core | as core | alias; axiom-guarded in Molt/Axioms.lean:66-69. |
| `lockstep_client_safety` | 406 | binders: {n : Nat}, hn, binders, hP, binders: {sc sc' : SignedChain Sig}, hVal, hVal', hHead, hHead', binders: {sTip sTip' : Block}, hTipS, hTipS', hRecent, hRecent', hLong, hLong', hTipHeight, binders: {B B' : Block}, hB, hB' | B = B' | Paper Theorem 5. Proof: rw [validSignedChainLock_eq_core] at hVal hVal'; exact MoltPetit.Model.lockstep_recent_tip_ancestor_agreement hn hP hVal hVal' hHead hHead' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'. Same shape as scheduled_client_safety (369) which uses FaultBounded (= ByzantineBounded by rfl, Molt/Assumptions.lean:82). |

## /etheron-pod/mini-consensus-lean/MoltPetit/Results/Axioms.lean

**Purpose:** Axiom audit. Lockstep block at lines 561-581 guards lockstep_declares_rosterGen, lockstep_validSignedChainSched, lockstep_recent_tip_ancestor_agreement, lockstep_recent_tip_ancestor_mem (all [propext, Classical.choice, Quot.sound]). Molt/Axioms.lean:66-69 and 128-130 guard the Molt aliases. Imports MoltPetit.Model.KeyStealingLockstep at line 19.

**Imports:** `MoltPetit.Model.KeyStealingLockstep`, `(and ~24 others)`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `axiom-guard idiom` | idiom | 570 | Build fails if a theorem acquires an extra axiom (sorry, native_decide). |

### Theorems

(none)

## reuse_notes

IMPORTS FOR A NEW ADDITIVE MODULE. `import MoltPetit.Model.KeyStealingLockstep` gives (transitively) KeyStealingScheduleBudget (PackageA/PackageB/erasure_freeze/exposedProducersSched/theftSched/induced_byzantine_bounded_sched), KeyStealingScheduleResults (sched_recent_tip_ancestor_agreement/_mem), KeyStealingScheduleCert (validSignedChainSchedCore, SchedCoreUnforgeable, schedUnforgeable_of_core, honestSlotsUnique_schedCore), KeyStealingSchedule (schedPinned, validSignedChainSched, SchedUnforgeable, badSched), KeyStealingCert (SignedDeclared), KeyIndex (validChainK, validChainK_sound), Definitions and Model (quorum, maxByzantine, producerForSlot, Block, blockAt?, StrictSlots, ValidChain, MaturedWindowsDense, badSlotsIn, ByzantineBounded, chainSlotsIn, mem_chainSlotsIn, chainSlotsIn_card, strictSlots_lt, exists_blockAt_of_mem). NOT transitively available and must be imported explicitly if needed: `MoltPetit.Model.KeyStealingScheduleHorizon` (horizon_shared_prefix, the lemma D1'-full must generalize; it imports only KeyStealingScheduleCert) and `MoltPetit.Results.KeyStealingResults` (KeyStealingSigned) — Molt/Rotation.lean imports both explicitly. Toolchain: leanprover/lean4:v4.30.0-rc2, Mathlib v4.30.0-rc2 (lakefile.toml). A new file under MoltPetit/Model/ that is not imported by MoltPetit.lean (the lib root) is NOT built by plain `lake build`; build it as `lake build MoltPetit.Model.<New>` (or Molt.<New> for a Molt-side file). With no edits allowed to Results/Axioms.lean or Molt/Axioms.lean, put the `/-- info: … -/ #guard_msgs in #print axioms …` guards at the bottom of the new module itself.

NAMESPACES AND STRUCTURE IDIOMS. Everything core is in `namespace MoltPetit.Model … end MoltPetit.Model`; validators use `{σ sk pk : Type}`, packages and theorems use `{Sig sk pk : Type}`; honestSigned is typed `Nat → Nat → Option Block` in the core (Molt uses the abbrev `SigningLog`). Packages are `structure X (n : Nat) … : Prop where` with named Prop fields; transports are theorems named `X.toPackageA` whose body is `PackageA … where field := …` (anonymous structure instance). Headline corollaries are term-mode wrappers that pass `hP.toPackageA` (or its projections) into an existing scheduled theorem. Lockstep proofs open no namespaces; they use the `classical` tactic where Finset filters need decidability (badSlotsIn/exposedProducersSched are noncomputable under `open Classical` in ScheduleBudget). The Molt/ re-presentation bridges by (i) restating a definition verbatim in `namespace Molt` over Molt's own re-exported/fresh names, (ii) proving `foo_eq_core : foo = MoltPetit.Model.foo` by `rfl` or `funext …; simp only [...]`, (iii) `abbrev P := @MoltPetit.Model.P` for Prop-structures (LockstepPackage, SchedUnforgeable, SignedDeclared, badSched), (iv) `alias thm := MoltPetit.Model.thm` when the statement uses only re-exported names, else a wrapper theorem that does `rw [validSignedChainLock_eq_core] at hVal hVal'` then `exact MoltPetit.Model.thm …`. Molt.FaultBounded = ByzantineBounded (faultBounded_eq_core, rfl); Molt.blockAt? = core blockAt? (rfl); Molt.noMixing = core lockstepOk (noMixing_eq_core).

HOW TO CONSUME THE LOCKSTEP RESULTS. The whole scheduled theorem set is available for a lockstep chain via two facts: `hP.toPackageA : PackageA n (lagSched n rosterGen) …` and `lockstep_validSignedChainSched hn hP hVal hHead ⟨sTip, hTipS, hRecent⟩ : validSignedChainSched n (lagSched n rosterGen) ops registry sc = true`. From the package: surface at any schedule via `schedCoreUnforgeable_mono (fun _ => Nat.zero_le _) hP.unforgeable`, full-validator surface via `schedUnforgeable_of_core`, budget via `packageA_byzantine_bounded hP.toPackageA : ByzantineBounded n (badSched n (lagSched n rosterGen) rented Stolen)`. To invoke the EUF-CMA surface directly on a lockstep chain (as the pinning proof does): validity argument `schedCore0_of_lock hVal`, membership `sb ∈ sc` obtained from `B ∈ stripSigs sc` by `List.mem_map.mp`, recency as the ∃-form `⟨t, getLast?, now ≤ t.slot + Δ⟩`, verification from `hSigs sb hsbmem` after `rw [sigOk]` (this fixes j := sb.block.keyIndex, the DECLARED version), then `¬ rented sb.block.slot` and `¬ Stolen (producerForSlot n sb.block.slot) sb.block.keyIndex`; the output feeds `hP.declared` to get `sb.block.keyIndex = rosterGen (sb.block.slot / n)`.

GOTCHAS. (1) Genesis and full chain: lockstep_declares_rosterGen, lockstep_validSignedChainSched and both corollaries all need `hHead : blockAt? (stripSigs sc) 0 = some G` (window-0 base case via genesis_gen and head_slot_min) and validity/recency of the WHOLE chain; none can be applied to a suffix. (2) Budget read-off: the pinning theorem consumes exposedBound and rentBound at u := W * n (aligned window starts) at schedule lagSched n rosterGen; theftSched there is `∃ j, rosterGen (s/n − 1) ≤ j ∧ Stolen (s % n) j` (cumulative). Every theft slot in the census window is at the single generation g = B.keyIndex, with witness j := g and side condition rosterGen (W−1) ≤ g from the previous window's pin plus chain monotonicity — so an erasure_freeze-shaped bound `((Finset.range n).filter (fun i => Stolen i g)).card ≤ T` would close the same counting (image of the theft filter under producerForSlot lands in that Finset; injectivity per window is the private window_producer_inj'). This is the template for an H3 package whose pinning theorem runs off erasure_freeze; the obstruction is only in the agreement engine's sliding window, not in pinning. (3) LockstepPackage.mono and hashInj are NOT consumed by the pinning theorem or the transport; mono is consumed by nothing in the module (chain-level monotonicity from lockstepOk is used instead); hashInj is used only by the scheduled engine through toPackageA. A new package may drop mono without loss for any lockstep theorem proved here. (4) erasure_freeze_of_exposedBound needs a full-window premise `∀ j, ∃ u, ∀ s ∈ [u,u+n), schedule s = j`; lagSched n rosterGen is not full-window in general (rosterGen may skip values), so a LockstepPackage does not yield erasure_freeze, and the converse implication is false by the PackageB docstring. (5) Signed-predicate versions: hashInj in PackageA/LockstepPackage is `SignedHashInjective (SignedDeclared n ops registry) G` (declared version B.keyIndex, exactly sigOk); the horizon theorems in KeyStealingHorizon.lean use `SignedHashInjective (KeyStealingSigned n ops registry) G` (∃ sig j, registered at SOME version). SignedDeclared → KeyStealingSigned (keyStealingSigned_of_declared), so an injectivity hypothesis at KeyStealingSigned implies one at SignedDeclared, not conversely; a new module reusing a KeyStealingSigned-domain engine cannot get it from a LockstepPackage. (6) The surface is assumed at the constant-0 schedule and is monotone in the schedule (schedCoreUnforgeable_mono); do not try to state a lockstep-scoped surface (circular, audit obstruction 3). (7) Private helpers lockstep_rel, lockstep_const, head_slot_min, window_producer_inj' (and ScheduleBudget's window_producer_inj) are `private` and cannot be imported; re-prove from the public lockstepOk_iff_pairwise + List.pairwise_iff_getElem + exists_blockAt_of_mem + strictSlots_lt (≈20 lines each). (8) lagSched at window 0 is rosterGen 0 (Nat 0 − 1 = 0); genesis_gen pins it; the matured-window witness form is `∃ D ∈ stripSigs sc, W * n + n ≤ D.slot + 1` for the ALIGNED window [W*n, W*n+n), while MaturedWindowsDense quantifies over every u. The tip's aligned window is never pinned — only rosterGen (W−1) ≤ keyIndex holds there. (9) maxByzantine n < quorum n is discharged inline by `unfold maxByzantine quorum; omega`; the design's quorum > 2·maxByzantine (needed for the relaxed bad-count < quorum engine, D1 option b) has no named lemma in the files read. (10) hLong : n < length is what makes window 0 matured (tip.slot ≥ n − 1 by strict slots), per the audit. (11) The pigeonhole in the scheduled engine runs at u := tip.slot + 1 − n (Safety.lean:97 as `D.slot + 1 − n`; KeyStealingScheduleHorizon.lean:191) — horizon_shared_prefix takes one budget window `hBudgetU : (badSlotsIn bad (tip.slot + 1 - n) n).card ≤ maxByzantine n` and record-level HonestSlotsUnique/IdInjective/ChainInRecord; D1'-full means an aligned-window variant of this lemma with a per-generation census there (confirmation depth 2n).

## open_items_found

- KeyStealingLockstep.lean:46-53 (module doc, 'Honest scope'): "The package's budget field is `exposedBound` at the lagged schedule — the **cumulative** census, exactly `PackageA`'s shape. The distinctive per-generation census (`erasure_freeze` as the load-bearing bound) is **not** delivered: the agreement engine's pigeonhole runs at the sliding trailing window, which straddles the un-pinned tip window, so the consulted census stays cumulative (`LOCKSTEP_DESIGN.md`, audit obstruction 2). Earning the per-generation reading is the D1′-full increment."
- KeyStealingLockstep.lean:59-62: "`rosterGen` itself is a genuine extra hypothesis relative to `PackageA` — an assumption about honest *coordination* (all honest signers track one generation counter), disclosed as such, and the formal content of \"lockstep coordination is necessary after that\"."
- KeyStealingLockstep.lean:249-251 (LockstepPackage docstring): "Honest accounting: assumption-wise this is `PackageA` at `lagSched` plus the behavioural `rosterGen` fields; what is *bought* is that the validator the deployment runs is schedule-free."
- Observation (not a doc quote): LockstepPackage.mono (line 256) is consumed by no proof in KeyStealingLockstep.lean — no `hP.mono` occurrence; toPackageA drops it; the pinning and transport proofs use chain-level monotonicity from lockstepOk instead. It is a documentary B1 field.
- LOCKSTEP_DESIGN.md:3-9 (status): "**Status: D1′-thin IMPLEMENTED** — Lean `8593455` … **D1′-full (the per-generation census) remains open** — see the audit section below for what it takes."
- LOCKSTEP_DESIGN.md:42-47: "Corollary worth flagging: this makes `erasure_freeze` **load-bearing**. Today it is documentary — consumed by no proof, and implied by `exposedBound` for full-window schedules (`erasure_freeze_of_exposedBound`), which is why `PackageB` is currently \"logically `PackageA`\". In the lockstep development it carries the argument. That resolves the standing honesty note in `KeyStealingScheduleBudget.lean`." — NOT resolved by what landed.
- LOCKSTEP_DESIGN.md:67-79 (D1 wrinkle, both options unbuilt): "require `ρ + 2T ≤ maxByzantine` in the package — simplest, honest, and costs a factor 2 in the tolerated theft rate; or observe `ρ + 2T ≤ 2(ρ+T) ≤ 2·maxByzantine < quorum` and prove a relaxed variant of the agreement engine that needs only `bad-count < quorum` rather than `≤ maxByzantine`. … Start with the first; the second is a clean follow-up that recovers the rate."
- LOCKSTEP_DESIGN.md:135: "### ⚠ Audit result (2026-08-01): PARTIAL — the factor-2 claim above is WRONG"
- LOCKSTEP_DESIGN.md:157-165 (obstruction 2): "The agreement engine's pigeonhole always runs at the sliding window `[tip.slot+1−n, tip.slot+1)` (`Safety.lean:97`, `KeyStealingScheduleHorizon` :191), which straddles exactly the un-pinned tip window. So the census over the consulted window is again the `≥`/cumulative one, **`erasure_freeze` stays non-load-bearing**, and D1's factor-2 wrinkle is *not* removed by the pinning lemma. Recovering the per-generation census requires generalizing `horizon_shared_prefix` to an arbitrary window — which costs confirmation depth `2n` instead of `n`."
- LOCKSTEP_DESIGN.md:166-171 (obstruction 3): "it means the lockstep package's crypto field is literally `PackageA`'s, so the lockstep validator's extra rules buy nothing on the crypto surface."
- LOCKSTEP_DESIGN.md:173-178 (Net): "the resulting package is assumption-wise `PackageA` (cumulative `exposedBound`), **not** the promised per-generation-census package. The timed layer does not transport at all."
- LOCKSTEP_DESIGN.md:214-218 (D1′-full, open): "additionally generalize `horizon_shared_prefix` to an arbitrary window so the pigeonhole can run inside a pinned region. This is what earns the per-generation census and makes `erasure_freeze` carry weight, at the cost of confirmation depth `2n` rather than `n` for this mode, plus real proof work."
- LOCKSTEP_DESIGN.md:220-224: "The one genuinely new hypothesis either way is B1-as-behaviour … it *is* an assumption about honest coordination, and it should be disclosed in the paper alongside A3/A0/B2 rather than buried."
- LOCKSTEP_DESIGN.md:228-230 (H1): lists `genOf` as an H1 deliverable; no `genOf` exists in the landed module.
- LOCKSTEP_DESIGN.md:231-234 (H2): "the recency-scoped EUF-CMA surface for the lockstep validator (same transparent shape as `SchedUnforgeable` / `KeyStealingEUFCMA`), honest-slot uniqueness" — superseded by obstruction 3 (constant-0 SchedCoreUnforgeable used instead); no lockstep-scoped surface or lockstep honest-slot-uniqueness lemma exists.
- LOCKSTEP_DESIGN.md:235-236 (H3, the recommended package): "`PackageC` (or `LockstepPackage`): `rentBound`, `erasure_freeze` now load-bearing, `budget_le`, and the derived `ByzantineBounded`." — the landed LockstepPackage has exposedBound (cumulative, at lagSched) rather than erasure_freeze; no derived ByzantineBounded from a per-generation census exists.
- LOCKSTEP_DESIGN.md:238-247 (H5 paper items): "the appendix mode-3 section promotes the census route from design-level to machine-checked" and "the abstract's 'of which the scheduled two are proved safe' needs re-auditing" — paper-side follow-ups.
- LOCKSTEP_DESIGN.md:145 (audit) says "its counting really does run off `erasure_freeze`" — but the implemented lockstep_declares_rosterGen counts off `exposedBound (W*n)` at lagSched (cumulative). The per-generation form would suffice for pinning (all census slots are at one generation g); this discrepancy is exactly the H3 gap.
- KeyStealingScheduleBudget.lean:313-323 (PackageB docstring): "`erasure_freeze` is consumed by no proof … The genuinely-B discharge of §10.2 — no-mixing forces any fork to a single generation, so a per-generation census suffices *without* the cumulative reading — is a different proof shape requiring the unmodeled B1 no-mixing rule (validator scope note)."
- KeyStealingScheduleBudget.lean:198-203 (PackageA docstring): "A3 (just-in-time provisioning: no theft of not-yet-live generations) and A0 (cold root) are the instantiation-level justifications of `exposedBound` — named here, formalized nowhere (the §10.4 temporal seam, same as the default model's `H-IND`)."
- KeyStealingScheduleHorizon.lean:35-39: re-deriving the KeyStealingScheduleResults statements from the horizon form with H := 0 is "true for any accepted chain longer than `n` by strict slots, though not recorded as a formal reduction."
- ROTATION_MODES.md:198-203 (mode-3 Honest scope): "The budget field is still mode 2's *cumulative* census; the sharper per-generation census, where erasure itself carries the count (B2 load-bearing), is 📐 design-level (**D1′-full**; D1′-thin is what is implemented — see `LOCKSTEP_DESIGN.md`)." and "Certificate-level lockstep statements are 📐 future work (a wrapper over M3-G2's transport)."
- ROTATION_MODES.md:228,230 (Not yet modeled): "X-2 | Per-generation census as the budget (D1′-full): pigeonhole moved inside the pinned region so erasure carries the count. | 3" and "X-4 | Lockstep certificate wrapper. | 3".
