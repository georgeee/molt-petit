# mode1-chain — Key index / in-band key rotation / key-stealing adversary (mode 1) core modules, plus the Molt/ paper re-presentation and the downstream Results/Horizon/Cert modules that the focus identifiers actually live in

Source: `/etheron-pod/rollout-work/maps/mode1-chain.json` (22 modules, 61 defs, 90 theorems).

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyIndex.lean

**Purpose:** Consensus-maintained per-producer delegate-key index: the in-band monotone rule keyMonoOk, the indexed validator validChainK, the per-producer floor keyFloor (foldl max over the producer's blocks), soundness of the rule (KeyIndexMonotone), no-rollback across extension, keyIndex agreement on finalized blocks, and the static-registry reduction pinAt.

**Imports:** `MoltPetit.Model.Safety`, `MoltPetit.Model.Soundness`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `keyMonoOk` | def | 54 | Validator's in-band monotone-index rule: no earlier block of a producer carries a higher keyIndex than a later block of the same producer. |
| `KeyIndexMonotone` | def | 64 | Semantic counterpart of keyMonoOk over chain positions. |
| `validChainK` | def | 71 | Indexed validator: structural validity plus monotone-index rule. |
| `keyFloor` | def | 77 | Participant i's floor: highest keyIndex it used anywhere in c (0 if none). |
| `pinAt` | def | 223 | Static index-blind directory pinning producer i at index e i. |
| `le_foldl_max / mem_le_foldl_max / foldl_max_append` | private theorem | 84 | PRIVATE, not importable; every downstream module re-proves its own copies (KeyRotation.lean 150-178, KeyStealingCert.lean 55-79, Molt/MaxSync.lean 45-72). |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `keyFloor_le_extend` | 113 | (n : Nat) (c d : Chain) (i : Nat) explicit, no Prop hypotheses | `keyFloor n c i ≤ keyFloor n (c ++ d) i` | No rollback across chain growth. |
| `block_keyIndex_le_floor` | 121 | (n : Nat) explicit; h | `B.keyIndex ≤ keyFloor n c (producerForSlot n B.slot)` | Positional form; membership form is mem_keyIndex_le_floor in KeyStealingCert.lean:82. |
| `keyMonoOk_iff_pairwise` | 136 | (c : Chain) explicit, n implicit | `keyMonoOk n c = true ↔ c.Pairwise (fun a b => producerForSlot n a.slot = producerForSlot n b.slot → a.keyIndex ≤ b.keyIndex)` |  |
| `keyMonoOk_sound` | 156 | h | `KeyIndexMonotone n c` |  |
| `deep_block_keyIndex_agreement` | 187 | hn; hBudget; hHonest; hId; hValid; hValid'; hRec; hRec'; hGenesis; hB; hB'; hD; hD'; hDeep; hDeep' | `B.keyIndex = B'.keyIndex` | congrArg Block.keyIndex of Safety.deep_block_agreement; abstract bad/record, not key-stealing specific. |
| `validChainK_sound` | 215 | h | `ValidChain n c ∧ KeyIndexMonotone n c` |  |
| `indexed_reduces_to_static` | 238 | (n : Nat) (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (e : Nat → Nat) (sb : Sign...; h | `sigOk n ops registry sb = sigOk n ops (pinAt registry e) sb` |  |
| `sigsOk_reduces_to_static` | 249 | (n ops registry e sc) explicit; h | `sigsOk n ops registry sc = sigsOk n ops (pinAt registry e) sc` |  |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyRotation.lean

**Purpose:** Phase 1 of sound key rotation: the confirmed prefix, the in-force index inForce (floor over the confirmed prefix), the ≤-pin inForcePinned, the pinned validators validChainK' / validSignedChainK', soundness/pin extraction, keyFloor/inForce agreement from membership agreement, membership finality deep_block_shared, confirmed_mem_iff, the execution-global inForce_agreement, and the validator-side kill of rotated-out keys (rotated_key_dead, rotated_index_rejected). NOTE: inForce_mono is NOT here; it is Molt.inForce_mono in Molt/MaxSync.lean:79.

**Imports:** `MoltPetit.Model.KeyIndex`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `confirmedPrefix` | def | 42 | Blocks of c at least Δconf slots before s. |
| `inForce` | def | 49 | In-force delegate index of participant i as seen from slot s: i's floor over the confirmed prefix of c. |
| `inForcePinned` | def | 79 | The ≤-pin: every block's declared keyIndex is ≥ the in-force index (read off c itself) at its slot. Docstring explains why ≤ not = (equality would freeze rotation). |
| `validChainK'` | def | 94 | Index-pinned unsigned validator (structure + monotone rule + pin). |
| `validSignedChainK'` | def | 385 | Index-pinned signed validator; sigsOk verifies each block under registry (producer, declared keyIndex). |
| `le_foldl_max / mem_le_foldl_max / foldl_max_le / foldl_max_zero_mono / mem_of_blockAt / commonPrefix_symm` | private theorem | 150 | PRIVATE helpers; KeyStealingSafety re-declares mem_of_blockAt' and commonPrefix_symm' locally because these are private. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `validChainK'_sound` | 122 | h | `ValidChain n c ∧ KeyIndexMonotone n c` | Standard idiom downstream: rw [validSignedChainK', Bool.and_eq_true] at hVal; exact (validChainK'_sound hVal.2).1 to get ValidChain n (stripSigs sc). |
| `validChainK'_pinned` | 130 | h | `∀ b ∈ c, inForce n Δconf c (producerForSlot n b.slot) b.slot ≤ b.keyIndex` |  |
| `keyFloor_eq_of_mem_iff` | 182 | h | `keyFloor n c i = keyFloor n c' i` |  |
| `inForce_agreement_of_confirmed_eq` | 201 | hAgree | `inForce n Δconf c i s = inForce n Δconf c' i s` | The reusable core; all cross-chain inForce reconciliation goes through this. |
| `deep_block_shared` | 245 | hn; hBudget; hHonest; hId; hValid; hValid'; hRec; hRec'; hGenesis; hb; hD; hD'; hDeep; hDeep' | `blockAt? c' k = some b` | Membership finality; also rules out c' being too short (via StrictSlots). |
| `confirmed_mem_iff` | 305 | hn; hΔ; hBudget; hHonest; hId; hValid; hValid'; hRec; hRec'; hGenesis; hD; hD'; hsD; hsD' | `∀ b : Block, b.slot + Δconf ≤ s → (b ∈ c ↔ b ∈ c')` |  |
| `inForce_agreement` | 349 | hn; hΔ; hBudget; hHonest; hId; hValid; hValid'; hRec; hRec'; hGenesis; hD; hD'; hsD; hsD'; (i : Nat) explicit | `inForce n Δconf c i s = inForce n Δconf c' i s` | Needs a global HonestSlotsUnique over an abstract bad — NOT usable directly inside the key-stealing uniqueness induction (circular); that is why KeyStealingSafety/HorizonCore have bounded variants. |
| `rotated_key_dead` | 401 | (n Δconf : Nat) (ops : SigOps σ sk pk) (registry : KeyRegistry pk) explicit; h; hmem | `ops.verify (registry (producerForSlot n sb.block.slot) sb.block.keyIndex) sb.block sb.sig = true ∧ inForce n Δconf (stripSigs sc) (producerForSlot n sb.block.slot) sb.block.slot ≤ sb.block.keyIndex` | inForce is read off THIS chain (stripSigs sc); chain-local by design. |
| `rotated_index_rejected` | 430 | (n Δconf ops registry) explicit; hmem; hRot | `validSignedChainK' n Δconf ops registry sc = false` |  |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealing.lean

**Purpose:** Phase 2 I1: the key-stealing corruption predicate badKeyrotOn (rented ∨ ∃ j ≥ inForce c₀ i s, Stolen i j) keyed on a fixed witness chain c₀; loss-only collapse; TimedExecution transport across pointwise-iff bad swap; the timed KeyStealingExecution structure and its refinement to plain TimedExecution.

**Imports:** `MoltPetit.Model.KeyRotation`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `badKeyrotOn` | def | 47 | Slot s is bad iff rented, or its producer holds a stolen key at a version at-or-above the in-force index read off c₀'s confirmed prefix. This is the core-name; Molt.badKeyrot is its rfl-copy. |
| `KeyStealingExecution` | structure | 101 | Timed (bare-Block) execution over the enriched corruption, plus 'a stolen-key block consumes a bad real slot'. Only consumer in repo: keyStealing_refines_timed. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `badKeyrotOn_lossOnly` | 67 | (n Δconf : Nat) (rented : ByzantineSlots) (c₀ : Chain) explicit; no Prop hypotheses | `badKeyrotOn n Δconf rented (fun _ _ => False) c₀ = rented` | funext + simp; this is what Molt.badKeyrot_lossOnly wraps. |
| `timedExecution_of_bad_iff` | 79 | hiff; h | `TimedExecution n bad' log G` |  |
| `keyStealing_refines_timed` | 117 | hNoStealLive; h | `TimedExecution n rented log G` |  |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingSafety.lean

**Purpose:** Phase 2 I2a: bounded (slot-limited) analogues of the Safety/KeyRotation core so honest-slot uniqueness is needed only up to a bound M / strictly below σ — no_deep_fork_le, deep_block_shared_le, and the opt-A confirmed_mem_iff_le (needs 2n ≤ Δconf). Plus helpers quorum_pos, windowCount_pos_block, block_in_minimal_window, strictSlots_unique.

**Imports:** `MoltPetit.Model.KeyRotation`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `mem_of_blockAt' / commonPrefix_symm' / no_deep_fork_aux_le` | private theorem | 40 | PRIVATE local copies (KeyRotation's are private too). |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `quorum_pos` | 51 | hn | `0 < quorum n` |  |
| `windowCount_pos_block` | 55 | h | `∃ B : Block, B ∈ c ∧ u ≤ B.slot ∧ B.slot < u + len` |  |
| `block_in_minimal_window` | 72 | hn; hDense; hDtip; hmat | `∃ B : Block, B ∈ c ∧ u ≤ B.slot ∧ B.slot < u + n` |  |
| `strictSlots_unique` | 86 | hS; hB; hB'; hslot | `B = B'` |  |
| `no_deep_fork_le` | 152 | hn; hBudget; hHonestLe; hValid; hValid'; hRec; hRec'; hLast; hF; hD; hD'; hMD; hMD'; hDeep; hDeep' | `False` |  |
| `deep_block_shared_le` | 187 | hn; hBudget; hHonestLe; hId; hValid; hValid'; hRec; hRec'; hGenesis; hb; hD; hD'; hMD; hMD'; hDeep; hDeep' | `blockAt? c' k = some b` |  |
| `confirmed_mem_iff_le` | 252 | hn; hΔ; hBudget; hId; hValid; hValid'; hRec; hRec'; hGenesis; hBσ; hsBσ; hBσ'; hsBσ'; hHonestLt | `∀ b : Block, b.slot + Δconf ≤ σ → (b ∈ c ↔ b ∈ c')` | Needs shared genesis and 2n ≤ Δconf; superseded (subsumed) by confirmed_mem_iff_horizon (n ≤ Δconf, no genesis, budget at one window). |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingUnique.lean

**Purpose:** Phase 2 I2b/I2c: the union slot record over two signed chains (chainUnionRecord), id-injectivity from collision resistance, the two crypto surfaces KeyStealingEUFCMA (primitive, assumed) and VersionedUnforgeable (derived via rotated_key_dead), and the strong-induction honest-slot uniqueness honestSlotsUnique_keyrot (2n ≤ Δconf, shared genesis).

**Imports:** `MoltPetit.Model.KeyStealing`, `MoltPetit.Model.KeyStealingSafety`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `chainUnionRecord` | def | 45 | Slot record built from the two stripped chains under test (the record every keyrot agreement theorem uses). |
| `KeyStealingEUFCMA` | structure | 136 | THE key-stealing signature surface (the only crypto trust surface of every headline mode-1 theorem). ONE field, `unforgeable`, with 6 premises: accepted pinned signed chain; block membership; recent tip (∃-form); explicit verification under version j; slot not rented; version j not stolen. Conclusion: the block is the honest signer's unique slot block. No inForce baked in; no forward security (Stolen not time-indexed). |
| `VersionedUnforgeable` | structure | 161 | Intermediate surface: ONE field `verified_was_signed`, 5 premises (no explicit ops.verify; instead ∀ j ≥ chain-local inForce, ¬Stolen). Derived from KeyStealingEUFCMA, never assumed independently. Consumed by honestSlotsUnique_keyrot / _horizon / _anchored. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `mem_chainUnionRecord` | 48 | none (all implicit) | `x ∈ chainUnionRecord sc sc' s ↔ (x ∈ stripSigs sc ∨ x ∈ stripSigs sc') ∧ x.slot = s` |  |
| `chainInRecord_left` | 54 | none | `ChainInRecord (chainUnionRecord sc sc') (stripSigs sc)` |  |
| `chainInRecord_right` | 60 | none | `ChainInRecord (chainUnionRecord sc sc') (stripSigs sc')` |  |
| `idInjective_keyrot` | 70 | hHash; hSig; hSig' | `IdInjective (chainUnionRecord sc sc')` |  |
| `versionedUnforgeable_of_keyStealingEUFCMA` | 184 | hEUF | `VersionedUnforgeable n Δconf ops registry rented Stolen honestSigned now Δ` | Uses rotated_key_dead: declared version verifies and is ≥ inForce, so the ∀ j ≥ inForce premise covers it. |
| `honestSlotsUnique_keyrot` | 201 | hn; hΔ; hUnf; hBudget; hId; hVal; hVal'; hRecent; hRecent'; hGenesis | `HonestSlotsUnique (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) (chainUnionRecord sc sc')` | Budget and corruption predicate keyed to sc (the FIRST chain). Proof idiom: `induction s using Nat.strongRecOn with \| ind s IH =>`, reconciling inForce of sc' to sc via inForce_agreement_of_confirmed_eq + confirmed_mem_iff_le. Superseded by honestSlotsUnique_keyrot_horizon (n ≤ Δconf, no genesis). |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingBudget.lean

**Purpose:** Increment I3: decompose the joint ByzantineBounded n (badKeyrotOn …) into a rent budget R (slots/window) plus a theft rate T (exposed producers/window): theftOn, exposedProducers, union no-double-count bound, producer↔slot injection per window, induced_byzantine_bounded. File has `open Classical`.

**Imports:** `MoltPetit.Model.KeyStealing`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `theftOn` | def | 42 | The theft disjunct of badKeyrotOn. |
| `exposedProducers` | noncomputable def | 62 | Producers holding a stolen not-yet-rotated-out key at their slot in [u, u+n). |
| `window_producer_inj` | private theorem | 69 | PRIVATE; producer is injective on an n-window. Molt/MaxSync.producer_slot_in_window is the public existence counterpart. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `badKeyrotOn_iff_or` | 45 | (s : Nat) explicit | `badKeyrotOn n Δconf rented Stolen c₀ s ↔ rented s ∨ theftOn n Δconf Stolen c₀ s` | Iff.rfl. |
| `badSlotsIn_union_le` | 52 | (A B : ByzantineSlots) (u n : Nat) explicit | `(badSlotsIn (fun s => A s ∨ B s) u n).card ≤ (badSlotsIn A u n).card + (badSlotsIn B u n).card` |  |
| `theftSlots_card_le_exposed` | 92 | (n Δconf : Nat) (Stolen) (c₀ : Chain) (u : Nat) explicit | `(badSlotsIn (theftOn n Δconf Stolen c₀) u n).card ≤ (exposedProducers n Δconf Stolen c₀ u).card` |  |
| `induced_byzantine_bounded` | 107 | hRent; hExposed; hRT | `ByzantineBounded n (badKeyrotOn n Δconf rented Stolen c₀)` | c₀ is an arbitrary witness chain; instantiate c₀ := stripSigs sc to feed the headline theorems. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingLongRange.lean

**Purpose:** Increment I4 provable core: old-key forks are long-range. Single-chain: a same-producer block Δconf past an announcement declares ≥ the announced version. Cross-chain: an accepted fork sharing the canonical prefix through the announcement's height obeys the announced version; contrapositive = fork with an older version branched strictly below the announcement. H-ANCHOR is reduced to excluding pre-anchor branches, stays a named assumption.

**Imports:** `MoltPetit.Model.KeyStealingCert`

### Defs

(none recorded)

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `oldkey_dead_after_confirmed_announcement` | 35 | hK'; hA; hb; hprod; hconf | `A.keyIndex ≤ b.keyIndex` | Uses validChainK'_pinned and mem_keyIndex_le_floor (KeyStealingCert); no budget, no crypto. |
| `recent_oldkey_fork_is_longrange` | 64 | hK'; hAat; hshared; hAk; hb; hprod; hconf | `A.keyIndex ≤ b.keyIndex` | Only c' need be validChainK'-accepted; c is any chain carrying A at height hA. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingCert.lean

**Purpose:** Certificate presentation for the pinned validator: mem_keyIndex_le_floor, keyFloor_append_one, the monotone rule implies the ≤-pin on full chains (inForcePinned_of_validChainK, validChainK'_of_validChainK), the suffix-side floor check keyMonoFrom and its lemmas, SignedDeclared, GroundedCertK/GroundedHistoryK reconstruction, AttestedHistoryK, and the certificate-level keyrot_recent_certified_suffix_agreement (global AttestedHistoryK budget).

**Imports:** `MoltPetit.Model.Grounded`, `MoltPetit.Results.KeyStealingResults`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `keyMonoFrom` | def | 159 | Suffix monotone check threading a per-producer floor snapshot. |
| `SignedDeclared` | def | 234 | Block verifies under its DECLARED version (stronger than KeyStealingSigned, which is ∃ j). |
| `GroundedCertK` | inductive | 315 | Grounded-K certificate derivation carrying claim + floor snapshot. |
| `GroundedHistoryK` | structure | 342 | What groundedCertK_history reconstructs. |
| `AttestedHistoryK` | def | 541 | A full chain the certificate could be attesting; the cert-level budget is quantified over all of these. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `mem_keyIndex_le_floor` | 82 | (n : Nat) explicit; hB | `B.keyIndex ≤ keyFloor n c (producerForSlot n B.slot)` | Membership form used by KeyStealingLongRange. |
| `keyFloor_append_one` | 91 | (n c b i) explicit | `keyFloor n (c ++ [b]) i = if producerForSlot n b.slot = i then max (keyFloor n c i) b.keyIndex else keyFloor n c i` |  |
| `inForcePinned_of_validChainK` | 122 | h | `inForcePinned n Δconf c = true` | Δconf implicit; the pin is free on full monotone chains. |
| `validChainK'_of_validChainK` | 145 | h | `validChainK' n Δconf c = true` |  |
| `keyMonoFrom_ge` | 169 | hle; h | `∀ y ∈ s, fl (producerForSlot n y.slot) ≤ y.keyIndex` |  |
| `keyMonoFrom_pairwise` | 192 | h | `s.Pairwise (fun a b => producerForSlot n a.slot = producerForSlot n b.slot → a.keyIndex ≤ b.keyIndex)` |  |
| `keyMonoOk_append_of_from` | 212 | hc; hs | `keyMonoOk n (c ++ s) = true` |  |
| `keyStealingSigned_of_declared` | 239 | h | `KeyStealingSigned n ops registry B` |  |
| `exists_signedChain_of_covered` | 247 | h | `∃ sc : SignedChain Sig, stripSigs sc = c ∧ sigsOk n ops registry sc = true` |  |
| `keyMonoFrom_congr` | 263 | hfg | `∀ s : Chain, keyMonoFrom n f s = keyMonoFrom n g s` |  |
| `keyMonoFrom_congr_lt` | 280 | hn; hfg | `∀ s : Chain, keyMonoFrom n f s = keyMonoFrom n g s` |  |
| `groundedCertK_history` | 355 | hn; h | `∃ c : Chain, GroundedHistoryK n Signed G cl fl c` |  |
| `groundedCertK_suffix_history` | 462 | (Δconf : Nat) explicit; hn; hG; hTipS; hLink; hLinks; hDense; hMono; hSigned | `∃ c : Chain, validChainK' n Δconf (c ++ s₁ :: srest) = true ∧ blockAt? (c ++ s₁ :: srest) 0 = some G ∧ c.length = cl.tipHeight + 1 ∧ (∀ B ∈ c ++ s₁ :: srest, Signed B)` |  |
| `keyrot_recent_certified_suffix_agreement` | 583 | hn; hΔ; hEUF; hHash; hcl; hcl'; hTipS; hTipS'; hLink; hLinks; hDense; hMono; hSigned; hLink' / hLinks' / hDense' / hMono' / hSigned'; hRecent; hRecent'; hBudget; hB; hB'; hHeight; hDeep; hDeep' | `B = B'` | Budget shape: GLOBAL ByzantineBounded over badKeyrotOn keyed on every attestable history c of the FIRST certificate (cl, s₁ :: srest); reconstructs full chains and calls keyrot_deep_block_agreement_of_length. Molt/Rotation.lean:308 aliases it and says the anchored/trailing-window form is future work. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Results/KeyStealingResults.lean

**Purpose:** Phase 3 core: KeyStealingSigned (the concrete hash-injectivity domain), validator-discharged coverage, and the chain-level agreement theorems under the key-stealing adversary: keyrot_deep_block_agreement(_of_length), keyrot_recent_tip_ancestor_agreement / _mem, and their loss-only specialisations. Long module docstring is the assumptions ledger.

**Imports:** `MoltPetit.Model.KeyStealingUnique`, `MoltPetit.Model.KeyStealingHorizonCore`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `KeyStealingSigned` | def | 158 | 'Carries a verifying registry signature at SOME version' — the concrete Signed domain of SignedHashInjective in the headline theorems. Molt.KeyStealingSigned is `abbrev KeyStealingSigned := @MoltPetit.Model.KeyStealingSigned`. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `keyStealingSigned_of_mem` | 169 | hVal; hB | `KeyStealingSigned n ops registry B` | Discharges hSig/hSig' from validator acceptance: fun b hb => Or.inr (keyStealingSigned_of_mem hVal hb). |
| `keyrot_deep_block_agreement` | 204 | hn; hΔ; hEUF; hHash; hBudget; hVal; hVal'; hSig; hSig'; hRecent; hRecent'; hGenesis; hB; hB'; hD; hD'; hDeep; hDeep' | `B = B'` | Budget shape: ByzantineBounded n over badKeyrotOn keyed on stripSigs sc — the FIRST chain. Record: chainUnionRecord sc sc'. Uses honestSlotsUnique_keyrot_horizon + deep_block_agreement_of_height_depth. |
| `keyrot_deep_block_agreement_of_length` | 250 | same as keyrot_deep_block_agreement through hGenesis; hB; hB'; hLen; hLen' | `B = B'` |  |
| `keyrot_recent_tip_ancestor_agreement` | 328 | hn; hΔ; hEUF; hHash; hBudget; hVal; hVal'; hHead; hHead'; hTipS; hTipS'; hRecent; hRecent'; hLong; hLong'; hTipHeight; hB; hB' | `B = B'` | Genesis is required at POSITION 0 of both stripped chains (hHead/hHead'). Budget: global ByzantineBounded over badKeyrotOn (stripSigs sc). |
| `keyrot_recent_tip_ancestor_mem` | 393 | hn, hΔ, hEUF, hHash (KeyStealingSigned domain), hBudget (over stripSigs sc), hVal, hVal...; hLong; hLe; hB | `∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B` |  |
| `keyrot_lossonly_recent_tip_ancestor_agreement` | 483 | hn; hΔ; hEUF; hHash; hBudget; hVal, hVal', hHead, hHead', hTipS, hTipS', hRecent, hRecent', hLong, hLong', hTipHeight... | `B = B'` | Proof: `by rw [badKeyrotOn_lossOnly]; exact hBudget` — the idiom for collapsing the chain-keyed budget. |
| `keyrot_lossonly_recent_tip_ancestor_mem` | 518 | as keyrot_recent_tip_ancestor_mem but hEUF at Stolen := fun _ _ => False and hBudget : ... | `∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B` |  |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingHorizonCore.lean

**Purpose:** σ-localized horizon core: the pigeonhole at the top window [σ-n, σ) so only n ≤ Δconf is needed, no shared genesis, and the budget consumed at a single window. Provides sigma_shared_prefix, confirmed_mem_iff_horizon, honestSlotsUnique_keyrot_horizon, and the anchored honestSlotsUnique_keyrot_anchored (budget only on windows ending after the anchor).

**Imports:** `MoltPetit.Model.KeyStealingSafety`, `MoltPetit.Model.KeyStealingUnique`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `exists_honest_shared_slot_at` | private theorem | 58 | PRIVATE single-window pigeonhole (Safety.exists_honest_shared_slot takes the global budget). |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `sigma_shared_prefix` | 91 | hn; hBudgetU; hId; hValid; hValid'; hRec; hRec'; hBσ; hsBσ; hBσ'; hsBσ'; hHonestLt; hb; hdeep | `blockAt? c' k = some b` |  |
| `confirmed_mem_iff_horizon` | 151 | hn; hΔ; hBudgetU; hId; hValid; hValid'; hRec; hRec'; hBσ; hsBσ; hBσ'; hsBσ'; hHonestLt | `∀ b : Block, b.slot + Δconf ≤ σ → (b ∈ c ↔ b ∈ c')` |  |
| `honestSlotsUnique_keyrot_horizon` | 183 | hn; hΔ; hUnf; hBudget; hId; hVal; hVal'; hRecent; hRecent' | `HonestSlotsUnique (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) (chainUnionRecord sc sc')` | No genesis hypothesis; the version consumed by all current headline theorems. |
| `honestSlotsUnique_keyrot_anchored` | 258 | hn; hΔ; hUnf; hA; hA'; hBudgetFrom; hId; hVal; hVal'; hRecent; hRecent' | `HonestSlotsUnique (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) (chainUnionRecord sc sc')` | Windowed budget shape: badSlotsIn card ≤ maxByzantine, only for windows u with A.slot + 1 ≤ u + n; below the anchor both chains are the same list (same_block_same_prefix). |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingHorizon.lean

**Purpose:** Genesis-free and anchored tip-ancestor agreement forms for mode 1 (n ≤ Δconf), built on horizon_shared_prefix (from KeyStealingScheduleHorizon) and the HorizonCore uniqueness results. These are what Molt.client_refresh_rule / sync_rule wrap.

**Imports:** `MoltPetit.Model.KeyStealingSafety`, `MoltPetit.Model.KeyStealingUnique`, `MoltPetit.Model.KeyStealingHorizonCore`, `MoltPetit.Results.KeyStealingResults`, `MoltPetit.Model.KeyStealingScheduleHorizon`

### Defs

(none recorded)

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `keyrot_recent_tip_ancestor_agreement_horizon` | 69 | hn; hΔ; hEUF; hHash; hSig; hSig'; hBudget; hVal; hVal'; hTipS; hTipS'; hRecent; hRecent'; hLong; hLong'; hTipHeight; hB; hB' | `B = B'` | NO hHead/hHead'; G appears only as the genesis exemption in SignedHashInjective. |
| `keyrot_recent_tip_ancestor_agreement_anchored` | 134 | hn; hΔ; hEUF; hHash; hA; hA'; hBudgetFrom; hVal; hVal'; hTipS; hTipS'; hRecent; hRecent'; hLong; hLong'; hTipHeight; hB; hB' | `B = B'` | The anchored (key-leak-horizon) form; budget is per-window card bound over badKeyrotOn keyed on stripSigs sc, only for windows ending after A.slot. Wrapped by Molt.client_refresh_rule. |
| `keyrot_recent_tip_ancestor_mem_anchored` | 222 | hn, hΔ, hEUF, hHash (KeyStealingSigned), hA, hA', hBudgetFrom, hVal, hVal', hTipS, hTip...; hLe; hB | `∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B` | Wrapped by Molt.sync_rule_mem. |
| `keyrot_recent_tip_ancestor_agreement_horizon_of_valid` | 310 | hn; hΔ; hEUF; hHash; hBudget; hVal, hVal', hTipS, hTipS', hRecent, hRecent', hLong, hLong', hTipHeight, hB, hB' as in... | `B = B'` |  |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingScheduleHorizon.lean

**Purpose:** (Only the one lemma the mode-1 horizon module imports is recorded here.) Trailing-window contraction used by KeyStealingHorizon.

**Imports:** `(not read in full)`

### Defs

(none recorded)

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `horizon_shared_prefix` | 161 | hn; hHonest; hId; hValid; hValid'; hRec; hRec'; hTip; hTip'; hle; hBudgetU; hkdeep | `∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P` | Abstract bad/record; budget at the single top window of the lower-tipped chain. |

## /etheron-pod/mini-consensus-lean/Molt/Rotation.lean

**Purpose:** Paper §6.3 re-presentation (namespace Molt): fresh paper-named copies of keyMonoOk/validChainK/keyFloor/confirmedPrefix/inForce/inForcePinned/validChainK'/validSignedChainK'/badKeyrot (mode 1), scheduled and lockstep validators (modes 2/3), abbrevs for the surfaces, rfl/pointwise *_eq_core bridges, badKeyrot_lossOnly, client_refresh_rule (Theorem 3 wrapper with explicit anchor age H), and aliases of the certificate/horizon theorems.

**Imports:** `Molt.Results`, `MoltPetit.Results.KeyStealingResults`, `MoltPetit.Results.KeyStealingScheduleResults`, `MoltPetit.Model.KeyStealingHorizon`, `MoltPetit.Model.KeyStealingLockstep`, `MoltPetit.Model.KeyStealingCert`, `MoltPetit.Model.KeyStealingScheduleCert`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `keyMonoOk` | def | 33 | Paper copy; bridge keyMonoOk_eq_core (168) by induction + producer_eq_core. |
| `validChainK` | def | 44 | Paper copy; bridge validChainK_eq_core (185). |
| `keyFloor` | def | 57 | Paper copy; keyFloor_eq_core (176) is rfl. |
| `confirmedPrefix` | def | 66 | rfl-bridged (177). |
| `inForce` | def | 72 | inForce_eq_core (179) is rfl; Molt.inForce_mono is stated over this. |
| `inForcePinned` | def | 80 | rfl-bridged (180). |
| `validChainK'` | def | 85 | Bridge validChainK'_eq_core (190) via funext+simp. |
| `validSignedChainK'` | def | 89 | Bridge validSignedChainK'_eq_core (196): `(validSignedChainK' (σ := σ) (sk := sk) (pk := pk)) = MoltPetit.Model.validSignedChainK'`; used as `rw [validSignedChainK'_eq_core] at hVal hVal'` before calling core theorems. |
| `badKeyrot` | def | 100 | Paper name for MoltPetit.Model.badKeyrotOn; badKeyrot_eq_core (182) : badKeyrot = MoltPetit.Model.badKeyrotOn := rfl. |
| `KeyStealingEUFCMA` | abbrev | 108 | Re-export (not re-declared). |
| `KeyStealingSigned` | abbrev | 112 | Re-export of the mode-1 hash-injectivity domain. |
| `schedPin / validSignedChainSched / SchedUnforgeable / badSched / SignedDeclared / noMixing / validSignedChainLock / LockstepPackage / GroundedCertK / GroundedCertSched` | def/abbrev | 119 | Not mode-1 focus; listed for namespace completeness. |
| `*_eq_core bridges` | theorem | 168 | Transport rails: every core theorem about the RHS is a theorem about the LHS. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `validChainK_structural` | 50 | h | `validChain n c = true` |  |
| `badKeyrot_lossOnly` | 230 | (n Δconf : Nat) (rented : ByzantineSlots) (c₀ : Chain) explicit | `badKeyrot n Δconf rented (fun _ _ => False) c₀ = rented` | Term-mode: MoltPetit.Model.badKeyrotOn_lossOnly n Δconf rented c₀ (types line up because badKeyrot is rfl-equal). Guarded in Molt/Axioms.lean:27 with axioms [propext, Quot.sound]. |
| `client_refresh_rule` | 267 | hn; hΔ; hEUF; hHash; hA; hA'; hFresh; hBudget; hVal; hVal'; hTipS; hTipS'; hRecent; hRecent'; hLong; hLong'; hTipHeight; hB; hB' | `B = B'` | Budget shape: per-window card bound over badKeyrot keyed on stripSigs sc (FIRST chain), only for windows with now < u + n + H. Proof: rw [validSignedChainK'_eq_core] at hVal hVal'; exact MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored … (fun u hu => hBudget u (by omega)) …. No genesis-position hypothesis. |
| `keyrot_recent_certified_suffix_agreement (alias)` | 308 | alias := MoltPetit.Model.keyrot_recent_certified_suffix_agreement | `see KeyStealingCert.lean:583` | Docstring: 'under the global, all-window budget (the anchored, trailing-window form is future work at this presentation)'. |
| `scheduled_client_safety` | 369 | mode 2, not mode-1 focus: hn, hUnf : SchedUnforgeable …, hHash : SignedHashInjective (S... | `B = B'` |  |
| `lockstep_client_safety` | 406 | mode 3, not mode-1 focus: hn, hP : LockstepPackage …, hVal/hVal' (validSignedChainLock)... | `B = B'` |  |

## /etheron-pod/mini-consensus-lean/Molt/ClientRule.lean

**Purpose:** The single-constant client rule (paper Theorem 3): deep_block_span (the n-deep anchor is < 2n slots below the tip), stay_recent_client_safe (H := 4n-1 instance of client_refresh_rule), sync_rule (Δconf := n), sync_rule_mem (membership form via keyrot_recent_tip_ancestor_mem_anchored).

**Imports:** `Molt.Rotation`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `countP_add_le_countP / countP_between_le` | private theorem | 27 | PRIVATE counting helpers over List.countP for deep_block_span. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `deep_block_span` | 123 | hn; hV; hA; hD | `D.slot < A.slot + 2 * n` | Stated over Molt.blockAt?/Molt.ValidChain (abbrev); proof starts `rw [blockAt?_eq_core] at hA hD` and uses MaturedWindowsDense twice + countP_between_le. Callers obtain hD from the tip via MoltPetit.Model.blockAt_getLast and an omega index rewrite. |
| `stay_recent_client_safe` | 174 | hn; hΔ; hEUF; hHash; hVPrev; hTipPrev; hRecPrev; hLongPrev; hAnchor; hCadence; hA; hA'; hBudget; hVal; hVal'; hTipS; hTipS'; hRecent; hRecent'; hLong; hLong'; hTipHeight; hB; hB' | `B = B'` | Budget: trailing < 5n windows, over badKeyrot keyed on stripSigs sc. |
| `sync_rule` | 238 | hn; same as stay_recent_client_safe with Δconf := n everywhere (hEUF : KeyStealingEUFCMA n ... | `B = B'` | Term-mode: stay_recent_client_safe hn (Nat.le_refl n) …. |
| `sync_rule_mem` | 284 | as sync_rule through hVal', hTipS, hTipS', hRecent, hRecent', hLong, hLong'; hLe; hB | `∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B` | Calls MoltPetit.Model.keyrot_recent_tip_ancestor_mem_anchored directly after rw [validSignedChainK'_eq_core]. |

## /etheron-pod/mini-consensus-lean/Molt/MaxSync.lean

**Purpose:** Maximum sync period (paper §6.3 mode 1): producer_slot_in_window, inForce_mono (floors never fall as s advances), the census lemmas census_accumulates / census_accumulates_later_thefts (bad-slot count of a window ≥ number of producers with an ever-stolen not-yet-retired version), no_budget_beyond (budget hypothesis unsatisfiable past faultBudget n victims), and max_sync_period (parametric F; trailing F + 4n budget).

**Imports:** `Molt.ClientRule`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `foldl_max_le' / acc_le_foldl_max / mem_le_foldl_max' / foldl_max_zero_mono'` | private theorem | 45 | PRIVATE foldl-max helpers (yet another local copy). |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `producer_slot_in_window` | 30 | hn; hi; (u : Nat) explicit | `∃ s, u ≤ s ∧ s < u + n ∧ producer n s = i` | Guarded in Molt/Axioms.lean:82. |
| `inForce_mono` | 79 | h | `inForce n Δconf c i s ≤ inForce n Δconf c i s'` | Namespace Molt, stated over Molt.inForce (rfl-equal to MoltPetit.Model.inForce, so it applies to the core definition by `inForce_eq_core ▸` or directly by defeq). Proof: unfold inForce keyFloor confirmedPrefix; foldl_max_zero_mono' on the filtered-map lists. NOT present in the MoltPetit core namespace. |
| `census_accumulates` | 95 | hP | `P.card ≤ (badSlotsIn (badKeyrot n Δconf rented Stolen c₀) u n).card` | rented and c₀ are implicit and arbitrary; uses classical choice (Finset.card_le_card_of_injOn with (hP i h).choose). |
| `census_accumulates_later_thefts` | 135 | hn; hP | `P.card ≤ (badSlotsIn (badKeyrot n Δconf rented Stolen c₀) u n).card` | Uses producer_slot_in_window + inForce_mono. |
| `no_budget_beyond` | 156 | hP; hbig | `¬ (badSlotsIn (badKeyrot n Δconf rented Stolen c₀) u n).card ≤ faultBudget n` |  |
| `max_sync_period` | 176 | hn; hΔ; hEUF; hHash; hVPrev; hTipPrev; hRecPrev; hLongPrev; hAnchor; hCadence; hA; hA'; hBudget; hVal; hVal'; hTipS; hTipS'; hRecent; hRecent'; hLong; hLong'; hTipHeight; hB; hB' | `B = B'` | Via deep_block_span + client_refresh_rule at H := F + 3n - 1. |

## /etheron-pod/mini-consensus-lean/Molt/Protocol.lean

**Purpose:** Paper §3 re-presentation: quorum, faultBudget (= maxByzantine), producer (= producerForSlot), Block/Chain re-exported as abbrevs, genesisOk/childOk/linksOk/blockInWindow/windowCount/windowDense/denseSoFar/validChain fresh copies with *_eq_core bridges.

**Imports:** `MoltPetit.Model.Definitions`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `quorum` | def | 23 | quorum_eq_core (110) rfl. |
| `faultBudget` | def | 27 | faultBudget_eq_core (111) : faultBudget = MoltPetit.Model.maxByzantine := rfl. |
| `producer` | def | 31 | producer_eq_core (112) : producer = MoltPetit.Model.producerForSlot := rfl. |
| `Block / Chain` | abbrev | 44 | Types are shared, never re-declared. |
| `validChain` | def | 94 | validChain_eq_core (129) by funext + cases. |

### Theorems

(none recorded)

## /etheron-pod/mini-consensus-lean/Molt/Verifier.lean

**Purpose:** Paper §4: SigOps/KeyRegistry/SignedBlock/SignedChain/CertClaim/CertOps/CertifiedChain re-exported as abbrevs; stripSigs, sigOk, sigsOk, validSignedChain, validSuffix, validCertifiedChain, produceBlock?, selectChain fresh copies with bridges.

**Imports:** `Molt.Protocol`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `stripSigs` | def | 177 | stripSigs_eq_core (289) rfl. |
| `sigOk / sigsOk` | def | 182 | sigOk_eq_core (291), sigsOk_eq_core (293) rfl. |
| `SigOps / KeyRegistry / SignedBlock / SignedChain / CertClaim / CertOps / CertifiedChain` | abbrev | 163 | Shared types. |

### Theorems

(none recorded)

## /etheron-pod/mini-consensus-lean/Molt/Assumptions.lean

**Purpose:** Paper §5: SlotRecord/ByzantineSlots/ValidChain/SigningLog abbrevs; badSlotsIn, FaultBounded (= ByzantineBounded), SignedHashInjective, HonestBlocksCover, HonestSlotsUnique, IdInjective fresh copies with rfl bridges; SigUnforgeableRecent/GroundedCert re-exported.

**Imports:** `Molt.Verifier`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `badSlotsIn` | noncomputable def | 33 | badSlotsIn_eq_core (81) rfl. |
| `FaultBounded` | def | 38 | faultBounded_eq_core (82) : FaultBounded = MoltPetit.Model.ByzantineBounded := rfl. |
| `SignedHashInjective` | def | 50 | signedHashInjective_eq_core (84) rfl. |
| `HonestSlotsUnique / IdInjective / SigningLog / ValidChain / ByzantineSlots / SlotRecord` | def/abbrev | 70 | rfl-bridged (88, 90) or abbrevs. |

### Theorems

(none recorded)

## /etheron-pod/mini-consensus-lean/Molt/Results.lean

**Purpose:** Paper §6.1–6.2: TimedLog/TimedExecution abbrevs, AvailableAt, blockAt? (Molt copy, blockAt?_eq_core rfl at 134), light_client_safety, forged_time_bound, aliases.

**Imports:** `Molt.Assumptions`, `MoltPetit.Results.Results`, `MoltPetit.Model.TimedSig`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `blockAt?` | def | 131 | blockAt?_eq_core (134) : blockAt? = MoltPetit.Model.blockAt? := rfl. Molt theorems state hB over Molt.blockAt? and pass them to core theorems by defeq. |

### Theorems

(none recorded)

## /etheron-pod/mini-consensus-lean/Molt/Axioms.lean

**Purpose:** Axiom-guard file for Molt: one `/-- info: 'Molt.<thm>' depends on axioms: [...] -/ #guard_msgs in #print axioms Molt.<thm>` per headline theorem. Existing guards include badKeyrot_lossOnly (27, [propext, Quot.sound]), client_refresh_rule (42), deep_block_span (47), stay_recent_client_safe (52), sync_rule (57), sync_rule_mem (62), max_sync_period (77), producer_slot_in_window (82, [propext, Quot.sound]), inForce_mono (87, [propext, Quot.sound]), census_accumulates (92), census_accumulates_later_thefts (97), no_budget_beyond (102), keyrot_recent_certified_suffix_agreement (107). Docstring: 'Extend this file with every new headline theorem.'

**Imports:** `Molt.Results`, `Molt.Rotation`, `Molt.ClientRule`, `Molt.MaxSync`, `Molt.Liveness`

### Defs

(none recorded)

### Theorems

(none recorded)

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/Definitions.lean

**Purpose:** (Core definitions consumed by the focus modules; only the relevant declarations recorded.)

**Imports:** `(not read in full)`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `Block` | structure | 58 | Six fields; keyIndex is the in-band delegate-key version. |
| `quorum / maxByzantine / producerForSlot` | def | 44 | Core constants. |
| `KeyRegistry / SignedBlock / SignedChain / stripSigs / sigOk / sigsOk` | abbrev/structure/def | 204 | Signed layer; sigOk verifies at the DECLARED keyIndex. |
| `SlotRecord / ByzantineSlots / blockAt? / SequentialHeights / StrictSlots / ParentLinked / MaturedWindowsDense / ValidChain / ChainInRecord / HonestSlotsUnique / IdInjective / badSlotsIn / ByzantineBounded / CommonPrefixUpTo / LastCommonHeight / chainSlotsIn / SigningLog` | def/abbrev | 456 | Proof-side predicates. ValidChain components are accessed positionally: hV.1 SequentialHeights, hV.2.1 StrictSlots, hV.2.2.1 ParentLinked, hV.2.2.2 MaturedWindowsDense. |
| `SignedHashInjective / SigUnforgeableRecent / TimedLog / TimedExecution` | def/structure | 656 | Crypto surfaces and the timed model; TimedExecution mentions bad only negatively (honest_stamp, honest_once), which is what timedExecution_of_bad_iff exploits. |

### Theorems

(none recorded)

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/Safety.lean

**Purpose:** (Core agreement engine consumed by the focus modules; only relevant theorems recorded.)

**Imports:** `(not read in full)`

### Defs

(none recorded)

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `exists_honest_shared_slot` | 45 | hn; hBudget; hS; hS'; hCard; hCard' | `∃ s, s ∈ S ∧ s ∈ S' ∧ ¬ bad s` |  |
| `no_deep_fork` | 134 | hn; hBudget; hHonest; hValid, hValid', hRec, hRec'; hLast; hF; hD, hD'; hDeep; hDeep' | `False` |  |
| `same_block_same_prefix` | 189 | hId; hRec; hRec'; hP; hP'; blockAt? c m = some B; blockAt? c' m = some B; k ≤ m | `∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P` | Aliased as Molt.same_block_same_prefix (Rotation.lean:348). |
| `deep_block_agreement` | 292 | hn; hBudget; hHonest; hId; hValid; hValid'; hRec; hRec'; hGenesis; hB; hB'; hD; hD'; hDeep; hDeep' | `B = B'` |  |
| `deep_block_agreement_of_height_depth` | 352 | same as deep_block_agreement through hB'; hD; hD'; hDeep; hDeep' | `B = B'` | This is what keyrot_deep_block_agreement instantiates with bad := badKeyrotOn … (stripSigs sc), record := chainUnionRecord sc sc'. |

## reuse_notes (verbatim)

WHERE THE FOCUS NAMES ACTUALLY LIVE (several are not in the seven listed files):
- inForce, inForcePinned, validChainK', validSignedChainK', validChainK'_sound/_pinned, rotated_key_dead, inForce_agreement: MoltPetit/Model/KeyRotation.lean (namespace MoltPetit.Model).
- inForce_mono: ONLY Molt/MaxSync.lean:79 as `Molt.inForce_mono`, stated over `Molt.inForce` (= MoltPetit.Model.inForce by rfl, `inForce_eq_core`). A new core (MoltPetit.Model) module cannot import Molt/ without inverting the layering (Molt imports MoltPetit); it must either re-prove the 8-line lemma locally or live in Molt/.
- badKeyrot (no `On`): Molt/Rotation.lean:100, `badKeyrot_eq_core : badKeyrot = MoltPetit.Model.badKeyrotOn := rfl`. The core name is badKeyrotOn (KeyStealing.lean:47). badKeyrot_lossOnly is Molt/Rotation.lean:230 (wrapping badKeyrotOn_lossOnly, KeyStealing.lean:67).
- KeyStealingSigned: DEFINED in MoltPetit/Results/KeyStealingResults.lean:158 (∃ sig j, verify under version j); Molt/Rotation.lean:112 is `abbrev KeyStealingSigned := @MoltPetit.Model.KeyStealingSigned`. Discharged from the validator by keyStealingSigned_of_mem (Results:169).
- census_accumulates / census_accumulates_later_thefts / no_budget_beyond / max_sync_period: Molt/MaxSync.lean (namespace Molt, over badKeyrot/producer/faultBudget).
- deep_block_span: Molt/ClientRule.lean:123 (namespace Molt; hyps ValidChain n c, blockAt? c m = some A, blockAt? c (m+n) = some D ⊢ D.slot < A.slot + 2n).
- mem_keyIndex_le_floor (used by LongRange): MoltPetit/Model/KeyStealingCert.lean:82.

THE KEY-STEALING SIGNATURE SURFACE: `structure KeyStealingEUFCMA (n Δconf : Nat) {Sig sk pk : Type} (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block) (now Δ : Nat) : Prop` (KeyStealingUnique.lean:136) has exactly ONE field `unforgeable` with premises, in order: (1) validSignedChainK' n Δconf ops registry sc = true, (2) sb ∈ sc, (3) ∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ, (4) ops.verify (registry (producerForSlot n sb.block.slot) j) sb.block sb.sig = true, (5) ¬ rented sb.block.slot, (6) ¬ Stolen (producerForSlot n sb.block.slot) j; conclusion honestSigned (producerForSlot n sb.block.slot) sb.block.slot = some sb.block. The version j is EXPLICIT and free (no inForce). Derived surface VersionedUnforgeable (line 161) has ONE field `verified_was_signed` replacing (4)+(6) by `∀ j, inForce n Δconf (stripSigs sc) (producer) sb.block.slot ≤ j → ¬ Stolen (producer) j` (chain-local inForce of the chain sb sits in). Always obtain it via `versionedUnforgeable_of_keyStealingEUFCMA hEUF`; never assume VersionedUnforgeable in a headline statement. In Molt/ the parameter is written `{honestSigned : SigningLog}` (abbrev for Nat → Nat → Option Block).

BUDGET HYPOTHESIS SHAPES (exact):
- Core global form: `hBudget : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc))` — ByzantineBounded over badKeyrotOn READ OFF THE FIRST SIGNED CHAIN `sc` (the one whose block B/anchor the conclusion is about). Used by honestSlotsUnique_keyrot(_horizon), keyrot_deep_block_agreement(_of_length), keyrot_recent_tip_ancestor_agreement/_mem, keyrot_recent_tip_ancestor_agreement_horizon(_of_valid). The sc'-side inForce is reconciled INSIDE the proof (inForce_agreement_of_confirmed_eq + confirmed_mem_iff_horizon at the coexistence slot). Record is always `chainUnionRecord sc sc'`.
- Anchored/windowed form (KeyStealingHorizonCore/Horizon): `hBudgetFrom : ∀ u, A.slot + 1 ≤ u + n → (badSlotsIn (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) u n).card ≤ maxByzantine n`.
- Molt client forms: `hBudget : ∀ u, now < u + n + H → (badSlotsIn (badKeyrot n Δconf rented Stolen (stripSigs sc)) u n).card ≤ faultBudget n` (client_refresh_rule); `now < u + 5 * n` (stay_recent_client_safe / sync_rule / sync_rule_mem, with Δconf := n in sync_rule*); `now < u + F + 4 * n` (max_sync_period). Note faultBudget = maxByzantine by rfl and Molt.badSlotsIn = core badSlotsIn by rfl, so these feed the core theorems with `fun u hu => hBudget u (by omega)`.
- Certificate form (KeyStealingCert): `hBudget : ∀ c : Chain, AttestedHistoryK n Δconf ops registry G cl.tipHeight (s₁ :: srest) c → ByzantineBounded n (badKeyrotOn n Δconf rented Stolen c)` — global, over every attestable history of the FIRST certificate.
- Loss-only: `ByzantineBounded n rented`, obtained by `by rw [badKeyrotOn_lossOnly]; exact hBudget`.
- Decomposed: induced_byzantine_bounded gives the global form from hRent (∀ u, (badSlotsIn rented u n).card ≤ R), hExposed (∀ u, (exposedProducers n Δconf Stolen c₀ u).card ≤ T), hRT : R + T ≤ maxByzantine n; instantiate c₀ := stripSigs sc.
- Abstract engine: deep_block_shared / confirmed_mem_iff / inForce_agreement take an abstract `bad` with a GLOBAL HonestSlotsUnique bad record — circular for key-stealing; use the bounded (`_le`, M-bounded) or σ-localized (`_horizon`, single-window `(badSlotsIn bad (σ - n) n).card ≤ maxByzantine n`) variants inside any strong-induction.

GENESIS / POSITION GOTCHAS: keyrot_recent_tip_ancestor_agreement/_mem and the lossonly forms require `hHead : blockAt? (stripSigs sc) 0 = some G` and `hHead'` (genesis at index 0 of both stripped chains) and turn them into CommonPrefixUpTo … 0. The `_horizon`, `_anchored` forms and all Molt client theorems need NO genesis hypothesis; G there only parameterizes SignedHashInjective's exemption. keyrot_deep_block_agreement(_of_length) take `hGenesis : CommonPrefixUpTo (stripSigs sc) (stripSigs sc') 0` directly. Depth in the tip-ancestor forms is `blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - n) = some B` plus `hLong : n < (stripSigs sc).length`; tip via `(stripSigs sc).getLast? = some sTip`, converted with `MoltPetit.Model.blockAt_getLast` (Soundness.lean:97) to `blockAt? c (c.length - 1) = some tip`; height = index via `hVc.1 (blockAt_getLast hTipS)`.

SIGNED PREDICATE: DECLARED vs REGISTERED VERSION. sigOk verifies at the block's DECLARED keyIndex (`registry (producerForSlot n slot) keyIndex`). KeyStealingSigned (Results:158) is ∃ sig j (any version); SignedDeclared (Cert:234) is ∃ sig at the declared keyIndex (stronger; keyStealingSigned_of_declared). Full-chain headline theorems use hHash over KeyStealingSigned; the certificate theorem uses hHash over SignedDeclared (strictly weaker hash assumption). rotated_key_dead gives verification at the declared version AND declared ≥ inForce (chain-local, read off stripSigs sc). KeyStealingEUFCMA's j is the verifying version, not the declared one; the pin links them.

IDIOMS A NEW ADDITIVE MODULE MUST FOLLOW:
- Core files: `namespace MoltPetit.Model … end MoltPetit.Model`; import the highest-needed module (e.g. `import MoltPetit.Model.KeyStealingHorizon` or `MoltPetit.Results.KeyStealingResults`); register the file in MoltPetit.lean's import list (the lean_lib picks up modules only via the root import chain — MoltPetit.lean lists every Model/Results module explicitly, KeyStealingLongRange at line 22) and add a `#guard_msgs in #print axioms` entry to MoltPetit/Results/Axioms.lean (all keyrot theorems are guarded there, lines 115-353 and 546-603). Expected axioms: `[propext, Classical.choice, Quot.sound]` (or `[propext, Quot.sound]` for choice-free lemmas); no sorry/axiom/native_decide.
- Molt/ files: `namespace Molt`; import `Molt.Rotation` (or Molt.ClientRule/Molt.MaxSync); define fresh paper-named copies ONLY if the paper must quote them, with `theorem foo_eq_core : foo = MoltPetit.Model.foo := rfl` (or funext+simp/induction when not rfl); re-export types/surfaces with `abbrev X := @MoltPetit.Model.X`; wrap core theorems by `rw [validSignedChainK'_eq_core] at hVal hVal'` (and `rw [blockAt?_eq_core] at …` where needed) then `exact MoltPetit.Model.<thm> …`; use `alias name := MoltPetit.Model.name` when nothing needs renaming. Register the new module in Molt.lean's import list AND import it in Molt/Axioms.lean, adding a guard per headline theorem. Molt vocabulary: producer (not producerForSlot), faultBudget (not maxByzantine), FaultBounded (not ByzantineBounded), badKeyrot (not badKeyrotOn), SigningLog for honestSigned. Bare `lake build` builds all four libs incl. guards.
- Private helpers: the foldl-max lemmas (le_foldl_max, mem_le_foldl_max, foldl_max_le, foldl_max_zero_mono), mem_of_blockAt, commonPrefix_symm are PRIVATE in every file that has them; a new module must re-prove its own (each existing module does).
- Proof idioms: ValidChain n (stripSigs sc) from hVal via `rw [validSignedChainK', Bool.and_eq_true] at hVal; exact (validChainK'_sound hVal.2).1`; membership of a signed block's block in stripSigs via `List.mem_map`; strong induction `induction s using Nat.strongRecOn with | ind s IH =>`; ¬badKeyrotOn unpacked with `simp only [badKeyrotOn, not_or] at hbad` then `push_neg`/`push Not`; window census via `badSlotsIn_union_le`, `theftSlots_card_le_exposed`, `Finset.card_le_card_of_injOn`.
- KeyStealingHorizon.lean depends on `horizon_shared_prefix` from KeyStealingScheduleHorizon (mode-2 module); importing KeyStealingHorizon pulls the whole schedule development in.
- Toolchain: Lean v4.30.0-rc2 + Mathlib (lakefile.toml); `relaxedAutoImplicit = false`, so all variables must be bound.

## open_items_found (verbatim)

1. MoltPetit/Results/KeyStealingResults.lean:34-42 (module docstring): "Two seams were isolated as named hypotheses / future work: (i) [closed, see above] the constant-size-certificate *suffix* wrapper … and (ii) the Role-B long-range / old-key-fork exclusion from the weak-subjectivity anchor `H-ANCHOR` (increment I4), which is what makes the strong-model story honest beyond the confirmed/recent zone and is **not** derivable from uniqueness." Seam (ii) remains a named assumption; KeyStealingLongRange only pins down its scope.

2. MoltPetit/Results/KeyStealingResults.lean:86-92: "theft of *future* keys is excluded in practice by the named `H-IND` instantiation property (a theft of `dk(i,j)` yields no `dk(i,j')` for `j' > j`), which is exactly what keeps `hBudget` satisfiable. `H-IND` appears in the Lean only through this hypothesis — it is the instantiation-level justification of `hBudget`, not a formalized premise." (KEY_ROTATION_SOUND.md:129-140 gives the all-higher-versions form; there is no Lean `ForwardIndependent Stolen` predicate.)

3. MoltPetit/Model/KeyStealingLongRange.lean:6-8,13-15: "`H-ANCHOR` — the light client trusts only recent-tipped chains anchored after the rotations it relies on — is a *named assumption* (weak subjectivity) and stays one: nothing can refute a fork built entirely in the past." … "What remains for `H-ANCHOR` is exactly (and only) ruling out forks that branch before the anchor — the irreducible weak-subjectivity residue."

4. Molt/Rotation.lean:303-307 (docstring of the alias keyrot_recent_certified_suffix_agreement): "Mode 1's certificate-level safety … under the global, all-window budget (the anchored, trailing-window form is future work at this presentation)." — i.e. no certificate-level analogue of keyrot_recent_tip_ancestor_agreement_anchored / client_refresh_rule exists.

5. MoltPetit/Model/KeyStealingUnique.lean:123-135 (KeyStealingEUFCMA docstring): "**Provenance — the exact boundary of trust.** This surface is **assumed**, not reduced to the timed model. … The key-stealing adversary deliberately **refuses** `NoBackdate`/forward security … so that derivation is unavailable by design; `KeyStealingEUFCMA` is therefore taken as a named primitive."

6. MoltPetit/Model/KeyStealingUnique.lean:104-110: "Two further instantiation obligations: the conclusion must hold for **every** version `j` the total registry `KeyRegistry pk = Nat → Nat → pk` reaches (an instantiation whose registry defaults unregistered versions to a degenerate key cannot satisfy this surface …); and blocks differing only in `keyIndex` must hash differently (the block id must commit `keyIndex` …), or `SignedHashInjective` is uninstantiable once a producer has two versions." — not formalized.

7. MoltPetit/Model/KeyStealing.lean:96-100 (KeyStealingExecution docstring): "`StolenMint : Block → Prop` is the unsigned image of 'verifies under a stolen registry version'; the actual `ops`/`registry`/`sig` content lives on the `SignedChain` side … and is connected to this predicate by a separate bridge hypothesis in Phase 3". No such bridge exists in the repo: KeyStealingExecution/StolenMint/steal_bad are consumed only by keyStealing_refines_timed (grep confirmed); the timed layer is not connected to the signed headline theorems.

8. MoltPetit/Model/KeyRotation.lean:114-121 (validChainK'_sound docstring): "Whether the honest producer can still sign at such a version is an instantiation property (fine for unbounded hash-derived key trees, fatal for a bounded committed tree) — **safety-irrelevant** …, a quantified liveness condition rather than an open question." — index-inflation liveness left as an instantiation condition.

9. MoltPetit/Model/KeyRotation.lean:396-400 (rotated_key_dead docstring): "That globalization (and discharging its recent-tip hypothesis) is the Phase-2 uniqueness derivation — `rotated_key_dead` itself is deliberately chain-local." (globalization landed via honestSlotsUnique_keyrot*, but rotated_key_dead's inForce stays read off stripSigs sc).

10. MoltPetit/Model/KeyStealingBudget.lean:30-33: "Under `H-IND` (thefts do not cascade to higher versions) and prompt emergency rotation, a single theft exposes one producer for the announcement-delay + `Δconf` window, so `T` is the number of *concurrently healing* producers — the natural deployment dial." — informal; the exposure-duration bound on T is not a Lean theorem.

11. MoltPetit/Model/KeyStealingCert.lean:41-46 and 533-540: "The corruption budget cannot be stated over verifier-visible data (it quantifies over the whole execution), so it is assumed over **every history the certificate could be attesting** (`AttestedHistoryK`)" — the certificate-level budget is quantified over all attestable histories, an admitted over-approximation.

12. MoltPetit/Model/KeyStealingCert.lean:568-582: "**Wire contract (MANDATORY for any instantiation — read before deploying).** … the certificate must **carry and authenticate the pair `(cl, fl)` together** — a TS-level certificate-unforgeability hypothesis must read `∀ hc, verify hc = true → ∃ cl fl, claim hc = cl ∧ floors hc = fl ∧ GroundedCertK n Signed G cl fl` (note the plain path's `hUnf` attests only `cl`; a naive port would leave `fl` unauthenticated)." — an unformalized TS/Rust-level obligation.

13. Molt/MaxSync.lean:8-13,22-23 (module docstring): "later-starting windows are load-bearing only against chains dated beyond the clock" and "Together: `F_max = S - 4n`, and with the minimal credible cap-span of a reactive deployment (`S = 5n`), the sync rule `F = n`." — the F_max/S reading is informal; max_sync_period is parametric in F and no theorem states F_max = S - 4n.

14. MoltPetit/Model/KeyStealingHorizonCore.lean:39-45 / KeyStealingHorizon.lean:47-54: "What does **not** transport from the scheduled variant is the budget contraction `ByzantineBoundedFrom`: mode 1's `badKeyrotOn` is chain-relative, so the slot-induction must still reconcile `inForce` across the two chains, and that induction consults windows all the way down." — mode 1 has no from-horizon budget contraction; only the anchor-scoped hBudgetFrom (windows ending after A.slot).

15. MoltPetit/Results/KeyStealingResults.lean:123-133 (assumptions ledger): "A deployment unwilling to assume retired keys stay secret forever keeps a rolling anchor instead … only an offline/fresh client needs a checkpoint younger than the deployment's key-leak horizon." — the retroactive reading of hBudget (Stolen has no time index) is documented as an operational assumption, not a theorem.

16. MoltPetit/Model/KeyStealingUnique.lean:66-69 (idInjective_keyrot docstring): "`Signed`/`G` and the genesis-or-signed facts are threaded from the certificate plumbing in Phase 3." and KeyRotation.lean:87-93: "The signature conjunct `sigsOk` … is woven in at Phase 2/3." — historical phase notes; both landed (KeyStealingResults, KeyStealingCert), recorded here only because the wording says 'Phase 3'.
