# timed-core-liveness

Timed model, timed-signature bridge, liveness, and core definitions (MoltPetit/Model/{Timed,TimedSig,Liveness,Definitions}.lean) plus the out-of-file declarations the brief names (Results.lean forged bounds, Molt/ re-presentation, KeyIndex/KeyRotationLiveness, Model/Soundness helper lemmas)


## /etheron-pod/mini-consensus-lean/MoltPetit/Model/Timed.lean

**Purpose:** Timed signing model proofs: signing-time monotonicity along parent-linked chains (from TimedExecution.chain_order + id_inj), the 'one real slot, one chain block' lemma, and the counting lemmas (belowCount / windows / Byzantine budget over Ico) that Results.lean assembles into forged_suffix_time_bound / forged_chain_time_bound. Namespace MoltPetit.Model. Contains ONE definition (belowCount); the model structures (TimedLog, TimedExecution, AvailableAt, SignedEver) live in Definitions.lean.

**Imports:**
- MoltPetit.Model.Grounded (transitively: MoltPetit.TS.Bridge, MoltPetit.Model.Liveness, Soundness, Safety, Model, KeyIndex, Definitions, Mathlib, MoltPetit.TS.Emitted)

### Defs (1)

| name | kind | line | meaning |
|---|---|---|---|
| belowCount | def | 254 | Number of chain blocks whose stamp is strictly below k. |

### Theorems (12)

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| block_signed | 47 | hGprev, hPL, hAvail, hk, hB | B ≠ G ∧ ∃ r, r ≤ R ∧ B ∈ log r | Needs NO TimedExecution. Index k ≥ 1 is essential: index 0 has prev = none by ParentLinked; blocks at index ≥ 1 have prev = some _, hence ≠ G. Does not require c[0] = G. |
| sigTime_mono_step | 67 | hexec, hPne, hprev, hPsig, hBsig | Nat.find hPsig ≤ Nat.find hBsig | Uses hexec.chain_order and hexec.id_inj only. First-signing time is Nat.find over ∃ r, B ∈ log r (needs DecidablePred — classical instance available since Finset membership on Block with DecidableEq). |
| sigTime_mono_chain | 87 | hexec, hGprev, hPL, hAvail, ∀ (d : Nat) {k : Nat}, 1 ≤ k →, ∀ {B B' : Block}, blockAt? c k = some B → blockAt? c (k +…, hBsig, hB'sig | Nat.find hBsig ≤ Nat.find hB'sig | Induction on the index gap d; uses block_signed + sigTime_mono_step. Only needs ParentLinked (not full ValidChain). |
| one_real_slot_one_block | 136 | hn, hexec, hGprev, hValid, hAvail, hk, hkk, hB, hB', hBr, hBmin, hB'r, hB'min | False | Two distinct chain blocks (indices ≥ 1) cannot both be FIRST-signed at the same real slot r. Uses hexec.key_match, MaturedWindowsDense at B' for window [B.slot+1, B.slot+1+n), 2 ≤ quorum n (from hn), StrictSlots, sigTime_mono_chain. The 'first-signed' minimality hypotheses are stated as ∀ r' < r, B ∉ log r' (not via Nat.find). |
| belowCount_le | 257 | (c : Chain) (k : Nat) | belowCount c k ≤ c.length |  |
| belowCount_cons | 260 | (b : Block) (rest : Chain) (k : Nat) | belowCount (b :: rest) k = (if b.slot < k then 1 else 0) + belowCount rest k |  |
| belowCount_split | 268 | (c : Chain) (u len : Nat) | belowCount c (u + len) = belowCount c u + windowCount c u len | Uses windowCount_cons from MoltPetit/TS/Bridge.lean:134. |
| belowCount_zero | 295 | (c : Chain) | belowCount c 0 = 0 |  |
| belowCount_windows | 303 | (c : Chain) (lo n q : Nat), ∀ m, (∀ j < m, q ≤ windowCount c (lo + j * n) n) | belowCount c lo + q * m ≤ belowCount c (lo + m * n) | Density of m consecutive n-windows starting at lo forces q·m blocks in [lo, lo + m·n). Windows must be aligned at lo + j*n. |
| belowCount_prefix | 320 | {c : Chain} (StrictSlots c), {k₀ : Nat} {F : Block} (blockAt? c k₀ = some F) | k₀ + 1 ≤ belowCount c (F.slot + 1) |  |
| le_div_succ_mul | 342 | hn | D + 1 ≤ (D / n + 1) * n |  |
| bad_budget_Ico | 355 | hBudget, (r₀ : Nat), ∀ k | ((Finset.Ico r₀ (r₀ + k * n)).filter fun s => bad s).card ≤ maxByzantine n * k | Declared under `open Classical in`. The filter predicate is the Prop `bad s`; matches badSlotsIn unfolded. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/TimedSig.lean

**Purpose:** Derives the recency-scoped unforgeability assumption SigUnforgeableRecent (consumed by light-client safety) from TimedExecution + a new residue NoBackdate, via the projected stamped log projectSigned; and proves NoBackdate is independent of the five TimedExecution fields by an explicit n = 2 counter-execution. Namespace MoltPetit.Model.

**Imports:**
- MoltPetit.Model.Timed

### Defs (2)

| name | kind | line | meaning |
|---|---|---|---|
| projectSigned | noncomputable def (open Classical in) | 53 | Stamped signing log read off a real-time log: participant p's entry at stamped slot s is (a choice of) the block stamped s that was signed AT real slot s, provided p is s's producer; canonical only at honest real slots (honest_once). |
| NoBackdate | def | 65 | No back-dating onto an honest stamp: a block whose STAMP is honest was signed at the real slot equal to its stamp (forward-secure / stamp-bound custody residue). Note `bad` is applied to the stamp B.slot, whereas TimedExecution applies `bad` to the real slot r. |

### Theorems (2)

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| sigUnforgeableRecent_of_timed | 79 | {n : Nat} {bad : ByzantineSlots} {log : TimedLog} {G : Bl…, hexec, hNB, hbridge | SigUnforgeableRecent n bad Signed (projectSigned n log) now Δ | now and Δ are arbitrary; the recency hypothesis inside SigUnforgeableRecent.verified_was_signed and the ValidChain/membership hypotheses are discarded (`intro B c _hVC _hBc _hrec hbadB hSB`). Uses only hexec.honest_once besides NoBackdate. The SigningLog produced is specifically projectSigned n log — to feed a safety theorem quantified over an abstract `signed : SigningLog`, instantiate signed := projectSigned n log. |
| noBackdate_independent | 119 | — | ∃ (bad : ByzantineSlots) (log : TimedLog) (G : Block), TimedExecution 2 bad log G ∧ ¬ NoBackdate bad log | Witness: bad := fun r => r = 3; log := fun r => if r = 3 then {⟨1, 1, some 100, 101, 0, 0⟩} else ∅; G := ⟨0, 0, none, 100, 0, 0⟩ (Block fields in order slot, height, prev, id, contentsHash, keyIndex). All five fields discharged via `refine { key_match := ?_, honest_stamp := ?_, honest_once := ?_, chain_order := ?_, id_inj := ?_ }`. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/Liveness.lean

**Purpose:** Liveness: (local) the honest one-block extension of a validator-accepted chain is again accepted, given the Byzantine budget and honest-block delivery (HonestBlocksCover) for newly matured windows; (global) a synchronous honest run buildChain g ss validates and has ss.length + 1 blocks. Namespace MoltPetit.Model. The produceBlock?-level corollaries (liveness_produce_block, liveness_produce_signed_block) are NOT here despite the module docstring — they are in MoltPetit/Results/Results.lean.

**Imports:**
- MoltPetit.Model.Soundness (transitively: MoltPetit.Model.Model, MoltPetit.Model.Safety, MoltPetit.Model.Definitions)

### Defs (2)

| name | kind | line | meaning |
|---|---|---|---|
| buildFrom | def | 289 | Extend tip by one honest block per schedule slot, each built on the previous; block id := its slot, contentsHash := 0, keyIndex := 0. |
| buildChain | def | 294 | A synchronous honest run from genesis g over honest schedule ss: a single linear chain, no forks, no adversarial blocks, no signatures, no record. |

### Theorems (16)

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| quorum_plus_byzantine_le | 48 | (n : Nat) | quorum n + maxByzantine n ≤ n |  |
| windowCount_mono | 58 | h | windowCount c u len ≤ windowCount c' u len |  |
| slot_le_tip_of_mem | 63 | hS, hTip, hx | x.slot ≤ tip.slot |  |
| strictSlots_append_one | 78 | hS, hAll | StrictSlots (c ++ [b]) |  |
| linksOk_append_one | 93 | ∀ (c : Chain) (b : Block), linksOk c = true, (∃ tip : Block, c.getLast? = some tip ∧ childOk tip b = t… | linksOk (c ++ [b]) = true |  |
| validChain_append_one | 123 | hValid, hTipEq, hChild, hAllDense | validChain n (c ++ [b]) = true | Purely structural; density for ALL windows matured at b (not just new ones) must be supplied. |
| window_dense_of_honest_cover_at | 161 | hS, hSCorrect, hBudgetU, hCover | quorum n ≤ windowCount c u n | Per-window form (budget only at this u). Uses chainSlotsIn_card, mem_chainSlotsIn (Model.lean), quorum_plus_byzantine_le, Finset.card_sdiff. |
| window_dense_of_honest_cover | 209 | hBudget, hS, hSCorrect, hCover | quorum n ≤ windowCount c u n |  |
| liveness_valid_extension | 232 | {n : Nat} {bad : ByzantineSlots} {record : SlotRecord} {c…, hBudget, hValid, hTipEq, hTipLt, hSCorrect, hCover | validChain n (c ++ [nextBlock slot newId contentsHash keyIndex tip]) = true | Liveness core. hCover is over the EXTENDED chain and only for windows newly matured at `slot` (old windows are dense by windowCount_mono). If `slot` itself is honest and lies in such a window, the cover demands some block of record slot inside c ++ [b], so the caller must have the new block (or another block at slot) in `record slot`. Uses validChain_sound (Soundness.lean) to obtain StrictSlots/MaturedWindowsDense from the Bool validator. |
| buildFrom_map_slot | 296 | (tip : Block) (ss : List Nat) | (buildFrom tip ss).map Block.slot = ss |  |
| buildFrom_length | 302 | (tip : Block) (ss : List Nat) | (buildFrom tip ss).length = ss.length |  |
| buildChain_length | 307 | (g : Block) (ss : List Nat) | (buildChain g ss).length = ss.length + 1 |  |
| buildChain_map_slot | 311 | (g : Block) (ss : List Nat) | (buildChain g ss).map Block.slot = g.slot :: ss |  |
| linksOk_buildFrom | 315 | ∀ (tip : Block) (ss : List Nat), List.IsChain (· < ·) (tip.slot :: ss) | linksOk (tip :: buildFrom tip ss) = true |  |
| strictSlots_buildChain | 335 | (g : Block) (ss : List Nat), h | StrictSlots (buildChain g ss) |  |
| liveness_global | 361 | {n : Nat} {g : Block} {ss : List Nat}, hGen, hChain, hBudget | validChain n (buildChain g ss) = true ∧ (buildChain g ss).length = ss.length + 1 | SINGLE-CHAIN ASSUMPTION BAKED IN: the run IS buildChain g ss — one linear chain where every block is built on its immediate predecessor (delivery/synchrony by construction, 'no honest fork'); the adversary is DEFINED as bad := fun s => s ∉ g.slot :: ss (every unscheduled slot is Byzantine, including the genesis slot being scheduled); the budget is required only over windows maturing at the last scheduled slot; record is defined internally as the run's own blocks (record s := (buildChain g ss).filter (·.slot = s)).toFinset). No TimedExecution/log, no signatures, no produceBlock?/selectChain, no competing chains, no id hypothesis (ids are the slot numbers). Aliased as Molt.global_liveness (Molt/Liveness.lean:33). |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/Definitions.lean

**Purpose:** All definitions needed to state the main results, in one file: executable model (blocks, chains, density validator, signed chains, production, chain selection), certified chains, semantic predicates of the safety proof, the signing model, TS-bridge injections, GroundedCert and the two light-client assumptions, the real-time signing model TimedExecution, HonestBlocksCover, and the ProverTiming defs. Namespace MoltPetit.Model (sub-namespace ProverTiming). No theorems. NOTE: validChainK, denseSoFar, faultBudget (named in the brief as if here) are NOT in this file — see Model/KeyIndex.lean:71, Molt/Protocol.lean:88, Molt/Protocol.lean:27.

**Imports:**
- Mathlib
- MoltPetit.TS.Emitted (namespace MoltPetit: the thales-emitted TS sidecar; provides MoltPetit.Chain, MoltPetit.CertClaim, MoltPetit.SignedChain, MoltPetit.SigOps, MoltPetit.RawSignature, MoltPetit.validChainK (Int) etc.)

### Defs (67)

| name | kind | line | meaning |
|---|---|---|---|
| quorum | def | 44 | Density threshold ⌈2n/3⌉. |
| maxByzantine | def | 47 | Max tolerated Byzantine slots per n-window ⌊(n-1)/3⌋ (Molt name: faultBudget). |
| producerForSlot | def | 50 | Round-robin producer index of a slot (Molt name: producer). |
| Block | structure | 58 | A block; id abstracts a collision-resistant hash supplied by the caller; keyIndex is the in-band delegate-key version the producer signed under. Anonymous-constructor field order: ⟨slot, height, prev, id, contentsHash, keyIndex⟩. |
| Chain | abbrev | 75 | Linear history, lowest height first. |
| blockInWindow | def | 78 | b's slot lies in [u, u+len). |
| windowCount | def | 82 | Number of chain blocks with slot in [u, u+len). |
| windowDense | def | 86 | One window meets quorum density. |
| maturedWindowsDense | def | 95 | All windows matured at tip slot t (u + n ≤ t + 1, i.e. u ∈ range (t+2-n)) are dense (Molt name: denseSoFar). |
| genesisOk | def | 99 | Structural genesis check (does NOT require slot = 0). |
| childOk | def | 103 | Immediate-successor check. |
| linksOk | def | 109 | Every adjacent pair satisfies childOk. |
| validChain | def | 122 | The executable validator replayed from genesis; [] is accepted. |
| tipHeight | def | 133 | Height of the tip if any. |
| selectChain | def | 141 | Longest-valid-chain adoption rule. No theorem anywhere in the repo is stated about it (only the definition, its @[export] wrapper, and Molt.selectChain which is the CERTIFIED-chain variant selectCertifiedChain). |
| nextBlock | def | 159 | The candidate child of tip. |
| produceBlock? | def | 162 | Honest production: only in own slot, only if the extension validates. |
| genesisBlock | def | 174 | Fresh-deployment genesis. |
| SigOps | structure | 187 | Abstract signature scheme over the Block content (signature not part of message). |
| KeyRegistry | abbrev | 204 | Versioned public-key directory: registry i j = participant i's delegate key at index j. |
| SignedBlock | structure | 212 | Wire block: content + detached signature. |
| SignedChain | abbrev | 218 | Signed chain. |
| stripSigs | def | 221 | Drop signatures. |
| sigOk | def | 226 | Per-block verification under the key selected by the block's producer AND its DECLARED in-band keyIndex. |
| sigsOk | def | 231 | All signatures verify. |
| validSignedChain | def | 241 | Signature check then structural validation. |
| produceSignedBlock? | def | 257 | Sign nextBlock with myKey, return it iff producerForSlot n slot = me and validSignedChain (sc ++ [sb]) (uses (stripSigs sc).getLast? as tip). |
| selectSignedChain | def | 272 | Adopt candidate iff validSignedChain and strictly longer. |
| trivialSigOps / trivialRegistry / signedGenesisBlock | def | 282 | Accept-everything signature instance for tests (lines 282, 288, 292). |
| validChainExport / produceBlockExport / selectChainExport | def (@[export mcv2_*]) | 300 | C entry points (lines 300, 303, 307). |
| CertClaim | structure | 322 | What a certificate claims: tip triple plus the boundary buffer of stripped prefix blocks near the tip. |
| CertOps | structure | 330 | Abstract certificate operations. |
| CertifiedChain | structure | 339 | Certificate for the prefix plus a signed suffix. |
| certTipHeight / certTipSlot / certTipId | def | 345 | Effective tip of a certified chain (suffix tip else claim). |
| validateSuffix | def | 365 | sigsOk on suffix && link from claim tip to first suffix block && linksOk && density of windows in [tipSlot+2-n, t.slot+2-n) counted over claim.tail ++ suffix. |
| validateCertifiedChain | def | 389 | Full certified-chain validation. |
| produceBlockCert? | def | 401 | Certified production; tip defaults to a synthetic block from the claim (prev := none, contentsHash 0, keyIndex 0) when the suffix is empty. |
| selectCertifiedChain | def | 419 | Adopt candidate iff validateCertifiedChain and certTipHeight strictly higher (this is what Molt.selectChain bridges to). |
| TrivialCert / trivialCertOps / trivialGenesisCertChain | abbrev/def | 431 | Trivial certificate = the full stripped prefix (lines 431, 434, 446). |
| SlotRecord | abbrev | 456 | Blocks produced in each slot over the whole execution. |
| ByzantineSlots | abbrev | 459 | Adversary schedule; bad s = adversary owns slot s (Prop, so Finset filters need Classical). |
| blockAt? | def | 462 | Block at list index h (unfold to getElem? then use List.getElem?_eq_some_iff / List.mem_of_getElem?). |
| SequentialHeights | def | 465 | Index = height. |
| StrictSlots | def | 469 | Slots strictly increase. |
| ParentLinked | def | 473 | Index 0 has no parent; every later block points at its predecessor's id. |
| MaturedWindowsDense | def | 484 | Every window matured at any chain block is quorum-dense (counted over the whole chain c). |
| ValidChain | def | 490 | Semantic validity; destructure as ⟨hSeq, hS, hPL, hMat⟩. |
| ChainInRecord | def | 494 | Every chain block was produced. |
| HonestSlotsUnique | def | 498 | Honest slot has ≤ 1 produced block. |
| IdInjective | def | 503 | Ids injective across the record. |
| badSlotsIn | noncomputable def (open Classical in) | 509 | Bad slots in [u, u+n). |
| ByzantineBounded | def | 513 | ≤ ⌊(n-1)/3⌋ bad slots in every n-window (Molt name: FaultBounded, rfl-equal). |
| CommonPrefixUpTo / LastCommonHeight | def | 517 | Fork-point predicates (lines 517, 521). |
| chainSlotsIn | def | 527 | Distinct slots occupied in a window; card = windowCount under StrictSlots (chainSlotsIn_card, Model.lean:60). |
| SigCorrect | structure (Prop) | 541 | Signature-scheme correctness at the block's DECLARED index j. |
| SigningLog | abbrev | 558 | Honest stamped signing log: signed i s = some B iff participant i signed exactly B for slot s. |
| toTSChain / toTSClaim / toTSSigned | def | 568 | Injections into the thales-emitted TS representation (lines 568, 574, 580). |
| TSSigned | def | 597 | B carries a signature verifying under keyFor (producer, DECLARED keyIndex) — the concrete Signed predicate for TS results. |
| GroundedCert | inductive (Prop) | 627 | Inductive certificate model: claims grounded in genesis G (which must have slot 0) by signed folds. |
| SignedHashInjective | def | 656 | Collision resistance over occurring blocks (same shape as TimedExecution.id_inj with Signed := ∃ r, · ∈ log r). |
| SigUnforgeableRecent | structure (Prop) | 677 | Recency-scoped honest-slot pinning; `bad` is applied to the STAMP B.slot. |
| TimedLog | abbrev | 694 | What was signed at each REAL slot r (under r's producer's key). |
| SignedEver | def | 698 | Domain of id injectivity in the timed model. |
| AvailableAt | def | 703 | B exists by real slot R. |
| TimedExecution | structure (Prop) | 719 | Real-time signing model, ALL FIVE FIELDS: key_match (stamp ≡ real slot mod n), honest_stamp (honest real slot signs only its own stamp), honest_once (honest real slot signs ≤ 1 block), chain_order (a signed block's parent — some block with the referenced id — is available at or before the signing real slot; residue of id = H(..., parentSig, ...)), id_inj (collision resistance over genesis ∪ ever-signed). `bad` here is over REAL slots r. Corruption is per real slot; a bad real slot may sign any stamp in its residue class. |
| HonestBlocksCover | def | 753 | Honest-block delivery for window [u, u+n): every honest slot has a recorded block already in c (liveness/synchrony packaging). |
| ProverTiming (namespace) | namespace | 763 | Prover-throughput model over ℚ; its theorems (nextBacklog_le, nextBacklog_nonneg, recommended_slot_sufficient, recommended_slot_necessary, backlog_diverges) are in MoltPetit/Results/Results.lean lines 514-596. |

### Theorems (0)

(none)

## /etheron-pod/mini-consensus-lean/MoltPetit/Results/Results.lean

**Purpose:** REFERENCE (partially read: statements only). Headline results: forged-time bounds assembled from Timed.lean, liveness_produce_block / liveness_produce_signed_block built on Liveness.lean, ProverTiming theorems. Namespace MoltPetit.Model. Docstring: 'All results depend only on propext, Classical.choice, Quot.sound'.

**Imports:**
- MoltPetit.Model.Grounded
- MoltPetit.Model.Timed

### Defs (1)

| name | kind | line | meaning |
|---|---|---|---|
| model_no_deep_fork / model_deep_block_agreement / model_validChain_sound | alias | 71 | Aliases of the Safety/Soundness engine results. |

### Theorems (8)

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| forged_suffix_time_bound | 102 | hn, hexec, hBudget, hValid, hGprev, hAvail, hk₀, hF, hFr, hFmin, hForged, hTip | quorum n * ((tip.slot - F.slot) / n) ≤ maxByzantine n * ((R - r₀) / n + 1) | `open Classical in`. Budget is ByzantineBounded on REAL slots (bad_budget_Ico over Ico r₀ (R+1)); density is read off c's own matured windows (hMat at the tip index blockAt_getLast). Uses belowCount_prefix, belowCount_windows, belowCount_le, block_signed, one_real_slot_one_block, le_div_succ_mul, Finset.card_le_card_of_injOn. Transported as Molt.forged_time_bound. |
| forged_suffix_lag | 231 | all hypotheses of forged_suffix_time_bound, hf | 2 * ((tip.slot - F.slot) / n) ≤ (R - r₀) / n + 1 | Uses 2 * maxByzantine n + 1 ≤ quorum n (omega after unfold). |
| forged_chain_time_bound | 285 | hn, hexec, hBudget, hValid, hGprev, hAvail, hForged, hTip | quorum n * ((tip.slot + 1) / n) ≤ maxByzantine n * (R / n + 1) + 1 | From-genesis form; windows aligned at 0 (belowCount_zero). Aliased verbatim as Molt.forged_chain_time_bound (Molt/Results.lean:128). |
| forged_chain_lag | 386 | all hypotheses of forged_chain_time_bound, hf | 2 * ((tip.slot + 1) / n) ≤ R / n + 3 |  |
| liveness_produce_block | 429 | {n me slot newId : Nat} {contentsHash keyIndex : Nat} {ba…, hBudget, hValid, hTipEq, hTipLt, hMine, hSCorrect, hCover | produceBlock? n me slot newId contentsHash keyIndex c = some (nextBlock slot newId contentsHash keyIndex tip) | = liveness_valid_extension + simp [produceBlock?]. Single chain c held by the producer; nothing about selectChain or other nodes. Aliased as Molt.production_liveness. |
| liveness_produce_signed_block | 455 | hn, {ops : SigOps σ sk pk} {registry : KeyRegistry pk} {keyPa…, hSig, hBudget, hValid, hTipEq, hTipLt, hMine, hSCorrect, hCover | produceSignedBlock? n me slot newId contentsHash keyIndex ops registry (keyPair me keyIndex) sc = some ⟨nextBlock slot newId contentsHash keyIndex tip, ops.sign (keyPair me keyIndex) (nextBlock slot newId contentsHash keyIndex tip)⟩ | Signs with keyPair me keyIndex, i.e. the DECLARED index; SigCorrect discharges the self-check. hn : 1 ≤ n is taken but (per docstring) a 'full registry' is not otherwise formalized. Aliased as Molt.signed_production_liveness. |
| ProverTiming.recommended_slot_sufficient | 544 | hn, hb, hpb, hτpos, hτ, hu₀, hub₀ | ∀ j, backlog baseline perBlock τ u₀ j ≤ n / 2 ∧ peakSuffix baseline perBlock τ (backlog baseline perBlock τ u₀ j) ≤ n | Aliased as Molt.slot_time_sufficient. |
| ProverTiming.recommended_slot_necessary | 571 | hn, hpb0, hpb, hτ, hsteady | n < peakSuffix baseline perBlock τ u | Aliased as Molt.slot_time_necessary. Other ProverTiming lemmas: nextBacklog_le (514), nextBacklog_nonneg (528), backlog_diverges (596: τ ≤ perBlock → ∀ j, u₀ + j * (baseline / τ) ≤ backlog ... j). |

## /etheron-pod/mini-consensus-lean/Molt/Results.lean

**Purpose:** REFERENCE (read lines 1-60, 90-150). Paper-facing (namespace Molt) re-presentation of safety and the timed bounds. Shows the bridging idiom: abbrev for structures (TimedExecution), fresh def + rfl bridge for simple defs (AvailableAt, blockAt?), transport theorem whose proof is the core theorem applied verbatim, and `alias` for theorems needing no renaming.

**Imports:**
- Molt.Assumptions
- MoltPetit.Results.Results
- MoltPetit.Model.TimedSig

### Defs (7)

| name | kind | line | meaning |
|---|---|---|---|
| Molt.TimedLog | abbrev | 25 | Re-export. |
| Molt.AvailableAt | def | 29 | Fresh copy; availableAt_eq_core (41) : AvailableAt = MoltPetit.Model.AvailableAt := rfl. |
| Molt.TimedExecution | abbrev | 36 | Re-export (structure, so not re-declared). |
| Molt.blockAt? | def | 39 | Fresh copy; blockAt?_eq_core (42) := rfl. |
| Molt.NoBackdate | abbrev | 140 | Re-export. |
| Molt.projectSigned | noncomputable abbrev | 143 | Re-export. |
| Molt.forged_chain_time_bound / forged_suffix_lag / sigUnforgeableRecent_of_timed / noBackdate_independent | alias | 128 | Verbatim aliases. |

### Theorems (2)

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| Molt.forged_time_bound | 110 | hn, hexec, hBudget, hValid, hGprev, hAvail, hk₀, hF, hFr, hFmin, hForged, hTip | quorum n * ((tip.slot - F.slot) / n) ≤ faultBudget n * ((rNow - r₀) / n + 1) | Proof is literally `MoltPetit.Model.forged_suffix_time_bound hn hexec hBudget hValid hGprev hAvail hk₀ hF hFr hFmin hForged hTip` — accepted because Molt.FaultBounded/AvailableAt/blockAt?/quorum/faultBudget are rfl-equal to the core. |
| Molt.light_client_safety | 54 | hn, hBudget, hSig, hHash, … (further cert/suffix hyps, not read in full) | B = B' | Transported from MoltPetit.Model.recent_certified_suffix_agreement; needs `rw [linksOk_eq_core] at hLinks hLinks'` because linksOk's bridge is not rfl. |

## /etheron-pod/mini-consensus-lean/Molt/Liveness.lean

**Purpose:** REFERENCE (read in full, 45 lines). Paper-facing liveness names — pure aliases, no restatement ('the theorems quantify over the model-level production and selection functions, which the paper does not re-present').

**Imports:**
- Molt.Rotation
- MoltPetit.Results.Results
- MoltPetit.Model.KeyRotationLiveness

### Defs (5)

| name | kind | line | meaning |
|---|---|---|---|
| Molt.production_liveness | alias | 19 | Paper Theorem 6, unsigned form. |
| Molt.signed_production_liveness | alias | 22 | Signed form. |
| Molt.liveness_produce_blockK | alias | 27 | Mode-1 (pinned validator) liveness. |
| Molt.global_liveness | alias | 33 | Paper Theorem 6, global form. |
| Molt.slot_time_sufficient / slot_time_necessary | alias | 39 | Slot-duration rule. |

### Theorems (0)

(none)

## /etheron-pod/mini-consensus-lean/Molt/Protocol.lean

**Purpose:** REFERENCE (read in full, 142 lines). Fresh paper-ordered restatement of the data model and density rule with rfl/funext bridges to MoltPetit.Model. Namespace Molt. Block/Chain are re-exported abbrevs (a re-declared structure would not transport).

**Imports:**
- MoltPetit.Model.Definitions

### Defs (7)

| name | kind | line | meaning |
|---|---|---|---|
| Molt.quorum | def | 23 | quorum_eq_core (110) := rfl. |
| Molt.faultBudget | def | 27 | faultBudget_eq_core (111) : faultBudget = MoltPetit.Model.maxByzantine := rfl. |
| Molt.producer | def | 31 | producer_eq_core (112) : producer = MoltPetit.Model.producerForSlot := rfl. |
| Molt.Block / Molt.Chain | abbrev | 44 | Shared types. |
| Molt.genesisBlock / genesisOk / childOk / linksOk / blockInWindow / windowCount / windowDense | def | 51 | Bridges: genesisBlock_eq_core (113), genesisOk_eq_core (114), childOk_eq_core (115), windowDense_eq_core (116) are rfl; linksOk_eq_core (119) is by funext+induction (NOT rfl). |
| Molt.denseSoFar | def | 88 | denseSoFar_eq_core (117) : denseSoFar = MoltPetit.Model.maturedWindowsDense := rfl. |
| Molt.validChain | def | 94 | validChain_eq_core (129) : validChain = MoltPetit.Model.validChain, by funext/cases/simp (NOT rfl). |

### Theorems (0)

(none)

## /etheron-pod/mini-consensus-lean/Molt/Assumptions.lean

**Purpose:** REFERENCE (read in full, 92 lines). Deployment assumptions in paper form; proof-side predicates re-exported as abbrevs; assumption statements written fresh with rfl bridges.

**Imports:**
- Molt.Verifier (← Molt.Protocol ← MoltPetit.Model.Definitions)

### Defs (7)

| name | kind | line | meaning |
|---|---|---|---|
| Molt.SlotRecord / ByzantineSlots / ValidChain / SigningLog | abbrev | 19 | Re-exports. |
| Molt.badSlotsIn | noncomputable def (open Classical in) | 33 | badSlotsIn_eq_core (81) := rfl. |
| Molt.FaultBounded | def | 38 | faultBounded_eq_core (82) : FaultBounded = MoltPetit.Model.ByzantineBounded := rfl. |
| Molt.SigUnforgeableRecent / GroundedCert | abbrev | 45 | Re-exported structure/inductive (note the explicit @). |
| Molt.SignedHashInjective | def | 50 | signedHashInjective_eq_core (84) := rfl. |
| Molt.HonestBlocksCover | def | 63 | honestBlocksCover_eq_core (86) := rfl. |
| Molt.HonestSlotsUnique / IdInjective | def | 70 | Conclusion-side predicates. |

### Theorems (0)

(none)

## /etheron-pod/mini-consensus-lean/Molt/Verifier.lean

**Purpose:** REFERENCE (declaration list + lines 150-199). Signed/certified verifier re-presentation. Molt.selectChain is the CERTIFIED-chain selection (bridges to MoltPetit.Model.selectCertifiedChain), not the plain MoltPetit.Model.selectChain.

**Imports:**
- Molt.Protocol

### Defs (2)

| name | kind | line | meaning |
|---|---|---|---|
| Molt.SigOps / KeyRegistry / SignedBlock / SignedChain / CertClaim / CertOps / CertifiedChain | abbrev | 21 | Re-exported types. |
| Molt.stripSigs / sigOk / sigsOk / validSignedChain / tipHeight / validSuffix / validCertifiedChain / produceBlock? / selectChain | def | 35 | Bridges: stripSigs_eq_core (147), sigOk_eq_core (149), sigsOk_eq_core (151), tipHeight_eq_core (161) are rfl; validSignedChain_eq_core (154), validSuffix_eq_core (164), validCertifiedChain_eq_core (177), produceBlock?_eq_core (184), selectChain_eq_core (191) are funext/simp (NOT rfl). |

### Theorems (0)

(none)

## /etheron-pod/mini-consensus-lean/Molt/Rotation.lean

**Purpose:** REFERENCE (lines 1-100, 175-215). Paper re-presentation of the indexed validators; validChainK lives here for Molt.

**Imports:**
- Molt.Results
- MoltPetit.Results.KeyStealingResults
- MoltPetit.Results.KeyStealingScheduleResults
- MoltPetit.Model.KeyStealingHorizon
- MoltPetit.Model.KeyStealingLockstep
- MoltPetit.Model.KeyStealingCert
- MoltPetit.Model.KeyStealingScheduleCert

### Defs (3)

| name | kind | line | meaning |
|---|---|---|---|
| Molt.keyMonoOk | def | 33 | In-band monotone rule. |
| Molt.validChainK | def | 44 | validChainK_eq_core (185) : validChainK = MoltPetit.Model.validChainK by funext/simp (NOT rfl). |
| Molt.keyFloor / confirmedPrefix / inForce / inForcePinned / validChainK' / validSignedChainK' | def | 57 | Mode-1 pinned validators; keyFloor/confirmedPrefix/inForce/inForcePinned bridges are rfl (176-181); validChainK'_eq_core (190), validSignedChainK'_eq_core (196) are funext/simp. |

### Theorems (1)

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| Molt.validChainK_structural | 50 | h | validChain n c = true |  |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyIndex.lean

**Purpose:** REFERENCE (lines 1-100). Core validChainK (the name the brief attributes to Definitions.lean).

**Imports:**
- MoltPetit.Model.Safety
- MoltPetit.Model.Soundness

### Defs (4)

| name | kind | line | meaning |
|---|---|---|---|
| keyMonoOk | def | 54 | Validator's in-band key-rotation rule. |
| KeyIndexMonotone | def | 64 | Semantic counterpart. |
| validChainK | def | 71 | Indexed validator; validChainK_sound (elsewhere in file) gives ValidChain. |
| keyFloor | def | 77 | Highest index participant i has used in c. |

### Theorems (0)

(none)

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyRotationLiveness.lean

**Purpose:** REFERENCE (lines 1-40, 100-180). Liveness under the index-pinned validator validChainK'.

**Imports:**
- MoltPetit.Results.Results
- MoltPetit.Model.KeyStealingCert

### Defs (0)

(none)

### Theorems (1)

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| liveness_produce_blockK | 130 | {n Δconf me slot newId : Nat} {contentsHash keyIndex : Na…, hBudget, hValidK, hTipEq, hTipLt, hMine, hSCorrect, hCover, hFloor | produceBlock? n me slot newId contentsHash keyIndex c = some (nextBlock slot newId contentsHash keyIndex tip) ∧ validChainK' n Δconf (c ++ [nextBlock slot newId contentsHash keyIndex tip]) = true | Same single-chain shape as liveness_produce_block plus floor clearance at the DECLARED keyIndex (vs the registered/in-force version handled by inForcePinned). Converse: extension_rejected_below_floor (100): keyIndex < keyFloor n c (producerForSlot n slot) → validChainK' n Δconf (c ++ [nextBlock ...]) = false. Signed variant liveness_produce_signed_blockK (160) adds hn : 1 ≤ n, SigCorrect, validSignedChainK' hypotheses and hFloor over stripSigs sc. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/Model.lean

**Purpose:** REFERENCE (lines 1-90). Basic lemmas Liveness.lean/Timed.lean consume.

**Imports:**
- MoltPetit.Model.Definitions

### Defs (0)

(none)

### Theorems (6)

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| mem_chainSlotsIn | 35 | {c : Chain} {u len s : Nat} | s ∈ chainSlotsIn c u len ↔ ∃ B : Block, B ∈ c ∧ (u ≤ B.slot ∧ B.slot < u + len) ∧ B.slot = s |  |
| chainSlotsIn_subset_Ico | 40 | {c : Chain} {u len : Nat} | chainSlotsIn c u len ⊆ Finset.Ico u (u + len) |  |
| strictSlots_lt | 47 | hS, hi, hj, hij | Bi.slot < Bj.slot |  |
| chainSlotsIn_card | 60 | hS | (chainSlotsIn c u len).card = windowCount c u len |  |
| exists_blockAt_of_mem | 71 | hB | ∃ k, blockAt? c k = some B |  |
| exists_blockAt_of_le | 79 | hk, hAt | ∃ C : Block, blockAt? c k = some C |  |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/Soundness.lean

**Purpose:** REFERENCE (lines 1-12, 90-145). Bool validator → semantic ValidChain.

**Imports:**
- MoltPetit.Model.Model
- MoltPetit.Model.Safety

### Defs (0)

(none)

### Theorems (3)

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| blockAt_getLast | 97 | hTip | blockAt? ch (ch.length - 1) = some tip |  |
| maturedDense_of_check | 104 | hS, hTip, hCheck | MaturedWindowsDense n ch |  |
| validChain_sound | 130 | {n : Nat} ∀ {ch : Chain}, validChain n ch = true | ValidChain n ch | Aliased as model_validChain_sound in Results.lean:78. The hinge from executable to semantic. |

## /etheron-pod/mini-consensus-lean/MoltPetit/TS/Bridge.lean

**Purpose:** REFERENCE (header + lines 128-140). Holds windowCount_cons, which Timed.lean's belowCount_split uses (reached via Grounded's import of TS.Bridge).

**Imports:**
- MoltPetit.Model.Model
- MoltPetit.Model.Soundness
- MoltPetit.Model.KeyIndex

### Defs (0)

(none)

### Theorems (1)

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| windowCount_cons | 134 | (b : Block) (rest : Chain) (u len : Nat) | windowCount (b :: rest) u len = (if blockInWindow u len b then 1 else 0) + windowCount rest u len |  |

## reuse_notes

IMPORT GRAPH (what a new file gets transitively): Definitions ← Model ← Safety ← Soundness ← Liveness; KeyIndex imports Safety+Soundness; TS/Bridge imports Model+Soundness+KeyIndex; Grounded imports TS/Bridge + Liveness; Timed imports Grounded; TimedSig imports Timed; Results/Results.lean imports Grounded + Timed (NOT TimedSig); KeyRotationLiveness imports Results.Results + KeyStealingCert. Molt side: Molt.Protocol ← Molt.Verifier ← Molt.Assumptions ← Molt.Results (also imports MoltPetit.Results.Results + MoltPetit.Model.TimedSig) ← Molt.Rotation ← Molt.Liveness (also imports KeyRotationLiveness). So: a new core module wanting TimedExecution + liveness + forged bounds + NoBackdate should `import MoltPetit.Results.Results` and `import MoltPetit.Model.TimedSig`; a new Molt-side module should `import Molt.Results` (and `Molt.Liveness`/`Molt.Rotation` if it needs validChainK/global_liveness names).

BUILD REGISTRATION GOTCHA: lakefile.toml declares the four lean_libs (MoltPetit, Rust, Thales, Molt) with NO `globs`, so the default `lake build` only compiles modules reachable from the root import lists in MoltPetit.lean / Molt.lean. A purely additive file (no edits to existing files) must be built explicitly, e.g. `lake build MoltPetit.Model.<New>` or `lake build Molt.<New>`, and it will not be covered by the existing axiom audit (MoltPetit/Results/Axioms.lean uses `#guard_msgs in #print axioms` per headline theorem) — replicate that guard locally in the new file if axiom hygiene matters. Toolchain: leanprover/lean4:v4.30.0-rc2, Mathlib v4.30.0-rc2, `relaxedAutoImplicit = false` (bind every variable), mathlib standard linter set on.

NAMESPACE/IDIOMS: core proofs live in `namespace MoltPetit.Model` (sub-namespace ProverTiming); paper-facing re-presentations in `namespace Molt`. Molt idiom: shared TYPES are `abbrev` (Block, Chain, SigOps, TimedLog, TimedExecution, NoBackdate, SigUnforgeableRecent via `@`), simple computable/Prop defs are re-declared verbatim and bridged by `theorem foo_eq_core : foo = MoltPetit.Model.foo := rfl`, recursive/matching defs are bridged by funext+induction/simp (linksOk, validChain, validSignedChain, validSuffix, validCertifiedChain, produceBlock?, selectChain, validChainK, validChainK', validSignedChainK') and must be `rw [..._eq_core] at h` before feeding hypotheses to a core theorem; theorems are either `alias X := MoltPetit.Model.X` or restated with paper names (FaultBounded, faultBudget, producer, rNow) and proved by applying the core theorem verbatim (definitional unfolding covers rfl bridges). Prop-structures (TimedExecution, SigUnforgeableRecent, SigCorrect) are built with `refine { key_match := ?_, honest_stamp := ?_, honest_once := ?_, chain_order := ?_, id_inj := ?_ }` or `constructor`. Finset filters over `bad : Nat → Prop` need `open Classical in` (badSlotsIn, bad_budget_Ico, projectSigned, forged_* theorems). First-signing time is `Nat.find (h : ∃ r, B ∈ log r)` with `Nat.find_eq_iff`, `Nat.find_spec`, `Nat.find_min'`, and theorems phrase minimality as `∀ r' < r, B ∉ log r'`. `blockAt?` is `getElem?`: unfold then `List.getElem?_eq_some_iff`, `List.getElem?_eq_getElem`, `List.mem_of_getElem?`; `ValidChain` destructures as ⟨hSeq, hS, hPL, hMat⟩; go Bool→semantic with `validChain_sound`; tip index via `blockAt_getLast`; index→slot order via `strictSlots_lt`; membership→index via `exists_blockAt_of_mem`.

GENESIS / INDEX-0 GOTCHAS: block_signed, sigTime_mono_chain, one_real_slot_one_block, forged_suffix_time_bound all require the index k (or k₀) ≥ 1 and `hGprev : G.prev = none`; they do NOT require c[0] = G, only ParentLinked (so c[0].prev = none) — hence any block at index ≥ 1 is ≠ G and is in the log by hAvail. hAvail must cover every block of c including index 0 (satisfied via the `B = G` disjunct or a log entry). GroundedCert.genesis additionally demands `G.slot = 0` and `genesisOk G`; liveness_global demands `genesisOk g` but not g.slot = 0 (g.slot is whatever heads the schedule). validChain accepts [] and does not check slot 0.

BAD-SLOT READINGS (real vs stamped): TimedExecution applies `bad` to REAL slots r (honest_stamp/honest_once, and hForged in the forged bounds quantify `bad r` over signing slots); NoBackdate, SigUnforgeableRecent.verified_was_signed, HonestBlocksCover, HonestSlotsUnique apply `bad` to the STAMP B.slot / record slot s; ByzantineBounded n bad is one budget used for both readings. They coincide only under NoBackdate/honest_stamp. A new module mixing timed and stamped statements must pick one `bad` and prove the crossover explicitly.

BUDGET/DENSITY READ-OFF: forged_suffix_time_bound / forged_chain_time_bound read density from the chain c's own MaturedWindowsDense at its tip (windows aligned at F.slot+1 + j*n resp. 0 + j*n via belowCount_windows) and the budget from ByzantineBounded on real slots (bad_budget_Ico over Ico r₀ (R+1) resp. Ico 0 (R+1)); both need hn : 2 ≤ n; the lag corollaries additionally need 1 ≤ maxByzantine n (i.e. n ≥ 4). Molt.forged_time_bound is the SUFFIX bound (paper Theorem 2); Molt.forged_chain_time_bound is the alias of the from-genesis bound.

SIGNED PREDICATE, DECLARED vs REGISTERED: sigUnforgeableRecent_of_timed takes an abstract `Signed : Block → Prop` plus the EUF-CMA bridge `hbridge : Signed B → ∃ r, B ∈ log r` (this bridge is the only place the crypto enters; nothing in the repo proves it for TSSigned). TSSigned / sigOk / SigCorrect all verify under the block's DECLARED in-band keyIndex (`keyFor (producerForSlot n B.slot) B.keyIndex`), not the version in force; the in-force check is validChainK'/inForcePinned (KeyRotation). The result of sigUnforgeableRecent_of_timed is for `signed := projectSigned n log` (noncomputable, Classical.choose; canonical only at honest real slots) and holds for every now and Δ — the recency scoping is slack there.

LIVENESS SINGLE-CHAIN ASSUMPTION: liveness_valid_extension / liveness_produce_block / liveness_produce_blockK all speak about ONE chain c the producer holds (c.getLast? = some tip, validChain n c = true as Bool) and demand HonestBlocksCover over the EXTENDED chain c ++ [nextBlock ...] for exactly the windows newly matured at `slot` (tip.slot + 1 < u + n ≤ slot + 1); if `slot` is honest and inside such a window the cover forces some `record slot` block to be in c ++ [b], i.e. the caller must register the new block in `record`; `hSCorrect : ∀ s B, B ∈ record s → B.slot = s` is a global record hypothesis. liveness_global hard-codes the single chain: the run IS buildChain g ss (each block built on its immediate predecessor; ids = slots, contentsHash = keyIndex = 0), `bad := fun s => s ∉ g.slot :: ss` (every unscheduled slot is adversarial by definition), budget only over windows maturing by the last scheduled slot, record := the run's own blocks. There is no theorem anywhere about MoltPetit.Model.selectChain (Molt.selectChain is selectCertifiedChain); no theorem connects liveness to TimedExecution/log, to competing chains, or to forks. A new module wanting multi-chain or network liveness must add its own model; the reusable pieces are validChain_append_one, window_dense_of_honest_cover(_at), windowCount_mono, strictSlots_append_one, linksOk_append_one, slot_le_tip_of_mem, quorum_plus_byzantine_le, and the buildChain lemmas.

ARITHMETIC FACTS proved inline (re-derive with `unfold quorum maxByzantine; omega`): quorum n + maxByzantine n ≤ n (theorem), 2 ≤ quorum n given 2 ≤ n, 2 * maxByzantine n + 1 ≤ quorum n.


## open_items_found

- Timed.lean:20-24 — 'Main results (stated in `Results/Results.lean`): `forged_suffix_time_bound` and `forged_chain_time_bound` … This module holds the model and the counting lemmas' — the headline timed theorems are NOT in Timed.lean; the module has only lemmas + belowCount.
- Timed.lean:14-18 — 'The id-formation contract (`moltPetit.ts`: a block id hashes the parent's *signature*) appears as its formal residue, `chain_order` … referencing an id whose preimage contains a not-yet-existing signature would be predicting a signature, i.e. an EUF-CMA forgery.' — the reduction from the hash/signature contract to chain_order is informal (chain_order is an assumed field).
- TimedSig.lean:30-36 — NoBackdate 'is guaranteed by *forward-secure / key-evolving* signatures (the per-period key cannot sign for a different period — exactly the upgrade the limitations section recommends), or by a signing oracle that stamps its own real slot.' — operational justification only; no formal model of forward-secure signatures.
- TimedSig.lean:37-40 — 'the scoping in `SigUnforgeableRecent` is then slack, which matches the operational reading that forward-secure custody removes the long-range residual entirely.' — informal reading.
- TimedSig.lean:74-77 — 'This is the formal replacement for the conjecture that the assumption "follows from the recency bound itself"' — records that the earlier conjecture was wrong and replaced; the recency→pinning route is explicitly NOT a theorem (noBackdate_independent).
- TimedSig.lean:114-116 — '(The forged block could moreover sit at an arbitrarily recent tip — an operational remark, not part of this statement, which asserts only the `TimedExecution` ∧ ¬`NoBackdate` witness.)'
- TimedSig.lean:83 — the EUF-CMA bridge `hbridge : ∀ ⦃B⦄, Signed B → ∃ r, B ∈ log r` is an assumption of sigUnforgeableRecent_of_timed; nothing in the four files (or Results/Molt headers read) discharges it for the concrete TSSigned predicate.
- Liveness.lean:26-34 module docstring '## Results' lists `liveness_produce_block` and `liveness_produce_signed_block — wire-level version: with signature correctness (`SigCorrect`), `produceSignedBlock?` succeeds too' as results of this module, but they are defined in MoltPetit/Results/Results.lean:429 and :455 — stale docstring.
- Liveness.lean:270-285 — 'The theorems above are *local*: one honest producer extends its chain. Global liveness is the temporal/network statement … We model a synchronous honest run as `buildChain g ss` … That each block is built on the previous one is exactly the delivery assumption — every honest block reaches the next honest producer within its slot, so the honest blocks form a single chain (no honest fork).' — synchrony/delivery is modeled by construction, not by a network or adversary model; no adversarial blocks, forks, or chain selection appear.
- Liveness.lean:348-351 — '`hChain` — genesis and the schedule slots strictly increase (a single honest chain: delivery makes each honest producer build on the last honest block)'.
- Liveness.lean:357-359 — 'Since `ss` can be arbitrarily long, the chain reaches any height — production never stalls, and every block eventually becomes `n`-deep.' — the 'any height' / 'eventually n-deep' reading is informal; the theorem states only validChain ∧ length = ss.length + 1 for a fixed schedule.
- Liveness.lean:19-21, Definitions.lean:746-751 — HonestBlocksCover 'packages two operational facts: honest producers were live in their slots (they produced), and the network delivered their blocks in time for the current producer to have built on them (synchrony).' — informal packaging.
- Definitions.lean:7-12 — 'read this and `Results.lean` … and you have the complete formal content of the development. The remaining modules contain only proofs.' — not accurate: Timed.lean defines belowCount, TimedSig.lean defines projectSigned/NoBackdate, Liveness.lean defines buildFrom/buildChain, KeyIndex/KeyRotation define validChainK/keyFloor/validChainK' etc.
- Definitions.lean:114-120 (validChain) — 'production code may check matured windows incrementally per received block, which is equivalent because earlier windows were checked when validating the parent.' — equivalence claim is informal.
- Definitions.lean:136-139 (selectChain) — 'Safety does not depend on this rule (the safety theorem quantifies over arbitrary valid chains); it only affects liveness.' — yet no liveness theorem mentions selectChain; only the definition, its @[export] wrapper, and Molt's certified-chain selectChain_eq_core exist.
- Definitions.lean:155-157 (produceBlock?) — 'The node's outer loop calls this at most once per slot, which together with the conditions above realises the honest-slot assumptions of the safety proof.' and :554-556 (SigningLog) — 'That this is a partial *function* … is precisely the honest behaviour of the implementation: the node's outer loop calls production at most once per slot.' — implementation↔HonestSlotsUnique/honest_once link is informal.
- Definitions.lean:665-675 (SigUnforgeableRecent docstring) — 'This is the assumption the timed model justifies for the tight rule `Δ = n` … a fork meeting the recency bar caps out around `2·maxByzantine ≈ 2n/3` harvested blocks — short of the `n + 1` needed … (breakeven at `Δ ≈ 1.5n`, so `Δ = n` keeps ~50% margin).' — a counting heuristic; there is no theorem deriving SigUnforgeableRecent from forged_suffix_time_bound (TimedSig derives it from NoBackdate with Δ unused, and explicitly says recency alone does not suffice).
- Definitions.lean:706-717 (TimedExecution docstring) — '`chain_order` is the formal residue of the id-formation contract (`id = H(slot, height, prev, parentSig, contentsHash, keyIndex)`) … Predicting an unavailable parent's id is predicting a signature, i.e. an EUF-CMA forgery.' — cryptographic argument informal.
- Definitions.lean:786-788 (recommendedSlot) — 'Sufficient and necessary (over steady states)' — proved in Results.lean (recommended_slot_sufficient/necessary), fine; but 'over steady states' means necessity is only for fixed points of nextBacklog.
- Results.lean:447-450 (liveness_produce_signed_block docstring) — 'additionally assuming signature-scheme correctness (`SigCorrect`), a full registry (`registry.size = n`), and that the producer signs with its own key' — 'registry.size = n' is not a hypothesis of the theorem (only hn : 1 ≤ n appears); stale wording.
- KeyRotationLiveness.lean:26-27 — 'The deployment-level mitigation (an out-of-band root-authorization horizon on index jumps) is orthogonal and stated in the paper.' — not formalized.
- Molt.lean docstring — 'Modules grow section by section with the paper; the imports above are the current frontier.' and Molt/Liveness.lean:37-38 — 'The paper states the rule qualitatively; the formula lives here.'
- Brief/naming mismatches: `validChainK` is not in Definitions.lean (core: MoltPetit/Model/KeyIndex.lean:71; Molt: Molt/Rotation.lean:44); `denseSoFar` is Molt/Protocol.lean:88 (= maturedWindowsDense, rfl); `faultBudget` is Molt/Protocol.lean:27 (= maxByzantine, rfl); `forged_time_bound` is Molt/Results.lean:110 (= forged_suffix_time_bound); `global_liveness` is the alias Molt/Liveness.lean:33 of liveness_global; `liveness_produce_blockK` is MoltPetit/Model/KeyRotationLiveness.lean:130.
- No `sorry`/`axiom` in project sources (Molt, MoltPetit, Rust, Thales, Main.lean); only mentions in docstrings of the axiom-audit files.
