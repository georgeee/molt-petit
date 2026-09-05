# core-grounded-cert1 — Certificate grounding + certified-suffix agreement: MoltPetit/Model/Grounded.lean and MoltPetit/Model/KeyStealingCert.lean (plus cited context ranges of the definitions they consume)

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/Grounded.lean

**Purpose:** Inductive model of the certificate primitive (GroundedCert, defined in Definitions.lean) reconstructed into a validator-accepted prefix chain (groundedCert_history), extended by a TS-validated suffix (grounded_suffix_history), and the headline suffix-level safety theorem recent_certified_suffix_agreement (generic Signed) with its TS instantiation ts_recent_certified_suffix_agreement (Signed := TSSigned n sigOps). Uses the GLOBAL all-window budget ByzantineBounded, the recency-scoped SigUnforgeableRecent, SignedHashInjective, and no anchor of any kind. 622 lines, namespace MoltPetit.Model (line 49) ... end (line 622).

**Imports:** `MoltPetit.TS.Bridge`, `MoltPetit.Model.Liveness`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `GroundedHistory` | structure (Prop) | 113 | What a GroundedCert derivation reconstructs: a validChain-accepted prefix starting at G at index 0, whose tip matches the claim, whose filtered near-tip blocks are exactly cl.tail, of length tipHeight+1, every block genesis-or-Signed (genesis may be unsigned). |
| `linksOk_slots_gt` | private theorem (NOT importable) | 90 | Blocks after a linksOk head have strictly later slots; private, must be re-proved locally if a new module needs it (via strictSlots_of_checks (linksOk_isChain h) and List.pairwise_cons). |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `windowCount_append` | 55 | (a b : Chain) (u len : Nat) — no hypotheses | `windowCount (a ++ b) u len = windowCount a u len + windowCount b u len` | Public plumbing; simp [windowCount, List.filter_append]. |
| `windowCount_filter_low` | 61 | hlo : lo ≤ u; (c : Chain) (len : Nat) | `windowCount (c.filter fun x => decide (lo ≤ x.slot)) u len = windowCount c u len` | The key rewrite that lets density counted over cl.tail (= filtered prefix) equal density over the full prefix for windows starting at or above the tail bound. |
| `windowCount_append_high` | 77 | h : ∀ x ∈ later, u + len ≤ x.slot | `windowCount (l ++ later) u len = windowCount l u len` | Blocks at/after the window's right edge don't count. |
| `groundedCert_facts` | 103 | h : GroundedCert n Signed G cl | `genesisOk G = true ∧ G.slot = 0` | Read off the derivation root by induction. Used in recent_certified_suffix_agreement to get G.slot = 0 (hG0). |
| `groundedCert_history` | 129 | hn : 1 ≤ n; h : GroundedCert n Signed G cl | `∃ c : Chain, GroundedHistory n Signed G cl c` | Induction on the derivation; genesis case yields [G] (needs hn to discharge maturedWindowsDense n [G] G.slot via n = 1 ∧ u = 0); extend case appends b via validChain_append_one, using hist.tail_eq + windowCount_append + windowCount_filter_low to transfer the fold's tail-buffer density check to c ++ [b]. Implicit binders {n} {Signed : Block → Prop} {G : Block} {cl : CertClaim}. |
| `validChain_append_suffix` | 222 | hDense : ∀ u, u + n ≤ sTipSlot + 1 → quorum n ≤ windowCount full u n  (full, sTipSlot, n implicit, inferred from hDense); (suffix c : Chain) (t : Block) explicit; hfull : full = c ++ suffix; hValid : validChain n c = true; hTipEq : c.getLast? = some t; hLinks : linksOk (t :: suffix) = true; hSlots : ∀ x ∈ suffix, x.slot ≤ sTipSlot | `validChain n full = true` | Stated as ∀ (suffix c t), ... → ... (curried after hDense) because it is proved by induction on suffix; callers pass `rfl` for hfull. Intermediate windows count the same as in full by windowCount_append_high. |
| `grounded_suffix_history` | 269 | hn : 1 ≤ n; hG : GroundedCert n Signed G cl; hTipS : (s₁ :: srest).getLast? = some sTip; hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId; hLinks : linksOk (s₁ :: srest) = true; hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n | `∃ c : Chain, validChain n (c ++ s₁ :: srest) = true ∧ blockAt? (c ++ s₁ :: srest) 0 = some G ∧ c.length = cl.tipHeight + 1 ∧ (∀ B ∈ c, B = G ∨ Signed B)` | Grounded prefix + validated suffix = full accepted chain. The suffix hypotheses are exactly the triple ts_validateSuffix_sound (TS/Bridge.lean:506) returns. hDense uses Int casts; proof bridges to Nat with `by push_cast; omega`. Suffix signedness is NOT a hypothesis here; conclusion covers only the prefix c. |
| `recent_certified_suffix_agreement` | 371 | hn : 1 ≤ n; hBudget : ByzantineBounded n bad  — GLOBAL all-window budget (∀ u, (badSlotsIn bad u n).card ≤ maxByzantine n); bad : ByzantineSlots is a free implicit; hSig : SigUnforgeableRecent n bad Signed signed now Δ  (signed : SigningLog := Nat → Nat → Option Block; single field verified_was_signed over ValidChain n c, B ∈ c, ∃ t, c.getLast? = some t ∧ now ≤ t.slot + Δ, ¬ bad B.slot, Signed B ⟹ signed (producerForSlot n B.slot) B.slot = some B); hHash : SignedHashInjective Signed G; hcl : GroundedCert n Signed G cl; hcl' : GroundedCert n Signed G cl'  (SAME G); hTipS : (s₁ :: srest).getLast? = some sTip; hTipS' : (s₁' :: srest').getLast? = some sTip'; hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId; hLinks : linksOk (s₁ :: srest) = true; hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n; hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧ s₁'.prev = some cl'.tipId; hLinks' : linksOk (s₁' :: srest') = true; hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip'.slot + 1 → quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n; hSigned : ∀ B ∈ s₁ :: srest, Signed B; hSigned' : ∀ B ∈ s₁' :: srest', Signed B; hRecent : now ≤ sTip.slot + Δ; hRecent' : now ≤ sTip'.slot + Δ; hB : blockAt? (s₁ :: srest) i = some B; hB' : blockAt? (s₁' :: srest') i' = some B'; hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i'; hDeep : i + n < (s₁ :: srest).length; hDeep' : i' + n < (s₁' :: srest').length | `B = B'` | Implicit binders: {n : Nat} {bad : ByzantineSlots} {signed : SigningLog} {Signed : Block → Prop} {G : Block} {now Δ : Nat} {cl cl' : CertClaim} {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block} {i i' : Nat} {B B' : Block}. Signed predicate: fully generic. Budget: global ByzantineBounded, passed unchanged to deep_block_agreement_of_height_depth (Safety.lean:352). NO anchor, NO horizon, NO Δconf, NO floor. Proof: reconstructs both full chains via grounded_suffix_history; builds a SlotRecord `record := fun s => ((full ++ full').filter fun x => x.slot == s).toFinset` under `classical`; derives HonestSlotsUnique bad record from hSig.verified_was_signed (both chains recent) plus hAtZero (a slot-0 block of a StrictSlots chain headed by G is G, handling the unsigned genesis); IdInjective from hHash over `x = G ∨ Signed x`; ChainInRecord by construction; CommonPrefixUpTo full full' 0 from the two hHead facts (shared genesis at index 0 is load-bearing); global height of suffix index i is c.length + i = cl.tipHeight + 1 + i; closes with deep_block_agreement_of_height_depth hn hBudget hUniq hInj hVS hVS' hRec hRec' hGenesis hBfull hB'full hE hE' le_rfl le_rfl. |
| `ts_recent_certified_suffix_agreement` | 553 | hn : 1 ≤ n; hBudget : ByzantineBounded n bad  (global all-window); hSig : SigUnforgeableRecent n bad (TSSigned n sigOps) signed now Δ; hHash : SignedHashInjective (TSSigned n sigOps) G; hcl : GroundedCert n (TSSigned n sigOps) G cl; hcl' : GroundedCert n (TSSigned n sigOps) G cl'; hval : MoltPetit.validateSuffix n (toTSClaim cl) (toTSChain (s₁ :: srest)) = true; hval' : MoltPetit.validateSuffix n (toTSClaim cl') (toTSChain (s₁' :: srest')) = true; hSigned : ∀ B ∈ s₁ :: srest, TSSigned n sigOps B; hSigned' : ∀ B ∈ s₁' :: srest', TSSigned n sigOps B; hTipS : (s₁ :: srest).getLast? = some sTip; hTipS' : (s₁' :: srest').getLast? = some sTip'; hRecent : now ≤ sTip.slot + Δ; hRecent' : now ≤ sTip'.slot + Δ; hB : blockAt? (s₁ :: srest) i = some B; hB' : blockAt? (s₁' :: srest') i' = some B'; hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i'; hDeep : i + n < (s₁ :: srest).length; hDeep' : i' + n < (s₁' :: srest').length | `B = B'` | Implicit binders {n} {bad : ByzantineSlots} {signed : SigningLog} {sigOps : MoltPetit.SigOps} {G : Block} {now Δ : Nat} {cl cl'} {s₁ s₁'} {srest srest'} {sTip sTip'} {i i'} {B B'}. Note sigOps is the TS-emitted dictionary MoltPetit.SigOps (Emitted.lean:237), not the model-level MoltPetit.Model.SigOps σ sk pk. Signed := TSSigned n sigOps = ∃ sig, sigOps.verify (sigOps.keyFor (producerForSlot n B.slot) B.keyIndex) B.slot B.height (B.prev.map Int.ofNat) B.id sig = true (verification at the block's DECLARED keyIndex). Proof is a one-liner: recent_certified_suffix_agreement with (ts_validateSuffix_sound hTipS hval).1/.2.1/.2.2 supplying hLink/hLinks/hDense. Binder order differs from the generic theorem (hval/hSigned precede {sTip sTip'}/hTipS). Consumed by MoltPetit/TS/Results.lean (lines 111, 273) and mirrored by Rust/Results_rust.lean via recent_certified_suffix_agreement directly. |
| `linksOk_height_at` | 592 | hL : linksOk (x :: c) = true  (∀ {c : Chain} {x : Block}); hB : blockAt? (x :: c) i = some B  (∀ {i : Nat} {B : Block}) | `B.height = x.height + i` | Heights ascend by one along a linked segment. Used by TS/Results.lean and Rust/Results_rust.lean to convert the height-based headline forms into the index-based hypotheses of recent_certified_suffix_agreement. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingCert.lean

**Purpose:** Certificate wrapper for the index-pinned (key-rotation) validator: GroundedCertK threads a per-producer key floor fl : Nat → Nat through the fold and gates each fold on fl (producer b) ≤ b.keyIndex; groundedCertK_history / groundedCertK_suffix_history reconstruct a validChainK / validChainK' chain; keyMonoFrom is the suffix-side floor check; SignedDeclared + exists_signedChain_of_covered rebuild a sigsOk SignedChain from blockwise declared signatures; AttestedHistoryK packages the histories a certificate could attest; keyrot_recent_certified_suffix_agreement is the certificate-level light-client theorem under key theft with the GLOBAL budget quantified over attestable histories. 685 lines, namespace MoltPetit.Model (line 49) ... end (line 685).

**Imports:** `MoltPetit.Model.Grounded`, `MoltPetit.Results.KeyStealingResults`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `foldl_max_le` | private theorem (NOT importable) | 55 | Local copy of a KeyIndex.lean private helper (header comment: 'local copies; the KeyIndex.lean helpers are private'). |
| `le_foldl_max'` | private theorem (NOT importable) | 64 | Local copy; seed ≤ foldl max. |
| `mem_le_foldl_max'` | private theorem (NOT importable) | 71 | Local copy; member ≤ foldl max. |
| `pos_le_of_slot_le` | private theorem (NOT importable) | 106 | Positions of a strict-slots chain are ordered like slots (via strictSlots_lt). |
| `keyMonoFrom` | def | 159 | Suffix-side monotone check: fold the certificate's floor snapshot through the suffix, gating each block on floor(producer) ≤ keyIndex and bumping the producer's floor. The only rotation check a cert+suffix verifier can run. Bridged to TS keyMonoFromTs by MoltPetit/TS/BridgeK.lean ts_keyMonoFromTs. |
| `SignedDeclared` | def (Prop) | 234 | Block carries a verifying signature under its DECLARED registry version B.keyIndex (sigOk's content blockwise). Strictly stronger than KeyStealingSigned (∃ j). The Signed predicate of the keyrot certificate theorem. Re-exported as Molt.SignedDeclared (Molt/Rotation.lean:137). |
| `GroundedCertK` | inductive (Prop) | 315 | Certificate derivation for the index-pinned validator: GroundedCert's fold checks plus a threaded per-producer floor fl (constant-size: only indices < n read) gated by the monotone rule. Differs from GroundedCert in: genesis must itself be Signed (no genesis exemption), the extra fold premise fl (producer b) ≤ b.keyIndex, and the floor step. Re-exported as Molt.GroundedCertK (Molt/Rotation.lean:314). |
| `GroundedHistoryK` | structure (Prop) | 342 | What a GroundedCertK derivation reconstructs: validChainK (validChain && keyMonoOk) prefix, G at index 0, tip/tail/length matching the claim, EVERY block Signed (genesis included), and the floor snapshot equals keyFloor of the prefix pointwise. |
| `AttestedHistoryK` | def (Prop) | 541 | A full chain the certificate (claim with tipHeight, suffix) could be attesting: validChainK'-accepted, rooted at G, blockwise SignedDeclared, splitting as a (tipHeight+1)-block prefix followed by exactly the suffix. The domain over which the keyrot certificate theorem quantifies its budget. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `mem_keyIndex_le_floor` | 82 | (n : Nat) explicit; hB : B ∈ c | `B.keyIndex ≤ keyFloor n c (producerForSlot n B.slot)` | Membership form of block_keyIndex_le_floor. Also used by KeyStealingLongRange.lean:51. |
| `keyFloor_append_one` | 91 | (n : Nat) (c : Chain) (b : Block) (i : Nat) — no hypotheses | `keyFloor n (c ++ [b]) i = if producerForSlot n b.slot = i then max (keyFloor n c i) b.keyIndex else keyFloor n c i` | One-block floor evolution; exactly the floor step GroundedCertK.extend performs. |
| `inForcePinned_of_validChainK` | 122 | h : validChainK n c = true  ({n Δconf : Nat} {c : Chain} implicit; Δconf is free) | `inForcePinned n Δconf c = true` | The monotone rule implies the ≤-pin on a full chain for ANY Δconf. Axiom-guarded in Results/Axioms.lean:288. |
| `validChainK'_of_validChainK` | 145 | h : validChainK n c = true | `validChainK' n Δconf c = true` | Index-pinned validator from the monotone one (Δconf implicit and free). |
| `keyMonoFrom_ge` | 169 | hle : ∀ i, fl i ≤ fl' i; h : keyMonoFrom n fl' s = true | `∀ y ∈ s, fl (producerForSlot n y.slot) ≤ y.keyIndex` | Every suffix block clears any floor at-or-below the snapshot it was checked against. |
| `keyMonoFrom_pairwise` | 192 | h : keyMonoFrom n fl s = true | `s.Pairwise (fun a b => producerForSlot n a.slot = producerForSlot n b.slot → a.keyIndex ≤ b.keyIndex)` | Intra-suffix monotonicity from the suffix check. |
| `keyMonoOk_append_of_from` | 212 | hc : keyMonoOk n c = true; hs : keyMonoFrom n (keyFloor n c) s = true | `keyMonoOk n (c ++ s) = true` | Assembles the full-chain monotone rule from a monotone prefix plus a suffix checked against the prefix's floor. Uses keyMonoOk_iff_pairwise (KeyIndex.lean:136). Also used by KeyRotationLiveness.lean:91. Axiom-guarded (propext, Quot.sound). |
| `keyStealingSigned_of_declared` | 239 | h : SignedDeclared n ops registry B | `KeyStealingSigned n ops registry B` | SignedDeclared → KeyStealingSigned (witness j := B.keyIndex). KeyStealingSigned is in Results/KeyStealingResults.lean:158. |
| `exists_signedChain_of_covered` | 247 | h : ∀ B ∈ c, SignedDeclared n ops registry B  ({Sig sk pk : Type} {n} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {c : Chain}) | `∃ sc : SignedChain Sig, stripSigs sc = c ∧ sigsOk n ops registry sc = true` | Blockwise declared coverage reconstructs a signed chain passing sigsOk. Callers must supply (Sig := Sig) explicitly (see line 629). Axiom-guarded (propext only). Also used by KeyStealingScheduleCert.lean:661. |
| `keyMonoFrom_congr` | 263 | hfg : ∀ i, f i = g i | `∀ s : Chain, keyMonoFrom n f s = keyMonoFrom n g s` | keyMonoFrom reads the floor only pointwise; used to swap fl for keyFloor n c via hist.floors. |
| `keyMonoFrom_congr_lt` | 280 | hn : 1 ≤ n; hfg : ∀ i, i < n → f i = g i | `∀ s : Chain, keyMonoFrom n f s = keyMonoFrom n g s` | Only producer indices < n are ever read (producerForSlot n s = s % n < n), so the wire floor is an n-vector. Used by TS/BridgeK.lean. Axiom-free. |
| `groundedCertK_history` | 355 | hn : 1 ≤ n; h : GroundedCertK n Signed G cl fl  ({n} {Signed} {G} {cl : CertClaim} {fl : Nat → Nat} implicit) | `∃ c : Chain, GroundedHistoryK n Signed G cl fl c` | Mirror of groundedCert_history plus keyMonoOk maintenance (validChainK) via keyMonoOk_append_of_from with the one-block keyMonoFrom check discharged by hist.floors ▸ hKI, and floor bookkeeping via keyFloor_append_one. Genesis case: floors of [G] computed by unfolding keyFloor. Axiom-guarded in Results/Axioms.lean:297. |
| `groundedCertK_suffix_history` | 462 | (Δconf : Nat) EXPLICIT first argument; hn : 1 ≤ n; hG : GroundedCertK n Signed G cl fl; hTipS : (s₁ :: srest).getLast? = some sTip; hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId; hLinks : linksOk (s₁ :: srest) = true; hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n; hMono : keyMonoFrom n fl (s₁ :: srest) = true; hSigned : ∀ B ∈ s₁ :: srest, Signed B | `∃ c : Chain, validChainK' n Δconf (c ++ s₁ :: srest) = true ∧ blockAt? (c ++ s₁ :: srest) 0 = some G ∧ c.length = cl.tipHeight + 1 ∧ (∀ B ∈ c ++ s₁ :: srest, Signed B)` | Grounded-K prefix + validated suffix = full validChainK'-accepted chain, every block Signed (prefix AND suffix, unlike grounded_suffix_history). fl consumed: hist.floors rewrites keyMonoFrom n fl → keyMonoFrom n (keyFloor n c) (keyMonoFrom_congr), then keyMonoOk_append_of_from; the pin comes free from validChainK'_of_validChainK. Δconf does not constrain anything here (any value works). Axiom-guarded in Results/Axioms.lean:300. |
| `keyrot_recent_certified_suffix_agreement` | 583 | hn : 1 ≤ n  ({n Δconf : Nat} implicit); hΔ : n ≤ Δconf; hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ  ({Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}); hHash : SignedHashInjective (SignedDeclared n ops registry) G; hcl : GroundedCertK n (SignedDeclared n ops registry) G cl fl  ({cl cl' : CertClaim} {fl fl' : Nat → Nat}); hcl' : GroundedCertK n (SignedDeclared n ops registry) G cl' fl'  (SAME G); hTipS : (s₁ :: srest).getLast? = some sTip; hTipS' : (s₁' :: srest').getLast? = some sTip'; hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId; hLinks : linksOk (s₁ :: srest) = true; hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n; hMono : keyMonoFrom n fl (s₁ :: srest) = true; hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B; hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧ s₁'.prev = some cl'.tipId; hLinks' : linksOk (s₁' :: srest') = true; hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip'.slot + 1 → quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n; hMono' : keyMonoFrom n fl' (s₁' :: srest') = true; hSigned' : ∀ B ∈ s₁' :: srest', SignedDeclared n ops registry B; hRecent : now ≤ sTip.slot + Δ; hRecent' : now ≤ sTip'.slot + Δ; hBudget : ∀ c : Chain, AttestedHistoryK n Δconf ops registry G cl.tipHeight (s₁ :: srest) c → ByzantineBounded n (badKeyrotOn n Δconf rented Stolen c)  — GLOBAL all-window ByzantineBounded, quantified over attestable histories of the FIRST (cl, s₁ :: srest) pair only; hB : blockAt? (s₁ :: srest) i = some B  ({i i' : Nat} {B B' : Block}); hB' : blockAt? (s₁' :: srest') i' = some B'; hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i'; hDeep : i + n < (s₁ :: srest).length; hDeep' : i' + n < (s₁' :: srest').length | `B = B'` | Signed predicate is SignedDeclared n ops registry throughout (GroundedCertK, hSigned, hHash); KeyStealingEUFCMA is separate and stated over validSignedChainK' SignedChains at arbitrary registered version j. Budget: ByzantineBounded (global; NOT ByzantineBoundedFrom) on badKeyrotOn read off the reconstructed FIRST chain: hBud := hBudget _ ⟨hK, hHead, hCov, c, rfl, hLen⟩ instantiated once at c ++ s₁ :: srest = stripSigs sc; the second chain's history never enters the budget (matches keyrot_deep_block_agreement_of_length's hBudget over stripSigs sc). NO anchor / H-ANCHOR / horizon hypothesis anywhere. fl / fl': consumed only via hcl/hMono (resp. hcl'/hMono') inside groundedCertK_suffix_history; never enter hBudget or hEUF. Proof: two groundedCertK_suffix_history calls (Δconf explicit); exists_signedChain_of_covered (Sig := Sig) materialises sc/sc' with sigsOk; validSignedChainK' assembled by rw + ⟨hsigs, hK⟩; hRecent repackaged as ⟨sTip, hfullTip, hRecent⟩ with (c ++ s₁ :: srest).getLast? = some sTip via List.getLast?_append; CommonPrefixUpTo (stripSigs sc) (stripSigs sc') 0 from the two hHead; hSig : ∀ b ∈ stripSigs sc, b = G ∨ SignedDeclared … b (Or.inr always); closes with keyrot_deep_block_agreement_of_length hn hΔ hEUF hHash hBud hVal hVal' hSig hSig' ⟨…⟩ ⟨…⟩ hGenesis (k := c.length + i) … with hLen goals by rw [hstrip, List.length_append]; omega. Aliased as Molt.keyrot_recent_certified_suffix_agreement (Molt/Rotation.lean:308) and axiom-guarded in Results/Axioms.lean:303 and Molt/Axioms.lean:107. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/Definitions.lean

**Purpose:** CONTEXT ONLY (cited ranges read, not the full file): the imported definitions the two mapped files consume. GroundedCert itself lives here, not in Grounded.lean.

**Imports:** (none listed)

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `CertClaim` | structure | 322 | What a certificate claims: tip (id, slot, height) plus the near-tip boundary buffer tail (≤ n-1 stripped prefix blocks with slot ≥ tipSlot + 2 - n). |
| `blockAt?` | def | 462 | List indexing; 'height' in the safety theorems is list index. |
| `StrictSlots` | def (Prop) | 469 | Slots strictly increase. |
| `ValidChain` | def (Prop) | 490 | Semantic validity; .2.1 is StrictSlots, .2.2.2 is MaturedWindowsDense (∀ m D, blockAt? c m = some D → ∀ u, u + n ≤ D.slot + 1 → quorum n ≤ windowCount c u n). |
| `ChainInRecord / HonestSlotsUnique / IdInjective` | def (Prop) | 494 | Record-level predicates (lines 494, 498, 503) that recent_certified_suffix_agreement derives before calling deep_block_agreement_of_height_depth. SlotRecord := Nat → Finset Block (line 456); ByzantineSlots := Nat → Prop (line 459). |
| `ByzantineBounded` | def (Prop) | 513 | The GLOBAL all-window budget: every n-window [u, u+n) has at most ⌊(n-1)/3⌋ bad slots (maxByzantine n := (n - 1) / 3, line 47; badSlotsIn noncomputable, line 509, needs Classical). This is the budget both mapped headline theorems use. rfl-equal to Molt.FaultBounded. |
| `CommonPrefixUpTo` | def (Prop) | 517 | Shared prefix; the headline theorems only ever need it at h = 0 (shared genesis). |
| `SigningLog` | abbrev | 558 | Honest signing log: signed i s = some B iff participant i signed exactly B for slot s. |
| `toTSChain / toTSClaim` | def | 568 | Injections of model chain/claim into the TS-emitted representation (Nat fields cast to Int). |
| `TSSigned` | def (Prop) | 597 | The TS per-block signature predicate at the block's declared keyIndex; the Signed of ts_recent_certified_suffix_agreement. |
| `GroundedCert` | inductive (Prop) | 627 | The plain certificate derivation (no floor). Genesis need NOT be Signed. Fold density check is Nat-form over cl.tail ++ [b]. Re-exported as Molt.GroundedCert (Molt/Assumptions.lean:59). |
| `SignedHashInjective` | def (Prop) | 656 | Collision resistance over genesis-or-Signed blocks. Molt.SignedHashInjective is a fresh rfl-equal copy. |
| `SigUnforgeableRecent` | structure (Prop) | 677 | Recency-scoped EUF-CMA + honest signing discipline; the crypto surface of recent_certified_suffix_agreement. Re-exported as Molt.SigUnforgeableRecent. |

### Theorems

(none)

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingUnique.lean

**Purpose:** CONTEXT ONLY (lines 100-190 read): the key-stealing EUF-CMA surface consumed by keyrot_recent_certified_suffix_agreement.

**Imports:** (none listed)

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `KeyStealingEUFCMA` | structure (Prop) | 136 | Recency-scoped registry-level EUF-CMA at an arbitrary registered version j, over validSignedChainK' SignedChains (not over a bare Signed predicate). Assumed, not derived (docstring: 'taken as a named primitive'). Re-exported as Molt.KeyStealingEUFCMA. |

### Theorems

(none)

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealing.lean

**Purpose:** CONTEXT ONLY (lines 20-75 read): the chain-dependent corruption predicate the keyrot budget is stated over.

**Imports:** (none listed)

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `badKeyrotOn` | def (Prop) | 47 | Slot s is bad if rented or some not-yet-rotated-out version (≥ in-force index read off witness chain c₀'s confirmed prefix) is stolen. Chain-dependent — this is why the certificate theorem must quantify the budget over AttestedHistoryK. Docstring line 63 names 'the gap that H-ANCHOR exists to close'. rfl-equal to Molt.badKeyrot. |

### Theorems

(none)

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/KeyStealingScheduleHorizon.lean

**Purpose:** CONTEXT ONLY (lines 55-95 read): the trailing/horizon-scoped budget variant, which does NOT appear in either mapped file.

**Imports:** (none listed)

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `ByzantineBoundedFrom` | def (Prop) | 70 | Budget required only of windows starting at or after horizon H. Only used by the scheduled-rotation path (sched_* theorems). Grep confirms zero occurrences in Grounded.lean and KeyStealingCert.lean. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `byzantineBoundedFrom_of_bounded` | 75 | h : ByzantineBounded n bad | `ByzantineBoundedFrom H n bad` | Global budget delivers every horizon budget; the direction a trailing/anchored variant of the mapped theorems would need to invert or bypass. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Results/KeyStealingResults.lean

**Purpose:** CONTEXT ONLY (lines 20-50, 150-175, 225-300 read): the full-chain consumer of keyrot_recent_certified_suffix_agreement and the KeyStealingSigned domain.

**Imports:** (none listed)

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `KeyStealingSigned` | def (Prop) | 158 | Existentially-versioned signed predicate of the full-chain keyrot theorems; SignedDeclared is the strictly stronger declared-version form. |

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `keyrot_deep_block_agreement_of_length` | 250 | hn : 1 ≤ n; hΔ : n ≤ Δconf; hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ; hHash : SignedHashInjective Signed G  (generic Signed); hBudget : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc))  — global budget read off the FIRST chain; hVal : validSignedChainK' n Δconf ops registry sc = true; hVal' : validSignedChainK' n Δconf ops registry sc' = true; hSig : ∀ B ∈ stripSigs sc, B = G ∨ Signed B; hSig' : ∀ B ∈ stripSigs sc', B = G ∨ Signed B; hRecent : ∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ; hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ; hGenesis : CommonPrefixUpTo (stripSigs sc) (stripSigs sc') 0; hB : blockAt? (stripSigs sc) k = some B; hB' : blockAt? (stripSigs sc') k = some B'; hLen : k + n < (stripSigs sc).length; hLen' : k + n < (stripSigs sc').length | `B = B'` | The exact consumer keyrot_recent_certified_suffix_agreement closes with. Internally uses honestSlotsUnique_keyrot_horizon (KeyStealingHorizonCore.lean) and deep_block_agreement_of_height_depth. |

## /etheron-pod/mini-consensus-lean/MoltPetit/Model/Safety.lean

**Purpose:** CONTEXT ONLY (lines 335-380 read): the record-level consumer of recent_certified_suffix_agreement.

**Imports:** (none listed)

### Defs

(none)

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `deep_block_agreement_of_height_depth` | 352 | hn : 1 ≤ n; hBudget : ByzantineBounded n bad; hHonest : HonestSlotsUnique bad record; hId : IdInjective record; hValid : ValidChain n c; hValid' : ValidChain n c'; hRec : ChainInRecord record c; hRec' : ChainInRecord record c'; hGenesis : CommonPrefixUpTo c c' 0; hB : blockAt? c k = some B; hB' : blockAt? c' k = some B'; hD : blockAt? c m = some D; hD' : blockAt? c' m' = some D'; hDeep : k + n ≤ m; hDeep' : k + n ≤ m' | `B = B'` | Global-budget, record-based deep agreement; the mapped Grounded.lean theorem builds record/hHonest/hId itself. |

## /etheron-pod/mini-consensus-lean/MoltPetit/TS/Bridge.lean

**Purpose:** CONTEXT ONLY (lines 478-530 read): the TS soundness lemma whose output triple is the suffix hypothesis shape of every mapped theorem.

**Imports:** (none listed)

### Defs

(none)

### Theorems

| name | line | hypotheses | conclusion | notes |
|---|---|---|---|---|
| `ts_validateSuffix_sound` | 506 | hTip : (s₁ :: srest).getLast? = some sTip; h : MoltPetit.validateSuffix n (toTSClaim cl) (toTSChain (s₁ :: srest)) = true | `(s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId) ∧ linksOk (s₁ :: srest) = true ∧ (∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)` | Source of the Int-cast hDense shape. Docstring at 488-490: the certificate-boundary floor form 'awaits the claim-format extension; see GroundedCertK'. |

## /etheron-pod/mini-consensus-lean/Molt/Rotation.lean

**Purpose:** CONTEXT ONLY (lines 95-145, 180-215, 295-420 read): the paper-facing re-presentation of the keyrot certificate theorem.

**Imports:** `MoltPetit.Model.KeyStealingCert (line 6)`

### Defs

| name | kind | line | meaning |
|---|---|---|---|
| `Molt.keyrot_recent_certified_suffix_agreement` | alias | 308 | Docstring (303-307): 'Mode 1's certificate-level safety ... under the global, all-window budget (the anchored, trailing-window form is future work at this presentation).' |
| `Molt.GroundedCertK` | abbrev | 314 | Re-export; docstring: 'the certificate must attest claim and floor together (paper §6.3)'. |
| `Molt.SignedDeclared / Molt.KeyStealingEUFCMA / Molt.badKeyrot` | abbrev / def + rfl bridge | 137 | The Molt bridging idiom: abbrev for Prop-structures/inductives, fresh defs for validators/predicates with *_eq_core rfl/funext lemmas, and wrappers doing `rw [validSignedChainK'_eq_core] at hVal hVal'; exact MoltPetit.Model.<core> ...`. |

### Theorems

(none)

## reuse_notes

IMPORTS FOR A NEW ADDITIVE MODULE. `import MoltPetit.Model.KeyStealingCert` transitively brings Grounded, TS.Bridge, Liveness, Results.KeyStealingResults (hence KeyStealingUnique, KeyStealingHorizonCore, KeyRotation, KeyIndex, KeyStealing, Safety, Soundness, Model, Definitions). Add `import MoltPetit.TS.BridgeK` for the TS floor bridge (ts_keyMonoFromTs, ts_validateSuffixK_sound). For a Molt/-side re-presentation import `Molt.Rotation` (already imports KeyStealingCert). Both mapped files open `namespace MoltPetit.Model` and close with `end MoltPetit.Model`; every name is MoltPetit.Model.* and is referenced unqualified inside that namespace; TS-emitted names are qualified `MoltPetit.validateSuffix`, `MoltPetit.SigOps`, `MoltPetit.keyMonoFromTs` (distinct from the model-level `SigOps σ sk pk` structure in Definitions.lean:187 — inside MoltPetit.Model bare `SigOps` is the model one).

BUILD GOTCHA (no-edit constraint). lakefile.toml declares `[[lean_lib]] name = "MoltPetit"` with no `globs`, so `lake build` compiles only modules reachable from MoltPetit.lean's import list. A new file that may not edit existing files must be built explicitly (`lake build MoltPetit.Model.<NewName>`) and will not be covered by the `#guard_msgs in #print axioms` ledger in MoltPetit/Results/Axioms.lean (lines 288-305 guard the KeyStealingCert theorems) or Molt/Axioms.lean:107-113 unless it carries its own guards. Lean options: `relaxedAutoImplicit = false` (bind every variable explicitly), mathlib standard linter set on, toolchain leanprover/lean4:v4.30.0-rc2, mathlib v4.30.0-rc2.

IDIOMS TO FOLLOW. (1) Certificate derivations are `inductive X (n : Nat) (Signed : Block → Prop) (G : Block) : CertClaim → … → Prop` with `genesis`/`extend` constructors whose result claims are record literals `{ tipId := b.id, tipSlot := b.slot, tipHeight := b.height, tail := (cl.tail ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot) }` and whose density premise is Nat-form `∀ u, cl.tipSlot + 2 ≤ u + n → u + n ≤ b.slot + 1 → quorum n ≤ windowCount (cl.tail ++ [b]) u n`. Any new variant must keep exactly this tail shape or the standard rewrite `rw [windowCount_append, windowCount_append, hist.tail_eq, windowCount_filter_low (by omega)]` and the tail re-filtering step (`List.filter_append, List.filter_filter, List.filter_congr`) will not transfer. (2) Reconstruction results are `structure GroundedHistory(K) … : Prop where` with named fields consumed as `hist.valid/head/tip/tail_eq/len_eq/signed/floors`, built by `refine ⟨c ++ [b], ?_, ?_, ⟨b, by simp, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩`; the extend step goes through `validChain_append_one hValid hTipEq hChild hAllDense` (Liveness.lean:123; hAllDense : ∀ u, u + n ≤ b.slot + 1 → windowDense n (c ++ [b]) u = true) with `hMat := (validChain_sound hist.valid).2.2.2` and `hTipAt := blockAt_getLast hTipEq` for old windows and the fold's tail check for newly matured ones; the K variant additionally does `keyMonoOk_append_of_from hcM (by rw [keyMonoFrom, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by rw [hist.floors]; exact hKI, rfl⟩)` and `keyFloor_append_one` for floors. (3) Suffix attachment: `validChain_append_suffix hFullDense (s₁ :: srest) c t rfl hist.valid hTipEq hLinksT hSlotsLe` with hLinksT built by `rw [show linksOk (t :: s₁ :: srest) = (childOk t s₁ && linksOk (s₁ :: srest)) from rfl, Bool.and_eq_true]` and `hSlotsLe` from `slot_le_tip_of_mem (strictSlots_of_checks (linksOk_isChain hLinks)) hTipS`. (4) Assumption bundles are single-field `structure … : Prop where` (SigUnforgeableRecent.verified_was_signed, KeyStealingEUFCMA.unforgeable); the Molt/ layer re-exports them with `abbrev X := @MoltPetit.Model.X`, restates plain predicates fresh with `theorem x_eq_core : X = MoltPetit.Model.X := rfl` (FaultBounded = ByzantineBounded, SignedHashInjective, badKeyrot = badKeyrotOn), proves validator equalities by `funext …; simp only […_eq_core]`, and transports theorems either by `alias` (keyrot_recent_certified_suffix_agreement) or by restating with Molt vocabulary and `rw [linksOk_eq_core] at hLinks hLinks'; exact MoltPetit.Model.recent_certified_suffix_agreement …` (Molt/Results.lean:54 light_client_safety). (5) Private helpers cannot be imported: linksOk_slots_gt (Grounded.lean:90), foldl_max_le / le_foldl_max' / mem_le_foldl_max' / pos_le_of_slot_le (KeyStealingCert.lean:55-114). KeyStealingCert.lean itself re-copied KeyIndex.lean's private foldl-max helpers ('local copies; the KeyIndex.lean helpers are private') — copying privately is the accepted idiom.

EXACT CONSUMPTION FACTS. Budget: both headline theorems consume the GLOBAL all-window `ByzantineBounded n bad` (Definitions.lean:513, ∀ u over every window); `ByzantineBoundedFrom` (trailing/horizon) and any anchor/H-ANCHOR/trailing-window hypothesis appear NOWHERE in either file (grep 'anchor' = 0 hits in both). In recent_certified_suffix_agreement hBudget is passed verbatim to deep_block_agreement_of_height_depth. In keyrot_recent_certified_suffix_agreement the budget is `∀ c, AttestedHistoryK n Δconf ops registry G cl.tipHeight (s₁ :: srest) c → ByzantineBounded n (badKeyrotOn n Δconf rented Stolen c)`, quantified over histories of the FIRST certificate/suffix only and instantiated exactly once at the reconstructed first chain `c ++ s₁ :: srest` (= stripSigs sc), because keyrot_deep_block_agreement_of_length reads badKeyrotOn off `stripSigs sc`; the second chain never enters the budget. Signed predicate: recent_certified_suffix_agreement is generic in Signed with SigUnforgeableRecent n bad Signed signed now Δ; ts_ fixes Signed := TSSigned n sigOps (TS dictionary, verification at declared B.keyIndex via sigOps.keyFor); keyrot fixes Signed := SignedDeclared n ops registry (verification under registry (producerForSlot n B.slot) B.keyIndex — the DECLARED version) uniformly in GroundedCertK, hSigned/hSigned' and SignedHashInjective, then feeds `∀ b ∈ stripSigs sc, b = G ∨ SignedDeclared … b` to the Signed-generic keyrot_deep_block_agreement_of_length; the EUF-CMA surface (KeyStealingEUFCMA) is at arbitrary registered j over validSignedChainK' SignedChains, connected via exists_signedChain_of_covered (Sig := Sig) which rebuilds sigsOk from blockwise SignedDeclared. Floor snapshot fl: consumed only through `hcl : GroundedCertK … cl fl` and `hMono : keyMonoFrom n fl (s₁ :: srest) = true` (likewise fl'/hcl'/hMono'); groundedCertK_history yields `hist.floors : ∀ i, keyFloor n c i = fl i`, groundedCertK_suffix_history rewrites `keyMonoFrom_congr hist.floors` and closes with keyMonoOk_append_of_from; fl is never read at indices ≥ n (keyMonoFrom_congr_lt), never enters hBudget or hEUF, and the docstring makes (cl, fl) joint authentication a MANDATORY wire contract. Genesis: GroundedCert.genesis needs genesisOk G = true ∧ G.slot = 0; GroundedCertK.genesis additionally needs Signed G. Every reconstruction returns `blockAt? (c ++ suffix) 0 = some G` (position 0), used to build `CommonPrefixUpTo … 0` — both certificates must be grounded in the SAME G; in the plain theorem the possibly-unsigned genesis is handled by the local hAtZero argument (a slot-0 block of a StrictSlots chain headed by G is G) using groundedCert_facts for G.slot = 0. hn : 1 ≤ n is required by every reconstruction (genesis maturedWindowsDense case); keyrot also needs hΔ : n ≤ Δconf; Δconf is an EXPLICIT first argument of groundedCertK_suffix_history but implicit in the keyrot theorem. Density hypotheses on suffixes are the Int-cast shape `(cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n` exactly as ts_validateSuffix_sound emits (bridge with `by push_cast; omega`); all density is counted over cl.tail ++ suffix, never over the reconstructed prefix. Recency is `now ≤ sTip.slot + Δ` on each suffix tip, repackaged as `⟨sTip, hfullTip, hRecent⟩` where `(c ++ s₁ :: srest).getLast? = some sTip` via `rw [List.getLast?_append, hTipS]; rfl`. Height convention: global height of suffix index i is cl.tipHeight + 1 + i = c.length + i (hLen : c.length = cl.tipHeight + 1); hDeep : i + n < suffix.length; linksOk_height_at converts height-based statements. A trailing/anchored variant of these theorems would have to replace the two consumers (deep_block_agreement_of_height_depth; keyrot_deep_block_agreement_of_length) with horizon-budget analogues — the existing model for that is the scheduled path in KeyStealingScheduleHorizon.lean (ByzantineBoundedFrom, no hHead/anchor) — and Molt/Rotation.lean:303-307 already records the anchored/trailing-window certificate form as future work.

## open_items_found

- Grounded.lean:327-331 — section header '-- Cryptographic assumptions, signature level' with no declarations under it (the assumptions now live in Definitions.lean §6); dead section.
- Grounded.lean:368-369 (docstring of recent_certified_suffix_agreement) — '`ts_certified_suffix_agreement` recovers the unscoped form (`now := 0` accepts every chain).' No declaration named ts_certified_suffix_agreement exists anywhere in the repo (grep finds only this docstring mention); dangling reference.
- Grounded.lean:45-46 (header) — 'The proof-bearing theorem here is `ts_recent_certified_suffix_agreement`; the headline light-client results built on it live in `Results/Results.lean`.' (pointer, not an open item, but signals where consumers live).
- KeyStealingCert.lean:13-18 (header) — 'gates each fold on the monotone rule `fl (producer b) ≤ b.keyIndex`. This is exactly what a recursive circuit can check per fold; no history is consulted.' — informal modelling justification of the circuit claim, not formalized.
- KeyStealingCert.lean:41-46 (header, 'Honest accounting') — 'The corruption budget cannot be stated over verifier-visible data (it quantifies over the whole execution), so it is assumed over **every history the certificate could be attesting** (`AttestedHistoryK`): "whatever the attested history was, the induced rent+theft corruption respects the 1/3 budget". In a real execution the certificate attests the one real history, so this is the natural reading of P2-A at the certificate level.'
- KeyStealingCert.lean:533-540 (AttestedHistoryK docstring) — 'The corruption budget of the certificate-level theorem is assumed over *every* such history (in a real execution the certificate attests the one real history; quantifying over all of them is the honest way to state an execution-level assumption from verifier-level data, and only ever *strengthens* the hypothesis).' — the budget remains a named, non-verifier-checkable assumption.
- KeyStealingCert.lean:562-566 — '`fl` is a `Nat → Nat` in the model, but only the `n` producer indices are ever read — `producerForSlot n s < n` — so the wire encoding is an `n`-vector.' (model/wire gap noted informally; formal bridge is TS/BridgeK.lean).
- KeyStealingCert.lean:568-582 ('Wire contract (MANDATORY for any instantiation — read before deploying)') — 'a TS-level certificate-unforgeability hypothesis must read `∀ hc, verify hc = true → ∃ cl fl, claim hc = cl ∧ floors hc = fl ∧ GroundedCertK n Signed G cl fl` (note the plain path's `hUnf` attests only `cl`; a naive port would leave `fl` unauthenticated). Feeding `keyMonoFrom` an **unauthenticated** floor is a real attack, not a formality'. This TS-level hypothesis and a fully TS-level corollary are NOT present in these files; MoltPetit/TS/BridgeK.lean:24-28 confirms: 'The remaining glue for a fully TS-level corollary is the certificate attestation shape'.
- KeyStealingCert.lean:34-39 — 'The name reserved by `KeyStealingResults.lean` is honoured here: this is the constant-blocks-download form.' (reservation closed; KeyStealingResults.lean:29-39 says 'seam (i) below is CLOSED').
- CROSS-FILE, about the mapped theorems: Molt/Rotation.lean:303-307 (docstring of alias keyrot_recent_certified_suffix_agreement) — 'under the global, all-window budget (the anchored, trailing-window form is future work at this presentation).'
- CROSS-FILE: MoltPetit/TS/Bridge.lean:488-490 and MoltPetit/Results/Axioms.lean:306-310 — 'The certificate-boundary form — a suffix checked against a claim-carried floor snapshot — awaits the claim-format extension; see `GroundedCertK`.'
- CROSS-FILE: MoltPetit/Results/KeyStealingResults.lean:40-46 — seam (ii) '(ii) the Role-B long-range / old-key-fork exclusion from the weak-subjectivity anchor `H-ANCHOR` (increment I4), which is what makes the strong-model story honest beyond the confirmed/recent zone and is **not** derivable from uniqueness. ... long-range old-key forks are excluded only by the named `H-ANCHOR` seam, not proved here.'
- CROSS-FILE: MoltPetit/Results/KeyStealingResults.lean:21-23 — P2-A 'the induced Byzantine budget `ByzantineBounded n (badKeyrotOn …)` — a named hypothesis here (its rent-budget + per-window-theft-rate justification is off the light-client critical path; see `PHASE2_DESIGN.md` increment I3)'.
- CROSS-FILE: MoltPetit/Model/KeyStealing.lean:60-63 (badKeyrotOn_lossOnly docstring) — 'a from-genesis fork (whose floor never advances) is judged by a *different* predicate than the real chain — the gap that `H-ANCHOR` exists to close.'
