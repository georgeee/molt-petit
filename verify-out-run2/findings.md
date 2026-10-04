NOT READY: The manuscript is not ready for submission because multiple major discrepancies and overclaims between the paper's theorem statements/prose and the mechanized Lean proofs remain unaddressed.

## Automated Check Results

| Check | Result | Details |
|---|---|---|
| Lean Build (`lake build`) | PASS | Exit code 0 |
| TeX Build (`paper/build.sh`) | PASS | Exit code 0 |
| Lean Proof Sorries / Admits | PASS | 3 occurrences in comments/docs (0 in proofs) |
| Custom Lean Axiom Declarations | PASS | 0 custom axioms (standard Lean axioms only) |
| LaTeX Warning Lines | PASS | 1 warning (rerunfilecheck) |
| Lake Command | - | `nix-run /home/etheron-bare-exec/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake` |

---

## Findings

### BLOCKER

None.

### MAJOR

#### [F-01] Claim C1 (TeX lines 61--65)
- **TeX Line(s)**: 61--65
- **Lean Declaration**: None (external trust / conceptual)
- **What is wrong**: The abstract asserts without qualification that 'All safety claims are machine-checked in Lean 4' and that the verified Rust source serves as the recursive-proof circuit. However, Lean does not verify the Plonky2 recursive circuit backend arithmetic faithfulness (Rust/Equiv.lean explicitly notes that circuit backend faithfulness is an external trust assumption, not a theorem). Cryptographic unforgeability and hash collision resistance are also assumed rather than reduced to standard hard problems.
- **Fix**: Qualify in the abstract that safety theorems hold under standard cryptographic and synchrony assumptions and that circuit backend equivalence is an external trust assumption.

#### [F-02] Claim C2 (TeX lines 84--87)
- **TeX Line(s)**: 84--87
- **Lean Declaration**: `Rust.rust_recent_tip_ancestor_mem`
- **What is wrong**: The prose claims 'If the certificate verifies and its tip is recent, the client may act on everything n blocks deep --- and that guarantee is a machine-checked theorem about the shipped validator code, not a design argument.' This implies full prefix agreement for the entire chain up to depth n. Lean's theorem only proves agreement for the single ancestor block at index length - 1 - n in the suffix, and requires extensive undisclosed hypotheses: Byzantine fault budget (ByzantineBounded), cryptographic unforgeability (SigUnforgeableRecent), hash injectivity (SignedHashInjective), certificate grounding (GroundedCert), and competing suffix overlap ((toModelBlock sr1').height + n <= sTip.height).
- **Fix**: State that the guarantee holds subject to Byzantine fault bounds, cryptographic unforgeability/grounding, and competing suffix overlap.

#### [F-03] Claim C3 (TeX lines 119--127)
- **TeX Line(s)**: 119--127
- **Lean Declaration**: `Rust.rust_valid_chain_sound, Rust.rust_valid_chain_k_sound, Rust.rust_recent_tip_ancestor_mem`
- **What is wrong**: The assertion that 'the same source is re-used as the recursive-proof circuit, so the prover proves the predicate that was verified' implies verified compilation or equivalence to circuit gates. While the Rust and TypeScript software validators are proved sound against MoltPetit.Model.ValidChain, the circuit implementation is not verified in Lean; Plonky2 constraint backend faithfulness is an external audit assumption.
- **Fix**: Clarify that the recursive-proof circuit reuses the backend-generic Rust source, but that circuit backend faithfulness is an external audit assumption rather than a Lean-verified equivalence.

#### [F-04] Claim C4 (TeX lines 174--178)
- **TeX Line(s)**: 174--178
- **Lean Declaration**: `Molt.liveness_produce_blockK`
- **What is wrong**: The prose presents liveness_produce_blockK as proving dynamic protocol recovery from key loss ('The loser recovers by its mode's own discipline...'). Lean's theorem only proves a local single-block production step: if an eligible producer whose slot has arrived chooses keyIndex >= keyFloor and quorum density is already satisfied across missed slots (HonestBlocksCover), produceBlock? produces a block passing validChainK'. It takes continued density coverage as a hypothesis rather than proving dynamic recovery.
- **Fix**: Clarify that liveness_produce_blockK is a local single-block production lemma that takes continued density coverage as a hypothesis, not a dynamic protocol recovery theorem.

#### [F-05] Claim C7 (TeX lines 231--232)
- **TeX Line(s)**: 231--232
- **Lean Declaration**: `Molt.lockstep_recent_certified_suffix_agreement`
- **What is wrong**: The prose broadly asserts that '(Mode 3's guarantees hold at the certificate presentation as well as for full chains (lockstep_recent_certified_suffix_agreement))'. In Lean, lockstep_recent_certified_suffix_agreement only proves single-block agreement at matching height at depth >= n within suffixes extending grounded certificates rooted at a shared genesis under the cumulative fault package. It does not establish the full battery of Mode 3 guarantees for arbitrary certificate presentations.
- **Fix**: Clarify that certificate presentation guarantees apply to blocks confirmed at depth >= n within suffixes extending grounded certificates rooted at a shared genesis under the Mode 3 lockstep cumulative package.

#### [F-06] Claim C39 (TeX lines 616--620)
- **TeX Line(s)**: 616--620
- **Lean Declaration**: `Molt.sigUnforgeableRecent_of_timed`
- **What is wrong**: The paper states that in the timed model 'recency scoping of Assumption 1 stops being an assumption and becomes a theorem (a separate derivation, sigUnforgeableRecent_of_timed)'. In Lean, sigUnforgeableRecent_of_timed requires NoBackdate bad log (which is logically independent of TimedExecution), and recency is unused/slack in the proof rather than deduced from real-time delay.
- **Fix**: Clarify that recency-scoped unforgeability is derived by assuming NoBackdate (forward-secure custody) in addition to the timed model, which renders recency slack rather than deducing it from real-time delay.

#### [F-07] Claim C81 (TeX lines 1166--1168)
- **TeX Line(s)**: 1166--1168
- **Lean Declaration**: `Molt.lockstep_client_safety_gen`
- **What is wrong**: Theorem \ref{thm:lock-gen} (line 1167) claims that any two accepted chains with recent tips agree on the block 2n below each tip without conditioning on equal tip heights, whereas Lean's lockstep_client_safety_gen explicitly requires sTip.height = sTip'.height. For unequal heights, the lower tip's confirmed block lies on the taller chain (lockstepGen_recent_tip_ancestor_mem), but they do not agree on 'the block 2n below each tip' because those blocks sit at different heights.
- **Fix**: Amend Theorem \ref{thm:lock-gen} statement to distinguish equal and unequal heights, matching Theorem \ref{thm:lock} and line 1211: 'agree: at equal heights on the block 2n below each tip; at unequal heights the lower chain's 2n-deep block lies on the taller (lockstepGen_recent_tip_ancestor_mem)'.

#### [F-08] Claim C88 (TeX lines 1204--1215)
- **TeX Line(s)**: 1204--1215
- **Lean Declaration**: `Molt.lockstep_recent_certified_suffix_agreement`
- **What is wrong**: Text in §6.3 (line 1208) conjoins certificate presentation lockstep_recent_certified_suffix_agreement with depth 2n under Theorem \ref{thm:lock-gen}, and §6.3 Honest Scope (line 1253) omits mode 3 certificates when scoping future work. In Lean, lockstep_recent_certified_suffix_agreement is proved exclusively under the cumulative fault budget at depth n, and per-generation credit at depth 2n is proved only for full chains.
- **Fix**: Clarify in §2, §6.3, and Honest Scope that mode 3's certificate presentation theorem is established only under the cumulative budget at depth n, and that lifting certificates to per-generation erasure credit at depth 2n remains future work.

### MINOR

#### [F-09] Claim C8 (TeX lines 232--238)
- **TeX Line(s)**: 232--238
- **Lean Declaration**: `Molt.lockstep_client_safety_gen`
- **What is wrong**: In the §2 overview, the text claims 'the same agreement holds at confirmation depth 2n instead of n, and with no shared-genesis hypothesis (lockstep_client_safety_gen)'. This omits the equal-tip-height premise in lockstep_client_safety_gen; for unequal heights, agreement is captured by lockstepGen_recent_tip_ancestor_mem.
- **Fix**: Note that lockstep_client_safety_gen establishes depth-2n agreement for equal-height tips, while general unequal-height prefix agreement is established by lockstepGen_recent_tip_ancestor_mem.

#### [F-10] Claim C16 (TeX lines 346--348)
- **TeX Line(s)**: 346--348
- **Lean Declaration**: None (conceptual / informal)
- **What is wrong**: Characterizing all safety theorems in Section 4 as simply 'this counting argument made precise and machine-checked' reduces multi-layered cryptographic, synchrony, and certificate-grounding theorems to a purely combinatorial intersection lemma.
- **Fix**: Clarify that the counting argument is the core combinatorial engine around which cryptographic unforgeability, certificate grounding, and rotation pin mechanisms are layered.

#### [F-11] Claim C23 (TeX lines 446--452)
- **TeX Line(s)**: 446--452
- **Lean Declaration**: `Molt.keyrot_recent_certified_suffix_agreement, Molt.sched_recent_certified_suffix_agreement, Molt.lockstep_recent_certified_suffix_agreement`
- **What is wrong**: §4 (line 451) states that validator checks at certificate level 'are proved for all three modes', but does not note that for modes 2 and 3 the certificate theorems assume global/cumulative budgets rather than horizon or per-generation budgets.
- **Fix**: Add a parenthetical clarification that mode 2 and mode 3 certificate theorems are proved under global/cumulative budgets.

---

## Claims Verified Faithful

A total of 96 claims out of 107 audited were verified faithful against the Lean formalization and paper statements:

| Claim ID | TeX Lines | Kind | Lean Declarations | Notes |
|---|---|---|---|---|
| C5 | 178--182 | prose | `Molt.badKeyrot_lossOnly`, `Molt.badSched_lossOnly`, `Molt.exposedSched_lossOnly` | Molt.badKeyrot_lossOnly is an alias for MoltPetit.Model.badKeyrotOn_lossOnly;... |
| C6 | 193--200 | prose | `Molt.no_budget_beyond` |  |
| C9 | 256--258 | prose | `Molt.producer` | Molt.producer is an alias for MoltPetit.Model.producerForSlot. |
| C10 | 276--289 | prose | `MoltPetit.Model.Block.keyIndex` |  |
| C11 | 301--305 | prose | `MoltPetit.Model.Block.contentsHash` |  |
| C12 | 305--307 | prose | `MoltPetit.Model.Block.keyIndex` |  |
| C13 | 309--314 | prose | `MoltPetit.Model.Block.prev`, `MoltPetit.Model.Block.id` |  |
| C14 | 325--329 | prose | `Molt.linksOk`, `Molt.genesisOk` | Molt.linksOk is an alias for MoltPetit.Model.linksOk; Molt.genesisOk is an al... |
| C15 | 333--338 | prose | `Molt.validChain`, `Molt.denseSoFar` | Molt.validChain is an alias for MoltPetit.Model.validChain. |
| C17 | 350--353 | prose | `MoltPetit.Model.Block.keyIndex`, `Molt.keyMonoOk` | Molt.keyMonoOk is an alias for MoltPetit.Model.keyMonoOk. |
| C18 | 353--355 | prose | `Molt.validChainK` | Molt.validChainK is an alias for MoltPetit.Model.validChainK. |
| C19 | 372--383 | prose | `Molt.SigOps`, `Molt.KeyRegistry`, `Molt.CertOps` | Molt.SigOps is an alias for MoltPetit.Model.SigOps; Molt.KeyRegistry is an al... |
| C20 | 402--409 | prose | `Molt.validCertifiedChain` | Molt.validCertifiedChain is an alias for MoltPetit.Model.validateCertifiedChain. |
| C21 | 430 | prose | `Molt.validCertifiedChain` | Molt.validCertifiedChain is an alias for MoltPetit.Model.validateCertifiedChain. |
| C22 | 430--446 | prose | `MoltPetit.Model.CertOps.verify`, `MoltPetit.Model.Block.prev`, `Molt.validSuffix`, `Molt.keyMonoOk` | Molt.validSuffix is an alias for MoltPetit.Model.validateSuffix; Molt.keyMono... |
| C24 | 452--456 | prose | `Molt.validChain` | Molt.validChain is an alias for MoltPetit.Model.validChain. |
| C25 | 461 | prose | `Molt.produceBlock?` | Molt.produceBlock? is an alias for MoltPetit.Model.produceBlockCert?. |
| C26 | 461--464 | prose | `Molt.validSuffix` | Molt.validSuffix is an alias for MoltPetit.Model.validateSuffix. |
| C27 | 468 | prose | `Molt.selectChain` | Molt.selectChain is an alias for MoltPetit.Model.selectCertifiedChain. |
| C28 | 483--485 | prose | `Molt.validCertifiedChain` | Molt.validCertifiedChain is an alias for MoltPetit.Model.validateCertifiedChain. |
| C29 | 518--519 | prose | `Molt.FaultBounded` | Molt.FaultBounded is an alias for MoltPetit.Model.ByzantineBounded. |
| C30 | 522--524 | prose | `Molt.SigningLog` | Molt.SigningLog is an alias for MoltPetit.Model.SigningLog. |
| C31 | 536 | prose | `Molt.SigUnforgeableRecent` | Molt.SigUnforgeableRecent is an alias for MoltPetit.Model.SigUnforgeableRecent. |
| C32 | 566--575 | prose | `Molt.KeyStealingSigned`, `Molt.SignedDeclared`, `MoltPetit.Model.Block.keyIndex` | Molt.KeyStealingSigned is an alias for MoltPetit.Model.KeyStealingSigned; Mol... |
| C33 | 575 | prose | `Molt.SignedHashInjective` | Molt.SignedHashInjective is an alias for MoltPetit.Model.SignedHashInjective. |
| C34 | 582--585 | prose | `MoltPetit.Model.groundedCert_history` | Prose claim citing the proved lemma (groundedCert_history) that reconstructs ... |
| C35 | 585--586 | prose | `Molt.GroundedCert` | Molt.GroundedCert is an alias for MoltPetit.Model.GroundedCert. |
| C36 | 602 | prose | `Molt.HonestBlocksCover` | Molt.HonestBlocksCover is an alias for MoltPetit.Model.HonestBlocksCover. |
| C37 | 609--612 | prose | `Molt.validChainK_structural` | Molt.validChainK_structural is an alias for MoltPetit.Model.validChainK_sound. |
| C38 | 612--616 | prose | `Molt.keyrot_recent_certified_suffix_agreement` | Molt.keyrot_recent_certified_suffix_agreement is an alias for MoltPetit.Model... |
| C40 | 631 | prose | *(prose / model-level)* | Prose section introduction asserting every result in Section 4 is a Lean theo... |
| C41 | 631--637 | prose | `Molt.light_client_safety`, `Molt.forged_time_bound`, `Rust.rust_recent_tip_ancestor_mem` | Prose summary connecting model theorems (light_client_safety, forged_time_bou... |
| C42 | 645--657 | theorem | `Molt.light_client_safety` | Molt.light_client_safety is an alias for MoltPetit.Model.recent_certified_suf... |
| C43 | 659--664 | prose | *(prose / model-level)* | Prose remark explicitly noting that the multi-representation property is an i... |
| C44 | 681--687 | prose | `Molt.TimedExecution` | Molt.TimedExecution is an alias for MoltPetit.Model.TimedExecution. |
| C45 | 687--692 | prose | `Molt.TimedExecution.chain_order` | Molt.TimedExecution.chain_order is an alias for MoltPetit.Model.TimedExecutio... |
| C46 | 696--717 | theorem | `Molt.forged_time_bound`, `Molt.forged_chain_time_bound` | Molt.forged_time_bound is an alias for MoltPetit.Model.forged_suffix_time_bou... |
| C47 | 720--726 | prose | `Molt.TimedExecution.chain_order` | Molt.TimedExecution.chain_order is an alias for MoltPetit.Model.TimedExecutio... |
| C48 | 741--748 | prose | `Molt.sigUnforgeableRecent_of_timed` | Molt.sigUnforgeableRecent_of_timed is an alias for MoltPetit.Model.sigUnforge... |
| C49 | 753--756 | prose | `MoltPetit.Model.Block.keyIndex`, `Molt.keyMonoOk` | Molt.keyMonoOk is an alias for MoltPetit.Model.keyMonoOk. |
| C50 | 780--784 | prose | `Molt.badKeyrot` | Molt.badKeyrot is an alias for MoltPetit.Model.badKeyrotOn. |
| C51 | 790--794 | prose | `Molt.KeyStealingSigned`, `Molt.SignedDeclared` | Molt.KeyStealingSigned is an alias for MoltPetit.Model.KeyStealingSigned; Mol... |
| C52 | 797 | prose | `Molt.KeyStealingEUFCMA`, `Molt.SchedCoreUnforgeable`, `Molt.badSched_single_key_safe_not_enough`, `Molt.badKeyrot_single_key_safe_not_enough` | Molt.KeyStealingEUFCMA is an alias for MoltPetit.Model.KeyStealingEUFCMA; Mol... |
| C53 | 802--805 | prose | `Molt.badKeyrot_lossOnly`, `Molt.badSched_lossOnly` | Molt.badKeyrot_lossOnly is an alias for MoltPetit.Model.badKeyrotOn_lossOnly;... |
| C54 | 811--815 | prose | `Molt.inForce`, `Molt.validSignedChainK'` | Molt.inForce is an alias for MoltPetit.Model.inForce; Molt.validSignedChainK'... |
| C55 | 840--852 | theorem | `Molt.sync_rule`, `Molt.sync_rule_mem` |  |
| C56 | 864--867 | prose | `Molt.deep_block_span` |  |
| C57 | 874--881 | prose | `Molt.client_refresh_rule` |  |
| C58 | 914--927 | prose | `Molt.keyrot_recent_certified_suffix_agreement`, `Molt.GroundedCertK`, `Molt.keyrot_certified_suffix_agreement_anchored`, `Molt.cert_sync_rule`, `Molt.cert_max_sync_period` | Molt.keyrot_recent_certified_suffix_agreement is an alias for MoltPetit.Model... |
| C59 | 930--937 | prose | `Molt.Reacts`, `Molt.budget_of_reaction`, `Molt.sync_rule_timed`, `Molt.max_sync_period_timed` | Molt.Reacts is an alias for MoltPetit.Model.Reacts; Molt.budget_of_reaction i... |
| C60 | 941--944 | prose | `Molt.max_sync_period` |  |
| C61 | 948--958 | prose | `Molt.census_accumulates`, `Molt.census_accumulates_later_thefts`, `Molt.no_budget_beyond`, `Molt.inForce_mono` |  |
| C62 | 969--973 | prose | `Molt.Reacts`, `Molt.NoTheftBackdating` | Molt.Reacts is an alias for MoltPetit.Model.Reacts; Molt.NoTheftBackdating is... |
| C63 | 973--976 | prose | `Molt.theft_exposure_window` | Molt.theft_exposure_window is an alias for MoltPetit.Model.theft_exposure_win... |
| C64 | 976--980 | prose | `Molt.paced_tight_census_bound_all_F`, `Molt.max_sync_period_tight` | Molt.max_sync_period_tight is an alias for MoltPetit.Model.budget_of_reaction... |
| C65 | 985--988 | prose | `Molt.client_refresh_rule`, `Molt.stay_recent_client_safe` |  |
| C66 | 1030--1036 | prose | `Molt.sync_rule`, `Molt.sync_rule_mem`, `Molt.same_block_same_prefix` | Molt.same_block_same_prefix is an alias for MoltPetit.Model.same_block_same_p... |
| C67 | 1036--1040 | prose | `Molt.sync_induction_full_chain` |  |
| C68 | 1040--1044 | prose | *(prose / model-level)* | Prose remark explicitly noting the density remark is an informal argument and... |
| C69 | 1044--1047 | prose | `Molt.client_refresh_rule` |  |
| C70 | 1055--1057 | prose | `Molt.validSignedChainSched` | Molt.validSignedChainSched is an alias for MoltPetit.Model.validSignedChainSc... |
| C71 | 1062--1073 | theorem | `Molt.scheduled_client_safety`, `Molt.sched_recent_tip_ancestor_mem` | Molt.scheduled_client_safety is an alias for MoltPetit.Model.sched_recent_tip... |
| C72 | 1077--1082 | prose | `Molt.NoPrematureTheft` | Molt.NoPrematureTheft is an alias for MoltPetit.Model.NoPrematureTheft. |
| C73 | 1089--1093 | prose | `Molt.sched_oldkey_fork_stale` | Molt.sched_oldkey_fork_stale is an alias for MoltPetit.Model.sched_oldkey_for... |
| C74 | 1093--1098 | prose | `Molt.GroundedCertSched`, `Molt.sched_recent_certified_suffix_agreement` | Molt.GroundedCertSched is an alias for MoltPetit.Model.GroundedCertSched; Mol... |
| C75 | 1112--1121 | prose | `Molt.sched_recent_tip_ancestor_agreement_horizon` | Molt.sched_recent_tip_ancestor_agreement_horizon is an alias for MoltPetit.Mo... |
| C76 | 1123--1128 | prose | `Molt.same_block_same_prefix`, `Molt.sched_recent_tip_ancestor_mem_horizon` | Molt.same_block_same_prefix is an alias for MoltPetit.Model.same_block_same_p... |
| C77 | 1128--1132 | prose | `Molt.GroundedCertSched`, `Molt.sched_recent_certified_suffix_agreement` | Molt.GroundedCertSched is an alias for MoltPetit.Model.GroundedCertSched; Mol... |
| C78 | 1135--1141 | prose | `Molt.noMixing`, `Molt.validSignedChainLock` | Molt.noMixing is an alias for MoltPetit.Model.lockstepOk; Molt.validSignedCha... |
| C79 | 1144--1155 | theorem | `Molt.lockstep_client_safety`, `Molt.lockstep_recent_tip_ancestor_mem` | Molt.lockstep_client_safety is an alias for MoltPetit.Model.lockstep_recent_t... |
| C80 | 1157--1162 | prose | `Molt.lockstep_declares_rosterGen` | Molt.lockstep_declares_rosterGen is an alias for MoltPetit.Model.lockstep_dec... |
| C82 | 1170 | prose | `Molt.lockstep_window_declares_rosterGen`, `Molt.window_shared_prefix` | Molt.lockstep_window_declares_rosterGen is an alias for MoltPetit.Model.locks... |
| C83 | 1170 | prose | `Molt.lockstepGen_shared_prefix_sharp` | Molt.lockstepGen_shared_prefix_sharp is an alias for MoltPetit.Model.lockstep... |
| C84 | 1170 | prose | `Molt.LockstepPackage.toGen` | Molt.LockstepPackage.toGen is an alias for MoltPetit.Model.LockstepPackage.to... |
| C85 | 1175 | prose | `Molt.ErasureTimedLock`, `Molt.genBound_of_preRetirementBound`, `Molt.lockstep_client_safety_timed` | Molt.ErasureTimedLock is an alias for MoltPetit.Model.ErasureTimedLock; Molt.... |
| C86 | 1187--1193 | prose | `Molt.groundedCertLock_gen_of_tail`, `Molt.groundedCertLock_gen_unique` | Molt.groundedCertLock_gen_of_tail is an alias for MoltPetit.Model.groundedCer... |
| C87 | 1193--1204 | prose | `Molt.lockstep_client_safety_timed` | Molt.lockstep_client_safety_timed is an alias for MoltPetit.Model.lockstepTim... |
| C89 | 1243--1251 | prose | `Molt.theft_exposure_window`, `Molt.NoTheftBackdating`, `Molt.paced_tight_census_bound_all_F`, `Molt.paced_budget_holds_under_timing` | Molt.theft_exposure_window is an alias for MoltPetit.Model.theft_exposure_win... |
| C90 | 1251--1255 | prose | `Molt.sched_recent_certified_suffix_agreement` | Molt.sched_recent_certified_suffix_agreement is an alias for MoltPetit.Model.... |
| C91 | 1255--1260 | prose | `Molt.badSched_single_key_safe_not_enough`, `Molt.badKeyrot_single_key_safe_not_enough` | Molt.badSched_single_key_safe_not_enough is an alias for MoltPetit.Model.badS... |
| C92 | 1270--1281 | theorem | `Molt.production_liveness`, `Molt.global_liveness` | Molt.production_liveness is an alias for MoltPetit.Model.liveness_produce_blo... |
| C93 | 1289--1294 | prose | `Molt.slot_time_sufficient`, `Molt.slot_time_necessary` | Molt.slot_time_sufficient is an alias for MoltPetit.Model.ProverTiming.recomm... |
| C94 | 1301--1306 | prose | `Rust.rust_valid_chain_sound` |  |
| C95 | 1306--1310 | prose | `Rust.rust_recent_tip_ancestor_mem` |  |
| C96 | 1310--1314 | prose | `Rust.rust_valid_chain_sound`, `Rust.rust_valid_chain_k_sound` |  |
| C97 | 1314--1320 | prose | `molt_petit.valid_chain_be`, `Rust.valid_chain_be_validChain` |  |
| C98 | 1374--1376 | prose | *(prose / model-level)* | Prose remark in Related Work comparing proving cost overhead. |
| C99 | 1397--1402 | prose | *(prose / model-level)* | Prose comparison in Related Work noting Molt Petit has a machine-checked arti... |
| C100 | 1408--1410 | prose | *(prose / model-level)* | Prose comparison in Related Work contrasting with Plumo pen-and-paper arguments. |
| C101 | 1426 | prose | *(prose / model-level)* | Prose paragraph heading/discussion contrasting Molt Petit verification direct... |
| C102 | 1471--1491 | prose | `Rust.valid_chain_be_validChain` |  |
| C103 | 1536--1541 | prose | `Molt.projectSigned` | Molt.projectSigned is an alias for MoltPetit.Model.projectSigned. |
| C104 | 1541--1548 | prose | `Molt.NoBackdate` | Molt.NoBackdate is an alias for MoltPetit.Model.NoBackdate. |
| C105 | 1551--1556 | theorem | `Molt.sigUnforgeableRecent_of_timed` | Molt.sigUnforgeableRecent_of_timed is an alias for MoltPetit.Model.sigUnforge... |
| C106 | 1571--1576 | prose | `Molt.noBackdate_independent` | Molt.noBackdate_independent is an alias for MoltPetit.Model.noBackdate_indepe... |
| C107 | 1589--1595 | prose | `Molt.badSched_single_key_safe_not_enough`, `Molt.badKeyrot_single_key_safe_not_enough` | Molt.badSched_single_key_safe_not_enough is an alias for MoltPetit.Model.badS... |
