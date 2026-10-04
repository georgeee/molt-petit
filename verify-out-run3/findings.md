NOT READY: The manuscript is not ready for submission due to 3 MAJOR findings regarding overclaimed single-chain finality and a contradictory operational definition of no-theft-backdating, alongside 5 MINOR discrepancies in theorem scoping, genesis hypotheses, and table presentation.

## Automated Check Results

| Check | Result | Details |
|---|---|---|
| Lean Build (`lake build`) | PASS | Exit code 0 |
| TeX Build (`paper/build.sh`) | PASS | Exit code 0 |
| Lean Proof Sorries / Admits | PASS | 4 matches in comments/docs (0 in proofs) |
| Custom Lean Axiom Declarations | PASS | 0 custom axioms (standard Lean axioms only) |
| LaTeX Warning Lines | PASS | 1 warning (rerunfilecheck) |
| Lake Command | - | `nix-run /home/etheron-bare-exec/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake` |

---

## Findings

### BLOCKER

None.

### MAJOR

#### [F-01] Claim C3 (TeX line(s) 87--92)
- **TeX Line(s)**: 87--92
- **Lean Declaration**: `Rust.rust_timed_certified_agreement`
- **What is wrong**: The prose claims that if the certificate verifies and its tip is recent, "the client may act on everything n blocks deep", implying unconditional single-chain finality against arbitrary shorter chains. In Lean, rust_timed_certified_agreement is a two-chain mutual agreement theorem requiring both competing valid recent certified chains to reach depth h + n to guarantee agreement at height h. It does not rule out shorter competing chains without additional height bounds.
- **Fix**: Clarify that the theorem guarantees agreement between any two certified recent chains that both reach height h + n (as stated in Theorem 1).

#### [F-02] Claim C70 (TeX line(s) 1031--1035)
- **TeX Line(s)**: 1031--1035
- **Lean Declaration**: `Molt.NoTheftBackdating`
- **What is wrong**: In Lean, NoTheftBackdating is defined as `∀ i j r s, stolenAt i j r → inForce n Δconf c₀ i s ≤ j → r ≤ s`, universally quantifying over all chain slots s where key version j has not yet been retired by the confirmed floor. Because chain confirmed floors start at 0 (hFloor0), `inForce ... s ≤ j` holds at s = 0 for initial active keys (j ≥ 0), asserting r ≤ 0. Consequently, NoTheftBackdating forces every theft of an initial active key to occur at slot 0 (r ≤ 0), making the hypothesis contradictory with non-zero theft times (r > 0) unless keys were pre-retired before slot 0.
- **Fix**: Redefine NoTheftBackdating to constrain only slots s where an adversarial block signing under key j is actually placed on the chain, avoiding universal quantification over unrotated historical slots.

#### [F-03] Claim C71 (TeX line(s) 1035--1038)
- **TeX Line(s)**: 1035--1038
- **Lean Declaration**: `MoltPetit.Model.theft_exposure_window`
- **What is wrong**: Theorem theft_exposure_window inherits the defective definition of NoTheftBackdating from C70. Because `inForce ... s ≤ j` holds at s = 0 for initial keys, any theft at r > 0 yields r ≤ 0 ∧ 0 < r + d, forcing r = 0. The claimed exposure window [r, r+d) only behaves as intended under chains that pre-rotate keys prior to slot 0.
- **Fix**: Redefine NoTheftBackdating so theft_exposure_window applies to slots actually signed by the adversary rather than all historical slots with unadvanced floors.

### MINOR

#### [F-04] Claim C12 (TeX line(s) 271)
- **TeX Line(s)**: 271
- **Lean Declaration**: `Table 1 (Mode 2) / Molt.sched_recent_tip_ancestor_agreement_horizon`
- **What is wrong**: Table 1 lists "genesis + clock + gen" under "client holds" for Mode 2, whereas lines 1141, 1146-1147, and 1184 emphasize that Mode 2 clients do not need genesis ("genesis agreement is a consequence", "client holds a clock and the constant gen").
- **Fix**: Change Table 1 Mode 2 "client holds" column to "clock + gen (genesis optional/derived)" for consistency.

#### [F-05] Claim C72 (TeX line(s) 1038--1042)
- **TeX Line(s)**: 1038--1042
- **Lean Declaration**: `Molt.paced_tight_census_bound_all_F, Molt.max_sync_period_tight`
- **What is wrong**: While paced_tight_census_bound_all_F is an unconditioned combinatorial bound on the tight census filter, the composed end-to-end guarantee max_sync_period_tight requires NoTheftBackdating and Reacts on the chain stripSigs sc. Because NoTheftBackdating cannot be jointly satisfied with initial zero floors hFloor0 for non-zero theft slots, max_sync_period_tight is bottlenecked by the defective NoTheftBackdating operational assumption.
- **Fix**: Note in the text that paced_tight_census_bound_all_F is an unconditioned combinatorial bound on the tight census filter, while the composed theorem max_sync_period_tight inherits the operational assumption NoTheftBackdating.

#### [F-06] Claim C79 (TeX line(s) 1141--1142)
- **TeX Line(s)**: 1141--1142
- **Lean Declaration**: `Molt.sched_recent_genesis_agreement_horizon`
- **What is wrong**: The text states "There is no shared-genesis hypothesis: genesis agreement is a consequence (sched_recent_genesis_agreement_horizon)" immediately following a statement that unequal-height membership requires length > n only for the lower chain. In Lean, sched_recent_genesis_agreement_horizon requires both chains to be longer than n (hLong and hLong').
- **Fix**: Clarify that the genesis agreement consequence specifically requires both competing chains to exceed length n.

#### [F-07] Claim C79 (TeX line(s) 1143--1144)
- **TeX Line(s)**: 1143--1144
- **Lean Declaration**: `Molt.scheduled_client_safety, Molt.sched_recent_tip_ancestor_agreement_horizon, MoltPetit.Model.byzantineBoundedFrom_of_bounded`
- **What is wrong**: The text states "The global-budget scheduled_client_safety is the corollary at any H (byzantineBoundedFrom_of_bounded)". In Lean, scheduled_client_safety is not formalized as a corollary of sched_recent_tip_ancestor_agreement_horizon (it retains legacy hHead/hHead' shared-genesis hypotheses and delegates to the un-horizoned theorem; formal reduction is noted in code comments as unformalized).
- **Fix**: Rephrase to clarify that scheduled_client_safety is the earlier global-budget theorem whose budget hypothesis is subsumed by byzantineBoundedFrom_of_bounded.

#### [F-08] Claim C88 (TeX line(s) 1248--1249)
- **TeX Line(s)**: 1248--1249
- **Lean Declaration**: `Molt.lockstepGen_recent_genesis_agreement`
- **What is wrong**: The text states "Through the parent-id chain, they agree on their whole common prefix down to height 0: no shared genesis is assumed (lockstepGen_recent_genesis_agreement)". In Lean, lockstepGen_recent_genesis_agreement requires both chains to satisfy 2n < length (hLong and hLong'), unlike unequal-heights membership which needs 2n < length only for the lower chain.
- **Fix**: Clarify that common prefix / genesis agreement requires both chains to exceed 2n.

---

## Claims Verified Faithful

A total of 110 claims out of 117 audited were verified faithful against the Lean formalization and paper statements:

| Claim ID | TeX Lines | Kind | Lean Declarations | Notes |
|---|---|---|---|---|
| C1 | 61--67 | prose | *(model / conceptual)* | High-level prose assertion summarizing formal results. |
| C2 | 67--73 | prose | *(model / conceptual)* | High-level prose assertion summarizing formal results. |
| C4 | 124--133 | prose | *(model / conceptual)* | High-level prose assertion summarizing formal results. |
| C5 | 180--185 | prose | `Molt.liveness_produce_blockK` | Prose claim referencing Molt.liveness_produce_blockK. |
| C6 | 185--189 | prose | `Molt.badKeyrot_lossOnly`, `Molt.badSched_lossOnly`, `Molt.exposedSched_lossOnly` | Prose claim referencing Molt.badKeyrot_lossOnly, Molt.badSched_lossOnly, Molt.exposedSched_lossOnly. |
| C7 | 200--207 | prose | `Molt.no_budget_beyond` | Prose claim referencing Molt.no_budget_beyond. |
| C8 | 238--241 | prose | `Molt.lockstep_recent_certified_suffix_agreement` | Prose claim referencing Molt.lockstep_recent_certified_suffix_agreement. |
| C9 | 241--250 | prose | `Molt.lockstep_client_safety_gen`, `Molt.lockstepGen_recent_tip_ancestor_mem` | Prose claim referencing Molt.lockstep_client_safety_gen, Molt.lockstepGen_recent_tip_ancestor_mem. |
| C10 | 262--267 | prose | `Molt.timed_light_client_safety`, `Rust.rust_timed_certified_agreement` | Prose claim referencing Molt.timed_light_client_safety, Rust.rust_timed_certified_agreement. |
| C11 | 267--271 | prose | `Molt.sync_rule_timed` | Prose claim referencing Molt.sync_rule_timed. |
| C13 | 276--277 | prose | `Molt.lockstep_client_safety` | Prose claim referencing Molt.lockstep_client_safety. |
| C14 | 277--284 | prose | `Molt.lockstep_client_safety_gen`, `Molt.lockstepGen_recent_tip_ancestor_mem` | Prose claim referencing Molt.lockstep_client_safety_gen, Molt.lockstepGen_recent_tip_ancestor_mem. |
| C15 | 305--307 | prose | `Molt.producer` | Prose claim referencing Molt.producer. |
| C16 | 325--338 | prose | `MoltPetit.Model.Block.keyIndex` | Prose claim referencing MoltPetit.Model.Block.keyIndex. |
| C17 | 351--355 | prose | `MoltPetit.Model.Block.contentsHash` | Prose claim referencing MoltPetit.Model.Block.contentsHash. |
| C18 | 355--357 | prose | `MoltPetit.Model.Block.keyIndex` | Prose claim referencing MoltPetit.Model.Block.keyIndex. |
| C19 | 359--364 | prose | `MoltPetit.Model.Block.prev`, `MoltPetit.Model.Block.id` | Prose claim referencing MoltPetit.Model.Block.prev, MoltPetit.Model.Block.id. |
| C20 | 375--379 | prose | `Molt.linksOk`, `Molt.genesisOk` | Prose claim referencing Molt.linksOk, Molt.genesisOk. |
| C21 | 383--388 | prose | `Molt.validChain`, `Molt.denseSoFar` | Prose claim referencing Molt.validChain, Molt.denseSoFar. |
| C22 | 396--400 | prose | *(model / conceptual)* | High-level prose assertion summarizing formal results. |
| C23 | 402--405 | prose | `MoltPetit.Model.Block.keyIndex`, `Molt.keyMonoOk` | Prose claim referencing MoltPetit.Model.Block.keyIndex, Molt.keyMonoOk. |
| C24 | 405--407 | prose | `Molt.validChainK` | Prose claim referencing Molt.validChainK. |
| C25 | 424--435 | prose | `Molt.SigOps`, `Molt.KeyRegistry`, `Molt.CertOps` | Prose claim referencing Molt.SigOps, Molt.KeyRegistry, Molt.CertOps. |
| C26 | 454--462 | prose | `Molt.validCertifiedChain` | Prose claim referencing Molt.validCertifiedChain. |
| C27 | 485 | prose | `Molt.validCertifiedChain` | Prose claim referencing Molt.validCertifiedChain. |
| C28 | 485--501 | prose | `MoltPetit.Model.CertOps.verify`, `MoltPetit.Model.Block.prev`, `Molt.validSuffix`, `Molt.keyMonoOk` | Prose claim referencing MoltPetit.Model.CertOps.verify, MoltPetit.Model.Block.prev, Molt.validSuffix, Molt.keyMonoOk. |
| C29 | 501--508 | prose | `Molt.validSignedChainK'`, `Molt.keyrot_recent_certified_suffix_agreement`, `Molt.sched_recent_certified_suffix_agreement`, `Molt.lockstep_recent_certified_suffix_agreement` | Prose claim referencing Molt.validSignedChainK', Molt.keyrot_recent_certified_suffix_agreement, Molt.sched_recent_cer... |
| C30 | 508--512 | prose | `Molt.validChain` | Prose claim referencing Molt.validChain. |
| C31 | 517--520 | prose | `Molt.validSuffix` | Prose claim referencing Molt.validSuffix. |
| C32 | 524 | prose | `Molt.selectChain` | Prose claim referencing Molt.selectChain. |
| C33 | 539--541 | prose | `Molt.validCertifiedChain` | Prose claim referencing Molt.validCertifiedChain. |
| C34 | 574--575 | prose | `Molt.ByzantineBounded` | Prose claim referencing Molt.ByzantineBounded. |
| C35 | 578--579 | prose | `Molt.TimedExecution` | Prose claim referencing Molt.TimedExecution. |
| C36 | 579--592 | prose | `MoltPetit.Model.TimedExecution.key_match`, `MoltPetit.Model.TimedExecution.honest_stamp`, `MoltPetit.Model.TimedExecution.honest_once` | Cites theorem hypothesis parameter `hbridge`. |
| C37 | 592--594 | prose | `MoltPetit.Model.TimedExecution.chain_order` | Prose claim referencing MoltPetit.Model.TimedExecution.chain_order. |
| C38 | 594--595 | prose | `Molt.TimedExecution` | Cites theorem hypothesis parameter `hbridge`. |
| C39 | 609--613 | prose | `MoltPetit.Model.TimedExecution.id_inj`, `MoltPetit.Model.SignedEver` | Prose claim referencing MoltPetit.Model.TimedExecution.id_inj, MoltPetit.Model.SignedEver. |
| C40 | 620--629 | prose | `Molt.KeyStealingSigned`, `Molt.SignedDeclared`, `MoltPetit.Model.Block.keyIndex` | Prose claim referencing Molt.KeyStealingSigned, Molt.SignedDeclared, MoltPetit.Model.Block.keyIndex. |
| C41 | 629--630 | prose | `MoltPetit.Model.TimedExecution.id_inj`, `Molt.SignedHashInjective` | Prose claim referencing MoltPetit.Model.TimedExecution.id_inj, Molt.SignedHashInjective. |
| C42 | 637--640 | prose | *(model / conceptual)* | High-level prose assertion summarizing formal results. |
| C43 | 640--641 | prose | `Molt.GroundedCert` | Prose claim referencing Molt.GroundedCert. |
| C44 | 658 | prose | `Molt.HonestBlocksCover` | Prose claim referencing Molt.HonestBlocksCover. |
| C45 | 664--666 | prose | `Molt.timed_light_client_safety` | Prose claim referencing Molt.timed_light_client_safety. |
| C46 | 679 | prose | *(model / conceptual)* | High-level prose assertion summarizing formal results. |
| C47 | 679--685 | prose | *(model / conceptual)* | High-level prose assertion summarizing formal results. |
| C48 | 693--719 | theorem | `Molt.timed_light_client_safety` | Theorem 1: headline timed light client safety. |
| C49 | 725--729 | prose | `MoltPetit.Model.late_tail_short` | Prose claim referencing MoltPetit.Model.late_tail_short. |
| C50 | 734--737 | prose | `Molt.light_client_safety`, `Molt.SigUnforgeableRecent` | Prose claim referencing Molt.light_client_safety, Molt.SigUnforgeableRecent. |
| C51 | 743--749 | prose | `Molt.TimedExecution` | Prose claim referencing Molt.TimedExecution. |
| C52 | 749--754 | prose | `MoltPetit.Model.TimedExecution.chain_order` | Prose claim referencing MoltPetit.Model.TimedExecution.chain_order. |
| C53 | 758--779 | theorem | `Molt.forged_time_bound`, `Molt.forged_chain_time_bound` | Theorem 2: forged suffixes advance at half speed. |
| C54 | 782--788 | prose | `MoltPetit.Model.TimedExecution.chain_order` | Prose claim referencing MoltPetit.Model.TimedExecution.chain_order. |
| C55 | 795--798 | prose | *(model / conceptual)* | High-level prose assertion summarizing formal results. |
| C56 | 807--810 | prose | `MoltPetit.Model.Block.keyIndex`, `Molt.keyMonoOk` | Prose claim referencing MoltPetit.Model.Block.keyIndex, Molt.keyMonoOk. |
| C57 | 834--838 | prose | `Molt.badKeyrot` | Prose claim referencing Molt.badKeyrot. |
| C58 | 844--848 | prose | `Molt.KeyStealingSigned`, `Molt.SignedDeclared` | Prose claim referencing Molt.KeyStealingSigned, Molt.SignedDeclared. |
| C59 | 851 | prose | `Molt.SigUnforgeableRecent`, `Molt.KeyStealingEUFCMA`, `Molt.SchedCoreUnforgeable`, `Molt.badSched_single_key_safe_not_enough`, `Molt.badKeyrot_single_key_safe_not_enough` | Prose claim referencing Molt.SigUnforgeableRecent, Molt.KeyStealingEUFCMA, Molt.SchedCoreUnforgeable, Molt.badSched_s... |
| C60 | 856--859 | prose | `Molt.badKeyrot_lossOnly`, `Molt.badSched_lossOnly` | Prose claim referencing Molt.badKeyrot_lossOnly, Molt.badSched_lossOnly. |
| C61 | 865--869 | prose | `Molt.inForce`, `Molt.validSignedChainK'` | Prose claim referencing Molt.inForce, Molt.validSignedChainK'. |
| C62 | 894--911 | theorem | `Molt.sync_rule_timed`, `Molt.sync_rule_mem_timed` | Theorem 3: client sync rule (timed confirmation depth and membership forms). |
| C63 | 913--915 | prose | `Molt.sync_rule`, `Molt.sync_rule_mem`, `MoltPetit.Model.budget_of_reaction` | Prose claim referencing Molt.sync_rule, Molt.sync_rule_mem, MoltPetit.Model.budget_of_reaction. |
| C64 | 930--933 | prose | `Molt.deep_block_span` | Prose claim referencing Molt.deep_block_span. |
| C65 | 940--947 | prose | `Molt.client_refresh_rule` | Prose claim referencing Molt.client_refresh_rule. |
| C66 | 980--993 | prose | `Molt.keyrot_recent_certified_suffix_agreement`, `Molt.GroundedCertK`, `Molt.keyrot_certified_suffix_agreement_anchored`, `Molt.cert_sync_rule`, `Molt.cert_max_sync_period` | Prose claim referencing Molt.keyrot_recent_certified_suffix_agreement, Molt.GroundedCertK, Molt.keyrot_certified_suff... |
| C67 | 996--999 | prose | `Molt.Reacts`, `MoltPetit.Model.budget_of_reaction`, `Molt.sync_rule_timed`, `Molt.max_sync_period_timed` | Prose claim referencing Molt.Reacts, MoltPetit.Model.budget_of_reaction, Molt.sync_rule_timed, Molt.max_sync_period_t... |
| C68 | 1003--1006 | prose | `Molt.max_sync_period` | Prose claim referencing Molt.max_sync_period. |
| C69 | 1010--1020 | prose | `Molt.census_accumulates`, `Molt.census_accumulates_later_thefts`, `Molt.no_budget_beyond`, `Molt.inForce_mono` | Prose claim referencing Molt.census_accumulates, Molt.census_accumulates_later_thefts, Molt.no_budget_beyond, Molt.in... |
| C73 | 1047--1050 | prose | `Molt.client_refresh_rule`, `Molt.stay_recent_client_safe` | Prose claim referencing Molt.client_refresh_rule, Molt.stay_recent_client_safe. |
| C74 | 1092--1098 | prose | `Molt.sync_rule_timed`, `Molt.sync_rule_mem_timed`, `Molt.same_block_same_prefix` | Prose claim referencing Molt.sync_rule_timed, Molt.sync_rule_mem_timed, Molt.same_block_same_prefix. |
| C75 | 1098--1102 | prose | `Molt.sync_induction_full_chain` | Prose claim referencing Molt.sync_induction_full_chain. |
| C76 | 1102--1106 | prose | *(model / conceptual)* | High-level prose assertion summarizing formal results. |
| C77 | 1106--1109 | prose | `Molt.client_refresh_rule` | Prose claim referencing Molt.client_refresh_rule. |
| C78 | 1117--1119 | prose | `Molt.validSignedChainSched` | Prose claim referencing Molt.validSignedChainSched. |
| C80 | 1151--1156 | prose | `Molt.NoPrematureTheft` | Prose claim referencing Molt.NoPrematureTheft. |
| C81 | 1163--1167 | prose | `Molt.sched_oldkey_fork_stale` | Prose claim referencing Molt.sched_oldkey_fork_stale. |
| C82 | 1167--1172 | prose | `Molt.GroundedCertSched`, `Molt.sched_recent_certified_suffix_agreement` | Prose claim referencing Molt.GroundedCertSched, Molt.sched_recent_certified_suffix_agreement. |
| C83 | 1192--1195 | prose | `Molt.same_block_same_prefix` | Prose claim referencing Molt.same_block_same_prefix. |
| C84 | 1195--1199 | prose | `Molt.GroundedCertSched`, `Molt.sched_recent_certified_suffix_agreement` | Prose claim referencing Molt.GroundedCertSched, Molt.sched_recent_certified_suffix_agreement. |
| C85 | 1202--1208 | prose | `Molt.noMixing`, `Molt.validSignedChainLock` | Prose claim referencing Molt.noMixing, Molt.validSignedChainLock. |
| C86 | 1211--1222 | theorem | `Molt.lockstep_client_safety`, `Molt.lockstep_recent_tip_ancestor_mem` | Theorem 5: lockstep safety. |
| C87 | 1224--1229 | prose | `Molt.lockstep_declares_rosterGen` | Prose claim referencing Molt.lockstep_declares_rosterGen. |
| C89 | 1252 | prose | `Molt.lockstep_window_declares_rosterGen`, `Molt.window_shared_prefix` | Prose claim referencing Molt.lockstep_window_declares_rosterGen, Molt.window_shared_prefix. |
| C90 | 1252 | prose | `Molt.lockstepGen_shared_prefix_sharp` | Prose claim referencing Molt.lockstepGen_shared_prefix_sharp. |
| C91 | 1252 | prose | `Molt.LockstepPackage.toGen` | Prose claim referencing Molt.LockstepPackage.toGen. |
| C92 | 1257 | prose | `Molt.ErasureTimedLock`, `Molt.genBound_of_preRetirementBound`, `Molt.lockstep_client_safety_timed` | Prose claim referencing Molt.ErasureTimedLock, Molt.genBound_of_preRetirementBound, Molt.lockstep_client_safety_timed. |
| C93 | 1269--1275 | prose | `Molt.groundedCertLock_gen_of_tail`, `Molt.groundedCertLock_gen_unique` | Prose claim referencing Molt.groundedCertLock_gen_of_tail, Molt.groundedCertLock_gen_unique. |
| C94 | 1275--1286 | prose | `Molt.lockstep_client_safety_timed` | Prose claim referencing Molt.lockstep_client_safety_timed. |
| C95 | 1286--1298 | prose | `Molt.lockstep_client_safety`, `Molt.lockstep_recent_tip_ancestor_mem`, `Molt.lockstep_declares_rosterGen`, `Molt.lockstep_recent_certified_suffix_agreement`, `Molt.lockstep_cert_gen_pinned`, `Molt.same_block_same_prefix` | Prose claim referencing Molt.lockstep_client_safety, Molt.lockstep_recent_tip_ancestor_mem, Molt.lockstep_declares_ro... |
| C96 | 1303--1311 | prose | `MoltPetit.Model.theft_exposure_window`, `Molt.NoTheftBackdating`, `Molt.paced_tight_census_bound_all_F`, `Molt.paced_budget_holds_under_timing` | Prose claim referencing MoltPetit.Model.theft_exposure_window, Molt.NoTheftBackdating, Molt.paced_tight_census_bound_... |
| C97 | 1311--1318 | prose | `Molt.sched_recent_certified_suffix_agreement`, `Molt.lockstep_recent_certified_suffix_agreement` | Prose claim referencing Molt.sched_recent_certified_suffix_agreement, Molt.lockstep_recent_certified_suffix_agreement. |
| C98 | 1318--1323 | prose | `Molt.badSched_single_key_safe_not_enough`, `Molt.badKeyrot_single_key_safe_not_enough` | Prose claim referencing Molt.badSched_single_key_safe_not_enough, Molt.badKeyrot_single_key_safe_not_enough. |
| C99 | 1333--1344 | theorem | `Molt.production_liveness`, `Molt.global_liveness` | Theorem 7: liveness (local production and global liveness). |
| C100 | 1352--1357 | prose | `Molt.slot_time_sufficient`, `Molt.slot_time_necessary` | Prose claim referencing Molt.slot_time_sufficient, Molt.slot_time_necessary. |
| C101 | 1364--1369 | prose | `Rust.rust_valid_chain_sound` | Prose claim referencing Rust.rust_valid_chain_sound. |
| C102 | 1369--1374 | prose | `Rust.rust_recent_tip_ancestor_mem`, `Rust.rust_timed_certified_agreement` | Prose claim referencing Rust.rust_recent_tip_ancestor_mem, Rust.rust_timed_certified_agreement. |
| C103 | 1374--1378 | prose | `Rust.rust_valid_chain_sound`, `Rust.rust_valid_chain_k_sound` | Prose claim referencing Rust.rust_valid_chain_sound, Rust.rust_valid_chain_k_sound. |
| C104 | 1378--1384 | prose | `molt_petit.valid_chain_be`, `Rust.valid_chain_be_validChain` | Prose claim referencing molt_petit.valid_chain_be, Rust.valid_chain_be_validChain. |
| C105 | 1438--1440 | prose | *(model / conceptual)* | High-level prose assertion summarizing formal results. |
| C106 | 1461--1466 | prose | *(model / conceptual)* | High-level prose assertion summarizing formal results. |
| C107 | 1472--1474 | prose | *(model / conceptual)* | High-level prose assertion summarizing formal results. |
| C108 | 1490 | prose | *(model / conceptual)* | High-level prose assertion summarizing formal results. |
| C109 | 1535--1555 | prose | `Rust.valid_chain_be_validChain` | Prose claim referencing Rust.valid_chain_be_validChain. |
| C110 | 1555--1560 | prose | `Molt.Reacts` | Prose claim referencing Molt.Reacts. |
| C111 | 1593--1594 | prose | `Molt.NoBackdate` | Prose claim referencing Molt.NoBackdate. |
| C112 | 1594--1596 | prose | `Molt.SigUnforgeableRecent`, `Molt.light_client_safety` | Prose claim referencing Molt.SigUnforgeableRecent, Molt.light_client_safety. |
| C113 | 1608--1613 | prose | `Molt.projectSigned` | Prose claim referencing Molt.projectSigned. |
| C114 | 1613--1620 | prose | `Molt.NoBackdate` | Prose claim referencing Molt.NoBackdate. |
| C115 | 1623--1628 | theorem | `Molt.sigUnforgeableRecent_of_timed` | Theorem 8: untimed residue derived in timed model. |
| C116 | 1643--1648 | prose | `Molt.noBackdate_independent` | Prose claim referencing Molt.noBackdate_independent. |
| C117 | 1661--1667 | prose | `Molt.badSched_single_key_safe_not_enough`, `Molt.badKeyrot_single_key_safe_not_enough` | Prose claim referencing Molt.badSched_single_key_safe_not_enough, Molt.badKeyrot_single_key_safe_not_enough. |
