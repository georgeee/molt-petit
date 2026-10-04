import Molt
import MoltPetit
import Rust

-- TEST: CertOps -> Molt.CertOps
#check @Molt.CertOps
-- TEST: CertOps -> MoltPetit.Model.CertOps
#check @MoltPetit.Model.CertOps
-- TEST: CertOps.verify -> Molt.CertOps.verify
#check @Molt.CertOps.verify
-- TEST: CertOps.verify -> MoltPetit.Model.CertOps.verify
#check @MoltPetit.Model.CertOps.verify
-- TEST: ErasureTimedLock -> Molt.ErasureTimedLock
#check @Molt.ErasureTimedLock
-- TEST: ErasureTimedLock -> MoltPetit.Model.ErasureTimedLock
#check @MoltPetit.Model.ErasureTimedLock
-- TEST: FaultBounded -> Molt.FaultBounded
#check @Molt.FaultBounded
-- TEST: FaultBounded -> MoltPetit.Model.FaultBounded
#check @MoltPetit.Model.FaultBounded
-- TEST: GroundedCert -> Molt.GroundedCert
#check @Molt.GroundedCert
-- TEST: GroundedCert -> MoltPetit.Model.GroundedCert
#check @MoltPetit.Model.GroundedCert
-- TEST: GroundedCertK -> Molt.GroundedCertK
#check @Molt.GroundedCertK
-- TEST: GroundedCertK -> MoltPetit.Model.GroundedCertK
#check @MoltPetit.Model.GroundedCertK
-- TEST: GroundedCertSched -> Molt.GroundedCertSched
#check @Molt.GroundedCertSched
-- TEST: GroundedCertSched -> MoltPetit.Model.GroundedCertSched
#check @MoltPetit.Model.GroundedCertSched
-- TEST: HonestBlocksCover -> Molt.HonestBlocksCover
#check @Molt.HonestBlocksCover
-- TEST: HonestBlocksCover -> MoltPetit.Model.HonestBlocksCover
#check @MoltPetit.Model.HonestBlocksCover
-- TEST: KeyRegistry -> Molt.KeyRegistry
#check @Molt.KeyRegistry
-- TEST: KeyRegistry -> MoltPetit.Model.KeyRegistry
#check @MoltPetit.Model.KeyRegistry
-- TEST: KeyStealingEUFCMA -> Molt.KeyStealingEUFCMA
#check @Molt.KeyStealingEUFCMA
-- TEST: KeyStealingEUFCMA -> MoltPetit.Model.KeyStealingEUFCMA
#check @MoltPetit.Model.KeyStealingEUFCMA
-- TEST: KeyStealingSigned -> Molt.KeyStealingSigned
#check @Molt.KeyStealingSigned
-- TEST: KeyStealingSigned -> MoltPetit.Model.KeyStealingSigned
#check @MoltPetit.Model.KeyStealingSigned
-- TEST: LockstepPackage.toGen -> Molt.LockstepPackage.toGen
#check @Molt.LockstepPackage.toGen
-- TEST: LockstepPackage.toGen -> MoltPetit.Model.LockstepPackage.toGen
#check @MoltPetit.Model.LockstepPackage.toGen
-- TEST: NoBackdate -> Molt.NoBackdate
#check @Molt.NoBackdate
-- TEST: NoBackdate -> MoltPetit.Model.NoBackdate
#check @MoltPetit.Model.NoBackdate
-- TEST: NoPrematureTheft -> Molt.NoPrematureTheft
#check @Molt.NoPrematureTheft
-- TEST: NoPrematureTheft -> MoltPetit.Model.NoPrematureTheft
#check @MoltPetit.Model.NoPrematureTheft
-- TEST: NoTheftBackdating -> Molt.NoTheftBackdating
#check @Molt.NoTheftBackdating
-- TEST: NoTheftBackdating -> MoltPetit.Model.NoTheftBackdating
#check @MoltPetit.Model.NoTheftBackdating
-- TEST: Reacts -> Molt.Reacts
#check @Molt.Reacts
-- TEST: Reacts -> MoltPetit.Model.Reacts
#check @MoltPetit.Model.Reacts
-- TEST: SchedCoreUnforgeable -> Molt.SchedCoreUnforgeable
#check @Molt.SchedCoreUnforgeable
-- TEST: SchedCoreUnforgeable -> MoltPetit.Model.SchedCoreUnforgeable
#check @MoltPetit.Model.SchedCoreUnforgeable
-- TEST: SigOps -> Molt.SigOps
#check @Molt.SigOps
-- TEST: SigOps -> MoltPetit.Model.SigOps
#check @MoltPetit.Model.SigOps
-- TEST: SigUnforgeableRecent -> Molt.SigUnforgeableRecent
#check @Molt.SigUnforgeableRecent
-- TEST: SigUnforgeableRecent -> MoltPetit.Model.SigUnforgeableRecent
#check @MoltPetit.Model.SigUnforgeableRecent
-- TEST: SignedDeclared -> Molt.SignedDeclared
#check @Molt.SignedDeclared
-- TEST: SignedDeclared -> MoltPetit.Model.SignedDeclared
#check @MoltPetit.Model.SignedDeclared
-- TEST: SignedHashInjective -> Molt.SignedHashInjective
#check @Molt.SignedHashInjective
-- TEST: SignedHashInjective -> MoltPetit.Model.SignedHashInjective
#check @MoltPetit.Model.SignedHashInjective
-- TEST: SigningLog -> Molt.SigningLog
#check @Molt.SigningLog
-- TEST: SigningLog -> MoltPetit.Model.SigningLog
#check @MoltPetit.Model.SigningLog
-- TEST: TimedExecution -> Molt.TimedExecution
#check @Molt.TimedExecution
-- TEST: TimedExecution -> MoltPetit.Model.TimedExecution
#check @MoltPetit.Model.TimedExecution
-- TEST: badKeyrot -> Molt.badKeyrot
#check @Molt.badKeyrot
-- TEST: badKeyrot -> MoltPetit.Model.badKeyrot
#check @MoltPetit.Model.badKeyrot
-- TEST: badKeyrot_lossOnly -> Molt.badKeyrot_lossOnly
#check @Molt.badKeyrot_lossOnly
-- TEST: badKeyrot_lossOnly -> MoltPetit.Model.badKeyrot_lossOnly
#check @MoltPetit.Model.badKeyrot_lossOnly
-- TEST: badKeyrot_single_key_safe_not_enough -> Molt.badKeyrot_single_key_safe_not_enough
#check @Molt.badKeyrot_single_key_safe_not_enough
-- TEST: badKeyrot_single_key_safe_not_enough -> MoltPetit.Model.badKeyrot_single_key_safe_not_enough
#check @MoltPetit.Model.badKeyrot_single_key_safe_not_enough
-- TEST: badSched_lossOnly -> Molt.badSched_lossOnly
#check @Molt.badSched_lossOnly
-- TEST: badSched_lossOnly -> MoltPetit.Model.badSched_lossOnly
#check @MoltPetit.Model.badSched_lossOnly
-- TEST: badSched_single_key_safe_not_enough -> Molt.badSched_single_key_safe_not_enough
#check @Molt.badSched_single_key_safe_not_enough
-- TEST: badSched_single_key_safe_not_enough -> MoltPetit.Model.badSched_single_key_safe_not_enough
#check @MoltPetit.Model.badSched_single_key_safe_not_enough
-- TEST: budget_of_reaction -> Molt.budget_of_reaction
#check @Molt.budget_of_reaction
-- TEST: budget_of_reaction -> MoltPetit.Model.budget_of_reaction
#check @MoltPetit.Model.budget_of_reaction
-- TEST: census_accumulates -> Molt.census_accumulates
#check @Molt.census_accumulates
-- TEST: census_accumulates -> MoltPetit.Model.census_accumulates
#check @MoltPetit.Model.census_accumulates
-- TEST: census_accumulates_later_thefts -> Molt.census_accumulates_later_thefts
#check @Molt.census_accumulates_later_thefts
-- TEST: census_accumulates_later_thefts -> MoltPetit.Model.census_accumulates_later_thefts
#check @MoltPetit.Model.census_accumulates_later_thefts
-- TEST: cert_max_sync_period -> Molt.cert_max_sync_period
#check @Molt.cert_max_sync_period
-- TEST: cert_max_sync_period -> MoltPetit.Model.cert_max_sync_period
#check @MoltPetit.Model.cert_max_sync_period
-- TEST: cert_sync_rule -> Molt.cert_sync_rule
#check @Molt.cert_sync_rule
-- TEST: cert_sync_rule -> MoltPetit.Model.cert_sync_rule
#check @MoltPetit.Model.cert_sync_rule
-- TEST: chain_order -> Molt.chain_order
#check @Molt.chain_order
-- TEST: chain_order -> MoltPetit.Model.chain_order
#check @MoltPetit.Model.chain_order
-- TEST: client_refresh_rule -> Molt.client_refresh_rule
#check @Molt.client_refresh_rule
-- TEST: client_refresh_rule -> MoltPetit.Model.client_refresh_rule
#check @MoltPetit.Model.client_refresh_rule
-- TEST: contentsHash -> Molt.Block.contentsHash
#check @Molt.Block.contentsHash
-- TEST: contentsHash -> MoltPetit.Model.Block.contentsHash
#check @MoltPetit.Model.Block.contentsHash
-- TEST: deep_block_span -> Molt.deep_block_span
#check @Molt.deep_block_span
-- TEST: deep_block_span -> MoltPetit.Model.deep_block_span
#check @MoltPetit.Model.deep_block_span
-- TEST: denseSoFar -> Molt.denseSoFar
#check @Molt.denseSoFar
-- TEST: denseSoFar -> MoltPetit.Model.denseSoFar
#check @MoltPetit.Model.denseSoFar
-- TEST: exposedSched_lossOnly -> Molt.exposedSched_lossOnly
#check @Molt.exposedSched_lossOnly
-- TEST: exposedSched_lossOnly -> MoltPetit.Model.exposedSched_lossOnly
#check @MoltPetit.Model.exposedSched_lossOnly
-- TEST: forged_chain_time_bound -> Molt.forged_chain_time_bound
#check @Molt.forged_chain_time_bound
-- TEST: forged_chain_time_bound -> MoltPetit.Model.forged_chain_time_bound
#check @MoltPetit.Model.forged_chain_time_bound
-- TEST: forged_time_bound -> Molt.forged_time_bound
#check @Molt.forged_time_bound
-- TEST: forged_time_bound -> MoltPetit.Model.forged_time_bound
#check @MoltPetit.Model.forged_time_bound
-- TEST: genBound_of_preRetirementBound -> Molt.genBound_of_preRetirementBound
#check @Molt.genBound_of_preRetirementBound
-- TEST: genBound_of_preRetirementBound -> MoltPetit.Model.genBound_of_preRetirementBound
#check @MoltPetit.Model.genBound_of_preRetirementBound
-- TEST: genesisOk -> Molt.genesisOk
#check @Molt.genesisOk
-- TEST: genesisOk -> MoltPetit.Model.genesisOk
#check @MoltPetit.Model.genesisOk
-- TEST: global_liveness -> Molt.global_liveness
#check @Molt.global_liveness
-- TEST: global_liveness -> MoltPetit.Model.global_liveness
#check @MoltPetit.Model.global_liveness
-- TEST: groundedCertLock_gen_of_tail -> Molt.groundedCertLock_gen_of_tail
#check @Molt.groundedCertLock_gen_of_tail
-- TEST: groundedCertLock_gen_of_tail -> MoltPetit.Model.groundedCertLock_gen_of_tail
#check @MoltPetit.Model.groundedCertLock_gen_of_tail
-- TEST: groundedCertLock_gen_unique -> Molt.groundedCertLock_gen_unique
#check @Molt.groundedCertLock_gen_unique
-- TEST: groundedCertLock_gen_unique -> MoltPetit.Model.groundedCertLock_gen_unique
#check @MoltPetit.Model.groundedCertLock_gen_unique
-- TEST: id -> Molt.Block.id
#check @Molt.Block.id
-- TEST: id -> MoltPetit.Model.Block.id
#check @MoltPetit.Model.Block.id
-- TEST: inForce -> Molt.inForce
#check @Molt.inForce
-- TEST: inForce -> MoltPetit.Model.inForce
#check @MoltPetit.Model.inForce
-- TEST: inForce_mono -> Molt.inForce_mono
#check @Molt.inForce_mono
-- TEST: inForce_mono -> MoltPetit.Model.inForce_mono
#check @MoltPetit.Model.inForce_mono
-- TEST: keyIndex -> Molt.Block.keyIndex
#check @Molt.Block.keyIndex
-- TEST: keyIndex -> MoltPetit.Model.Block.keyIndex
#check @MoltPetit.Model.Block.keyIndex
-- TEST: keyMonoOk -> Molt.keyMonoOk
#check @Molt.keyMonoOk
-- TEST: keyMonoOk -> MoltPetit.Model.keyMonoOk
#check @MoltPetit.Model.keyMonoOk
-- TEST: keyrot_certified_suffix_agreement_anchored -> Molt.keyrot_certified_suffix_agreement_anchored
#check @Molt.keyrot_certified_suffix_agreement_anchored
-- TEST: keyrot_certified_suffix_agreement_anchored -> MoltPetit.Model.keyrot_certified_suffix_agreement_anchored
#check @MoltPetit.Model.keyrot_certified_suffix_agreement_anchored
-- TEST: keyrot_recent_certified_suffix_agreement -> Molt.keyrot_recent_certified_suffix_agreement
#check @Molt.keyrot_recent_certified_suffix_agreement
-- TEST: keyrot_recent_certified_suffix_agreement -> MoltPetit.Model.keyrot_recent_certified_suffix_agreement
#check @MoltPetit.Model.keyrot_recent_certified_suffix_agreement
-- TEST: light_client_safety -> Molt.light_client_safety
#check @Molt.light_client_safety
-- TEST: light_client_safety -> MoltPetit.Model.light_client_safety
#check @MoltPetit.Model.light_client_safety
-- TEST: linksOk -> Molt.linksOk
#check @Molt.linksOk
-- TEST: linksOk -> MoltPetit.Model.linksOk
#check @MoltPetit.Model.linksOk
-- TEST: liveness_produce_blockK -> Molt.liveness_produce_blockK
#check @Molt.liveness_produce_blockK
-- TEST: liveness_produce_blockK -> MoltPetit.Model.liveness_produce_blockK
#check @MoltPetit.Model.liveness_produce_blockK
-- TEST: lockstepGen_recent_genesis_agreement -> Molt.lockstepGen_recent_genesis_agreement
#check @Molt.lockstepGen_recent_genesis_agreement
-- TEST: lockstepGen_recent_genesis_agreement -> MoltPetit.Model.lockstepGen_recent_genesis_agreement
#check @MoltPetit.Model.lockstepGen_recent_genesis_agreement
-- TEST: lockstepGen_shared_prefix_sharp -> Molt.lockstepGen_shared_prefix_sharp
#check @Molt.lockstepGen_shared_prefix_sharp
-- TEST: lockstepGen_shared_prefix_sharp -> MoltPetit.Model.lockstepGen_shared_prefix_sharp
#check @MoltPetit.Model.lockstepGen_shared_prefix_sharp
-- TEST: lockstep_cert_gen_pinned -> Molt.lockstep_cert_gen_pinned
#check @Molt.lockstep_cert_gen_pinned
-- TEST: lockstep_cert_gen_pinned -> MoltPetit.Model.lockstep_cert_gen_pinned
#check @MoltPetit.Model.lockstep_cert_gen_pinned
-- TEST: lockstep_client_safety -> Molt.lockstep_client_safety
#check @Molt.lockstep_client_safety
-- TEST: lockstep_client_safety -> MoltPetit.Model.lockstep_client_safety
#check @MoltPetit.Model.lockstep_client_safety
-- TEST: lockstep_client_safety_gen -> Molt.lockstep_client_safety_gen
#check @Molt.lockstep_client_safety_gen
-- TEST: lockstep_client_safety_gen -> MoltPetit.Model.lockstep_client_safety_gen
#check @MoltPetit.Model.lockstep_client_safety_gen
-- TEST: lockstep_client_safety_timed -> Molt.lockstep_client_safety_timed
#check @Molt.lockstep_client_safety_timed
-- TEST: lockstep_client_safety_timed -> MoltPetit.Model.lockstep_client_safety_timed
#check @MoltPetit.Model.lockstep_client_safety_timed
-- TEST: lockstep_declares_rosterGen -> Molt.lockstep_declares_rosterGen
#check @Molt.lockstep_declares_rosterGen
-- TEST: lockstep_declares_rosterGen -> MoltPetit.Model.lockstep_declares_rosterGen
#check @MoltPetit.Model.lockstep_declares_rosterGen
-- TEST: lockstep_recent_certified_suffix_agreement -> Molt.lockstep_recent_certified_suffix_agreement
#check @Molt.lockstep_recent_certified_suffix_agreement
-- TEST: lockstep_recent_certified_suffix_agreement -> MoltPetit.Model.lockstep_recent_certified_suffix_agreement
#check @MoltPetit.Model.lockstep_recent_certified_suffix_agreement
-- TEST: lockstep_recent_tip_ancestor_mem -> Molt.lockstep_recent_tip_ancestor_mem
#check @Molt.lockstep_recent_tip_ancestor_mem
-- TEST: lockstep_recent_tip_ancestor_mem -> MoltPetit.Model.lockstep_recent_tip_ancestor_mem
#check @MoltPetit.Model.lockstep_recent_tip_ancestor_mem
-- TEST: lockstep_window_declares_rosterGen -> Molt.lockstep_window_declares_rosterGen
#check @Molt.lockstep_window_declares_rosterGen
-- TEST: lockstep_window_declares_rosterGen -> MoltPetit.Model.lockstep_window_declares_rosterGen
#check @MoltPetit.Model.lockstep_window_declares_rosterGen
-- TEST: max_sync_period -> Molt.max_sync_period
#check @Molt.max_sync_period
-- TEST: max_sync_period -> MoltPetit.Model.max_sync_period
#check @MoltPetit.Model.max_sync_period
-- TEST: max_sync_period_tight -> Molt.max_sync_period_tight
#check @Molt.max_sync_period_tight
-- TEST: max_sync_period_tight -> MoltPetit.Model.max_sync_period_tight
#check @MoltPetit.Model.max_sync_period_tight
-- TEST: max_sync_period_timed -> Molt.max_sync_period_timed
#check @Molt.max_sync_period_timed
-- TEST: max_sync_period_timed -> MoltPetit.Model.max_sync_period_timed
#check @MoltPetit.Model.max_sync_period_timed
-- TEST: noBackdate_independent -> Molt.noBackdate_independent
#check @Molt.noBackdate_independent
-- TEST: noBackdate_independent -> MoltPetit.Model.noBackdate_independent
#check @MoltPetit.Model.noBackdate_independent
-- TEST: noMixing -> Molt.noMixing
#check @Molt.noMixing
-- TEST: noMixing -> MoltPetit.Model.noMixing
#check @MoltPetit.Model.noMixing
-- TEST: no_budget_beyond -> Molt.no_budget_beyond
#check @Molt.no_budget_beyond
-- TEST: no_budget_beyond -> MoltPetit.Model.no_budget_beyond
#check @MoltPetit.Model.no_budget_beyond
-- TEST: paced_budget_holds_under_timing -> Molt.paced_budget_holds_under_timing
#check @Molt.paced_budget_holds_under_timing
-- TEST: paced_budget_holds_under_timing -> MoltPetit.Model.paced_budget_holds_under_timing
#check @MoltPetit.Model.paced_budget_holds_under_timing
-- TEST: paced_tight_census_bound_all_F -> Molt.paced_tight_census_bound_all_F
#check @Molt.paced_tight_census_bound_all_F
-- TEST: paced_tight_census_bound_all_F -> MoltPetit.Model.paced_tight_census_bound_all_F
#check @MoltPetit.Model.paced_tight_census_bound_all_F
-- TEST: prev -> Molt.Block.prev
#check @Molt.Block.prev
-- TEST: prev -> MoltPetit.Model.Block.prev
#check @MoltPetit.Model.Block.prev
-- TEST: produceBlock? -> Molt.produceBlock?
#check @Molt.produceBlock?
-- TEST: produceBlock? -> MoltPetit.Model.produceBlock?
#check @MoltPetit.Model.produceBlock?
-- TEST: producer -> Molt.producer
#check @Molt.producer
-- TEST: producer -> MoltPetit.Model.producer
#check @MoltPetit.Model.producer
-- TEST: production_liveness -> Molt.production_liveness
#check @Molt.production_liveness
-- TEST: production_liveness -> MoltPetit.Model.production_liveness
#check @MoltPetit.Model.production_liveness
-- TEST: projectSigned -> Molt.projectSigned
#check @Molt.projectSigned
-- TEST: projectSigned -> MoltPetit.Model.projectSigned
#check @MoltPetit.Model.projectSigned
-- TEST: rust_recent_tip_ancestor_mem -> Rust.rust_recent_tip_ancestor_mem
#check @Rust.rust_recent_tip_ancestor_mem
-- TEST: rust_valid_chain_k_sound -> Rust.rust_valid_chain_k_sound
#check @Rust.rust_valid_chain_k_sound
-- TEST: rust_valid_chain_sound -> Rust.rust_valid_chain_sound
#check @Rust.rust_valid_chain_sound
-- TEST: same_block_same_prefix -> Molt.same_block_same_prefix
#check @Molt.same_block_same_prefix
-- TEST: same_block_same_prefix -> MoltPetit.Model.same_block_same_prefix
#check @MoltPetit.Model.same_block_same_prefix
-- TEST: sched_oldkey_fork_stale -> Molt.sched_oldkey_fork_stale
#check @Molt.sched_oldkey_fork_stale
-- TEST: sched_oldkey_fork_stale -> MoltPetit.Model.sched_oldkey_fork_stale
#check @MoltPetit.Model.sched_oldkey_fork_stale
-- TEST: sched_recent_certified_suffix_agreement -> Molt.sched_recent_certified_suffix_agreement
#check @Molt.sched_recent_certified_suffix_agreement
-- TEST: sched_recent_certified_suffix_agreement -> MoltPetit.Model.sched_recent_certified_suffix_agreement
#check @MoltPetit.Model.sched_recent_certified_suffix_agreement
-- TEST: sched_recent_tip_ancestor_agreement_horizon -> Molt.sched_recent_tip_ancestor_agreement_horizon
#check @Molt.sched_recent_tip_ancestor_agreement_horizon
-- TEST: sched_recent_tip_ancestor_agreement_horizon -> MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon
#check @MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon
-- TEST: sched_recent_tip_ancestor_mem -> Molt.sched_recent_tip_ancestor_mem
#check @Molt.sched_recent_tip_ancestor_mem
-- TEST: sched_recent_tip_ancestor_mem -> MoltPetit.Model.sched_recent_tip_ancestor_mem
#check @MoltPetit.Model.sched_recent_tip_ancestor_mem
-- TEST: sched_recent_tip_ancestor_mem_horizon -> Molt.sched_recent_tip_ancestor_mem_horizon
#check @Molt.sched_recent_tip_ancestor_mem_horizon
-- TEST: sched_recent_tip_ancestor_mem_horizon -> MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon
#check @MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon
-- TEST: scheduled_client_safety -> Molt.scheduled_client_safety
#check @Molt.scheduled_client_safety
-- TEST: scheduled_client_safety -> MoltPetit.Model.scheduled_client_safety
#check @MoltPetit.Model.scheduled_client_safety
-- TEST: selectChain -> Molt.selectChain
#check @Molt.selectChain
-- TEST: selectChain -> MoltPetit.Model.selectChain
#check @MoltPetit.Model.selectChain
-- TEST: sigUnforgeableRecent_of_timed -> Molt.sigUnforgeableRecent_of_timed
#check @Molt.sigUnforgeableRecent_of_timed
-- TEST: sigUnforgeableRecent_of_timed -> MoltPetit.Model.sigUnforgeableRecent_of_timed
#check @MoltPetit.Model.sigUnforgeableRecent_of_timed
-- TEST: slot_time_necessary -> Molt.slot_time_necessary
#check @Molt.slot_time_necessary
-- TEST: slot_time_necessary -> MoltPetit.Model.slot_time_necessary
#check @MoltPetit.Model.slot_time_necessary
-- TEST: slot_time_sufficient -> Molt.slot_time_sufficient
#check @Molt.slot_time_sufficient
-- TEST: slot_time_sufficient -> MoltPetit.Model.slot_time_sufficient
#check @MoltPetit.Model.slot_time_sufficient
-- TEST: stay_recent_client_safe -> Molt.stay_recent_client_safe
#check @Molt.stay_recent_client_safe
-- TEST: stay_recent_client_safe -> MoltPetit.Model.stay_recent_client_safe
#check @MoltPetit.Model.stay_recent_client_safe
-- TEST: sync_induction_full_chain -> Molt.sync_induction_full_chain
#check @Molt.sync_induction_full_chain
-- TEST: sync_induction_full_chain -> MoltPetit.Model.sync_induction_full_chain
#check @MoltPetit.Model.sync_induction_full_chain
-- TEST: sync_rule -> Molt.sync_rule
#check @Molt.sync_rule
-- TEST: sync_rule -> MoltPetit.Model.sync_rule
#check @MoltPetit.Model.sync_rule
-- TEST: sync_rule_mem -> Molt.sync_rule_mem
#check @Molt.sync_rule_mem
-- TEST: sync_rule_mem -> MoltPetit.Model.sync_rule_mem
#check @MoltPetit.Model.sync_rule_mem
-- TEST: sync_rule_timed -> Molt.sync_rule_timed
#check @Molt.sync_rule_timed
-- TEST: sync_rule_timed -> MoltPetit.Model.sync_rule_timed
#check @MoltPetit.Model.sync_rule_timed
-- TEST: theft_exposure_window -> Molt.theft_exposure_window
#check @Molt.theft_exposure_window
-- TEST: theft_exposure_window -> MoltPetit.Model.theft_exposure_window
#check @MoltPetit.Model.theft_exposure_window
-- TEST: validCertifiedChain -> Molt.validCertifiedChain
#check @Molt.validCertifiedChain
-- TEST: validCertifiedChain -> MoltPetit.Model.validCertifiedChain
#check @MoltPetit.Model.validCertifiedChain
-- TEST: validChain -> Molt.validChain
#check @Molt.validChain
-- TEST: validChain -> MoltPetit.Model.validChain
#check @MoltPetit.Model.validChain
-- TEST: validChainK -> Molt.validChainK
#check @Molt.validChainK
-- TEST: validChainK -> MoltPetit.Model.validChainK
#check @MoltPetit.Model.validChainK
-- TEST: validChainK_structural -> Molt.validChainK_structural
#check @Molt.validChainK_structural
-- TEST: validChainK_structural -> MoltPetit.Model.validChainK_structural
#check @MoltPetit.Model.validChainK_structural
-- TEST: validSignedChainK' -> Molt.validSignedChainK'
#check @Molt.validSignedChainK'
-- TEST: validSignedChainK' -> MoltPetit.Model.validSignedChainK'
#check @MoltPetit.Model.validSignedChainK'
-- TEST: validSignedChainLock -> Molt.validSignedChainLock
#check @Molt.validSignedChainLock
-- TEST: validSignedChainLock -> MoltPetit.Model.validSignedChainLock
#check @MoltPetit.Model.validSignedChainLock
-- TEST: validSignedChainSched -> Molt.validSignedChainSched
#check @Molt.validSignedChainSched
-- TEST: validSignedChainSched -> MoltPetit.Model.validSignedChainSched
#check @MoltPetit.Model.validSignedChainSched
-- TEST: validSuffix -> Molt.validSuffix
#check @Molt.validSuffix
-- TEST: validSuffix -> MoltPetit.Model.validSuffix
#check @MoltPetit.Model.validSuffix
-- TEST: valid_chain_be -> molt_petit.valid_chain_be
#check @molt_petit.valid_chain_be
-- TEST: valid_chain_be -> Rust.valid_chain_be
#check @Rust.valid_chain_be
-- TEST: valid_chain_be_validChain -> Rust.valid_chain_be_validChain
#check @Rust.valid_chain_be_validChain
-- TEST: window_shared_prefix -> Molt.window_shared_prefix
#check @Molt.window_shared_prefix
-- TEST: window_shared_prefix -> MoltPetit.Model.window_shared_prefix
#check @MoltPetit.Model.window_shared_prefix