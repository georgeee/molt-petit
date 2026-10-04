import Molt
import MoltPetit
import Rust

set_option pp.all false
set_option pp.fullNames true

-- DECL: Molt.ByzantineBounded
#check @Molt.ByzantineBounded
#print axioms Molt.ByzantineBounded

-- DECL: Molt.CertOps
#check @Molt.CertOps
#print axioms Molt.CertOps

-- DECL: Molt.ErasureTimedLock
#check @Molt.ErasureTimedLock
#print axioms Molt.ErasureTimedLock

-- DECL: Molt.GroundedCert
#check @Molt.GroundedCert
#print axioms Molt.GroundedCert

-- DECL: Molt.GroundedCertK
#check @Molt.GroundedCertK
#print axioms Molt.GroundedCertK

-- DECL: Molt.GroundedCertSched
#check @Molt.GroundedCertSched
#print axioms Molt.GroundedCertSched

-- DECL: Molt.HonestBlocksCover
#check @Molt.HonestBlocksCover
#print axioms Molt.HonestBlocksCover

-- DECL: Molt.KeyRegistry
#check @Molt.KeyRegistry
#print axioms Molt.KeyRegistry

-- DECL: Molt.KeyStealingEUFCMA
#check @Molt.KeyStealingEUFCMA
#print axioms Molt.KeyStealingEUFCMA

-- DECL: Molt.KeyStealingSigned
#check @Molt.KeyStealingSigned
#print axioms Molt.KeyStealingSigned

-- DECL: Molt.LockstepPackage.toGen
#check @Molt.LockstepPackage.toGen
#print axioms Molt.LockstepPackage.toGen

-- DECL: Molt.NoBackdate
#check @Molt.NoBackdate
#print axioms Molt.NoBackdate

-- DECL: Molt.NoPrematureTheft
#check @Molt.NoPrematureTheft
#print axioms Molt.NoPrematureTheft

-- DECL: Molt.NoTheftBackdating
#check @Molt.NoTheftBackdating
#print axioms Molt.NoTheftBackdating

-- DECL: Molt.Reacts
#check @Molt.Reacts
#print axioms Molt.Reacts

-- DECL: Molt.SchedCoreUnforgeable
#check @Molt.SchedCoreUnforgeable
#print axioms Molt.SchedCoreUnforgeable

-- DECL: Molt.SigOps
#check @Molt.SigOps
#print axioms Molt.SigOps

-- DECL: Molt.SigUnforgeableRecent
#check @Molt.SigUnforgeableRecent
#print axioms Molt.SigUnforgeableRecent

-- DECL: Molt.SignedDeclared
#check @Molt.SignedDeclared
#print axioms Molt.SignedDeclared

-- DECL: Molt.SignedHashInjective
#check @Molt.SignedHashInjective
#print axioms Molt.SignedHashInjective

-- DECL: Molt.TimedExecution
#check @Molt.TimedExecution
#print axioms Molt.TimedExecution

-- DECL: Molt.badKeyrot
#check @Molt.badKeyrot
#print axioms Molt.badKeyrot

-- DECL: Molt.badKeyrot_lossOnly
#check @Molt.badKeyrot_lossOnly
#print axioms Molt.badKeyrot_lossOnly

-- DECL: Molt.badKeyrot_single_key_safe_not_enough
#check @Molt.badKeyrot_single_key_safe_not_enough
#print axioms Molt.badKeyrot_single_key_safe_not_enough

-- DECL: Molt.badSched_lossOnly
#check @Molt.badSched_lossOnly
#print axioms Molt.badSched_lossOnly

-- DECL: Molt.badSched_single_key_safe_not_enough
#check @Molt.badSched_single_key_safe_not_enough
#print axioms Molt.badSched_single_key_safe_not_enough

-- DECL: Molt.census_accumulates
#check @Molt.census_accumulates
#print axioms Molt.census_accumulates

-- DECL: Molt.census_accumulates_later_thefts
#check @Molt.census_accumulates_later_thefts
#print axioms Molt.census_accumulates_later_thefts

-- DECL: Molt.cert_max_sync_period
#check @Molt.cert_max_sync_period
#print axioms Molt.cert_max_sync_period

-- DECL: Molt.cert_sync_rule
#check @Molt.cert_sync_rule
#print axioms Molt.cert_sync_rule

-- DECL: Molt.client_refresh_rule
#check @Molt.client_refresh_rule
#print axioms Molt.client_refresh_rule

-- DECL: Molt.deep_block_span
#check @Molt.deep_block_span
#print axioms Molt.deep_block_span

-- DECL: Molt.denseSoFar
#check @Molt.denseSoFar
#print axioms Molt.denseSoFar

-- DECL: Molt.exposedSched_lossOnly
#check @Molt.exposedSched_lossOnly
#print axioms Molt.exposedSched_lossOnly

-- DECL: Molt.forged_chain_time_bound
#check @Molt.forged_chain_time_bound
#print axioms Molt.forged_chain_time_bound

-- DECL: Molt.forged_time_bound
#check @Molt.forged_time_bound
#print axioms Molt.forged_time_bound

-- DECL: Molt.genBound_of_preRetirementBound
#check @Molt.genBound_of_preRetirementBound
#print axioms Molt.genBound_of_preRetirementBound

-- DECL: Molt.genesisOk
#check @Molt.genesisOk
#print axioms Molt.genesisOk

-- DECL: Molt.global_liveness
#check @Molt.global_liveness
#print axioms Molt.global_liveness

-- DECL: Molt.groundedCertLock_gen_of_tail
#check @Molt.groundedCertLock_gen_of_tail
#print axioms Molt.groundedCertLock_gen_of_tail

-- DECL: Molt.groundedCertLock_gen_unique
#check @Molt.groundedCertLock_gen_unique
#print axioms Molt.groundedCertLock_gen_unique

-- DECL: Molt.inForce
#check @Molt.inForce
#print axioms Molt.inForce

-- DECL: Molt.inForce_mono
#check @Molt.inForce_mono
#print axioms Molt.inForce_mono

-- DECL: Molt.keyMonoOk
#check @Molt.keyMonoOk
#print axioms Molt.keyMonoOk

-- DECL: Molt.keyrot_certified_suffix_agreement_anchored
#check @Molt.keyrot_certified_suffix_agreement_anchored
#print axioms Molt.keyrot_certified_suffix_agreement_anchored

-- DECL: Molt.keyrot_recent_certified_suffix_agreement
#check @Molt.keyrot_recent_certified_suffix_agreement
#print axioms Molt.keyrot_recent_certified_suffix_agreement

-- DECL: Molt.light_client_safety
#check @Molt.light_client_safety
#print axioms Molt.light_client_safety

-- DECL: Molt.linksOk
#check @Molt.linksOk
#print axioms Molt.linksOk

-- DECL: Molt.liveness_produce_blockK
#check @Molt.liveness_produce_blockK
#print axioms Molt.liveness_produce_blockK

-- DECL: Molt.lockstepGen_recent_tip_ancestor_mem
#check @Molt.lockstepGen_recent_tip_ancestor_mem
#print axioms Molt.lockstepGen_recent_tip_ancestor_mem

-- DECL: Molt.lockstepGen_shared_prefix_sharp
#check @Molt.lockstepGen_shared_prefix_sharp
#print axioms Molt.lockstepGen_shared_prefix_sharp

-- DECL: Molt.lockstep_cert_gen_pinned
#check @Molt.lockstep_cert_gen_pinned
#print axioms Molt.lockstep_cert_gen_pinned

-- DECL: Molt.lockstep_client_safety
#check @Molt.lockstep_client_safety
#print axioms Molt.lockstep_client_safety

-- DECL: Molt.lockstep_client_safety_gen
#check @Molt.lockstep_client_safety_gen
#print axioms Molt.lockstep_client_safety_gen

-- DECL: Molt.lockstep_client_safety_timed
#check @Molt.lockstep_client_safety_timed
#print axioms Molt.lockstep_client_safety_timed

-- DECL: Molt.lockstep_declares_rosterGen
#check @Molt.lockstep_declares_rosterGen
#print axioms Molt.lockstep_declares_rosterGen

-- DECL: Molt.lockstep_recent_certified_suffix_agreement
#check @Molt.lockstep_recent_certified_suffix_agreement
#print axioms Molt.lockstep_recent_certified_suffix_agreement

-- DECL: Molt.lockstep_recent_tip_ancestor_mem
#check @Molt.lockstep_recent_tip_ancestor_mem
#print axioms Molt.lockstep_recent_tip_ancestor_mem

-- DECL: Molt.lockstep_window_declares_rosterGen
#check @Molt.lockstep_window_declares_rosterGen
#print axioms Molt.lockstep_window_declares_rosterGen

-- DECL: Molt.max_sync_period
#check @Molt.max_sync_period
#print axioms Molt.max_sync_period

-- DECL: Molt.max_sync_period_tight
#check @Molt.max_sync_period_tight
#print axioms Molt.max_sync_period_tight

-- DECL: Molt.max_sync_period_timed
#check @Molt.max_sync_period_timed
#print axioms Molt.max_sync_period_timed

-- DECL: Molt.noBackdate_independent
#check @Molt.noBackdate_independent
#print axioms Molt.noBackdate_independent

-- DECL: Molt.noMixing
#check @Molt.noMixing
#print axioms Molt.noMixing

-- DECL: Molt.no_budget_beyond
#check @Molt.no_budget_beyond
#print axioms Molt.no_budget_beyond

-- DECL: Molt.paced_budget_holds_under_timing
#check @Molt.paced_budget_holds_under_timing
#print axioms Molt.paced_budget_holds_under_timing

-- DECL: Molt.paced_tight_census_bound_all_F
#check @Molt.paced_tight_census_bound_all_F
#print axioms Molt.paced_tight_census_bound_all_F

-- DECL: Molt.producer
#check @Molt.producer
#print axioms Molt.producer

-- DECL: Molt.production_liveness
#check @Molt.production_liveness
#print axioms Molt.production_liveness

-- DECL: Molt.projectSigned
#check @Molt.projectSigned
#print axioms Molt.projectSigned

-- DECL: Molt.same_block_same_prefix
#check @Molt.same_block_same_prefix
#print axioms Molt.same_block_same_prefix

-- DECL: Molt.sched_oldkey_fork_stale
#check @Molt.sched_oldkey_fork_stale
#print axioms Molt.sched_oldkey_fork_stale

-- DECL: Molt.sched_recent_certified_suffix_agreement
#check @Molt.sched_recent_certified_suffix_agreement
#print axioms Molt.sched_recent_certified_suffix_agreement

-- DECL: Molt.sched_recent_tip_ancestor_agreement_horizon
#check @Molt.sched_recent_tip_ancestor_agreement_horizon
#print axioms Molt.sched_recent_tip_ancestor_agreement_horizon

-- DECL: Molt.sched_recent_tip_ancestor_mem_horizon
#check @Molt.sched_recent_tip_ancestor_mem_horizon
#print axioms Molt.sched_recent_tip_ancestor_mem_horizon

-- DECL: Molt.selectChain
#check @Molt.selectChain
#print axioms Molt.selectChain

-- DECL: Molt.sigUnforgeableRecent_of_timed
#check @Molt.sigUnforgeableRecent_of_timed
#print axioms Molt.sigUnforgeableRecent_of_timed

-- DECL: Molt.slot_time_necessary
#check @Molt.slot_time_necessary
#print axioms Molt.slot_time_necessary

-- DECL: Molt.slot_time_sufficient
#check @Molt.slot_time_sufficient
#print axioms Molt.slot_time_sufficient

-- DECL: Molt.stay_recent_client_safe
#check @Molt.stay_recent_client_safe
#print axioms Molt.stay_recent_client_safe

-- DECL: Molt.sync_induction_full_chain
#check @Molt.sync_induction_full_chain
#print axioms Molt.sync_induction_full_chain

-- DECL: Molt.sync_rule
#check @Molt.sync_rule
#print axioms Molt.sync_rule

-- DECL: Molt.sync_rule_mem
#check @Molt.sync_rule_mem
#print axioms Molt.sync_rule_mem

-- DECL: Molt.sync_rule_mem_timed
#check @Molt.sync_rule_mem_timed
#print axioms Molt.sync_rule_mem_timed

-- DECL: Molt.sync_rule_timed
#check @Molt.sync_rule_timed
#print axioms Molt.sync_rule_timed

-- DECL: Molt.timed_light_client_safety
#check @Molt.timed_light_client_safety
#print axioms Molt.timed_light_client_safety

-- DECL: Molt.validCertifiedChain
#check @Molt.validCertifiedChain
#print axioms Molt.validCertifiedChain

-- DECL: Molt.validChain
#check @Molt.validChain
#print axioms Molt.validChain

-- DECL: Molt.validChainK
#check @Molt.validChainK
#print axioms Molt.validChainK

-- DECL: Molt.validSignedChainK'
#check @Molt.validSignedChainK'
#print axioms Molt.validSignedChainK'

-- DECL: Molt.validSignedChainLock
#check @Molt.validSignedChainLock
#print axioms Molt.validSignedChainLock

-- DECL: Molt.validSignedChainSched
#check @Molt.validSignedChainSched
#print axioms Molt.validSignedChainSched

-- DECL: Molt.validSuffix
#check @Molt.validSuffix
#print axioms Molt.validSuffix

-- DECL: Molt.window_shared_prefix
#check @Molt.window_shared_prefix
#print axioms Molt.window_shared_prefix

-- DECL: MoltPetit.Model.Block.contentsHash
#check @MoltPetit.Model.Block.contentsHash
#print axioms MoltPetit.Model.Block.contentsHash

-- DECL: MoltPetit.Model.Block.id
#check @MoltPetit.Model.Block.id
#print axioms MoltPetit.Model.Block.id

-- DECL: MoltPetit.Model.Block.keyIndex
#check @MoltPetit.Model.Block.keyIndex
#print axioms MoltPetit.Model.Block.keyIndex

-- DECL: MoltPetit.Model.Block.prev
#check @MoltPetit.Model.Block.prev
#print axioms MoltPetit.Model.Block.prev

-- DECL: MoltPetit.Model.ByzantineBounded
#check @MoltPetit.Model.ByzantineBounded
#print axioms MoltPetit.Model.ByzantineBounded

-- DECL: MoltPetit.Model.CertOps
#check @MoltPetit.Model.CertOps
#print axioms MoltPetit.Model.CertOps

-- DECL: MoltPetit.Model.CertOps.verify
#check @MoltPetit.Model.CertOps.verify
#print axioms MoltPetit.Model.CertOps.verify

-- DECL: MoltPetit.Model.ErasureTimedLock
#check @MoltPetit.Model.ErasureTimedLock
#print axioms MoltPetit.Model.ErasureTimedLock

-- DECL: MoltPetit.Model.GroundedCert
#check @MoltPetit.Model.GroundedCert
#print axioms MoltPetit.Model.GroundedCert

-- DECL: MoltPetit.Model.GroundedCertK
#check @MoltPetit.Model.GroundedCertK
#print axioms MoltPetit.Model.GroundedCertK

-- DECL: MoltPetit.Model.GroundedCertSched
#check @MoltPetit.Model.GroundedCertSched
#print axioms MoltPetit.Model.GroundedCertSched

-- DECL: MoltPetit.Model.HonestBlocksCover
#check @MoltPetit.Model.HonestBlocksCover
#print axioms MoltPetit.Model.HonestBlocksCover

-- DECL: MoltPetit.Model.KeyRegistry
#check @MoltPetit.Model.KeyRegistry
#print axioms MoltPetit.Model.KeyRegistry

-- DECL: MoltPetit.Model.KeyStealingEUFCMA
#check @MoltPetit.Model.KeyStealingEUFCMA
#print axioms MoltPetit.Model.KeyStealingEUFCMA

-- DECL: MoltPetit.Model.KeyStealingSigned
#check @MoltPetit.Model.KeyStealingSigned
#print axioms MoltPetit.Model.KeyStealingSigned

-- DECL: MoltPetit.Model.LockstepPackage.toGen
#check @MoltPetit.Model.LockstepPackage.toGen
#print axioms MoltPetit.Model.LockstepPackage.toGen

-- DECL: MoltPetit.Model.NoBackdate
#check @MoltPetit.Model.NoBackdate
#print axioms MoltPetit.Model.NoBackdate

-- DECL: MoltPetit.Model.NoPrematureTheft
#check @MoltPetit.Model.NoPrematureTheft
#print axioms MoltPetit.Model.NoPrematureTheft

-- DECL: MoltPetit.Model.NoTheftBackdating
#check @MoltPetit.Model.NoTheftBackdating
#print axioms MoltPetit.Model.NoTheftBackdating

-- DECL: MoltPetit.Model.ProverTiming.recommended_slot_necessary
#check @MoltPetit.Model.ProverTiming.recommended_slot_necessary
#print axioms MoltPetit.Model.ProverTiming.recommended_slot_necessary

-- DECL: MoltPetit.Model.ProverTiming.recommended_slot_sufficient
#check @MoltPetit.Model.ProverTiming.recommended_slot_sufficient
#print axioms MoltPetit.Model.ProverTiming.recommended_slot_sufficient

-- DECL: MoltPetit.Model.Reacts
#check @MoltPetit.Model.Reacts
#print axioms MoltPetit.Model.Reacts

-- DECL: MoltPetit.Model.SchedCoreUnforgeable
#check @MoltPetit.Model.SchedCoreUnforgeable
#print axioms MoltPetit.Model.SchedCoreUnforgeable

-- DECL: MoltPetit.Model.SigOps
#check @MoltPetit.Model.SigOps
#print axioms MoltPetit.Model.SigOps

-- DECL: MoltPetit.Model.SigUnforgeableRecent
#check @MoltPetit.Model.SigUnforgeableRecent
#print axioms MoltPetit.Model.SigUnforgeableRecent

-- DECL: MoltPetit.Model.SignedDeclared
#check @MoltPetit.Model.SignedDeclared
#print axioms MoltPetit.Model.SignedDeclared

-- DECL: MoltPetit.Model.SignedEver
#check @MoltPetit.Model.SignedEver
#print axioms MoltPetit.Model.SignedEver

-- DECL: MoltPetit.Model.SignedHashInjective
#check @MoltPetit.Model.SignedHashInjective
#print axioms MoltPetit.Model.SignedHashInjective

-- DECL: MoltPetit.Model.TimedExecution
#check @MoltPetit.Model.TimedExecution
#print axioms MoltPetit.Model.TimedExecution

-- DECL: MoltPetit.Model.TimedExecution.chain_order
#check @MoltPetit.Model.TimedExecution.chain_order
#print axioms MoltPetit.Model.TimedExecution.chain_order

-- DECL: MoltPetit.Model.TimedExecution.honest_once
#check @MoltPetit.Model.TimedExecution.honest_once
#print axioms MoltPetit.Model.TimedExecution.honest_once

-- DECL: MoltPetit.Model.TimedExecution.honest_stamp
#check @MoltPetit.Model.TimedExecution.honest_stamp
#print axioms MoltPetit.Model.TimedExecution.honest_stamp

-- DECL: MoltPetit.Model.TimedExecution.id_inj
#check @MoltPetit.Model.TimedExecution.id_inj
#print axioms MoltPetit.Model.TimedExecution.id_inj

-- DECL: MoltPetit.Model.TimedExecution.key_match
#check @MoltPetit.Model.TimedExecution.key_match
#print axioms MoltPetit.Model.TimedExecution.key_match

-- DECL: MoltPetit.Model.badKeyrotOn
#check @MoltPetit.Model.badKeyrotOn
#print axioms MoltPetit.Model.badKeyrotOn

-- DECL: MoltPetit.Model.badKeyrotOn_lossOnly
#check @MoltPetit.Model.badKeyrotOn_lossOnly
#print axioms MoltPetit.Model.badKeyrotOn_lossOnly

-- DECL: MoltPetit.Model.badKeyrotOn_single_key_safe_not_enough
#check @MoltPetit.Model.badKeyrotOn_single_key_safe_not_enough
#print axioms MoltPetit.Model.badKeyrotOn_single_key_safe_not_enough

-- DECL: MoltPetit.Model.badSched
#check @MoltPetit.Model.badSched
#print axioms MoltPetit.Model.badSched

-- DECL: MoltPetit.Model.badSched_single_key_safe_not_enough
#check @MoltPetit.Model.badSched_single_key_safe_not_enough
#print axioms MoltPetit.Model.badSched_single_key_safe_not_enough

-- DECL: MoltPetit.Model.budget_of_reaction
#check @MoltPetit.Model.budget_of_reaction
#print axioms MoltPetit.Model.budget_of_reaction

-- DECL: MoltPetit.Model.budget_of_reaction_tight
#check @MoltPetit.Model.budget_of_reaction_tight
#print axioms MoltPetit.Model.budget_of_reaction_tight

-- DECL: MoltPetit.Model.exposedProducersSched
#check @MoltPetit.Model.exposedProducersSched
#print axioms MoltPetit.Model.exposedProducersSched

-- DECL: MoltPetit.Model.forged_chain_time_bound
#check @MoltPetit.Model.forged_chain_time_bound
#print axioms MoltPetit.Model.forged_chain_time_bound

-- DECL: MoltPetit.Model.forged_suffix_time_bound
#check @MoltPetit.Model.forged_suffix_time_bound
#print axioms MoltPetit.Model.forged_suffix_time_bound

-- DECL: MoltPetit.Model.genBound_of_preRetirementBound
#check @MoltPetit.Model.genBound_of_preRetirementBound
#print axioms MoltPetit.Model.genBound_of_preRetirementBound

-- DECL: MoltPetit.Model.genesisOk
#check @MoltPetit.Model.genesisOk
#print axioms MoltPetit.Model.genesisOk

-- DECL: MoltPetit.Model.groundedCertLock_gen_of_tail
#check @MoltPetit.Model.groundedCertLock_gen_of_tail
#print axioms MoltPetit.Model.groundedCertLock_gen_of_tail

-- DECL: MoltPetit.Model.groundedCertLock_gen_unique
#check @MoltPetit.Model.groundedCertLock_gen_unique
#print axioms MoltPetit.Model.groundedCertLock_gen_unique

-- DECL: MoltPetit.Model.inForce
#check @MoltPetit.Model.inForce
#print axioms MoltPetit.Model.inForce

-- DECL: MoltPetit.Model.keyMonoOk
#check @MoltPetit.Model.keyMonoOk
#print axioms MoltPetit.Model.keyMonoOk

-- DECL: MoltPetit.Model.keyrot_certified_suffix_agreement_anchored
#check @MoltPetit.Model.keyrot_certified_suffix_agreement_anchored
#print axioms MoltPetit.Model.keyrot_certified_suffix_agreement_anchored

-- DECL: MoltPetit.Model.keyrot_recent_certified_suffix_agreement
#check @MoltPetit.Model.keyrot_recent_certified_suffix_agreement
#print axioms MoltPetit.Model.keyrot_recent_certified_suffix_agreement

-- DECL: MoltPetit.Model.late_tail_short
#check @MoltPetit.Model.late_tail_short
#print axioms MoltPetit.Model.late_tail_short

-- DECL: MoltPetit.Model.linksOk
#check @MoltPetit.Model.linksOk
#print axioms MoltPetit.Model.linksOk

-- DECL: MoltPetit.Model.liveness_global
#check @MoltPetit.Model.liveness_global
#print axioms MoltPetit.Model.liveness_global

-- DECL: MoltPetit.Model.liveness_produce_block
#check @MoltPetit.Model.liveness_produce_block
#print axioms MoltPetit.Model.liveness_produce_block

-- DECL: MoltPetit.Model.liveness_produce_blockK
#check @MoltPetit.Model.liveness_produce_blockK
#print axioms MoltPetit.Model.liveness_produce_blockK

-- DECL: MoltPetit.Model.lockstepGen_recent_tip_ancestor_agreement
#check @MoltPetit.Model.lockstepGen_recent_tip_ancestor_agreement
#print axioms MoltPetit.Model.lockstepGen_recent_tip_ancestor_agreement

-- DECL: MoltPetit.Model.lockstepGen_recent_tip_ancestor_mem
#check @MoltPetit.Model.lockstepGen_recent_tip_ancestor_mem
#print axioms MoltPetit.Model.lockstepGen_recent_tip_ancestor_mem

-- DECL: MoltPetit.Model.lockstepGen_shared_prefix_sharp
#check @MoltPetit.Model.lockstepGen_shared_prefix_sharp
#print axioms MoltPetit.Model.lockstepGen_shared_prefix_sharp

-- DECL: MoltPetit.Model.lockstepOk
#check @MoltPetit.Model.lockstepOk
#print axioms MoltPetit.Model.lockstepOk

-- DECL: MoltPetit.Model.lockstepTimed_recent_tip_ancestor_agreement
#check @MoltPetit.Model.lockstepTimed_recent_tip_ancestor_agreement
#print axioms MoltPetit.Model.lockstepTimed_recent_tip_ancestor_agreement

-- DECL: MoltPetit.Model.lockstep_cert_gen_pinned
#check @MoltPetit.Model.lockstep_cert_gen_pinned
#print axioms MoltPetit.Model.lockstep_cert_gen_pinned

-- DECL: MoltPetit.Model.lockstep_declares_rosterGen
#check @MoltPetit.Model.lockstep_declares_rosterGen
#print axioms MoltPetit.Model.lockstep_declares_rosterGen

-- DECL: MoltPetit.Model.lockstep_recent_certified_suffix_agreement
#check @MoltPetit.Model.lockstep_recent_certified_suffix_agreement
#print axioms MoltPetit.Model.lockstep_recent_certified_suffix_agreement

-- DECL: MoltPetit.Model.lockstep_recent_tip_ancestor_agreement
#check @MoltPetit.Model.lockstep_recent_tip_ancestor_agreement
#print axioms MoltPetit.Model.lockstep_recent_tip_ancestor_agreement

-- DECL: MoltPetit.Model.lockstep_recent_tip_ancestor_mem
#check @MoltPetit.Model.lockstep_recent_tip_ancestor_mem
#print axioms MoltPetit.Model.lockstep_recent_tip_ancestor_mem

-- DECL: MoltPetit.Model.lockstep_window_declares_rosterGen
#check @MoltPetit.Model.lockstep_window_declares_rosterGen
#print axioms MoltPetit.Model.lockstep_window_declares_rosterGen

-- DECL: MoltPetit.Model.noBackdate_independent
#check @MoltPetit.Model.noBackdate_independent
#print axioms MoltPetit.Model.noBackdate_independent

-- DECL: MoltPetit.Model.producerForSlot
#check @MoltPetit.Model.producerForSlot
#print axioms MoltPetit.Model.producerForSlot

-- DECL: MoltPetit.Model.projectSigned
#check @MoltPetit.Model.projectSigned
#print axioms MoltPetit.Model.projectSigned

-- DECL: MoltPetit.Model.recent_certified_suffix_agreement
#check @MoltPetit.Model.recent_certified_suffix_agreement
#print axioms MoltPetit.Model.recent_certified_suffix_agreement

-- DECL: MoltPetit.Model.same_block_same_prefix
#check @MoltPetit.Model.same_block_same_prefix
#print axioms MoltPetit.Model.same_block_same_prefix

-- DECL: MoltPetit.Model.sched_oldkey_fork_stale
#check @MoltPetit.Model.sched_oldkey_fork_stale
#print axioms MoltPetit.Model.sched_oldkey_fork_stale

-- DECL: MoltPetit.Model.sched_recent_certified_suffix_agreement
#check @MoltPetit.Model.sched_recent_certified_suffix_agreement
#print axioms MoltPetit.Model.sched_recent_certified_suffix_agreement

-- DECL: MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon
#check @MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon
#print axioms MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon

-- DECL: MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon
#check @MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon
#print axioms MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon

-- DECL: MoltPetit.Model.selectCertifiedChain
#check @MoltPetit.Model.selectCertifiedChain
#print axioms MoltPetit.Model.selectCertifiedChain

-- DECL: MoltPetit.Model.sigUnforgeableRecent_of_timed
#check @MoltPetit.Model.sigUnforgeableRecent_of_timed
#print axioms MoltPetit.Model.sigUnforgeableRecent_of_timed

-- DECL: MoltPetit.Model.theft_exposure_window
#check @MoltPetit.Model.theft_exposure_window
#print axioms MoltPetit.Model.theft_exposure_window

-- DECL: MoltPetit.Model.timed_certified_agreement
#check @MoltPetit.Model.timed_certified_agreement
#print axioms MoltPetit.Model.timed_certified_agreement

-- DECL: MoltPetit.Model.validChain
#check @MoltPetit.Model.validChain
#print axioms MoltPetit.Model.validChain

-- DECL: MoltPetit.Model.validChainK
#check @MoltPetit.Model.validChainK
#print axioms MoltPetit.Model.validChainK

-- DECL: MoltPetit.Model.validSignedChainK'
#check @MoltPetit.Model.validSignedChainK'
#print axioms MoltPetit.Model.validSignedChainK'

-- DECL: MoltPetit.Model.validSignedChainLock
#check @MoltPetit.Model.validSignedChainLock
#print axioms MoltPetit.Model.validSignedChainLock

-- DECL: MoltPetit.Model.validSignedChainSched
#check @MoltPetit.Model.validSignedChainSched
#print axioms MoltPetit.Model.validSignedChainSched

-- DECL: MoltPetit.Model.validateCertifiedChain
#check @MoltPetit.Model.validateCertifiedChain
#print axioms MoltPetit.Model.validateCertifiedChain

-- DECL: MoltPetit.Model.validateSuffix
#check @MoltPetit.Model.validateSuffix
#print axioms MoltPetit.Model.validateSuffix

-- DECL: MoltPetit.Model.window_shared_prefix
#check @MoltPetit.Model.window_shared_prefix
#print axioms MoltPetit.Model.window_shared_prefix

-- DECL: Rust.rust_recent_tip_ancestor_mem
#check @Rust.rust_recent_tip_ancestor_mem
#print axioms Rust.rust_recent_tip_ancestor_mem

-- DECL: Rust.rust_timed_certified_agreement
#check @Rust.rust_timed_certified_agreement
#print axioms Rust.rust_timed_certified_agreement

-- DECL: Rust.rust_valid_chain_k_sound
#check @Rust.rust_valid_chain_k_sound
#print axioms Rust.rust_valid_chain_k_sound

-- DECL: Rust.rust_valid_chain_sound
#check @Rust.rust_valid_chain_sound
#print axioms Rust.rust_valid_chain_sound

-- DECL: Rust.valid_chain_be_validChain
#check @Rust.valid_chain_be_validChain
#print axioms Rust.valid_chain_be_validChain

-- DECL: molt_petit.valid_chain_be
#check @molt_petit.valid_chain_be
#print axioms molt_petit.valid_chain_be

