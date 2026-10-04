import Paper.Statements

/-!
# The paper's results, proved

Each result `xxx` that `paper/molt.tex` cites is the theorem
`MoltPaper.xxx : MoltPaper.thm_xxx` below, proved by the development's own
theorem. `tools/paper-bundle.sh` checks that every theorem the paper cites
appears here and depends on no axiom beyond `propext`, `Classical.choice`
and `Quot.sound`.
-/

namespace MoltPaper

theorem badKeyrot_single_key_safe_not_enough : thm_badKeyrot_single_key_safe_not_enough :=
  @MoltPetit.Model.badKeyrotOn_single_key_safe_not_enough
theorem badSched_single_key_safe_not_enough : thm_badSched_single_key_safe_not_enough :=
  @MoltPetit.Model.badSched_single_key_safe_not_enough
theorem exposure_agreement_ever_on : thm_exposure_agreement_ever_on :=
  @MoltPetit.Model.exposure_agreement_ever_on
theorem exposure_agreement_on : thm_exposure_agreement_on :=
  @MoltPetit.Model.exposure_agreement_on
theorem exposure_certified_agreement_on : thm_exposure_certified_agreement_on :=
  @MoltPetit.Model.exposure_certified_agreement_on
theorem exposure_no_early_signing_ever_on : thm_exposure_no_early_signing_ever_on :=
  @MoltPetit.Model.exposure_no_early_signing_ever_on
theorem exposure_no_early_signing_on : thm_exposure_no_early_signing_on :=
  @MoltPetit.Model.exposure_no_early_signing_on
theorem global_liveness : thm_global_liveness :=
  @MoltPetit.Model.liveness_global
theorem groundedCertLock_gen_of_tail : thm_groundedCertLock_gen_of_tail :=
  @MoltPetit.Model.groundedCertLock_gen_of_tail
theorem groundedCertLock_gen_unique : thm_groundedCertLock_gen_unique :=
  @MoltPetit.Model.groundedCertLock_gen_unique
theorem keyrot_loss_agreement : thm_keyrot_loss_agreement :=
  @MoltPetit.Model.keyrot_loss_agreement
theorem liveness_produce_blockK : thm_liveness_produce_blockK :=
  @MoltPetit.Model.liveness_produce_blockK
theorem lockstepGen_recent_certified_suffix_agreement : thm_lockstepGen_recent_certified_suffix_agreement :=
  @MoltPetit.Model.lockstepGen_recent_certified_suffix_agreement
theorem lockstep_cert_gen_pinned : thm_lockstep_cert_gen_pinned :=
  @MoltPetit.Model.lockstep_cert_gen_pinned
theorem lockstep_declares_rosterGen : thm_lockstep_declares_rosterGen :=
  @MoltPetit.Model.lockstep_declares_rosterGen
theorem lockstep_loss_agreement : thm_lockstep_loss_agreement :=
  @MoltPetit.Model.lockstep_loss_agreement
theorem lockstep_recent_certified_suffix_agreement : thm_lockstep_recent_certified_suffix_agreement :=
  @MoltPetit.Model.lockstep_recent_certified_suffix_agreement
theorem lockstep_recent_tip_ancestor_mem : thm_lockstep_recent_tip_ancestor_mem :=
  @MoltPetit.Model.lockstep_recent_tip_ancestor_mem
theorem no_early_signing : thm_no_early_signing :=
  @MoltPetit.Model.exposure_no_early_signing_on
theorem production_liveness : thm_production_liveness :=
  @MoltPetit.Model.liveness_produce_block
theorem same_block_same_prefix : thm_same_block_same_prefix :=
  @MoltPetit.Model.same_block_same_prefix
theorem sched_exposure_agreement : thm_sched_exposure_agreement :=
  @MoltPetit.Model.sched_exposure_agreement
theorem sched_exposure_certified_agreement : thm_sched_exposure_certified_agreement :=
  @MoltPetit.Model.sched_exposure_certified_agreement
theorem sched_loss_agreement : thm_sched_loss_agreement :=
  @MoltPetit.Model.sched_loss_agreement
theorem sched_oldkey_fork_stale : thm_sched_oldkey_fork_stale :=
  @MoltPetit.Model.sched_oldkey_fork_stale
theorem sched_recent_certified_suffix_agreement_horizon : thm_sched_recent_certified_suffix_agreement_horizon :=
  @MoltPetit.Model.sched_recent_certified_suffix_agreement_horizon
theorem sched_recent_genesis_agreement_horizon : thm_sched_recent_genesis_agreement_horizon :=
  @MoltPetit.Model.sched_recent_genesis_agreement_horizon
theorem sched_recent_tip_ancestor_agreement_horizon : thm_sched_recent_tip_ancestor_agreement_horizon :=
  @MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon
theorem sched_recent_tip_ancestor_mem_horizon : thm_sched_recent_tip_ancestor_mem_horizon :=
  @MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon
theorem ts_timed_certified_agreement : thm_ts_timed_certified_agreement :=
  @MoltPetit.Model.ts_timed_certified_agreement
theorem window_shared_prefix : thm_window_shared_prefix :=
  @MoltPetit.Model.window_shared_prefix
theorem LockstepPackage.toGen : LockstepPackage.thm_toGen :=
  @MoltPetit.Model.LockstepPackage.toGen
theorem genBound_of_preRetirementBound : thm_genBound_of_preRetirementBound :=
  @MoltPetit.Model.genBound_of_preRetirementBound
theorem lockstepGen_recent_genesis_agreement : thm_lockstepGen_recent_genesis_agreement :=
  @MoltPetit.Model.lockstepGen_recent_genesis_agreement
theorem lockstepGen_recent_tip_ancestor_mem : thm_lockstepGen_recent_tip_ancestor_mem :=
  @MoltPetit.Model.lockstepGen_recent_tip_ancestor_mem
theorem lockstepGen_shared_prefix_sharp : thm_lockstepGen_shared_prefix_sharp :=
  @MoltPetit.Model.lockstepGen_shared_prefix_sharp
theorem lockstep_window_declares_rosterGen : thm_lockstep_window_declares_rosterGen :=
  @MoltPetit.Model.lockstep_window_declares_rosterGen
theorem slot_time_necessary : thm_slot_time_necessary :=
  @MoltPetit.Model.ProverTiming.recommended_slot_necessary
theorem slot_time_sufficient : thm_slot_time_sufficient :=
  @MoltPetit.Model.ProverTiming.recommended_slot_sufficient
theorem badKeyrot_lossOnly : thm_badKeyrot_lossOnly :=
  @Molt.badKeyrot_lossOnly
theorem badSched_lossOnly : thm_badSched_lossOnly :=
  @Molt.badSched_lossOnly
theorem lockstep_client_safety : thm_lockstep_client_safety :=
  @Molt.lockstep_client_safety
theorem lockstep_client_safety_gen : thm_lockstep_client_safety_gen :=
  @Molt.lockstep_client_safety_gen
theorem lockstep_client_safety_timed : thm_lockstep_client_safety_timed :=
  @Molt.lockstep_client_safety_timed
theorem timed_light_client_safety : thm_timed_light_client_safety :=
  @Molt.timed_light_client_safety
theorem rust_timed_certified_agreement : thm_rust_timed_certified_agreement :=
  @Rust.rust_timed_certified_agreement
theorem rust_valid_chain_k_sound : thm_rust_valid_chain_k_sound :=
  @Rust.rust_valid_chain_k_sound
theorem rust_valid_chain_sound : thm_rust_valid_chain_sound :=
  @Rust.rust_valid_chain_sound
theorem valid_chain_be_validChain : thm_valid_chain_be_validChain :=
  @Rust.valid_chain_be_validChain

end MoltPaper
