import json
import re

# Complete symbol map:
# symbol -> (lean_decl, lean_resolved)
sym_map = {
    'ByzantineBounded': ('Molt.ByzantineBounded', 'MoltPetit.Model.ByzantineBounded'),
    'CertOps': ('Molt.CertOps', 'MoltPetit.Model.CertOps'),
    'CertOps.verify': ('MoltPetit.Model.CertOps.verify', 'MoltPetit.Model.CertOps.verify'),
    'ErasureTimedLock': ('Molt.ErasureTimedLock', 'MoltPetit.Model.ErasureTimedLock'),
    'FaultBounded': ('Molt.FaultBounded', 'MoltPetit.Model.ByzantineBounded'),
    'GroundedCert': ('Molt.GroundedCert', 'MoltPetit.Model.GroundedCert'),
    'GroundedCertK': ('Molt.GroundedCertK', 'MoltPetit.Model.GroundedCertK'),
    'GroundedCertSched': ('Molt.GroundedCertSched', 'MoltPetit.Model.GroundedCertSched'),
    'HonestBlocksCover': ('Molt.HonestBlocksCover', 'MoltPetit.Model.HonestBlocksCover'),
    'KeyRegistry': ('Molt.KeyRegistry', 'MoltPetit.Model.KeyRegistry'),
    'KeyStealingEUFCMA': ('Molt.KeyStealingEUFCMA', 'MoltPetit.Model.KeyStealingEUFCMA'),
    'KeyStealingSigned': ('Molt.KeyStealingSigned', 'MoltPetit.Model.KeyStealingSigned'),
    'LockstepPackage.toGen': ('Molt.LockstepPackage.toGen', 'MoltPetit.Model.LockstepPackage.toGen'),
    'NoBackdate': ('Molt.NoBackdate', 'MoltPetit.Model.NoBackdate'),
    'NoPrematureTheft': ('Molt.NoPrematureTheft', 'MoltPetit.Model.NoPrematureTheft'),
    'NoTheftBackdating': ('Molt.NoTheftBackdating', 'MoltPetit.Model.NoTheftBackdating'),
    'Reacts': ('Molt.Reacts', 'MoltPetit.Model.Reacts'),
    'SchedCoreUnforgeable': ('Molt.SchedCoreUnforgeable', 'MoltPetit.Model.SchedCoreUnforgeable'),
    'SchedUnforgeable': ('Molt.SchedUnforgeable', 'MoltPetit.Model.SchedUnforgeable'),
    'SigOps': ('Molt.SigOps', 'MoltPetit.Model.SigOps'),
    'SigUnforgeableRecent': ('Molt.SigUnforgeableRecent', 'MoltPetit.Model.SigUnforgeableRecent'),
    'SignedDeclared': ('Molt.SignedDeclared', 'MoltPetit.Model.SignedDeclared'),
    'SignedEver': ('MoltPetit.Model.SignedEver', 'MoltPetit.Model.SignedEver'),
    'SignedHashInjective': ('Molt.SignedHashInjective', 'MoltPetit.Model.SignedHashInjective'),
    'TimedExecution': ('Molt.TimedExecution', 'MoltPetit.Model.TimedExecution'),
    'TimedExecution.id_inj': ('MoltPetit.Model.TimedExecution.id_inj', 'MoltPetit.Model.TimedExecution.id_inj'),
    'badKeyrot': ('Molt.badKeyrot', 'MoltPetit.Model.badKeyrotOn'),
    'badKeyrot_lossOnly': ('Molt.badKeyrot_lossOnly', 'MoltPetit.Model.badKeyrotOn_lossOnly'),
    'badKeyrot_single_key_safe_not_enough': ('Molt.badKeyrot_single_key_safe_not_enough', 'MoltPetit.Model.badKeyrotOn_single_key_safe_not_enough'),
    'badSched': ('Molt.badSched_lossOnly', 'MoltPetit.Model.badSched'),
    'badSched_lossOnly': ('Molt.badSched_lossOnly', 'MoltPetit.Model.badSched'),
    'badSched_single_key_safe_not_enough': ('Molt.badSched_single_key_safe_not_enough', 'MoltPetit.Model.badSched_single_key_safe_not_enough'),
    'badSlotsIn': ('MoltPetit.Model.badSlotsIn', 'MoltPetit.Model.badSlotsIn'),
    'budget_of_reaction': ('MoltPetit.Model.budget_of_reaction', 'MoltPetit.Model.budget_of_reaction'),
    'byzantineBoundedFrom_of_bounded': ('MoltPetit.Model.byzantineBoundedFrom_of_bounded', 'MoltPetit.Model.byzantineBoundedFrom_of_bounded'),
    'census_accumulates': ('Molt.census_accumulates', 'Molt.census_accumulates'),
    'census_accumulates_later_thefts': ('Molt.census_accumulates_later_thefts', 'Molt.census_accumulates_later_thefts'),
    'cert_max_sync_period': ('Molt.cert_max_sync_period', 'Molt.cert_max_sync_period'),
    'cert_sync_rule': ('Molt.cert_sync_rule', 'Molt.cert_sync_rule'),
    'chain_order': ('MoltPetit.Model.TimedExecution.chain_order', 'MoltPetit.Model.TimedExecution.chain_order'),
    'client_refresh_rule': ('Molt.client_refresh_rule', 'Molt.client_refresh_rule'),
    'contentsHash': ('MoltPetit.Model.Block.contentsHash', 'MoltPetit.Model.Block.contentsHash'),
    'deep_block_span': ('Molt.deep_block_span', 'Molt.deep_block_span'),
    'denseSoFar': ('Molt.denseSoFar', 'Molt.denseSoFar'),
    'exposedSched_lossOnly': ('Molt.exposedSched_lossOnly', 'MoltPetit.Model.exposedProducersSched'),
    'forged_chain_time_bound': ('Molt.forged_chain_time_bound', 'MoltPetit.Model.forged_chain_time_bound'),
    'forged_time_bound': ('Molt.forged_time_bound', 'MoltPetit.Model.forged_suffix_time_bound'),
    'genBound_of_preRetirementBound': ('Molt.genBound_of_preRetirementBound', 'MoltPetit.Model.genBound_of_preRetirementBound'),
    'genesisOk': ('Molt.genesisOk', 'MoltPetit.Model.genesisOk'),
    'global_liveness': ('Molt.global_liveness', 'MoltPetit.Model.liveness_global'),
    'groundedCertLock_gen_of_tail': ('Molt.groundedCertLock_gen_of_tail', 'MoltPetit.Model.groundedCertLock_gen_of_tail'),
    'groundedCertLock_gen_unique': ('Molt.groundedCertLock_gen_unique', 'MoltPetit.Model.groundedCertLock_gen_unique'),
    'honest_once': ('MoltPetit.Model.TimedExecution.honest_once', 'MoltPetit.Model.TimedExecution.honest_once'),
    'honest_stamp': ('MoltPetit.Model.TimedExecution.honest_stamp', 'MoltPetit.Model.TimedExecution.honest_stamp'),
    'id': ('MoltPetit.Model.Block.id', 'MoltPetit.Model.Block.id'),
    'inForce': ('Molt.inForce', 'MoltPetit.Model.inForce'),
    'inForce_mono': ('Molt.inForce_mono', 'Molt.inForce_mono'),
    'keyIndex': ('MoltPetit.Model.Block.keyIndex', 'MoltPetit.Model.Block.keyIndex'),
    'keyMonoOk': ('Molt.keyMonoOk', 'MoltPetit.Model.keyMonoOk'),
    'key_match': ('MoltPetit.Model.TimedExecution.key_match', 'MoltPetit.Model.TimedExecution.key_match'),
    'keyrot_certified_suffix_agreement_anchored': ('Molt.keyrot_certified_suffix_agreement_anchored', 'MoltPetit.Model.keyrot_certified_suffix_agreement_anchored'),
    'keyrot_recent_certified_suffix_agreement': ('Molt.keyrot_recent_certified_suffix_agreement', 'MoltPetit.Model.keyrot_recent_certified_suffix_agreement'),
    'late_tail_short': ('MoltPetit.Model.late_tail_short', 'MoltPetit.Model.late_tail_short'),
    'light_client_safety': ('Molt.light_client_safety', 'MoltPetit.Model.recent_certified_suffix_agreement'),
    'Molt.light_client_safety': ('Molt.light_client_safety', 'MoltPetit.Model.recent_certified_suffix_agreement'),
    'linksOk': ('Molt.linksOk', 'MoltPetit.Model.linksOk'),
    'liveness_produce_blockK': ('Molt.liveness_produce_blockK', 'MoltPetit.Model.liveness_produce_blockK'),
    'lockstepGen_recent_genesis_agreement': ('Molt.lockstepGen_recent_genesis_agreement', 'MoltPetit.Model.lockstepGen_recent_genesis_agreement'),
    'lockstepGen_recent_tip_ancestor_mem': ('Molt.lockstepGen_recent_tip_ancestor_mem', 'MoltPetit.Model.lockstepGen_recent_tip_ancestor_mem'),
    'lockstepGen_shared_prefix_sharp': ('Molt.lockstepGen_shared_prefix_sharp', 'MoltPetit.Model.lockstepGen_shared_prefix_sharp'),
    'lockstep_cert_gen_pinned': ('Molt.lockstep_cert_gen_pinned', 'MoltPetit.Model.lockstep_cert_gen_pinned'),
    'lockstep_client_safety': ('Molt.lockstep_client_safety', 'MoltPetit.Model.lockstep_recent_tip_ancestor_agreement'),
    'lockstep_client_safety_gen': ('Molt.lockstep_client_safety_gen', 'MoltPetit.Model.lockstepGen_recent_tip_ancestor_agreement'),
    'lockstep_client_safety_timed': ('Molt.lockstep_client_safety_timed', 'MoltPetit.Model.lockstepTimed_recent_tip_ancestor_agreement'),
    'lockstep_declares_rosterGen': ('Molt.lockstep_declares_rosterGen', 'MoltPetit.Model.lockstep_declares_rosterGen'),
    'lockstep_recent_certified_suffix_agreement': ('Molt.lockstep_recent_certified_suffix_agreement', 'MoltPetit.Model.lockstep_recent_certified_suffix_agreement'),
    'lockstep_recent_tip_ancestor_mem': ('Molt.lockstep_recent_tip_ancestor_mem', 'MoltPetit.Model.lockstep_recent_tip_ancestor_mem'),
    'lockstep_window_declares_rosterGen': ('Molt.lockstep_window_declares_rosterGen', 'MoltPetit.Model.lockstep_window_declares_rosterGen'),
    'max_sync_period': ('Molt.max_sync_period', 'Molt.max_sync_period'),
    'max_sync_period_tight': ('Molt.max_sync_period_tight', 'MoltPetit.Model.budget_of_reaction_tight'),
    'max_sync_period_timed': ('Molt.max_sync_period_timed', 'Molt.max_sync_period_timed'),
    'noBackdate_independent': ('Molt.noBackdate_independent', 'MoltPetit.Model.noBackdate_independent'),
    'noMixing': ('Molt.noMixing', 'MoltPetit.Model.lockstepOk'),
    'no_budget_beyond': ('Molt.no_budget_beyond', 'Molt.no_budget_beyond'),
    'paced_budget_holds_under_timing': ('Molt.paced_budget_holds_under_timing', 'Molt.paced_budget_holds_under_timing'),
    'paced_tight_census_bound_all_F': ('Molt.paced_tight_census_bound_all_F', 'Molt.paced_tight_census_bound_all_F'),
    'prev': ('MoltPetit.Model.Block.prev', 'MoltPetit.Model.Block.prev'),
    'produceBlock?': ('Molt.produceBlock?', 'MoltPetit.Model.produceBlockCert?'),
    'producer': ('Molt.producer', 'MoltPetit.Model.producerForSlot'),
    'production_liveness': ('Molt.production_liveness', 'MoltPetit.Model.liveness_produce_block'),
    'projectSigned': ('Molt.projectSigned', 'MoltPetit.Model.projectSigned'),
    'rust_recent_tip_ancestor_mem': ('Rust.rust_recent_tip_ancestor_mem', 'Rust.rust_recent_tip_ancestor_mem'),
    'rust_timed_certified_agreement': ('Rust.rust_timed_certified_agreement', 'Rust.rust_timed_certified_agreement'),
    'Rust.rust_timed_certified_agreement': ('Rust.rust_timed_certified_agreement', 'Rust.rust_timed_certified_agreement'),
    'rust_valid_chain_k_sound': ('Rust.rust_valid_chain_k_sound', 'Rust.rust_valid_chain_k_sound'),
    'rust_valid_chain_sound': ('Rust.rust_valid_chain_sound', 'Rust.rust_valid_chain_sound'),
    'same_block_same_prefix': ('Molt.same_block_same_prefix', 'MoltPetit.Model.same_block_same_prefix'),
    'sched_oldkey_fork_stale': ('Molt.sched_oldkey_fork_stale', 'MoltPetit.Model.sched_oldkey_fork_stale'),
    'sched_recent_certified_suffix_agreement': ('Molt.sched_recent_certified_suffix_agreement', 'MoltPetit.Model.sched_recent_certified_suffix_agreement'),
    'sched_recent_genesis_agreement_horizon': ('Molt.sched_recent_genesis_agreement_horizon', 'MoltPetit.Model.sched_recent_genesis_agreement_horizon'),
    'sched_recent_tip_ancestor_agreement_horizon': ('Molt.sched_recent_tip_ancestor_agreement_horizon', 'MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon'),
    'sched_recent_tip_ancestor_mem': ('Molt.sched_recent_tip_ancestor_mem', 'MoltPetit.Model.sched_recent_tip_ancestor_mem'),
    'sched_recent_tip_ancestor_mem_horizon': ('Molt.sched_recent_tip_ancestor_mem_horizon', 'MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon'),
    'scheduled_client_safety': ('Molt.scheduled_client_safety', 'MoltPetit.Model.sched_recent_tip_ancestor_agreement'),
    'selectChain': ('Molt.selectChain', 'MoltPetit.Model.selectCertifiedChain'),
    'sigUnforgeableRecent_of_timed': ('Molt.sigUnforgeableRecent_of_timed', 'MoltPetit.Model.sigUnforgeableRecent_of_timed'),
    'slot_time_necessary': ('Molt.slot_time_necessary', 'MoltPetit.Model.ProverTiming.recommended_slot_necessary'),
    'slot_time_sufficient': ('Molt.slot_time_sufficient', 'MoltPetit.Model.ProverTiming.recommended_slot_sufficient'),
    'stay_recent_client_safe': ('Molt.stay_recent_client_safe', 'Molt.stay_recent_client_safe'),
    'sync_induction_full_chain': ('Molt.sync_induction_full_chain', 'Molt.sync_induction_full_chain'),
    'sync_rule': ('Molt.sync_rule', 'Molt.sync_rule'),
    'sync_rule_mem': ('Molt.sync_rule_mem', 'Molt.sync_rule_mem'),
    'sync_rule_mem_timed': ('Molt.sync_rule_mem_timed', 'Molt.sync_rule_mem_timed'),
    'sync_rule_timed': ('Molt.sync_rule_timed', 'Molt.sync_rule_timed'),
    'theft_exposure_window': ('MoltPetit.Model.theft_exposure_window', 'MoltPetit.Model.theft_exposure_window'),
    'timed_light_client_safety': ('Molt.timed_light_client_safety', 'MoltPetit.Model.timed_certified_agreement'),
    'validCertifiedChain': ('Molt.validCertifiedChain', 'MoltPetit.Model.validateCertifiedChain'),
    'validChain': ('Molt.validChain', 'MoltPetit.Model.validChain'),
    'validChainK': ('Molt.validChainK', 'MoltPetit.Model.validChainK'),
    'validChainK_structural': ('Molt.validChainK_structural', 'MoltPetit.Model.validChainK_sound'),
    "validSignedChainK'": ("Molt.validSignedChainK'", "MoltPetit.Model.validSignedChainK'"),
    'validSignedChainLock': ('Molt.validSignedChainLock', 'MoltPetit.Model.validSignedChainLock'),
    'validSignedChainSched': ('Molt.validSignedChainSched', 'MoltPetit.Model.validSignedChainSched'),
    'validSuffix': ('Molt.validSuffix', 'MoltPetit.Model.validateSuffix'),
    'valid_chain_be': ('molt_petit.valid_chain_be', 'molt_petit.valid_chain_be'),
    'valid_chain_be_validChain': ('Rust.valid_chain_be_validChain', 'Rust.valid_chain_be_validChain'),
    'window_shared_prefix': ('Molt.window_shared_prefix', 'MoltPetit.Model.window_shared_prefix'),
}

with open("verify-out/claims-draft.json") as f:
    claims = json.load(f)

# Theorem overrides
thm_mappings = {
    'C48': (['Molt.timed_light_client_safety'], ['MoltPetit.Model.timed_certified_agreement'],
            "Theorem 1: headline timed light client safety."),
    'C53': (['Molt.forged_time_bound', 'Molt.forged_chain_time_bound'],
            ['MoltPetit.Model.forged_suffix_time_bound', 'MoltPetit.Model.forged_chain_time_bound'],
            "Theorem 2: forged suffixes advance at half speed."),
    'C62': (['Molt.sync_rule_timed', 'Molt.sync_rule_mem_timed'],
            ['Molt.sync_rule_timed', 'Molt.sync_rule_mem_timed'],
            "Theorem 3: client sync rule (timed confirmation depth and membership forms)."),
    'C79': (['Molt.sched_recent_tip_ancestor_agreement_horizon', 'Molt.sched_recent_tip_ancestor_mem_horizon'],
            ['MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon', 'MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon'],
            "Theorem 4: scheduled safety under horizon budget (agreement and ancestor membership)."),
    'C86': (['Molt.lockstep_client_safety', 'Molt.lockstep_recent_tip_ancestor_mem'],
            ['MoltPetit.Model.lockstep_recent_tip_ancestor_agreement', 'MoltPetit.Model.lockstep_recent_tip_ancestor_mem'],
            "Theorem 5: lockstep safety."),
    'C88': (['Molt.lockstep_client_safety_gen', 'Molt.lockstepGen_recent_tip_ancestor_mem'],
            ['MoltPetit.Model.lockstepGen_recent_tip_ancestor_agreement', 'MoltPetit.Model.lockstepGen_recent_tip_ancestor_mem'],
            "Theorem 6: lockstep safety, per-generation census."),
    'C99': (['Molt.production_liveness', 'Molt.global_liveness'],
            ['MoltPetit.Model.liveness_produce_block', 'MoltPetit.Model.liveness_global'],
            "Theorem 7: liveness (local production and global liveness)."),
    'C115': (['Molt.sigUnforgeableRecent_of_timed'],
             ['MoltPetit.Model.sigUnforgeableRecent_of_timed'],
             "Theorem 8: untimed residue derived in timed model.")
}

all_needed_decls = set()

for c in claims:
    cid = c['id']
    if cid in thm_mappings:
        decls, resolved, note = thm_mappings[cid]
        c['lean_decls'] = decls
        c['lean_resolved'] = resolved
        c['notes'] = note
    else:
        decls = []
        resolved = []
        notes = []
        for code in c.get('raw_codes', []):
            sym = code.replace(r'\_', '_').replace('$', '').strip()
            if sym in sym_map:
                d, r = sym_map[sym]
                if d not in decls:
                    decls.append(d)
                if r not in resolved:
                    resolved.append(r)
            elif sym in {'hbridge', 'hA', 'hA\'', 'hAnchor', 'hCadence', 'hDense', 'hEUF', 'hHash', 'hLe', 'hLink', 'hLinks', 'hLong', 'hRT', 'hReacts', 'hRecent', 'hRecent\'', 'hRent', 'hSigned', 'hTheft', 'hTipHeight', 'hVPrev', 'hVal', 'hVal\''}:
                notes.append(f"Cites theorem hypothesis parameter `{sym}`.")
            else:
                notes.append(f"Unmapped symbol `{sym}`.")
        
        c['lean_decls'] = decls
        c['lean_resolved'] = resolved
        if not decls and not notes:
            if c.get('has_kw'):
                c['notes'] = "High-level prose assertion summarizing formal results."
            else:
                c['notes'] = "Informal context or descriptive assertion."
        elif notes:
            c['notes'] = "; ".join(notes)
        else:
            c['notes'] = f"Prose claim referencing {', '.join(decls)}."

    for d in c['lean_decls']:
        all_needed_decls.add(d)
    for r in c['lean_resolved']:
        all_needed_decls.add(r)

print(f"Total claims processed: {len(claims)}")
print(f"Total unique Lean declarations to check: {len(all_needed_decls)}")

with open("verify-out/claims-draft.json", "w") as f:
    json.dump(claims, f, indent=2)

# Generate verify-out/Stmts.lean
stmts_lean = """import Molt
import MoltPetit
import Rust

set_option pp.all false
set_option pp.fullNames true

"""

for d in sorted(all_needed_decls):
    stmts_lean += f"-- DECL: {d}\n"
    stmts_lean += f"#check @{d}\n"
    stmts_lean += f"#print axioms {d}\n\n"

with open("verify-out/Stmts.lean", "w") as f:
    f.write(stmts_lean)

print("Saved verify-out/claims-draft.json and verify-out/Stmts.lean")
