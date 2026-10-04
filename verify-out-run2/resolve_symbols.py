import subprocess
import re

symbols = """
CertOps
CertOps.verify
ErasureTimedLock
FaultBounded
GroundedCert
GroundedCertK
GroundedCertSched
HonestBlocksCover
KeyRegistry
KeyStealingEUFCMA
KeyStealingSigned
LockstepPackage.toGen
NoBackdate
NoPrematureTheft
NoTheftBackdating
Reacts
SchedCoreUnforgeable
SigOps
SigUnforgeableRecent
SignedDeclared
SignedHashInjective
SigningLog
TimedExecution
badKeyrot
badKeyrot_lossOnly
badKeyrot_single_key_safe_not_enough
badSched_lossOnly
badSched_single_key_safe_not_enough
budget_of_reaction
census_accumulates
census_accumulates_later_thefts
cert_max_sync_period
cert_sync_rule
chain_order
client_refresh_rule
contentsHash
deep_block_span
denseSoFar
exposedSched_lossOnly
forged_chain_time_bound
forged_time_bound
genBound_of_preRetirementBound
genesisOk
global_liveness
groundedCertLock_gen_of_tail
groundedCertLock_gen_unique
id
inForce
inForce_mono
keyIndex
keyMonoOk
keyrot_certified_suffix_agreement_anchored
keyrot_recent_certified_suffix_agreement
light_client_safety
linksOk
liveness_produce_blockK
lockstepGen_recent_genesis_agreement
lockstepGen_shared_prefix_sharp
lockstep_cert_gen_pinned
lockstep_client_safety
lockstep_client_safety_gen
lockstep_client_safety_timed
lockstep_declares_rosterGen
lockstep_recent_certified_suffix_agreement
lockstep_recent_tip_ancestor_mem
lockstep_window_declares_rosterGen
max_sync_period
max_sync_period_tight
max_sync_period_timed
noBackdate_independent
noMixing
no_budget_beyond
paced_budget_holds_under_timing
paced_tight_census_bound_all_F
prev
produceBlock?
producer
production_liveness
projectSigned
rust_recent_tip_ancestor_mem
rust_valid_chain_k_sound
rust_valid_chain_sound
same_block_same_prefix
sched_oldkey_fork_stale
sched_recent_certified_suffix_agreement
sched_recent_tip_ancestor_agreement_horizon
sched_recent_tip_ancestor_mem
sched_recent_tip_ancestor_mem_horizon
scheduled_client_safety
selectChain
sigUnforgeableRecent_of_timed
slot_time_necessary
slot_time_sufficient
stay_recent_client_safe
sync_induction_full_chain
sync_rule
sync_rule_mem
sync_rule_timed
theft_exposure_window
validCertifiedChain
validChain
validChainK
validChainK_structural
validSignedChainK'
validSignedChainLock
validSignedChainSched
validSuffix
valid_chain_be
valid_chain_be_validChain
window_shared_prefix
""".strip().splitlines()

# We test prefixes for each symbol:
# Molt.<sym>, Molt.Block.<sym>, MoltPetit.Model.<sym>, MoltPetit.Model.Block.<sym>, Rust.<sym>, molt_petit.<sym>
candidates = []
for s in symbols:
    if s in ['id', 'prev', 'contentsHash', 'keyIndex']:
        candidates.append((s, [f"Molt.Block.{s}", f"MoltPetit.Model.Block.{s}"]))
    elif s == 'CertOps.verify':
        candidates.append((s, ["Molt.CertOps.verify", "MoltPetit.Model.CertOps.verify"]))
    elif s == 'LockstepPackage.toGen':
        candidates.append((s, ["Molt.LockstepPackage.toGen", "MoltPetit.Model.LockstepPackage.toGen"]))
    elif s.startswith('rust_'):
        candidates.append((s, [f"Rust.{s}"]))
    elif s == 'valid_chain_be':
        candidates.append((s, ["molt_petit.valid_chain_be", "Rust.valid_chain_be"]))
    elif s == 'valid_chain_be_validChain':
        candidates.append((s, ["Rust.valid_chain_be_validChain"]))
    else:
        candidates.append((s, [f"Molt.{s}", f"MoltPetit.Model.{s}"]))

# Generate a Lean file to test all candidates
lines = [
    "import Molt",
    "import MoltPetit",
    "import Rust",
    ""
]

for s, opts in candidates:
    for opt in opts:
        lines.append(f"-- TEST: {s} -> {opt}")
        lines.append(f"#check @{opt}")

with open("verify-out/test_resolution.lean", "w") as f:
    f.write("\n".join(lines))

print(f"Generated verify-out/test_resolution.lean with {len(lines)} lines")
