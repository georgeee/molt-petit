import MoltPetit.Results.Results
import MoltPetit.TS.Results
import MoltPetit.Model.Liveness
import MoltPetit.Model.Safety
import MoltPetit.Model.TimedSig
import MoltPetit.Model.KeyIndex
import MoltPetit.Model.KeyRotation
import MoltPetit.Model.KeyStealing
import MoltPetit.Model.KeyStealingSafety
import MoltPetit.Model.KeyStealingUnique
import MoltPetit.Results.KeyStealingResults
import MoltPetit.Model.KeyStealingCert
import MoltPetit.Model.KeyRotationLiveness
import MoltPetit.Model.KeyStealingBudget
import MoltPetit.Model.KeyStealingLongRange
import MoltPetit.TS.BridgeK
import MoltPetit.Model.KeyStealingSchedule
import MoltPetit.Results.KeyStealingScheduleResults
import MoltPetit.Model.KeyStealingLockstep
import MoltPetit.Model.KeyStealingHorizonCore
import MoltPetit.Model.KeyStealingHorizon
import MoltPetit.Model.KeyStealingScheduleCert
import MoltPetit.Model.KeyStealingScheduleBudget
import MoltPetit.Model.KeyStealingScheduleHorizon
import MoltPetit.Model.KeyStealingScheduleTimed

/-!
# Axiom audit — model and TypeScript results

Every headline theorem the paper states is checked here against Lean's axioms.
Each `#guard_msgs`-wrapped `#print axioms` makes the build **fail** if the
theorem ever comes to depend on anything beyond the three classical axioms
`propext`, `Classical.choice`, `Quot.sound` — in particular it would catch a
stray `native_decide` (`Lean.ofReduceBool`) or a `Float`/`sorry` leak (the
Aeneas runtime model carries `sorry`s in unrelated `Std` lemmas; the guards
confirm none reach our results). This is the machine-checked form of the paper's
axiom-hygiene claim. The Rust path is audited in `Rust/Axioms.lean`.
-/

-- Safety core (the shared engine behind T1)
/-- info: 'MoltPetit.Model.no_deep_fork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.no_deep_fork
/-- info: 'MoltPetit.Model.deep_block_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.deep_block_agreement

-- T1 light-client safety — TypeScript corollaries
/-- info: 'MoltPetit.Model.ts_recent_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.ts_recent_tip_ancestor_agreement
/-- info: 'MoltPetit.Model.ts_recent_tip_ancestor_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.ts_recent_tip_ancestor_mem
/-- info: 'MoltPetit.Model.ts_recent_produced_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.ts_recent_produced_tip_ancestor_agreement

-- T2 forged chains take real time — model + TypeScript corollary
/-- info: 'MoltPetit.Model.forged_suffix_time_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.forged_suffix_time_bound
/-- info: 'MoltPetit.Model.forged_suffix_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.forged_suffix_lag
/-- info: 'MoltPetit.Model.forged_chain_time_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.forged_chain_time_bound
/-- info: 'MoltPetit.Model.forged_chain_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.forged_chain_lag
/-- info: 'MoltPetit.Model.ts_forged_chain_time_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.ts_forged_chain_time_bound
/-- info: 'MoltPetit.Model.ts_forged_chain_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.ts_forged_chain_lag

-- T3 liveness — production succeeds
/-- info: 'MoltPetit.Model.liveness_produce_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.liveness_produce_block
/-- info: 'MoltPetit.Model.liveness_produce_signed_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.liveness_produce_signed_block

-- T4 global liveness
/-- info: 'MoltPetit.Model.liveness_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.liveness_global

-- Recency-scoped unforgeability is a theorem of the timed model + no-back-dating
/-- info: 'MoltPetit.Model.sigUnforgeableRecent_of_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sigUnforgeableRecent_of_timed
/-- info: 'MoltPetit.Model.noBackdate_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.noBackdate_independent

-- T5 recommended slot time
/-- info: 'MoltPetit.Model.ProverTiming.recommended_slot_sufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.ProverTiming.recommended_slot_sufficient
/-- info: 'MoltPetit.Model.ProverTiming.recommended_slot_necessary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.ProverTiming.recommended_slot_necessary
/-- info: 'MoltPetit.Model.ProverTiming.backlog_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.ProverTiming.backlog_diverges

-- Key-index extension (in-band consensus-maintained key rotation)
-- (A) no disagreement on the index of a finalized block
/-- info: 'MoltPetit.Model.deep_block_keyIndex_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.deep_block_keyIndex_agreement
-- (A) the in-band monotone-index rule is sound (no rollback within a chain)
/-- info: 'MoltPetit.Model.keyMonoOk_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyMonoOk_sound
-- (A) the per-producer floor never decreases as the chain grows (no rollback)
/-- info: 'MoltPetit.Model.keyFloor_le_extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyFloor_le_extend
/-- info: 'MoltPetit.Model.block_keyIndex_le_floor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.block_keyIndex_le_floor
-- (B) the indexed validator is sound for the original ValidChain (safety transports)
/-- info: 'MoltPetit.Model.validChainK_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.validChainK_sound
-- (B) per-settled-state reduction to the static index-blind registry
/-- info: 'MoltPetit.Model.indexed_reduces_to_static' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MoltPetit.Model.indexed_reduces_to_static
/-- info: 'MoltPetit.Model.sigsOk_reduces_to_static' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MoltPetit.Model.sigsOk_reduces_to_static

-- Sound key rotation (Phase 1): the in-force index pin is a discharged validator
-- rule, and the pinned validator is still sound for the original ValidChain.
/-- info: 'MoltPetit.Model.validChainK'_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.validChainK'_sound
/-- info: 'MoltPetit.Model.validChainK'_pinned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.validChainK'_pinned
-- the in-force-agreement core: keyFloor depends only on the producer's block-set,
-- so confirmed-prefix agreement pins the in-force index
/-- info: 'MoltPetit.Model.keyFloor_eq_of_mem_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyFloor_eq_of_mem_iff
/-- info: 'MoltPetit.Model.inForce_agreement_of_confirmed_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.inForce_agreement_of_confirmed_eq
-- Phase 1c: the agreement hypothesis is discharged from finality. `deep_block_shared`
-- strengthens `deep_block_agreement` to membership (rules out the too-short chain);
-- `inForce_agreement` is then unconditional — `inForce` is execution-global on the
-- confirmed zone, so `badKeyrot` (§2.1) is a genuine chain-independent slot predicate.
/-- info: 'MoltPetit.Model.deep_block_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.deep_block_shared
/-- info: 'MoltPetit.Model.confirmed_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.confirmed_mem_iff
/-- info: 'MoltPetit.Model.inForce_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.inForce_agreement
-- Phase 1c, signed layer: a rotated-out key is dead. An accepted index-pinned signed
-- chain verifies each block under its DECLARED registry entry, whose version is never
-- below the in-force one (the ≤-pin); a block keyed to a rotated-out version is
-- rejected (the validator/pin half; the crypto half is Phase 2).
/-- info: 'MoltPetit.Model.rotated_key_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.rotated_key_dead
/-- info: 'MoltPetit.Model.rotated_index_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.rotated_index_rejected
-- Phase 2 (I1): the key-stealing adversary. TimedExecution transports across a
-- pointwise-iff bad swap; with no key stolen the model collapses to TimedExecution
-- over the plain rent predicate (strict-superset witness, instruction 1).
/-- info: 'MoltPetit.Model.timedExecution_of_bad_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.timedExecution_of_bad_iff
/-- info: 'MoltPetit.Model.keyStealing_refines_timed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyStealing_refines_timed
-- Phase 2 (I2a): the bounded safety core for opt-A. `no_deep_fork`/`deep_block_shared`
-- weakened to require honest-slot uniqueness only up to the witness slot, plus
-- `confirmed_mem_iff_le`: with Δconf ≥ 2n and both chains carrying a block at the
-- coexistence slot σ, confirmed-prefix membership agrees using uniqueness only below σ
-- (minimal depth witnesses in the matured window). This is what breaks the
-- finality↔uniqueness cycle by a single strong slot-induction (§7.5).
/-- info: 'MoltPetit.Model.strictSlots_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.strictSlots_unique
/-- info: 'MoltPetit.Model.block_in_minimal_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.block_in_minimal_window
/-- info: 'MoltPetit.Model.no_deep_fork_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.no_deep_fork_le
/-- info: 'MoltPetit.Model.deep_block_shared_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.deep_block_shared_le
/-- info: 'MoltPetit.Model.confirmed_mem_iff_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.confirmed_mem_iff_le
-- Phase 2 (I2b/I2c): the cross-chain honest-slot uniqueness derivation. The record
-- of the two chains under test, its id-injectivity from collision resistance, and the
-- headline `honestSlotsUnique_keyrot` — the opt-A strong slot-induction that closes the
-- finality↔uniqueness cycle under the key-stealing adversary, given the named
-- `VersionedUnforgeable` crypto surface (versioned-EUF-CMA + honest signing, ¬Stolen at
-- every not-yet-rotated-out version — no forward security re-assumed).
/-- info: 'MoltPetit.Model.chainInRecord_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.chainInRecord_left
/-- info: 'MoltPetit.Model.chainInRecord_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.chainInRecord_right
/-- info: 'MoltPetit.Model.idInjective_keyrot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.idInjective_keyrot
/-- info: 'MoltPetit.Model.honestSlotsUnique_keyrot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.honestSlotsUnique_keyrot
-- The index pin made load-bearing: VersionedUnforgeable is DERIVED from the primitive,
-- transparent registry-level EUF-CMA (KeyStealingEUFCMA) using the proven validator pin
-- rotated_key_dead — so the headline theorems rest on the minimal faithful crypto
-- assumption, with the pin genuinely used rather than silently assumed.
/-- info: 'MoltPetit.Model.versionedUnforgeable_of_keyStealingEUFCMA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.versionedUnforgeable_of_keyStealingEUFCMA
-- Phase 3 core: light-client deep-block agreement under the key-stealing adversary —
-- P2-A (induced budget, named) + P2-B (honestSlotsUnique_keyrot_horizon, the
-- σ-localized n ≤ Δconf form) + P2-C
-- (idInjective_keyrot) fed into deep_block_agreement_of_height_depth over the index-
-- pinned signed validator validSignedChainK'. Named the deep-block-agreement CORE (not
-- the cert-suffix wrapper): the constant-size-certificate suffix wrapper and the I4
-- long-range/old-key-fork exclusion remain (documented in KeyStealingResults.lean).
/-- info: 'MoltPetit.Model.keyrot_deep_block_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_deep_block_agreement
-- verifier-facing form: the n-deep witnesses are discharged from chain length
/-- info: 'MoltPetit.Model.keyrot_deep_block_agreement_of_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_deep_block_agreement_of_length
-- THE FINAL light-client theorem: tip-ancestor agreement integrating the strong
-- key-stealing adversary (Stolen/badKeyrotOn, no forward security) with n ≤ Δconf
-- confirmation-gated key rotation (strengthened from the 2n gate by the σ-localized
-- horizon route). Two validSignedChainK' chains with recent equal-
-- height tips agree on the n-confirmed ancestor below each tip. Keyrot analogue of
-- ts_recent_tip_ancestor_agreement, stated over the signed pinned validator.
/-- info: 'MoltPetit.Model.keyrot_recent_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_recent_tip_ancestor_agreement
-- consistency form (unequal tip heights): the n-confirmed ancestor of the lower chain
-- is a member of the other chain too — keyrot analogue of ts_recent_tip_ancestor_mem.
/-- info: 'MoltPetit.Model.keyrot_recent_tip_ancestor_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_recent_tip_ancestor_mem
-- the loss-only adversary (Stolen := fun _ _ => False): losing a key grants no signing
-- power, so badKeyrotOn collapses to plain rent (badKeyrotOn_lossOnly) and carries no
-- chain argument. Prophylactic and loss-driven rotation are therefore anchor-free: a
-- plain rent budget, no H-IND, no key-leak horizon, no update mechanism.
/-- info: 'MoltPetit.Model.badKeyrotOn_lossOnly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.badKeyrotOn_lossOnly
/-- info: 'MoltPetit.Model.keyrot_lossonly_recent_tip_ancestor_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_lossonly_recent_tip_ancestor_agreement
/-- info: 'MoltPetit.Model.keyrot_lossonly_recent_tip_ancestor_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_lossonly_recent_tip_ancestor_mem
-- genesis-or-signed coverage is not a free assumption: every block of an accepted
-- index-pinned signed chain carries a verifying signature (KeyStealingSigned), so the
-- final theorems discharge hSig/hSig' from the validator rather than assuming them.
/-- info: 'MoltPetit.Model.keyStealingSigned_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyStealingSigned_of_mem
-- The certificate wrapper (the constant-blocks light-client form under key theft +
-- n≤Δconf-gated rotation): GroundedCertK threads a per-producer floor through the
-- fold and gates each step on the monotone rule; on the reconstructed full chain the
-- ≤-pin is implied (inForcePinned_of_validChainK), sigsOk is rebuilt from blockwise
-- declared signatures, and the headline honours the reserved name — a light client
-- needs O(n) blocks (claim + floor snapshot + suffix) and a clock.
/-- info: 'MoltPetit.Model.inForcePinned_of_validChainK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.inForcePinned_of_validChainK
/-- info: 'MoltPetit.Model.keyMonoOk_append_of_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyMonoOk_append_of_from
/-- info: 'MoltPetit.Model.exists_signedChain_of_covered' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MoltPetit.Model.exists_signedChain_of_covered
/-- info: 'MoltPetit.Model.groundedCertK_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.groundedCertK_history
/-- info: 'MoltPetit.Model.groundedCertK_suffix_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.groundedCertK_suffix_history
/-- info: 'MoltPetit.Model.keyrot_recent_certified_suffix_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_recent_certified_suffix_agreement
-- The TypeScript validator now enforces the key-index rules at full-chain level:
-- validChainK (structure + density + monotone rule) is bridged to the model, from
-- which the ≤ in-force pin follows (inForcePinned_of_validChainK). The certificate-
-- boundary form (suffix vs claim-carried floor snapshot) awaits the claim-format
-- extension mirroring GroundedCertK.
/-- info: 'MoltPetit.Model.ts_keyMonoOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.ts_keyMonoOk
/-- info: 'MoltPetit.Model.ts_validChainK_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.ts_validChainK_sound
-- Rotation liveness under the pinned validator — the previously-disclosed seam,
-- closed with a sharp two-sided characterization: production succeeds AND the
-- extension passes validChainK' iff the declared version clears the producer's
-- chain floor; declaring below the floor is rejected. The floor-clearance
-- hypothesis is exactly the index-inflation griefing condition, now a theorem.
/-- info: 'MoltPetit.Model.liveness_produce_blockK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.liveness_produce_blockK
/-- info: 'MoltPetit.Model.liveness_produce_signed_blockK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.liveness_produce_signed_blockK
/-- info: 'MoltPetit.Model.extension_rejected_below_floor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.extension_rejected_below_floor
-- I3, the induced budget decomposed: the joint rent∨theft ByzantineBounded that every
-- key-stealing theorem consumes is DERIVED from a rent budget (R slots/window) + a
-- theft rate (T exposed producers/window) with R + T ≤ ⌊(n-1)/3⌋ — via the union
-- no-double-count bound and the per-window producer↔slot injection.
/-- info: 'MoltPetit.Model.badSlotsIn_union_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.badSlotsIn_union_le
/-- info: 'MoltPetit.Model.theftSlots_card_le_exposed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.theftSlots_card_le_exposed
/-- info: 'MoltPetit.Model.induced_byzantine_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.induced_byzantine_bounded
-- I4, the provable core: old-key forks are long-range. The ≤-pin FORCES a fork that
-- carries a rotated-out-key block Δconf past the announcement to exclude the
-- announcement — it branched strictly before it. What remains for H-ANCHOR is exactly
-- ruling out pre-anchor branches: the irreducible weak-subjectivity residue.
/-- info: 'MoltPetit.Model.oldkey_dead_after_confirmed_announcement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.oldkey_dead_after_confirmed_announcement
/-- info: 'MoltPetit.Model.recent_oldkey_fork_is_longrange' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.recent_oldkey_fork_is_longrange
-- The TS certificate-boundary floor check: keyMonoFromTs (wire FloorList folded
-- through the suffix) agrees with the model keyMonoFrom under the snapshot's
-- denotation, and validateSuffixK yields exactly the suffix hypotheses of
-- keyrot_recent_certified_suffix_agreement. The wire contract (attest the pair
-- (claim, floors)) is documented on the model theorem.
/-- info: 'MoltPetit.Model.ts_keyMonoFromTs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.ts_keyMonoFromTs
/-- info: 'MoltPetit.Model.ts_validateSuffixK_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.ts_validateSuffixK_sound
/-- info: 'MoltPetit.Model.keyMonoFrom_congr_lt' does not depend on any axioms -/
#guard_msgs in
#print axioms MoltPetit.Model.keyMonoFrom_congr_lt
-- The scheduled-rotation variant (KEY_ROTATION_SOUND §10 — the anchor-discharging
-- device). Position-determined generation `schedule s` replaces the chain-local
-- inForce, so badSched is chain-independent and honest-slot uniqueness is DIRECT —
-- the finality↔uniqueness cycle (confirmed_mem_iff_le + strong induction + Δconf≥2n)
-- vanishes. Both operational packages (A: scheduled/no-erasure, B: erasure+lockstep)
-- license this one device; a genesis-only stateless light client follows, with the
-- budget read retroactively (see the honest-scope note in KeyStealingScheduleResults).
/-- info: 'MoltPetit.Model.rotated_key_dead_sched' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.rotated_key_dead_sched
/-- info: 'MoltPetit.Model.honestSlotsUnique_sched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.honestSlotsUnique_sched
/-- info: 'MoltPetit.Model.sched_deep_block_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_deep_block_agreement
-- The scheduled main-theorem set (KEY_ROTATION_SOUND §10, task step 1): the
-- tip-ancestor forms over validSignedChainSched/badSched. The statements carry
-- NO Δconf gate and a chain-independent budget — no anchor beyond genesis.
/-- info: 'MoltPetit.Model.sched_deep_block_agreement_of_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_deep_block_agreement_of_length
/-- info: 'MoltPetit.Model.sched_recent_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_recent_tip_ancestor_agreement
/-- info: 'MoltPetit.Model.sched_recent_tip_ancestor_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_recent_tip_ancestor_mem
-- The scheduled certificate (task step 2): NO floor snapshot — the fold checks the
-- pin schedule(slot) ≤ keyIndex per block, so the default certificate's (claim, floors)
-- wire-authentication contract disappears, and the budget is one global hypothesis
-- (no AttestedHistoryK). The safety chain is mirrored over the core validator
-- (sigs + structure/density + pin; keyMonoOk is not load-bearing for scheduled safety).
/-- info: 'MoltPetit.Model.schedUnforgeable_of_core' depends on axioms: [propext] -/
#guard_msgs in
#print axioms MoltPetit.Model.schedUnforgeable_of_core
/-- info: 'MoltPetit.Model.honestSlotsUnique_schedCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.honestSlotsUnique_schedCore
/-- info: 'MoltPetit.Model.sched_deep_block_agreement_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_deep_block_agreement_core
/-- info: 'MoltPetit.Model.groundedCertSched_suffix_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.groundedCertSched_suffix_history
/-- info: 'MoltPetit.Model.sched_recent_certified_suffix_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_recent_certified_suffix_agreement
-- §10.0 claim 2, formal (review response, tip-only): any accepted chain whose TIP
-- declares a generation whose era ended more than Δ ago FAILS the plain recency
-- check — no budget, no honesty consumed (hybrid forks with honest prefixes covered).
-- This is the precise formal scope of §10.1's "retired-key secrecy not required";
-- the budget's retroactive reading is disclosed in the module docs.
/-- info: 'MoltPetit.Model.sched_oldkey_fork_stale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_oldkey_fork_stale
-- The scheduled I3 (task step 3): the chain-independent budget DERIVED from a rent
-- budget R + a current-generation theft rate T (R + T ≤ ⌊(n-1)/3⌋), via the union
-- bound + per-window producer↔slot injection — one global hypothesis, no chain.
/-- info: 'MoltPetit.Model.theftSlotsSched_card_le_exposed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.theftSlotsSched_card_le_exposed
/-- info: 'MoltPetit.Model.induced_byzantine_bounded_sched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.induced_byzantine_bounded_sched
-- The two operational packages (KEY_ROTATION_SOUND §10.1/§10.2) as Lean structures,
-- each delivering the anchor-free light-client conclusions in both forms. PackageB
-- extends PackageA (erasure_freeze added), so PackageB.toPackageA records the
-- assumption-set inclusion "B assumes A plus erasure"; the packageB_* proofs are
-- literally the packageA_* theorems through that projection. For full-window
-- schedules the erasure field is redundant (erasure_freeze_of_exposedBound) — the
-- honest weight accounting is in the PackageB docstring.
/-- info: 'MoltPetit.Model.packageA_recent_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.packageA_recent_tip_ancestor_agreement
/-- info: 'MoltPetit.Model.packageA_recent_certified_suffix_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.packageA_recent_certified_suffix_agreement
/-- info: 'MoltPetit.Model.packageB_recent_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.packageB_recent_tip_ancestor_agreement
/-- info: 'MoltPetit.Model.packageB_recent_certified_suffix_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.packageB_recent_certified_suffix_agreement
/-- info: 'MoltPetit.Model.sched_oldkey_fork_stale_core' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_oldkey_fork_stale_core
/-- info: 'MoltPetit.Model.erasure_freeze_of_exposedBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.erasure_freeze_of_exposedBound
/-- info: 'MoltPetit.Model.schedule_div_full_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.schedule_div_full_window
-- The horizon-scoped budget (the top-window contraction, seam §10.4 part 1): the
-- pigeonhole runs at the trailing matured window below the lower tip, so the budget
-- is consulted only on windows from a horizon H one window below the tips — the
-- retroactive reading (historical windows charged for later-generation thefts) is
-- gone from the hypothesis; windows from H on still carry badSched's timeless
-- cumulative count, whose temporal confinement is KeyStealingScheduleTimed's
-- business — and shared genesis becomes a conclusion (stated literally by
-- sched_recent_genesis_agreement_horizon), not a hypothesis.
-- byzantineBoundedFrom_of_bounded: the old global budget delivers the new one.
/-- info: 'MoltPetit.Model.horizon_shared_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.horizon_shared_prefix
/-- info: 'MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon
/-- info: 'MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon
/-- info: 'MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon_core
/-- info: 'MoltPetit.Model.byzantineBoundedFrom_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.byzantineBoundedFrom_of_bounded
-- The timed theft layer (seam §10.4 part 2): A3/B3/B2's temporal content, formerly
-- prose, is now formal (NoPrematureTheft / NoPrematureMint / ErasureTimed) with
-- machine-checked consequences — backward theft-locality (a window is never charged
-- for thefts more than one period before it), the horizon budget DERIVED from a
-- recent-theft census (the timed I3), and bounded forward-stamping (the FORWARD
-- half of the static model's two-sided NoBackdate pin, DERIVED where the static
-- model assumes the whole pin; the back-dating half is NOT derived —
-- sched_backdate_consistent machine-checks it stays consistent, mirroring
-- noBackdate_independent). PackageATimed delivers the horizon light-client
-- conclusion end to end. Residual (module doc): the census is future-inclusive;
-- confining it to thefts before the client's validation time needs a timed
-- EUF-CMA surface keying on theft-before-mint (next increment).
/-- info: 'MoltPetit.Model.theft_is_recent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.theft_is_recent
/-- info: 'MoltPetit.Model.exposedSched_subset_recentTheft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.exposedSched_subset_recentTheft
/-- info: 'MoltPetit.Model.horizon_budget_of_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.horizon_budget_of_timed
/-- info: 'MoltPetit.Model.sched_forwardstamp_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_forwardstamp_bounded
/-- info: 'MoltPetit.Model.sched_recent_block_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_recent_block_fresh
/-- info: 'MoltPetit.Model.theft_during_era_of_erasure' does not depend on any axioms -/
#guard_msgs in
#print axioms MoltPetit.Model.theft_during_era_of_erasure
/-- info: 'MoltPetit.Model.packageATimed_recent_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MoltPetit.Model.packageATimed_recent_tip_ancestor_agreement
/-- info: 'MoltPetit.Model.packageBTimed_recent_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MoltPetit.Model.packageBTimed_recent_tip_ancestor_agreement
/-- info: 'MoltPetit.Model.sched_recent_genesis_agreement_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MoltPetit.Model.sched_recent_genesis_agreement_horizon
/-- info: 'MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon_core
/-- info: 'MoltPetit.Model.sched_backdate_consistent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sched_backdate_consistent

-- ---------------------------------------------------------------------------
-- The horizon route for mode 1: the same agreement at `n ≤ Δconf`
-- ---------------------------------------------------------------------------
-- Δconf ≥ 2n is an artifact of running the pigeonhole at the divergence window.
-- Run it at a σ-localized top window [σ-n, σ) — matured in both chains by the
-- coexistence block at σ — and the honest-slot obligation still lands strictly
-- below σ (what the strong induction needs) while only b.slot + n ≤ σ is
-- required of the confirmed block. Hence n ≤ Δconf suffices, and shared genesis
-- drops out. Smaller Δconf grows confirmedPrefix, raises inForce and shrinks
-- badKeyrotOn, so these subsume the 2n forms rather than replacing them.
/-- info: 'MoltPetit.Model.sigma_shared_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.sigma_shared_prefix
/-- info: 'MoltPetit.Model.confirmed_mem_iff_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.confirmed_mem_iff_horizon
/-- info: 'MoltPetit.Model.honestSlotsUnique_keyrot_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.honestSlotsUnique_keyrot_horizon
/-- info: 'MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_horizon
/-- info: 'MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_horizon_of_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_horizon_of_valid

-- ---------------------------------------------------------------------------
-- Free-cadence lockstep rotation (mode 3, D1'-thin)
-- ---------------------------------------------------------------------------
-- The lockstep validator carries no schedule; lockstep is a behavioural
-- hypothesis (an execution-level, per-window, monotone rosterGen every honest
-- signature declares). The pinning theorem machine-checks "no-mixing pins any
-- fork to one generation"; the lagged-schedule transport then hands the whole
-- scheduled theorem set to lockstep chains. Assumption-wise the package is
-- PackageA at the lagged schedule plus the behavioural rosterGen fields.
/-- info: 'MoltPetit.Model.lockstep_declares_rosterGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstep_declares_rosterGen
/-- info: 'MoltPetit.Model.lockstep_validSignedChainSched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstep_validSignedChainSched
/-- info: 'MoltPetit.Model.lockstep_recent_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstep_recent_tip_ancestor_agreement
/-- info: 'MoltPetit.Model.lockstep_recent_tip_ancestor_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.lockstep_recent_tip_ancestor_mem

-- ---------------------------------------------------------------------------
-- The anchored horizon: the key-leak horizon as a theorem
-- ---------------------------------------------------------------------------
-- With an anchor block both chains carry, the corruption budget is consulted
-- only on windows ending after the anchor's slot: below the anchor the two
-- chains are literally the same list, so no budget, no retired-key secrecy and
-- no crypto is assumed there. The anchor's age is ARBITRARY -- an older anchor
-- just means more windows must satisfy the budget -- and A := genesis recovers
-- the global-budget theorem. This is the paper's "key-leak horizon", formal.
/-- info: 'MoltPetit.Model.honestSlotsUnique_keyrot_anchored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.honestSlotsUnique_keyrot_anchored
/-- info: 'MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored
-- anchored membership form (unequal tip heights), same trailing budget
/-- info: 'MoltPetit.Model.keyrot_recent_tip_ancestor_mem_anchored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.keyrot_recent_tip_ancestor_mem_anchored
