# Molt Petit — Publication Preparation Status Log

**Branch:** `publish-prep` (branched from `main` at `b46d439`)  
**Objective:** Prepare the Molt Petit paper (`paper/molt.tex`) for publication with all claims faithfully and precisely matching the machine-checked Lean 4 proofs verbatim, without esoteric or convenience assumptions, removing acknowledged leftovers that are now proved, and explicitly documenting the formal boundaries.

---

## 1. Toolchain & Environment Status

- **Lean 4 Toolchain:**
  - Pinned version: `leanprover/lean4:v4.30.0-rc2` (specified in `lean-toolchain`).
  - Executable: Managed via `elan` under `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake`, executed in this environment via `nix-run`.
  - Lake targets: `Molt`, `MoltPetit`, `Rust`, `Thales`.
  - Proof soundness: 0 `sorry`, 0 `admit`, 0 unapproved axioms, 0 code `TODO`s across the entire Lean codebase. All headline theorems satisfy `#guard_msgs` checking `#print axioms` (standard classical axioms `[propext, Classical.choice, Quot.sound]`).
- **LaTeX Toolchain:**
  - Status: **Available via Nix store.** `paper/build.sh` invokes `/nix/store/xwg31kngm9c3p4cgqhjhyc0hzb8i24ji-texlive-2025-r78234-final-env/bin/latexmk` via `nix-run`.
  - Verification: Compiles `paper/molt.tex` cleanly to `molt.pdf` (18 pages, zero errors).

---

## 2. Claim-to-Theorem Mapping & Audit Table

Every theorem statement in the paper is audited against its Lean counterpart to ensure verbatim conceptual alignment and honest hypothesis disclosure.

| Paper Theorem & Label | Paper Location | Lean Declaration | Lean Source File | Proof Status | Paper Presentation Status |
|---|---|---|---|---|---|
| **Light-Client Safety** (Thm 1, `thm:lc`) | §6.1, L644 | `Molt.light_client_safety`, `Molt.same_block_same_prefix` | `Molt/Results.lean` | Proved (0 sorry) | Restored production-side caveat (§6.1 L659) |
| **Forged Suffixes Half-Speed Bound** (Thm 2, `thm:forge`) | §6.2, L694 | `Molt.forged_time_bound`, `MoltPetit.Model.forged_chain_time_bound` | `Molt/Results.lean`, `MoltPetit/Model/Timed.lean` | Proved (0 sorry) | Matches verbatim; non-degeneracy conditions ($n \ge 2$) disclosed |
| **Uniqueness Derived from Timed Execution** (Thm 7, `thm:timed-uniq`) | Appendix A, L1486 | `Molt.sigUnforgeableRecent_of_timed`, `Molt.noBackdate_independent` | `Molt/Results.lean` | Proved (0 sorry) | Matches verbatim; independence of `NoBackdate` witnessed |
| **Mode 1: Client Sync Rule** (Thm 3, `thm:refresh`) | §6.3, L834 | `Molt.sync_rule`, `Molt.sync_rule_mem`, `Molt.stay_recent_client_safe` | `Molt/ClientRule.lean` | Proved (0 sorry) | Matches verbatim; trailing $5n$ budget |
| **Mode 1: Anchored Certificate Client Rule** (W2) | §6.3, L913 | `Molt.cert_sync_rule`, `Molt.keyrot_certified_suffix_agreement_anchored` | `Molt/CertClientRule.lean` | Proved (0 sorry) | Folded into §6.3 (L913-925); constant-size client anchored rule |
| **Mode 1: Timed Theft & Exposure Window** (W3a) | §6.3, L925 | `Molt.sync_rule_timed`, `Molt.max_sync_period_timed`, `MoltPetit.Model.theft_exposure_window` | `Molt/SyncRuleTimed.lean` | Proved (0 sorry) | Folded into §6.3 (L925-934); derived budget from reaction delay |
| **Mode 1: Paced Tight Census / $F_{max}$** (W3b) | §6.3, L965 | `Molt.max_sync_period_tight`, `Molt.paced_tight_census_bound_all_F`, `Molt.paced_separation_witnessed` | `Molt/MaxSyncSignatureTimed.lean` | Proved (0 sorry) | Folded into §6.3 (L965-981); non-retroactive census via NoTheftBackdating |
| **Mode 1: Induction Over Syncs** (W4) | §6.3, L1030 | `Molt.sync_induction_full_chain` | `Molt/SyncInduction.lean` | Proved (0 sorry) | Folded into §6.3 (L1030-1040); machine-checked conditional on `hRLe` |
| **Mode 2: Scheduled Safety** (Thm 4, `thm:sched`) | §6.3, L1028 | `Molt.scheduled_client_safety`, `Molt.sched_recent_tip_ancestor_mem_horizon` | `Molt/Rotation.lean` | Proved (0 sorry) | Matches verbatim; horizon-scoped budget without anchor |
| **Mode 3: Lockstep Safety (Cumulative)** (Thm 5, `thm:lock`) | §6.3, L1110 | `Molt.lockstep_client_safety`, `Molt.lockstep_declares_rosterGen` | `Molt/Rotation.lean` | Proved (0 sorry) | Matches verbatim; depth $n$ under global budget |
| **Mode 3: Certificate Presentation** (W1) | §6.3, L1178+ | `Molt.lockstep_recent_certified_suffix_agreement`, `Molt.lockstep_cert_gen_pinned` | `Molt/LockstepCert.lean` | Proved (0 sorry) | Folded into §6.3; constant-overhead suffix verification on wake ($n \ge 2$) |
| **Mode 3: Per-Generation Census & Erasure** (W5, Thm 5b) | §6.3, L1160+ | `Molt.lockstep_client_safety_gen`, `Molt.lockstep_client_safety_timed` | `Molt/LockstepGen.lean` | Proved (0 sorry) | Folded into §6.3 as Theorem 5b / Thm 5′ (`thm:lock-gen`); depth $2n$, non-inductive, genesis-free pinning |
| **Obstruction Witnesses for Timed Signature Surfaces** (W6) | §8, L1419 | `Molt.badSched_single_key_safe_not_enough`, `Molt.badKeyrot_single_key_safe_not_enough` | `Molt/KeyStealingTimedScope.lean` | Proved (0 sorry) | **To Fold In:** Explains structural impossibility of deriving per-version surface from slot-timed model |
| **Liveness & Prover Timing** (Thm 6, `thm:live`) | §6.4, L1208 | `Molt.production_liveness`, `Molt.global_liveness`, `Molt.slot_time_sufficient`, `Molt.slot_time_necessary` | `Molt/Liveness.lean` | Proved (0 sorry) | Matches verbatim |
| **Multi-Chain Network Model** (W7) | §6.4, L1223 | — | — | Intentionally Deferred | Retained as acknowledged limitation/future work |

---

## 3. Work in Progress & Execution Log

- [x] Branch `publish-prep` created off `main`.
- [x] Lean toolchain verified (`leanprover/lean4:v4.30.0-rc2` via `nix-run`).
- [x] Full audit of paper text against Lean proofs and post-annotation rollout.
- [x] Initial status log established at `docs/PUBLISH_PREP_STATUS.md`.
- [x] **Pass 1:** Apply editorial corrections (census precision, representability note, cadence wording).
  - Commit `31e0fc1`: Updated §1 cadence wording ("no cadence rule at all"), §6.1 representability caveat ("argued, not proved (the representability lemmas are production-side)"), §6.3 census precision ("producers with a stolen key not yet retired there"), and `paper/build.sh` Nix TeX Live toolchain runner.
- [x] **Pass 2:** Update §2, §4, §6 intro with Mode 3 certified forms and per-generation credit.
  - Commit `146f554`: Updated §2 Mode 3 overview for certificate presentation (`lockstep_recent_certified_suffix_agreement`) and per-generation credit (`lockstep_client_safety_gen`, depth $2n$); §4 verifier rule certified forms across all three modes; §6 intro for lockstep twin.
- [x] **Pass 3:** Update §6.3 Mode 1 with W2 (certified anchored), W3a/W3b (timed theft & tight census), W4 (sync induction).
  - Commit `5b68719`: Folded in W2 (`keyrot_certified_suffix_agreement_anchored`, `cert_sync_rule`, `cert_max_sync_period`), W3a (`Reacts`, `recentTheftProducersK`, `budget_of_reaction`, `sync_rule_timed`, `max_sync_period_timed`), W3b (`NoTheftBackdating`, `theft_exposure_window`, `paced_tight_census_bound_all_F`, `max_sync_period_tight`), and W4 (`sync_induction_full_chain` with explicit `hRLe` disclosure).
- [x] **Pass 4:** Update §6.3 Mode 3 with Theorem 5b (`thm:lock-gen`, W5), Mode 3 certificate presentation (W1), and updated Modes table.
  - Commit `66f9e96`: Folded in Theorem 5b (`thm:lock-gen`: `lockstep_client_safety_gen`, depth $2n$, genesis-free via `lockstep_window_declares_rosterGen`), operator erasure credit (`ErasureTimedLock`, `genBound_of_preRetirementBound`, `lockstep_client_safety_timed`), certificate sync (`groundedCertLock_gen_of_tail`, `groundedCertLock_gen_unique`, `lockstep_recent_certified_suffix_agreement`, `lockstep_cert_gen_pinned`), and updated Modes table with credited erasure.
- [ ] **Pass 5:** Consolidate §6.3 Honest Scope and update §8 Limitations / Appendix A with W6 obstruction witnesses.
- [ ] **Pass 6:** Audit theorem statements for exact hypothesis match and publishability.

---

## 4. Open Questions & Design Decisions for George

1. **W7 (Multi-chain network model):** Retained as future work / limitation (§6.4 L1223). The rollout evaluation concluded that formalizing a full dynamic gossip network model with fork choice is out of scope for this consensus protocol paper and yields diminishing returns.
2. **Mode 2 Certificate Horizon Scoping:** Proved under global all-window budget (`sched_recent_certified_suffix_agreement`). Horizon scoping for certificates remains future work (while Mode 1 and Mode 3 certificate forms are fully closed).
3. **Representability Lemma Note:** Restored explicit disclosure in §6.1 that the representability lemmas are production-side only, justifying why the hypothesis is retained in Theorem 1 (`thm:lc`).
4. **W3b Separation Framing (§6.3):** The text explicitly avoids claiming that the timed budget saves executions that the untimed budget rejected (which `paced_budget_holds_under_timing` disproves); rather, `paced_separation_witnessed` proves a separation in the operational assumptions a deployment must defend (a constant per-window bound vs a stretch-wide retroactive accumulation).
5. **W4 Sync Induction Hypotheses (§6.3):** The paper now states `sync_induction_full_chain` is machine-checked conditional on `hRLe` (reference tip at least as tall at every sync), while the informal density argument justifying `hRLe` remains acknowledged as informal on paper.
6. **Mode 3 Certificate Generation Attestation (§6.3):** The certificate attests the tip generation alongside the claim, but for $n \ge 2$ this generation is uniquely determined by the tail buffer (`groundedCertLock_gen_of_tail`, `groundedCertLock_gen_unique`), so only $n = 1$ carries an extra counter over the wire.
7. **Mode 3 Safety Twins (§6.3):** Both the cumulative global form (Theorem 5, depth $n$) and the per-generation credited form (Theorem 5b, depth $2n$) are presented as options for deployments, with the modes table highlighting credited erasure under Theorem 5b.
