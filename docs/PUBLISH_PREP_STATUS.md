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
  - Status: **Missing in container.** `pdflatex`, `xelatex`, `lualatex`, and `latexmk` are not installed on the system `PATH`, and `nix-shell` is not available.
  - Per instructions, this is explicitly documented rather than guessed. Any edits to `paper/molt.tex` will be meticulously checked for TeX syntax and structure.

---

## 2. Claim-to-Theorem Mapping & Audit Table

Every theorem statement in the paper is audited against its Lean counterpart to ensure verbatim conceptual alignment and honest hypothesis disclosure.

| Paper Theorem & Label | Paper Location | Lean Declaration | Lean Source File | Proof Status | Paper Presentation Status |
|---|---|---|---|---|---|
| **Light-Client Safety** (Thm 1, `thm:lc`) | §6.1, L644 | `Molt.light_client_safety`, `Molt.same_block_same_prefix` | `Molt/Results.lean` | Proved (0 sorry) | Needs restoration of production-side representability caveat |
| **Forged Suffixes Half-Speed Bound** (Thm 2, `thm:forge`) | §6.2, L694 | `Molt.forged_time_bound`, `MoltPetit.Model.forged_chain_time_bound` | `Molt/Results.lean`, `MoltPetit/Model/Timed.lean` | Proved (0 sorry) | Matches verbatim; non-degeneracy conditions ($n \ge 2$) disclosed |
| **Uniqueness Derived from Timed Execution** (Thm 7, `thm:timed-uniq`) | Appendix A, L1486 | `Molt.sigUnforgeableRecent_of_timed`, `Molt.noBackdate_independent` | `Molt/Results.lean` | Proved (0 sorry) | Matches verbatim; independence of `NoBackdate` witnessed |
| **Mode 1: Client Sync Rule** (Thm 3, `thm:refresh`) | §6.3, L834 | `Molt.sync_rule`, `Molt.sync_rule_mem`, `Molt.stay_recent_client_safe` | `Molt/ClientRule.lean` | Proved (0 sorry) | Matches verbatim; trailing $5n$ budget |
| **Mode 1: Anchored Certificate Client Rule** (W2) | §6.3, L916 | `Molt.cert_sync_rule`, `Molt.keyrot_certified_suffix_agreement_anchored` | `Molt/CertClientRule.lean` | Proved (0 sorry) | **To Fold In:** Replaces "carrying anchored trailing-5n form to certificates is future work" |
| **Mode 1: Timed Theft & Exposure Window** (W3a) | §6.3, L948 | `Molt.sync_rule_timed`, `Molt.max_sync_period_timed`, `MoltPetit.Model.theft_exposure_window` | `Molt/SyncRuleTimed.lean` | Proved (0 sorry) | **To Fold In:** Replaces future work on creation/theft times |
| **Mode 1: Paced Tight Census / $F_{max}$** (W3b) | §6.3, L948 | `Molt.max_sync_period_tight`, `Molt.paced_tight_census_bound_all_F`, `Molt.paced_separation_witnessed` | `Molt/MaxSyncSignatureTimed.lean` | Proved (0 sorry) | **To Fold In:** Formalizes non-retroactive budget bounds |
| **Mode 1: Induction Over Syncs** (W4) | §6.3, L1007 | `Molt.sync_induction_full_chain` | `Molt/SyncInduction.lean` | Proved (0 sorry) | **To Fold In:** Replaces informal paper argument (conditional on `hRLe`) |
| **Mode 2: Scheduled Safety** (Thm 4, `thm:sched`) | §6.3, L1028 | `Molt.scheduled_client_safety`, `Molt.sched_recent_tip_ancestor_mem_horizon` | `Molt/Rotation.lean` | Proved (0 sorry) | Matches verbatim; horizon-scoped budget without anchor |
| **Mode 3: Lockstep Safety (Cumulative)** (Thm 5, `thm:lock`) | §6.3, L1110 | `Molt.lockstep_client_safety`, `Molt.lockstep_declares_rosterGen` | `Molt/Rotation.lean` | Proved (0 sorry) | Matches verbatim; depth $n$ under global budget |
| **Mode 3: Certificate Presentation** (W1) | §6.3, L1148 | `Molt.lockstep_recent_certified_suffix_agreement`, `Molt.lockstep_cert_gen_pinned` | `Molt/LockstepCert.lean` | Proved (0 sorry) | **To Fold In:** Replaces "full chain verification on wake is future work" |
| **Mode 3: Per-Generation Census & Erasure** (W5, Thm 5b) | §6.3, L1110+ | `Molt.lockstep_client_safety_gen`, `Molt.lockstep_client_safety_timed` | `Molt/LockstepGen.lean` | Proved (0 sorry) | **To Fold In:** Replaces "erasure's per-generation credit is future work"; confirmation depth $2n$ |
| **Obstruction Witnesses for Timed Signature Surfaces** (W6) | §8, L1419 | `Molt.badSched_single_key_safe_not_enough`, `Molt.badKeyrot_single_key_safe_not_enough` | `Molt/KeyStealingTimedScope.lean` | Proved (0 sorry) | **To Fold In:** Explains structural impossibility of deriving per-version surface from slot-timed model |
| **Liveness & Prover Timing** (Thm 6, `thm:live`) | §6.4, L1208 | `Molt.production_liveness`, `Molt.global_liveness`, `Molt.slot_time_sufficient`, `Molt.slot_time_necessary` | `Molt/Liveness.lean` | Proved (0 sorry) | Matches verbatim |
| **Multi-Chain Network Model** (W7) | §6.4, L1223 | — | — | Intentionally Deferred | Retained as acknowledged limitation/future work |

---

## 3. Work in Progress & Execution Log

- [x] Branch `publish-prep` created off `main`.
- [x] Lean toolchain verified (`leanprover/lean4:v4.30.0-rc2` via `nix-run`).
- [x] Full audit of paper text against Lean proofs and post-annotation rollout.
- [x] Initial status log established at `docs/PUBLISH_PREP_STATUS.md`.
- [ ] **Pass 1:** Apply editorial corrections (census precision, representability note, cadence wording).
- [ ] **Pass 2:** Update §2, §4, §6 intro with Mode 3 certified forms and per-generation credit.
- [ ] **Pass 3:** Update §6.3 Mode 1 with W2 (certified anchored), W3a/W3b (timed theft & tight census), W4 (sync induction).
- [ ] **Pass 4:** Update §6.3 Mode 3 with Theorem 5b (`thm:lock-gen`, W5), Mode 3 certificate presentation (W1), and updated Modes table.
- [ ] **Pass 5:** Consolidate §6.3 Honest Scope and update §8 Limitations / Appendix A with W6 obstruction witnesses.
- [ ] **Pass 6:** Audit theorem statements for exact hypothesis match and publishability.

---

## 4. Open Questions & Design Decisions for George

1. **W7 (Multi-chain network model):** Retained as future work / limitation (§6.4 L1223). The rollout evaluation concluded that formalizing a full dynamic gossip network model with fork choice is out of scope for this consensus protocol paper and yields diminishing returns.
2. **Mode 2 Certificate Horizon Scoping:** Proved under global all-window budget (`sched_recent_certified_suffix_agreement`). Horizon scoping for certificates remains future work (while Mode 1 and Mode 3 certificate forms are fully closed).
3. **Representability Lemma Note:** Restored explicit disclosure in §6.1 that the representability lemmas are production-side only, justifying why the hypothesis is retained in Theorem 1 (`thm:lc`).
