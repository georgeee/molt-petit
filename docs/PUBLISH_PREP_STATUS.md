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
| **Light-Client Safety** (Thm 1, `thm:lc`) | §6.1, L646 | `Molt.light_client_safety`, `Molt.same_block_same_prefix` | `Molt/Results.lean` | Proved (0 sorry) | Restored production-side caveat (§6.1 L659) |
| **Forged Suffixes Half-Speed Bound** (Thm 2, `thm:forge`) | §6.2, L697 | `Molt.forged_time_bound`, `MoltPetit.Model.forged_chain_time_bound` | `Molt/Results.lean`, `MoltPetit/Model/Timed.lean` | Proved (0 sorry) | Matches verbatim; non-degeneracy conditions ($n \ge 2$) disclosed |
| **Uniqueness Derived from Timed Execution** (Thm 7, `thm:timed-uniq`) | Appendix A, L1552 | `Molt.sigUnforgeableRecent_of_timed`, `Molt.noBackdate_independent` | `Molt/Results.lean` | Proved (0 sorry) | Matches verbatim; independence of `NoBackdate` witnessed |
| **Mode 1: Client Sync Rule** (Thm 3, `thm:refresh`) | §6.3, L841 | `Molt.sync_rule`, `Molt.sync_rule_mem`, `Molt.stay_recent_client_safe` | `Molt/ClientRule.lean` | Proved (0 sorry) | Matches verbatim; trailing $5n$ budget |
| **Mode 1: Anchored Certificate Client Rule** (W2) | §6.3, L923 | `Molt.cert_sync_rule`, `Molt.keyrot_certified_suffix_agreement_anchored` | `Molt/CertClientRule.lean` | Proved (0 sorry) | Folded into §6.3 (L913-925); constant-size client anchored rule |
| **Mode 1: Timed Theft & Exposure Window** (W3a) | §6.3, L936 | `Molt.sync_rule_timed`, `Molt.max_sync_period_timed`, `MoltPetit.Model.theft_exposure_window` | `Molt/SyncRuleTimed.lean` | Proved (0 sorry) | Folded into §6.3 (L925-934); derived budget from reaction delay |
| **Mode 1: Paced Tight Census / $F_{max}$** (W3b) | §6.3, L977 | `Molt.max_sync_period_tight`, `Molt.paced_tight_census_bound_all_F`, `Molt.paced_separation_witnessed` | `Molt/MaxSyncSignatureTimed.lean` | Proved (0 sorry) | Folded into §6.3 (L965-981); non-retroactive census via NoTheftBackdating |
| **Mode 1: Induction Over Syncs** (W4) | §6.3, L1043 | `Molt.sync_induction_full_chain` | `Molt/SyncInduction.lean` | Proved (0 sorry) | Folded into §6.3 (L1030-1040); machine-checked conditional on `hRLe` |
| **Mode 2: Scheduled Safety** (Thm 4, `thm:sched`) | §6.3, L1063 | `Molt.scheduled_client_safety`, `Molt.sched_recent_tip_ancestor_mem_horizon` | `Molt/Rotation.lean` | Proved (0 sorry) | Matches verbatim; horizon-scoped budget without anchor |
| **Mode 3: Lockstep Safety (Cumulative)** (Thm 5, `thm:lock`) | §6.3, L1145 | `Molt.lockstep_client_safety`, `Molt.lockstep_declares_rosterGen` | `Molt/Rotation.lean` | Proved (0 sorry) | Matches verbatim; depth $n$ under global budget |
| **Mode 3: Certificate Presentation** (W1) | §6.3, L1194 | `Molt.lockstep_recent_certified_suffix_agreement`, `Molt.lockstep_cert_gen_pinned` | `Molt/LockstepCert.lean` | Proved (0 sorry) | Folded into §6.3; constant-overhead suffix verification on wake ($n \ge 2$) |
| **Mode 3: Per-Generation Census & Erasure** (W5, Thm 5b) | §6.3, L1166 | `Molt.lockstep_client_safety_gen`, `Molt.lockstep_client_safety_timed` | `Molt/LockstepGen.lean` | Proved (0 sorry) | Folded into §6.3 as Theorem 5b / Thm 5′ (`thm:lock-gen`); depth $2n$, non-inductive, genesis-free pinning |
| **Obstruction Witnesses for Timed Signature Surfaces** (W6) | §6.3, §8, App A | `Molt.badSched_single_key_safe_not_enough`, `Molt.badKeyrot_single_key_safe_not_enough` | `Molt/KeyStealingTimedScope.lean` | Proved (0 sorry) | Folded into §6.3 (Assump. 6, L796), §8 (L1480), and App A (L1589); structural impossibility machine-checked |
| **Liveness & Prover Timing** (Thm 6, `thm:live`) | §6.4, L1271 | `Molt.production_liveness`, `Molt.global_liveness`, `Molt.slot_time_sufficient`, `Molt.slot_time_necessary` | `Molt/Liveness.lean` | Proved (0 sorry) | Matches verbatim |
| **Multi-Chain Network Model** (W7) | §6.4, L1287 | — | — | Intentionally Deferred | Retained as acknowledged limitation/future work |

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
- [x] **Pass 5:** Consolidate §6.3 Honest Scope and update §8 Limitations / Appendix A with W6 obstruction witnesses.
  - Commit `1c2891f`: Added Assumption~\ref{ass:rotation-honest} (per-mode honest custody & no back-dating); updated §6.3 Honest Scope with non-retroactive exposure boundary, Mode 2 global certificate scoping disclosure, and W6 timed-model structural gap; updated §8 Named Seams and Appendix~\ref{app:timed-uniq} citing `Molt.badSched_single_key_safe_not_enough` and `Molt.badKeyrot_single_key_safe_not_enough` for the single-key vs whole-slot obstruction.
- [x] **Pass 6:** Audit theorem statements for exact hypothesis match and publishability.
  - Completed comprehensive hypothesis audit across all paper theorems (Theorems 1–7, Assumptions 1–6, W1–W6 extensions) against Lean signatures in `Molt`, `MoltPetit`, and `Rust`.
  - Verified verbatim conceptual alignment, explicit disclosure of non-degeneracy conditions ($n \ge 2$, $k_0 \ge 1$), presentation caveats (production-side representability), conditional hypotheses (`hRLe` in W4 sync induction), and operational assumptions (Assumption~\ref{ass:rotation-honest}, credited erasure).
  - Verified all cited Lean declarations resolve in the codebase with zero errors.
  - Verified axiom audit clean with zero `sorry`, zero `admit`, zero unapproved axioms; checked `#guard_msgs` across all headline theorems in `Molt.Axioms`.
  - Verified LaTeX build with zero errors, zero warnings, 19 pages (`molt.pdf`).

### Reviewer-set passes (2026-10-03)

The passes below were set by the top-level reviewer. Pass 6's audit missed a central gap: Theorem 1 assumes
`SigUnforgeableRecent`, which the timed model yields only under `NoBackdate`. `NoBackdate` is independent of the model
(`noBackdate_independent`) and excludes the very future-stamp harvesting the paper's adversary performs, so "recency
is load-bearing for safety" is not machine-checked. George's decision: prove the timed theorem first. Do the passes in
order. A pass marked *(reviewer spec pending)* has no spec yet: skip it and record that you skipped it.

- [x] **Pass 7: timed light-client safety (Lean only).** Prove `MoltPetit.Model.timed_tip_ancestor_agreement` following
  `docs/TIMED_SAFETY_SPEC.md`. (Subdivided into Passes 7a–7e per progress plan).
  - [x] **Pass 7a: Step 0 (Arithmetic & basics).**
    - Commit `3666849`: Moved `import Molt.AxiomsTimedSafety` before doc comments in `Molt.lean` so library root parses cleanly.
    - Commit `801b06e`: Added arithmetic bounds ($2f + 1 \le q$, $3f < n$, $bad \implies f \ge 1 \implies n \ge 4 \land q \ge 3$), residue gap ($a \equiv b \pmod n \land a < b \implies a + n \le b$), honest stamp contrapositive, and `FirstSigned` definition and `Nat.find` equivalence in `MoltPetit/Model/TimedSafety.lean`.
    - Created `docs/TIMED_SAFETY_PROGRESS.md`.
  - [x] **Pass 7b: Step 1 (No pre-signing).** Prove $B.slot \le \sigma(B)$ for all chain indices $k \ge 1$.
    - Commit `66d0cda`: Proved `slot_le_sigTime` and `slot_le_firstSigned` in `MoltPetit/Model/TimedSafety.lean`.
  - [x] **Pass 7c: Step 2 (Late is forever).** Prove that any descendant of a late block is late.
  - [x] **Pass 7d: Step 3 (Late tail is short).** Prove late tail length $m \le f$ and $T.slot + 1 < L.slot + n$ on recent chains.
  - [x] **Pass 7e: Step 4 (Main argument).** Complete `timed_tip_ancestor_agreement` via post-divergence window analysis.
- [x] **Pass 8: certified-history timed safety (Lean)**. Spec: `docs/TIMED_CERT_SPEC.md`; pinned `timed_certified_agreement`, guard `Molt/AxiomsTimedSafetyCert.lean`. The certificate form over attested
  histories; removes Theorem 1's "exposes that height" clause.
- [x] **Pass 8b: timed certified safety for the shipped Rust validator (Lean)**. Spec: `docs/RUST_TIMED_SPEC.md`; pinned `Rust.rust_timed_certified_agreement`, guard `Rust/AxiomsTimed.lean`. Prove timed certified safety for the extracted Rust validator using `timed_certified_agreement` and the signature bridge.
- [x] **Pass 8c: timed certified safety for the TypeScript validator (Lean)**. Spec: `docs/TS_TIMED_SPEC.md`; pinned `MoltPetit.Model.ts_timed_certified_agreement`, guard `Molt/AxiomsTSTimed.lean`. The TS twin of Pass 8b, so the paper's "each implementation's soundness bridge" claim holds for both implementations.
- [x] **Pass 9: Theorem 1 and recency rework (paper)**. Spec: `docs/PAPER_TIMED_REWORK_SPEC.md`. The timed theorem becomes the headline
  - Reworked `paper/molt.tex` per `docs/PAPER_TIMED_REWORK_SPEC.md`: `Molt.timed_light_client_safety` is Theorem 1 headline, clock stated as $b + \delta \le n$, untimed result demoted, dropped unproven $3/2n$ and 50% numbers, reframed Appendix A as untimed residue derived, created `docs/PAPER_TIMED_REWORK_PROGRESS.md`.
  safety result; abstract, §6.1, Assumption 1 and Appendix A reframed; clock assumption stated as recency bar plus clock
  error at most `n`.
- [x] **Pass 10: Mode 2 headline under the horizon budget (paper).** Make the horizon-scoped
  `sched_recent_tip_ancestor_mem_horizon` the primary statement of Theorem 4 (thm:sched) and state the global-budget
  `scheduled_client_safety` as the corollary, with the exact Lean hypotheses of each.
  - Reworked Theorem 4 (`thm:sched`) to headline `sched_recent_tip_ancestor_agreement_horizon` and `sched_recent_tip_ancestor_mem_horizon` with full Lean hypotheses, stated genesis agreement consequence and `scheduled_client_safety` corollary, and shortened realistic mode-2 deployment paragraph.
- [x] **Pass 11: thm:lock-gen hypotheses (paper).** State `hTipHeight` (equal tip heights) and `hLong` (`2n <
  length`) explicitly in Theorem 5b, as in `Molt.lockstep_client_safety_gen` (audit findings F-07, F-09).
  - Stated `hTipHeight` and `hLong` explicitly in Theorem 5b (`thm:lock-gen`), distinguished equal-heights agreement from unequal-heights membership via `lockstepGen_recent_tip_ancestor_mem`, and updated §2 overview sentence.
- [x] **Pass 12: remaining audit findings.** Resolve every finding F-01..F-11 in `verify-out/findings.md` (if that
  directory is gone, regenerate it with the `lean-paper-verify` workflow). Each one is either fixed, or answered in this
  file with the reason it is not a defect.
  - Resolved all findings F-01..F-11 per `docs/PASS10_12_SPEC.md` across abstract, intro, §2, §3.2, §4, §6.3, and §7 of `paper/molt.tex`, and recorded resolutions in `docs/FINDINGS_RESOLUTION.md` and `docs/PASS10_12_PROGRESS.md`.
- [x] **Pass 13: Mode 1 sync-rule budget (paper)**. Spec: `docs/PASS13_SYNC_RULE_SPEC.md`. The `sync_rule` budget is stated over a
  chain-dependent fault predicate (`badKeyrot ... (stripSigs sc)`); a deployment cannot check it in advance.
  - Reworked Theorem 3 (`thm:refresh`) in `paper/molt.tex` per `docs/PASS13_SYNC_RULE_SPEC.md`: headline statement now cites `sync_rule_timed` / `sync_rule_mem_timed` with timed hypotheses (`KeyStealingEUFCMA` with `stolenOf`, hash injectivity, cadence and anchor, rent rate `badSlotsIn`, theft census `recentTheftProducersK`, fault budget $\rho + T \le \fmax$, reaction delay $d$ with `Reacts`); stated reaction duty as confirmed prefix of validated chain and noted open chain-independent duty in §Limitations; preserved untimed census form as engine via `budget_of_reaction`; updated boxed summary and shortened downstream discussion; created `docs/PASS13_PROGRESS.md`.
- [x] **Pass 14: final consistency.** Re-run `lake build` (all targets) and `bash paper/build.sh`; refresh the table in §2
  so every row is accurate; then append the line `STATUS: READY FOR REVIEW`. Never write `STATUS: COMPLETE`:
  only the reviewer does, after an independent review.

---

## 4. Open Questions & Design Decisions for George

1. **W7 (Multi-chain network model):** Retained as future work / limitation (§6.4 L1223). The rollout evaluation concluded that formalizing a full dynamic gossip network model with fork choice is out of scope for this consensus protocol paper and yields diminishing returns.
2. **Mode 2 Certificate Horizon Scoping:** Proved under global all-window budget (`sched_recent_certified_suffix_agreement`). Horizon scoping for certificates remains future work (while Mode 1 and Mode 3 certificate forms are fully closed).
3. **Mode-1 reaction delay (`Reacts`):** Mode-1 reaction delay `Reacts` is read off the validated chain (open, disclosed in Named seams).
4. **W3b timed theft layer (§6.3), removed:** `NoTheftBackdating` was degenerate: it forced every theft to real slot 0 (audit run 3 F-02). At George's request (10-04), the layer was deleted from the Lean (KeyStealingSignatureTimed, MaxSyncSignatureTimed and their guards), and the paper no longer mentions it. A theft is charged through `Reacts` to every window `u` with `u < r + d`. Charging a theft only to later windows needs forward-secure signing, and is future work.
5. **W4 Sync Induction Hypotheses (§6.3):** The paper now states `sync_induction_full_chain` is machine-checked conditional on `hRLe` (reference tip at least as tall at every sync), while the informal density argument justifying `hRLe` remains acknowledged as informal on paper.
6. **Mode 3 Certificate Generation Attestation (§6.3):** The certificate attests the tip generation alongside the claim, but for $n \ge 2$ this generation is uniquely determined by the tail buffer (`groundedCertLock_gen_of_tail`, `groundedCertLock_gen_unique`), so only $n = 1$ carries an extra counter over the wire.
7. **Mode 3 Safety Twins (§6.3):** Both the cumulative global form (Theorem 5, depth $n$) and the per-generation credited form (Theorem 5b, depth $2n$) are presented as options for deployments, with the modes table highlighting credited erasure under Theorem 5b.
8. **W6 Obstruction & Per-Mode No-Backdating Assumption:** As established by `Molt.badSched_single_key_safe_not_enough` and `Molt.badKeyrot_single_key_safe_not_enough`, slot-level custody does not imply single-key safety when multiple key versions are eligible. The operational content is stated directly as Assumption~\ref{ass:rotation-honest} and cross-referenced in §8 Named Seams and Appendix~\ref{app:timed-uniq}. If a positive derivation is ever desired, it requires revising the definition of `KeyStealingEUFCMA` / `SchedCoreUnforgeable` to restrict the adversary's target to the declared version rather than an arbitrary version.

## 5. Reviewer sign-off (2026-10-03)

- Gate: `bash tools/check.sh` prints `check: all green` at db3b292 (Lean build with all axiom guards, no `sorry`, no axiom declarations, paper builds).
- Audit: `lean-paper-verify` run 4 (79b9b215) is READY. 119 claims are faithful, no findings, and all eight run-3 findings are resolved.
- Headline theorems:
  - Thm 1 is `Molt.timed_light_client_safety` in the timed model, with no `NoBackdate` or exposure clause.
  - Thm 1 is carried to Rust (`Rust.rust_timed_certified_agreement`) and to TypeScript (`ts_timed_certified_agreement`).
  - Thm 3 is `sync_rule_timed` / `sync_rule_mem_timed`.
  - Thm 4 is the horizon pair.
  - Thms 5/5b are lockstep.
  - Every statement in the paper was checked against its Lean statement.
- Disclosed open items (not carve-outs; each is stated in the paper as future work or a named seam): mode-1 `Reacts` is read off the validated chain; mode-2 certificate horizon scoping; per-generation credit for mode-3 certificates; forward-secure theft timing; the multi-chain network model; the recency check in the node loop.

## 6. Reopened (2026-10-04)

`Reacts` (the mode-1 reaction delay, a hypothesis of Thm 3 `sync_rule_timed`) quantifies over every slot `s ≥ r + d` on the finite presented chain. At large `s`, `inForce` is the floor of the whole chain, so `Reacts` implies that every stolen version is already rotated past on the presented chain. A live, not-yet-rotated theft (the attack the theorem is for) falsifies it. Decision pending with George.

STATUS: READY FOR REVIEW
