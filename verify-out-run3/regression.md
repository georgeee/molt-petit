Progress: Part A (review git diff main..HEAD -- paper/ Molt/ MoltPetit/ hunk by hunk) and Part B (audit remaining future work, informal, not machine-checked, assumed, open phrases in paper/molt.tex against Lean in both directions) fully covered.

# Regression Audit: Skeptical Referee Report

## Findings Summary

- [MINOR] tex line 1143, commit 58d5a98: text states "The global-budget \code{scheduled\_client\_safety} is the corollary at any $H$ (\code{byzantineBoundedFrom\_of\_bounded})" -> In Lean, `scheduled_client_safety` is not formalized as a corollary of `sched_recent_tip_ancestor_agreement_horizon` (it retains legacy `hHead`/`hHead'` shared-genesis hypotheses and delegates to the un-horizoned theorem; formal reduction is noted in code comments as unformalized): rephrase to clarify that `scheduled_client_safety` is the earlier global-budget theorem whose budget hypothesis is subsumed by `byzantineBoundedFrom_of_bounded`.
- [MINOR] tex line 1141, commit 58d5a98: text states "There is no shared-genesis hypothesis: genesis agreement is a consequence (\code{sched\_recent\_genesis\_agreement\_horizon})" -> In Lean, `sched_recent_genesis_agreement_horizon` requires both chains to be longer than $n$ (`hLong` and `hLong'`), whereas the preceding sentence noted that unequal-height membership requires length $> n$ only for the lower chain: clarify that the genesis agreement consequence specifically requires both chains to exceed length $n$.
- [MINOR] tex line 1248, commit 073bd52: text states "Through the parent-id chain, they agree on their whole common prefix down to height 0: no shared genesis is assumed (\code{lockstepGen\_recent\_genesis\_agreement})" -> In Lean, `lockstepGen_recent_genesis_agreement` requires both chains to satisfy $2n < \mathit{length}$ (`hLong` and `hLong'`), unlike unequal-heights membership which needs $2n < \mathit{length}$ only for the lower chain: clarify that common prefix / genesis agreement requires both chains to exceed $2n$.
- [MINOR] tex line 271, commit b59125e: Table 1 lists "genesis + clock + $\mathit{gen}$" under "client holds" for Mode 2 -> Lines 1141, 1146-1147, and 1184 emphasize that Mode 2 clients do not need genesis ("genesis agreement is a consequence", "client holds a clock and the constant $\mathit{gen}$"): change Table 1 Mode 2 "client holds" to "clock + $\mathit{gen}$ (genesis optional/derived)" for consistency.

---

## Part A: Review of `git diff main..HEAD -- paper/ Molt/ MoltPetit/`

### 1. Are the Lean changes purely presentational?
**No.** The Lean changes in `main..HEAD` are not purely presentational:
1. **New mathematical proofs and theorems**:
   - `MoltPetit/Model/TimedSafety.lean` (910 lines): complete machine-checked proof of `timed_tip_ancestor_agreement` (commits `801b06e` through `7038323`), establishing safety directly in the timed execution model without relying on the untimed residue assumption.
   - `MoltPetit/Model/TimedSafetyCert.lean` (132 lines): machine-checked proof of `timed_certified_agreement` (commit `b6d47c0`), lifting timed tip agreement to recursive certificate presentations.
   - `Rust/TimedResults_rust.lean` and `Rust/AxiomsTimed.lean`: machine-checked proof of `Rust.rust_timed_certified_agreement` (commit `a7c31aa`).
2. **Refactoring**:
   - `MoltPetit/Model/Grounded.lean`: factored out `grounded_suffix_history_of` to cleanly separate chain validity of certificate-extended histories (commit `f24bfd1`).
3. **Presentational / Export Layer**:
   - `Molt/Results.lean`: exported `timed_light_client_safety` alias/wrapper.
   - `Molt/LockstepGen.lean`: exported aliases `ErasureTimedLock`, `genBound_of_preRetirementBound`, `lockstepGen_recent_tip_ancestor_mem`, `lockstepGen_recent_genesis_agreement`, `lockstepGen_shared_prefix_sharp`, `window_shared_prefix`, `LockstepPackage.toGen`.
   - `Molt/Rotation.lean`: exported abbrevs `SchedCoreUnforgeable`, `NoPrematureTheft`.
   - `Molt/LockstepCert.lean`: exported `groundedCertLock_gen_unique`.
   - `Molt/Axioms.lean`, `Molt/AxiomsTimedSafety.lean`, `Molt/AxiomsTimedSafetyCert.lean`: added `#guard_msgs` checks for standard axioms.

### 2. Hunk-by-Hunk Audit of `paper/molt.tex`

- **Abstract (lines 62-73, commits 0691a88, d88ee0c)**:
  - *Claim*: Safety claims machine-checked under Section 5 assumptions; circuit-backend faithfulness stated as trust assumption; light-client safety proved directly in timed model; recency check machine-checked safety ingredient.
  - *Audit*: Accurately reflects `timed_light_client_safety` and explicit trust boundary. No overclaiming.
- **Section 1 Introduction (lines 90-92, 122, 129-130, 160-161, 183-185, commits 0691a88, 31e0fc1, d88ee0c)**:
  - *Claim*: `Rust.rust_timed_certified_agreement` cited under Section 5 assumptions; circuit-backend faithfulness noted as trust assumption; recency bound $b + \delta \le n$; `liveness_produce_blockK` qualified as local single-block production step under continued density coverage.
  - *Audit*: Matches Lean implementation and resolves F-01..F-04.
- **Section 2 Overview & Table 1 (lines 238-288, commits 146f554, b59125e, 0691a88)**:
  - *Claim*: Mode 3 certificate presentation holds under cumulative budget at depth $n$ (`lockstep_recent_certified_suffix_agreement`), while per-generation credit at depth $2n$ remains future work for certificates; per-generation credit machine-checked for full chains (`lockstep_client_safety_gen`, `lockstepGen_recent_tip_ancestor_mem`). Table 1 collects all four modes with their headline theorems.
  - *Audit*: Accurately mirrors Lean theorems. (Minor note recorded regarding Mode 2 genesis in Table 1).
- **Section 3.1 & 3.2 Combinatorial Engine (lines 322-342, 396-400, commits d88ee0c, 0691a88)**:
  - *Claim*: Notation table updated for $b + \delta \le n$; counting argument characterized as core combinatorial engine around which cryptographic layers and certificates are built.
  - *Audit*: Consistent with Lean definitions and proofs.
- **Section 4 Rules (lines 460-475, 504-508, commits d88ee0c, 146f554)**:
  - *Claim*: Recency check updated to $now \le tip.slot + b$ with $R \le now + \delta$ and $b + \delta \le n$. Certificate presentation theorems cited for all three modes (modes 2 and 3 under cumulative budget at depth $n$).
  - *Audit*: Hypotheses and statements match Lean.
- **Section 5 Assumptions (lines 561-652, commit 58ab21d)**:
  - *Claim*: Restated for timed execution (`TimedExecution`), real slots, collision resistance over occurring blocks (`TimedExecution.id_inj` over `SignedEver`), clock condition $b + \delta \le n$.
  - *Audit*: Exactly aligns with Lean definitions in `MoltPetit/Model/TimedSig.lean` and `MoltPetit/Model/TimedSafety.lean`.
- **Section 6.1 Light-Client Safety / Theorem 1 (lines 665-738, commits 4b7ff9a, 781d896)**:
  - *Claim*: Theorem 1 re-anchored to `timed_light_client_safety`. Proof idea updated to reflect `late_tail_short` rather than Theorem 2 (`thm:forge`). Untimed model noted as legacy.
  - *Audit*: Matches Lean theorem `Molt.timed_light_client_safety` verbatim.
- **Section 6.2 Forged Time (lines 793-802, commits 781d896, 4b7ff9a)**:
  - *Claim*: Rate argument connects `thm:forge` and `thm:lc`.
  - *Audit*: Matches Lean formalization.
- **Section 6.3 Mode 1 / Theorem 3 (lines 850-853, 894-925, 960-961, 986-1047, 1089-1106, commits 1c2891f, fcb3b8d, 31e0fc1, 5b68719)**:
  - *Claim*: Assumption 6 (no backdating honest custody) stated; Theorem 3 updated to `sync_rule_timed` and `sync_rule_mem_timed` with trailing $5n$ window and reaction delay $d$; `Reacts` noted as evaluated on the chain being validated; anchored certificate sync rule `keyrot_certified_suffix_agreement_anchored`; timed theft and tight census (`theft_exposure_window`, `paced_tight_census_bound_all_F`); sync induction over full chains (`sync_induction_full_chain`).
  - *Audit*: Exact correspondence with Lean theorems. Caveats on `Reacts` and height hypothesis in sync induction are explicitly declared.
- **Section 6.3 Mode 2 / Theorem 4 (lines 1124-1146, 1185-1195, commit 58d5a98)**:
  - *Claim*: Theorem 4 updated to horizon budget `sched_recent_tip_ancestor_agreement_horizon` and `sched_recent_tip_ancestor_mem_horizon`, with genesis agreement `sched_recent_genesis_agreement_horizon`.
  - *Audit*: Exact correspondence with Lean theorems. (Minor note recorded regarding corollary description).
- **Section 6.3 Mode 3 / Theorem 5b (lines 1233-1296, 1300-1323, commits 073bd52, 66f9e96, 0691a88, b59125e, 1c2891f)**:
  - *Claim*: Theorem 5b `lockstep_client_safety_gen` and `lockstepGen_recent_tip_ancestor_mem` under per-generation census; erasure formalization via `ErasureTimedLock` and `genBound_of_preRetirementBound`; certificate presentation under cumulative budget; future work boundaries for certificate per-gen credit.
  - *Audit*: Exact correspondence with Lean theorems.
- **Section 7 Implementation (lines 1373-1374, commit 0691a88)**:
  - *Claim*: Added `Rust.rust_timed_certified_agreement` under timed model and certificate bridge.
  - *Audit*: Fully verified in `Rust/TimedResults_rust.lean`.
- **Section 8 Limitations & Appendix A (lines 1508-1668, commits 4f3cc55, 1c2891f, e100ddc)**:
  - *Claim*: Explicit enumeration of named trust boundaries; Appendix A reframed as untimed residue derivation (`SigUnforgeableRecent` from `NoBackdate` + EUF-CMA) not consumed by Theorem 1; single-key safety obstruction counterexamples (`badSched_single_key_safe_not_enough`, `badKeyrot_single_key_safe_not_enough`).
  - *Audit*: Accurately reflects mathematical facts and Lean counterexamples.

---

## Part B: Audit of "Future Work", "Informal", "Not Machine-Checked", "Assumed", and "Open"

All 22 occurrences in `paper/molt.tex` were audited against the Lean formalization in both directions:

1. **Line 241 ("future work")**: Lifting Mode 3 certificates to per-generation erasure credit at depth $2n$ remains future work.
   - *Lean status*: True in Lean. `lockstep_recent_certified_suffix_agreement` is proved only under the cumulative budget at depth $n$. Per-generation credit at depth $2n$ is proved only for full chains (`lockstep_client_safety_gen`).
2. **Line 552 ("assumed")**: `#print axioms confirms that nothing further is assumed behind the scenes`.
   - *Lean status*: True in Lean. All headline theorems (`timed_light_client_safety`, `sync_rule_timed`, `sched_recent_tip_ancestor_agreement_horizon`, `lockstep_client_safety_gen`, etc.) depend strictly on standard Lean kernel axioms `[propext, Classical.choice, Quot.sound]`. No `sorry` and no `axiom` declarations exist in the repository.
3. **Line 724 ("assumed")**: Honest-slot uniqueness of chain blocks is derived, not assumed.
   - *Lean status*: True in Lean. Proved in `MoltPetit/Model/TimedSafety.lean` via `late_tail_short`, `late_is_forever`, and `timed_tip_ancestor_agreement`.
4. **Line 824 ("assumed")**: No forward security is assumed.
   - *Lean status*: True in Lean. Adversary with stolen key of version $j$ can sign arbitrarily at any slot in `KeyStealingEUFCMA`.
5. **Line 851 ("assumed")**: Assumption 6 (no back-dating, honest custody per mode) is stated directly rather than derived from timed model.
   - *Lean status*: True in Lean. Obstruction theorems `badSched_single_key_safe_not_enough` and `badKeyrot_single_key_safe_not_enough` machine-check that single-key safety does not imply slot safety when multiple versions are eligible.
6. **Line 917 ("open")**: Mode 1 reaction delay quantified only over honest chain is open.
   - *Lean status*: True in Lean. `Molt.Reacts` is evaluated on `stripSigs sc` (the chain being validated); no theorem in Lean proves safety from honest-chain reaction alone.
7. **Line 938 ("assumed")**: Nothing assumed about windows starting earlier than trailing $5n$.
   - *Lean status*: True in Lean. The premise `now < u + 5*n` in `sync_rule_timed` restricts budget quantification strictly to trailing windows.
8. **Line 1031 ("future work")**: Certifying one such execution end-to-end in Lean is future work.
   - *Lean status*: True in Lean. Mode 1 takes `Reacts` and `NoTheftBackdating` as hypotheses rather than embedding interactive execution semantics.
9. **Line 1046 ("future work")**: Deriving no-back-dating from mint-timed signature primitives and model where honest nodes never extend adversarial forks are future work.
   - *Lean status*: True in Lean. `NoTheftBackdating` is taken as a Prop hypothesis.
10. **Line 1104 ("informal")**: Height comparison in sync induction is argued informally, not machine-checked.
    - *Lean status*: True in Lean. `Molt.sync_induction_full_chain` takes `(∀ k, (tip k).height ≤ (rTip k).height)` as an explicit hypothesis.
11. **Line 1156 ("informal")**: Cold-root custody stays informal.
    - *Lean status*: True in Lean. Key provisioning ceremonies and offline root key safety are operational assumptions.
12. **Line 1199 ("future work")**: Carrying horizon scoping to Mode 2 certificates is future work.
    - *Lean status*: True in Lean. `sched_recent_certified_suffix_agreement` consumes global budget `FaultBounded n (badSched ...)`.
13. **Line 1248 ("assumed")**: No shared genesis is assumed in Mode 3 per-generation safety.
    - *Lean status*: True in Lean. `lockstepGen_recent_genesis_agreement` and `lockstep_client_safety_gen` do not assume `blockAt? c 0 = some G`.
14. **Line 1311 ("future work")**: Deriving no-theft-backdating from mint-timed signature primitives remains future work.
    - *Lean status*: True in Lean. Identical to Line 1046.
15. **Line 1318 ("future work")**: Carrying horizon scoping to Mode 2 certificates and per-generation erasure credit to Mode 3 certificates at depth $2n$ remain future work.
    - *Lean status*: True in Lean. Matches findings for lines 241 and 1199.
16. **Line 1348 ("future work")**: Fully multi-chain network model is future work.
    - *Lean status*: True in Lean. `global_liveness` assumes honest blocks arrive in a single chain.
17. **Line 1504 ("future work")**: Section 8 title "Limitations and future work".
18. **Line 1526 ("assumed")**: Network synchrony is never assumed.
    - *Lean status*: True in Lean. Delivery is asynchronous / adversarial across all safety theorems.
19. **Line 1541 ("not machine-checked")**: Circuit backend faithfulness stated rather than proved.
    - *Lean status*: True in Lean. `valid_chain_be_validChain` proves equivalence between Rust extracted code and Lean specification, but circuit compilation semantics are assumed.
20. **Line 1544 ("assumed")**: Key-stealing signature surface assumed, not derived from timed model.
    - *Lean status*: True in Lean. Restates Assumption 6.
21. **Line 1553 ("future work")**: Threading `now` through pure validators is mechanical future work.
    - *Lean status*: True in Lean. The pure validator functions do not inspect real-time clocks.
22. **Line 1560 ("open")**: Form of reaction delay quantified only over honest chain is open.
    - *Lean status*: True in Lean. Restates Line 917.

### Reverse Direction Check
- Are there unproved conjectures, `sorry`, or custom axioms claimed as proved?
  - Audited: 0 `sorry`, 0 custom axioms across the entire repository. All cited Lean names correspond to fully proved theorems in Lean 4.

REGRESSION: DONE
