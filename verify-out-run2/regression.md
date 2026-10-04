Progress: Part A (all 17 hunks in git diff main..HEAD across paper/molt.tex, Molt/, MoltPetit/) and Part B (audit of all occurrences of 'future work', 'informal', 'not machine-checked', 'assumed', and 'open' in paper/molt.tex in both directions) fully covered.

# Skeptical Referee Regression Audit: main..HEAD

## Executive Summary & Lean Changes Assessment

1. **Are the Lean changes purely presentational?**
   **YES.**
   - In `MoltPetit/`: Zero changes (`git diff main..HEAD -- MoltPetit/` is empty).
   - In `Molt/Axioms.lean`: Added `#guard_msgs` axiom checks for headline theorems (`lockstep_client_safety_gen`, `lockstep_client_safety_timed`, `lockstep_recent_certified_suffix_agreement`, `lockstep_cert_gen_pinned`, `cert_sync_rule`, `keyrot_certified_suffix_agreement_anchored`, `sync_rule_timed`, `max_sync_period_timed`, `max_sync_period_tight`, `paced_tight_census_bound_all_F`, `paced_separation_witnessed`, `sync_induction_full_chain`, `badSched_single_key_safe_not_enough`, `badKeyrot_single_key_safe_not_enough`). All theorems depend only on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) or no axioms at all (`badSched_single_key_safe_not_enough`, `badKeyrot_single_key_safe_not_enough`).
   - In `Molt/LockstepCert.lean`: Added 2 `alias` declarations (`groundedCertLock_gen_of_tail`, `groundedCertLock_gen_unique`) re-exporting existing `MoltPetit.Model` lemmas.
   - In `Molt/LockstepGen.lean`: Added 1 `abbrev` (`ErasureTimedLock`) and 5 `alias` declarations (`genBound_of_preRetirementBound`, `lockstepGen_recent_tip_ancestor_mem`, `lockstepGen_recent_genesis_agreement`, `lockstepGen_shared_prefix_sharp`, `window_shared_prefix`, `LockstepPackage.toGen`), all re-exporting existing `MoltPetit.Model` definitions and theorems.
   - In `Molt/Rotation.lean`: Added 2 `abbrev` declarations (`SchedCoreUnforgeable`, `NoPrematureTheft`) re-exporting existing `MoltPetit.Model` definitions.
   - **Conclusion**: The Lean changes are strictly presentational re-exports, abbreviations, and axiom verification tests. No new axioms were introduced, no proofs were altered or weakened, and there are zero `sorry`s.

2. **Summary of Findings in Paper (`paper/molt.tex`):**
   - **MAJOR**: Theorem~\ref{thm:lock-gen} (line 1167, commit 66f9e96) claims that any two accepted chains with recent tips agree on the block $2n$ below each tip without conditioning on equal tip heights. In Lean, `lockstep_client_safety_gen` explicitly requires `sTip.height = sTip'.height`. For unequal heights, the lower tip's confirmed block lies on the taller chain (`lockstepGen_recent_tip_ancestor_mem`), but they do not agree on "the block $2n$ below each tip" because those blocks sit at different heights.
   - **MAJOR**: In §6.3 (line 1208, commit 66f9e96), the text conjoins certificate presentation `lockstep_recent_certified_suffix_agreement` with depth $2n$ under Theorem~\ref{thm:lock-gen}, and §6.3 Honest Scope (line 1253, commit 1c2891f) omits mode 3 certificates when scoping future work. In Lean, `lockstep_recent_certified_suffix_agreement` is proved exclusively under the cumulative fault budget (`LockstepPackage`, depth $n$). Mode 3 certificate presentation under the per-generation package (`LockstepPackageGen`, depth $2n$) is unformalized and remains future work.
   - **MINOR**: In §4 (line 451, commit 146f554), stating that mode checks at certificate level "are proved for all three modes" is formally true for all three cited theorems, but elides the caveat that modes 2 and 3 certificates are proved only under global/cumulative budgets, unlike mode 1's anchored trailing form.

---

## Part A: Hunk-by-Hunk Review of `git diff main..HEAD`

### Hunk 0: line 117 (commit 31e0fc1)
- **Diff**: `clients of the other two modes obey no rule at all.` $\to$ `clients of the other two modes obey no cadence rule at all.`
- **Audit**: Clarification is accurate. In modes 2 and 3, clients do not have a periodic synchronization cadence requirement (unlike mode 1's $n$-slot sync cadence), but still execute verification rules. No overclaiming.

### Hunk 1: lines 231-238 (commit 146f554)
- **Diff**: Mode 3 overview updated to claim certificate presentation (`lockstep_recent_certified_suffix_agreement`) and per-generation credit at depth $2n$ without shared genesis (`lockstep_client_safety_gen`).
- **Audit**: `lockstep_client_safety_gen` proves safety at depth $2n$ without assuming shared genesis (`lockstepGen_recent_genesis_agreement`). However, juxtaposing this with `lockstep_recent_certified_suffix_agreement` without clarifying that the certificate theorem is strictly under the cumulative package (depth $n$) creates an overclaim that per-generation credit applies to certificates (see Finding 2).

### Hunk 2: lines 449-453 (commit 146f554)
- **Diff**: Stating that certificate-level checks are proved for all three modes (`keyrot_recent_certified_suffix_agreement`, `sched_recent_certified_suffix_agreement`, `lockstep_recent_certified_suffix_agreement`).
- **Audit**: All 3 Lean theorems exist and match their statements in `verify-out/lean-statements.txt`. As noted, modes 2 and 3 certificate theorems are under global/cumulative budgets; caveat is addressed in Finding 3.

### Hunk 3: line 616 (commit 146f554)
- **Diff**: `(\code{keyrot_recent_certified_suffix_agreement} and its scheduled twin)` $\to$ `(\code{keyrot_recent_certified_suffix_agreement} and its scheduled and lockstep twins)`.
- **Audit**: Accurate; `lockstep_recent_certified_suffix_agreement` exists.

### Hunk 4: lines 663-664 (commit 31e0fc1)
- **Diff**: Added caveat: `--- argued, not proved (the representability lemmas are production-side), which is why the hypothesis stays in the statement.`
- **Audit**: Rigorous and accurate caveat addition; correctly acknowledges that re-presentation is argued rather than Lean-checked.

### Hunk 5: lines 796-798 (commit 1c2891f)
- **Diff**: Added Assumption~\ref{ass:rotation-honest} (No back-dating, honest custody per mode), citing `KeyStealingEUFCMA`, `SchedCoreUnforgeable`, `badSched_single_key_safe_not_enough`, `badKeyrot_single_key_safe_not_enough`.
- **Audit**: All 4 cited Lean names match Lean declarations. The justification that per-key EUF-CMA does not imply slot-safety is substantiated by the two counterexample obstruction theorems in `MoltPetit.Model` and `Molt`. Caveat is necessary and properly stated.

### Hunk 6: lines 858-859 (commit 31e0fc1)
- **Diff**: Mode 1 budget definition refined to: `slots plus producers with a stolen key not yet retired there --- their version in force, or any later one --- total at most \fmax per window.`
- **Audit**: Matches Lean definition `KeyStealingHorizon.badKeyrotOn` / `stolenNotRetired`. Necessary precision to prevent understating retroactive theft counting.

### Hunk 7: lines 894-895 (commit 31e0fc1)
- **Diff**: Mode 1 retroactive census: `window counts every producer any of whose versions not yet retired there is ever stolen`.
- **Audit**: Exactly matches formalization.

### Hunk 8: lines 920-937 (commit 5b68719)
- **Diff**: Mode 1 anchored certificate presentation (`keyrot_certified_suffix_agreement_anchored`, `cert_sync_rule`, `cert_max_sync_period`) and reaction delay (`budget_of_reaction`, `sync_rule_timed`, `max_sync_period_timed`).
- **Audit**: All cited names exist in Lean. Statements match: `keyrot_certified_suffix_agreement_anchored` proves $n$-deep agreement when the anchor is contained in the verified suffixes (`s1 :: srest`). Reaction delay `Reacts` is properly noted as asserted rather than derived.

### Hunk 9: lines 969-985 (commit 5b68719)
- **Diff**: Paced adversary and timed theft layer: `Reacts`, `NoTheftBackdating`, `theft_exposure_window`, `paced_tight_census_bound_all_F`, `max_sync_period_tight`, `client_refresh_rule`, `stay_recent_client_safe`.
- **Audit**: All Lean theorems match. Explicitly notes that `NoTheftBackdating` is an asserted operational hypothesis, and that deriving it from mint-timed signature primitives is future work.

### Hunk 10: lines 1027-1028 (commit 31e0fc1)
- **Diff**: Mode 1 budget summary: `producers with a stolen key not yet retired there --- their version in force, or any later one --- total at most T, \rho + T \le 2`.
- **Audit**: Accurate refinement of the census definition.

### Hunk 11: lines 1036-1045 (commit 5b68719)
- **Diff**: Replaced "argued on paper, not itself machine-checked" for sync induction with machine-checked `sync_induction_full_chain`, while keeping the caveat that the height comparison hypothesis is argued informally via density and not machine-checked.
- **Audit**: Matches Lean: `sync_induction_full_chain` takes `(tip k).height \le (rTip k).height` as a hypothesis. Fully accurate caveat preservation.

### Hunk 12: lines 1166-1175 (commit 66f9e96)
- **Diff**: Theorem~\ref{thm:lock-gen} (`lockstep_client_safety_gen`), `lockstepGen_recent_genesis_agreement`, `lockstep_window_declares_rosterGen`, `window_shared_prefix`, `lockstepGen_shared_prefix_sharp`, `LockstepPackage.toGen`, `ErasureTimedLock`, `genBound_of_preRetirementBound`, `lockstep_client_safety_timed`.
- **Audit**:
  - Overclaim in Theorem~\ref{thm:lock-gen}: Lean theorem `lockstep_client_safety_gen` requires `sTip.height = sTip'.height`. The theorem prose states "any two accepted chains with recent tips agree on the block $2n$ below each tip" without conditioning on equal tip heights (see Finding 1).
  - All other lemmas (`window_shared_prefix`, `lockstepGen_shared_prefix_sharp`, `LockstepPackage.toGen`, `ErasureTimedLock`, `genBound_of_preRetirementBound`, `lockstep_client_safety_timed`) match their Lean statements faithfully.

### Hunk 13: lines 1185-1215 (commit 66f9e96)
- **Diff**: Mode 3 certificate presentation (`groundedCertLock_gen_of_tail`, `groundedCertLock_gen_unique`, `lockstep_client_safety`, `lockstep_recent_tip_ancestor_mem`, `lockstep_declares_rosterGen`, `lockstep_recent_certified_suffix_agreement`, `lockstep_cert_gen_pinned`, `same_block_same_prefix`).
- **Audit**:
  - Overclaim: The text states "and at the certificate presentation `lockstep_recent_certified_suffix_agreement` ... any two accepted chains agree --- at equal heights on the block $n$ below each tip (or $2n$ under Theorem~\ref{thm:lock-gen})". In Lean, `lockstep_recent_certified_suffix_agreement` is proved ONLY under the cumulative package at depth $n$. There is no certificate theorem for per-generation credit at depth $2n$ (see Finding 2).
  - All cited Lean declarations exist and their statements match.

### Hunk 14: lines 1232, 1239-1240 (commit 66f9e96)
- **Diff**: Mode table and summary: Mode 3 erasure credited under Thm~\ref{thm:lock-gen} at depth $2n$.
- **Audit**: Matches full-chain theorem `lockstep_client_safety_gen`.

### Hunk 15: lines 1244-1260 (commit 1c2891f)
- **Diff**: Honest scope consolidation: `theft_exposure_window`, `NoTheftBackdating`, `paced_tight_census_bound_all_F`, `paced_budget_holds_under_timing`, Theorem~\ref{thm:lock-gen}, `sched_recent_certified_suffix_agreement`, `badSched_single_key_safe_not_enough`, `badKeyrot_single_key_safe_not_enough`, Assumption~\ref{ass:rotation-honest}.
- **Audit**: Accurately bounds the timed theft layer and explains the non-derivation of Assumption~\ref{ass:rotation-honest}. However, item 2 notes that mode 2 certificate is proved under a global budget, but omits that mode 3 certificate is ALSO proved only under a global/cumulative budget (see Finding 2).

### Hunk 16: lines 1480-1483 (commit 1c2891f)
- **Diff**: In §8 Limitations: explicitly records that key-stealing signature surface cannot be derived via Appendix A.2's technique without weakening per-key premises, referencing Assumption~\ref{ass:rotation-honest}.
- **Audit**: Faithful to Lean counterexamples.

### Hunk 17: lines 1589-1596 (commit 1c2891f)
- **Diff**: Appendix A.2: records non-derivation of per-mode key-stealing surfaces and cites `badSched_single_key_safe_not_enough` and `badKeyrot_single_key_safe_not_enough`.
- **Audit**: Faithful to Lean theorems.

---

## Part B: Bidirectional Audit of Keywords

We audited all occurrences of `future work`, `informal`, `not machine-checked`, `assumed` (including `assumption`), and `open` in `paper/molt.tex` against Lean sources in both directions:

1. **`future work` (8 occurrences)**:
   - Line 969: Certifying a mode 1 fork execution end-to-end in Lean is future work. (Verified: Lean has obstruction counterexamples, but no full execution trace proof. Lean does not prove this; paper correctly marks as future work.)
   - Line 984: Deriving no-back-dating from mint-timed signatures, and honest fork-choice model, are future work. (Verified: Neither is in Lean. Correct.)
   - Line 1132: Carrying horizon scoping to mode 2 certificates is future work. (Verified: `sched_recent_certified_suffix_agreement` is under global budget. Lean does not have a horizon-scoped cert theorem. Correct.)
   - Line 1251: Deriving no-theft-backdating from mint-timed primitives remains future work. (Verified: Correct.)
   - Line 1255: Carrying horizon scoping to mode-2 certificates is future work. (Verified: Correct, but misses noting mode 3 cert per-generation scoping; see Finding 2.)
   - Line 1285: Multi-chain network model is future work. (Verified: Lean models single-chain validity progress; no network-level gossip/fork-choice model. Correct.)
   - Line 1440: Section header: Limitations and future work.
   - Line 1489: Threading `now` through pure validators is mechanical future work. (Verified: Pure validators take no clock; `now` is an external theorem parameter. Correct.)

2. **`informal` (2 occurrences)**:
   - Line 1042: Density remark argued informally; not machine-checked. (Verified: `sync_induction_full_chain` takes `(tip k).height \le (rTip k).height` as a hypothesis; density is not mechanized. Correct.)
   - Line 1082: Cold-root custody stays informal. (Verified: Key hierarchy from cold roots is not modeled in Lean. Correct.)

3. **`not machine-checked` (2 occurrences)**:
   - Line 1043: Density remark is not itself machine-checked. (Verified: Correct.)
   - Line 1477: Everything not machine-checked is a named hypothesis. (Verified: All 110 cited Lean symbols verified against `lean-statements.txt`; `#print axioms` verifies zero unproven axioms/sorrys. Correct.)

4. **`assumed` / `assumption`**:
   - Line 496: "confirms that nothing further is assumed behind the scenes" (Verified: Axiom audit confirms only Lean standard axioms).
   - Line 770: "no forward security is assumed" (Verified: Matches timeless adversary model).
   - Line 797: Assumption~\ref{ass:rotation-honest} (Verified: Matches Lean obstruction theorems).
   - Line 872: Window reach assumption (Verified).
   - Line 930: Budget need not be assumed outright under `Reacts` (Verified: `budget_of_reaction`).
   - Line 1167: No shared genesis is assumed in Theorem~\ref{thm:lock-gen} (Verified: `lockstepGen_recent_genesis_agreement` derives common block at index 0 without assuming shared genesis).
   - Line 1462: Recency rule is a clock check (Verified).
   - Line 1480: Key-stealing surface assumed, not derived (Verified).

5. **`open` (0 occurrences)**:
   - Zero occurrences in `paper/molt.tex`.

---

## Findings

- [MAJOR] tex line 1167, commit 66f9e96: Theorem~\ref{thm:lock-gen} claims that any two accepted chains with recent tips agree on the block $2n$ below each tip without conditioning on equal tip heights, whereas Lean's `lockstep_client_safety_gen` explicitly requires `sTip.height = sTip'.height` -> Amend Theorem~\ref{thm:lock-gen} statement to distinguish equal and unequal heights, matching Theorem~\ref{thm:lock} and line 1211: "agree: at equal heights on the block $2n$ below each tip; at unequal heights the lower chain's $2n$-deep block lies on the taller (\code{lockstepGen_recent_tip_ancestor_mem})".
- [MAJOR] tex line 1208, commit 66f9e96: Text in §6.3 conjoins certificate presentation `lockstep_recent_certified_suffix_agreement` with depth $2n$ under Theorem~\ref{thm:lock-gen}, and §6.3 Honest Scope (line 1253, commit 1c2891f) omits mode 3 certificates when scoping future work, but in Lean `lockstep_recent_certified_suffix_agreement` is proved exclusively under the cumulative fault budget at depth $n$, and per-generation credit at depth $2n$ is proved only for full chains -> Clarify in §2, §6.3, and Honest Scope that mode 3's certificate presentation theorem is established only under the cumulative budget at depth $n$, and that lifting certificates to per-generation erasure credit at depth $2n$ remains future work.
- [MINOR] tex line 451, commit 146f554: §4 states that validator checks at certificate level "are proved for all three modes", but does not note that for modes 2 and 3 the certificate theorems assume global/cumulative budgets rather than horizon or per-generation budgets -> Add a parenthetical clarification that mode 2 and mode 3 certificate theorems are proved under global/cumulative budgets.

REGRESSION: DONE
