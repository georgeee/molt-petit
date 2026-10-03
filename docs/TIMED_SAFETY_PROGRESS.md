# Timed Light-Client Safety — Progress Log

Tracking implementation of `MoltPetit.Model.timed_tip_ancestor_agreement` per `docs/TIMED_SAFETY_SPEC.md`.

## Status Summary

- [x] **Step 0: Arithmetic and basics** (Pass 7a)
  - `two_mul_maxByzantine_add_one_le_quorum`: $2f + 1 \le q$
  - `three_mul_maxByzantine_lt`: $3f < n$ for $n \ge 1$
  - `maxByzantine_pos_of_bad`: any bad slot implies $f \ge 1$ under `ByzantineBounded`
  - `four_le_of_maxByzantine_pos`: $f \ge 1 \implies 4 \le n$
  - `three_le_quorum_of_maxByzantine_pos`: $f \ge 1 \implies 3 \le q$
  - `add_le_of_mod_eq_of_lt`: $a \equiv b \pmod n \land a < b \implies a + n \le b$
  - `bad_of_signed_ne_slot`: block signed at $r$ with stamp $
e r$ implies $bad\ r$
  - `FirstSigned`: definition and equivalence with `Nat.find`
  - Monotonicity lemmas reused from `MoltPetit.Model.Timed`: `sigTime_mono_step`, `sigTime_mono_chain`, `one_real_slot_one_block`.
- [ ] **Step 1: No pre-signing** (Pass 7b)
  - Goal: For every index $k \ge 1$, $B.slot \le \sigma(B)$.
  - Method: Induction on index $k$; contradiction via `MaturedWindowsDense` on $[B.slot - n, B.slot)$ having $\le 1$ block $< q$.
- [ ] **Step 2: Late is forever** (Pass 7c)
  - Goal: If $P$ (index $\ge 1$) is late and $N$ is its child, then $N$ is late.
- [ ] **Step 3: Late tail is short on a recent chain** (Pass 7d)
  - Goal: Tail of late blocks has length $m \le f$ and $T.slot + 1 < L.slot + n$.
- [ ] **Step 4: Main argument** (Pass 7e)
  - Goal: Prove `timed_tip_ancestor_agreement` using divergence index, matured window $W_1$, honest slot disjointness and cases.
