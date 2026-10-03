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
- [x] **Step 1: No pre-signing** (Pass 7b)
  - `slot_le_sigTime`: for every index $k \ge 1$, $B.slot \le \text{Nat.find } hBsig$.
  - `slot_le_firstSigned`: for every index $k \ge 1$ and `FirstSigned log B r`, $B.slot \le r$.
  - Proved by strong induction on $k$: if $r = \sigma(B) < B.slot$, then $r$ is bad, $r + n \le B.slot$, $q \ge 3$; by IH and monotonicity any ancestor before $P$ has slot $< P.slot \le \sigma(P) \le \sigma(B) \le B.slot - n$, so matured window $[B.slot - n, B.slot)$ contains at most $P$, giving windowCount $\le 1 < 3 \le q$, contradiction.
- [x] **Step 2: Late is forever** (Pass 7c)
  - `late_step`: if $P$ (index $\ge 1$) is late and $N$ is its child, then $N$ is late.
  - `late_chain`: any descendant at index $k + d$ of a late block is late.
  - Proved by contradiction: if $N$ were on time, $N.slot = \sigma(N) \ge \sigma(P) \ge P.slot + n$, making window $[P.slot + 1, P.slot + n]$ matured at $N$. The window can contain only $N$ among chain blocks, giving windowCount $\le 1 < 3 \le q$, contradiction.
- [x] **Step 3: Late tail is short on a recent chain** (Pass 7d)
  - `belowCount_mono`: monotonicity of belowCount in slot bound.
  - `div_zero_of_quorum_le`: arithmetic forcing $K = 0$ and $m \le f$ from $q \cdot K \le m \le f \cdot (K + 1)$ and $2f + 1 \le q$.
  - `late_tail_short`: for any chain meeting recency $R \le tip.slot + n$, tail from any late index $\ell \ge 1$ has length $c.length - \ell \le f$ and $tip.slot + 1 < L.slot + n$.
  - Proved by density ($q \cdot K \le m$ from $K$ consecutive matured windows) vs budget ($m \le f \cdot (K+1)$ from bad slot count via injection of late blocks into $Ico (L.slot + n) (R + 1)$).
- [x] **Step 4: Main argument** (Pass 7e)
  - `same_block_same_parent_timed`: identical available blocks on valid chains share parents.
  - `same_block_same_prefix_timed`: identical available blocks force agreement down to genesis.
  - `same_block_same_height`: identical blocks on valid chains have equal heights.
  - `exists_lastCommonHeight_timed`: two chains disagreeing at height $k$ have a last common height $h < k$.
  - `disjoint_blocks_of_lastCommonHeight`: post-divergence blocks on the two chains are strictly distinct.
  - `bad_of_same_slot_on_time`: two on-time post-divergence blocks cannot share an honest slot.
  - `exists_ontime_slots_in_window`: in the post-divergence window $[D.slot + 1, D.slot + 1 + n)$, on-time blocks provide $\min(n + 1 - f, q)$ distinct slot witnesses.
  - `timed_tip_ancestor_agreement`: light-client safety theorem in the timed model, proved by pigeonhole on the divergence window $[D.slot + 1, D.slot + 1 + n)$.
