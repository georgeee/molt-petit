# Timed light-client safety: spec and proof plan

Owner of this spec: the reviewer (top-level driver). Archon proves; it does not
change the statement.

## Why

Paper Theorem 1 (`Molt.light_client_safety`) assumes `SigUnforgeableRecent`. In
the timed model that follows only from `NoBackdate` (`sigUnforgeableRecent_of_timed`),
and `NoBackdate` is not implied by the model (`noBackdate_independent`). It rules
out the very future-stamp harvesting the paper's adversary performs. So the
paper's claim that recency is load-bearing for safety is not machine-checked
today. George's decision (2026-10-03): prove the timed theorem first.

## The statement (FIXED)

`MoltPetit.Model.timed_tip_ancestor_agreement` in
`MoltPetit/Model/TimedSafety.lean`. Its exact type is pinned by
`Molt/AxiomsTimedSafety.lean`. That file is reviewer-owned and must not be
edited. If you believe the statement is false, do not weaken it. Write the
concrete counterexample or the failing step into
`docs/TIMED_SAFETY_PROGRESS.md` under a heading `## PROOF GAP` and stop.

Hypotheses, in words:

- `TimedExecution n bad log G`: EUF-CMA, honest stamping and signing once, id-formation, collision resistance.
- `ByzantineBounded n bad`: at most `f` bad real slots in every `n`-window.
- Two valid chains, both from genesis `G`, both available by real slot `R`.
- Both pass recency at `R` (`R ≤ tip.slot + n`).
- `c` is no longer than `c'`, and `n < c.length`.

Conclusion: the two chains agree at index `c.length - 1 - n`.

## Notation

- `q = quorum n`, `f = maxByzantine n`.
- `σ(B)` is the first real slot at which `B` is in the log: `FirstSigned log B r := B ∈ log r ∧ ∀ r' < r, B ∉ log r'`. Use `Nat.find`.
- A block at index ≥ 1 is **on time** if `σ(B) = B.slot` and **late** if `σ(B) > B.slot`.

## Reusable lemmas already in the repo

- `MoltPetit/Model/Timed.lean`:
  - `block_signed`: index ≥ 1 ⇒ `B ≠ G` and signed by `R`.
  - `one_real_slot_one_block`: distinct indices ≥ 1 have distinct first-signing slots. Needs `2 ≤ n`, which holds whenever a bad slot exists (see step 0).
  - `belowCount`, `belowCount_split`, `belowCount_windows`, `belowCount_prefix`.
  - `bad_budget_Ico`.
  - `sigTime_mono_step` and `sigTime_mono_chain`. Adapt these or reuse their method.
- `MoltPetit/Model/Model.lean`: `strictSlots_lt`, `chainSlotsIn`, `mem_chainSlotsIn`, `chainSlotsIn_card`, `exists_blockAt_of_mem`, `exists_blockAt_of_le`.
- `MoltPetit/Model/Safety.lean`: `parentLinked_at_succ`, `same_block_same_parent`, `same_block_same_prefix`.
- `MoltPetit/Model/Liveness.lean`: `windowCount_mono`.
- `MoltPetit/Model/Soundness.lean`: `blockAt_getLast`.

Search with `grep -rn` before writing a helper; most bookkeeping exists already.

## Proof plan

### Step 0. Arithmetic and basics

- `q ≥ 2f+1`, `3f < n` (for `n ≥ 1`), and `n + f < 2q`.
- If any slot `r` is bad, then `f ≥ 1` (`ByzantineBounded` at `u = r`). Hence `n ≥ 4` and `q ≥ 3`.
- Same residue (`key_match`) and `a < b` imply `a + n ≤ b`.
- First signing at a slot other than the stamp ⇒ that real slot is bad (`honest_stamp`).
- σ is monotone along a chain at indices ≥ 1. Let `P` be the parent of `B`. Use `chain_order` at `σ(B)`: some `P'` with `P'.id = B.prev` is available at `σ(B)`. By `id_inj`, `P' = P`. So `P = G` or `σ(P) ≤ σ(B)`.

### Step 1. No pre-signing

For every index ≥ 1: `B.slot ≤ σ(B)`. Prove by induction on the index.

Suppose `r = σ(B) < B.slot`. Then `r` is bad, so `r + n ≤ B.slot` and `q ≥ 3`. Let `P` be the parent.

- If `P` is not `G`: by IH and monotonicity, `P.slot ≤ σ(P) ≤ r ≤ B.slot - n`.
- Every ancestor older than `P` has slot `< P.slot`.

So the matured window `[B.slot - n, B.slot)` contains at most `P`, which gives `windowCount ≤ 1 < q`. That contradicts `MaturedWindowsDense` at `B`. If `P = G`, the window can only contain `G`.

### Step 2. Late is forever

If `P` (index ≥ 1) is late and `N` is its child, then `N` is late.

Suppose instead that `N` is on time (by Step 1, not late means on time). Then:

- `N.slot = σ(N) ≥ σ(P) ≥ P.slot + n`.
- The window `[P.slot + 1, P.slot + n]` is matured at `N` and contains at most `N`.
- `q ≥ 3` because `σ(P)` is bad.

That is a contradiction. By induction, every block after a late block is late.

### Step 3. Late tail is short on a recent chain

Take a chain with tip `T` and `R ≤ T.slot + n`. Let `ℓ` be the first late index, with block `L`, and let `m = len - ℓ`. Then `m ≤ f` and `T.slot + 1 < L.slot + n`.

Let `K = (T.slot + 1 - L.slot) / n`.

1. **Density.** The `K` consecutive windows starting at `L.slot` are matured at `T` and only contain blocks at index ≥ ℓ. So `q·K ≤ m` (`belowCount_windows`).
2. **Budget.** By Step 2, all `m` tail blocks are late. Their first-signing slots are pairwise distinct (`one_real_slot_one_block`) and bad. Each lies in `Ico (L.slot + n) (R + 1)`, which is contained in `Ico (L.slot + n) (L.slot + n + (K+1)·n)`. So `m ≤ f·(K+1)` (`bad_budget_Ico`).
3. **Conclusion.** With `q ≥ 2f+1` this forces `K = 0`. Hence `m ≤ f` and `T.slot + 1 < L.slot + n`.

### Step 4. Main argument

1. **Prefix.** If `c[j] = c'[j]` then the chains agree at every `i ≤ j`. If `c[i] = c'[j]` then `i = j` by `SequentialHeights`.
2. **Divergence.** Let `e` be the first index `< len` with `c[e] ≠ c'[e]`. If there is none, the claim follows. Otherwise `e ≥ 1`; let `D = c[e-1] = c'[e-1]`. Suppose, for contradiction, `len - e ≥ n + 1`.
3. **Disjoint blocks.** Past-divergence blocks (index ≥ e) of the two chains are pairwise distinct (Step 4.1).
4. **The window.** Let `W1 = [D.slot + 1, D.slot + n]`, the window `u = D.slot + 1` of length `n`. It is matured on both chains because `c[e+n]` and `c'[e+n]` exist. Let `S_X` be the blocks of chain `X` in `W1`. All are past divergence, and `|S_X| ≥ q`.
5. **Honest slots.** Two on-time past-divergence blocks, one from each chain, cannot share an honest slot (`honest_once`). Let `b` be the number of bad slots in `W1`; `b ≤ f`.
6. **If chain `X` has a late block in `W1`.** Let `ℓ` be X's first late index overall.
   - If `ℓ < e`, then all `≥ n+1` past-divergence blocks are late, contradicting Step 3 (`m ≤ f < n+1`). So `ℓ ≥ e`.
   - The on-time past-divergence blocks of `X` are those at indices `e .. ℓ-1`. There are `≥ n+1-f` of them, and all lie in `W1`.
   - The set `H_X` of those at honest slots has size `≥ n+1-f-b`.
7. **Cases.** Each case contradicts the setup, so `len - e ≤ n`:
   - **Both chains late in `W1`.** `H_c` and `H_c'` are disjoint subsets of the `n-b` honest slots. So `n + 2 ≤ 2f + b ≤ 3f < n`.
   - **Exactly one chain (say `c`) late in `W1`.** Every block of `c'` in `W1` is on time and avoids the slots in `H_c`. So `|S_c'| ≤ n - |H_c| ≤ f + b - 1 ≤ 2f - 1 < q`. The other case is symmetric.
   - **Neither chain late in `W1`.** Honest-slot blocks are disjoint, so `|S_c| + |S_c'| ≤ n + b ≤ n + f < 2q`.

## Conventions

- Put helper lemmas in `MoltPetit/Model/TimedSafety.lean`. Split into `MoltPetit/Model/TimedSafety*.lean` if it grows past about 600 lines; the main file then imports the parts.
- Do not edit any other existing Lean file.
- No `sorry`, `admit` or `axiom`.
- `lake build` must pass. The guard in `Molt/AxiomsTimedSafety.lean` must report only `[propext, Classical.choice, Quot.sound]`.
- Keep progress notes in `docs/TIMED_SAFETY_PROGRESS.md`: which steps are done, which lemma is in flight, and what failed. A fresh session must be able to resume from it.
- Commit on `publish-prep` after each lemma that compiles.
