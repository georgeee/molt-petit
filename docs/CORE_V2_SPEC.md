# Core v2: light-client safety under arbitrary-time key exposure

Reviewer-owned spec. Four statements are pinned in `MoltPetit/Model/ExposureSafety.lean`
and guarded by `Molt/AxiomsExposureSafety.lean`:

- `MoltPetit.Model.exposure_agreement` (Theorem 1)
- `MoltPetit.Model.exposure_no_early_signing` (forged chains cannot run ahead of real time)

Do not edit either statement, the guard, or the definitions `Exposure`,
`SigningExecution`, `HonestClock`, `ExposureBounded` and `ExposureBoundedEver` in `MoltPetit/Model/Definitions.lean`.

## Why a new core

The old `TimedExecution` model (Definitions §7) assumed two things that are false in deployment:

- `key_match`: a corrupted key signs only at its own seat's real slots.
- `honest_stamp`: honest producers have zero clock skew.

A stolen key signs whenever its holder likes. In the new model:

- `exposed s r` is an arbitrary predicate on the key that verifies stamp `s`, at real slot `r`.
- The budget counts every stamp whose key was exposed at *any* time before
  `v + n + φ`. Keys, once stolen, stay stolen. Thefts after that time do not count
  (the long-range-attack boundary).
- Honest clock skew `σ` enters only the no-early-signing theorem. Safety does not depend on it.

The proof is written from scratch. **Do not import or use** `Timed.lean`,
`TimedSafety.lean`, `TimedSafetyCert.lean`, `TimedSig.lean`, or any lemma about
`TimedExecution`/`ByzantineSlots`; they are going to be deleted. Put helpers in
`ExposureSafety.lean` above the theorems, or in a new imported file
`MoltPetit/Model/ExposureCore.lean`.

The helpers already there (`availableAt_parent_of_signed`, `step_A_ancestor_available`,
`ancestor_availableAt`, and the list lemmas) were written against an earlier draft.
Keep and fix them as needed.

## Notation

| Symbol | Meaning |
|---|---|
| `f` | `maxByzantine n` |
| `q` | `quorum n` |
| `e` | `n + f + σ + 1 - q` |

The arithmetic fact `2q - n ≥ f + 1` holds for every `n ≥ 1`. Check it by residue of `n`
mod 3. Also `q ≥ f + 1`, and `q ≥ f + 2` when `n ≥ 2`.

## Step A: ancestors are available at the signing time

Let `c` be a `ValidChain` with `blockAt? c 0 = some G` and `∀ B ∈ c, AvailableAt log G B R`.
If `B` is at index `j`, `B ∈ log r`, and `k ≤ j`, then the block at index `k` satisfies
`AvailableAt log G _ r`.

1. `chain_order` gives a parent candidate `P'` available at `r`.
2. `id_inj` identifies `P'` with the chain parent. Both are SignedEver.
3. Iterate. Available means genesis, or in `log r₁` for some `r₁ ≤ r`.

This step is already largely done.

## Step B: `exposure_no_early_signing_ever` (DONE)

Let `s = B.slot ≥ n - 1`, and suppose `s > r + e`. Write `d = s - r`, so `d ≥ e + 1`.

The window `W = [v, v + n)` with `v = s + 1 - n` is matured at `B`
(`MaturedWindowsDense`, `D = B`, `u = v`), so at least `q` chain blocks have stamps in `W`.
They are `B` or ancestors of `B` (StrictSlots plus index order). By Step A each `A` other
than `G` is in `log r_A` with `r_A ≤ r`. Classify them:

- **Genesis:** at most 1 block.
- **Exposed type:** `A ≠ G` and `exposed A.slot r_A`. Then `r_A ≤ r < s < v + n + φ`, so
  `A.slot` is in the filter set of `ExposureBoundedEver` at `v`. Stamps are distinct, so there
  are at most `f` of these.
- **Honest type:** `A ≠ G` and `¬ exposed A.slot r_A`. `HonestClock` gives
  `A.slot ≤ r_A + σ ≤ r + σ`. These distinct stamps lie in `[v, r + σ]`, so there are at most
  `r + σ + 1 - v = n + σ - d` of them (0 if negative).

So `q ≤ (n + σ - d) + f + 1 ≤ n + σ + f - e` (with `d ≥ e + 1`), and
`n + σ + f - e = q - 1 < q`. If the honest bound is truncated at 0, then `q ≤ f + 1`. That is
impossible for `n ≥ 2`. For `n = 1`, `W = {s}` holds only `B`, so the genesis count is 0 and
`q = 1 ≤ f = 0` is false.

No induction is needed.

## Step C: common prefix from a common block

If `X` is at index `j` in `c` and at index `j'` in `c'`, SequentialHeights gives
`j = X.height = j'`. Then `blockAt? c k = blockAt? c' k` for every `k ≤ j`. Prove it by
downward induction using ParentLinked, `id_inj` and SignedEver from `hAvail`/`hAvail'`.

## Step D: `exposure_agreement_ever` (the one open `_ever` proof)

Let `m = min tip.slot tip'.slot`, and let `c₀` be the chain whose tip has slot `m`. Then
`R ≤ m + φ` (its `hRecent`).

1. `c₀.length ≥ n + 1` and slots strictly increase, so `m ≥ n`.
2. `W* = [v, v + n)` with `v = m + 1 - n` is matured in both chains. Use the tips as `D`;
   `v + n = m + 1 ≤ tip.slot + 1`.
3. Let `S` and `S'` be the stamp sets of `c` and `c'` in `W*`. Each has at least `q`
   elements, so `|S ∩ S'| ≥ 2q - n ≥ f + 1`.
4. Suppose that for every `s ∈ S ∩ S'` the blocks `X_s ∈ c` and `X'_s ∈ c'` differ.
   1. Neither is `G`. If `X_s = G`, it is at index 0 of `c'`, and StrictSlots on `c'`
      forces `X'_s = G`.
   2. Pick `r, r' ≤ R` with `X_s ∈ log r` and `X'_s ∈ log r'` (`hAvail`).
   3. By `honest_once`, `exposed s r` or `exposed s r'` holds.
   4. Both times are `≤ R ≤ m + φ < v + n + φ`, so every `s ∈ S ∩ S'` is in the filter set
      of `ExposureBoundedEver` at `v`. That gives at least `f + 1` stamps, a contradiction.
5. So some block `X` with stamp in `W*` is in both chains, at the same index `j` (Step C).
6. In `c₀`, the blocks after `X` have strictly increasing slots in `(X.slot, m]`, and
   `X.slot ≥ v`. So at most `n - 1` blocks follow `X`, and `j ≥ c₀.length - n > h`
   (`hDeep`/`hDeep'`).
7. Step C at `k = h` finishes the proof.

## Pass 19b: the windowed headline

Theorem 1 of the paper is now the WINDOWED form. The cumulative (`_ever`) forms stay,
and they are cited as a remark. The new pinned statements are in `ExposureSafety.lean`:

- `exposure_no_early_signing` concludes `B.slot ≤ r + ℓ`. It has no slot precondition.
- `exposure_agreement` is Step D with `ExposureBounded n ℓ φ`, plus `HonestClock σ`, `hL`
  and `hL'`.

`ExposureBounded n ℓ φ` charges stamp `s ∈ [v, v + n)` only for an exposure at a real slot
`r` with `v ≤ r + ℓ ∧ r < v + n + φ`. The hypotheses are:

- `hL : n ≤ ℓ + 1`
- `hL' : n + f + σ + 1 ≤ q + ℓ`, which is `ℓ ≥ e`

Facts used below:

- `ℓ ≥ σ + 1`, because `q ≤ n`.
- `G.slot < n` whenever some chain block `B` has `n - 1 ≤ B.slot`. Apply density to the
  window `[0, n)` matured at `B`. Some block has a slot `< n`, and `G` (index 0) has the
  least slot by StrictSlots.

### Step E: `exposure_no_early_signing` (strong induction on the chain index)

Prove the following by strong induction on `m`.

> For every `B` with `blockAt? c m = some B`, `B ≠ G`, and `B ∈ log r`: `B.slot ≤ r + ℓ`.

Fix `B` at index `m`, and write `s = B.slot`. Suppose `s > r + ℓ`. Then `s ≥ ℓ + 1 ≥ n`.

1. **`B` is not honest at `r`.** Otherwise `s ≤ r + σ ≤ r + ℓ`. So `exposed s r`.
2. Let `W = [v, v + n)` with `v = s + 1 - n ≥ 1`. It is matured at `B`, so it holds at
   least `q` chain blocks. Each is `B`, an ancestor of `B`, or possibly `G`.
3. **Ancestors.** Each ancestor `A ≠ G` in `W` is in `log r_A` with `r_A ≤ r` (Step A).
   - If `A` is unexposed at `r_A`, then `A.slot ≤ r + σ`.
   - If `A` is exposed at `r_A`, the induction hypothesis (smaller index) gives
     `v ≤ A.slot ≤ r_A + ℓ`. Also `r_A ≤ r < s < v + n + φ`. So `A.slot` is in the
     `ExposureBounded` filter at `v`.
4. **Case (i): `v ≤ r + ℓ`.** `B` is in the filter too. The chain stamps in `W` are then
   covered by three sets:
   - the filter, with at most `f` stamps;
   - `{s' ≤ r + σ}`, with at most `r + σ + 1 - v` stamps;
   - possibly `G.slot`.

   This gives `q ≤ 1 + f + (r + σ + 1 - v)` (truncated subtraction).
   - If the honest term is positive, it is at most `n + σ - ℓ - 1`, so
     `q ≤ n + f + σ - ℓ < q` by `hL'`.
   - If it is 0, then `q ≤ 1 + f`. That contradicts `q ≥ f + 2` for `n ≥ 2`.
   - For `n = 1`, `W = {s}` holds `B` only. `G ∉ W`, as in the existing proof
     (`genesis_slot_not_mem_chainSlotsIn_of_ne`). So `q ≤ f = 0`, a contradiction.
5. **Case (ii): `v > r + ℓ`.**
   - **`n ≥ 2`.** Here `s ≥ r + ℓ + n ≥ 2n - 1`, so `v ≥ n > G.slot` and `G ∉ W`. The
     honest set `{s' ≤ r + σ}` misses `W`, because `r + σ < r + ℓ < v`. So the stamps in
     `W` are `s` plus filter stamps from ancestors, giving `q ≤ 1 + f`. That contradicts
     `q ≥ f + 2`.
   - **`n = 1`.** Then `f = 0` and `q = 1`. The window `[s - 1, s - 1]` is matured at `B`,
     so some chain block `A` has slot `s - 1`. It has a smaller index.
     - If `A = G`, then `G.slot = 0` (from the `G.slot < n` fact), so `s = 1 ≤ ℓ`, a
       contradiction.
     - Otherwise `A ∈ log r_A` with `r_A ≤ r` (Step A). If `A` is unexposed at `r_A`, then
       `s - 1 ≤ r + σ`, so `s ≤ r + ℓ`, a contradiction. If `A` is exposed at `r_A`, the
       induction hypothesis gives `s - 1 ≤ r_A + ℓ`, and `r_A ≤ r < s < s + φ`. So `s - 1`
       is in the filter at `v' = s - 1`, which contradicts `f = 0`.

It may be easier to state Step E for a block at index `m` and recover the `B ∈ c` form
through `exists_blockAt_of_mem`. Reuse `chainSlotsIn_subset_classification`'s pattern, but
note that it was written for `ExposureBoundedEver`'s filter. Write a windowed variant whose
exposed set is the `ExposureBounded` filter.

### Step D′: `exposure_agreement`

Follow Step D verbatim. The only change is at 4.4: an `s ∈ S ∩ S'` whose block `X` (on
either chain, `X ≠ G`) is exposed at its signing time `r ≤ R` needs `v ≤ r + ℓ`. Step E
gives `v ≤ s = X.slot ≤ r + ℓ`, and `r ≤ R ≤ m + φ < v + n + φ` as before. Factor Step D
through a lemma that takes, for each conflicting stamp, membership in a general filter. Then
both `exposure_agreement_ever` and `exposure_agreement` follow from it.

## Gate

`bash tools/check.sh` must print `check: all green`. The old modules still build alongside
the new one at this stage. Write `STATUS: READY FOR REVIEW` in `docs/PUBLISH_PREP_STATUS.md`
(Pass 19 section; all four pinned theorems sorry-free) only when the gate is green and both `#print axioms` guards pass.
