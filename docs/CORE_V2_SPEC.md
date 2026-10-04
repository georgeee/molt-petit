# Core v2: light-client safety under arbitrary-time key exposure

Reviewer-owned spec. Two statements are pinned in `MoltPetit/Model/ExposureSafety.lean`
and guarded by `Molt/AxiomsExposureSafety.lean`:

- `MoltPetit.Model.exposure_agreement` (Theorem 1)
- `MoltPetit.Model.exposure_no_early_signing` (forged chains cannot run ahead of real time)

Do not edit either statement, the guard, or the definitions `Exposure`,
`SigningExecution`, `HonestClock` and `ExposureBounded` in `MoltPetit/Model/Definitions.lean`.

## Why a new core

The old `TimedExecution` model (Definitions §7) assumed two things that are false in deployment:

- `key_match`: a corrupted key signs only at its own seat's real slots.
- `honest_stamp`: honest producers have zero clock skew.

A stolen key signs whenever its holder likes. In the new model:

- `exposed s r` is an arbitrary predicate on the key that verifies stamp `s`, at real slot `r`.
- The budget counts every stamp whose key was exposed at *any* time before
  `v + n + ρ`. Keys, once stolen, stay stolen. Thefts after that time do not count
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

## Step B: `exposure_no_early_signing`

Let `s = B.slot ≥ n - 1`, and suppose `s > r + e`. Write `d = s - r`, so `d ≥ e + 1`.

The window `W = [v, v + n)` with `v = s + 1 - n` is matured at `B`
(`MaturedWindowsDense`, `D = B`, `u = v`), so at least `q` chain blocks have stamps in `W`.
They are `B` or ancestors of `B` (StrictSlots plus index order). By Step A each `A` other
than `G` is in `log r_A` with `r_A ≤ r`. Classify them:

- **Genesis:** at most 1 block.
- **Exposed type:** `A ≠ G` and `exposed A.slot r_A`. Then `r_A ≤ r < s < v + n + ρ`, so
  `A.slot` is in the filter set of `ExposureBounded` at `v`. Stamps are distinct, so there
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

## Step D: `exposure_agreement`

Let `m = min tip.slot tip'.slot`, and let `c₀` be the chain whose tip has slot `m`. Then
`R ≤ m + ρ` (its `hRecent`).

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
   4. Both times are `≤ R ≤ m + ρ < v + n + ρ`, so every `s ∈ S ∩ S'` is in the filter set
      of `ExposureBounded` at `v`. That gives at least `f + 1` stamps, a contradiction.
5. So some block `X` with stamp in `W*` is in both chains, at the same index `j` (Step C).
6. In `c₀`, the blocks after `X` have strictly increasing slots in `(X.slot, m]`, and
   `X.slot ≥ v`. So at most `n - 1` blocks follow `X`, and `j ≥ c₀.length - n > h`
   (`hDeep`/`hDeep'`).
7. Step C at `k = h` finishes the proof.

## Gate

`bash tools/check.sh` must print `check: all green`. The old modules still build alongside
the new one at this stage. Write `STATUS: READY FOR REVIEW` in `docs/PUBLISH_PREP_STATUS.md`
(Pass 19 section) only when the gate is green and both `#print axioms` guards pass.
