# Core v2: light-client safety under arbitrary-time key exposure

Reviewer-owned spec. The pinned statement is
`MoltPetit.Model.exposure_agreement` in `MoltPetit/Model/ExposureSafety.lean`,
with its type guarded by `Molt/AxiomsExposureSafety.lean`. Do not edit the statement,
the guard, or the new definitions `Exposure`, `SigningExecution` and `ExposureBounded`
in `MoltPetit/Model/Definitions.lean`.

## Why a new core

The old `TimedExecution` model (Definitions §7) assumed two things that are false in deployment:

- `key_match`: a corrupted key signs only at its own seat's real slots.
- `honest_stamp`: honest producers have zero clock skew.

A stolen key signs whenever its holder likes. The new model has neither assumption:

- `exposed i r` is an arbitrary predicate saying the key of seat `i` is usable by
  someone else at real slot `r`.
- An honest holder's signature only satisfies `B.slot ≤ r + σ`, which allows a
  clock that runs up to `σ` slots ahead.
- The budget is per seat over sliding windows of `Λ` real slots.

The new proof is written from scratch. **Do not reuse or import** `Timed.lean`,
`TimedSafety.lean` or `TimedSafetyCert.lean`, or any lemma about
`TimedExecution`/`ByzantineSlots`. Those modules are going to be deleted. Generic
list/chain lemmas from other modules may be reused if they do not mention the old
timed model, but self-contained new lemmas are preferred.

Put helper lemmas in `MoltPetit/Model/ExposureSafety.lean`, above the theorem, or in a
new file `MoltPetit/Model/ExposureCore.lean` that it imports.

## Notation

| Symbol | Meaning |
|---|---|
| `f` | `maxByzantine n` |
| `q` | `quorum n` |
| `seat s` | `producerForSlot n s = s % n` |
| `e` | `n + f + σ + 1 - q`, the early-signing bound. `q ≤ n` for `n ≥ 1`, so `e ≥ f + σ + 1 ≥ σ + 1`. |

From `hΛ`, `Λ ≥ 2n + ρ` and `Λ ≥ n + e + ρ`. The second holds because
`n + e = 2n + f + σ + 1 - q ≤ 2n + (f + σ + 1 - q)`.

The arithmetic fact `2q - n ≥ f + 1` holds for every `n ≥ 1`. Check it by residue of `n`
mod 3, with `n = 3k`, `3k+1`, `3k+2`.

## Step A — ancestors are available at the signing time

Let `c` be a `ValidChain` with `blockAt? c 0 = some G` and `∀ B ∈ c, AvailableAt log G B R`.
If `B` is at index `j`, `B ∈ log r`, and `k ≤ j`, then the block at index `k` satisfies
`AvailableAt log G _ r`.

Proof:
1. `chain_order` at `r` gives `P'` with `P'.id = B.prev` and `P'` available at `r`.
2. The chain parent `P` has `B.prev = some P.id` (ParentLinked).
3. Both `P'` and `P` are `SignedEver`: available implies SignedEver, and `hAvail` gives it for `P`.
4. `id_inj` then gives `P' = P`, so `P` is available at `r`.
5. Iterate. An available non-genesis block has some `r₁ ≤ r` with `P ∈ log r₁`, so apply
   `chain_order` at `r₁`, and so on down. Induct on `j - k`.

## Step B (Lemma E) — no chain block is signed more than `e` slots early

Let `c` be as in Step A. For every block `B ∈ c` with `B ≠ G` and `n - 1 ≤ B.slot`, and
every `r` with `B ∈ log r`, we have `B.slot ≤ r + e`.

This holds for **every** signing time `r`, not only the first one. The proof is by strong
induction on `B.slot`.

Assume `d := B.slot - r > e` and derive a contradiction. Let `s = B.slot` and take the
window `W = [s + 1 - n, s]`, of length `n`. It is matured at `B` (`MaturedWindowsDense`
with `D = B`, `u = s + 1 - n`), so at least `q` chain blocks have stamps in `W`. All of
them are `B` or ancestors of `B`, by StrictSlots and index order. By Step A, each one other
than `G` is in `log r_A` for some `r_A ≤ r`. Classify the blocks of `W`:

- **Genesis:** at most 1.
- **Honest type:** `A ≠ G` and `seat A.slot` is not exposed at `r_A`. By `honest_early`,
  `A.slot ≤ r_A + σ ≤ r + σ`. These stamps are distinct and lie in `[s + 1 - n, r + σ]`, so
  there are at most `n + σ - d` of them (0 if that is negative).
- **Exposed type:** `A ≠ G` and `seat A.slot` is exposed at `r_A`. Stamps in `W` are
  distinct mod `n`, so the seats are distinct. Every `r_A` lies in one interval of length
  at most `2n`:
  - If `A.slot ≥ n - 1`, the induction hypothesis gives `r_A ≥ A.slot - e ≥ s + 1 - n - e`,
    and `r_A ≤ r = s - d < s - e`. The interval `[s + 1 - n - e, r]` has length less than `n`.
  - If some `A.slot < n - 1`, then `s < 2n - 2` and every `r_A ∈ [0, r]` with `r < s`.
    That interval has length at most `2n - 2`.

  Take `u` to be `s + 1 - n - e` (truncated) or `0`. Then `[u, u + Λ)` contains every `r_A`,
  so `ExposureBounded` gives at most `f` exposed-type blocks.

So `q ≤ (n + σ - d) + f + 1`. With `d ≥ e + 1`, this gives `q ≤ n + σ + f - e < q`, a
contradiction.

Edge cases:
- When `n + σ - d ≤ 0`, the honest count is 0. If `n ≥ 2`, then `q ≥ f + 2`, which is a
  contradiction. If `n = 1`, `W = {s}` contains only `B` (since `G ≠ B` and stamps are
  distinct), `B` is exposed type, and the count is `1 > f = 0`, also a contradiction.
- `B` itself falls in one of the classes: it is honest type only if `d ≤ σ < e`.

## Step C — common prefix from a common block

Let `X` be at index `j` in both `c` and `c'` (SequentialHeights gives
`X.height = j = j'`). Then `blockAt? c k = blockAt? c' k` for all `k ≤ j`. Prove this by
downward induction using ParentLinked, `id_inj` and SignedEver from `hAvail`/`hAvail'`.

## Step D — the main count

Let `m = min tip.slot tip'.slot`, and let `c₀` be the chain whose tip has slot `m`.

1. Since `c₀.length ≥ n + 1` and slots strictly increase, `m ≥ n`.
2. `W* = [m + 1 - n, m]` is matured in both chains. Use `D` = the tip, with
   `u + n = m + 1 ≤ tip.slot + 1`.
3. Let `S` and `S'` be the stamp sets of `c` and `c'` in `W*`. Each has at least `q`
   elements, so `|S ∩ S'| ≥ 2q - n ≥ f + 1`.
4. Suppose that for every `s ∈ S ∩ S'` the blocks `X_s ∈ c` and `X'_s ∈ c'` differ.
   1. Neither is `G`. If `X_s = G`, it sits at index 0 of `c'`, and StrictSlots on `c'`
      forces `X'_s = G`.
   2. Pick `r ≤ R` with `X_s ∈ log r` and `r' ≤ R` with `X'_s ∈ log r'` (`hAvail`).
   3. By `honest_once`, `seat s` is exposed at `r` or at `r'`.
5. Both of these times lie in one window:
   - Lower bound: if `s ≥ n - 1`, Step B gives `r, r' ≥ s - e ≥ m + 1 - n - e`. If
     `s < n - 1`, then `m < 2n - 2` and the bound is `r, r' ≥ 0`.
   - Upper bound: `r, r' ≤ R ≤ m + ρ`.
   - Window: take `u = m + 1 - n - e` (truncated) or `0`. Then `[u, u + Λ)` contains the
     interval, using `Λ ≥ n + e + ρ` and `Λ ≥ 2n + ρ`.
6. The seats `s % n` are distinct across `S ∩ S'`. That gives at least `f + 1` exposed seats
   in one `Λ`-window, contradicting `ExposureBounded`.
7. So some `X ∈ W*` is in both chains, at the same index `j` (Step C setup).
8. In `c₀`, the blocks after `X` have strictly increasing slots in `(X.slot, m]` and
   `X.slot ≥ m + 1 - n`. So at most `n - 1` blocks follow `X`, and `j ≥ c₀.length - n > h`
   by `hDeep`/`hDeep'`.
9. Step C at `k = h` finishes the proof.

## Gate

`bash tools/check.sh` must print `check: all green`. The old modules still build alongside
the new one at this stage; they are removed in a later pass. Write
`STATUS: READY FOR REVIEW` in `docs/PUBLISH_PREP_STATUS.md` (Pass 19 section) only when the
gate is green and `#print axioms` shows only `[propext, Classical.choice, Quot.sound]`.
