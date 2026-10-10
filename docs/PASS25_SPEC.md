# Pass 25: second-pass review items N6, N8, N9

## Why

- **N6.** No liveness statement covers the validators modes 2 and 3 actually run. `production_liveness` and `liveness_produce_blockK` check only the unsigned chain rules.
- **N8.** The timed mode-3 route has only an equal-heights theorem. `LockstepPackageTimed.toGen` already exists in `MoltPetit/Model/KeyStealingLockstepTimed.lean`, but it is not stated in `Spec/`, so the paper cannot cite it. With it pinned, every per-generation theorem applies to the timed package.
- **N9.** `LockstepPackage.toGen` asks for `∀ j, ∃ W, rosterGen W = j`, which is too strong. Window 0 already bounds every generation `j ≥ rosterGen 0`.

## Pinned goals (reviewer-written, DO NOT EDIT)

There are four new statements, appended to `Spec/Statements.lean` in the scaffold commit and typechecked there:

| statement | proof |
|---|---|
| `thm_sched_liveness_produce_block` | new |
| `thm_lockstep_liveness_produce_block` | new |
| `LockstepPackageTimed.thm_toGen` | existing `LockstepPackageTimed.toGen` |
| `LockstepPackage.thm_toGen_of_low` | new |

At the end, `git diff <scaffold> -- Spec/` must be empty.

## Proof plans

- **`sched_liveness_produce_block`.**
  1. `validSignedChainSched` unfolds to `sigsOk ∧ validChainK ∧ schedPinned`.
  2. `liveness_produce_blockK` (with `hFloor`) gives `produceBlock? = some _` and `validChainK'` of the extension, hence `validChainK`.
  3. `sigsOk` of the append is `sigsOk sc ∧ sigOk new`. The new block's producer is `me` (`hMine`), so `sigOk` is `hSig`.
  4. `schedPinned` of the append is `schedPinned c ∧ schedule slot ≤ keyIndex`.
- **`lockstep_liveness_produce_block`.**
  1. Same as above, with `lockstepOk` in place of `schedPinned`.
  2. `keyFloor n c me ≤ keyIndex` follows from `hGen` (the floor is a max of chain key indices, starting at 0).
  3. Prove `lockstepOk n (c ++ [b]) = lockstepOk n c && c.all (fun b' => b'.slot / n = b.slot / n → b'.keyIndex = b.keyIndex ∧ b'.keyIndex ≤ b.keyIndex)` (or the shape the definition gives), and close it with `hGen`.
- **`LockstepPackageTimed.thm_toGen`.** This is the alias of the existing theorem.
- **`LockstepPackage.thm_toGen_of_low`.** Copy every field of the thin package except `genBound`.
  - For `j ≥ rosterGen 0`: every `i < n` with `Stolen i j` is the producer of slot `i` in window `[0, n)`. There `lagSched n rosterGen i = rosterGen 0 ≤ j`, so `i ∈ exposedProducersSched n (lagSched n rosterGen) Stolen 0`, whose card is at most `T` by `exposedBound 0`.
  - For `j < rosterGen 0`: use `hLow`.

## Steps (one per prover turn; commit after each, tick it in `docs/PASS25_PROGRESS.md`)

Build one module at a time, never a bare `lake build` or `tools/check.sh` in the foreground:

    T=$HOME/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin
    env PATH="$T:$PATH" $T/lake build <Module> > /tmp/p25-build.log 2>&1; echo rc=$?; grep -A6 "error" /tmp/p25-build.log | head -60

1. Alias only: in `Paper/Proofs.lean`, next to `LockstepPackage.toGen` (~line 96), add
   `theorem LockstepPackageTimed.toGen : LockstepPackageTimed.thm_toGen := @MoltPetit.Model.LockstepPackageTimed.toGen`
   (the development theorem is `MoltPetit/Model/KeyStealingLockstepTimed.lean:117`). If its binders differ from the pinned
   statement, add a wrapper theorem `LockstepPackageTimed.toGen'` in that file with the pinned binders and alias that. Build `Paper.Proofs`.
2. `LockstepPackage.toGen_of_low` in `MoltPetit/Model/KeyStealingLockstepGen.lean`, right after `LockstepPackage.toGen` (~257),
   with exactly the binders of `LockstepPackage.thm_toGen_of_low`. Copy every field of `LockstepPackage.toGen` except
   `genBound`, which is `fun j => ...` by cases on `j < rosterGen 0`:
   - `j < rosterGen 0`: `hLow j h`.
   - otherwise: `(Finset.range n).filter (fun i => Stolen i j) ⊆ exposedProducersSched n (lagSched n rosterGen) Stolen 0`
     (each such `i` is the image of slot `i ∈ Finset.Ico 0 n`; `producerForSlot n i = i % n = i`;
     `lagSched n rosterGen i = rosterGen (i / n - 1) = rosterGen 0 ≤ j` since `i / n = 0`), then
     `(Finset.card_le_card hsub).trans (hP.exposedBound 0)`.
   Build `MoltPetit.Model.KeyStealingLockstepGen`. Then alias it in `Paper/Proofs.lean` and build `Paper.Proofs`.
3. `sched_liveness_produce_block` in `MoltPetit/Model/KeyRotationLiveness.lean` after `liveness_produce_blockK` (~130)
   (if that module cannot see `validSignedChainSched`, put it in a new module `MoltPetit/Model/SignedLiveness.lean`
   that imports what it needs, and import that from `Molt.lean`). Binders exactly those of `thm_sched_liveness_produce_block`.
   Proof per the plan above: unfold `validSignedChainSched`, `sigsOk`, `schedPinned` with `Bool.and_eq_true`, `List.all_append`;
   `liveness_produce_blockK` with `c := stripSigs sc` gives the first conjunct and `validChainK'` of the extension, from which
   `validChainK` follows (find the lemma relating `validChainK'` and `validChainK` with one grep). `stripSigs (sc ++ [⟨b, sig⟩]) = stripSigs sc ++ [b]`.
   The new block's `sigOk` reduces to `hSig` after rewriting `producerForSlot n slot = me` (the `nextBlock` slot is `slot`).
   Build the module, alias in `Paper/Proofs.lean`, build `Paper.Proofs`.
4. `lockstep_liveness_produce_block`, same place, binders of `thm_lockstep_liveness_produce_block`. Same proof, except:
   `hFloor` is derived — `keyFloor n (stripSigs sc) me` is a `foldl max 0` over key indices of chain blocks, all `≤ keyIndex` by `hGen`;
   and the `lockstepOk` part is `lockstepOk_append_iff` (`MoltPetit/Model/KeyStealingLockstepCert.lean:64`) with `s := [b]`:
   `lockstepOk n [b] = true` by `rfl`/`simp`, and the cross condition is exactly `hGen` (the block's slot is `slot`).
   If `KeyStealingLockstepCert` is not importable there, use the new module from step 3. Build, alias, build `Paper.Proofs`.
5. Run `bash tools/check.sh > /tmp/p25-check.log 2>&1 &` in the background and poll `tail -3 /tmp/p25-check.log`
   until `check: all green`.

Aliases go in `Paper/Proofs.lean` (`theorem X : thm_X := @MoltPetit.Model.X`). If a statement looks false, STOP and report it in `docs/PASS25_PROGRESS.md`. Do not edit `paper/molt.tex`.

## Done when

- `bash tools/check.sh` prints `check: all green`.
- The pins are unchanged.
- The aliases use classical axioms only.
- `docs/PASS25_PROGRESS.md` lists what was done.
