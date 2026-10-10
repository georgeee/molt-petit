# Pass 26: a certificate the circuit can actually produce (review items N2, N5)

## Why

- **N5.** The certified theorems of modes 2 and 3 take `GroundedCertSched` / `GroundedCertLock` as a hypothesis: a claim built by folding one block at a time, each fold checking the schedule pin (mode 2) or no-mixing against a threaded generation (mode 3). The prototype's certificate cannot discharge it. Its circuit runs `valid_chain_be` over the whole chain, and `BlockG` has no key version.
- **N2.** Mode 1's certificate route takes its key floor from the caller. `GroundedCertK` threads the floor per fold, but nothing produces it.

## What changes

1. **`rust/src/lib.rs`** (scaffold, reviewer-written, appended after `valid_chain_be`, so earlier extraction locations are unchanged):
   - `BackendK: Backend`, which adds `div`, `rem`, `select` and `monus`;
   - the claim state `CertStateG`, with the tail as a fixed buffer `TailG` of `(flag, slot)` entries;
   - the per-producer floors `FloorsG`;
   - one fold step per mode: `cert_step_core_be`, `cert_step_k_be`, `cert_step_sched_be`, `cert_step_lock_be`;
   - the state updates `cert_next_tail_be`, `cert_next_floors_be`, and the genesis check `cert_genesis_ok_be`.

   `Backend`, `valid_chain_be` and `Rust/Equiv.lean` are untouched. The plonky2 instance (Stage B, `rust-keyrot/`) is the step of a recursive certificate. `Signed b` is not in the step: the circuit checks it with its signature gadget, as now.
2. **Native differential test** (reviewer, `work/p26/foldtest`): on 200,000 random chains (n ≤ 6, era ≤ 5), folding each step from the genesis state accepts exactly what the full validators accept:
   - `valid_chain` (core);
   - `valid_chain_k` (mode 1);
   - `valid_chain` + `slot / era ≤ ki` (mode 2);
   - `valid_chain` + `lockstepOk` (mode 3).

   A mutant that drops the anchor windows is caught.
3. **`Spec/`** (reviewer-written):
   - `GroundedCertK` moves from `MoltPetit/Model/KeyStealingCert.lean` to `Spec/Model.lean`, unchanged.
   - New bridge definitions in `Spec/RustBridge.lean`: `initTail`, `initFloors`, `floorsFun`, `genesisState`, `modelClaimOf`, `FoldK`, `FoldSched`, `FoldLock`.
   - Three statements in `Spec/Statements.lean`: `thm_cert_fold_k_sound`, `thm_cert_fold_sched_sound`, `thm_cert_fold_lock_sound`. Each says that if the fold accepts the genesis `G` and then `bs`, and every block is `Signed`, then `modelClaimOf` of that history is `GroundedCertK` / `GroundedCertSched` / `GroundedCertLock`. That is the hypothesis the certified theorems take, now discharged by the code the circuit runs.

## Proof plan (Stage A, Archon)

The buffer relation, which is the only real idea:

    TailRepr n st cl :=
      st.tail has length n - 1, its present entries form a suffix of the buffer,
      their slots are strictly increasing and the last one is cl.tipSlot (when n ≥ 2),
      and (present slots of st.tail).filter (cl.tipSlot + 2 - n ≤ ·) = cl.tail.map slot

Lemmas:

1. **`tail_count_be` / window count.** For `u` with `cl.tipSlot + 2 ≤ u + n`, `tail_count_be st.tail u n` plus the new block's indicator equals `windowCount (cl.tail ++ [b]) u n`. Present slots below `cl.tipSlot + 2 - n` are below `u`, so they never count.
2. **Anchors suffice.** If every window `u ∈ {monus (tipSlot+2) n} ∪ {s+1 | s a buffer slot}` passes `fold_window_ok_be`, then every `u` with `tipSlot + 2 ≤ u + n ≤ b.slot + 1` has `quorum n ≤ windowCount (cl.tail ++ [b]) u n`.
   - Take `u` in range and let `u'` be the largest anchor `≤ u`.
   - No slot of `cl.tail ++ [b]` lies in `[u', u)`, since the next slot after `u'-1` would be an anchor.
   - So `windowCount u ≥ windowCount u'`: the window `[u, u+n)` loses nothing and can only gain slots up to `u+n`.
   - This is the argument of the existing `matured_dense` anchor proofs in `Rust/Bridge.lean`; reuse their lemmas.
3. **Core step sound.** `cert_step_core_be ... = ok true` and `TailRepr` give the `extend` premises: height, slot, prev (via `hashToNat`, as in `child_ok_be_sound`), and density.
4. **Tail preserved.** `cert_next_tail_be` gives `TailRepr` for the next claim. When the dropped head is present, every entry is present, so the head slot is `≤ tipSlot - (n-2) < b.slot + 2 - n`.
5. **Mode extras.**
   - K: `floors_ok_be` is `fl (b.slot % n) ≤ ki`, and `floors_bump_be` is the `max` update, under `floorsFun`.
   - Sched: `div` is `/`.
   - Lock: two `div`s and an `eq`.
6. **Fold theorems.** Induct on `bs` with the claim `modelClaimOf n G (prefix)`. `modelClaimOf`'s tail is the filter of the whole prefix, which is what the derivation's iterated filters give, because bounds rise with the slots.

## Stages B and C (after A)

- **B, circuit.**
  - `MpCircuit` implements `BackendK`: witnessed `div`/`rem` with a range check, and `select`.
  - `rust-keyrot/` gets a cyclic-recursive fold circuit. Each step verifies the previous step's proof, runs `cert_step_*_be` on one block, verifies that block's signature subproof, and exposes `CertStateG` (+ floors / g) as public inputs.
  - Add a benchmark row for one fold step.
- **C, client.**
  - The Rust/TS `CertClaim` gains the floors (mode 1) and generation (mode 3) the certificate now exposes.
  - `validate_certified_chain_k` reads the floors from the claim instead of taking them from the caller.
  - Bridge theorems, then the paper: the N2/N5 disclosures become results.
