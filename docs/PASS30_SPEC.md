# Pass 30: remove disclosed carve-outs (signed liveness, derived density, per-mode producer, two check times)

Statements approved by the reviewer (work/review-moltpetit review-10). Scaffold: commit "pass30 scaffold".

## S1. Signed liveness, exported
`validSignedChain`, `produceSignedBlock?` and `SigCorrect` moved verbatim from
`MoltPetit/Model/Definitions.lean` to `Spec/Model.lean` (same namespace `MoltPetit.Model`).
- `thm_liveness_produce_signed_block` is exactly `MoltPetit.Model.liveness_produce_signed_block`
  (`MoltPetit/Results/Results.lean:99`).
- `thm_liveness_produce_signed_blockK` is exactly `MoltPetit.Model.liveness_produce_signed_blockK`
  (`MoltPetit/Model/KeyRotationLiveness.lean:161`).
Proof: add both to `Paper/Proofs.lean` as `@MoltPetit.Model.<name>`.

## S2. `thm_rust_produce_block_deployed_live_budget` (Rust/Deployed.lean)
Same hypotheses as `thm_rust_produce_block_deployed_live`, with `hDense` replaced by
`hBudget : ByzantineBounded n.val bad` and `hCover` (slot form). Prove `hDense`, then apply
`rust_produce_block_deployed_live`.
- Let `c := (toModelClaim cl).tail ++ toModelChain tl ++ [dummy at at_slot]` (the exact list in hDense).
- For a window `u` in range: every `s ∈ Finset.Ico u (u+n) \ badSlotsIn bad u n` is in
  `((c.filter (blockInWindow u n)).map Block.slot).toFinset` (from hCover; the dummy covers `s = at_slot`).
- `List.toFinset_card_le`: that finset's card ≤ the mapped list's length = `windowCount c u n`.
- `(Ico \ bad).card ≥ n - maxByzantine n ≥ quorum n` by `hBudget u` and `quorum_plus_byzantine_le`
  (see `window_dense_of_honest_cover_at`, MoltPetit/Model/Liveness.lean, for the same counting).
No `StrictSlots` is needed.

## S3. Per-mode producer liveness (Rust/Deployed.lean)
Each takes the S2 hypotheses plus the mode rule. Get `suffix'`, `tl'`, `nb` from S2, with
`strip_sigs suffix' = ok tl'`, `toModelChain tl' = toModelChain tl ++ [toModelBlock nb]`,
`nb.slot = at_slot`, `nb.key_index = key_index`. Unfold `validate_deployed_X`: the base check is
S2's conclusion. What is left is the mode check on `tl'` = `tl` with `nb` appended
(prove a lemma `strip_sigs`/append shape: `tl'` is `tl` with `nb` snoc'd at the Rust level).
- **sched:** `sched_pin_ok era (tl ++ [nb])` by induction on `tl` from `hPinOld`, `hera`, `hPinNew`.
- **lock:** `lockstep_from n st.tip_slot g (tl ++ [nb])` by induction on `tl`, generalising `(ts, g)`;
  in the `Cons b rest` step, instantiate `hLockNew` at `toModelBlock b` for the new state.
  Note `validate_deployed_lock` reads `cert_state` (= `st` by hst) and `cert_gen` (= `g` by hgen).
- **k:** `key_mono_from n fl (tl ++ [nb])` by induction on `tl`, generalising `fl` and the invariant
  "`floor_lookup fl me = ok f` with `f.val ≤ key_index.val`". Helper:
  `floor_lookup fl me = ok f → floor_bump fl i v = ok bumped → ∃ f', floor_lookup bumped me = ok f' ∧
  f'.val ≤ max f.val (if i = me then v.val else 0)`, plus totality of `floor_bump`
  (`clone_floors_eq`, Rust/BridgeK.lean:48). Use `producer_for_slot_corr` for `i = me` ↔ model producer.
  `hshape` is only needed for the `floors_shape_ok` conjunct of `validate_deployed_k`.

## S4. Two real check times (in place)
`thm_rust_deployed_{agreement,k_agreement,sched_agreement}` now take `{R R' d}`, `hbridge` at
`max R R'`, `hφ : Δ.val + δ + d ≤ φ`, `hNow : R ≤ now+δ`, `hNow' : R' ≤ now'+δ`,
`hRR : R ≤ R' + d ∧ R' ≤ R + d`.
Proof: rename the current proofs to private `..._one_time` lemmas with the old statement (copy the old
statement text from `git show a5768f7~1:Spec/Statements.lean`), then instantiate at
`R* := max R R'`, `δ* := δ + d` (all side conditions by `omega`). Fix callers
(`rust_deployed_k_agreement` calls `rust_deployed_agreement` positionally).

## Close-out
All new theorems in `Paper/Proofs.lean` (`MoltPaper.<name> : thm_<name>`), axioms only
propext/Classical.choice/Quot.sound. Existing `#guard_msgs` axiom files: add entries for the new names
if the pattern there lists every Paper theorem.
