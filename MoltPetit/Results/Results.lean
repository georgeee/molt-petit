import MoltPetit.Model.Grounded

/-!
# MoltPetit — main results

The protocol is defined in TypeScript (`moltPetit.ts`, compiled to
the Lean sidecar `Spec/TS.lean` by thales); everything below is
about the artifacts a node actually runs: `produceBlockCert` (sign →
compact against the certificate store → validate → ship) and
`validateCertifiedChain` (certificate verification, per-block signature
checks, structural suffix validation).

## Safety — the light-client theorems

* `ts_recent_tip_ancestor_agreement` — two certified chains accepted by
  `validateCertifiedChain`, suffixes longer than `n`, both tips passing
  the **tight recency rule** (`now ≤ tip.slot + n`) and at equal height,
  have the **same** ancestor `n` blocks below the tip.
* `ts_recent_tip_ancestor_mem` — the consistency form, without equal
  heights: the `n`-deep ancestor of the recent chain with the lower tip
  *is a block of* every other recent chain, at least `n` deep there too.
  All recent chains agree on their common prefix up to `n` below the
  lower tip.
* `ts_recent_produced_tip_ancestor_agreement` — the production side: a
  chain shipped by `produceBlockCert` agrees the same way with any
  validated recent chain.

Assumptions: `ByzantineBounded` (≤ `⌊(n-1)/3⌋` adversarial slots per
`n`-window), `SigUnforgeableRecent` (EUF-CMA + honest signing
discipline, scoped to recency-passing valid chains; an untimed stand-in.
The paper's Theorem 1 is the timed `exposure_certified_agreement`, which
derives this scope from the exposure model instead of assuming it), `SignedHashInjective` (id collision resistance
over occurring blocks), and per-node certificate unforgeability
(verifying certificates carry claims grounded in the genesis, over
*signed* blocks).

## Liveness — the chain grows

* `liveness_produce_block` / `liveness_produce_signed_block` — in an
  honest participant's slot, production *succeeds*: the extension passes
  the validator, so the chain keeps growing and blocks keep maturing
  toward finality (under `HonestBlocksCover` delivery).

All results depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace MoltPetit.Model

-- ---------------------------------------------------------------------------
-- Model safety (proved in Safety.lean, surfaced here as the model results
-- that the per-implementation corollaries in Results_ts / Results_rust rest on)
-- ---------------------------------------------------------------------------

/-- No two semantically valid chains fork `n`-deep (model form). -/
alias model_no_deep_fork := no_deep_fork

/-- Any block `n`-deep on two semantically valid chains is identical (model form). -/
alias model_deep_block_agreement := deep_block_agreement

/-- A chain the executable validator `validChain` accepts is semantically valid
(`ValidChain`); this is the hinge both implementations transfer through. -/
alias model_validChain_sound := validChain_sound

-- ---------------------------------------------------------------------------
-- Liveness: production succeeds
-- ---------------------------------------------------------------------------

/--
**Liveness, abstract chain.** When slot `slot` belongs to honest
participant `me`, production succeeds: `produceBlock?` returns the new
block — the honest producer never skips its slot.
-/
theorem liveness_produce_block
    {n me slot newId : Nat} {contentsHash keyIndex : Nat}
    {bad : ByzantineSlots} {record : SlotRecord}
    {c : Chain} {tip : Block}
    (hBudget   : ByzantineBounded n bad)
    (hValid    : validChain n c = true)
    (hTipEq    : c.getLast? = some tip)
    (hTipLt    : tip.slot < slot)
    (hMine     : producerForSlot n slot = me)
    (hSCorrect : ∀ s (B : Block), B ∈ record s → B.slot = s)
    (hCover    : ∀ u, tip.slot + 1 < u + n → u + n ≤ slot + 1 →
        HonestBlocksCover bad record (c ++ [nextBlock slot newId contentsHash keyIndex tip]) u n) :
    produceBlock? n me slot newId contentsHash keyIndex c
      = some (nextBlock slot newId contentsHash keyIndex tip) := by
  have hExt := liveness_valid_extension hBudget hValid hTipEq hTipLt
    hSCorrect hCover
  simp [produceBlock?, hMine, hTipEq, hExt]

/--
**Liveness, wire level.** The signed variant also succeeds, additionally
assuming signature-scheme correctness (`SigCorrect`), a full registry
(`registry.size = n`), and that the producer signs with its own key.
This is exactly where the "standard assumption about the signature
primitive" discharges the self-check `produceSignedBlock?` performs on
its own signature.
-/
theorem liveness_produce_signed_block {σ sk pk : Type}
    {n me slot newId : Nat} {contentsHash keyIndex : Nat} (hn : 1 ≤ n)
    {ops : SigOps σ sk pk} {registry : KeyRegistry pk} {keyPair : Nat → Nat → sk}
    {bad : ByzantineSlots} {record : SlotRecord}
    {sc : SignedChain σ} {tip : Block}
    (hSig      : SigCorrect n ops registry keyPair)
    (hBudget   : ByzantineBounded n bad)
    (hValid    : validSignedChain n ops registry sc = true)
    (hTipEq    : (stripSigs sc).getLast? = some tip)
    (hTipLt    : tip.slot < slot)
    (hMine     : producerForSlot n slot = me)
    (hSCorrect : ∀ s (B : Block), B ∈ record s → B.slot = s)
    (hCover    : ∀ u, tip.slot + 1 < u + n → u + n ≤ slot + 1 →
        HonestBlocksCover bad record
          (stripSigs sc ++ [nextBlock slot newId contentsHash keyIndex tip]) u n) :
    produceSignedBlock? n me slot newId contentsHash keyIndex ops registry (keyPair me keyIndex) sc =
      some ⟨nextBlock slot newId contentsHash keyIndex tip,
            ops.sign (keyPair me keyIndex) (nextBlock slot newId contentsHash keyIndex tip)⟩ := by
  set b := nextBlock slot newId contentsHash keyIndex tip with hb
  set sb : SignedBlock σ := ⟨b, ops.sign (keyPair me keyIndex) b⟩ with hsb
  rw [validSignedChain, Bool.and_eq_true] at hValid
  obtain ⟨hSigs, hChain⟩ := hValid
  -- the new block's signature verifies against the versioned directory at
  -- the producer's current index (`b.keyIndex = keyIndex` by construction)
  have hbProducer : producerForSlot n b.slot = me := hMine
  have hbIndex : b.keyIndex = keyIndex := rfl
  have hSigOk : sigOk n ops registry sb = true := by
    rw [sigOk]
    show ops.verify (registry (producerForSlot n b.slot) b.keyIndex)
      b (ops.sign (keyPair me keyIndex) b) = true
    rw [hbProducer, hbIndex]
    exact hSig.verify_sign me keyIndex b hbProducer hbIndex
  -- all signatures of the extension verify
  have hSigsExt : sigsOk n ops registry (sc ++ [sb]) = true := by
    rw [sigsOk, List.all_append]
    rw [sigsOk] at hSigs
    simp [hSigs, hSigOk]
  -- the stripped extension passes the structural validator
  have hStrip : stripSigs (sc ++ [sb]) = stripSigs sc ++ [b] := by
    simp only [stripSigs, List.map_append, List.map_cons, List.map_nil]
    rfl
  have hExt : validChain n (stripSigs (sc ++ [sb])) = true := by
    rw [hStrip]
    exact liveness_valid_extension hBudget hChain hTipEq hTipLt
      hSCorrect hCover
  have hValidExt : validSignedChain n ops registry (sc ++ [sb]) = true := by
    rw [validSignedChain, Bool.and_eq_true]
    exact ⟨hSigsExt, hExt⟩
  simp [produceSignedBlock?, hMine, hTipEq, ← hb, ← hsb, hValidExt]


-- ---------------------------------------------------------------------------
-- Slot duration from certificate-prover throughput
-- ---------------------------------------------------------------------------

namespace ProverTiming

/-- One cycle preserves the budget: a backlog within `n/2` folds into a
backlog within `n/2`, provided the slot meets the recommendation. -/
theorem nextBacklog_le {n baseline perBlock τ : ℚ}
    (hn : 0 < n) (hpb : 0 ≤ perBlock) (hτpos : 0 < τ)
    (hτ : recommendedSlot n baseline perBlock ≤ τ)
    {u : ℚ} (hu : 0 ≤ u) (hub : u ≤ n / 2) :
    nextBacklog baseline perBlock τ u ≤ n / 2 := by
  unfold nextBacklog certTime
  rw [div_le_iff₀ hτpos]
  unfold recommendedSlot at hτ
  have h2 : 2 * baseline ≤ (τ - perBlock) * n := by
    have := (div_le_iff₀ hn).mp (by linarith : 2 * baseline / n ≤ τ - perBlock)
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hub hpb, mul_pos hτpos hn]

/-- Backlogs are never negative. -/
theorem nextBacklog_nonneg {baseline perBlock τ : ℚ}
    (hb : 0 ≤ baseline) (hpb : 0 ≤ perBlock) (hτpos : 0 < τ)
    {u : ℚ} (hu : 0 ≤ u) :
    0 ≤ nextBacklog baseline perBlock τ u := by
  unfold nextBacklog certTime
  positivity

/--
**The recommendation is sufficient.** At any slot duration meeting
`recommendedSlot`, a single prover that starts within budget
(`u₀ ≤ n/2`) keeps, for every future run `j`:

* the backlog at most `n/2`, and
* the peak uncovered suffix at most `n` — the node always holds a
  certificate plus at most `n` slots' worth of blocks.
-/
theorem recommended_slot_sufficient {n baseline perBlock τ : ℚ}
    (hn : 0 < n) (hb : 0 ≤ baseline) (hpb : 0 ≤ perBlock) (hτpos : 0 < τ)
    (hτ : recommendedSlot n baseline perBlock ≤ τ)
    {u₀ : ℚ} (hu₀ : 0 ≤ u₀) (hub₀ : u₀ ≤ n / 2) :
    ∀ j, backlog baseline perBlock τ u₀ j ≤ n / 2 ∧
      peakSuffix baseline perBlock τ (backlog baseline perBlock τ u₀ j) ≤ n := by
  have hstep : ∀ j, 0 ≤ backlog baseline perBlock τ u₀ j ∧
      backlog baseline perBlock τ u₀ j ≤ n / 2 := by
    intro j
    induction j with
    | zero => exact ⟨hu₀, hub₀⟩
    | succ j ih =>
      exact ⟨nextBacklog_nonneg hb hpb hτpos ih.1,
        nextBacklog_le hn hpb hτpos hτ ih.1 ih.2⟩
  intro j
  refine ⟨(hstep j).2, ?_⟩
  have hnext := nextBacklog_le hn hpb hτpos hτ (hstep j).1 (hstep j).2
  unfold peakSuffix
  linarith [(hstep j).2]

/--
**The recommendation is necessary.** At any slot duration strictly
between `perBlock` and `recommendedSlot`, the pipeline's steady state
(the backlog the prover converges to, where each fold leaves exactly the
backlog it started with) already overflows the window: its peak
uncovered suffix exceeds `n` slots' worth of blocks.
-/
theorem recommended_slot_necessary {n baseline perBlock τ : ℚ}
    (hn : 0 < n) (hpb0 : 0 ≤ perBlock) (hpb : perBlock < τ)
    (hτ : τ < recommendedSlot n baseline perBlock)
    {u : ℚ} (hsteady : nextBacklog baseline perBlock τ u = u) :
    n < peakSuffix baseline perBlock τ u := by
  have hτpos : 0 < τ := lt_of_le_of_lt hpb0 hpb
  have hfix : baseline + u * perBlock = u * τ := by
    have := hsteady
    unfold nextBacklog certTime at this
    field_simp at this
    linarith
  unfold peakSuffix
  rw [hsteady]
  -- goal: n < u + u; from u·(τ − perBlock) = baseline and τ − perBlock < 2·baseline/n
  unfold recommendedSlot at hτ
  have h2 : (τ - perBlock) * n < 2 * baseline := by
    have := (lt_div_iff₀ hn).mp (by linarith : τ - perBlock < 2 * baseline / n)
    linarith
  nlinarith

/--
**Slots at or below the per-block cost diverge.** If `τ ≤ perBlock`, the
prover falls behind by at least `baseline/τ` blocks every cycle — no
batching schedule keeps up, regardless of `n`.
-/
theorem backlog_diverges {baseline perBlock τ : ℚ}
    (hb : 0 ≤ baseline) (hτpos : 0 < τ) (hpb : τ ≤ perBlock)
    {u₀ : ℚ} (hu₀ : 0 ≤ u₀) :
    ∀ j : ℕ, u₀ + j * (baseline / τ) ≤ backlog baseline perBlock τ u₀ j := by
  have hstep : ∀ {u : ℚ}, 0 ≤ u →
      u + baseline / τ ≤ nextBacklog baseline perBlock τ u := by
    intro u hu
    unfold nextBacklog certTime
    have key : (u + baseline / τ) * τ = u * τ + baseline := by
      field_simp
    rw [le_div_iff₀ hτpos, key]
    nlinarith [mul_le_mul_of_nonneg_left hpb hu]
  intro j
  induction j with
  | zero => simp [backlog]
  | succ j ih =>
    have hnn : (0 : ℚ) ≤ backlog baseline perBlock τ u₀ j := by
      have hge := ih
      have : (0 : ℚ) ≤ u₀ + j * (baseline / τ) := by positivity
      linarith
    have := hstep hnn
    have hcast : ((j + 1 : ℕ) : ℚ) = (j : ℚ) + 1 := by push_cast; ring
    calc u₀ + ((j + 1 : ℕ) : ℚ) * (baseline / τ)
        = (u₀ + (j : ℚ) * (baseline / τ)) + baseline / τ := by rw [hcast]; ring
      _ ≤ backlog baseline perBlock τ u₀ j + baseline / τ := by linarith
      _ ≤ backlog baseline perBlock τ u₀ (j + 1) := this


end ProverTiming

end MoltPetit.Model
