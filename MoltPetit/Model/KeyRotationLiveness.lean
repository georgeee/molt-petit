import MoltPetit.Results.Results
import MoltPetit.Model.KeyStealingCert

/-!
# MoltPetit — liveness under the index-pinned validator

The transport `validChainK'_sound` covers theorems *about accepted chains*
(safety, forged-time); liveness needs the **converse** — that the honest
producer's next block passes the *stricter* validator. This module closes that
disclosed seam with a sharp two-sided characterization:

* `liveness_produce_blockK` / `liveness_produce_signed_blockK` — production
  succeeds **and the extension is accepted by the index-pinned validator**,
  under exactly one hypothesis beyond the plain liveness ones: the declared
  version clears the producer's current chain floor
  (`keyFloor n c me ≤ keyIndex`). An honest producer signing at its live
  version satisfies this whenever the floor is its own (normal operation and
  its own rotations, where the declared version *is* the new floor).
* `extension_rejected_below_floor` — the converse: declaring **below** the
  floor is rejected (`validChainK' = false`). Together these make the
  index-inflation griefing surface a *theorem*, not just a disclosure: the
  extension is accepted iff the declared version clears the floor, so an
  adversary who legally inflates a producer's floor beyond the versions the
  producer can sign for (bounded key trees) provably halts that producer,
  while producers with unbounded hash-derived trees always recover. The
  deployment-level mitigation (an out-of-band root-authorization horizon on
  index jumps) is orthogonal and stated in the paper.
-/

namespace MoltPetit.Model

-- ---------------------------------------------------------------------------
-- Floor attainment
-- ---------------------------------------------------------------------------

private theorem foldl_max_attained (a : Nat) (L : List Nat) :
    L.foldl max a = a ∨ L.foldl max a ∈ L := by
  induction L generalizing a with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases ih (max a x) with h | h
    · rcases Nat.le_total a x with hax | hxa
      · right
        rw [h, Nat.max_eq_right hax]
        exact List.mem_cons_self ..
      · left
        rw [h, Nat.max_eq_left hxa]
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- A positive floor is attained: some chain block of the producer carries
exactly the floor index. -/
theorem exists_keyFloor_witness {n : Nat} {c : Chain} {i : Nat}
    (h : 0 < keyFloor n c i) :
    ∃ B ∈ c, producerForSlot n B.slot = i ∧ B.keyIndex = keyFloor n c i := by
  unfold keyFloor at h ⊢
  rcases foldl_max_attained 0 (((c.filter
      (fun b => decide (producerForSlot n b.slot = i))).map Block.keyIndex)) with h0 | hmem
  · omega
  · obtain ⟨B, hBf, hBk⟩ := List.mem_map.mp hmem
    obtain ⟨hBc, hBp⟩ := List.mem_filter.mp hBf
    rw [decide_eq_true_eq] at hBp
    exact ⟨B, hBc, hBp, hBk⟩

-- ---------------------------------------------------------------------------
-- The extension passes the pinned validator iff the version clears the floor
-- ---------------------------------------------------------------------------

/-- **Acceptance direction.** A `validChainK`-accepted chain extended by one
block whose declared version clears its producer's floor is accepted by the
**index-pinned** validator (any `Δconf`): structure and density via the plain
liveness lemma, the monotone rule via the floor gate, and the `≤`-pin implied
on the full chain. -/
theorem liveness_extension_validChainK'
    {n Δconf : Nat} {bad : ByzantineSlots} {record : SlotRecord}
    {c : Chain} {slot newId : Nat} {contentsHash keyIndex : Nat} {tip : Block}
    (hBudget   : ByzantineBounded n bad)
    (hValidK   : validChainK n c = true)
    (hTipEq    : c.getLast? = some tip)
    (hTipLt    : tip.slot < slot)
    (hSCorrect : ∀ s (B : Block), B ∈ record s → B.slot = s)
    (hCover    : ∀ u, tip.slot + 1 < u + n → u + n ≤ slot + 1 →
        HonestBlocksCover bad record (c ++ [nextBlock slot newId contentsHash keyIndex tip]) u n)
    (hFloor    : keyFloor n c (producerForSlot n slot) ≤ keyIndex) :
    validChainK' n Δconf (c ++ [nextBlock slot newId contentsHash keyIndex tip]) = true := by
  rw [validChainK, Bool.and_eq_true] at hValidK
  obtain ⟨hValid, hMono⟩ := hValidK
  apply validChainK'_of_validChainK
  rw [validChainK, Bool.and_eq_true]
  refine ⟨liveness_valid_extension hBudget hValid hTipEq hTipLt hSCorrect hCover, ?_⟩
  refine keyMonoOk_append_of_from hMono ?_
  rw [keyMonoFrom, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hFloor, rfl⟩

/-- **Rejection direction (the griefing surface, as a theorem).** Declaring a
version strictly below the producer's floor makes the extension fail the
monotone rule, so the index-pinned validator rejects it. With
`liveness_extension_validChainK'` this is a sharp characterization: the
extension is accepted iff the declared version clears the floor. -/
theorem extension_rejected_below_floor
    {n Δconf : Nat} {c : Chain} {slot newId : Nat} {contentsHash keyIndex : Nat}
    {tip : Block}
    (hLt : keyIndex < keyFloor n c (producerForSlot n slot)) :
    validChainK' n Δconf (c ++ [nextBlock slot newId contentsHash keyIndex tip]) = false := by
  set b := nextBlock slot newId contentsHash keyIndex tip with hb
  have hbSlot : b.slot = slot := rfl
  have hbKi : b.keyIndex = keyIndex := rfl
  obtain ⟨W, hWc, hWp, hWk⟩ := exists_keyFloor_witness (n := n) (c := c)
    (i := producerForSlot n slot) (by omega)
  cases hK' : validChainK' n Δconf (c ++ [b]) with
  | false => rfl
  | true =>
    exfalso
    rw [validChainK', Bool.and_eq_true, validChainK, Bool.and_eq_true] at hK'
    have hpw := (keyMonoOk_iff_pairwise (n := n) (c ++ [b])).mp hK'.1.2
    rw [List.pairwise_append] at hpw
    have hcross := hpw.2.2 W hWc b (List.mem_singleton_self b)
      (by rw [hbSlot, hWp])
    rw [hWk, hbKi] at hcross
    omega

-- ---------------------------------------------------------------------------
-- Headline liveness theorems, pinned validator
-- ---------------------------------------------------------------------------

/-- **Liveness under the pinned validator, abstract chain.** Under the plain
liveness hypotheses plus the floor clearance `keyFloor n c me ≤ keyIndex`,
production succeeds and the produced extension is accepted by the
index-pinned validator `validChainK'`. -/
theorem liveness_produce_blockK
    {n Δconf me slot newId : Nat} {contentsHash keyIndex : Nat}
    {bad : ByzantineSlots} {record : SlotRecord}
    {c : Chain} {tip : Block}
    (hBudget   : ByzantineBounded n bad)
    (hValidK   : validChainK n c = true)
    (hTipEq    : c.getLast? = some tip)
    (hTipLt    : tip.slot < slot)
    (hMine     : producerForSlot n slot = me)
    (hSCorrect : ∀ s (B : Block), B ∈ record s → B.slot = s)
    (hCover    : ∀ u, tip.slot + 1 < u + n → u + n ≤ slot + 1 →
        HonestBlocksCover bad record (c ++ [nextBlock slot newId contentsHash keyIndex tip]) u n)
    (hFloor    : keyFloor n c me ≤ keyIndex) :
    produceBlock? n me slot newId contentsHash keyIndex c
      = some (nextBlock slot newId contentsHash keyIndex tip) ∧
    validChainK' n Δconf (c ++ [nextBlock slot newId contentsHash keyIndex tip]) = true := by
  have hValid : validChain n c = true := by
    rw [validChainK, Bool.and_eq_true] at hValidK
    exact hValidK.1
  refine ⟨liveness_produce_block hBudget hValid hTipEq hTipLt hMine hSCorrect hCover, ?_⟩
  exact liveness_extension_validChainK' hBudget hValidK hTipEq hTipLt hSCorrect hCover
    (by rw [hMine]; exact hFloor)

/-- **Liveness under the pinned validator, wire level.** The signed variant:
under signature-scheme correctness and the floor clearance, signed production
succeeds and the signed extension is accepted by the index-pinned **signed**
validator `validSignedChainK'`. This is the honest form of "liveness
transports": it does *not* hold unconditionally — the floor-clearance
hypothesis is exactly the index-inflation condition
(`extension_rejected_below_floor` is the converse). -/
theorem liveness_produce_signed_blockK {σ sk pk : Type}
    {n Δconf me slot newId : Nat} {contentsHash keyIndex : Nat} (hn : 1 ≤ n)
    {ops : SigOps σ sk pk} {registry : KeyRegistry pk} {keyPair : Nat → Nat → sk}
    {bad : ByzantineSlots} {record : SlotRecord}
    {sc : SignedChain σ} {tip : Block}
    (hSig      : SigCorrect n ops registry keyPair)
    (hBudget   : ByzantineBounded n bad)
    (hValidK'  : validSignedChainK' n Δconf ops registry sc = true)
    (hTipEq    : (stripSigs sc).getLast? = some tip)
    (hTipLt    : tip.slot < slot)
    (hMine     : producerForSlot n slot = me)
    (hSCorrect : ∀ s (B : Block), B ∈ record s → B.slot = s)
    (hCover    : ∀ u, tip.slot + 1 < u + n → u + n ≤ slot + 1 →
        HonestBlocksCover bad record
          (stripSigs sc ++ [nextBlock slot newId contentsHash keyIndex tip]) u n)
    (hFloor    : keyFloor n (stripSigs sc) me ≤ keyIndex) :
    produceSignedBlock? n me slot newId contentsHash keyIndex ops registry (keyPair me keyIndex) sc =
      some ⟨nextBlock slot newId contentsHash keyIndex tip,
            ops.sign (keyPair me keyIndex) (nextBlock slot newId contentsHash keyIndex tip)⟩ ∧
    validSignedChainK' n Δconf ops registry
      (sc ++ [⟨nextBlock slot newId contentsHash keyIndex tip,
              ops.sign (keyPair me keyIndex) (nextBlock slot newId contentsHash keyIndex tip)⟩]) = true := by
  set b := nextBlock slot newId contentsHash keyIndex tip with hb
  set sb : SignedBlock σ := ⟨b, ops.sign (keyPair me keyIndex) b⟩ with hsb
  rw [validSignedChainK', Bool.and_eq_true] at hValidK'
  obtain ⟨hSigs, hChainK'⟩ := hValidK'
  have hChainK : validChainK n (stripSigs sc) = true := by
    rw [validChainK', Bool.and_eq_true] at hChainK'
    exact hChainK'.1
  have hChain : validChain n (stripSigs sc) = true := by
    rw [validChainK, Bool.and_eq_true] at hChainK
    exact hChainK.1
  -- the plain signed liveness gives production success
  have hProd := liveness_produce_signed_block (n := n) hn hSig hBudget (by
      rw [validSignedChain, Bool.and_eq_true]
      exact ⟨hSigs, hChain⟩) hTipEq hTipLt hMine hSCorrect hCover
  refine ⟨hProd, ?_⟩
  -- signed extension passes the pinned signed validator
  have hStrip : stripSigs (sc ++ [sb]) = stripSigs sc ++ [b] := by
    simp only [stripSigs, List.map_append, List.map_cons, List.map_nil]
    rfl
  have hSigOk : sigOk n ops registry sb = true := by
    rw [sigOk]
    show ops.verify (registry (producerForSlot n b.slot) b.keyIndex)
      b (ops.sign (keyPair me keyIndex) b) = true
    have hbProducer : producerForSlot n b.slot = me := hMine
    have hbIndex : b.keyIndex = keyIndex := rfl
    rw [hbProducer, hbIndex]
    exact hSig.verify_sign me keyIndex b hbProducer hbIndex
  have hSigsExt : sigsOk n ops registry (sc ++ [sb]) = true := by
    rw [sigsOk, List.all_append]
    rw [sigsOk] at hSigs
    simp [hSigs, hSigOk]
  rw [validSignedChainK', Bool.and_eq_true]
  refine ⟨hSigsExt, ?_⟩
  rw [hStrip]
  exact liveness_extension_validChainK' hBudget hChainK hTipEq hTipLt hSCorrect hCover
    (by rw [hMine]; exact hFloor)

end MoltPetit.Model
