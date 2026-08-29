import MoltPetit.Model.KeyStealingSafety
import MoltPetit.Model.KeyStealingUnique


/-!
# MoltPetit — the σ-localized horizon core (`Δconf ≥ n`)

The default key-stealing development gates confirmation at `Δconf ≥ 2n`
(`confirmed_mem_iff_le`, `KeyStealingSafety.lean`). That threshold is an
artifact of **where the pigeonhole is run**, not of what safety needs.

`confirmed_mem_iff_le` runs the agreement engine at the *divergence* window and
draws its depth witnesses from a confirmed block's matured window
`[b.slot+n, b.slot+2n)`; placing that whole window strictly below the
coexistence slot `σ` — which the strong slot-induction needs, so that the
uniqueness obligations land at `τ < σ` — is exactly what forces `2n ≤ Δconf`.

This module runs the same pigeonhole at a **σ-localized top window** `[σ-n, σ)`
instead. That window is matured in *both* chains by the coexistence block at
slot `σ` itself, so:

* the honest-slot obligation still lands strictly below `σ` (the induction is
  unchanged), while
* only `b.slot + n ≤ σ` is required of the confirmed block.

Hence `n ≤ Δconf` suffices. Two further consequences fall out:

* **Shared genesis is no longer a hypothesis.** Agreement propagates *downward*
  from the shared top-window block (`same_block_same_prefix`), so no
  last-common-height and no `hHead`/`hHead'` is consumed — mirroring the
  contraction `KeyStealingScheduleHorizon.lean` performs for the scheduled
  variant.
* Because a smaller `Δconf` makes `confirmedPrefix` **grow**, `inForce` rise and
  `badKeyrotOn` shrink, the budget hypothesis at `Δconf = n` is *weaker* than at
  `2n`: these statements are strictly **stronger** than their
  `KeyStealingSafety`/`KeyStealingResults` counterparts, which they therefore
  subsume rather than replace (the `2n` forms remain true and are kept).

What does **not** transport from the scheduled variant is the budget
contraction `ByzantineBoundedFrom`: mode 1's `badKeyrotOn` is chain-relative, so
the slot-induction must still reconcile `inForce` across the two chains, and
that induction consults windows all the way down. Chain-independence of
`badSched` is load-bearing upstream in `honestSlotsUnique_sched`, not inside the
horizon core — which is why the core transports here verbatim and the budget
contraction does not.

`n ≤ Δconf` is also the *semantic* floor, independently of this proof:
`inForce_agreement` (`KeyRotation.lean`) needs `n ≤ Δconf` to make `inForce`
execution-global, hence `badKeyrotOn` a genuine slot predicate.
-/


namespace MoltPetit.Model

/-- `exists_honest_shared_slot` with the budget consumed at the **single**
window it actually inspects — the enabling step for horizon- and
anchor-scoped budgets. -/
private theorem exists_honest_shared_slot_at
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {u : Nat}
    (hBudgetU : (badSlotsIn bad u n).card ≤ maxByzantine n)
    {S S' : Finset Nat}
    (hS : S ⊆ Finset.Ico u (u + n)) (hS' : S' ⊆ Finset.Ico u (u + n))
    (hCard : quorum n ≤ S.card) (hCard' : quorum n ≤ S'.card) :
    ∃ s, s ∈ S ∧ s ∈ S' ∧ ¬ bad s := by
  classical
  have hIcoCard : (Finset.Ico u (u + n)).card = n := by
    rw [Nat.card_Ico]
    omega
  have hUnion : (S ∪ S').card ≤ n := by
    calc (S ∪ S').card ≤ (Finset.Ico u (u + n)).card :=
          Finset.card_le_card (Finset.union_subset hS hS')
      _ = n := hIcoCard
  have hSum := Finset.card_union_add_card_inter S S'
  have hOverlap := quorum_overlap hn
  have hInter : maxByzantine n < (S ∩ S').card := by omega
  by_contra hNo
  push Not at hNo
  have hSub : S ∩ S' ⊆ badSlotsIn bad u n := by
    intro s hs
    have hsS := Finset.mem_inter.mp hs
    exact Finset.mem_filter.mpr ⟨hS hsS.1, hNo s hsS.1 hsS.2⟩
  have hLe : (S ∩ S').card ≤ (badSlotsIn bad u n).card := Finset.card_le_card hSub
  omega

/-- σ-localized top-window shared prefix: the pigeonhole runs at `[σ-n, σ)`,
matured in both chains by the coexistence block at slot `σ`, so the honest-slot
obligation lands **strictly below σ**, and a block `b` with `b.slot + n ≤ σ` is
shared. No genesis hypothesis, and the budget is consumed at the **single**
window `[σ-n, σ)`. -/
theorem sigma_shared_prefix
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord} {σ : Nat}
    (hBudgetU : (badSlotsIn bad (σ - n) n).card ≤ maxByzantine n)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    {Bσ Bσ' : Block}
    (hBσ : Bσ ∈ c) (hsBσ : Bσ.slot = σ)
    (hBσ' : Bσ' ∈ c') (hsBσ' : Bσ'.slot = σ)
    (hHonestLt : ∀ τ, τ < σ → ¬ bad τ →
      ∀ ⦃B B' : Block⦄, B ∈ record τ → B' ∈ record τ → B = B')
    {k : Nat} {b : Block}
    (hb : blockAt? c k = some b) (hdeep : b.slot + n ≤ σ) :
    blockAt? c' k = some b := by
  obtain ⟨hSeq, hS, hPL, hDense⟩ := hValid
  obtain ⟨hSeq', hS', hPL', hDense'⟩ := hValid'
  obtain ⟨mσ, hmσ⟩ := exists_blockAt_of_mem hBσ
  obtain ⟨mσ', hmσ'⟩ := exists_blockAt_of_mem hBσ'
  set u := σ - n with hu
  have hun : u + n = σ := by omega
  have hq : quorum n ≤ (chainSlotsIn c u n).card := by
    rw [chainSlotsIn_card hS]
    exact hDense hmσ u (by omega)
  have hq' : quorum n ≤ (chainSlotsIn c' u n).card := by
    rw [chainSlotsIn_card hS']
    exact hDense' hmσ' u (by omega)
  obtain ⟨s, hsC, hsC', hsHonest⟩ :=
    exists_honest_shared_slot_at hn hBudgetU
      chainSlotsIn_subset_Ico chainSlotsIn_subset_Ico hq hq'
  obtain ⟨B₁, hB₁mem, hB₁win, hB₁slot⟩ := mem_chainSlotsIn.mp hsC
  obtain ⟨B₂, hB₂mem, hB₂win, hB₂slot⟩ := mem_chainSlotsIn.mp hsC'
  obtain ⟨k₁, hk₁⟩ := exists_blockAt_of_mem hB₁mem
  obtain ⟨k₂, hk₂⟩ := exists_blockAt_of_mem hB₂mem
  have hB₁rec : B₁ ∈ record s := by rw [← hB₁slot]; exact hRec hk₁
  have hB₂rec : B₂ ∈ record s := by rw [← hB₂slot]; exact hRec' hk₂
  have hsLt : s < σ := by have := hB₁win.2; omega
  have hBeq : B₁ = B₂ := hHonestLt s hsLt hsHonest hB₁rec hB₂rec
  have hkk : k₁ = k₂ := by
    have h₁ := hSeq hk₁
    have h₂ := hSeq' hk₂
    rw [hBeq] at h₁
    omega
  -- b sits at or below the window's lower edge, hence at height ≤ k₁
  have hble : b.slot ≤ s := by have := hB₁win.1; omega
  have hkle : k ≤ k₁ := by
    by_contra hlt
    push_neg at hlt
    have := strictSlots_lt hS hk₁ hb hlt
    omega
  have hk₂' : blockAt? c' k₁ = some B₁ := by rw [hkk, hBeq]; exact hk₂
  obtain ⟨P, hPc, hPc'⟩ :=
    same_block_same_prefix hId hRec hRec' hPL hPL' hk₁ hk₂' hkle
  rw [hb] at hPc
  rw [Option.some.inj hPc]
  exact hPc'

/-- Confirmed-prefix membership agreement with `n ≤ Δconf` (not `2n`),
uniqueness only strictly below `σ`, and **no shared-genesis hypothesis**. -/
theorem confirmed_mem_iff_horizon
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {bad : ByzantineSlots} {record : SlotRecord} {σ : Nat}
    (hBudgetU : (badSlotsIn bad (σ - n) n).card ≤ maxByzantine n)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    {Bσ Bσ' : Block}
    (hBσ : Bσ ∈ c) (hsBσ : Bσ.slot = σ)
    (hBσ' : Bσ' ∈ c') (hsBσ' : Bσ'.slot = σ)
    (hHonestLt : ∀ τ, τ < σ → ¬ bad τ →
      ∀ ⦃B B' : Block⦄, B ∈ record τ → B' ∈ record τ → B = B') :
    ∀ b : Block, b.slot + Δconf ≤ σ → (b ∈ c ↔ b ∈ c') := by
  intro b hbconf
  constructor
  · intro hbc
    obtain ⟨k, hk⟩ := exists_blockAt_of_mem hbc
    have := sigma_shared_prefix hn hBudgetU hId hValid hValid' hRec hRec'
      hBσ hsBσ hBσ' hsBσ' hHonestLt hk (by omega)
    unfold blockAt? at this
    exact List.mem_of_getElem? this
  · intro hbc'
    obtain ⟨k, hk⟩ := exists_blockAt_of_mem hbc'
    have := sigma_shared_prefix hn hBudgetU hId hValid' hValid hRec' hRec
      hBσ' hsBσ' hBσ hsBσ hHonestLt hk (by omega)
    unfold blockAt? at this
    exact List.mem_of_getElem? this

/-- `honestSlotsUnique_keyrot` re-proved on the σ-localized horizon route:
`hΔ` weakened from `2 * n ≤ Δconf` to `n ≤ Δconf`, and the shared-genesis
hypothesis `hGenesis` **removed**. -/
theorem honestSlotsUnique_keyrot_horizon
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    (hUnf : VersionedUnforgeable n Δconf ops registry rented Stolen honestSigned now Δ)
    {sc sc' : SignedChain Sig}
    (hBudget : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc)))
    (hId : IdInjective (chainUnionRecord sc sc'))
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    (hRecent  : ∃ t,  (stripSigs sc ).getLast? = some t ∧ now ≤ t.slot + Δ)
    (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ) :
    HonestSlotsUnique (badKeyrotOn n Δconf rented Stolen (stripSigs sc))
      (chainUnionRecord sc sc') := by
  have hVc  : ValidChain n (stripSigs sc) := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal;  exact (validChainK'_sound hVal.2).1
  have hVc' : ValidChain n (stripSigs sc') := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal'; exact (validChainK'_sound hVal'.2).1
  have hRec  : ChainInRecord (chainUnionRecord sc sc') (stripSigs sc)  := chainInRecord_left
  have hRec' : ChainInRecord (chainUnionRecord sc sc') (stripSigs sc') := chainInRecord_right
  intro s
  induction s using Nat.strongRecOn with
  | ind s IH =>
    intro hbad B B' hB hB'
    rw [mem_chainUnionRecord] at hB hB'
    obtain ⟨hBmem, hBs⟩ := hB
    obtain ⟨hB'mem, hB's⟩ := hB'
    simp only [badKeyrotOn, not_or] at hbad
    obtain ⟨hNotRent, hNotStolen⟩ := hbad
    push Not at hNotStolen
    have cross : ∀ (X Y : Block), X ∈ stripSigs sc → Y ∈ stripSigs sc' →
        X.slot = s → Y.slot = s → X = Y := by
      intro X Y hXc hYc' hXs hYs
      obtain ⟨sbx, hsbxmem, hsbxeq⟩ := List.mem_map.mp hXc
      obtain ⟨sby, hsbymem, hsbyeq⟩ := List.mem_map.mp hYc'
      have hAgree : inForce n Δconf (stripSigs sc') (producerForSlot n s) s
                  = inForce n Δconf (stripSigs sc)  (producerForSlot n s) s := by
        apply inForce_agreement_of_confirmed_eq
        intro b hbconf
        exact confirmed_mem_iff_horizon hn hΔ (hBudget _) hId hVc' hVc hRec' hRec
          hYc' hYs hXc hXs IH b hbconf
      have hsbxslot : sbx.block.slot = s := by rw [hsbxeq]; exact hXs
      have hsbyslot : sby.block.slot = s := by rw [hsbyeq]; exact hYs
      have h1 : honestSigned (producerForSlot n s) s = some X := by
        have := hUnf.verified_was_signed hVal hsbxmem hRecent
          (by rw [hsbxslot]; exact hNotRent)
          (by rw [hsbxslot]; exact hNotStolen)
        rwa [hsbxslot, hsbxeq] at this
      have hNotStolen' : ∀ j, inForce n Δconf (stripSigs sc') (producerForSlot n s) s ≤ j →
          ¬ Stolen (producerForSlot n s) j := by
        rw [hAgree]; exact hNotStolen
      have h2 : honestSigned (producerForSlot n s) s = some Y := by
        have := hUnf.verified_was_signed hVal' hsbymem hRecent'
          (by rw [hsbyslot]; exact hNotRent)
          (by rw [hsbyslot]; exact hNotStolen')
        rwa [hsbyslot, hsbyeq] at this
      rw [h1] at h2; exact Option.some.inj h2
    rcases hBmem with hBc | hBc' <;> rcases hB'mem with hB'c | hB'c'
    · exact strictSlots_unique hVc.2.1 hBc hB'c (hBs.trans hB's.symm)
    · exact cross B B' hBc hB'c' hBs hB's
    · exact (cross B' B hB'c hBc' hB's hBs).symm
    · exact strictSlots_unique hVc'.2.1 hBc' hB'c' (hBs.trans hB's.symm)

/-- **Anchored honest-slot uniqueness: the budget reaches back only to the
anchor.** If both chains carry one shared block `A` — the client's *anchor* —
then honest-slot uniqueness holds with the corruption budget consulted
**only on windows ending after `A.slot`**: for slots at or below the anchor,
the two chains are literally the same list (`same_block_same_prefix` from
`A`), so no budget, no crypto, and no honesty is consumed there.

This is the formal content of the paper's *key-leak horizon*: the anchor may
be **arbitrarily old** — an older anchor simply means more windows must
satisfy the budget. With `A :=` genesis it degenerates to the global-budget
form. -/
theorem honestSlotsUnique_keyrot_anchored
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    (hUnf : VersionedUnforgeable n Δconf ops registry rented Stolen honestSigned now Δ)
    {sc sc' : SignedChain Sig} {A : Block}
    (hA  : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    (hBudgetFrom : ∀ u, A.slot + 1 ≤ u + n →
      (badSlotsIn (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) u n).card
        ≤ maxByzantine n)
    (hId : IdInjective (chainUnionRecord sc sc'))
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    (hRecent  : ∃ t,  (stripSigs sc ).getLast? = some t ∧ now ≤ t.slot + Δ)
    (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ) :
    HonestSlotsUnique (badKeyrotOn n Δconf rented Stolen (stripSigs sc))
      (chainUnionRecord sc sc') := by
  have hVc  : ValidChain n (stripSigs sc) := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal;  exact (validChainK'_sound hVal.2).1
  have hVc' : ValidChain n (stripSigs sc') := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal'; exact (validChainK'_sound hVal'.2).1
  have hRec  : ChainInRecord (chainUnionRecord sc sc') (stripSigs sc)  := chainInRecord_left
  have hRec' : ChainInRecord (chainUnionRecord sc sc') (stripSigs sc') := chainInRecord_right
  -- the anchor sits at the same index — its height — in both chains
  obtain ⟨kA, hkA⟩ := exists_blockAt_of_mem hA
  obtain ⟨kA', hkA'⟩ := exists_blockAt_of_mem hA'
  have hkAeq : kA' = kA := by
    have h1 := hVc.1 hkA
    have h2 := hVc'.1 hkA'
    omega
  rw [hkAeq] at hkA'
  have hPrefix : ∀ {k : Nat}, k ≤ kA →
      ∃ P : Block, blockAt? (stripSigs sc) k = some P ∧
        blockAt? (stripSigs sc') k = some P :=
    fun {k} hk =>
      same_block_same_prefix hId hRec hRec' hVc.2.2.1 hVc'.2.2.1 hkA hkA' hk
  intro s
  induction s using Nat.strongRecOn with
  | ind s IH =>
    intro hbad B B' hB hB'
    rw [mem_chainUnionRecord] at hB hB'
    obtain ⟨hBmem, hBs⟩ := hB
    obtain ⟨hB'mem, hB's⟩ := hB'
    rcases Nat.lt_or_ge s (A.slot + 1) with hsA | hsA
    · -- at or below the anchor: both chains are the same list here
      have cross0 : ∀ (X Y : Block), X ∈ stripSigs sc → Y ∈ stripSigs sc' →
          X.slot = s → Y.slot = s → X = Y := by
        intro X Y hXc hYc' hXs hYs
        obtain ⟨i, hi⟩ := exists_blockAt_of_mem hXc
        have hile : i ≤ kA := by
          by_contra hlt
          push Not at hlt
          have := strictSlots_lt hVc.2.1 hkA hi hlt
          omega
        obtain ⟨P, hPc, hPc'⟩ := hPrefix hile
        rw [hi] at hPc
        have hPX : X = P := Option.some.inj hPc
        rw [← hPX] at hPc'
        have hXc' : X ∈ stripSigs sc' := by
          unfold blockAt? at hPc'
          exact List.mem_of_getElem? hPc'
        exact strictSlots_unique hVc'.2.1 hXc' hYc' (hXs.trans hYs.symm)
      rcases hBmem with hBc | hBc' <;> rcases hB'mem with hB'c | hB'c'
      · exact strictSlots_unique hVc.2.1 hBc hB'c (hBs.trans hB's.symm)
      · exact cross0 B B' hBc hB'c' hBs hB's
      · exact (cross0 B' B hB'c hBc' hB's hBs).symm
      · exact strictSlots_unique hVc'.2.1 hBc' hB'c' (hBs.trans hB's.symm)
    · -- above the anchor: the horizon cross argument, budget at [s-n, s) only
      simp only [badKeyrotOn, not_or] at hbad
      obtain ⟨hNotRent, hNotStolen⟩ := hbad
      push Not at hNotStolen
      have cross : ∀ (X Y : Block), X ∈ stripSigs sc → Y ∈ stripSigs sc' →
          X.slot = s → Y.slot = s → X = Y := by
        intro X Y hXc hYc' hXs hYs
        obtain ⟨sbx, hsbxmem, hsbxeq⟩ := List.mem_map.mp hXc
        obtain ⟨sby, hsbymem, hsbyeq⟩ := List.mem_map.mp hYc'
        have hAgree : inForce n Δconf (stripSigs sc') (producerForSlot n s) s
                    = inForce n Δconf (stripSigs sc)  (producerForSlot n s) s := by
          apply inForce_agreement_of_confirmed_eq
          intro b hbconf
          exact confirmed_mem_iff_horizon hn hΔ
            (hBudgetFrom (s - n) (by omega)) hId hVc' hVc hRec' hRec
            hYc' hYs hXc hXs IH b hbconf
        have hsbxslot : sbx.block.slot = s := by rw [hsbxeq]; exact hXs
        have hsbyslot : sby.block.slot = s := by rw [hsbyeq]; exact hYs
        have h1 : honestSigned (producerForSlot n s) s = some X := by
          have := hUnf.verified_was_signed hVal hsbxmem hRecent
            (by rw [hsbxslot]; exact hNotRent)
            (by rw [hsbxslot]; exact hNotStolen)
          rwa [hsbxslot, hsbxeq] at this
        have hNotStolen' : ∀ j,
            inForce n Δconf (stripSigs sc') (producerForSlot n s) s ≤ j →
            ¬ Stolen (producerForSlot n s) j := by
          rw [hAgree]; exact hNotStolen
        have h2 : honestSigned (producerForSlot n s) s = some Y := by
          have := hUnf.verified_was_signed hVal' hsbymem hRecent'
            (by rw [hsbyslot]; exact hNotRent)
            (by rw [hsbyslot]; exact hNotStolen')
          rwa [hsbyslot, hsbyeq] at this
        rw [h1] at h2; exact Option.some.inj h2
      rcases hBmem with hBc | hBc' <;> rcases hB'mem with hB'c | hB'c'
      · exact strictSlots_unique hVc.2.1 hBc hB'c (hBs.trans hB's.symm)
      · exact cross B B' hBc hB'c' hBs hB's
      · exact (cross B' B hB'c hBc' hB's hBs).symm
      · exact strictSlots_unique hVc'.2.1 hBc' hB'c' (hBs.trans hB's.symm)

end MoltPetit.Model
