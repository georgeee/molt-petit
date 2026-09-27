import MoltPetit.Model.KeyRotation

/-!
# MoltPetit — bounded safety core for key rotation (Phase 2, increment I2a)

The cross-chain `HonestSlotsUnique` derivation under the key-stealing adversary
(`KeyStealingUnique.lean`) is an entanglement: honest-slot uniqueness — via the
versioned signature pin — needs the **in-force index** to agree across the two
chains under test, and in-force agreement runs through finality
(`deep_block_shared` / `no_deep_fork`), which in turn needs honest-slot
uniqueness. The standard BFT resolution is to break the cycle by a single strong
induction on the slot. For that to close we need a **bounded** form of the safety
core: one that requires honest-slot uniqueness only **up to the slot of its depth
witnesses**, not globally.

This file provides exactly that, as faithful bounded analogues of the audited
`Safety.lean` / `KeyRotation.lean` lemmas (the originals are left untouched):

* `no_deep_fork_le` — `no_deep_fork` with the honest hypothesis weakened to
  `∀ τ ≤ M, …` for a bound `M` dominating both depth witnesses' slots.
* `deep_block_shared_le` — the bounded membership-finality lemma.
* `confirmed_mem_iff_le` — **opt-A** (see `georgeee/mini-consensus-lean: PHASE2_DESIGN.md` §7.5): with
  `Δconf ≥ 2n` and both chains carrying a block at the coexistence slot `σ`, the
  confirmed prefixes (`b.slot + Δconf ≤ σ`) agree on membership, using only
  uniqueness at slots `< σ`. The trick is to pick **minimal** depth witnesses in
  the matured window `[b.slot+n, b.slot+2n) ⊆ [b.slot+1, σ)`, which exist in both
  chains because each reached `σ` (`block_in_minimal_window`).

The helpers `windowCount_pos_block`, `block_in_minimal_window`, `quorum_pos`,
`strictSlots_unique` are independently useful.
-/

namespace MoltPetit.Model

-- ===========================================================================
-- Witness existence: a quorum-dense matured window contains a block
-- ===========================================================================

/-- A block addressed at height `k` of `c` is a member of `c`. -/
private theorem mem_of_blockAt' {c : Chain} {k : Nat} {b : Block}
    (h : blockAt? c k = some b) : b ∈ c := by
  unfold blockAt? at h
  exact List.mem_of_getElem? h

/-- `CommonPrefixUpTo` is symmetric (local copy; the KeyRotation one is private). -/
private theorem commonPrefix_symm' {c c' : Chain} {h : Nat}
    (hG : CommonPrefixUpTo c c' h) : CommonPrefixUpTo c' c h :=
  fun k hk => (hG k hk).imp fun _ hB => ⟨hB.2, hB.1⟩

/-- The quorum is at least one whenever there is at least one participant. -/
theorem quorum_pos {n : Nat} (hn : 1 ≤ n) : 0 < quorum n := by
  unfold quorum; omega

/-- A window with a positive block count actually contains a chain block in it. -/
theorem windowCount_pos_block {c : Chain} {u len : Nat}
    (h : 0 < windowCount c u len) :
    ∃ B : Block, B ∈ c ∧ u ≤ B.slot ∧ B.slot < u + len := by
  unfold windowCount at h
  have hne : c.filter (blockInWindow u len) ≠ [] :=
    List.ne_nil_of_length_pos h
  obtain ⟨B, hB⟩ := List.exists_mem_of_ne_nil _ hne
  rw [List.mem_filter] at hB
  refine ⟨B, hB.1, ?_⟩
  have := hB.2
  simp only [blockInWindow, decide_eq_true_eq] at this
  exact this

/-- **A matured, dense window contains a block.** If `c` is matured-windows-dense
and observed a block `Dtip` at height `m` with the window `[u, u+n)` matured at
`Dtip` (`u + n ≤ Dtip.slot + 1`), then `c` carries a block whose slot lies in that
window. -/
theorem block_in_minimal_window {n : Nat} (hn : 1 ≤ n) {c : Chain}
    (hDense : MaturedWindowsDense n c)
    {m : Nat} {Dtip : Block} (hDtip : blockAt? c m = some Dtip)
    {u : Nat} (hmat : u + n ≤ Dtip.slot + 1) :
    ∃ B : Block, B ∈ c ∧ u ≤ B.slot ∧ B.slot < u + n := by
  have hq : quorum n ≤ windowCount c u n := hDense hDtip u hmat
  exact windowCount_pos_block (lt_of_lt_of_le (quorum_pos hn) hq)

-- ===========================================================================
-- Strict-slots uniqueness: one block per slot inside a single chain
-- ===========================================================================

/-- On a strictly-slot-increasing chain, two members occupying the same slot are
the same block. (The intra-chain half of cross-chain honest-slot uniqueness.) -/
theorem strictSlots_unique {c : Chain} (hS : StrictSlots c) {B B' : Block}
    (hB : B ∈ c) (hB' : B' ∈ c) (hslot : B.slot = B'.slot) : B = B' := by
  obtain ⟨i, hi⟩ := exists_blockAt_of_mem hB
  obtain ⟨j, hj⟩ := exists_blockAt_of_mem hB'
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd (strictSlots_lt hS hi hj h) (by omega)
  · subst h; rw [hi] at hj; exact Option.some.inj hj
  · exact absurd (strictSlots_lt hS hj hi h) (by omega)

-- ===========================================================================
-- Bounded no_deep_fork (uniqueness needed only up to the witness slot)
-- ===========================================================================

/-- Bounded analogue of `no_deep_fork_aux`: honest-slot uniqueness is needed only
up to `D.slot`, the slot of the (earlier) depth witness. The shared honest slot
the pigeonhole produces lies in `[D.slot+1-n, D.slot+1)`, hence `≤ D.slot`. -/
private theorem no_deep_fork_aux_le
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hBudget : ByzantineBounded n bad)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    {h : Nat} (hLast : LastCommonHeight c c' h)
    {F D D' : Block} {m m' : Nat}
    (hHonestLe : ∀ τ, τ ≤ D.slot → ¬ bad τ →
      ∀ ⦃B B' : Block⦄, B ∈ record τ → B' ∈ record τ → B = B')
    (hF : blockAt? c h = some F)
    (hD : blockAt? c m = some D) (hD' : blockAt? c' m' = some D')
    (hDeep : F.slot + n ≤ D.slot) (hle : D.slot ≤ D'.slot) :
    False := by
  obtain ⟨hSeq, hS, -, hDense⟩ := hValid
  obtain ⟨hSeq', hS', -, hDense'⟩ := hValid'
  set u := D.slot + 1 - n with hu
  have hun : u + n = D.slot + 1 := by omega
  have huF : F.slot < u := by omega
  have hq : quorum n ≤ (chainSlotsIn c u n).card := by
    rw [chainSlotsIn_card hS]
    exact hDense hD u (by omega)
  have hq' : quorum n ≤ (chainSlotsIn c' u n).card := by
    rw [chainSlotsIn_card hS']
    exact hDense' hD' u (by omega)
  obtain ⟨s, hsC, hsC', hsHonest⟩ :=
    exists_honest_shared_slot hn hBudget
      chainSlotsIn_subset_Ico chainSlotsIn_subset_Ico hq hq'
  obtain ⟨B₁, hB₁mem, hB₁win, hB₁slot⟩ := mem_chainSlotsIn.mp hsC
  obtain ⟨B₂, hB₂mem, hB₂win, hB₂slot⟩ := mem_chainSlotsIn.mp hsC'
  obtain ⟨k₁, hk₁⟩ := exists_blockAt_of_mem hB₁mem
  obtain ⟨k₂, hk₂⟩ := exists_blockAt_of_mem hB₂mem
  have hB₁rec : B₁ ∈ record s := by rw [← hB₁slot]; exact hRec hk₁
  have hB₂rec : B₂ ∈ record s := by rw [← hB₂slot]; exact hRec' hk₂
  have hsLe : s ≤ D.slot := by
    have := hB₁win.2; omega
  have hBeq : B₁ = B₂ := hHonestLe s hsLe hsHonest hB₁rec hB₂rec
  have hkk : k₁ = k₂ := by
    have h₁ := hSeq hk₁
    have h₂ := hSeq' hk₂
    rw [hBeq] at h₁
    omega
  have hPost : h < k₁ :=
    height_gt_of_slot_gt hS hF hk₁ (by omega)
  exact hLast.2 k₁ hPost B₁ ⟨hk₁, by rw [hkk, hBeq]; exact hk₂⟩

/-- **Bounded core fork-killing theorem.** As `no_deep_fork`, but honest-slot
uniqueness is needed only at slots `≤ M`, for any bound `M` dominating both depth
witnesses' slots. -/
theorem no_deep_fork_le
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hBudget : ByzantineBounded n bad)
    {M : Nat}
    (hHonestLe : ∀ τ, τ ≤ M → ¬ bad τ →
      ∀ ⦃B B' : Block⦄, B ∈ record τ → B' ∈ record τ → B = B')
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    {h : Nat} (hLast : LastCommonHeight c c' h)
    {F D D' : Block} {m m' : Nat}
    (hF : blockAt? c h = some F)
    (hD : blockAt? c m = some D) (hD' : blockAt? c' m' = some D')
    (hMD : D.slot ≤ M) (hMD' : D'.slot ≤ M)
    (hDeep : F.slot + n ≤ D.slot) (hDeep' : F.slot + n ≤ D'.slot) :
    False := by
  rcases Nat.le_total D.slot D'.slot with hle | hle
  · exact no_deep_fork_aux_le hn hBudget hValid hValid' hRec hRec' hLast
      (fun τ hτ => hHonestLe τ (le_trans hτ hMD)) hF hD hD' hDeep hle
  · obtain ⟨X, hXc, hXc'⟩ := hLast.1 h le_rfl
    have hXF : X = F := by
      rw [hF] at hXc
      exact (Option.some.inj hXc).symm
    subst hXF
    exact no_deep_fork_aux_le hn hBudget hValid' hValid hRec' hRec hLast.symm
      (fun τ hτ => hHonestLe τ (le_trans hτ hMD')) hXc' hD' hD hDeep' hle

-- ===========================================================================
-- Bounded membership finality
-- ===========================================================================

/-- **Bounded membership finality.** As `deep_block_shared` (KeyRotation.lean),
but honest-slot uniqueness is needed only at slots `≤ M`, for `M` dominating both
witnesses' slots. -/
theorem deep_block_shared_le
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hBudget : ByzantineBounded n bad)
    {M : Nat}
    (hHonestLe : ∀ τ, τ ≤ M → ¬ bad τ →
      ∀ ⦃B B' : Block⦄, B ∈ record τ → B' ∈ record τ → B = B')
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hGenesis : CommonPrefixUpTo c c' 0)
    {k mD mD' : Nat} {b D D' : Block}
    (hb : blockAt? c k = some b)
    (hD : blockAt? c mD = some D) (hD' : blockAt? c' mD' = some D')
    (hMD : D.slot ≤ M) (hMD' : D'.slot ≤ M)
    (hDeep : b.slot + n ≤ D.slot) (hDeep' : b.slot + n ≤ D'.slot) :
    blockAt? c' k = some b := by
  cases hck : blockAt? c' k with
  | some B' =>
    by_cases hbB' : b = B'
    · rw [hbB']
    · obtain ⟨hgt, hhk, hLast⟩ :=
        exists_lastCommonHeight hId hRec hRec' hValid.2.2.1 hValid'.2.2.1
          hGenesis hb hck hbB'
      obtain ⟨F, hFc, -⟩ := hLast.1 hgt le_rfl
      have hFb : F.slot < b.slot := strictSlots_lt hValid.2.1 hFc hb hhk
      exact (no_deep_fork_le hn hBudget hHonestLe hValid hValid' hRec hRec'
        hLast hFc hD hD' hMD hMD' (by omega) (by omega)).elim
  | none =>
    exfalso
    have hmD'len : mD' < c'.length := by
      have h' := hD'; unfold blockAt? at h'
      obtain ⟨hlen, -⟩ := List.getElem?_eq_some_iff.mp h'
      exact hlen
    have hklen : c'.length ≤ k := by
      have h' := hck; unfold blockAt? at h'
      exact List.getElem?_eq_none_iff.mp h'
    have hmD'k : mD' < k := lt_of_lt_of_le hmD'len hklen
    obtain ⟨Bc, hBc⟩ := exists_blockAt_of_le (Nat.le_of_lt hmD'k) hb
    by_cases hsh : Bc = D'
    · have hlt : D'.slot < b.slot := by
        have := strictSlots_lt hValid.2.1 hBc hb hmD'k
        rwa [hsh] at this
      omega
    · obtain ⟨hgt, hhm, hLast⟩ :=
        exists_lastCommonHeight hId hRec hRec' hValid.2.2.1 hValid'.2.2.1
          hGenesis hBc hD' hsh
      obtain ⟨F, hFc, -⟩ := hLast.1 hgt le_rfl
      have hFb : F.slot < b.slot :=
        strictSlots_lt hValid.2.1 hFc hb (lt_trans hhm hmD'k)
      exact no_deep_fork_le hn hBudget hHonestLe hValid hValid' hRec hRec'
        hLast hFc hD hD' hMD hMD' (by omega) (by omega)

-- ===========================================================================
-- opt-A: confirmed-prefix membership agreement, uniqueness only below σ
-- ===========================================================================

/-- **opt-A confirmed-prefix agreement.** Two valid chains sharing genesis, each
carrying a block at the coexistence slot `σ`, agree on membership of every
confirmed block (`b.slot + Δconf ≤ σ`), needing honest-slot uniqueness only at
slots **strictly below `σ`**. The depth witnesses are chosen minimal — in the
matured window `[b.slot+n, b.slot+2n)`, which (given `Δconf ≥ 2n`) sits in
`[b.slot+1, σ)` and is matured in both chains because both reached `σ`. This is
the cycle-breaking lemma of `georgeee/mini-consensus-lean: PHASE2_DESIGN.md` §7.5. -/
theorem confirmed_mem_iff_le
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : 2 * n ≤ Δconf)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hBudget : ByzantineBounded n bad)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hGenesis : CommonPrefixUpTo c c' 0)
    {σ : Nat} {Bσ Bσ' : Block}
    (hBσ : Bσ ∈ c) (hsBσ : Bσ.slot = σ)
    (hBσ' : Bσ' ∈ c') (hsBσ' : Bσ'.slot = σ)
    (hHonestLt : ∀ τ, τ < σ → ¬ bad τ →
      ∀ ⦃B B' : Block⦄, B ∈ record τ → B' ∈ record τ → B = B') :
    ∀ b : Block, b.slot + Δconf ≤ σ → (b ∈ c ↔ b ∈ c') := by
  have key : ∀ {x x' : Chain} {Ex Ex' : Block},
      ValidChain n x → ValidChain n x' →
      ChainInRecord record x → ChainInRecord record x' →
      CommonPrefixUpTo x x' 0 →
      Ex ∈ x → Ex.slot = σ → Ex' ∈ x' → Ex'.slot = σ →
      ∀ b : Block, b.slot + Δconf ≤ σ → b ∈ x → b ∈ x' := by
    intro x x' Ex Ex' hVx hVx' hRx hRx' hGen hExmem hExσ hEx'mem hEx'σ b hbconf hbx
    obtain ⟨kb, hkb⟩ := exists_blockAt_of_mem hbx
    obtain ⟨mx, hmx⟩ := exists_blockAt_of_mem hExmem
    obtain ⟨mx', hmx'⟩ := exists_blockAt_of_mem hEx'mem
    have hmatx : (b.slot + n) + n ≤ Ex.slot + 1 := by omega
    obtain ⟨D, hDmem, hDlo, hDhi⟩ := block_in_minimal_window hn hVx.2.2.2 hmx hmatx
    have hmatx' : (b.slot + n) + n ≤ Ex'.slot + 1 := by omega
    obtain ⟨D', hD'mem, hD'lo, hD'hi⟩ := block_in_minimal_window hn hVx'.2.2.2 hmx' hmatx'
    obtain ⟨mD, hmD⟩ := exists_blockAt_of_mem hDmem
    obtain ⟨mD', hmD'⟩ := exists_blockAt_of_mem hD'mem
    have hMlt : max D.slot D'.slot < σ := by
      rw [Nat.max_lt]; exact ⟨by omega, by omega⟩
    refine mem_of_blockAt' (deep_block_shared_le hn hBudget (M := max D.slot D'.slot)
      (fun τ hτ => hHonestLt τ (lt_of_le_of_lt hτ hMlt)) hId
      hVx hVx' hRx hRx' hGen hkb hmD hmD'
      (le_max_left _ _) (le_max_right _ _) (by omega) (by omega))
  intro b hb
  constructor
  · intro hbc
    exact key hValid hValid' hRec hRec' hGenesis hBσ hsBσ hBσ' hsBσ' b hb hbc
  · intro hbc'
    exact key hValid' hValid hRec' hRec (commonPrefix_symm' hGenesis)
      hBσ' hsBσ' hBσ hsBσ b hb hbc'

end MoltPetit.Model
