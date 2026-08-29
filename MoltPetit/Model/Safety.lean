import MoltPetit.Model.Model

/-!
# MoltPetit — safety

The headline result is `deep_block_agreement`:

> Under the practical execution assumptions (at most `⌊(n-1)/3⌋` adversarial
> slots in any `n`-slot window, honest slots contain at most one block,
> block ids are collision-free, observed chains consist of produced blocks),
> any two valid chains agree on every block that lies at least `n` slots
> behind an observed block of **both** chains.

The engine is `no_deep_fork`: two valid chains cannot both extend `n` slots
past their last common block. Its proof needs no window-alignment or
"no-recovery" assumption: take the `n`-slot window ending at the *earlier*
of the two observed blocks. By the cumulative density rule that window is
matured — hence quorum-dense — on **both** chains, and it lies entirely
after the fork point, so every block either chain places there is
post-fork. Two quorums in one window overlap in more than `maxByzantine n`
slots, so they share an honest slot; the honest block in that slot is the
same on both branches, contradicting divergence.
-/

namespace MoltPetit.Model

/-- A chain block occupying a slot beyond the slot of the height-`h` block
must itself sit at a height above `h`. -/
theorem height_gt_of_slot_gt {c : Chain} (hS : StrictSlots c)
    {h k : Nat} {F B : Block}
    (hF : blockAt? c h = some F) (hB : blockAt? c k = some B)
    (hSlot : F.slot < B.slot) : h < k := by
  by_contra hle
  push Not at hle
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · rw [hF] at hB
    injection hB with hEq
    rw [hEq] at hSlot
    omega
  · have := strictSlots_lt hS hB hF hlt
    omega

/-- Pigeonhole: two quorum-sized slot sets inside one `n`-slot window share
a slot the adversary does not control. -/
theorem exists_honest_shared_slot
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} (hBudget : ByzantineBounded n bad)
    {S S' : Finset Nat} {u : Nat}
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
  have hBound := hBudget u
  omega

/--
Asymmetric core: if `D` on chain `c` lies at least `n` slots past the last
common block `F`, and `D'` on chain `c'` is no earlier than `D`, the
execution is contradictory.

The shared window is `[D.slot + 1 - n, D.slot + 1)`: matured for `c` at `D`
and for `c'` at `D'`, entirely after `F.slot`.
-/
private theorem no_deep_fork_aux
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hBudget : ByzantineBounded n bad)
    (hHonest : HonestSlotsUnique bad record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    {h : Nat} (hLast : LastCommonHeight c c' h)
    {F D D' : Block} {m m' : Nat}
    (hF : blockAt? c h = some F)
    (hD : blockAt? c m = some D) (hD' : blockAt? c' m' = some D')
    (hDeep : F.slot + n ≤ D.slot) (hle : D.slot ≤ D'.slot) :
    False := by
  obtain ⟨hSeq, hS, -, hDense⟩ := hValid
  obtain ⟨hSeq', hS', -, hDense'⟩ := hValid'
  set u := D.slot + 1 - n with hu
  have hun : u + n = D.slot + 1 := by omega
  have huF : F.slot < u := by omega
  -- the common window is quorum-dense on both chains
  have hq : quorum n ≤ (chainSlotsIn c u n).card := by
    rw [chainSlotsIn_card hS]
    exact hDense hD u (by omega)
  have hq' : quorum n ≤ (chainSlotsIn c' u n).card := by
    rw [chainSlotsIn_card hS']
    exact hDense' hD' u (by omega)
  obtain ⟨s, hsC, hsC', hsHonest⟩ :=
    exists_honest_shared_slot hn hBudget
      chainSlotsIn_subset_Ico chainSlotsIn_subset_Ico hq hq'
  -- the blocks both chains place in the shared honest slot
  obtain ⟨B₁, hB₁mem, hB₁win, hB₁slot⟩ := mem_chainSlotsIn.mp hsC
  obtain ⟨B₂, hB₂mem, hB₂win, hB₂slot⟩ := mem_chainSlotsIn.mp hsC'
  obtain ⟨k₁, hk₁⟩ := exists_blockAt_of_mem hB₁mem
  obtain ⟨k₂, hk₂⟩ := exists_blockAt_of_mem hB₂mem
  -- both were produced, and the slot is honest, so they are the same block
  have hB₁rec : B₁ ∈ record s := by rw [← hB₁slot]; exact hRec hk₁
  have hB₂rec : B₂ ∈ record s := by rw [← hB₂slot]; exact hRec' hk₂
  have hBeq : B₁ = B₂ := hHonest s hsHonest hB₁rec hB₂rec
  -- they occupy the same height on both chains, strictly above the fork
  have hkk : k₁ = k₂ := by
    have h₁ := hSeq hk₁
    have h₂ := hSeq' hk₂
    rw [hBeq] at h₁
    omega
  have hPost : h < k₁ :=
    height_gt_of_slot_gt hS hF hk₁ (by omega)
  exact hLast.2 k₁ hPost B₁ ⟨hk₁, by rw [hkk, hBeq]; exact hk₂⟩

/--
**Core fork-killing theorem.** Two valid chains drawn from the same
execution record cannot both contain blocks at least `n` slots past their
last common block.
-/
theorem no_deep_fork
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hBudget : ByzantineBounded n bad)
    (hHonest : HonestSlotsUnique bad record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    {h : Nat} (hLast : LastCommonHeight c c' h)
    {F D D' : Block} {m m' : Nat}
    (hF : blockAt? c h = some F)
    (hD : blockAt? c m = some D) (hD' : blockAt? c' m' = some D')
    (hDeep : F.slot + n ≤ D.slot) (hDeep' : F.slot + n ≤ D'.slot) :
    False := by
  rcases Nat.le_total D.slot D'.slot with hle | hle
  · exact no_deep_fork_aux hn hBudget hHonest hValid hValid' hRec hRec'
      hLast hF hD hD' hDeep hle
  · obtain ⟨X, hXc, hXc'⟩ := hLast.1 h le_rfl
    have hXF : X = F := by
      rw [hF] at hXc
      exact (Option.some.inj hXc).symm
    subst hXF
    exact no_deep_fork_aux hn hBudget hHonest hValid' hValid hRec' hRec
      hLast.symm hXc' hD' hD hDeep' hle

/-! ## From a shared block back to a shared prefix

These lemmas (parent links plus collision-free ids force agreement on the
whole prefix below a shared block) are only needed to *locate* the last
common height in the user-facing theorem. -/

/-- Parent-link fact for a non-genesis block. -/
theorem parentLinked_at_succ {c : Chain} (hP : ParentLinked c)
    {k : Nat} {B : Block} (hAt : blockAt? c (k + 1) = some B) :
    ∃ P : Block, blockAt? c k = some P ∧ B.prev = some P.id := by
  simpa using hP hAt

/-- A block shared at height `k + 1` forces a shared parent at height `k`. -/
theorem same_block_same_parent
    {record : SlotRecord} (hId : IdInjective record)
    {c c' : Chain}
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hP : ParentLinked c) (hP' : ParentLinked c')
    {k : Nat} {B : Block}
    (hAt : blockAt? c (k + 1) = some B) (hAt' : blockAt? c' (k + 1) = some B) :
    ∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P := by
  obtain ⟨P, hPc, hPrev⟩ := parentLinked_at_succ hP hAt
  obtain ⟨P', hPc', hPrev'⟩ := parentLinked_at_succ hP' hAt'
  have hIdEq : P.id = P'.id := by
    rw [hPrev] at hPrev'
    exact Option.some.inj hPrev'
  have hPP : P = P' := hId P.slot P'.slot (hRec hPc) (hRec' hPc') hIdEq
  exact ⟨P, hPc, hPP ▸ hPc'⟩

/-- A shared block forces agreement at every earlier height. -/
theorem same_block_same_prefix
    {record : SlotRecord} (hId : IdInjective record)
    {c c' : Chain}
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hP : ParentLinked c) (hP' : ParentLinked c') :
    ∀ {m : Nat} {B : Block},
      blockAt? c m = some B →
      blockAt? c' m = some B →
      ∀ {k : Nat}, k ≤ m →
      ∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P := by
  intro m
  induction m with
  | zero =>
      intro B hAt hAt' k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      exact ⟨B, hAt, hAt'⟩
  | succ m ih =>
      intro B hAt hAt' k hk
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · exact ⟨B, hAt, hAt'⟩
      · have hkLe : k ≤ m := Nat.lt_succ_iff.mp hlt
        obtain ⟨P, hPc, hPc'⟩ :=
          same_block_same_parent hId hRec hRec' hP hP' hAt hAt'
        exact ih hPc hPc' hkLe

/-- Two chains sharing genesis but disagreeing at height `k` have a
well-defined last common height strictly below `k`. -/
theorem exists_lastCommonHeight
    {record : SlotRecord} (hId : IdInjective record)
    {c c' : Chain}
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hP : ParentLinked c) (hP' : ParentLinked c')
    (hCommon0 : CommonPrefixUpTo c c' 0)
    {k : Nat} {B B' : Block}
    (hAt : blockAt? c k = some B) (hAt' : blockAt? c' k = some B')
    (hNe : B ≠ B') :
    ∃ h, h < k ∧ LastCommonHeight c c' h := by
  classical
  let P : Nat → Prop := fun d =>
    d ≤ k ∧ ∀ X : Block, ¬ (blockAt? c d = some X ∧ blockAt? c' d = some X)
  have hPk : P k := by
    refine ⟨le_rfl, ?_⟩
    intro X hShared
    have hBX : B = X := by
      rw [hAt] at hShared
      exact Option.some.inj hShared.1
    have hB'X : B' = X := by
      rw [hAt'] at hShared
      exact Option.some.inj hShared.2
    exact hNe (hBX.trans hB'X.symm)
  have hExists : ∃ d, P d := ⟨k, hPk⟩
  let d := Nat.find hExists
  have hdP : P d := Nat.find_spec hExists
  have hdLe : d ≤ k := hdP.1
  have hdNeZero : d ≠ 0 := by
    intro hdZero
    rcases hCommon0 0 (by omega) with ⟨G, hG, hG'⟩
    exact hdP.2 G ⟨by simpa [d, hdZero] using hG, by simpa [d, hdZero] using hG'⟩
  refine ⟨d - 1, by omega, ?_, ?_⟩
  · intro j hj
    by_cases hShared : ∃ X : Block, blockAt? c j = some X ∧ blockAt? c' j = some X
    · simpa using hShared
    · have hjLeK : j ≤ k := by omega
      have hPj : P j := ⟨hjLeK, by simpa using hShared⟩
      have hdLeJ : d ≤ j := Nat.find_min' hExists hPj
      omega
  · intro j hj X hShared
    have hdLeJ : d ≤ j := by omega
    obtain ⟨Y, hY, hY'⟩ :=
      same_block_same_prefix hId hRec hRec' hP hP'
        hShared.1 hShared.2 (k := d) hdLeJ
    exact hdP.2 Y ⟨hY, hY'⟩

/--
**Safety (finality).**

Take any two valid chains `c`, `c'` drawn from the same execution record
and sharing genesis. If chain `c` contains an (observed) block `D` and
chain `c'` an observed block `D'`, then both chains carry the *same* block
at every height whose block lies at least `n` slots behind both `D` and
`D'`.

Operationally: a node finalizes a block in its chain once its own chain has
extended `n` slots past it; no valid chain anywhere in the system can ever
disagree with that block once it, too, reaches that depth — and a chain
that never does is dead, because growing past slot `B.slot + n` is exactly
what it cannot do without agreeing.

Assumptions are all operational:

* `hn` — at least one participant;
* `hBudget` — the adversary controls at most `⌊(n-1)/3⌋` slots in any `n`
  consecutive slots (one-third corruption, dynamic);
* `hHonest` — an honest slot contains at most one produced block ever
  (honest producers sign once; signatures are unforgeable);
* `hId` — block ids are collision-resistant hashes;
* `hValid`/`hValid'` — both chains pass the validator
  (`validChain_sound` in `Model/Soundness.lean` discharges this from the
  executable check);
* `hRec`/`hRec'` — chains consist of blocks that were actually produced;
* `hGenesis` — both chains start from the same genesis block.
-/
theorem deep_block_agreement
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hBudget : ByzantineBounded n bad)
    (hHonest : HonestSlotsUnique bad record)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hGenesis : CommonPrefixUpTo c c' 0)
    {k m m' : Nat} {B B' D D' : Block}
    (hB : blockAt? c k = some B) (hB' : blockAt? c' k = some B')
    (hD : blockAt? c m = some D) (hD' : blockAt? c' m' = some D')
    (hDeep : B.slot + n ≤ D.slot) (hDeep' : B.slot + n ≤ D'.slot) :
    B = B' := by
  by_contra hNe
  obtain ⟨h, hhk, hLast⟩ :=
    exists_lastCommonHeight hId hRec hRec' hValid.2.2.1 hValid'.2.2.1
      hGenesis hB hB' hNe
  obtain ⟨F, hFc, hFc'⟩ := hLast.1 h le_rfl
  have hFB : F.slot < B.slot := strictSlots_lt hValid.2.1 hFc hB hhk
  exact no_deep_fork hn hBudget hHonest hValid hValid' hRec hRec' hLast hFc
    hD hD' (by omega) (by omega)

/-! ## Height-depth corollary -/

/--
On a chain with strictly increasing slots, going from height `i` to height
`j ≥ i` adds at least `j - i` to the slot (each step adds ≥ 1).
-/
private theorem slot_ge_of_height_gap {c : Chain} (hS : StrictSlots c)
    {i : Nat} {Bi : Block} (hi : blockAt? c i = some Bi) :
    ∀ {j : Nat} {Bj : Block}, blockAt? c j = some Bj → i ≤ j →
      Bi.slot + (j - i) ≤ Bj.slot := by
  intro j
  induction j with
  | zero =>
    intro Bj hj hij
    have hiz : i = 0 := Nat.eq_zero_of_le_zero hij
    subst hiz; rw [hi] at hj; simp [Option.some.inj hj]
  | succ j' ih =>
    intro Bj hj hij
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · rw [hi] at hj; simp [Option.some.inj hj]
    · have hij' : i ≤ j' := Nat.lt_succ_iff.mp hlt
      obtain ⟨Bj', hBj'⟩ := exists_blockAt_of_le (Nat.le_succ j') hj
      have hIH := ih hBj' hij'
      have hStep : Bj'.slot < Bj.slot := strictSlots_lt hS hBj' hj (Nat.lt_succ_self j')
      omega

/--
**Safety, height-depth form.**

A block `B` at height `k` is final for chain `c` once chain `c` reaches
height `k + n` (i.e. contains at least `n` more blocks), and similarly for
`c'`. No slot arithmetic needed from the caller.

This is a direct corollary of `deep_block_agreement`: strictly-increasing
slots mean `n` extra heights imply at least `n` extra slots.
-/
theorem deep_block_agreement_of_height_depth
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hBudget : ByzantineBounded n bad)
    (hHonest : HonestSlotsUnique bad record)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hGenesis : CommonPrefixUpTo c c' 0)
    {k m m' : Nat} {B B' D D' : Block}
    (hB  : blockAt? c  k  = some B)  (hB' : blockAt? c' k  = some B')
    (hD  : blockAt? c  m  = some D)  (hD' : blockAt? c' m' = some D')
    (hDeep  : k + n ≤ m)
    (hDeep' : k + n ≤ m') :
    B = B' := by
  by_contra hNe
  obtain ⟨h, hhk, hLast⟩ :=
    exists_lastCommonHeight hId hRec hRec' hValid.2.2.1 hValid'.2.2.1
      hGenesis hB hB' hNe
  obtain ⟨F, hFc, hFc'⟩ := hLast.1 h le_rfl
  -- F is strictly earlier in slot than both B and B'
  have hFslotB  : F.slot < B.slot  :=
    strictSlots_lt hValid.2.1  hFc  hB  hhk
  have hFslotB' : F.slot < B'.slot :=
    strictSlots_lt hValid'.2.1 hFc' hB' hhk
  -- height gaps give slot gaps
  have hgapC  : B.slot  + (m  - k) ≤ D.slot  :=
    slot_ge_of_height_gap hValid.2.1  hB  hD  (by omega)
  have hgapC' : B'.slot + (m' - k) ≤ D'.slot :=
    slot_ge_of_height_gap hValid'.2.1 hB' hD' (by omega)
  exact no_deep_fork hn hBudget hHonest hValid hValid' hRec hRec' hLast hFc
    hD hD' (by omega) (by omega)

end MoltPetit.Model
