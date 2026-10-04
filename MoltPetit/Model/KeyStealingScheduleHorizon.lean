import MoltPetit.Model.KeyStealingScheduleCert
import Spec.Model

/-!
# MoltPetit — the horizon-scoped budget (the top-window contraction)

The scheduled main theorems (`KeyStealingScheduleResults.lean`) consume the
chain-independent budget `ByzantineBounded n (badSched …)` — quantified over
**every** window, which forces the disclosed *retroactive reading*: because
`badSched s` counts thefts of any generation `j ≥ schedule s` and `Stolen` is
timeless, early windows accumulate the thefts of all later generations, and
the budget at historical windows is a lifetime-cumulative bound.

This module removes that price. The observation is proof-shaped: the default
agreement engine (`deep_block_agreement_of_height_depth`) runs its pigeonhole
at the **divergence** window — for a deep fork, an *old* window, which is why
the budget must hold retroactively there. But disagreement propagates
**upward** (a child commits its parent's id, so agreement at any height forces
agreement at every height below — `same_block_same_prefix`), so the pigeonhole
can instead run at the **trailing matured window below the lower tip**: both
chains are quorum-dense there, `2·quorum > n + maxByzantine` hands them a
shared non-corrupt slot, honest-slot uniqueness makes the two blocks there
**equal**, and the shared block drags the whole common prefix down to the
`n`-deep ancestor — and to genesis.

Consequences, both visible in the statements below:

* **The budget is consulted only above a horizon `H`** (`ByzantineBoundedFrom`)
  with `H + n ≤ tip.slot + 1` — under the tight recency rule
  (`now ≤ tip.slot + Δ`), a client may take `H = now − (Δ + n − 1)`: no
  window reaching further back than the last `Δ + n` slots is ever budgeted.
  The quantifier is a one-sided horizon — windows from `H` on, later ones
  included, remain in the hypothesis (the proof consults exactly one, the
  trailing window of the lower tip); what is removed is every constraint on
  historical windows: the *retroactive* reading is gone from the hypothesis.
  (`byzantineBoundedFrom_of_bounded` records that the old global budget
  delivers the new one; re-deriving the `KeyStealingScheduleResults`
  statements takes `H := 0`, whose side conditions `hH`/`hH'` reduce to
  `n ≤ tip.slot + 1` — true for any accepted chain longer than `n` by strict
  slots, though not recorded as a formal reduction.)
* **Shared genesis is a conclusion, not a hypothesis.** The top-window shared
  block forces agreement at *every* height below it, height `0` included —
  the statements consume no `hHead`/`hHead'` and no anchor of any kind. (The
  genesis parameter `G` survives only inside `SignedHashInjective`'s
  genesis-or-signed domain, where full signature coverage makes its branch
  unused.)

The temporal reading of the horizon budget — which real-time thefts can poison
a window above `H` — is the business of `KeyStealingScheduleTimed.lean`, which
derives the horizon budget from a *recent-theft rate* under just-in-time
provisioning. This module is purely combinatorial: no new model, no new
assumption surface, the same `SchedUnforgeable`/`SchedCoreUnforgeable`
surfaces as the existing scheduled set.

Honest scope: recency is still consumed as the domain scope of the EUF-CMA
surface (unchanged), and the surface itself is still a named crypto
assumption. What this module changes is exactly the budget's quantifier — from
all windows to the recent horizon — and the removal of the shared-genesis
hypothesis.
-/

namespace MoltPetit.Model

-- ===========================================================================
-- The horizon-scoped budget
-- ===========================================================================

/-- The global budget delivers every horizon budget — the horizon theorems
strictly generalize the global-budget ones. -/
theorem byzantineBoundedFrom_of_bounded {H n : Nat} {bad : ByzantineSlots}
    (h : ByzantineBounded n bad) : ByzantineBoundedFrom H n bad :=
  fun u _ => h u

-- ===========================================================================
-- Single-window pigeonhole and slot-gap plumbing
-- ===========================================================================

/-- `exists_honest_shared_slot` with the budget consumed at the **single**
window it is applied to (the original takes the global `ByzantineBounded` and
uses it only at `u`; this variant makes that locality available). -/
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

/-- Along a strict-slot chain, slots grow at least as fast as positions:
`d` positions apart means at least `d` slots apart. -/
private theorem slot_gap_of_position_gap {c : Chain} (hS : StrictSlots c) :
    ∀ (d p : Nat) {X Y : Block}, blockAt? c p = some X →
      blockAt? c (p + d) = some Y → X.slot + d ≤ Y.slot := by
  intro d
  induction d with
  | zero =>
    intro p X Y hX hY
    rw [Nat.add_zero, hX] at hY
    injection hY with hEq
    subst hEq
    omega
  | succ d ih =>
    intro p X Y hX hY
    have hYlt : p + d + 1 < c.length := by
      unfold blockAt? at hY
      obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hY
      exact h
    obtain ⟨Z, hZ⟩ : ∃ Z, blockAt? c (p + d) = some Z := by
      cases hopt : blockAt? c (p + d) with
      | none =>
        unfold blockAt? at hopt
        have := List.getElem?_eq_none_iff.mp hopt
        omega
      | some Z => exact ⟨Z, rfl⟩
    have h1 := ih p hX hZ
    have h2 : Z.slot < Y.slot :=
      strictSlots_lt hS hZ hY (by omega)
    omega

-- ===========================================================================
-- The model-level core: top-window pigeonhole ⇒ shared prefix
-- ===========================================================================

/-- **Top-window shared prefix (the horizon core).** Two valid chains from one
execution record, with the lower tip's trailing matured window within budget:
they share their block at every height that is `n`-deep in the *lower-tipped*
chain. Validator-agnostic — consumed below by both the full and the core
scheduled validators.

The proof runs the `2q > n + f` pigeonhole at `u = tip.slot + 1 − n` (matured
in both chains, since `tip.slot ≤ tip'.slot`): the shared non-corrupt slot's
two blocks are equal by honest-slot uniqueness, sit strictly above height `k`
(their slot exceeds `B`'s, and slots order heights), and `same_block_same_prefix`
carries the agreement down to `k`. No hypothesis touches any window below
`u`, and no shared genesis is assumed. -/
theorem horizon_shared_prefix
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hHonest : HonestSlotsUnique bad record)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hle : tip.slot ≤ tip'.slot)
    (hBudgetU : (badSlotsIn bad (tip.slot + 1 - n) n).card ≤ maxByzantine n)
    {k : Nat} (hkdeep : k + n < c.length) :
    ∃ P : Block, blockAt? c k = some P ∧ blockAt? c' k = some P := by
  obtain ⟨hSeq, hS, hPL, hDense⟩ := hValid
  obtain ⟨hSeq', hS', hPL', hDense'⟩ := hValid'
  have hTipAt : blockAt? c (c.length - 1) = some tip := blockAt_getLast hTip
  have hTipAt' : blockAt? c' (c'.length - 1) = some tip' := blockAt_getLast hTip'
  obtain ⟨B, hB⟩ : ∃ B, blockAt? c k = some B := by
    cases hopt : blockAt? c k with
    | none =>
      unfold blockAt? at hopt
      have := List.getElem?_eq_none_iff.mp hopt
      omega
    | some X => exact ⟨X, rfl⟩
  -- the n-gap above k pushes B at least n slots below the tip
  have hgap : B.slot + n ≤ tip.slot := by
    have hstep := slot_gap_of_position_gap hS (c.length - 1 - k) k hB
      (by rw [show k + (c.length - 1 - k) = c.length - 1 by omega]; exact hTipAt)
    omega
  set u := tip.slot + 1 - n with hu
  have hun : u + n = tip.slot + 1 := by omega
  have hBu : B.slot < u := by omega
  -- both chains are quorum-dense on the trailing window of the lower tip
  have hq : quorum n ≤ (chainSlotsIn c u n).card := by
    rw [chainSlotsIn_card hS]
    exact hDense hTipAt u (by omega)
  have hq' : quorum n ≤ (chainSlotsIn c' u n).card := by
    rw [chainSlotsIn_card hS']
    exact hDense' hTipAt' u (by omega)
  obtain ⟨s, hsC, hsC', hsHonest⟩ :=
    exists_honest_shared_slot_at hn hBudgetU
      chainSlotsIn_subset_Ico chainSlotsIn_subset_Ico hq hq'
  -- the blocks both chains place in the shared honest slot are equal
  obtain ⟨B₁, hB₁mem, hB₁win, hB₁slot⟩ := mem_chainSlotsIn.mp hsC
  obtain ⟨B₂, hB₂mem, hB₂win, hB₂slot⟩ := mem_chainSlotsIn.mp hsC'
  obtain ⟨k₁, hk₁⟩ := exists_blockAt_of_mem hB₁mem
  obtain ⟨k₂, hk₂⟩ := exists_blockAt_of_mem hB₂mem
  have hB₁rec : B₁ ∈ record s := by rw [← hB₁slot]; exact hRec hk₁
  have hB₂rec : B₂ ∈ record s := by rw [← hB₂slot]; exact hRec' hk₂
  have hBeq : B₁ = B₂ := hHonest s hsHonest hB₁rec hB₂rec
  -- same height on both chains, strictly above k
  have hkk : k₁ = k₂ := by
    have h₁ := hSeq hk₁
    have h₂ := hSeq' hk₂
    rw [hBeq] at h₁
    omega
  have hsu : u ≤ s := (Finset.mem_Ico.mp (chainSlotsIn_subset_Ico hsC)).1
  have hk_lt : k < k₁ :=
    height_gt_of_slot_gt hS hB hk₁ (by omega)
  have hk₂' : blockAt? c' k₁ = some B₁ := by rw [hkk, hBeq]; exact hk₂
  -- the shared block drags the shared prefix down to k
  exact same_block_same_prefix hId hRec hRec' hPL hPL' hk₁ hk₂' (Nat.le_of_lt hk_lt)

-- ===========================================================================
-- Full-validator horizon theorems
-- ===========================================================================

/-- **Scheduled light-client safety with a horizon-scoped budget.** Two chains
accepted by the scheduled signed validator, with recent equal-height tips,
agree on the block `n` below each tip — with the corruption budget required
**only on windows from the horizon `H` on**, where `H` is at most one window
below both tips (`hH`/`hH'`; under the tight recency rule a client may take
`H = now − (Δ + n − 1)`, so no slot more than `Δ + n − 1` before `now` is
ever budgeted — windows from the horizon on remain in the hypothesis).

Against `sched_recent_tip_ancestor_agreement`: the budget hypothesis is
**weakened** from the global `ByzantineBounded` to `ByzantineBoundedFrom H`
(no retroactive reading — a theft of any generation charged to a historical
window is never consulted) at the price of the two arithmetic side
conditions `hH`/`hH'` tying `H` to the tips; and the shared genesis
(`hHead`/`hHead'`) is **gone** — the top-window shared block forces the
entire common prefix, so genesis agreement is a consequence (stated
literally by `sched_recent_genesis_agreement_horizon` below; `G` survives
only as the unused genesis exemption inside `SignedHashInjective`). Recency
remains exactly the domain scope of `SchedUnforgeable`. -/
theorem sched_recent_tip_ancestor_agreement_horizon
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hUnf : SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    {H : Nat}
    (hBudget : ByzantineBoundedFrom H n (badSched n schedule rented Stolen))
    (hVal  : validSignedChainSched n schedule ops registry sc  = true)
    (hVal' : validSignedChainSched n schedule ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hH  : H + n ≤ sTip.slot  + 1)
    (hH' : H + n ≤ sTip'.slot + 1)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B' := by
  have hVc  : ValidChain n (stripSigs sc)  := validChain_of_validSignedChainSched hVal
  have hVc' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSched hVal'
  have hSig  : ∀ b ∈ stripSigs sc,  b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_sched hVal  hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_sched hVal' hb)
  -- height = list index, so equal tip heights ⇒ equal lengths ⇒ one global k
  have hTipIdx  : sTip.height  = (stripSigs sc ).length - 1 := hVc.1  (blockAt_getLast hTipS)
  have hTipIdx' : sTip'.height = (stripSigs sc').length - 1 := hVc'.1 (blockAt_getLast hTipS')
  have hLenEq : (stripSigs sc).length - 1 - n = (stripSigs sc').length - 1 - n := by omega
  rw [← hLenEq] at hB'
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · have hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hHash hSig hSig'
    have hUniq := honestSlotsUnique_sched hUnf hVal hVal'
      ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩
    obtain ⟨P, hPc, hPc'⟩ := horizon_shared_prefix hn hUniq hId hVc hVc'
      chainInRecord_left chainInRecord_right hTipS hTipS' hle
      (hBudget _ (by omega)) (k := (stripSigs sc).length - 1 - n) (by omega)
    rw [hB] at hPc
    rw [hB'] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']
  · have hId : IdInjective (chainUnionRecord sc' sc) := idInjective_keyrot hHash hSig' hSig
    have hUniq := honestSlotsUnique_sched hUnf hVal' hVal
      ⟨sTip', hTipS', hRecent'⟩ ⟨sTip, hTipS, hRecent⟩
    obtain ⟨P, hPc', hPc⟩ := horizon_shared_prefix hn hUniq hId hVc' hVc
      chainInRecord_left chainInRecord_right hTipS' hTipS hle
      (hBudget _ (by omega)) (k := (stripSigs sc).length - 1 - n) (by omega)
    rw [hB] at hPc
    rw [hB'] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']

/-- **Consistency form with a horizon-scoped budget** (unequal tip heights):
the `n`-deep ancestor of the lower-tipped chain is a block of the other chain
too, at least `n` deep there. Same horizon budget, no shared-genesis
hypothesis. -/
theorem sched_recent_tip_ancestor_mem_horizon
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hUnf : SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    {H : Nat}
    (hBudget : ByzantineBoundedFrom H n (badSched n schedule rented Stolen))
    (hVal  : validSignedChainSched n schedule ops registry sc  = true)
    (hVal' : validSignedChainSched n schedule ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hH  : H + n ≤ sTip.slot  + 1)
    (hH' : H + n ≤ sTip'.slot + 1)
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block}
    (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - n) = some B) :
    ∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B := by
  have hVc  : ValidChain n (stripSigs sc)  := validChain_of_validSignedChainSched hVal
  have hVc' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSched hVal'
  have hSig  : ∀ b ∈ stripSigs sc,  b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_sched hVal  hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_sched hVal' hb)
  have hTipIdx  : sTip.height  = (stripSigs sc ).length - 1 := hVc.1  (blockAt_getLast hTipS)
  have hTipIdx' : sTip'.height = (stripSigs sc').length - 1 := hVc'.1 (blockAt_getLast hTipS')
  set k : Nat := (stripSigs sc).length - 1 - n with hk
  have hkn' : k + n < (stripSigs sc').length := by omega
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · have hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hHash hSig hSig'
    have hUniq := honestSlotsUnique_sched hUnf hVal hVal'
      ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩
    obtain ⟨P, hPc, hPc'⟩ := horizon_shared_prefix hn hUniq hId hVc hVc'
      chainInRecord_left chainInRecord_right hTipS hTipS' hle
      (hBudget _ (by omega)) (k := k) (by omega)
    rw [hB] at hPc
    exact ⟨k, hkn', by rw [Option.some.inj hPc]; exact hPc'⟩
  · have hId : IdInjective (chainUnionRecord sc' sc) := idInjective_keyrot hHash hSig' hSig
    have hUniq := honestSlotsUnique_sched hUnf hVal' hVal
      ⟨sTip', hTipS', hRecent'⟩ ⟨sTip, hTipS, hRecent⟩
    obtain ⟨P, hPc', hPc⟩ := horizon_shared_prefix hn hUniq hId hVc' hVc
      chainInRecord_left chainInRecord_right hTipS' hTipS hle
      (hBudget _ (by omega)) (k := k) (by omega)
    rw [hB] at hPc
    exact ⟨k, hkn', by rw [Option.some.inj hPc]; exact hPc'⟩

/-- **Genesis agreement, stated as a conclusion** (the module-doc claim made
literal). Two scheduled-validated chains with recent tips — heights
unconstrained, no shared-genesis or anchor hypothesis of any kind — carry the
**same block at height 0**. The top-window shared block forces the common
prefix all the way down. -/
theorem sched_recent_genesis_agreement_horizon
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hUnf : SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    {H : Nat}
    (hBudget : ByzantineBoundedFrom H n (badSched n schedule rented Stolen))
    (hVal  : validSignedChainSched n schedule ops registry sc  = true)
    (hVal' : validSignedChainSched n schedule ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hH  : H + n ≤ sTip.slot  + 1)
    (hH' : H + n ≤ sTip'.slot + 1) :
    ∃ P : Block, blockAt? (stripSigs sc ) 0 = some P ∧
      blockAt? (stripSigs sc') 0 = some P := by
  have hVc  : ValidChain n (stripSigs sc)  := validChain_of_validSignedChainSched hVal
  have hVc' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSched hVal'
  have hSig  : ∀ b ∈ stripSigs sc,  b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_sched hVal  hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_sched hVal' hb)
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · have hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hHash hSig hSig'
    have hUniq := honestSlotsUnique_sched hUnf hVal hVal'
      ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩
    exact horizon_shared_prefix hn hUniq hId hVc hVc'
      chainInRecord_left chainInRecord_right hTipS hTipS' hle
      (hBudget _ (by omega)) (k := 0) (by omega)
  · have hId : IdInjective (chainUnionRecord sc' sc) := idInjective_keyrot hHash hSig' hSig
    have hUniq := honestSlotsUnique_sched hUnf hVal' hVal
      ⟨sTip', hTipS', hRecent'⟩ ⟨sTip, hTipS, hRecent⟩
    obtain ⟨P, h1, h2⟩ := horizon_shared_prefix hn hUniq hId hVc' hVc
      chainInRecord_left chainInRecord_right hTipS' hTipS hle
      (hBudget _ (by omega)) (k := 0) (by omega)
    exact ⟨P, h2, h1⟩

-- ===========================================================================
-- Core-validator horizon theorems (certificate-path parity)
-- ===========================================================================

/-- `sched_recent_tip_ancestor_agreement_horizon` at core scope. -/
theorem sched_recent_tip_ancestor_agreement_horizon_core
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hUnf : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    {H : Nat}
    (hBudget : ByzantineBoundedFrom H n (badSched n schedule rented Stolen))
    (hVal  : validSignedChainSchedCore n schedule ops registry sc  = true)
    (hVal' : validSignedChainSchedCore n schedule ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hH  : H + n ≤ sTip.slot  + 1)
    (hH' : H + n ≤ sTip'.slot + 1)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B' := by
  have hVc  : ValidChain n (stripSigs sc)  := validChain_of_validSignedChainSchedCore hVal
  have hVc' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSchedCore hVal'
  have hSig  : ∀ b ∈ stripSigs sc,  b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_schedCore hVal  hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_schedCore hVal' hb)
  have hTipIdx  : sTip.height  = (stripSigs sc ).length - 1 := hVc.1  (blockAt_getLast hTipS)
  have hTipIdx' : sTip'.height = (stripSigs sc').length - 1 := hVc'.1 (blockAt_getLast hTipS')
  have hLenEq : (stripSigs sc).length - 1 - n = (stripSigs sc').length - 1 - n := by omega
  rw [← hLenEq] at hB'
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · have hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hHash hSig hSig'
    have hUniq := honestSlotsUnique_schedCore hUnf hVal hVal'
      ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩
    obtain ⟨P, hPc, hPc'⟩ := horizon_shared_prefix hn hUniq hId hVc hVc'
      chainInRecord_left chainInRecord_right hTipS hTipS' hle
      (hBudget _ (by omega)) (k := (stripSigs sc).length - 1 - n) (by omega)
    rw [hB] at hPc
    rw [hB'] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']
  · have hId : IdInjective (chainUnionRecord sc' sc) := idInjective_keyrot hHash hSig' hSig
    have hUniq := honestSlotsUnique_schedCore hUnf hVal' hVal
      ⟨sTip', hTipS', hRecent'⟩ ⟨sTip, hTipS, hRecent⟩
    obtain ⟨P, hPc', hPc⟩ := horizon_shared_prefix hn hUniq hId hVc' hVc
      chainInRecord_left chainInRecord_right hTipS' hTipS hle
      (hBudget _ (by omega)) (k := (stripSigs sc).length - 1 - n) (by omega)
    rw [hB] at hPc
    rw [hB'] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']

/-- `sched_recent_tip_ancestor_mem_horizon` at core scope. -/
theorem sched_recent_tip_ancestor_mem_horizon_core
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hUnf : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    {H : Nat}
    (hBudget : ByzantineBoundedFrom H n (badSched n schedule rented Stolen))
    (hVal  : validSignedChainSchedCore n schedule ops registry sc  = true)
    (hVal' : validSignedChainSchedCore n schedule ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hH  : H + n ≤ sTip.slot  + 1)
    (hH' : H + n ≤ sTip'.slot + 1)
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block}
    (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - n) = some B) :
    ∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B := by
  have hVc  : ValidChain n (stripSigs sc)  := validChain_of_validSignedChainSchedCore hVal
  have hVc' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSchedCore hVal'
  have hSig  : ∀ b ∈ stripSigs sc,  b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_schedCore hVal  hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_schedCore hVal' hb)
  have hTipIdx  : sTip.height  = (stripSigs sc ).length - 1 := hVc.1  (blockAt_getLast hTipS)
  have hTipIdx' : sTip'.height = (stripSigs sc').length - 1 := hVc'.1 (blockAt_getLast hTipS')
  set k : Nat := (stripSigs sc).length - 1 - n with hk
  have hkn' : k + n < (stripSigs sc').length := by omega
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · have hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hHash hSig hSig'
    have hUniq := honestSlotsUnique_schedCore hUnf hVal hVal'
      ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩
    obtain ⟨P, hPc, hPc'⟩ := horizon_shared_prefix hn hUniq hId hVc hVc'
      chainInRecord_left chainInRecord_right hTipS hTipS' hle
      (hBudget _ (by omega)) (k := k) (by omega)
    rw [hB] at hPc
    exact ⟨k, hkn', by rw [Option.some.inj hPc]; exact hPc'⟩
  · have hId : IdInjective (chainUnionRecord sc' sc) := idInjective_keyrot hHash hSig' hSig
    have hUniq := honestSlotsUnique_schedCore hUnf hVal' hVal
      ⟨sTip', hTipS', hRecent'⟩ ⟨sTip, hTipS, hRecent⟩
    obtain ⟨P, hPc', hPc⟩ := horizon_shared_prefix hn hUniq hId hVc' hVc
      chainInRecord_left chainInRecord_right hTipS' hTipS hle
      (hBudget _ (by omega)) (k := k) (by omega)
    rw [hB] at hPc
    exact ⟨k, hkn', by rw [Option.some.inj hPc]; exact hPc'⟩

end MoltPetit.Model
