import Molt.Rotation

/-!
# The single-constant client rule (paper §6.3, mode 1)

Mode 1's client contract with **no user-chosen constant**: *re-sync at
least once every `n` slots*, anchoring the block `n` deep below each
verified tip.

The derivation, made formal here:

* `deep_block_span` — in a valid chain, the block `n` deep below a block
  `D` is fewer than `2n` slots below it: two full windows between them
  would demand `2·quorum > n` chain blocks where only `n` exist.
* At sync time `t` the tip passed recency, so `tipPrev.slot ≥ t - n`;
  hence the anchor satisfies `A.slot > t - 3n`; validating again within
  `n` slots of the sync gives `now ≤ A.slot + (4n - 1)`.
* `stay_recent_client_safe` — feeding that age into
  `client_refresh_rule` (at `H := 4n - 1`): safety with the corruption
  budget consulted only on windows meeting the trailing `< 5n` slots.
-/

namespace Molt

/-- Two disjoint predicates jointly refining `q`: their counts sum below
`q`'s count. -/
private theorem countP_add_le_countP
    {p₁ p₂ q : MoltPetit.Model.Block → Bool}
    (hdis : ∀ b, p₁ b = true → p₂ b = true → False)
    (h₁ : ∀ b, p₁ b = true → q b = true)
    (h₂ : ∀ b, p₂ b = true → q b = true) :
    ∀ l : List MoltPetit.Model.Block,
      l.countP p₁ + l.countP p₂ ≤ l.countP q
  | [] => by simp
  | b :: tl => by
    have ih := countP_add_le_countP hdis h₁ h₂ tl
    have key : (if p₁ b then 1 else 0) + (if p₂ b then 1 else 0)
        ≤ (if q b then (1 : Nat) else 0) := by
      by_cases hb₁ : p₁ b = true
      · have hq := h₁ b hb₁
        have hb₂ : p₂ b = false :=
          Bool.eq_false_iff.mpr fun h => hdis b hb₁ h
        simp [hb₁, hb₂, hq]
      · have hb₁' : p₁ b = false := Bool.eq_false_iff.mpr hb₁
        by_cases hb₂ : p₂ b = true
        · have hq := h₂ b hb₂
          simp [hb₁', hb₂, hq]
        · have hb₂' : p₂ b = false := Bool.eq_false_iff.mpr hb₂
          simp [hb₁', hb₂']
    simp only [List.countP_cons]
    omega

/-- On a strictly-slot-increasing chain, at most `k` blocks carry slots
in `(A.slot, D.slot]` when `A` and `D` sit `k` indices apart. -/
private theorem countP_between_le {c : MoltPetit.Model.Chain}
    (hS : MoltPetit.Model.StrictSlots c) {m k : Nat}
    {A D : MoltPetit.Model.Block}
    (hA : MoltPetit.Model.blockAt? c m = some A)
    (hD : MoltPetit.Model.blockAt? c (m + k) = some D) :
    c.countP (fun b => decide (A.slot < b.slot ∧ b.slot ≤ D.slot)) ≤ k := by
  set p : MoltPetit.Model.Block → Bool :=
    fun b => decide (A.slot < b.slot ∧ b.slot ≤ D.slot) with hp
  have hmlen : m < c.length := by
    unfold MoltPetit.Model.blockAt? at hA
    exact (List.getElem?_eq_some_iff.mp hA).1
  -- the prefix through `A` contributes nothing: its slots are ≤ A.slot
  have htake0 : (c.take (m + 1)).countP p = 0 := by
    apply List.countP_eq_zero.mpr
    intro b hb
    have hSt : MoltPetit.Model.StrictSlots (c.take (m + 1)) :=
      List.Pairwise.sublist (List.take_sublist _ _) hS
    have hlast : (c.take (m + 1)).getLast? = some A := by
      rw [List.getLast?_eq_getElem?]
      have hlen : (c.take (m + 1)).length = m + 1 := by
        rw [List.length_take]; omega
      rw [hlen, Nat.add_sub_cancel, List.getElem?_take_of_succ]
      unfold MoltPetit.Model.blockAt? at hA
      exact hA
    have hle : b.slot ≤ A.slot :=
      MoltPetit.Model.slot_le_tip_of_mem hSt hlast hb
    simp only [hp, decide_eq_true_eq]
    omega
  -- the suffix past `D` contributes nothing: its slots are > D.slot
  have hdrop0 : (c.drop (m + 1 + k)).countP p = 0 := by
    apply List.countP_eq_zero.mpr
    intro b hb
    have hD' := hD
    unfold MoltPetit.Model.blockAt? at hD'
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hD'
    have hcons := List.drop_eq_getElem_cons (l := c) hlt
    rw [heq] at hcons
    have hSd : MoltPetit.Model.StrictSlots (c.drop (m + k)) :=
      List.Pairwise.sublist (List.drop_sublist _ _) hS
    rw [hcons] at hSd
    have hb' : b ∈ c.drop (m + k + 1) := by
      have hidx : m + 1 + k = m + k + 1 := by omega
      rw [hidx] at hb
      exact hb
    have hDb : D.slot < b.slot := (List.pairwise_cons.mp hSd).1 b hb'
    simp only [hp, decide_eq_true_eq]
    omega
  -- assemble: prefix + (≤ k middle) + suffix
  calc c.countP p
      = (c.take (m + 1)).countP p + (c.drop (m + 1)).countP p := by
        rw [← List.countP_append, List.take_append_drop]
    _ = (c.drop (m + 1)).countP p := by rw [htake0]; omega
    _ = ((c.drop (m + 1)).take k).countP p
          + ((c.drop (m + 1)).drop k).countP p := by
        rw [← List.countP_append, List.take_append_drop]
    _ ≤ k + ((c.drop (m + 1)).drop k).countP p := by
        have h1 : ((c.drop (m + 1)).take k).countP p
            ≤ ((c.drop (m + 1)).take k).length := List.countP_le_length
        have h2 : ((c.drop (m + 1)).take k).length ≤ k := by
          rw [List.length_take]; omega
        omega
    _ = k + (c.drop (m + 1 + k)).countP p := by rw [List.drop_drop]
    _ = k := by rw [hdrop0]; omega

/-- **The deep anchor is nearby.** In a valid chain, the block `n` deep
below a block `D` is fewer than `2n` slots below it: were the gap `2n` or
more, the two matured `n`-slot windows inside it would each need `quorum`
chain blocks — more than the `n` blocks that exist between them. -/
theorem deep_block_span {n : Nat} (hn : 1 ≤ n) {c : Chain}
    (hV : ValidChain n c) {m : Nat} {A D : Block}
    (hA : blockAt? c m = some A) (hD : blockAt? c (m + n) = some D) :
    D.slot < A.slot + 2 * n := by
  rw [blockAt?_eq_core] at hA hD
  by_contra hcon
  obtain ⟨hSeq, hS, hPL, hMat⟩ := hV
  have hq₁ : MoltPetit.Model.quorum n
      ≤ MoltPetit.Model.windowCount c (A.slot + 1) n :=
    hMat hD (A.slot + 1) (by omega)
  have hq₂ : MoltPetit.Model.quorum n
      ≤ MoltPetit.Model.windowCount c (A.slot + 1 + n) n :=
    hMat hD (A.slot + 1 + n) (by omega)
  have hwc : ∀ u, MoltPetit.Model.windowCount c u n
      = c.countP (MoltPetit.Model.blockInWindow u n) := by
    intro u
    unfold MoltPetit.Model.windowCount
    rw [List.countP_eq_length_filter]
  have hsum := countP_add_le_countP
    (p₁ := MoltPetit.Model.blockInWindow (A.slot + 1) n)
    (p₂ := MoltPetit.Model.blockInWindow (A.slot + 1 + n) n)
    (q := fun b => decide (A.slot < b.slot ∧ b.slot ≤ D.slot))
    (fun b h₁ h₂ => by
      simp only [MoltPetit.Model.blockInWindow, decide_eq_true_eq] at h₁ h₂
      omega)
    (fun b h => by
      simp only [MoltPetit.Model.blockInWindow, decide_eq_true_eq] at h ⊢
      omega)
    (fun b h => by
      simp only [MoltPetit.Model.blockInWindow, decide_eq_true_eq] at h ⊢
      omega)
    c
  have hbetween := countP_between_le hS hA hD
  have hquorum : MoltPetit.Model.quorum n = (2 * n + 2) / 3 := rfl
  rw [hwc] at hq₁ hq₂
  omega

/-- **The single-constant client rule** (paper Theorem 3). No horizon
parameter: the client re-verifies a chain at least once every `n` slots
(`hCadence`, against the sync time `t` of the previously accepted chain
`scPrev`), each time anchoring the block `n` deep below the verified tip
(`hAnchor`), and refuses chains not containing its anchor. The corruption
budget is consulted only on windows meeting the trailing `< 5n` slots
(`hBudget`) — nothing is assumed about older history. Then two accepted,
recent, equal-height chains containing the anchor agree on the block `n`
below each tip.

Derivation: `tipPrev.slot ≥ t - n` (recency at sync),
`A.slot > tipPrev.slot - 2n` (`deep_block_span`), `now ≤ t + n`
(cadence) — so `now ≤ A.slot + (4n - 1)`, and `client_refresh_rule`
applies at `H := 4n - 1`. -/
theorem stay_recent_client_safe
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block}
    {sc sc' scPrev : SignedChain Sig} {A : Block}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen
      honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    -- the previous sync, at clock time t
    {t : Nat} {tipPrev : Block}
    (hVPrev : validSignedChainK' n Δconf ops registry scPrev = true)
    (hTipPrev : (stripSigs scPrev).getLast? = some tipPrev)
    (hRecPrev : t ≤ tipPrev.slot + n)
    (hLongPrev : n < (stripSigs scPrev).length)
    (hAnchor : blockAt? (stripSigs scPrev)
      ((stripSigs scPrev).length - 1 - n) = some A)
    -- the cadence
    (hCadence : now ≤ t + n)
    -- the anchor is honoured
    (hA : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    -- the standing budget, trailing < 5n slots
    (hBudget : ∀ u, now < u + 5 * n →
      (badSlotsIn (badKeyrot n Δconf rented Stolen (stripSigs sc)) u n).card
        ≤ faultBudget n)
    (hVal : validSignedChainK' n Δconf ops registry sc = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc )
      ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc')
      ((stripSigs sc').length - 1 - n) = some B') :
    B = B' := by
  -- the anchor's age is under 4n
  have hVPrev' := hVPrev
  rw [validSignedChainK'_eq_core] at hVPrev'
  rw [MoltPetit.Model.validSignedChainK', Bool.and_eq_true] at hVPrev'
  have hVc : MoltPetit.Model.ValidChain n (stripSigs scPrev) :=
    (MoltPetit.Model.validChainK'_sound hVPrev'.2).1
  have hTipIdx : MoltPetit.Model.blockAt? (stripSigs scPrev)
      ((stripSigs scPrev).length - 1) = some tipPrev :=
    MoltPetit.Model.blockAt_getLast hTipPrev
  have hidx : ((stripSigs scPrev).length - 1 - n) + n
      = (stripSigs scPrev).length - 1 := by omega
  have hspan : tipPrev.slot < A.slot + 2 * n :=
    deep_block_span hn hVc hAnchor (by rw [hidx]; exact hTipIdx)
  have hFresh : now ≤ A.slot + (4 * n - 1) := by omega
  exact client_refresh_rule hn hΔ hEUF hHash hA hA' hFresh
    (fun u hu => hBudget u (by omega)) hVal hVal' hTipS hTipS'
    hRecent hRecent' hLong hLong' hTipHeight hB hB'

/-- **The sync rule, final form** (paper Theorem 3): the confirmation
depth fixed at its provable minimum `n`, so the statement carries no
`Δconf` — the protocol has exactly one timing constant. A rotation takes
force once its announcing block is `n` slots deep; everything else is as
in `stay_recent_client_safe`. -/
theorem sync_rule
    {n : Nat} (hn : 1 ≤ n)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block}
    {sc sc' scPrev : SignedChain Sig} {A : Block}
    (hEUF : KeyStealingEUFCMA n n ops registry rented Stolen
      honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    {t : Nat} {tipPrev : Block}
    (hVPrev : validSignedChainK' n n ops registry scPrev = true)
    (hTipPrev : (stripSigs scPrev).getLast? = some tipPrev)
    (hRecPrev : t ≤ tipPrev.slot + n)
    (hLongPrev : n < (stripSigs scPrev).length)
    (hAnchor : blockAt? (stripSigs scPrev)
      ((stripSigs scPrev).length - 1 - n) = some A)
    (hCadence : now ≤ t + n)
    (hA : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    (hBudget : ∀ u, now < u + 5 * n →
      (badSlotsIn (badKeyrot n n rented Stolen (stripSigs sc)) u n).card
        ≤ faultBudget n)
    (hVal : validSignedChainK' n n ops registry sc = true)
    (hVal' : validSignedChainK' n n ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc )
      ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc')
      ((stripSigs sc').length - 1 - n) = some B') :
    B = B' :=
  stay_recent_client_safe hn (Nat.le_refl n) hEUF hHash hVPrev hTipPrev
    hRecPrev hLongPrev hAnchor hCadence hA hA' hBudget hVal hVal'
    hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'

/-- **The sync rule, membership form** (unequal tip heights): under the
same cadence, anchor, and trailing-`5n` budget as `sync_rule`, the
`n`-deep block of the lower-tipped accepted chain is a block of every
taller accepted chain too, at least `n` deep there. Together the two
forms cover any pair of accepted chains. -/
theorem sync_rule_mem
    {n : Nat} (hn : 1 ≤ n)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block}
    {sc sc' scPrev : SignedChain Sig} {A : Block}
    (hEUF : KeyStealingEUFCMA n n ops registry rented Stolen
      honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    {t : Nat} {tipPrev : Block}
    (hVPrev : validSignedChainK' n n ops registry scPrev = true)
    (hTipPrev : (stripSigs scPrev).getLast? = some tipPrev)
    (hRecPrev : t ≤ tipPrev.slot + n)
    (hLongPrev : n < (stripSigs scPrev).length)
    (hAnchor : blockAt? (stripSigs scPrev)
      ((stripSigs scPrev).length - 1 - n) = some A)
    (hCadence : now ≤ t + n)
    (hA : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    (hBudget : ∀ u, now < u + 5 * n →
      (badSlotsIn (badKeyrot n n rented Stolen (stripSigs sc)) u n).card
        ≤ faultBudget n)
    (hVal : validSignedChainK' n n ops registry sc = true)
    (hVal' : validSignedChainK' n n ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block}
    (hB : blockAt? (stripSigs sc)
      ((stripSigs sc).length - 1 - n) = some B) :
    ∃ i', i' + n < (stripSigs sc').length ∧
      blockAt? (stripSigs sc') i' = some B := by
  have hVPrev' := hVPrev
  rw [validSignedChainK'_eq_core] at hVPrev'
  rw [MoltPetit.Model.validSignedChainK', Bool.and_eq_true] at hVPrev'
  have hVc : MoltPetit.Model.ValidChain n (stripSigs scPrev) :=
    (MoltPetit.Model.validChainK'_sound hVPrev'.2).1
  have hTipIdx : MoltPetit.Model.blockAt? (stripSigs scPrev)
      ((stripSigs scPrev).length - 1) = some tipPrev :=
    MoltPetit.Model.blockAt_getLast hTipPrev
  have hidx : ((stripSigs scPrev).length - 1 - n) + n
      = (stripSigs scPrev).length - 1 := by omega
  have hspan : tipPrev.slot < A.slot + 2 * n :=
    deep_block_span hn hVc hAnchor (by rw [hidx]; exact hTipIdx)
  have hFresh : now ≤ A.slot + (4 * n - 1) := by omega
  have hVal₁ := hVal
  have hVal₁' := hVal'
  rw [validSignedChainK'_eq_core] at hVal₁ hVal₁'
  exact MoltPetit.Model.keyrot_recent_tip_ancestor_mem_anchored hn
    (Nat.le_refl n) hEUF hHash hA hA'
    (fun u hu => hBudget u (by omega))
    hVal₁ hVal₁' hTipS hTipS' hRecent hRecent' hLong hLong' hLe hB

end Molt
