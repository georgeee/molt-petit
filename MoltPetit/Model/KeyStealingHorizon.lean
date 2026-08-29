import MoltPetit.Model.KeyStealingSafety
import MoltPetit.Model.KeyStealingUnique
import MoltPetit.Model.KeyStealingHorizonCore
import MoltPetit.Results.KeyStealingResults
import MoltPetit.Model.KeyStealingScheduleHorizon

/-!
# MoltPetit — the genesis-free tip-ancestor form (mode 1, `Δconf ≥ n`)

The σ-localized core is in `KeyStealingHorizonCore.lean`, and the mode-1
theorem set in `KeyStealingSafety`/`KeyStealingResults`/`KeyStealingCert` now
consumes `n ≤ Δconf` directly. What this module adds is the one form that also
drops **shared genesis**, which needs the trailing-window contraction
`horizon_shared_prefix` from the scheduled horizon module (hence its position
late in the import order).

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

/-- **Tip-ancestor agreement, genesis-free.** The mode-1 headline proved through
the trailing-window contraction `horizon_shared_prefix`: `n ≤ Δconf`, and
**no** `hHead`/`hHead'`. Genesis-or-signed coverage is taken as `hSig`/`hSig'`
here; `keyrot_recent_tip_ancestor_agreement_horizon_of_valid` below discharges
it from the validator. -/
theorem keyrot_recent_tip_ancestor_agreement_horizon
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    {Signed : Block → Prop} {G : Block}
    {sc sc' : SignedChain Sig}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective Signed G)
    (hSig  : ∀ B ∈ stripSigs sc,  B = G ∨ Signed B)
    (hSig' : ∀ B ∈ stripSigs sc', B = G ∨ Signed B)
    (hBudget : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc)))
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
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
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B' := by
  have hVc  : ValidChain n (stripSigs sc) := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal;  exact (validChainK'_sound hVal.2).1
  have hVc' : ValidChain n (stripSigs sc') := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal'; exact (validChainK'_sound hVal'.2).1
  have hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hHash hSig hSig'
  have hUniq := honestSlotsUnique_keyrot_horizon hn hΔ
    (versionedUnforgeable_of_keyStealingEUFCMA hEUF) hBudget hId hVal hVal'
    ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩
  have hTipIdx  : sTip.height  = (stripSigs sc ).length - 1 := hVc.1  (blockAt_getLast hTipS)
  have hTipIdx' : sTip'.height = (stripSigs sc').length - 1 := hVc'.1 (blockAt_getLast hTipS')
  have hLenEq : (stripSigs sc).length - 1 - n = (stripSigs sc').length - 1 - n := by omega
  rw [← hLenEq] at hB'
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · obtain ⟨P, hPc, hPc'⟩ := horizon_shared_prefix hn hUniq hId hVc hVc'
      chainInRecord_left chainInRecord_right hTipS hTipS' hle
      (hBudget _) (k := (stripSigs sc).length - 1 - n) (by omega)
    rw [hB] at hPc
    rw [hB'] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']
  · obtain ⟨P, hPc', hPc⟩ := horizon_shared_prefix hn hUniq hId hVc' hVc
      chainInRecord_right chainInRecord_left hTipS' hTipS hle
      (hBudget _) (k := (stripSigs sc).length - 1 - n) (by omega)
    rw [hB] at hPc
    rw [hB'] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']

/-- **The anchored agreement — the key-leak horizon as a theorem.** If both
chains carry one shared block `A` — the client's *anchor*, of **arbitrary
age** — then the agreement conclusion holds with the corruption budget
consulted **only on windows ending after `A.slot`**. Below the anchor the two
chains are literally the same list, so nothing is assumed there: no budget,
no retired-key secrecy.

This is what sets the paper's *key-leak horizon*: the deployment picks how
old an anchor it will accept, and the budget (including any retired-key
leakage) must hold only over windows younger than that. An older anchor
means more windows to defend; `A :=` genesis recovers the global-budget
theorem. The anchor check is client-side and cheap: reject any chain not
containing the anchor block. -/
theorem keyrot_recent_tip_ancestor_agreement_anchored
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig} {A : Block}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    (hA  : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    (hBudgetFrom : ∀ u, A.slot + 1 ≤ u + n →
      (badSlotsIn (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) u n).card
        ≤ maxByzantine n)
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
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
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B' := by
  have hVc  : ValidChain n (stripSigs sc) := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal;  exact (validChainK'_sound hVal.2).1
  have hVc' : ValidChain n (stripSigs sc') := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal'; exact (validChainK'_sound hVal'.2).1
  have hId : IdInjective (chainUnionRecord sc sc') :=
    idInjective_keyrot hHash
      (fun b hb => Or.inr (keyStealingSigned_of_mem hVal  hb))
      (fun b hb => Or.inr (keyStealingSigned_of_mem hVal' hb))
  have hUniq := honestSlotsUnique_keyrot_anchored hn hΔ
    (versionedUnforgeable_of_keyStealingEUFCMA hEUF) hA hA' hBudgetFrom hId hVal hVal'
    ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩
  -- the anchor lies at or below each tip
  have hAle : A.slot ≤ sTip.slot := by
    obtain ⟨i, hi⟩ := exists_blockAt_of_mem hA
    have hTipAt : blockAt? (stripSigs sc) ((stripSigs sc).length - 1) = some sTip :=
      blockAt_getLast hTipS
    have hiLen : i < (stripSigs sc).length := by
      unfold blockAt? at hi
      exact (List.getElem?_eq_some_iff.mp hi).1
    rcases Nat.lt_or_ge i ((stripSigs sc).length - 1) with h | h
    · exact Nat.le_of_lt (strictSlots_lt hVc.2.1 hi hTipAt h)
    · have hieq : i = (stripSigs sc).length - 1 := by omega
      rw [hieq, hTipAt] at hi
      injection hi with hi
      rw [hi]
  have hAle' : A.slot ≤ sTip'.slot := by
    obtain ⟨i, hi⟩ := exists_blockAt_of_mem hA'
    have hTipAt : blockAt? (stripSigs sc') ((stripSigs sc').length - 1) = some sTip' :=
      blockAt_getLast hTipS'
    have hiLen : i < (stripSigs sc').length := by
      unfold blockAt? at hi
      exact (List.getElem?_eq_some_iff.mp hi).1
    rcases Nat.lt_or_ge i ((stripSigs sc').length - 1) with h | h
    · exact Nat.le_of_lt (strictSlots_lt hVc'.2.1 hi hTipAt h)
    · have hieq : i = (stripSigs sc').length - 1 := by omega
      rw [hieq, hTipAt] at hi
      injection hi with hi
      rw [hi]
  have hTipIdx  : sTip.height  = (stripSigs sc ).length - 1 := hVc.1  (blockAt_getLast hTipS)
  have hTipIdx' : sTip'.height = (stripSigs sc').length - 1 := hVc'.1 (blockAt_getLast hTipS')
  have hLenEq : (stripSigs sc).length - 1 - n = (stripSigs sc').length - 1 - n := by omega
  rw [← hLenEq] at hB'
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · obtain ⟨P, hPc, hPc'⟩ := horizon_shared_prefix hn hUniq hId hVc hVc'
      chainInRecord_left chainInRecord_right hTipS hTipS' hle
      (hBudgetFrom (sTip.slot + 1 - n) (by omega))
      (k := (stripSigs sc).length - 1 - n) (by omega)
    rw [hB] at hPc
    rw [hB'] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']
  · obtain ⟨P, hPc', hPc⟩ := horizon_shared_prefix hn hUniq hId hVc' hVc
      chainInRecord_right chainInRecord_left hTipS' hTipS hle
      (hBudgetFrom (sTip'.slot + 1 - n) (by omega))
      (k := (stripSigs sc).length - 1 - n) (by omega)
    rw [hB] at hPc
    rw [hB'] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']

/-- **Anchored membership form** (unequal tip heights): under the same
anchored budget, the `n`-deep block of the lower-tipped chain is a block
of the taller chain too, at least `n` deep there. The anchored analogue
of `keyrot_recent_tip_ancestor_mem`. -/
theorem keyrot_recent_tip_ancestor_mem_anchored
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig} {A : Block}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    (hA  : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    (hBudgetFrom : ∀ u, A.slot + 1 ≤ u + n →
      (badSlotsIn (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) u n).card
        ≤ maxByzantine n)
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block}
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B) :
    ∃ i', i' + n < (stripSigs sc').length ∧
      blockAt? (stripSigs sc') i' = some B := by
  have hVc  : ValidChain n (stripSigs sc) := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal;  exact (validChainK'_sound hVal.2).1
  have hVc' : ValidChain n (stripSigs sc') := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal'; exact (validChainK'_sound hVal'.2).1
  have hId : IdInjective (chainUnionRecord sc sc') :=
    idInjective_keyrot hHash
      (fun b hb => Or.inr (keyStealingSigned_of_mem hVal  hb))
      (fun b hb => Or.inr (keyStealingSigned_of_mem hVal' hb))
  have hUniq := honestSlotsUnique_keyrot_anchored hn hΔ
    (versionedUnforgeable_of_keyStealingEUFCMA hEUF) hA hA' hBudgetFrom hId hVal hVal'
    ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩
  have hAle : A.slot ≤ sTip.slot := by
    obtain ⟨i, hi⟩ := exists_blockAt_of_mem hA
    have hTipAt : blockAt? (stripSigs sc) ((stripSigs sc).length - 1) = some sTip :=
      blockAt_getLast hTipS
    have hiLen : i < (stripSigs sc).length := by
      unfold blockAt? at hi
      exact (List.getElem?_eq_some_iff.mp hi).1
    rcases Nat.lt_or_ge i ((stripSigs sc).length - 1) with h | h
    · exact Nat.le_of_lt (strictSlots_lt hVc.2.1 hi hTipAt h)
    · have hieq : i = (stripSigs sc).length - 1 := by omega
      rw [hieq, hTipAt] at hi
      injection hi with hi
      rw [hi]
  have hAle' : A.slot ≤ sTip'.slot := by
    obtain ⟨i, hi⟩ := exists_blockAt_of_mem hA'
    have hTipAt : blockAt? (stripSigs sc') ((stripSigs sc').length - 1) = some sTip' :=
      blockAt_getLast hTipS'
    have hiLen : i < (stripSigs sc').length := by
      unfold blockAt? at hi
      exact (List.getElem?_eq_some_iff.mp hi).1
    rcases Nat.lt_or_ge i ((stripSigs sc').length - 1) with h | h
    · exact Nat.le_of_lt (strictSlots_lt hVc'.2.1 hi hTipAt h)
    · have hieq : i = (stripSigs sc').length - 1 := by omega
      rw [hieq, hTipAt] at hi
      injection hi with hi
      rw [hi]
  have hTipIdx  : sTip.height  = (stripSigs sc ).length - 1 := hVc.1  (blockAt_getLast hTipS)
  have hTipIdx' : sTip'.height = (stripSigs sc').length - 1 := hVc'.1 (blockAt_getLast hTipS')
  have hkn' : ((stripSigs sc).length - 1 - n) + n < (stripSigs sc').length := by omega
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · obtain ⟨P, hPc, hPc'⟩ := horizon_shared_prefix hn hUniq hId hVc hVc'
      chainInRecord_left chainInRecord_right hTipS hTipS' hle
      (hBudgetFrom (sTip.slot + 1 - n) (by omega))
      (k := (stripSigs sc).length - 1 - n) (by omega)
    have hBP : B = P := by
      rw [hB] at hPc
      exact Option.some.inj hPc
    exact ⟨(stripSigs sc).length - 1 - n, hkn', by rw [hBP]; exact hPc'⟩
  · obtain ⟨P, hPc', hPc⟩ := horizon_shared_prefix hn hUniq hId hVc' hVc
      chainInRecord_right chainInRecord_left hTipS' hTipS hle
      (hBudgetFrom (sTip'.slot + 1 - n) (by omega))
      (k := (stripSigs sc).length - 1 - n) (by omega)
    have hBP : B = P := by
      rw [hB] at hPc
      exact Option.some.inj hPc
    exact ⟨(stripSigs sc).length - 1 - n, hkn', by rw [hBP]; exact hPc'⟩

/-- **Genesis-free tip-ancestor agreement, validator-discharged.** Same
conclusion as `keyrot_recent_tip_ancestor_agreement`, and from strictly fewer
hypotheses: no `hHead`/`hHead'`. Genesis-or-signed coverage is discharged from
the validator, exactly as that theorem does. -/
theorem keyrot_recent_tip_ancestor_agreement_horizon_of_valid
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    (hBudget : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc)))
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
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
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B' :=
  keyrot_recent_tip_ancestor_agreement_horizon hn hΔ hEUF hHash
    (fun b hb => Or.inr (keyStealingSigned_of_mem hVal  hb))
    (fun b hb => Or.inr (keyStealingSigned_of_mem hVal' hb))
    hBudget hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'


end MoltPetit.Model
