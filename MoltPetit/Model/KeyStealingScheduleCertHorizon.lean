import MoltPetit.Model.KeyStealingScheduleHorizon
import MoltPetit.Model.KeyStealingScheduleCert

/-!
# Mode 2 certificates under the horizon-scoped budget

THE STATEMENT OF `sched_recent_certified_suffix_agreement_horizon` IS FIXED. Its
exact type is pinned by `Molt/AxiomsSchedCertHorizon.lean`; prove it, do not
change it. It is `sched_recent_certified_suffix_agreement` with the global
budget replaced by `ByzantineBoundedFrom H n` plus the two horizon side
conditions of `sched_recent_tip_ancestor_agreement_horizon`.
-/

namespace MoltPetit.Model

/-- **Certificate-level mode-2 safety under a horizon-scoped budget.** -/
theorem sched_recent_certified_suffix_agreement_horizon
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {Formed : Block → Prop}
    (hUnf : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedFormed n ops registry Formed) G)
    {H : Nat}
    (hBudget : ByzantineBoundedFrom H n (badSched n schedule rented Stolen))
    {cl cl' : CertClaim}
    (hcl  : GroundedCertSched n schedule (SignedFormed n ops registry Formed) G cl)
    (hcl' : GroundedCertSched n schedule (SignedFormed n ops registry Formed) G cl')
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hTipS  : (s₁  :: srest ).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink  : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧
        s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hPinS : schedPinned schedule (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedFormed n ops registry Formed B)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip'.slot + 1 → quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hPinS' : schedPinned schedule (s₁' :: srest') = true)
    (hSigned' : ∀ B ∈ s₁' :: srest', SignedFormed n ops registry Formed B)
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hH  : H + n ≤ sTip.slot  + 1)
    (hH' : H + n ≤ sTip'.slot + 1)
    {i i' : Nat} {B B' : Block}
    (hB  : blockAt? (s₁  :: srest ) i  = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep  : i  + n < (s₁  :: srest ).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B' := by
  -- reconstruct the two full core-accepted chains
  obtain ⟨c, hV, hPin, hHead, hLen, hCov⟩ :=
    groundedCertSched_suffix_history hn hcl hTipS hLink hLinks hDense hPinS hSigned
  obtain ⟨c', hV', hPin', hHead', hLen', hCov'⟩ :=
    groundedCertSched_suffix_history hn hcl' hTipS' hLink' hLinks' hDense' hPinS' hSigned'
  -- materialize the signed chains
  obtain ⟨sc, hstrip, hsigs⟩ :=
    exists_signedChain_of_covered (Sig := Sig) fun B hB => (hCov B hB).1
  obtain ⟨sc', hstrip', hsigs'⟩ :=
    exists_signedChain_of_covered (Sig := Sig) fun B hB => (hCov' B hB).1
  have hVal : validSignedChainSchedCore n schedule ops registry sc = true := by
    rw [validSignedChainSchedCore, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨hsigs, by rw [hstrip]; exact hV⟩, by rw [hstrip]; exact hPin⟩
  have hVal' : validSignedChainSchedCore n schedule ops registry sc' = true := by
    rw [validSignedChainSchedCore, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨hsigs', by rw [hstrip']; exact hV'⟩, by rw [hstrip']; exact hPin'⟩
  -- recent tips of the full chains
  have hfullTip : (stripSigs sc).getLast? = some sTip := by
    rw [hstrip, List.getLast?_append, hTipS]
    rfl
  have hfullTip' : (stripSigs sc').getLast? = some sTip' := by
    rw [hstrip', List.getLast?_append, hTipS']
    rfl
  -- locate the blocks at their global heights
  have hBfull : blockAt? (stripSigs sc) (c.length + i) = some B := by
    rw [hstrip]
    unfold blockAt? at hB ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hB
  have hB'full : blockAt? (stripSigs sc') (c'.length + i') = some B' := by
    rw [hstrip']
    unfold blockAt? at hB' ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hB'
  have hkEq : c'.length + i' = c.length + i := by omega
  rw [hkEq] at hB'full
  have hVc  : ValidChain n (stripSigs sc)  := validChain_of_validSignedChainSchedCore hVal
  have hVc' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSchedCore hVal'
  have hSig  : ∀ b ∈ stripSigs sc,  b = G ∨ SignedFormed n ops registry Formed b := by
    rw [hstrip]; exact fun b hb => Or.inr (hCov b hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ SignedFormed n ops registry Formed b := by
    rw [hstrip']; exact fun b hb => Or.inr (hCov' b hb)
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · have hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hHash hSig hSig'
    have hUniq := honestSlotsUnique_schedCore hUnf hVal hVal'
      ⟨sTip, hfullTip, hRecent⟩ ⟨sTip', hfullTip', hRecent'⟩
    obtain ⟨P, hPc, hPc'⟩ := horizon_shared_prefix hn hUniq hId hVc hVc'
      chainInRecord_left chainInRecord_right hfullTip hfullTip' hle
      (hBudget _ (by omega)) (k := c.length + i)
      (by rw [hstrip, List.length_append]; omega)
    rw [hBfull] at hPc
    rw [hB'full] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']
  · have hId : IdInjective (chainUnionRecord sc' sc) := idInjective_keyrot hHash hSig' hSig
    have hUniq := honestSlotsUnique_schedCore hUnf hVal' hVal
      ⟨sTip', hfullTip', hRecent'⟩ ⟨sTip, hfullTip, hRecent⟩
    obtain ⟨P, hPc', hPc⟩ := horizon_shared_prefix hn hUniq hId hVc' hVc
      chainInRecord_left chainInRecord_right hfullTip' hfullTip hle
      (hBudget _ (by omega)) (k := c.length + i)
      (by rw [hstrip', List.length_append]; omega)
    rw [hBfull] at hPc
    rw [hB'full] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']

/-- Paper: cited in sec:rotation. Like `sched_recent_certified_suffix_agreement_horizon`,
but for any histories behind the two certificates: every block at least n below the tip of the
full chain, certified prefix included. -/
theorem sched_recent_certified_history_agreement_horizon
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {Formed : Block → Prop}
    (hUnf : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedFormed n ops registry Formed) G)
    {H : Nat}
    (hBudget : ByzantineBoundedFrom H n (badSched n schedule rented Stolen))
    {cl cl' : CertClaim}
    {c : Chain}
    (hc : GroundedHistorySched n schedule (SignedFormed n ops registry Formed) G cl c)
    {c' : Chain}
    (hc' : GroundedHistorySched n schedule (SignedFormed n ops registry Formed) G cl' c')
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧
        s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hPinS : schedPinned schedule (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedFormed n ops registry Formed B)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip'.slot + 1 → quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hPinS' : schedPinned schedule (s₁' :: srest') = true)
    (hSigned' : ∀ B ∈ s₁' :: srest', SignedFormed n ops registry Formed B)
    (hRecent : now ≤ sTip.slot + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hH : H + n ≤ sTip.slot + 1)
    (hH' : H + n ≤ sTip'.slot + 1)
    {k : Nat}
    (hDeep : k + n < (c ++ s₁ :: srest).length)
    (hDeep' : k + n < (c' ++ s₁' :: srest').length) :
    blockAt? (c ++ s₁ :: srest) k = blockAt? (c' ++ s₁' :: srest') k := by
  obtain ⟨hV, hPin, hHead, hLen, hCov⟩ :=
    groundedHistorySched_suffix_history hn hc hTipS hLink hLinks hDense hPinS hSigned
  obtain ⟨hV', hPin', hHead', hLen', hCov'⟩ :=
    groundedHistorySched_suffix_history hn hc' hTipS' hLink' hLinks' hDense' hPinS' hSigned'
  obtain ⟨sc, hstrip, hsigs⟩ :=
    exists_signedChain_of_covered (Sig := Sig) fun B hB => (hCov B hB).1
  obtain ⟨sc', hstrip', hsigs'⟩ :=
    exists_signedChain_of_covered (Sig := Sig) fun B hB => (hCov' B hB).1
  have hVal : validSignedChainSchedCore n schedule ops registry sc = true := by
    rw [validSignedChainSchedCore, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨hsigs, by rw [hstrip]; exact hV⟩, by rw [hstrip]; exact hPin⟩
  have hVal' : validSignedChainSchedCore n schedule ops registry sc' = true := by
    rw [validSignedChainSchedCore, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨hsigs', by rw [hstrip']; exact hV'⟩, by rw [hstrip']; exact hPin'⟩
  have hfullTip : (stripSigs sc).getLast? = some sTip := by
    rw [hstrip, List.getLast?_append, hTipS]
    rfl
  have hfullTip' : (stripSigs sc').getLast? = some sTip' := by
    rw [hstrip', List.getLast?_append, hTipS']
    rfl
  have hk : k < (stripSigs sc).length := by rw [hstrip]; omega
  have hk' : k < (stripSigs sc').length := by rw [hstrip']; omega
  obtain ⟨B, hB⟩ : ∃ B, blockAt? (stripSigs sc) k = some B :=
    ⟨(stripSigs sc)[k]'hk, List.getElem?_eq_getElem hk⟩
  obtain ⟨B', hB'⟩ : ∃ B', blockAt? (stripSigs sc') k = some B' :=
    ⟨(stripSigs sc')[k]'hk', List.getElem?_eq_getElem hk'⟩
  have hVc : ValidChain n (stripSigs sc) := validChain_of_validSignedChainSchedCore hVal
  have hVc' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSchedCore hVal'
  have hSig : ∀ b ∈ stripSigs sc, b = G ∨ SignedFormed n ops registry Formed b := by
    rw [hstrip]; exact fun b hb => Or.inr (hCov b hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ SignedFormed n ops registry Formed b := by
    rw [hstrip']; exact fun b hb => Or.inr (hCov' b hb)
  have heq : B = B' := by
    rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
    · have hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hHash hSig hSig'
      have hUniq := honestSlotsUnique_schedCore hUnf hVal hVal'
        ⟨sTip, hfullTip, hRecent⟩ ⟨sTip', hfullTip', hRecent'⟩
      obtain ⟨P, hPc, hPc'⟩ := horizon_shared_prefix hn hUniq hId hVc hVc'
        chainInRecord_left chainInRecord_right hfullTip hfullTip' hle
        (hBudget _ (by omega)) (k := k)
        (by rw [hstrip]; exact hDeep)
      rw [hB] at hPc
      rw [hB'] at hPc'
      obtain rfl := Option.some.inj hPc
      obtain rfl := Option.some.inj hPc'
      rfl
    · have hId : IdInjective (chainUnionRecord sc' sc) := idInjective_keyrot hHash hSig' hSig
      have hUniq := honestSlotsUnique_schedCore hUnf hVal' hVal
        ⟨sTip', hfullTip', hRecent'⟩ ⟨sTip, hfullTip, hRecent⟩
      obtain ⟨P, hPc', hPc⟩ := horizon_shared_prefix hn hUniq hId hVc' hVc
        chainInRecord_left chainInRecord_right hfullTip' hfullTip hle
        (hBudget _ (by omega)) (k := k)
        (by rw [hstrip']; exact hDeep')
      rw [hB] at hPc
      rw [hB'] at hPc'
      obtain rfl := Option.some.inj hPc
      obtain rfl := Option.some.inj hPc'
      rfl
  rw [hstrip] at hB
  rw [hstrip'] at hB'
  rw [hB, hB', heq]

end MoltPetit.Model
