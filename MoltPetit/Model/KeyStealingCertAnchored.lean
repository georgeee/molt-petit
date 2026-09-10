import MoltPetit.Model.KeyStealingCert
import MoltPetit.Model.KeyStealingHorizon

/-!
# MoltPetit — mode 1 anchored certificate agreement (rollout item W2)

`keyrot_recent_certified_suffix_agreement` (`KeyStealingCert.lean:583`) is
proved under the GLOBAL all-window budget — the lifetime assumption the
paper itself argues no deployment can defend under key theft. This module
carries the anchored, trailing-window form (already available at the
full-chain presentation via `keyrot_recent_tip_ancestor_agreement_anchored`,
`KeyStealingHorizon.lean:134`) to the certificate presentation.

**The anchor enters as membership in the exposed suffix**
(`hA : A ∈ s₁ :: srest`), lifted into the reconstructed full chain by
`List.mem_append_right`; it cannot usefully be located inside the certified
prefix, since the verifier cannot check that. The protocol reading: the
prover starts the suffix at or before the client's anchor — under the sync
rule, at most `4n` slots back, so the suffix stays `O(n)` blocks.

**The confirmed floors are read as `inForce` over the reconstructed chain**,
exactly as in the global certificate theorem — the budget is quantified over
`AttestedHistoryK` (every history the certificate could be attesting), now
restricted to windows ending after the anchor rather than every window.

**No existing theorem is modified.** The chain-level engine
`keyrot_deep_block_agreement_anchored` is new (the existing anchored core,
`keyrot_recent_tip_ancestor_agreement_anchored`, is tip-shaped and fixes its
hash-injectivity domain to `KeyStealingSigned`, a domain strictly larger than
the certificate path's `SignedDeclared`); its proof is the existing one
generalized to a generic `Signed` predicate and an arbitrary depth `k`
(`hLen`/`hLen'` in place of the tip-relative index), reusing
`slot_le_tip_of_mem` in place of the tip-shaped anchor-below-tip argument.
-/

namespace MoltPetit.Model

/-- **The generic-Signed, arbitrary-depth anchored engine.** Two
`validSignedChainK'`-accepted chains, recent, sharing an anchor `A`, with the
corruption budget consulted only on windows ending after `A.slot`, agree on
any block at a common index `k` that is `n`-deep in both. -/
theorem keyrot_deep_block_agreement_anchored
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    {Signed : Block → Prop} {G : Block} {sc sc' : SignedChain Sig} {A : Block}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective Signed G)
    (hSig : ∀ B ∈ stripSigs sc, B = G ∨ Signed B)
    (hSig' : ∀ B ∈ stripSigs sc', B = G ∨ Signed B)
    (hA : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    (hBudgetFrom : ∀ u, A.slot + 1 ≤ u + n →
      (badSlotsIn (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) u n).card
        ≤ maxByzantine n)
    (hVal : validSignedChainK' n Δconf ops registry sc = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    {k : Nat} {B B' : Block}
    (hB : blockAt? (stripSigs sc) k = some B)
    (hB' : blockAt? (stripSigs sc') k = some B')
    (hLen : k + n < (stripSigs sc).length)
    (hLen' : k + n < (stripSigs sc').length) :
    B = B' := by
  have hVc : ValidChain n (stripSigs sc) := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal
    exact (validChainK'_sound hVal.2).1
  have hVc' : ValidChain n (stripSigs sc') := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal'
    exact (validChainK'_sound hVal'.2).1
  have hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hHash hSig hSig'
  have hUniq := honestSlotsUnique_keyrot_anchored hn hΔ
    (versionedUnforgeable_of_keyStealingEUFCMA hEUF) hA hA' hBudgetFrom hId hVal hVal'
    ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩
  have hAle : A.slot ≤ sTip.slot := slot_le_tip_of_mem hVc.2.1 hTipS hA
  have hAle' : A.slot ≤ sTip'.slot := slot_le_tip_of_mem hVc'.2.1 hTipS' hA'
  rcases Nat.le_total sTip.slot sTip'.slot with hle | hle
  · obtain ⟨P, hPc, hPc'⟩ := horizon_shared_prefix hn hUniq hId hVc hVc'
      chainInRecord_left chainInRecord_right hTipS hTipS' hle
      (hBudgetFrom (sTip.slot + 1 - n) (by omega))
      (k := k) hLen
    rw [hB] at hPc
    rw [hB'] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']
  · obtain ⟨P, hPc', hPc⟩ := horizon_shared_prefix hn hUniq hId hVc' hVc
      chainInRecord_right chainInRecord_left hTipS' hTipS hle
      (hBudgetFrom (sTip'.slot + 1 - n) (by omega))
      (k := k) hLen'
    rw [hB] at hPc
    rw [hB'] at hPc'
    rw [Option.some.inj hPc, Option.some.inj hPc']

/-- Everything a certificate client checks about one (claim, floor snapshot,
suffix) triple before acting. Field shapes are byte-identical to the
hypotheses of `keyrot_recent_certified_suffix_agreement` /
`groundedCertK_suffix_history` (`KeyStealingCert.lean:462-475`). -/
structure AcceptedSuffixK (n : Nat) (Signed : Block → Prop) (G : Block)
    (cl : CertClaim) (fl : Nat → Nat) (s₁ : Block) (srest : Chain)
    (sTip : Block) : Prop where
  cert : GroundedCertK n Signed G cl fl
  tip : (s₁ :: srest).getLast? = some sTip
  link : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧
    s₁.prev = some cl.tipId
  links : linksOk (s₁ :: srest) = true
  dense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
    u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n
  mono : keyMonoFrom n fl (s₁ :: srest) = true
  signed : ∀ B ∈ s₁ :: srest, Signed B

/-- The reconstructed full pinned chain behind an accepted triple. -/
theorem AcceptedSuffixK.history {n : Nat} (Δconf : Nat) (hn : 1 ≤ n)
    {Signed : Block → Prop} {G : Block} {cl : CertClaim} {fl : Nat → Nat}
    {s₁ : Block} {srest : Chain} {sTip : Block}
    (h : AcceptedSuffixK n Signed G cl fl s₁ srest sTip) :
    ∃ c : Chain, validChainK' n Δconf (c ++ s₁ :: srest) = true ∧
      blockAt? (c ++ s₁ :: srest) 0 = some G ∧
      c.length = cl.tipHeight + 1 ∧ (∀ B ∈ c ++ s₁ :: srest, Signed B) :=
  groundedCertK_suffix_history Δconf hn h.cert h.tip h.link h.links h.dense
    h.mono h.signed

/-- **Mode 1's certificate-level safety under the trailing/anchored budget.**
Two verifying `GroundedCertK` certificates, each extended by a validated
recent suffix containing a client anchor `A`, agree on every block at the
same global height that is `n`-deep in both suffixes — with the corruption
budget consulted only on windows ending after `A.slot`, over every history
the first certificate could be attesting. -/
theorem keyrot_certified_suffix_agreement_anchored
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {A : Block}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    {cl cl' : CertClaim} {fl fl' : Nat → Nat}
    (hcl : GroundedCertK n (SignedDeclared n ops registry) G cl fl)
    (hcl' : GroundedCertK n (SignedDeclared n ops registry) G cl' fl')
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧
        s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hMono : keyMonoFrom n fl (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip'.slot + 1 → quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hMono' : keyMonoFrom n fl' (s₁' :: srest') = true)
    (hSigned' : ∀ B ∈ s₁' :: srest', SignedDeclared n ops registry B)
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hA : A ∈ s₁ :: srest) (hA' : A ∈ s₁' :: srest')
    (hBudgetFrom : ∀ c : Chain,
        AttestedHistoryK n Δconf ops registry G cl.tipHeight (s₁ :: srest) c →
        ∀ u, A.slot + 1 ≤ u + n →
          (badSlotsIn (badKeyrotOn n Δconf rented Stolen c) u n).card
            ≤ maxByzantine n)
    {i i' : Nat} {B B' : Block}
    (hB : blockAt? (s₁ :: srest) i = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep : i + n < (s₁ :: srest).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B' := by
  obtain ⟨c, hK, hHead, hLen, hCov⟩ :=
    groundedCertK_suffix_history Δconf hn hcl hTipS hLink hLinks hDense hMono hSigned
  obtain ⟨c', hK', hHead', hLen', hCov'⟩ :=
    groundedCertK_suffix_history Δconf hn hcl' hTipS' hLink' hLinks' hDense' hMono' hSigned'
  obtain ⟨sc, hstrip, hsigs⟩ :=
    exists_signedChain_of_covered (Sig := Sig) fun B hB => hCov B hB
  obtain ⟨sc', hstrip', hsigs'⟩ :=
    exists_signedChain_of_covered (Sig := Sig) fun B hB => hCov' B hB
  have hVal : validSignedChainK' n Δconf ops registry sc = true := by
    rw [validSignedChainK', Bool.and_eq_true]
    exact ⟨hsigs, by rw [hstrip]; exact hK⟩
  have hVal' : validSignedChainK' n Δconf ops registry sc' = true := by
    rw [validSignedChainK', Bool.and_eq_true]
    exact ⟨hsigs', by rw [hstrip']; exact hK'⟩
  have hBud : ∀ u, A.slot + 1 ≤ u + n →
      (badSlotsIn (badKeyrotOn n Δconf rented Stolen (stripSigs sc)) u n).card
        ≤ maxByzantine n := by
    rw [hstrip]
    exact hBudgetFrom _ ⟨hK, hHead, hCov, c, rfl, hLen⟩
  have hAsc : A ∈ stripSigs sc := by
    rw [hstrip]; exact List.mem_append_right c hA
  have hAsc' : A ∈ stripSigs sc' := by
    rw [hstrip']; exact List.mem_append_right c' hA'
  have hfullTip : (c ++ s₁ :: srest).getLast? = some sTip := by
    rw [List.getLast?_append, hTipS]; rfl
  have hfullTip' : (c' ++ s₁' :: srest').getLast? = some sTip' := by
    rw [List.getLast?_append, hTipS']; rfl
  have hBfull : blockAt? (c ++ s₁ :: srest) (c.length + i) = some B := by
    unfold blockAt? at hB ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hB
  have hB'full : blockAt? (c' ++ s₁' :: srest') (c'.length + i') = some B' := by
    unfold blockAt? at hB' ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hB'
  have hkEq : c'.length + i' = c.length + i := by omega
  rw [hkEq] at hB'full
  have hSig : ∀ b ∈ stripSigs sc, b = G ∨ SignedDeclared n ops registry b := by
    rw [hstrip]; exact fun b hb => Or.inr (hCov b hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ SignedDeclared n ops registry b := by
    rw [hstrip']; exact fun b hb => Or.inr (hCov' b hb)
  exact keyrot_deep_block_agreement_anchored hn hΔ hEUF hHash hSig hSig' hAsc hAsc'
    hBud hVal hVal'
    (by rw [hstrip]; exact hfullTip) (by rw [hstrip']; exact hfullTip')
    hRecent hRecent' (k := c.length + i)
    (by rw [hstrip]; exact hBfull) (by rw [hstrip']; exact hB'full)
    (by rw [hstrip, List.length_append]; omega)
    (by rw [hstrip', List.length_append]; omega)

end MoltPetit.Model
