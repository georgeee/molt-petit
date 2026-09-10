import Molt.ClientRule
import MoltPetit.Model.KeyStealingCertAnchored

/-!
# The client refresh rule at the certificate presentation (rollout item W2)

Certificate-level twins of `client_refresh_rule` / `stay_recent_client_safe` /
`sync_rule` (`Molt/Rotation.lean`, `Molt/ClientRule.lean`): each is the
existing theorem's body, with the accepted chains supplied as certificate +
suffix bundles (`AcceptedSuffixK`) reconstructed via
`MoltPetit.Model.keyrot_certified_suffix_agreement_anchored` in place of the
full-chain anchored engine. See `MoltPetit/Model/KeyStealingCertAnchored.lean`
and `docs/rollout/ROLLOUT_NOTES.md` §1 row W2.

**The anchor's certificate-side contract**: the anchor must lie in the
exposed suffix, not merely the certified prefix — the verifier cannot check
prefix membership. Under `sync_rule`'s cadence the anchor is under `4n`
slots old, so the required suffix stays `O(n)` blocks; this is the same
reach a full-chain client needs.
-/

namespace Molt

/-- Paper-namespace re-export of `AcceptedSuffixK` — the same term, no
bridge needed. -/
abbrev AcceptedSuffixK := @MoltPetit.Model.AcceptedSuffixK

/-- Paper-namespace re-export of `AttestedHistoryK`. -/
abbrev AttestedHistoryK := @MoltPetit.Model.AttestedHistoryK

/-- Supersedes the "future work at this presentation" remark on
`Molt.keyrot_recent_certified_suffix_agreement` (`Molt/Rotation.lean:303-307`)
for mode 1's anchored/trailing form specifically; the global-budget
certificate theorem is unaffected and unchanged. -/
alias keyrot_certified_suffix_agreement_anchored :=
  MoltPetit.Model.keyrot_certified_suffix_agreement_anchored

/-- `client_refresh_rule` at the certificate presentation: pick a horizon
`H`; a certificate client that refreshes with an anchor no older than `H`
slots is safe with the budget consulted only on windows overlapping the
trailing `H + n` slots, over every history the first certificate could be
attesting. -/
theorem cert_client_refresh_rule
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block} {A : Block} {H : Nat}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    {cl cl' : CertClaim} {fl fl' : Nat → Nat}
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hAcc : AcceptedSuffixK n (SignedDeclared n ops registry) G cl fl s₁ srest sTip)
    (hAcc' : AcceptedSuffixK n (SignedDeclared n ops registry) G cl' fl' s₁' srest' sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hA : A ∈ s₁ :: srest) (hA' : A ∈ s₁' :: srest')
    (hFresh : now ≤ A.slot + H)
    (hBudget : ∀ c : Chain,
        AttestedHistoryK n Δconf ops registry G cl.tipHeight (s₁ :: srest) c →
        ∀ u, now < u + n + H →
          (badSlotsIn (badKeyrot n Δconf rented Stolen c) u n).card ≤ faultBudget n)
    {i i' : Nat} {B B' : Block}
    (hB : blockAt? (s₁ :: srest) i = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep : i + n < (s₁ :: srest).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B' :=
  MoltPetit.Model.keyrot_certified_suffix_agreement_anchored hn hΔ hEUF hHash
    hAcc.cert hAcc'.cert hAcc.tip hAcc'.tip hAcc.link hAcc.links hAcc.dense
    hAcc.mono hAcc.signed hAcc'.link hAcc'.links hAcc'.dense hAcc'.mono
    hAcc'.signed hRecent hRecent' hA hA'
    (fun c hc u hu => hBudget c hc u (by omega))
    hB hB' hHeight hDeep hDeep'

/-- `stay_recent_client_safe` at the certificate presentation: the previous
sync is itself a certificate verification (`hAccPrev`), and its `n`-deep
block is the exposed anchor of the current suffixes. Derives the anchor's
age (`< 4n`) from `deep_block_span` applied to the reconstructed previous
chain, exactly as the full-chain form does. -/
theorem cert_stay_recent_client_safe
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block} {A : Block}
    {clP : CertClaim} {flP : Nat → Nat} {s₁P : Block} {srestP : Chain}
    {tipPrev : Block} {t : Nat}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    (hAccPrev : AcceptedSuffixK n (SignedDeclared n ops registry) G clP flP
      s₁P srestP tipPrev)
    (hRecPrev : t ≤ tipPrev.slot + n)
    (hLongPrev : n < (s₁P :: srestP).length)
    (hAnchor : blockAt? (s₁P :: srestP) ((s₁P :: srestP).length - 1 - n) = some A)
    (hCadence : now ≤ t + n)
    {cl cl' : CertClaim} {fl fl' : Nat → Nat}
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hAcc : AcceptedSuffixK n (SignedDeclared n ops registry) G cl fl s₁ srest sTip)
    (hAcc' : AcceptedSuffixK n (SignedDeclared n ops registry) G cl' fl' s₁' srest' sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hA : A ∈ s₁ :: srest) (hA' : A ∈ s₁' :: srest')
    (hBudget : ∀ c : Chain,
        AttestedHistoryK n Δconf ops registry G cl.tipHeight (s₁ :: srest) c →
        ∀ u, now < u + 5 * n →
          (badSlotsIn (badKeyrot n Δconf rented Stolen c) u n).card ≤ faultBudget n)
    {i i' : Nat} {B B' : Block}
    (hB : blockAt? (s₁ :: srest) i = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep : i + n < (s₁ :: srest).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B' := by
  obtain ⟨cP, hKP, -, hLenP, -⟩ := hAccPrev.history Δconf hn
  have hVcP : MoltPetit.Model.ValidChain n (cP ++ s₁P :: srestP) :=
    (MoltPetit.Model.validChainK'_sound hKP).1
  have hfullTip : (cP ++ s₁P :: srestP).getLast? = some tipPrev := by
    rw [List.getLast?_append, hAccPrev.tip]; rfl
  have hTipIdx := MoltPetit.Model.blockAt_getLast hfullTip
  have hAfull : blockAt? (cP ++ s₁P :: srestP)
      (cP.length + ((s₁P :: srestP).length - 1 - n)) = some A := by
    unfold blockAt? at hAnchor ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hAnchor
  have hidx : cP.length + ((s₁P :: srestP).length - 1 - n) + n
      = (cP ++ s₁P :: srestP).length - 1 := by
    rw [List.length_append]; omega
  have hspan : tipPrev.slot < A.slot + 2 * n :=
    deep_block_span hn hVcP hAfull (by rw [hidx]; exact hTipIdx)
  have hFresh : now ≤ A.slot + (4 * n - 1) := by omega
  exact cert_client_refresh_rule hn hΔ hEUF hHash hAcc hAcc' hRecent hRecent'
    hA hA' hFresh (fun c hc u hu => hBudget c hc u (by omega)) hB hB' hHeight
    hDeep hDeep'

/-- `sync_rule` at the certificate presentation: the confirmation depth fixed
at its provable minimum `n`. -/
theorem cert_sync_rule
    {n : Nat} (hn : 1 ≤ n)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block} {A : Block}
    {clP : CertClaim} {flP : Nat → Nat} {s₁P : Block} {srestP : Chain}
    {tipPrev : Block} {t : Nat}
    (hEUF : KeyStealingEUFCMA n n ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    (hAccPrev : AcceptedSuffixK n (SignedDeclared n ops registry) G clP flP
      s₁P srestP tipPrev)
    (hRecPrev : t ≤ tipPrev.slot + n)
    (hLongPrev : n < (s₁P :: srestP).length)
    (hAnchor : blockAt? (s₁P :: srestP) ((s₁P :: srestP).length - 1 - n) = some A)
    (hCadence : now ≤ t + n)
    {cl cl' : CertClaim} {fl fl' : Nat → Nat}
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hAcc : AcceptedSuffixK n (SignedDeclared n ops registry) G cl fl s₁ srest sTip)
    (hAcc' : AcceptedSuffixK n (SignedDeclared n ops registry) G cl' fl' s₁' srest' sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hA : A ∈ s₁ :: srest) (hA' : A ∈ s₁' :: srest')
    (hBudget : ∀ c : Chain,
        AttestedHistoryK n n ops registry G cl.tipHeight (s₁ :: srest) c →
        ∀ u, now < u + 5 * n →
          (badSlotsIn (badKeyrot n n rented Stolen c) u n).card ≤ faultBudget n)
    {i i' : Nat} {B B' : Block}
    (hB : blockAt? (s₁ :: srest) i = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep : i + n < (s₁ :: srest).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B' :=
  cert_stay_recent_client_safe hn (Nat.le_refl n) hEUF hHash hAccPrev hRecPrev
    hLongPrev hAnchor hCadence hAcc hAcc' hRecent hRecent' hA hA' hBudget hB
    hB' hHeight hDeep hDeep'

/-- `max_sync_period` at the certificate presentation: fully parametric in
the sync period `F`. -/
theorem cert_max_sync_period
    {n Δconf F : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block} {A : Block}
    {clP : CertClaim} {flP : Nat → Nat} {s₁P : Block} {srestP : Chain}
    {tipPrev : Block} {t : Nat}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    (hAccPrev : AcceptedSuffixK n (SignedDeclared n ops registry) G clP flP
      s₁P srestP tipPrev)
    (hRecPrev : t ≤ tipPrev.slot + n)
    (hLongPrev : n < (s₁P :: srestP).length)
    (hAnchor : blockAt? (s₁P :: srestP) ((s₁P :: srestP).length - 1 - n) = some A)
    (hCadence : now ≤ t + F)
    {cl cl' : CertClaim} {fl fl' : Nat → Nat}
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hAcc : AcceptedSuffixK n (SignedDeclared n ops registry) G cl fl s₁ srest sTip)
    (hAcc' : AcceptedSuffixK n (SignedDeclared n ops registry) G cl' fl' s₁' srest' sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hA : A ∈ s₁ :: srest) (hA' : A ∈ s₁' :: srest')
    (hBudget : ∀ c : Chain,
        AttestedHistoryK n Δconf ops registry G cl.tipHeight (s₁ :: srest) c →
        ∀ u, now < u + F + 4 * n →
          (badSlotsIn (badKeyrot n Δconf rented Stolen c) u n).card ≤ faultBudget n)
    {i i' : Nat} {B B' : Block}
    (hB : blockAt? (s₁ :: srest) i = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep : i + n < (s₁ :: srest).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B' := by
  obtain ⟨cP, hKP, -, hLenP, -⟩ := hAccPrev.history Δconf hn
  have hVcP : MoltPetit.Model.ValidChain n (cP ++ s₁P :: srestP) :=
    (MoltPetit.Model.validChainK'_sound hKP).1
  have hfullTip : (cP ++ s₁P :: srestP).getLast? = some tipPrev := by
    rw [List.getLast?_append, hAccPrev.tip]; rfl
  have hTipIdx := MoltPetit.Model.blockAt_getLast hfullTip
  have hAfull : blockAt? (cP ++ s₁P :: srestP)
      (cP.length + ((s₁P :: srestP).length - 1 - n)) = some A := by
    unfold blockAt? at hAnchor ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hAnchor
  have hidx : cP.length + ((s₁P :: srestP).length - 1 - n) + n
      = (cP ++ s₁P :: srestP).length - 1 := by
    rw [List.length_append]; omega
  have hspan : tipPrev.slot < A.slot + 2 * n :=
    deep_block_span hn hVcP hAfull (by rw [hidx]; exact hTipIdx)
  have hFresh : now ≤ A.slot + (F + 3 * n - 1) := by omega
  exact cert_client_refresh_rule hn hΔ hEUF hHash hAcc hAcc' hRecent hRecent'
    hA hA' hFresh (fun c hc u hu => hBudget c hc u (by omega)) hB hB' hHeight
    hDeep hDeep'

end Molt
