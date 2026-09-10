import Molt.ClientRule
import Molt.MaxSync
import MoltPetit.Model.KeyStealingTimed

/-!
# The timed theft layer, composed (paper §6.3, mode 1 — rollout item W3a)

Each wrapper below is literally the existing client theorem
(`client_refresh_rule`, `sync_rule`, `sync_rule_mem`, `max_sync_period`)
with its `hBudget` argument replaced by
`MoltPetit.Model.budget_of_reaction`, instantiated at that theorem's own
outward-facing window guard — no restatement of validity, recency, or
anchor plumbing. See `MoltPetit/Model/KeyStealingTimed.lean` for the
derivation itself and `docs/rollout/ROLLOUT_NOTES.md` §1 row W3a for the paper-facing
account.
-/

namespace Molt

/-- Paper-vocabulary re-export of the mode-1 reaction hypothesis; the same
reducible-abbrev idiom as `Molt.KeyStealingEUFCMA` (`Molt/Rotation.lean:108`). -/
abbrev Reacts := @MoltPetit.Model.Reacts

open Classical in
/-- Fresh Molt-named copy of `MoltPetit.Model.recentTheftProducersK`,
following the `Molt.badSlotsIn` precedent (`Molt/Assumptions.lean:33,81`)
for Finset-valued paper-vocabulary defs. -/
noncomputable def recentTheftProducersK (n d : Nat)
    (stolenAt : Nat → Nat → Nat → Prop) (u : Nat) : Finset Nat :=
  (Finset.range n).filter (fun i => ∃ j r, stolenAt i j r ∧ u < r + d)

theorem recentTheftProducersK_eq_core :
    recentTheftProducersK = MoltPetit.Model.recentTheftProducersK := rfl

/-- `client_refresh_rule` at a `Reacts`-derived budget. -/
theorem client_refresh_rule_timed
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop} {d : Nat}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig} {A : Block} {H : Nat}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented
      (MoltPetit.Model.stolenOf stolenAt) honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    (hA : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    (hFresh : now ≤ A.slot + H)
    {Rrent T : Nat}
    (hReacts : Reacts n Δconf d (stripSigs sc) stolenAt)
    (hRent : ∀ u, now < u + n + H → (badSlotsIn rented u n).card ≤ Rrent)
    (hTheft : ∀ u, now < u + n + H →
      (recentTheftProducersK n d stolenAt u).card ≤ T)
    (hRT : Rrent + T ≤ faultBudget n)
    (hVal : validSignedChainK' n Δconf ops registry sc = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong : n < (stripSigs sc).length) (hLong' : n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B' :=
  client_refresh_rule hn hΔ hEUF hHash hA hA' hFresh
    (MoltPetit.Model.budget_of_reaction (by omega) hReacts hRent hTheft hRT)
    hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'

/-- `sync_rule` at a `Reacts`-derived budget. -/
theorem sync_rule_timed
    {n : Nat} (hn : 1 ≤ n)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop} {d : Nat}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block}
    {sc sc' scPrev : SignedChain Sig} {A : Block}
    (hEUF : KeyStealingEUFCMA n n ops registry rented
      (MoltPetit.Model.stolenOf stolenAt) honestSigned now Δ)
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
    {Rrent T : Nat}
    (hReacts : Reacts n n d (stripSigs sc) stolenAt)
    (hRent : ∀ u, now < u + 5 * n → (badSlotsIn rented u n).card ≤ Rrent)
    (hTheft : ∀ u, now < u + 5 * n →
      (recentTheftProducersK n d stolenAt u).card ≤ T)
    (hRT : Rrent + T ≤ faultBudget n)
    (hVal : validSignedChainK' n n ops registry sc = true)
    (hVal' : validSignedChainK' n n ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong : n < (stripSigs sc).length) (hLong' : n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B' :=
  sync_rule hn hEUF hHash hVPrev hTipPrev hRecPrev hLongPrev hAnchor hCadence
    hA hA' (MoltPetit.Model.budget_of_reaction (by omega) hReacts hRent hTheft hRT)
    hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'

/-- `sync_rule_mem` at a `Reacts`-derived budget. -/
theorem sync_rule_mem_timed
    {n : Nat} (hn : 1 ≤ n)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop} {d : Nat}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block}
    {sc sc' scPrev : SignedChain Sig} {A : Block}
    (hEUF : KeyStealingEUFCMA n n ops registry rented
      (MoltPetit.Model.stolenOf stolenAt) honestSigned now Δ)
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
    {Rrent T : Nat}
    (hReacts : Reacts n n d (stripSigs sc) stolenAt)
    (hRent : ∀ u, now < u + 5 * n → (badSlotsIn rented u n).card ≤ Rrent)
    (hTheft : ∀ u, now < u + 5 * n →
      (recentTheftProducersK n d stolenAt u).card ≤ T)
    (hRT : Rrent + T ≤ faultBudget n)
    (hVal : validSignedChainK' n n ops registry sc = true)
    (hVal' : validSignedChainK' n n ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong : n < (stripSigs sc).length) (hLong' : n < (stripSigs sc').length)
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block}
    (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - n) = some B) :
    ∃ i', i' + n < (stripSigs sc').length ∧
      blockAt? (stripSigs sc') i' = some B :=
  sync_rule_mem hn hEUF hHash hVPrev hTipPrev hRecPrev hLongPrev hAnchor
    hCadence hA hA' (MoltPetit.Model.budget_of_reaction (by omega) hReacts hRent hTheft hRT)
    hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hLe hB

/-- `max_sync_period` at a `Reacts`-derived budget. -/
theorem max_sync_period_timed
    {n Δconf F : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop} {d : Nat}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block}
    {sc sc' scPrev : SignedChain Sig} {A : Block}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented
      (MoltPetit.Model.stolenOf stolenAt) honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    {t : Nat} {tipPrev : Block}
    (hVPrev : validSignedChainK' n Δconf ops registry scPrev = true)
    (hTipPrev : (stripSigs scPrev).getLast? = some tipPrev)
    (hRecPrev : t ≤ tipPrev.slot + n)
    (hLongPrev : n < (stripSigs scPrev).length)
    (hAnchor : blockAt? (stripSigs scPrev)
      ((stripSigs scPrev).length - 1 - n) = some A)
    (hCadence : now ≤ t + F)
    (hA : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    {Rrent T : Nat}
    (hReacts : Reacts n Δconf d (stripSigs sc) stolenAt)
    (hRent : ∀ u, now < u + F + 4 * n → (badSlotsIn rented u n).card ≤ Rrent)
    (hTheft : ∀ u, now < u + F + 4 * n →
      (recentTheftProducersK n d stolenAt u).card ≤ T)
    (hRT : Rrent + T ≤ faultBudget n)
    (hVal : validSignedChainK' n Δconf ops registry sc = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS : (stripSigs sc).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent : now ≤ sTip.slot + Δ) (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong : n < (stripSigs sc).length) (hLong' : n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B' :=
  max_sync_period hn hΔ hEUF hHash hVPrev hTipPrev hRecPrev hLongPrev hAnchor
    hCadence hA hA' (MoltPetit.Model.budget_of_reaction (by omega) hReacts hRent hTheft hRT)
    hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'

end Molt
