import Molt.SyncRuleTimed
import Molt.MaxSync
import MoltPetit.Model.KeyStealingSignatureTimed

/-!
# The tightened census, composed, plus the separation it buys (rollout W3b)

`max_sync_period_tight` below is this item's concrete cash-out of "larger
`F_max`": composed with a two-sided theft census (`Reacts` +
`NoTheftBackdating`), the sync-period guard's budget no longer accumulates
retroactively. `pacedStolenAt_safe_under_tight_unsafe_under_untimed` is the
machine-checked counterpart of the paper's own illustrative paced-theft
adversary: a witnessed schedule the tight census bounds by a fixed constant
for every window, that the SAME schedule provably defeats the untimed
(`Reacts`-free) census's budget at the very first window.
-/

namespace Molt

/-- Paper-vocabulary re-export of the time-aware signature surface; the same
reducible-abbrev idiom as `Molt.Reacts`. -/
abbrev NoTheftBackdating := @MoltPetit.Model.NoTheftBackdating

open Classical in
/-- Fresh Molt-named copy of `MoltPetit.Model.recentTheftProducersTight`,
following the `Molt.recentTheftProducersK` precedent. -/
noncomputable def recentTheftProducersTight (n d : Nat)
    (stolenAt : Nat → Nat → Nat → Prop) (u : Nat) : Finset Nat :=
  (Finset.range n).filter (fun i => ∃ j r, stolenAt i j r ∧ u < r + d ∧ r < u + n)

theorem recentTheftProducersTight_eq_core :
    recentTheftProducersTight = MoltPetit.Model.recentTheftProducersTight := rfl

/-- `max_sync_period` at a `Reacts` + `NoTheftBackdating`-derived (tight)
budget — the item's headline consumer, the sync-period parameter `F` this
item's title names. -/
theorem max_sync_period_tight
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
    (hNoBack : NoTheftBackdating n Δconf (stripSigs sc) stolenAt)
    (hRent : ∀ u, now < u + F + 4 * n → (badSlotsIn rented u n).card ≤ Rrent)
    (hTheft : ∀ u, now < u + F + 4 * n →
      (recentTheftProducersTight n d stolenAt u).card ≤ T)
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
    hCadence hA hA'
    (MoltPetit.Model.budget_of_reaction_tight (by omega) hReacts hNoBack hRent hTheft hRT)
    hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'

-- ===========================================================================
-- The separation: a witnessed paced-theft adversary
-- ===========================================================================

/-- **The witnessed separating adversary**: a paced multi-victim theft
schedule, one key every `P` slots, no two thefts ever concurrent. The
formal counterpart of the paper's own illustrative attacker ("an adversary
that quietly collects one key every couple of windows, each victim
rotating promptly so that no more than one is ever compromised at a
time"). -/
def pacedStolenAt (ι : Nat → Nat) (P : Nat) : Nat → Nat → Nat → Prop :=
  fun i j r => i = ι j ∧ r = j * P

/-- **The tight census stays bounded by `1`, for every window, independent
of `F`.** At most one `j` can satisfy the two-sided window test when
thefts are paced `P ≥ n + d` apart. -/
theorem recentTheftProducersTight_card_le_one_of_paced
    {n d P : Nat} (hP : n + d ≤ P) {ι : Nat → Nat} (u : Nat) :
    (recentTheftProducersTight n d (pacedStolenAt ι P) u).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  unfold recentTheftProducersTight at ha hb
  rw [Finset.mem_filter] at ha hb
  obtain ⟨-, j, r, ⟨hia, hrj⟩, hu1, hu2⟩ := ha
  obtain ⟨-, j', r', ⟨hib, hrj'⟩, hu1', hu2'⟩ := hb
  have hjj' : j = j' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hge : j' * P ≥ j * P + P := by
        have : j + 1 ≤ j' := hlt
        calc j' * P ≥ (j + 1) * P := Nat.mul_le_mul_right P this
          _ = j * P + P := by rw [Nat.succ_mul]
      omega
    · have hge : j * P ≥ j' * P + P := by
        have : j' + 1 ≤ j := hlt
        calc j * P ≥ (j' + 1) * P := Nat.mul_le_mul_right P this
          _ = j' * P + P := by rw [Nat.succ_mul]
      omega
  rw [hia, hib, hjj']

/-- **The SAME schedule defeats the untimed (`Reacts`-free) census's
budget at window `0`.** With `m > faultBudget n` distinct victims all
exposed inside `[0, n)`, `badKeyrot`'s window-`0` bad-slot count already
exceeds the fault budget — no instantiation of the plain, untimed budget
hypothesis covers it. -/
theorem pacedStolenAt_exceeds_untimed_budget
    {n Δconf P : Nat} (hn : 1 ≤ n)
    {c₀ : Chain} {ι : Nat → Nat} (hInj : Function.Injective ι)
    (hRange : ∀ k, k < n → ι k < n)
    (hFloor0 : ∀ k, k < n → ∀ s, s < n → inForce n Δconf c₀ (ι k) s = 0)
    {rented : ByzantineSlots} {m : Nat} (hm : faultBudget n < m) (hmn : m ≤ n) :
    ¬ (badSlotsIn
        (badKeyrot n Δconf rented (MoltPetit.Model.stolenOf (pacedStolenAt ι P)) c₀) 0 n).card
        ≤ faultBudget n := by
  have hP : ∀ i ∈ (Finset.range m).image ι, ∃ s, 0 ≤ s ∧ s < 0 + n ∧ producer n s = i ∧
      ∃ j, inForce n Δconf c₀ i s ≤ j ∧ MoltPetit.Model.stolenOf (pacedStolenAt ι P) i j := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    rw [Finset.mem_range] at hk
    have hkn : k < n := by omega
    obtain ⟨s, hlo, hhi, hprod⟩ := producer_slot_in_window hn (hRange k hkn) 0
    refine ⟨s, hlo, by omega, hprod, k, ?_, ?_⟩
    · rw [hFloor0 k hkn s (by omega)]
      omega
    · exact ⟨k * P, rfl, rfl⟩
  have hcard : ((Finset.range m).image ι).card = m := by
    rw [Finset.card_image_of_injOn hInj.injOn, Finset.card_range]
  exact no_budget_beyond (c₀ := c₀) (rented := rented) hP (by rw [hcard]; omega)

/-- **The separation, combined.** The paced schedule is safe under the
tight census — bounded by `1` regardless of `F` — while the same schedule
already defeats the untimed census's budget at the very first window.
Composing the left conjunct into a concrete `max_sync_period_tight`
instance (at `T := 1`) is a direct application, left to the caller. -/
theorem pacedStolenAt_safe_under_tight_unsafe_under_untimed
    {n Δconf P d : Nat} (hn : 1 ≤ n) (hP : n + d ≤ P)
    {c₀ : Chain} {ι : Nat → Nat} (hInj : Function.Injective ι)
    (hRange : ∀ k, k < n → ι k < n)
    (hFloor0 : ∀ k, k < n → ∀ s, s < n → inForce n Δconf c₀ (ι k) s = 0)
    (hReacts : Reacts n Δconf d c₀ (pacedStolenAt ι P))
    (hNoBack : NoTheftBackdating n Δconf c₀ (pacedStolenAt ι P))
    {rented : ByzantineSlots} {m : Nat} (hm : faultBudget n < m) (hmn : m ≤ n) :
    (∀ u, (recentTheftProducersTight n d (pacedStolenAt ι P) u).card ≤ 1) ∧
      ¬ (badSlotsIn
          (badKeyrot n Δconf rented (MoltPetit.Model.stolenOf (pacedStolenAt ι P)) c₀) 0 n).card
          ≤ faultBudget n :=
  ⟨fun u => recentTheftProducersTight_card_le_one_of_paced hP u,
    pacedStolenAt_exceeds_untimed_budget hn hInj hRange hFloor0 hm hmn⟩

end Molt
