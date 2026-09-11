import Molt.SyncRuleTimed
import Molt.MaxSync
import MoltPetit.Model.KeyStealingSignatureTimed

/-!
# The tightened census, composed, plus the separation it buys (rollout W3b)

`max_sync_period_tight` composes the two-sided theft census (`Reacts` +
`NoTheftBackdating`) into the sync-period rule. What that buys, stated
precisely enough to cite:

* `MoltPetit.Model.theft_exposure_window` — a theft at real slot `r` exposes
  chain-slots only in `[r, r + d)`. Fixed width, independent of where the
  window sits in the run. This is "the census is no longer retroactive".
* `paced_tight_census_bound_all_F` — for a paced adversary the census
  hypothesis of `max_sync_period_tight` is discharged at `T := 1` for EVERY
  `F`. This is the formal residue of "`F_max` rises": the census, which
  under the untimed reading grew with the stretch being checked, no longer
  constrains `F` at all. It is *not* a proof that a larger `F` is safe on
  its own — rent still has to be bounded over the same stretch.
* `pacedStolenAt_safe_under_tight_unsafe_under_untimed`, and its
  hypothesis-free instance `paced_separation_witnessed` — the same paced
  schedule has a tight census of `1` at every window while its untimed
  bad-slot count at window `0` already exceeds the fault budget.

**What this does NOT show, and a correction.** There is no execution in
which `Reacts` + `NoTheftBackdating` hold and the untimed budget
nevertheless fails: `paced_budget_holds_under_timing` proves the opposite,
that under those hypotheses the paced adversary satisfies the old budget
too. An earlier version of the combined separation theorem carried
`Reacts`/`NoTheftBackdating` as hypotheses alongside `hFloor0`, which made
it VACUOUS (those three are jointly contradictory — see that theorem's own
docstring). The honest reading is that the timed route changes which
hypotheses a deployment can *defend* — a fixed per-window concurrency bound
instead of a per-stretch total — not which executions are safe.
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

/-- **The separation, combined.** For one and the same paced schedule: the
tight census is bounded by `1` at every window — no `c₀`, no timing
hypotheses, and in particular no dependence on the sync period — while the
untimed bad-slot count at window `0` already exceeds the fault budget on a
chain whose floors have not yet risen.

The two conjuncts are deliberately conditioned differently, and that is the
whole content: the left one needs nothing but the pacing `n + d ≤ P`, the
right one needs only `hFloor0`, and `hFloor0` is satisfiable (the empty
chain gives floors `0`), so the statement is not vacuous —
`paced_separation_witnessed` below discharges every hypothesis at concrete
parameters.

**This theorem deliberately does NOT assume `Reacts`/`NoTheftBackdating`.**
An earlier version carried them, meaning to record "the paced schedule is
one the tight route legitimately applies to"; that was a mistake, because
those hypotheses together with `hFloor0` are *contradictory* (see
`paced_budget_holds_under_timing` for why, in positive form). A separation
of the shape "the timed hypotheses hold and the untimed budget still fails"
does not exist — which is a fact about the timed hypotheses being strong
enough, not a defect. -/
theorem pacedStolenAt_safe_under_tight_unsafe_under_untimed
    {n Δconf P d : Nat} (hn : 1 ≤ n) (hP : n + d ≤ P)
    {c₀ : Chain} {ι : Nat → Nat} (hInj : Function.Injective ι)
    (hRange : ∀ k, k < n → ι k < n)
    (hFloor0 : ∀ k, k < n → ∀ s, s < n → inForce n Δconf c₀ (ι k) s = 0)
    {rented : ByzantineSlots} {m : Nat} (hm : faultBudget n < m) (hmn : m ≤ n) :
    (∀ u, (recentTheftProducersTight n d (pacedStolenAt ι P) u).card ≤ 1) ∧
      ¬ (badSlotsIn
          (badKeyrot n Δconf rented (MoltPetit.Model.stolenOf (pacedStolenAt ι P)) c₀) 0 n).card
          ≤ faultBudget n :=
  ⟨fun u => recentTheftProducersTight_card_le_one_of_paced hP u,
    pacedStolenAt_exceeds_untimed_budget hn hInj hRange hFloor0 hm hmn⟩

/-- **The separation, fully witnessed — no hypotheses at all.** At `n = 4`,
`d = 1`, `P = 5`, victims `ι = id`, and the empty witness chain: the tight
census is `≤ 1` at every window, while the untimed bad-slot count at window
`0` exceeds `faultBudget 4 = 1` outright. Closes the "hypotheses stated but
never shown jointly satisfiable" gap the design left open. -/
theorem paced_separation_witnessed :
    (∀ u, (recentTheftProducersTight 4 1 (pacedStolenAt id 5) u).card ≤ 1) ∧
      ¬ ((badSlotsIn (badKeyrot 4 0 (fun _ => False)
            (MoltPetit.Model.stolenOf (pacedStolenAt id 5)) []) 0 4).card ≤ faultBudget 4) := by
  refine ⟨fun u => recentTheftProducersTight_card_le_one_of_paced (by omega) u, ?_⟩
  exact pacedStolenAt_exceeds_untimed_budget (n := 4) (Δconf := 0) (P := 5)
    (by omega) Function.injective_id (fun k hk => hk)
    (fun _ _ _ _ => rfl) (m := 2) (by decide) (by omega)

-- ===========================================================================
-- What the timed hypotheses actually rule out
-- ===========================================================================

/-- **Under the timed hypotheses the UNTIMED census is already bounded.**
For a paced schedule, `Reacts` + `NoTheftBackdating` confine each theft's
exposure to `[r, r + d)` (`theft_exposure_window`), and pacing `n + d ≤ P`
puts at most one such interval in any window — so the *cumulative*
`exposedProducers` census, the one the untimed budget reads, is itself
`≤ 1` everywhere. -/
theorem exposedProducers_card_le_one_of_paced
    {n Δconf d P : Nat} (hn : 0 < n) (hP : n + d ≤ P) {ι : Nat → Nat} {c₀ : Chain}
    (hReacts : Reacts n Δconf d c₀ (pacedStolenAt ι P))
    (hNoBack : NoTheftBackdating n Δconf c₀ (pacedStolenAt ι P))
    (u : Nat) :
    (MoltPetit.Model.exposedProducers n Δconf
      (MoltPetit.Model.stolenOf (pacedStolenAt ι P)) c₀ u).card ≤ 1 := by
  have hsub := MoltPetit.Model.exposedProducers_subset_recentTheftTight hn hReacts hNoBack u
  have hone := recentTheftProducersTight_card_le_one_of_paced
    (n := n) (d := d) (P := P) (ι := ι) hP u
  rw [recentTheftProducersTight_eq_core] at hone
  exact le_trans (Finset.card_le_card hsub) hone

/-- **Why no "both hypotheses hold and the untimed budget fails" separation
exists.** Under `Reacts` + `NoTheftBackdating`, the paced adversary does not
break the untimed budget either — it *satisfies* it, for any rent rate
leaving one seat of headroom. So the timed hypotheses do not merely make the
budget easier to attest: for this adversary family they make the old budget
true as well. The gain the timed route buys is therefore about which
hypotheses a deployment can *defend* (a fixed per-window concurrency bound
versus a per-stretch total), not about executions the untimed route gets
wrong — and the paper should say it that way. -/
theorem paced_budget_holds_under_timing
    {n Δconf d P : Nat} (hn : 0 < n) (hP : n + d ≤ P) {ι : Nat → Nat} {c₀ : Chain}
    {rented : ByzantineSlots} {Rrent : Nat}
    (hReacts : Reacts n Δconf d c₀ (pacedStolenAt ι P))
    (hNoBack : NoTheftBackdating n Δconf c₀ (pacedStolenAt ι P))
    (hRent : ∀ u, (badSlotsIn rented u n).card ≤ Rrent)
    (hRT : Rrent + 1 ≤ faultBudget n) :
    ∀ u, (badSlotsIn (badKeyrot n Δconf rented
        (MoltPetit.Model.stolenOf (pacedStolenAt ι P)) c₀) u n).card ≤ faultBudget n := by
  intro u
  rw [badKeyrot_eq_core]
  refine MoltPetit.Model.budget_of_reaction_tight (guard := fun _ => True) hn hReacts hNoBack
    (fun u _ => hRent u) (fun u _ => ?_) hRT u trivial
  have hone := recentTheftProducersTight_card_le_one_of_paced
    (n := n) (d := d) (P := P) (ι := ι) hP u
  rw [recentTheftProducersTight_eq_core] at hone
  exact hone

/-- **The census hypothesis of `max_sync_period_tight` holds for EVERY `F`.**
The formal residue of "`F_max` rises": for a paced adversary the tight
census bound is a single per-window fact, so it discharges
`max_sync_period_tight`'s `hTheft` at `T := 1` for an arbitrary sync period.
Nothing here proves a larger `F` is *safe* on its own — rent still has to be
bounded over the same stretch — but the census, which is what the untimed
route made grow with the stretch, no longer constrains `F` at all. -/
theorem paced_tight_census_bound_all_F
    {n d P : Nat} (hP : n + d ≤ P) {ι : Nat → Nat} (F now : Nat) :
    ∀ u, now < u + F + 4 * n →
      (recentTheftProducersTight n d (pacedStolenAt ι P) u).card ≤ 1 :=
  fun u _ => recentTheftProducersTight_card_le_one_of_paced hP u

end Molt
