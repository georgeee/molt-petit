import MoltPetit.Model.KeyStealingTimed

/-!
# MoltPetit — the time-aware signature surface (rollout item W3b)

`KeyStealingTimed.lean` (W3a) gives mode 1 a real-time census
(`recentTheftProducersK`), but that census is not actually independent of
how far back a client's window guard reaches: its membership test `u < r +
d` bounds the theft's real time `r` from ABOVE relative to the window `u`,
but not from below. At an ancient window (exactly what a large sync period
`F` forces `max_sync_period_timed`'s guard `now < u + F + 4n` to admit),
a theft with any finite `r` still counts — the same retroactive
accumulation W3a was built to avoid, just moved one level down.

The missing ingredient is a LOWER bound on `r` relative to the exposed
slot. Mode 2 gets this for free from `NoPrematureTheft`'s two-sided
schedule pin (`j = s / R`, `KeyStealingScheduleTimed.lean:96`); mode 1
cannot, because `badKeyrotOn`'s `∃ j ≥ inForce(s), Stolen i j` existential
is `≤`-only (`KeyStealing.lean:47-50`) by design — the key-stealing
adversary deliberately refuses `NoBackdate`/forward security
(`KeyStealingUnique.lean`'s own docstring). Supplying that lower bound is
exactly what a signature-level "the adversary does not backdate a
stolen-key signature to before it stole the key" fact buys — the literal
cryptographic content this module's name refers to.

**`NoTheftBackdating` is named, not derived** — the same status `Reacts`,
`NoPrematureTheft`, and `ErasureTimed` already have. A fully derived version
would need a genuine mint-time-aware EUF-CMA primitive
(`KeyStealingEUFCMATimed`, keying the unforgeability conclusion on "not
stolen by the block's own mint slot" rather than "never stolen") and a
re-derivation of `VersionedUnforgeable`/`honestSlotsUnique_keyrot` under
it — comparable in size to the whole existing `KeyStealing*.lean` stack,
and explicitly parked as future work (mirroring `KeyStealingScheduleTimed.
lean`'s own honest-scope note about its `SchedCoreUnforgeable` surface).
`NoTheftBackdating` is deliberately WEAKER than the model's blanket refusal
of `NoBackdate`: it only constrains the theft-exploit relationship (a
stolen key cannot backdate its OWN exposure before the theft), not signing
in general, so it does not silently re-import the assumption the model's
adversary is built to exclude.

This module changes nothing `KeyStealingTimed.lean` states or proves; it
adds a strictly separate, sound superset relation
(`exposedProducers ⊆ recentTheftProducersTight`) that happens to need the
new hypothesis, alongside — not instead of — W3a's own `Reacts`-only
census.
-/

namespace MoltPetit.Model
open Classical

/-- **The time-aware signature surface.** A stolen version `j` of producer
`i`'s key, exfiltrated at real slot `r`, cannot be exploited to expose a
chain-slot `s` that predates the theft: if the floor `c₀` confirms for `i`
at `s` has not yet reached `j`, the theft cannot have happened before `s`.
Contrapositively: once the floor at `s` has reached `j`, any theft of that
version happened at or before `s`. -/
def NoTheftBackdating (n Δconf : Nat) (c₀ : Chain) (stolenAt : Nat → Nat → Nat → Prop) :
    Prop :=
  ∀ i j r s, stolenAt i j r → inForce n Δconf c₀ i s ≤ j → r ≤ s

/-- **`NoTheftBackdating` is degenerate.** At any positive confirmation depth
nothing is confirmed at slot `0`, so the floor there is `0` and the hypothesis
forces every theft to have happened at real slot `0`. It is retained only as a
documented negative result; no paper-facing theorem should consume it.

THE STATEMENT OF `noTheftBackdating_degenerate` IS FIXED (pinned by
`Molt/AxiomsTSTimed.lean`). Prove it; do not change it. -/
theorem noTheftBackdating_degenerate {n Δconf : Nat} (hΔ : 1 ≤ Δconf)
    {c₀ : Chain} {stolenAt : Nat → Nat → Nat → Prop}
    (h : NoTheftBackdating n Δconf c₀ stolenAt)
    {i j r : Nat} (hst : stolenAt i j r) : r = 0 := by
  sorry

/-- The two-sided-bounded census: `recentTheftProducersK` with the extra
conjunct `r < u + n`, pinning a qualifying theft's real time to the fixed
interval `(u − d, u + n)` around the window — independent of the window's
own position, closing the gap `NoTheftBackdating`'s docstring names. -/
noncomputable def recentTheftProducersTight (n d : Nat)
    (stolenAt : Nat → Nat → Nat → Prop) (u : Nat) : Finset Nat :=
  (Finset.range n).filter (fun i => ∃ j r, stolenAt i j r ∧ u < r + d ∧ r < u + n)

/-- **The subset bound `Reacts` + `NoTheftBackdating` buy, tightened.**
Every producer exposed at window `u` was hit by a theft real-time-recent to
`u`, from BOTH sides. -/
theorem exposedProducers_subset_recentTheftTight
    {n Δconf d : Nat} (hn : 0 < n) {c₀ : Chain}
    {stolenAt : Nat → Nat → Nat → Prop}
    (hReacts : Reacts n Δconf d c₀ stolenAt)
    (hNoBack : NoTheftBackdating n Δconf c₀ stolenAt) (u : Nat) :
    exposedProducers n Δconf (stolenOf stolenAt) c₀ u ⊆
      recentTheftProducersTight n d stolenAt u := by
  intro i hi
  unfold exposedProducers at hi
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hi
  rw [Finset.mem_filter] at hs
  obtain ⟨hsIco, hTheft⟩ := hs
  rw [Finset.mem_Ico] at hsIco
  unfold theftOn stolenOf at hTheft
  obtain ⟨j, hle, r, hr⟩ := hTheft
  have hslt : s < r + d := by
    by_contra hcon
    push Not at hcon
    have hgt := hReacts (producerForSlot n s) j r hr s hcon
    omega
  have hrle : r ≤ s := hNoBack (producerForSlot n s) j r s hr hle
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, j, r, hr, ?_, ?_⟩
  · unfold producerForSlot
    exact Nat.mod_lt _ hn
  · omega
  · omega

/-- **Non-retroactivity, sharp.** The precise content of "the census is no
longer retroactive": under `Reacts` + `NoTheftBackdating`, a theft of
version `j` at real slot `r` can expose a chain-slot `s` only for
`s ∈ [r, r + d)` — never before the theft (that is `NoTheftBackdating`),
and never once the reaction has fired (that is `Reacts`). The exposure
window has fixed width `d`, independent of where `s` sits in the run, which
is exactly what stops a census at an ancient window from accumulating
later thefts. This is the statement a paper sentence about theft times
should cite; the two-sided filter in `recentTheftProducersTight` is its
Finset-level shadow. -/
theorem theft_exposure_window
    {n Δconf d : Nat} {c₀ : Chain} {stolenAt : Nat → Nat → Nat → Prop}
    (hReacts : Reacts n Δconf d c₀ stolenAt)
    (hNoBack : NoTheftBackdating n Δconf c₀ stolenAt)
    {i j r s : Nat} (hst : stolenAt i j r)
    (hexp : inForce n Δconf c₀ i s ≤ j) :
    r ≤ s ∧ s < r + d := by
  refine ⟨hNoBack i j r s hst hexp, ?_⟩
  by_contra hcon
  push Not at hcon
  have := hReacts i j r hst s hcon
  omega

/-- **The mode-1 timed I3, tightened** — the exact budget hypothesis every
mode-1 client theorem consumes, derived from a rent rate, a two-sided
theft census, and the `1/3` bound, at an arbitrary window guard. Line-for
-line mirror of `budget_of_reaction` with the tighter subset lemma
substituted. -/
theorem budget_of_reaction_tight
    {n Δconf d : Nat} (hn : 0 < n)
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop} {c₀ : Chain}
    {guard : Nat → Prop} {Rrent T : Nat}
    (hReacts : Reacts n Δconf d c₀ stolenAt)
    (hNoBack : NoTheftBackdating n Δconf c₀ stolenAt)
    (hRent : ∀ u, guard u → (badSlotsIn rented u n).card ≤ Rrent)
    (hTheft : ∀ u, guard u → (recentTheftProducersTight n d stolenAt u).card ≤ T)
    (hRT : Rrent + T ≤ maxByzantine n) :
    ∀ u, guard u →
      (badSlotsIn (badKeyrotOn n Δconf rented (stolenOf stolenAt) c₀) u n).card
        ≤ maxByzantine n := by
  intro u hu
  have hsplit := badSlotsIn_union_le rented (theftOn n Δconf (stolenOf stolenAt) c₀) u n
  have htheft := theftSlots_card_le_exposed n Δconf (stolenOf stolenAt) c₀ u
  have hsub := exposedProducers_subset_recentTheftTight hn hReacts hNoBack u
  have hcard := Finset.card_le_card hsub
  have hrw : (badSlotsIn (badKeyrotOn n Δconf rented (stolenOf stolenAt) c₀) u n).card
      = (badSlotsIn (fun s => rented s ∨ theftOn n Δconf (stolenOf stolenAt) c₀ s) u n).card :=
    rfl
  rw [hrw]
  calc (badSlotsIn (fun s => rented s ∨ theftOn n Δconf (stolenOf stolenAt) c₀ s) u n).card
      ≤ (badSlotsIn rented u n).card
          + (badSlotsIn (theftOn n Δconf (stolenOf stolenAt) c₀) u n).card := hsplit
    _ ≤ Rrent + T :=
        Nat.add_le_add (hRent u hu) (le_trans htheft (le_trans hcard (hTheft u hu)))
    _ ≤ maxByzantine n := hRT

/-- The one-line specialization at the core anchored guard — exact mirror
of `anchored_budget_of_reaction`. -/
theorem anchored_budget_of_reaction_tight
    {n Δconf d : Nat} (hn : 0 < n)
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop} {c₀ : Chain}
    {A : Block} {Rrent T : Nat}
    (hReacts : Reacts n Δconf d c₀ stolenAt)
    (hNoBack : NoTheftBackdating n Δconf c₀ stolenAt)
    (hRent : ∀ u, A.slot + 1 ≤ u + n → (badSlotsIn rented u n).card ≤ Rrent)
    (hTheft : ∀ u, A.slot + 1 ≤ u + n →
      (recentTheftProducersTight n d stolenAt u).card ≤ T)
    (hRT : Rrent + T ≤ maxByzantine n) :
    ∀ u, A.slot + 1 ≤ u + n →
      (badSlotsIn (badKeyrotOn n Δconf rented (stolenOf stolenAt) c₀) u n).card
        ≤ maxByzantine n :=
  budget_of_reaction_tight hn hReacts hNoBack hRent hTheft hRT

end MoltPetit.Model
