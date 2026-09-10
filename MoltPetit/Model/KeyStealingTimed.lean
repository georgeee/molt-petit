import MoltPetit.Model.KeyStealingBudget
import MoltPetit.Model.KeyStealingScheduleTimed

/-!
# MoltPetit — the timed theft layer for mode 1 (rollout item W3a)

The mode-1 mirror of `KeyStealingScheduleTimed`'s timed I3
(`horizon_budget_of_timed`): derive the exact budget hypothesis the mode-1
client theorems already consume (the trailing/anchored form,
`∀ u, guard u → (badSlotsIn (badKeyrotOn n Δconf rented (stolenOf stolenAt)
c₀) u n).card ≤ maxByzantine n`, for whatever window guard the caller
names) from a rent rate, a per-window recent-theft-producer census, and a
new named REACTION hypothesis — rather than assuming the joint budget
outright. Time-stamped theft reuses `stolenAt`/`stolenOf` from
`KeyStealingScheduleTimed.lean` verbatim (`Stolen := stolenOf stolenAt`); no
new theft-timing vocabulary is invented.

**Why `Reacts` is named, not derived.** Mode 2's `theft_is_recent`
(`KeyStealingScheduleTimed.lean:122`) derives its backward-locality content
from the flagship schedule's period (`j = s / R`): a theft of generation `j`
cannot be stale relative to its own provisioning window. Mode 1's floor
`inForce` (`KeyRotation.lean:49`, read off a witness chain `c₀`'s confirmed
prefix) carries no such period — there is no schedule to derive a real-time
bound from. `Reacts` therefore plays the role `NoPrematureTheft`/
`ErasureTimed` already play in mode 2 (a *named* operational hypothesis, not
a derived one): a reaction delay `d` after a theft, the floor `c₀` confirms
for the victim producer has moved strictly past the stolen version — i.e.
the emergency rotation is confirmed on the witness chain within `d` slots of
the theft.

**Why the derivation is per accepted chain.** `badKeyrotOn` is keyed to a
fixed witness chain `c₀` (`KeyStealing.lean:47`), so `Reacts` is likewise
parametrized by that same `c₀` (unlike mode 2's chain-independent `s / R`).
Composing with a client theorem instantiates `c₀ := stripSigs sc`, the same
chain the theorem's own budget hypothesis already reads its census from.

**Genericity in the window guard.** `budget_of_reaction` is stated over an
arbitrary `guard : Nat → Prop` rather than a fixed `H ≤ u` shape, because its
proof (mirroring `horizon_budget_of_timed`) never inspects `guard` beyond
calling `hRent u hu`/`hTheft u hu` opaquely — genericizing costs nothing and
lets one theorem serve the core anchored form *and* all of the Molt client
wrappers with no restatement.

**Honest scope.** `recentTheftProducersK`'s census is future-inclusive in
the same sense mode 2's is: a theft counted at window `u` stays counted at
every window before `r + d`, and is never subtracted once the reaction
actually fires (`Reacts` says the corruption *heals* at `s ≥ r + d`; it says
nothing that would shrink the census below `r + d`). Confining the census to
a non-retroactive form needs a further, mint-time-aware signature surface —
`docs/rollout/ROLLOUT_NOTES.md` §1 row W3b, not attempted here.
-/

namespace MoltPetit.Model

open Classical

/-- The mode-1 REACTION hypothesis: a reaction delay `d` after a theft of
producer `i`'s generation-`j` key at real slot `r`, the floor `c₀` confirms
for `i` has moved strictly past `j` at every later slot `s ≥ r + d`. -/
def Reacts (n Δconf d : Nat) (c₀ : Chain) (stolenAt : Nat → Nat → Nat → Prop) :
    Prop :=
  ∀ i j r, stolenAt i j r → ∀ s, r + d ≤ s → j < inForce n Δconf c₀ i s

/-- The mode-1 mirror of `recentTheftProducers`
(`KeyStealingScheduleTimed.lean:149`): producers hit by a theft whose real
time `r` is within `d` of window `u`. No generation-floor conjunct — mode 1
has no period to define one from, and it would be redundant here just as
mode 2's own floor conjunct is redundant under `NoPrematureTheft`
(`KeyStealingScheduleTimed.lean:137-148`). -/
noncomputable def recentTheftProducersK (n d : Nat)
    (stolenAt : Nat → Nat → Nat → Prop) (u : Nat) : Finset Nat :=
  (Finset.range n).filter (fun i => ∃ j r, stolenAt i j r ∧ u < r + d)

/-- **The subset bound `Reacts` buys.** Every producer exposed (in the
chain-relative sense `exposedProducers` counts) at window `u` was hit by a
theft real-time-recent to `u`. -/
theorem exposedProducers_subset_recentTheftK
    {n Δconf d : Nat} (hn : 0 < n) {c₀ : Chain}
    {stolenAt : Nat → Nat → Nat → Prop}
    (hReacts : Reacts n Δconf d c₀ stolenAt) (u : Nat) :
    exposedProducers n Δconf (stolenOf stolenAt) c₀ u ⊆
      recentTheftProducersK n d stolenAt u := by
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
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, j, r, hr, ?_⟩
  · unfold producerForSlot
    exact Nat.mod_lt _ hn
  · omega

/-- **The mode-1 timed I3** — the exact budget hypothesis every mode-1
client theorem consumes, derived from a rent rate, a reaction-delay-bounded
theft census, and the `1/3` bound, at an arbitrary window guard. -/
theorem budget_of_reaction
    {n Δconf d : Nat} (hn : 0 < n)
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop} {c₀ : Chain}
    {guard : Nat → Prop} {Rrent T : Nat}
    (hReacts : Reacts n Δconf d c₀ stolenAt)
    (hRent : ∀ u, guard u → (badSlotsIn rented u n).card ≤ Rrent)
    (hTheft : ∀ u, guard u → (recentTheftProducersK n d stolenAt u).card ≤ T)
    (hRT : Rrent + T ≤ maxByzantine n) :
    ∀ u, guard u →
      (badSlotsIn (badKeyrotOn n Δconf rented (stolenOf stolenAt) c₀) u n).card
        ≤ maxByzantine n := by
  intro u hu
  have hsplit := badSlotsIn_union_le rented (theftOn n Δconf (stolenOf stolenAt) c₀) u n
  have htheft := theftSlots_card_le_exposed n Δconf (stolenOf stolenAt) c₀ u
  have hsub := exposedProducers_subset_recentTheftK hn hReacts u
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

/-- The one-line specialization at the core anchored guard — the shape
`honestSlotsUnique_keyrot_anchored`/`keyrot_recent_tip_ancestor_agreement_anchored`/
`keyrot_recent_tip_ancestor_mem_anchored` (`KeyStealingHorizon*.lean`) take as
`hBudgetFrom`. -/
theorem anchored_budget_of_reaction
    {n Δconf d : Nat} (hn : 0 < n)
    {rented : ByzantineSlots} {stolenAt : Nat → Nat → Nat → Prop} {c₀ : Chain}
    {A : Block} {Rrent T : Nat}
    (hReacts : Reacts n Δconf d c₀ stolenAt)
    (hRent : ∀ u, A.slot + 1 ≤ u + n → (badSlotsIn rented u n).card ≤ Rrent)
    (hTheft : ∀ u, A.slot + 1 ≤ u + n →
      (recentTheftProducersK n d stolenAt u).card ≤ T)
    (hRT : Rrent + T ≤ maxByzantine n) :
    ∀ u, A.slot + 1 ≤ u + n →
      (badSlotsIn (badKeyrotOn n Δconf rented (stolenOf stolenAt) c₀) u n).card
        ≤ maxByzantine n :=
  budget_of_reaction hn hReacts hRent hTheft hRT

end MoltPetit.Model
