import MoltPetit.Model.KeyStealing

/-!
# MoltPetit — the induced Byzantine budget, decomposed (increment I3)

The key-stealing safety theorems assume `ByzantineBounded n (badKeyrotOn …)` —
the `1/3` bound over the *joint* rent-or-theft corruption. This module derives
that joint budget from two independently meaningful quantities, closing the I3
seam (`KEY_ROTATION_SOUND.md` §3):

* a **rent budget** `R`: at most `R` rented slots per `n`-window (the classical
  slot-corruption rate), and
* a **theft rate** `T`: at most `T` **exposed producers** per window — producers
  holding *any* stolen not-yet-rotated-out key while their window slot comes up.

`induced_byzantine_bounded : R + T ≤ ⌊(n-1)/3⌋ → ByzantineBounded n (badKeyrotOn …)`.

The two non-trivial ingredients are exactly the ones the design note promised:

* **no double-count** — the union bound `badSlotsIn_union_le` (a slot both
  rented and theft-exposed is charged at most once on the left, so bounding the
  two parts separately can only over-charge);
* **the producer↔slot bijection** — each producer owns exactly one slot per
  `n`-window (`producerForSlot n s = s % n` is injective on any `n`-window), so
  theft-corrupt *slots* per window are bounded by exposed *producers* per
  window (`theftSlots_card_le_exposed`). This is what makes `T` a per-producer
  quantity — "how many producers are currently exposed" — rather than a
  slot-counting artifact.

Under `H-IND` (thefts do not cascade to higher versions) and prompt emergency
rotation, a single theft exposes one producer for the announcement-delay +
`Δconf` window, so `T` is the number of *concurrently healing* producers — the
natural deployment dial.
-/

namespace MoltPetit.Model

open Classical

/-- The theft half of `badKeyrotOn`: the slot's producer holds a stolen
not-yet-rotated-out key. -/
def theftOn (n Δconf : Nat) (Stolen : Nat → Nat → Prop) (c₀ : Chain) (s : Nat) : Prop :=
  ∃ j, inForce n Δconf c₀ (producerForSlot n s) s ≤ j ∧ Stolen (producerForSlot n s) j

theorem badKeyrotOn_iff_or {n Δconf : Nat} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {c₀ : Chain} (s : Nat) :
    badKeyrotOn n Δconf rented Stolen c₀ s ↔ rented s ∨ theftOn n Δconf Stolen c₀ s :=
  Iff.rfl

/-- **No double-count**: the joint corruption's window census is bounded by the
sum of the two parts' censuses. -/
theorem badSlotsIn_union_le (A B : ByzantineSlots) (u n : Nat) :
    (badSlotsIn (fun s => A s ∨ B s) u n).card ≤
      (badSlotsIn A u n).card + (badSlotsIn B u n).card := by
  classical
  refine le_trans (Finset.card_le_card fun s hs => ?_) (Finset.card_union_le _ _)
  simp only [badSlotsIn, Finset.mem_filter, Finset.mem_union] at hs ⊢
  tauto

/-- The **exposed producers** of a window: producers holding a stolen
not-yet-rotated-out key at their (unique) slot in `[u, u+n)`. -/
noncomputable def exposedProducers (n Δconf : Nat) (Stolen : Nat → Nat → Prop)
    (c₀ : Chain) (u : Nat) : Finset Nat :=
  (Finset.Ico u (u + n)).filter (fun s => theftOn n Δconf Stolen c₀ s) |>.image
    (producerForSlot n)

/-- Two slots of one `n`-window with the same producer are the same slot —
the producer↔slot correspondence is injective per window. -/
private theorem window_producer_inj {n u : Nat} {s s' : Nat}
    (hs : s ∈ Finset.Ico u (u + n)) (hs' : s' ∈ Finset.Ico u (u + n))
    (h : producerForSlot n s = producerForSlot n s') : s = s' := by
  rw [Finset.mem_Ico] at hs hs'
  unfold producerForSlot at h
  have h1 := Nat.div_add_mod s n
  have h2 := Nat.div_add_mod s' n
  rcases Nat.lt_trichotomy (s / n) (s' / n) with hlt | heq | hgt
  · exfalso
    have hmul : n * (s / n) + n ≤ n * (s' / n) :=
      calc n * (s / n) + n = n * (s / n + 1) := by ring
        _ ≤ n * (s' / n) := Nat.mul_le_mul (Nat.le_refl n) (Nat.succ_le_of_lt hlt)
    omega
  · rw [heq] at h1
    omega
  · exfalso
    have hmul : n * (s' / n) + n ≤ n * (s / n) :=
      calc n * (s' / n) + n = n * (s' / n + 1) := by ring
        _ ≤ n * (s / n) := Nat.mul_le_mul (Nat.le_refl n) (Nat.succ_le_of_lt hgt)
    omega

/-- **The producer↔slot bijection**: theft-corrupt slots per window are exactly
the exposed producers per window (each producer owns one slot per window). -/
theorem theftSlots_card_le_exposed (n Δconf : Nat) (Stolen : Nat → Nat → Prop)
    (c₀ : Chain) (u : Nat) :
    (badSlotsIn (theftOn n Δconf Stolen c₀) u n).card ≤
      (exposedProducers n Δconf Stolen c₀ u).card := by
  unfold badSlotsIn exposedProducers
  refine Finset.card_le_card_of_injOn (producerForSlot n) (fun s hs => ?_) ?_
  · exact Finset.mem_image_of_mem _ hs
  · intro s hs s' hs' h
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hs hs'
    exact window_producer_inj hs.1 hs'.1 h

/-- **I3 — the induced Byzantine budget, decomposed.** A rent budget of `R`
slots per window and a theft rate of `T` exposed producers per window, with
`R + T` within the `1/3` bound, give the joint `ByzantineBounded` over the
key-stealing corruption that every key-stealing safety theorem consumes. -/
theorem induced_byzantine_bounded {n Δconf : Nat}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop} {c₀ : Chain} {R T : Nat}
    (hRent : ∀ u, (badSlotsIn rented u n).card ≤ R)
    (hExposed : ∀ u, (exposedProducers n Δconf Stolen c₀ u).card ≤ T)
    (hRT : R + T ≤ maxByzantine n) :
    ByzantineBounded n (badKeyrotOn n Δconf rented Stolen c₀) := by
  intro u
  have hsplit := badSlotsIn_union_le rented (theftOn n Δconf Stolen c₀) u n
  have htheft := theftSlots_card_le_exposed n Δconf Stolen c₀ u
  have : (badSlotsIn (badKeyrotOn n Δconf rented Stolen c₀) u n).card =
      (badSlotsIn (fun s => rented s ∨ theftOn n Δconf Stolen c₀ s) u n).card := rfl
  rw [this]
  calc (badSlotsIn (fun s => rented s ∨ theftOn n Δconf Stolen c₀ s) u n).card
      ≤ (badSlotsIn rented u n).card + (badSlotsIn (theftOn n Δconf Stolen c₀) u n).card :=
        hsplit
    _ ≤ R + T := Nat.add_le_add (hRent u) (le_trans htheft (hExposed u))
    _ ≤ maxByzantine n := hRT

end MoltPetit.Model
