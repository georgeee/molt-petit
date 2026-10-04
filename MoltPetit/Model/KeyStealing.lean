import MoltPetit.Model.KeyRotation
import Spec.Model

/-!
# MoltPetit — the key-stealing adversary (Phase 2, increment I1)

The strong adversary of `georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md` (v3): a stolen delegate key
`dk(i,j)` signs **anything, at any slot, forever** — no forward security. This
module lays the foundation (see `georgeee/mini-consensus-lean: PHASE2_DESIGN.md`, increment I1):

* `badKeyrotOn` — the induced corruption as a **chain-independent slot predicate**,
  keyed on the in-force index read off a **fixed** witness chain `c₀`'s finalized
  prefix: `rented s ∨ ∃ j ≥ inForce c₀ i s, Stolen i j` (any stolen
  not-yet-rotated-out key corrupts the slot; a stolen rotated-out key never does).
-/

namespace MoltPetit.Model

-- ===========================================================================
-- The induced corruption predicate
-- ===========================================================================

/-- **The loss-only adversary: with nothing stolen, the corruption predicate is
just rent — and is chain-independent.**

Key *loss* is not key *theft*: losing a delegate key gives the adversary no
signing power, and the loser simply rotates, which the validator already
supports. So the loss-only adversary is this model at `Stolen := fun _ _ =>
False`, and no new development is needed for it.

The payoff is the `c₀` argument disappearing. `badKeyrotOn` reads the in-force
index off a witness chain, which is exactly why a from-genesis fork (whose
floor never advances) is judged by a *different* predicate than the real chain
— the gap that `H-ANCHOR` exists to close. With no theft the existential is
vacuous, the predicate collapses to `rented`, and that asymmetry has nothing
to attach to: prophylactic and loss-driven rotation need no anchor, no
key-leak horizon, and no update mechanism. -/
theorem badKeyrotOn_lossOnly (n Δconf : Nat) (rented : ByzantineSlots) (c₀ : Chain) :
    badKeyrotOn n Δconf rented (fun _ _ => False) c₀ = rented := by
  funext s
  simp [badKeyrotOn]

end MoltPetit.Model
