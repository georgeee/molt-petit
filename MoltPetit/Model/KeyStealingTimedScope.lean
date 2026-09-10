import MoltPetit.Model.KeyStealingSchedule
import MoltPetit.Model.KeyStealing

/-!
# MoltPetit — the no-back-dating obstruction (rollout item W6)

`docs/rollout/ROLLOUT_PLAN.md` item W6 assesses deriving per-mode honest-slot uniqueness
(`KeyStealingEUFCMA`, mode 1; `SchedCoreUnforgeable`, modes 2-3) from a timed
model, mirroring `sigUnforgeableRecent_of_timed` (`TimedSig.lean`). The
finding, independent of the owner's separate, already-settled rejection of
`NoBackdate`/forward security as a constraint on *stolen* keys
(`memory/key-rotation-mission.md`): a timed custody argument
(`TimedExecution`'s `honest_once`/`honest_stamp`) only ever certifies "the
whole real slot is safe", while the existing EUF-CMA surfaces are premised on
a single key *version* being safe. One real slot can host one safe key and
one stolen key simultaneously, so single-key safety does not imply slot
safety, and the derivation does not go through without weakening an
already-assumed primitive's type — forbidden by the additive-only rule.

The two theorems below exhibit the gap concretely: a slot where one named key
is unstolen, yet the slot is bad anyway because a *different* key eligible at
that slot is stolen. They exist so the paper's "not derived" claim (a new
assumption, stated directly rather than derived — see `docs/rollout/ROLLOUT_NOTES.md` §1,
row W6) is machine-checked, not merely asserted.
-/

namespace MoltPetit.Model

/-- **Mode 2/3: single-key safety does not imply slot safety.** A witness slot
where key `j = 0` is safe yet the slot is bad anyway, because another key
`j = 1`, eligible under `badSched`'s `schedule s ≤ j` clause, is stolen. This
is the formal reason a timed, per-real-slot custody argument cannot certify
`SchedCoreUnforgeable`'s single-key premise. -/
theorem badSched_single_key_safe_not_enough :
    ∃ (n : Nat) (schedule : Nat → Nat) (rented : ByzantineSlots)
      (Stolen : Nat → Nat → Prop) (s j : Nat),
      ¬ rented s ∧ ¬ Stolen (producerForSlot n s) j ∧
        badSched n schedule rented Stolen s := by
  refine ⟨1, fun _ => 0, fun _ => False, fun _ j' => j' = 1, 0, 0, ?_, ?_, ?_⟩
  · exact id
  · decide
  · exact Or.inr ⟨1, by decide, rfl⟩

/-- **Mode 1: the same obstruction over `badKeyrotOn`.** The witness chain is
the empty chain, over which `inForce` is `0` for every producer and slot (the
confirmed prefix of `[]` is `[]`, and `keyFloor` of `[]` is `0`). -/
theorem badKeyrotOn_single_key_safe_not_enough :
    ∃ (n Δconf : Nat) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop)
      (s j : Nat),
      ¬ rented s ∧ ¬ Stolen (producerForSlot n s) j ∧
        badKeyrotOn n Δconf rented Stolen ([] : Chain) s := by
  refine ⟨1, 0, fun _ => False, fun _ j' => j' = 1, 0, 0, ?_, ?_, ?_⟩
  · exact id
  · decide
  · exact Or.inr ⟨1, by decide, rfl⟩

end MoltPetit.Model
