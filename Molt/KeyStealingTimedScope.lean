import Molt.Rotation
import MoltPetit.Model.KeyStealingTimedScope

/-!
# Molt — the no-back-dating obstruction, re-presented (rollout item W6)

Paper-aligned wrappers of `MoltPetit.Model.badSched_single_key_safe_not_enough`
and `MoltPetit.Model.badKeyrotOn_single_key_safe_not_enough`
(`MoltPetit/Model/KeyStealingTimedScope.lean`), so the paper's citations
resolve inside `Molt/` per the codebase convention (every paper2 Lean
citation resolves here, `CLAUDE.md`) — `badSched` is already `abbrev`
re-exported and `badKeyrot`/`producer` are already `rfl`-bridged to their
core originals (`badKeyrot_eq_core`, `producer_eq_core`,
`Molt/Rotation.lean:182`, `Molt/Protocol.lean:112`), so both wrappers are
one-line terms under that existing defeq, exactly as
`badKeyrot_lossOnly`/`badSched_lossOnly` already are (`Molt/Rotation.lean`).
-/

namespace Molt

theorem badSched_single_key_safe_not_enough :
    ∃ (n : Nat) (schedule : Nat → Nat) (rented : ByzantineSlots)
      (Stolen : Nat → Nat → Prop) (s j : Nat),
      ¬ rented s ∧ ¬ Stolen (producer n s) j ∧
        badSched n schedule rented Stolen s :=
  MoltPetit.Model.badSched_single_key_safe_not_enough

theorem badKeyrot_single_key_safe_not_enough :
    ∃ (n Δconf : Nat) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop)
      (s j : Nat),
      ¬ rented s ∧ ¬ Stolen (producer n s) j ∧
        badKeyrot n Δconf rented Stolen ([] : Chain) s :=
  MoltPetit.Model.badKeyrotOn_single_key_safe_not_enough

end Molt
