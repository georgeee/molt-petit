import Molt.Verifier
import Spec.Reference

/-!
# What a deployment must provide (paper §5)

The named operational assumptions, exactly as the theorems consume them.
Everything here is a *hypothesis* of the results in `Molt/Results.lean` —
never a global axiom; the axiom audit (`MoltPetit/Results/Axioms.lean`)
confirms nothing else is smuggled in.

Proof-side semantic predicates (`ValidChain`, `SlotRecord`, …) are
re-exported from the core; the deployer-facing assumption statements are
written out fresh.
-/

namespace Molt

/-- Semantic (proof-side) chain validity. -/
abbrev ValidChain := MoltPetit.Model.ValidChain

open Classical in
/-- The bad slots inside the window `[u, u + n)`. -/
noncomputable def badSlotsIn (bad : ByzantineSlots) (u n : Nat) : Finset Nat :=
  (Finset.Ico u (u + n)).filter fun s => bad s

/-- **Assumption 1 (fault budget).** In every window of `n` consecutive
slots, at most `⌊(n-1)/3⌋` are bad. -/
def FaultBounded (n : Nat) (bad : ByzantineSlots) : Prop :=
  ∀ u, (badSlotsIn bad u n).card ≤ faultBudget n

/-- **Assumption 2's formal residue (recency-scoped uniqueness).** For a
block of a semantically valid chain whose tip is recent: if its slot is
honest and it carries a verifying signature, it is the unique block in its
producer's signing log for that slot. Re-exported structure. -/
abbrev SigUnforgeableRecent := @MoltPetit.Model.SigUnforgeableRecent

/-! Conclusion-side predicates the theorems use. -/

/-- An honest slot contains at most one produced block. -/
def HonestSlotsUnique (bad : ByzantineSlots) (record : SlotRecord) : Prop :=
  ∀ s, ¬ bad s →
    ∀ ⦃B B' : Block⦄, B ∈ record s → B' ∈ record s → B = B'

/-- Block ids are injective across the record. -/
def IdInjective (record : SlotRecord) : Prop :=
  ∀ s t, ∀ ⦃B B' : Block⦄,
    B ∈ record s → B' ∈ record t → B.id = B'.id → B = B'

/-! ## Bridge to the core development -/

theorem badSlotsIn_eq_core : badSlotsIn = MoltPetit.Model.badSlotsIn := rfl
theorem faultBounded_eq_core :
    FaultBounded = MoltPetit.Model.ByzantineBounded := rfl
theorem signedHashInjective_eq_core :
    SignedHashInjective = MoltPetit.Model.SignedHashInjective := rfl
theorem honestBlocksCover_eq_core :
    HonestBlocksCover = MoltPetit.Model.HonestBlocksCover := rfl
theorem honestSlotsUnique_eq_core :
    HonestSlotsUnique = MoltPetit.Model.HonestSlotsUnique := rfl
theorem idInjective_eq_core : IdInjective = MoltPetit.Model.IdInjective := rfl

end Molt
