import MoltPetit.Model.Timed
import MoltPetit.Model.Safety

/-!
# Light-client safety in the timed model — no back-dating assumption

`light_client_safety` assumes `SigUnforgeableRecent`, which the timed model only
yields under `NoBackdate` (`sigUnforgeableRecent_of_timed`), and `NoBackdate` is
not implied by the model (`noBackdate_independent`): a bad real slot may sign a
block carrying one of its producer's honest stamps. This module proves
light-client safety **directly from the timed model**: EUF-CMA (blocks are signed
only through the timed log), collision resistance (`id_inj`), the per-window
fault budget and the recency rule. It needs neither `NoBackdate` nor any
exposure hypothesis, and it genuinely uses recency.

`R` is the verifier's real slot. Both chains must exist by `R` and pass the
recency rule `R ≤ tip.slot + n`. The proof plan is in `docs/TIMED_SAFETY_SPEC.md`.

THE STATEMENT OF `timed_tip_ancestor_agreement` IS FIXED. Its exact type is pinned
by `Molt/AxiomsTimedSafety.lean`. Prove it; do not change it.
-/

namespace MoltPetit.Model

/-- **Timed light-client safety.** Two valid chains from the same genesis, both
available by real slot `R` and both recent at `R`, agree on the block `n` below
the shorter chain's tip. -/
theorem timed_tip_ancestor_agreement {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    (hBudget : ByzantineBounded n bad)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    (hHead : blockAt? c 0 = some G) (hHead' : blockAt? c' 0 = some G)
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hRecent : R ≤ tip.slot + n) (hRecent' : R ≤ tip'.slot + n)
    (hLen : c.length ≤ c'.length)
    (hLong : n < c.length) :
    blockAt? c' (c.length - 1 - n) = blockAt? c (c.length - 1 - n) := by
  sorry

end MoltPetit.Model
