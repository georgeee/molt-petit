import MoltPetit.Model.TimedSafety

/-!
# Pinned statement and axiom audit for timed light-client safety

Owned by the reviewer. Do not edit. The `example` fixes the exact type of
`MoltPetit.Model.timed_tip_ancestor_agreement`, and the guard fails the build if
the proof is `sorry` or uses any non-classical axiom.
-/

open MoltPetit.Model in
example {n : Nat} (hn : 1 ≤ n)
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
    blockAt? c' (c.length - 1 - n) = blockAt? c (c.length - 1 - n) :=
  timed_tip_ancestor_agreement hn hexec hBudget hc hc' hHead hHead' hAvail hAvail'
    hTip hTip' hRecent hRecent' hLen hLong

/-- info: 'MoltPetit.Model.timed_tip_ancestor_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MoltPetit.Model.timed_tip_ancestor_agreement
