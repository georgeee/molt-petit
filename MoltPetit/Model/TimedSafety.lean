import MoltPetit.Model.Timed
import MoltPetit.Model.Safety

namespace MoltPetit.Model

theorem two_mul_maxByzantine_add_one_le_quorum (n : Nat) (hn : 1 ≤ n) :
    2 * maxByzantine n + 1 ≤ quorum n := by
  unfold quorum maxByzantine
  omega

theorem three_mul_maxByzantine_lt (n : Nat) (hn : 1 ≤ n) :
    3 * maxByzantine n < n := by
  unfold maxByzantine
  omega

open Classical in
theorem maxByzantine_pos_of_bad {n : Nat} {bad : ByzantineSlots}
    (hn : 1 ≤ n) (hBudget : ByzantineBounded n bad) {r : Nat} (hbad : bad r) :
    1 ≤ maxByzantine n := by
  have hcard := hBudget r
  have hmem : r ∈ (Finset.Ico r (r + n)).filter (fun s => bad s) := by
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨le_rfl, by omega⟩, hbad⟩
  have hpos : 1 ≤ ((Finset.Ico r (r + n)).filter (fun s => bad s)).card :=
    Finset.card_pos.mpr ⟨r, hmem⟩
  exact le_trans hpos hcard

theorem four_le_of_maxByzantine_pos {n : Nat} (h : 1 ≤ maxByzantine n) : 4 ≤ n := by
  unfold maxByzantine at h
  omega

theorem three_le_quorum_of_maxByzantine_pos {n : Nat} (h : 1 ≤ maxByzantine n) :
    3 ≤ quorum n := by
  unfold maxByzantine at h
  unfold quorum
  omega

theorem add_le_of_mod_eq_of_lt {n a b : Nat}
    (hmod : a % n = b % n) (hlt : a < b) : a + n ≤ b := by
  have hmodeq : Nat.ModEq n a b := hmod
  have hdvd : n ∣ b - a := (Nat.modEq_iff_dvd' (le_of_lt hlt)).mp hmodeq
  have hpos : 0 < b - a := by omega
  have := Nat.le_of_dvd hpos hdvd
  omega

theorem bad_of_signed_ne_slot {n : Nat} {bad : ByzantineSlots}
    {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    {r : Nat} {B : Block} (hBr : B ∈ log r) (hne : B.slot ≠ r) : bad r := by
  by_contra hnot
  have := hexec.honest_stamp hnot hBr
  exact hne this

def FirstSigned (log : TimedLog) (B : Block) (r : Nat) : Prop :=
  B ∈ log r ∧ ∀ r' < r, B ∉ log r'

theorem firstSigned_iff_find {log : TimedLog} {B : Block}
    (hBsig : ∃ r, B ∈ log r) {r : Nat} :
    FirstSigned log B r ↔ Nat.find hBsig = r := by
  constructor
  · rintro ⟨hBr, hmin⟩
    exact (Nat.find_eq_iff hBsig).mpr ⟨hBr, hmin⟩
  · rintro rfl
    exact ⟨Nat.find_spec hBsig, fun r' hr' => Nat.find_min hBsig hr'⟩

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
