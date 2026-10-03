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

/-- Step 1 (No pre-signing): along a valid chain, a non-genesis block is never
signed before its slot. In other words, its first-signing slot is at least its stamp. -/
theorem slot_le_sigTime {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    (hBudget : ByzantineBounded n bad)
    {c : Chain} (hc : ValidChain n c)
    (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R) :
    ∀ (k : Nat), 1 ≤ k →
      ∀ {B : Block}, blockAt? c k = some B →
      ∀ (hBsig : ∃ r, B ∈ log r),
      B.slot ≤ Nat.find hBsig := by
  have hGprev : G.prev = none := hc.2.2.1 hHead
  have hS : StrictSlots c := hc.2.1
  have hMat : MaturedWindowsDense n c := hc.2.2.2
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk B hB hBsig
    by_contra hlt
    push Not at hlt
    set r := Nat.find hBsig with hrdef
    have hBr : B ∈ log r := Nat.find_spec hBsig
    have hbad : bad r := bad_of_signed_ne_slot hexec hBr (ne_of_gt hlt)
    have hmodB : B.slot % n = r % n := hexec.key_match hBr
    have hrn : r + n ≤ B.slot := add_le_of_mod_eq_of_lt hmodB.symm hlt
    have hFpos : 1 ≤ maxByzantine n := maxByzantine_pos_of_bad hn hBudget hbad
    have h4n : 4 ≤ n := four_le_of_maxByzantine_pos hFpos
    have h3q : 3 ≤ quorum n := three_le_quorum_of_maxByzantine_pos hFpos
    have hUle : (B.slot - n) + n ≤ B.slot + 1 := by omega
    have hqDense := hMat hB (B.slot - n) hUle
    set W := c.filter (blockInWindow (B.slot - n) n) with hWdef
    have hWlen : 3 ≤ W.length := by
      have he : windowCount c (B.slot - n) n = W.length := rfl
      omega
    have hWpair : W.Pairwise (fun a b => a.slot < b.slot) :=
      hS.sublist List.filter_sublist
    have hySame : ∀ y ∈ W, ∃ j, blockAt? c j = some y ∧ j = k - 1 := by
      intro y hyW
      have hyc : y ∈ c := List.mem_of_mem_filter hyW
      have hywin : blockInWindow (B.slot - n) n y = true := List.of_mem_filter hyW
      simp only [blockInWindow, decide_eq_true_eq] at hywin
      obtain ⟨j, hjlen, hjy⟩ := List.mem_iff_getElem.mp hyc
      have hjAt : blockAt? c j = some y := by
        unfold blockAt?
        rw [List.getElem?_eq_getElem hjlen, hjy]
      have hjlt : j < k := by
        rcases Nat.lt_or_ge j k with h | h
        · exact h
        · rcases Nat.eq_or_lt_of_le h with rfl | h
          · have hBy : B = y := Option.some.inj (hB.symm.trans hjAt)
            subst hBy
            omega
          · have := strictSlots_lt hS hB hjAt h
            omega
      have hjnotlt : ¬ (j < k - 1) := by
        intro hjltpred
        have hk2 : 2 ≤ k := by omega
        obtain ⟨kpred, rfl⟩ : ∃ kp, k = kp + 1 := ⟨k - 1, by omega⟩
        obtain ⟨P, hPat, hprev⟩ := parentLinked_at_succ hc.2.2.1 hB
        have hkp1 : 1 ≤ kpred := by omega
        obtain ⟨hPne, rP, _, hrPmem⟩ := block_signed hGprev hc.2.2.1 hAvail hkp1 hPat
        have hPsig : ∃ r, P ∈ log r := ⟨rP, hrPmem⟩
        have hPslot : P.slot ≤ Nat.find hPsig := ih kpred (by omega) hkp1 hPat hPsig
        have hPstep : Nat.find hPsig ≤ Nat.find hBsig :=
          sigTime_mono_step hexec hPne hprev hPsig hBsig
        have hyltP : y.slot < P.slot := strictSlots_lt hS hjAt hPat (by omega)
        omega
      refine ⟨j, hjAt, by omega⟩
    have h0 : 0 < W.length := by omega
    have h1 : 1 < W.length := by omega
    obtain ⟨j0, hj0At, hj0Eq⟩ := hySame (W[0]'h0) (List.getElem_mem h0)
    obtain ⟨j1, hj1At, hj1Eq⟩ := hySame (W[1]'h1) (List.getElem_mem h1)
    rw [hj0Eq] at hj0At
    rw [hj1Eq] at hj1At
    have hy01 : W[0]'h0 = W[1]'h1 := Option.some.inj (hj0At.symm.trans hj1At)
    have hlt01 := List.pairwise_iff_getElem.mp hWpair 0 1 h0 h1 (by omega)
    rw [hy01] at hlt01
    exact (lt_irrefl _) hlt01

/-- Step 1 (FirstSigned form): along a valid chain, a non-genesis block's stamp
is at most any first-signing slot `r`. -/
theorem slot_le_firstSigned {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    (hBudget : ByzantineBounded n bad)
    {c : Chain} (hc : ValidChain n c)
    (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {k : Nat} (hk : 1 ≤ k) {B : Block} (hB : blockAt? c k = some B)
    {r : Nat} (hr : FirstSigned log B r) :
    B.slot ≤ r := by
  have hBsig : ∃ r0, B ∈ log r0 := ⟨r, hr.1⟩
  have heq : Nat.find hBsig = r := (firstSigned_iff_find hBsig).mp hr
  have := slot_le_sigTime hn hexec hBudget hc hHead hAvail k hk hB hBsig
  rwa [heq] at this

/-- Step 2 (Late is forever, single step): if block at index k is late,
its child at index k + 1 is also late. -/
theorem late_step {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    (hBudget : ByzantineBounded n bad)
    {c : Chain} (hc : ValidChain n c)
    (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {k : Nat} (hk : 1 ≤ k)
    {P N : Block} (hP : blockAt? c k = some P) (hN : blockAt? c (k + 1) = some N)
    (hPsig : ∃ r, P ∈ log r) (hNsig : ∃ r, N ∈ log r)
    (hLateP : P.slot < Nat.find hPsig) :
    N.slot < Nat.find hNsig := by
  have hGprev : G.prev = none := hc.2.2.1 hHead
  have hS : StrictSlots c := hc.2.1
  have hPL : ParentLinked c := hc.2.2.1
  have hMat : MaturedWindowsDense n c := hc.2.2.2
  obtain ⟨P', hP'at, hprev'⟩ := parentLinked_at_succ hPL hN
  have hP'eq : P' = P := Option.some.inj (hP'at.symm.trans hP)
  have hprev : N.prev = some P.id := hP'eq ▸ hprev'
  obtain ⟨hPne, -⟩ := block_signed hGprev hPL hAvail hk hP
  have hmono := sigTime_mono_step hexec hPne hprev hPsig hNsig
  by_contra hnot
  push Not at hnot
  have hleN := slot_le_sigTime hn hexec hBudget hc hHead hAvail (k + 1) (by omega) hN hNsig
  have hNeq : Nat.find hNsig = N.slot := by omega
  have hPr : P ∈ log (Nat.find hPsig) := Nat.find_spec hPsig
  have hbadP : bad (Nat.find hPsig) := bad_of_signed_ne_slot hexec hPr (ne_of_lt hLateP)
  have hmodP : P.slot % n = (Nat.find hPsig) % n := hexec.key_match hPr
  have hPn : P.slot + n ≤ Nat.find hPsig := add_le_of_mod_eq_of_lt hmodP hLateP
  have hPNslot : P.slot + n ≤ N.slot := by omega
  have hFpos : 1 ≤ maxByzantine n := maxByzantine_pos_of_bad hn hBudget hbadP
  have h3q : 3 ≤ quorum n := three_le_quorum_of_maxByzantine_pos hFpos
  have hUle : (P.slot + 1) + n ≤ N.slot + 1 := by omega
  have hqDense := hMat hN (P.slot + 1) hUle
  set W := c.filter (blockInWindow (P.slot + 1) n) with hWdef
  have hWlen : 3 ≤ W.length := by
    have he : windowCount c (P.slot + 1) n = W.length := rfl
    omega
  have hWpair : W.Pairwise (fun a b => a.slot < b.slot) :=
    hS.sublist List.filter_sublist
  have hySame : ∀ y ∈ W, ∃ j, blockAt? c j = some y ∧ j = k + 1 := by
    intro y hyW
    have hyc : y ∈ c := List.mem_of_mem_filter hyW
    have hywin : blockInWindow (P.slot + 1) n y = true := List.of_mem_filter hyW
    simp only [blockInWindow, decide_eq_true_eq] at hywin
    obtain ⟨j, hjlen, hjy⟩ := List.mem_iff_getElem.mp hyc
    have hjAt : blockAt? c j = some y := by
      unfold blockAt?
      rw [List.getElem?_eq_getElem hjlen, hjy]
    rcases Nat.lt_or_ge j (k + 1) with hjlt | hjge
    · rcases Nat.eq_or_lt_of_le (show j ≤ k by omega) with rfl | hjltk
      · have hPy : P = y := Option.some.inj (hP.symm.trans hjAt)
        subst hPy
        omega
      · have := strictSlots_lt hS hjAt hP hjltk
        omega
    · rcases Nat.eq_or_lt_of_le hjge with rfl | hjgt
      · exact ⟨k + 1, hjAt, rfl⟩
      · have := strictSlots_lt hS hN hjAt hjgt
        omega
  have h0 : 0 < W.length := by omega
  have h1 : 1 < W.length := by omega
  obtain ⟨j0, hj0At, hj0Eq⟩ := hySame (W[0]'h0) (List.getElem_mem h0)
  obtain ⟨j1, hj1At, hj1Eq⟩ := hySame (W[1]'h1) (List.getElem_mem h1)
  rw [hj0Eq] at hj0At
  rw [hj1Eq] at hj1At
  have hy01 : W[0]'h0 = W[1]'h1 := Option.some.inj (hj0At.symm.trans hj1At)
  have hlt01 := List.pairwise_iff_getElem.mp hWpair 0 1 h0 h1 (by omega)
  rw [hy01] at hlt01
  exact (lt_irrefl _) hlt01

/-- Step 2 (Late is forever, chain form): if block at index k is late,
any descendant at index k + d is also late. -/
theorem late_chain {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    (hBudget : ByzantineBounded n bad)
    {c : Chain} (hc : ValidChain n c)
    (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R) :
    ∀ (d : Nat) {k : Nat}, 1 ≤ k →
      ∀ {P B : Block}, blockAt? c k = some P → blockAt? c (k + d) = some B →
      ∀ (hPsig : ∃ r, P ∈ log r) (hBsig : ∃ r, B ∈ log r),
      P.slot < Nat.find hPsig →
      B.slot < Nat.find hBsig := by
  intro d
  induction d with
  | zero =>
    intro k hk P B hP hB hPsig hBsig hLateP
    rw [Nat.add_zero] at hB
    have heq : B = P := Option.some.inj (hB.symm.trans hP)
    subst heq
    have hfind : Nat.find hPsig = Nat.find hBsig := by congr 1
    rwa [hfind] at hLateP
  | succ d ih =>
    intro k hk P B hP hB hPsig hBsig hLateP
    have hlt : k + d < c.length := by
      unfold blockAt? at hB
      obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hB
      omega
    obtain ⟨M, hMat⟩ : ∃ M, blockAt? c (k + d) = some M := by
      unfold blockAt?
      exact ⟨getElem c (k + d) hlt, List.getElem?_eq_getElem hlt⟩
    have hkd : 1 ≤ k + d := by omega
    obtain ⟨hMne, rM, _, hrMmem⟩ := block_signed (hc.2.2.1 hHead) hc.2.2.1 hAvail hkd hMat
    have hMsig : ∃ r, M ∈ log r := ⟨rM, hrMmem⟩
    have hLateM := ih hk hP hMat hPsig hMsig hLateP
    have hBsucc : blockAt? c ((k + d) + 1) = some B := by
      rw [show (k + d) + 1 = k + (d + 1) by omega]
      exact hB
    exact late_step hn hexec hBudget hc hHead hAvail hkd hMat hBsucc hMsig hBsig hLateM

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
