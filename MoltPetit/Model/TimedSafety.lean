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

theorem belowCount_mono (c : Chain) {a b : Nat} (h : a ≤ b) :
    belowCount c a ≤ belowCount c b := by
  induction c with
  | nil => rfl
  | cons x xs ih =>
    rw [belowCount_cons, belowCount_cons]
    have : (if x.slot < a then 1 else 0) ≤ (if x.slot < b then 1 else 0) := by
      split_ifs with h1 h2
      · rfl
      · omega
      · exact Nat.zero_le 1
      · rfl
    omega

theorem div_zero_of_quorum_le {q f K m : Nat}
    (hq : 2 * f + 1 ≤ q) (hdens : q * K ≤ m) (hbud : m ≤ f * (K + 1)) :
    K = 0 ∧ m ≤ f := by
  have hK : K = 0 := by
    cases K with
    | zero => rfl
    | succ K =>
      have h1 : (2 * f + 1) * (K + 1) ≤ q * (K + 1) :=
        Nat.mul_le_mul_right (K + 1) hq
      have h2 : q * (K + 1) ≤ f * (K + 2) := le_trans hdens hbud
      have h3 : (2 * f + 1) * (K + 1) ≤ f * (K + 2) := le_trans h1 h2
      have h4 : f * (K + 1) + (f + 1) * (K + 1) ≤ f * (K + 1) + f := by
        calc f * (K + 1) + (f + 1) * (K + 1)
            = (2 * f + 1) * (K + 1) := by ring
          _ ≤ f * (K + 2) := h3
          _ = f * (K + 1) + f := by ring
      have h5 : (f + 1) * (K + 1) ≤ f := Nat.le_of_add_le_add_left h4
      have h6 : f + 1 ≤ (f + 1) * (K + 1) :=
        Nat.le_mul_of_pos_right (f + 1) (Nat.succ_pos K)
      omega
  have hm : m ≤ f := by
    subst hK
    simpa using hbud
  exact ⟨hK, hm⟩

/-- Step 3 (Late tail is short on a recent chain): on a chain meeting recency at R,
the tail of blocks from any late index ℓ has length at most f,
and the tip slot + 1 is strictly less than L.slot + n. -/
theorem late_tail_short {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    (hBudget : ByzantineBounded n bad)
    {c : Chain} (hc : ValidChain n c)
    (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {tip : Block} (hTip : c.getLast? = some tip)
    (hRecent : R ≤ tip.slot + n)
    {ℓ : Nat} (hℓ1 : 1 ≤ ℓ) (hℓlen : ℓ < c.length)
    {L : Block} (hL : blockAt? c ℓ = some L)
    (hLsig : ∃ r, L ∈ log r)
    (hLateL : L.slot < Nat.find hLsig) :
    c.length - ℓ ≤ maxByzantine n ∧ tip.slot + 1 < L.slot + n := by
  classical
  have hGprev : G.prev = none := hc.2.2.1 hHead
  have hS : StrictSlots c := hc.2.1
  have hPL : ParentLinked c := hc.2.2.1
  have hMat : MaturedWindowsDense n c := hc.2.2.2
  have hTipAt : blockAt? c (c.length - 1) = some tip := blockAt_getLast hTip
  have hLmem : L ∈ c := by unfold blockAt? at hL; exact List.mem_of_getElem? hL
  have hLs : L.slot ≤ tip.slot := slot_le_tip_of_mem hS hTip hLmem
  set s := tip.slot + 1 - L.slot with hsdef
  have hs_pos : 0 < s := by omega
  set K := s / n with hKdef
  set m := c.length - ℓ with hmdef
  have hwin : ∀ j < K, quorum n ≤ windowCount c (L.slot + j * n) n := by
    intro j hj
    apply hMat hTipAt
    calc L.slot + j * n + n
        = L.slot + (j + 1) * n := by ring
      _ ≤ L.slot + K * n := Nat.add_le_add_left (Nat.mul_le_mul_right n (by omega)) _
      _ ≤ L.slot + s := Nat.add_le_add_left (Nat.div_mul_le_self s n) _
      _ = tip.slot + 1 := by omega
  obtain ⟨P, hPat⟩ : ∃ P, blockAt? c (ℓ - 1) = some P := by
    have : ℓ - 1 < c.length := by omega
    exact ⟨getElem c (ℓ - 1) this, by unfold blockAt?; exact List.getElem?_eq_getElem this⟩
  have hPslot : P.slot < L.slot := strictSlots_lt hS hPat hL (by omega)
  have hbelowP := belowCount_prefix hS hPat
  have hP1 : (ℓ - 1) + 1 = ℓ := by omega
  rw [hP1] at hbelowP
  have hbelowL : ℓ ≤ belowCount c L.slot := by
    have hmono := belowCount_mono c (show P.slot + 1 ≤ L.slot by omega)
    exact le_trans hbelowP hmono
  have hbelowWin := belowCount_windows c L.slot n (quorum n) K hwin
  have hcount : ℓ + quorum n * K ≤ c.length :=
    calc ℓ + quorum n * K ≤ belowCount c L.slot + quorum n * K := Nat.add_le_add_right hbelowL _
      _ ≤ belowCount c (L.slot + K * n) := hbelowWin
      _ ≤ c.length := belowCount_le _ _
  have hdens : quorum n * K ≤ m := by
    have : quorum n * K ≤ c.length - ℓ := Nat.le_sub_of_add_le (by omega)
    exact this
  have hLr : L ∈ log (Nat.find hLsig) := Nat.find_spec hLsig
  have hbadL : bad (Nat.find hLsig) := bad_of_signed_ne_slot hexec hLr (ne_of_lt hLateL)
  have hmodL : L.slot % n = (Nat.find hLsig) % n := hexec.key_match hLr
  have hLn : L.slot + n ≤ Nat.find hLsig := add_le_of_mod_eq_of_lt hmodL hLateL
  have hFpos : 1 ≤ maxByzantine n := maxByzantine_pos_of_bad hn hBudget hbadL
  have h4n : 4 ≤ n := four_le_of_maxByzantine_pos hFpos
  have h2n : 2 ≤ n := by omega
  have hsig : ∀ k, ∃ r, ℓ ≤ k → k < c.length →
      (L.slot + n ≤ r ∧ r ≤ R ∧ bad r ∧ ∃ B, blockAt? c k = some B ∧ B ∈ log r ∧ ∀ r' < r, B ∉ log r') := by
    intro k
    by_cases hk : ℓ ≤ k ∧ k < c.length
    · obtain ⟨hk1, hk2⟩ := hk
      have hB : blockAt? c k = some (getElem c k hk2) := by
        unfold blockAt?; exact List.getElem?_eq_getElem hk2
      obtain ⟨hBne, rB, hrBle, hrBmem⟩ := block_signed hGprev hPL hAvail (by omega) hB
      have hBsig : ∃ r, (getElem c k hk2) ∈ log r := ⟨rB, hrBmem⟩
      have hLateB := late_chain hn hexec hBudget hc hHead hAvail (k - ℓ) hℓ1 hL
        (show blockAt? c (ℓ + (k - ℓ)) = some (getElem c k hk2) by rw [show ℓ + (k - ℓ) = k by omega]; exact hB)
        hLsig hBsig hLateL
      have hmono := sigTime_mono_chain hexec hGprev hPL hAvail (k - ℓ) hℓ1 hL
        (show blockAt? c (ℓ + (k - ℓ)) = some (getElem c k hk2) by rw [show ℓ + (k - ℓ) = k by omega]; exact hB)
        hLsig hBsig
      have hBr : (getElem c k hk2) ∈ log (Nat.find hBsig) := Nat.find_spec hBsig
      have hbadB : bad (Nat.find hBsig) := bad_of_signed_ne_slot hexec hBr (ne_of_lt hLateB)
      refine ⟨Nat.find hBsig, fun _ _ => ⟨?_, ?_, hbadB, getElem c k hk2, hB, hBr, fun r' hr' => Nat.find_min hBsig hr'⟩⟩
      · exact le_trans hLn hmono
      · exact le_trans (Nat.find_min' hBsig hrBmem) hrBle
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose σ hσ using hsig
  have hcard : m ≤ ((Finset.Ico (L.slot + n) (R + 1)).filter fun s => bad s).card := by
    have hmaps : ∀ a ∈ Finset.Ico ℓ c.length, σ a ∈ (Finset.Ico (L.slot + n) (R + 1)).filter fun s => bad s := by
      intro a ha
      rw [Finset.mem_Ico] at ha
      obtain ⟨h0, h1, h2, -⟩ := hσ a ha.1 ha.2
      rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨h0, by omega⟩, h2⟩
    have hinj : Set.InjOn σ (Finset.Ico ℓ c.length) := by
      intro a ha b hb hab
      simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
      by_contra hne
      rcases Nat.lt_or_ge a b with h | h
      · obtain ⟨-, -, -, B, hBat, hBr, hBmin⟩ := hσ a ha.1 ha.2
        obtain ⟨-, -, -, B', hB'at, hB'r, hB'min⟩ := hσ b hb.1 hb.2
        rw [hab] at hBr hBmin
        exact one_real_slot_one_block h2n hexec hGprev hc hAvail (by omega) h hBat hB'at hBr hBmin hB'r hB'min
      · have h' : b < a := by omega
        obtain ⟨-, -, -, B, hBat, hBr, hBmin⟩ := hσ a ha.1 ha.2
        obtain ⟨-, -, -, B', hB'at, hB'r, hB'min⟩ := hσ b hb.1 hb.2
        rw [hab] at hBr hBmin
        exact one_real_slot_one_block h2n hexec hGprev hc hAvail (by omega) h' hB'at hBat hB'r hB'min hBr hBmin
    have := Finset.card_le_card_of_injOn σ hmaps hinj
    rwa [Nat.card_Ico] at this
  have hbound : R + 1 ≤ (L.slot + n) + (K + 1) * n := by
    have hs_bound : s ≤ (K + 1) * n := by
      have hle := le_div_succ_mul s n hn
      change s + 1 ≤ (K + 1) * n at hle
      omega
    calc R + 1 ≤ tip.slot + n + 1 := by omega
      _ = (L.slot + s) + n := by omega
      _ = (L.slot + n) + s := by ring
      _ ≤ (L.slot + n) + (K + 1) * n := Nat.add_le_add_left hs_bound _
  have hbad : ((Finset.Ico (L.slot + n) (R + 1)).filter fun s => bad s).card ≤ maxByzantine n * (K + 1) := by
    calc ((Finset.Ico (L.slot + n) (R + 1)).filter fun s => bad s).card
        ≤ ((Finset.Ico (L.slot + n) ((L.slot + n) + (K + 1) * n)).filter fun s => bad s).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Ico_subset_Ico le_rfl hbound))
      _ ≤ maxByzantine n * (K + 1) := bad_budget_Ico hBudget (L.slot + n) (K + 1)
  have hbud : m ≤ maxByzantine n * (K + 1) := le_trans hcard hbad
  have h2f1 : 2 * maxByzantine n + 1 ≤ quorum n := two_mul_maxByzantine_add_one_le_quorum n hn
  obtain ⟨hK0, hm_le⟩ := div_zero_of_quorum_le h2f1 hdens hbud
  have hs_lt : s < n := by
    by_contra hge
    have hge' : n ≤ s := by omega
    have hdiv_pos : 1 ≤ s / n := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    omega
  refine ⟨hm_le, by omega⟩

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
