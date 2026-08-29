import MoltPetit.Model.Grounded

/-!
# MoltPetit — timed signing model and forged-chain time bounds

The agreement theorems treat the signing log as indexed by *stamped*
slots. That cannot express the cost of **harvesting**: a blob-signing
adversary coercing nodes during its bad slots to sign blocks with
arbitrary stamps. This module adds the real-time axis and proves the
counting bounds that make light-client recency rules sound.

`TimedLog` records what was signed at each **real** slot (by that slot's
producer — the only signing oracle the adversary can reach then). The
id-formation contract (`moltPetit.ts`: a block id hashes the
parent's *signature*) appears as its formal residue, `chain_order`: a
block can only be signed once its parent is available — referencing an
id whose preimage contains a not-yet-existing signature would be
predicting a signature, i.e. an EUF-CMA forgery.

Main results (stated in `Results/Results.lean`): `forged_suffix_time_bound`
and `forged_chain_time_bound` — a chain forged above a fork point first
signed at `r₀` cannot reach tip stamp `r₀ + s` before real slot
`≈ r₀ + 2s` (from genesis: tip stamp `T` needs `≈ 2T`). This module
holds the model and the counting lemmas:

* `sigTime_mono_step` / `sigTime_mono_chain` — first-signing times are
  monotone along any parent-linked chain (`chain_order` + id
  injectivity);
* `one_real_slot_one_block` — at most one block of a valid chain is
  first-signed per real slot: two blocks signed at real slot `r` belong
  to `r`'s producer, so their stamps are ≥ `n` apart; window density
  places a block of a *different* producer between them, and signing
  monotonicity pins its first signing to `r` too — the wrong oracle;
* `belowCount_windows` / `bad_budget_Ico` — density forces `quorum`
  blocks per stamped window while the budget caps bad real slots.
-/

namespace MoltPetit.Model


-- ---------------------------------------------------------------------------
-- Signing-time monotonicity along a chain
-- ---------------------------------------------------------------------------

/-- A chain block at index ≥ 1 is distinct from `G` and was signed by
real slot `R`, given availability of the chain. -/
theorem block_signed {log : TimedLog} {G : Block} (hGprev : G.prev = none)
    {c : Chain} (hPL : ParentLinked c) {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {k : Nat} (hk : 1 ≤ k) {B : Block} (hB : blockAt? c k = some B) :
    B ≠ G ∧ ∃ r, r ≤ R ∧ B ∈ log r := by
  have hBne : B ≠ G := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨P, hP, hprev⟩ := hPL hB
    intro h
    rw [h, hGprev] at hprev
    cases hprev
  have hmem : B ∈ c := by
    unfold blockAt? at hB
    exact List.mem_of_getElem? hB
  rcases hAvail B hmem with rfl | ⟨r, hr, hmem'⟩
  · exact absurd rfl hBne
  · exact ⟨hBne, r, hr, hmem'⟩

/-- One link of monotonicity: a block is first-signed no earlier than its
(non-genesis) parent. -/
theorem sigTime_mono_step {n : Nat} {bad : ByzantineSlots}
    {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    {P B : Block} (hPne : P ≠ G) (hprev : B.prev = some P.id)
    (hPsig : ∃ r, P ∈ log r) (hBsig : ∃ r, B ∈ log r) :
    Nat.find hPsig ≤ Nat.find hBsig := by
  have hBmem : B ∈ log (Nat.find hBsig) := Nat.find_spec hBsig
  obtain ⟨Q, hQid, hQav⟩ := hexec.chain_order hBmem hprev
  have hQsigned : SignedEver log G Q := by
    rcases hQav with rfl | ⟨r, _, hm⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨r, hm⟩
  have hQP : Q = P := hexec.id_inj hQsigned (Or.inr hPsig) hQid
  subst hQP
  rcases hQav with rfl | ⟨r, hrle, hm⟩
  · exact absurd rfl hPne
  · exact le_trans (Nat.find_min' hPsig hm) hrle

/-- First-signing times are monotone along the chain, away from the
genesis head. -/
theorem sigTime_mono_chain {n : Nat} {bad : ByzantineSlots}
    {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G) (hGprev : G.prev = none)
    {c : Chain} (hPL : ParentLinked c) {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R) :
    ∀ (d : Nat) {k : Nat}, 1 ≤ k →
      ∀ {B B' : Block}, blockAt? c k = some B → blockAt? c (k + d) = some B' →
      ∀ (hBsig : ∃ r, B ∈ log r) (hB'sig : ∃ r, B' ∈ log r),
        Nat.find hBsig ≤ Nat.find hB'sig := by
  intro d
  induction d with
  | zero =>
    intro k hk B B' hB hB' hBsig hB'sig
    rw [Nat.add_zero, hB, Option.some.injEq] at hB'
    subst hB'
    exact le_of_eq (by rw [Subsingleton.elim hBsig hB'sig])
  | succ d ih =>
    intro k hk B B' hB hB' hBsig hB'sig
    have hlt : k + d < c.length := by
      unfold blockAt? at hB'
      obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.mp hB'
      omega
    obtain ⟨P, hP⟩ : ∃ P, blockAt? c (k + d) = some P := by
      unfold blockAt?
      exact ⟨getElem c (k + d) hlt, List.getElem?_eq_getElem hlt⟩
    obtain ⟨P', hP'at, hprev⟩ := hPL (show blockAt? c ((k + d) + 1) = some B' from hB')
    have hP2 := hP
    rw [hP'at] at hP2
    have hPP : P' = P := Option.some.inj hP2
    subst hPP
    obtain ⟨hPne, rP, _, hrPmem⟩ := block_signed hGprev hPL hAvail
      (show 1 ≤ k + d by omega) hP'at
    have hPsig : ∃ r, P' ∈ log r := ⟨rP, hrPmem⟩
    exact le_trans (ih hk hB hP'at hBsig hPsig)
      (sigTime_mono_step hexec hPne hprev hPsig hB'sig)

-- ---------------------------------------------------------------------------
-- At most one chain block first-signed per real slot
-- ---------------------------------------------------------------------------

/--
**One real slot, one chain block.** Two distinct blocks of a valid chain
cannot both be first-signed at the same real slot `r`: both would belong
to `r`'s producer, so their stamps differ by at least `n`; the window
just above the earlier one is matured and quorum-dense, so it contains a
block of a *different* producer between them — and signing-time
monotonicity pins that block's first signing to `r` as well,
contradicting that only `r`'s producer signs at `r`.
-/
theorem one_real_slot_one_block {n : Nat} (hn : 2 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G) (hGprev : G.prev = none)
    {c : Chain} (hValid : ValidChain n c) {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {k k' : Nat} (hk : 1 ≤ k) (hkk : k < k')
    {B B' : Block}
    (hB : blockAt? c k = some B) (hB' : blockAt? c k' = some B')
    {r : Nat}
    (hBr : B ∈ log r) (hBmin : ∀ r' < r, B ∉ log r')
    (hB'r : B' ∈ log r) (hB'min : ∀ r' < r, B' ∉ log r') :
    False := by
  obtain ⟨hSeq, hS, hPL, hMat⟩ := hValid
  have hBsig : ∃ r0, B ∈ log r0 := ⟨r, hBr⟩
  have hB'sig : ∃ r0, B' ∈ log r0 := ⟨r, hB'r⟩
  have hfB : Nat.find hBsig = r := (Nat.find_eq_iff hBsig).mpr ⟨hBr, hBmin⟩
  have hfB' : Nat.find hB'sig = r := (Nat.find_eq_iff hB'sig).mpr ⟨hB'r, hB'min⟩
  have hslot : B.slot < B'.slot := strictSlots_lt hS hB hB' hkk
  have hmodB : B.slot % n = r % n := hexec.key_match hBr
  have hmodB' : B'.slot % n = r % n := hexec.key_match hB'r
  -- same producer's stamps are ≥ n apart
  have hge : B.slot + n ≤ B'.slot := by
    have hmod : Nat.ModEq n B.slot B'.slot := hmodB.trans hmodB'.symm
    have hdvd : n ∣ B'.slot - B.slot :=
      (Nat.modEq_iff_dvd' (le_of_lt hslot)).mp hmod
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  -- the window above B is matured at B' and quorum-dense
  have hq : quorum n ≤ windowCount c (B.slot + 1) n := hMat hB' (B.slot + 1) (by omega)
  have hq2 : 2 ≤ quorum n := by
    unfold quorum
    omega
  -- find a window block of a different producer
  obtain ⟨Y, hYW, hYmod⟩ :
      ∃ Y ∈ c.filter (blockInWindow (B.slot + 1) n), Y.slot % n ≠ B.slot % n := by
    by_contra hall
    push Not at hall
    set W := c.filter (blockInWindow (B.slot + 1) n) with hWdef
    have hWlen : 2 ≤ W.length := by
      have he : windowCount c (B.slot + 1) n = W.length := rfl
      omega
    have hWpair : W.Pairwise (fun a b => a.slot < b.slot) :=
      hS.sublist List.filter_sublist
    have hy : ∀ y ∈ W, y.slot = B.slot + n := by
      intro y hyW
      have hyw : blockInWindow (B.slot + 1) n y = true := List.of_mem_filter hyW
      have hyr : y.slot % n = B.slot % n := hall y hyW
      simp only [blockInWindow, decide_eq_true_eq] at hyw
      have hmod : Nat.ModEq n B.slot y.slot := hyr.symm
      have hdvd : n ∣ y.slot - B.slot :=
        (Nat.modEq_iff_dvd' (by omega)).mp hmod
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    have h0 : 0 < W.length := by omega
    have h1 : 1 < W.length := by omega
    have hy0 := hy (W[0]'h0) (List.getElem_mem h0)
    have hy1 := hy (W[1]'h1) (List.getElem_mem h1)
    have hlt := List.pairwise_iff_getElem.mp hWpair 0 1 h0 h1 (by omega)
    omega
  have hYc : Y ∈ c := List.mem_of_mem_filter hYW
  have hYwin : blockInWindow (B.slot + 1) n Y = true := List.of_mem_filter hYW
  simp only [blockInWindow, decide_eq_true_eq] at hYwin
  -- Y sits strictly between B and B' in slots
  have hYltB' : Y.slot < B'.slot := by
    rcases Nat.lt_or_ge Y.slot B'.slot with h | h
    · exact h
    · have hYeq : Y.slot = B'.slot := by omega
      have hBB' : B'.slot % n = B.slot % n := hmodB'.trans hmodB.symm
      rw [hYeq] at hYmod
      exact absurd hBB' hYmod
  -- locate Y's index, strictly between k and k'
  obtain ⟨j, hjlen, hjY⟩ := List.mem_iff_getElem.mp hYc
  have hYat : blockAt? c j = some Y := by
    unfold blockAt?
    rw [List.getElem?_eq_getElem hjlen, hjY]
  have hkj : k < j := by
    rcases Nat.lt_or_ge k j with h | h
    · exact h
    · rcases Nat.eq_or_lt_of_le h with heq | h
      · rw [← heq] at hB
        rw [hYat] at hB
        have hYB := Option.some.inj hB
        subst hYB
        omega
      · have := strictSlots_lt hS hYat hB h
        omega
  have hjk' : j < k' := by
    rcases Nat.lt_or_ge j k' with h | h
    · exact h
    · rcases Nat.eq_or_lt_of_le h with heq | h
      · rw [← heq] at hYat
        rw [hYat] at hB'
        have hYB := Option.some.inj hB'
        subst hYB
        omega
      · have := strictSlots_lt hS hB' hYat h
        omega
  -- Y is signed; its first signing is squeezed to r
  obtain ⟨hYne, rY, _, hrYmem⟩ := block_signed hGprev hPL hAvail
    (show 1 ≤ j by omega) hYat
  have hYsig : ∃ r0, Y ∈ log r0 := ⟨rY, hrYmem⟩
  have h1 := sigTime_mono_chain hexec hGprev hPL hAvail (j - k) hk hB
    (show blockAt? c (k + (j - k)) = some Y by
      rw [show k + (j - k) = j by omega]; exact hYat) hBsig hYsig
  have h2 := sigTime_mono_chain hexec hGprev hPL hAvail (k' - j)
    (show 1 ≤ j by omega) hYat
    (show blockAt? c (j + (k' - j)) = some B' by
      rw [show j + (k' - j) = k' by omega]; exact hB') hYsig hB'sig
  rw [hfB] at h1
  rw [hfB'] at h2
  have hYfind : Nat.find hYsig = r := by omega
  have hYr : Y ∈ log r := hYfind ▸ Nat.find_spec hYsig
  exact hYmod ((hexec.key_match hYr).trans hmodB.symm)

-- ---------------------------------------------------------------------------
-- Counting: density vs the Byzantine budget
-- ---------------------------------------------------------------------------

def belowCount (c : Chain) (k : Nat) : Nat :=
  (c.filter fun B => decide (B.slot < k)).length

theorem belowCount_le (c : Chain) (k : Nat) : belowCount c k ≤ c.length :=
  List.length_filter_le _ _

theorem belowCount_cons (b : Block) (rest : Chain) (k : Nat) :
    belowCount (b :: rest) k = (if b.slot < k then 1 else 0) + belowCount rest k := by
  unfold belowCount
  rw [List.filter_cons]
  by_cases h : b.slot < k
  · simp [h, Nat.add_comm]
  · simp [h]

theorem belowCount_split (c : Chain) (u len : Nat) :
    belowCount c (u + len) = belowCount c u + windowCount c u len := by
  induction c with
  | nil => rfl
  | cons b rest ih =>
    rw [belowCount_cons, belowCount_cons, windowCount_cons]
    by_cases h1 : b.slot < u
    · have h3 : blockInWindow u len b = false := by
        simp only [blockInWindow, decide_eq_false_iff_not]
        omega
      simp only [h3]
      simp [h1, show b.slot < u + len by omega]
      omega
    · by_cases h2 : b.slot < u + len
      · have h3 : blockInWindow u len b = true := by
          simp only [blockInWindow, decide_eq_true_eq]
          omega
        simp only [h3]
        simp [h1, h2]
        omega
      · have h3 : blockInWindow u len b = false := by
          simp only [blockInWindow, decide_eq_false_iff_not]
          omega
        simp only [h3]
        simp [h1, h2]
        omega

theorem belowCount_zero (c : Chain) : belowCount c 0 = 0 := by
  unfold belowCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x _
  simp

/-- Density of `m` consecutive windows starting at `lo` puts `q·m` blocks
above the `lo` prefix. -/
theorem belowCount_windows (c : Chain) (lo n q : Nat) :
    ∀ m, (∀ j < m, q ≤ windowCount c (lo + j * n) n) →
      belowCount c lo + q * m ≤ belowCount c (lo + m * n)
  | 0, _ => by simp
  | m + 1, h => by
    have ih := belowCount_windows c lo n q m fun j hj => h j (by omega)
    have hwin := h m (by omega)
    have hsplit := belowCount_split c (lo + m * n) n
    have he : lo + (m + 1) * n = (lo + m * n) + n := by ring
    rw [he, hsplit]
    calc belowCount c lo + q * (m + 1)
        = (belowCount c lo + q * m) + q := by ring
      _ ≤ belowCount c (lo + m * n) + windowCount c (lo + m * n) n :=
          Nat.add_le_add ih hwin

/-- The first `k₀ + 1` chain blocks all sit strictly below the slot bound
`F.slot + 1`. -/
theorem belowCount_prefix :
    ∀ {c : Chain}, StrictSlots c → ∀ {k₀ : Nat} {F : Block},
      blockAt? c k₀ = some F → k₀ + 1 ≤ belowCount c (F.slot + 1)
  | [], _, k₀, F, hF => by simp [blockAt?] at hF
  | b :: rest, hS, 0, F, hF => by
      have hFb : b = F := by
        simpa [blockAt?] using hF
      subst hFb
      rw [belowCount_cons, if_pos (by omega : b.slot < b.slot + 1)]
      omega
  | b :: rest, hS, k₀ + 1, F, hF => by
      have hFr : blockAt? rest k₀ = some F := by
        simpa [blockAt?] using hF
      have hSr : StrictSlots rest := (List.pairwise_cons.mp hS).2
      have ih := belowCount_prefix hSr hFr
      have hFm : F ∈ rest := by
        unfold blockAt? at hFr
        exact List.mem_of_getElem? hFr
      have hbF : b.slot < F.slot := (List.pairwise_cons.mp hS).1 F hFm
      rw [belowCount_cons, if_pos (by omega : b.slot < F.slot + 1)]
      omega

theorem le_div_succ_mul (D n : Nat) (hn : 1 ≤ n) :
    D + 1 ≤ (D / n + 1) * n := by
  have he : (D / n + 1) * n = n * (D / n) + n := by ring
  rw [he]
  have hmod := Nat.div_add_mod D n
  have hlt : D % n < n := Nat.mod_lt _ (by omega)
  set t := n * (D / n) with ht
  set w := D % n with hw
  omega

open Classical in
/-- The budget caps bad real slots in any union of `k` consecutive
windows starting at `r₀`. -/
theorem bad_budget_Ico {n : Nat} {bad : ByzantineSlots}
    (hBudget : ByzantineBounded n bad) (r₀ : Nat) :
    ∀ k, ((Finset.Ico r₀ (r₀ + k * n)).filter fun s => bad s).card ≤
      maxByzantine n * k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have he : r₀ + (k + 1) * n = (r₀ + k * n) + n := by ring
    rw [he]
    have hsplit : Finset.Ico r₀ (r₀ + k * n + n) =
        Finset.Ico r₀ (r₀ + k * n) ∪ Finset.Ico (r₀ + k * n) (r₀ + k * n + n) := by
      rw [Finset.Ico_union_Ico_eq_Ico (Nat.le_add_right _ _) (Nat.le_add_right _ _)]
    rw [hsplit, Finset.filter_union]
    have hwin : ((Finset.Ico (r₀ + k * n) (r₀ + k * n + n)).filter
        fun s => bad s).card ≤ maxByzantine n := by
      have h := hBudget (r₀ + k * n)
      unfold badSlotsIn at h
      exact h
    calc ((Finset.Ico r₀ (r₀ + k * n)).filter (fun s => bad s) ∪
          (Finset.Ico (r₀ + k * n) (r₀ + k * n + n)).filter (fun s => bad s)).card
        ≤ ((Finset.Ico r₀ (r₀ + k * n)).filter (fun s => bad s)).card +
          ((Finset.Ico (r₀ + k * n) (r₀ + k * n + n)).filter
            (fun s => bad s)).card := Finset.card_union_le _ _
      _ ≤ maxByzantine n * k + maxByzantine n := Nat.add_le_add ih hwin
      _ = maxByzantine n * (k + 1) := by ring

end MoltPetit.Model
