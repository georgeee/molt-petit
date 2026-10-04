import MoltPetit.Model.Model

/-!
# Light-client safety under arbitrary-time key exposure

The core of the timed model. Keys are exposed (Byzantine seats, stolen keys)
at arbitrary real times and sign whatever stamps they verify.

* `exposure_agreement` (Theorem 1): if, of any `n` consecutive stamps, at
  most `maxByzantine n` have a key exposed from `ℓ` slots before the window
  to `φ` slots after it, honest clocks run at most `σ` ahead, and the
  lookback `ℓ` is long enough, then two quorum-dense chains that are fresh
  (their tips within `φ` slots of the real time `R` at which every one of
  their blocks exists) agree at every height at least `n` below both tips.
* `exposure_no_early_signing`: under the same hypotheses, no block of a
  valid chain is signed more than `ℓ` slots before its stamp.
* `exposure_agreement_ever` / `exposure_no_early_signing_ever`: the same
  under the cumulative budget `ExposureBoundedEver` (every exposure before
  the window's freshness deadline counts); agreement then needs no clock.

THE STATEMENTS OF THESE FOUR THEOREMS ARE FIXED. Their exact types are pinned
by `Molt/AxiomsExposureSafety.lean`. Prove them; do not change them. See
`docs/CORE_V2_SPEC.md` for the proof plan.
-/

namespace MoltPetit.Model

theorem signedEver_of_availableAt {log : TimedLog} {G B : Block} {R : Nat}
    (h : AvailableAt log G B R) : SignedEver log G B := by
  rcases h with rfl | ⟨r, _, hr⟩
  · left; rfl
  · right; exact ⟨r, hr⟩

theorem availableAt_mono {log : TimedLog} {G B : Block} {r r' : Nat}
    (hr : r ≤ r') (h : AvailableAt log G B r) : AvailableAt log G B r' := by
  rcases h with rfl | ⟨r0, hr0, hr0log⟩
  · left; rfl
  · right; exact ⟨r0, le_trans hr0 hr, hr0log⟩

theorem mem_of_blockAt {c : Chain} {k : Nat} {B : Block}
    (h : blockAt? c k = some B) : B ∈ c := by
  unfold blockAt? at h
  exact List.mem_of_getElem? h

theorem index_zero_of_eq_head {c : Chain} (hS : StrictSlots c)
    {G : Block} (hHead : blockAt? c 0 = some G)
    {m : Nat} (hm : blockAt? c m = some G) : m = 0 := by
  by_contra hne
  have hlt : 0 < m := Nat.pos_of_ne_zero hne
  have hslot := strictSlots_lt hS hHead hm hlt
  exact (lt_irrefl _) hslot

def SigningExecution.toOn {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G) (Adm : Block → Prop := fun _ => True) :
    SigningExecutionOn Adm exposed log G where
  honest_once := fun _ _ _ _ hr hr' _ _ hslot hexp hexp' =>
    hexec.honest_once hr hr' hslot hexp hexp'
  chain_order := hexec.chain_order
  id_inj := hexec.id_inj

def HonestClock.toOn {σ : Nat} {exposed : Exposure} {log : TimedLog}
    (hClock : HonestClock σ exposed log) (Adm : Block → Prop := fun _ => True) :
    HonestClockOn Adm σ exposed log :=
  fun _r _B hr _hAdm hexp => hClock hr hexp

theorem availableAt_parent_of_signed {n : Nat} {Adm : Block → Prop} {exposed : Exposure}
    {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    {c : Chain} (hc : ValidChain n c)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {k : Nat} {P B : Block}
    (hP : blockAt? c k = some P) (hB : blockAt? c (k + 1) = some B)
    {r : Nat} (hr : B ∈ log r) :
    AvailableAt log G P r := by
  have hPL : ParentLinked c := hc.2.2.1
  have hsucc : ∃ P0 : Block, blockAt? c k = some P0 ∧ B.prev = some P0.id := by
    have hmatch := hPL hB
    exact hmatch
  obtain ⟨P0, hP0at, hprev⟩ := hsucc
  have hP0eq : P0 = P := Option.some.inj (hP0at.symm.trans hP)
  have hprevP : B.prev = some P.id := hP0eq ▸ hprev
  obtain ⟨P', hP'id, hP'avail⟩ := hexec.chain_order hr hprevP
  have hP'signed : SignedEver log G P' := signedEver_of_availableAt hP'avail
  have hPsigned : SignedEver log G P := signedEver_of_availableAt (hAvail P (mem_of_blockAt hP))
  have hEq : P' = P := hexec.id_inj hP'signed hPsigned (by rw [hP'id])
  exact hEq ▸ hP'avail

theorem step_A_ancestor_available {n : Nat} {Adm : Block → Prop} {exposed : Exposure}
    {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    {c : Chain} (hc : ValidChain n c)
    (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R) :
    ∀ (d : Nat) {j k : Nat} (hdiff : j - k = d) (hk : k ≤ j)
      {B A : Block} {r : Nat} (hB : blockAt? c j = some B) (hr : B ∈ log r)
      (hA : blockAt? c k = some A),
      AvailableAt log G A r := by
  intro d
  induction d with
  | zero =>
    intro j k hdiff hk B A r hB hr hA
    have hjk : j = k := by omega
    subst hjk
    have heq : A = B := Option.some.inj (hA.symm.trans hB)
    subst heq
    exact Or.inr ⟨r, le_rfl, hr⟩
  | succ d ih =>
    intro j k hdiff hk B A r hB hr hA
    have hjpos : 0 < j := by omega
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hclen : m < c.length := by
      unfold blockAt? at hB
      have ⟨hlen, _⟩ := List.getElem?_eq_some_iff.mp hB
      omega
    obtain ⟨P, hmAt⟩ : ∃ P, blockAt? c m = some P := by
      unfold blockAt?
      exact ⟨getElem c m hclen, List.getElem?_eq_getElem hclen⟩
    have hPavail := availableAt_parent_of_signed hexec hc hAvail hmAt hB hr
    rcases hPavail with hPG | ⟨rP, hrPle, hrPlog⟩
    · have hm0 : m = 0 := index_zero_of_eq_head hc.2.1 hHead (hPG ▸ hmAt)
      have hk0 : k = 0 := by omega
      subst hk0
      have hAG : A = G := Option.some.inj (hA.symm.trans hHead)
      subst hAG
      exact Or.inl rfl
    · have hkm : k ≤ m := by omega
      have hdiff' : m - k = d := by omega
      have hAavailP := ih hdiff' hkm hmAt hrPlog hA
      exact availableAt_mono hrPle hAavailP

/-- Step A: every ancestor of an available signed block is available at the signing time. -/
theorem ancestor_availableAt {n : Nat} {Adm : Block → Prop} {exposed : Exposure}
    {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    {c : Chain} (hc : ValidChain n c)
    (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {j k : Nat} (hk : k ≤ j)
    {B A : Block} {r : Nat} (hB : blockAt? c j = some B) (hr : B ∈ log r)
    (hA : blockAt? c k = some A) :
    AvailableAt log G A r :=
  step_A_ancestor_available hexec hc hHead hAvail (j - k) rfl hk hB hr hA

theorem two_quorum_sub_n_ge (n : Nat) (hn : 1 ≤ n) :
    maxByzantine n + 1 ≤ 2 * quorum n - n := by
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  unfold maxByzantine quorum
  rcases hmod with h0 | h1 | h2
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
    subst hk; omega
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
    subst hk; omega
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
    subst hk; omega

theorem quorum_ge_maxByzantine_add_two (n : Nat) (hn : 2 ≤ n) :
    maxByzantine n + 2 ≤ quorum n := by
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  unfold maxByzantine quorum
  rcases hmod with h0 | h1 | h2
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
    subst hk; omega
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
    subst hk; omega
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
    subst hk; omega

theorem quorum_ge_maxByzantine_add_one (n : Nat) (hn : 1 ≤ n) :
    maxByzantine n + 1 ≤ quorum n := by
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  unfold maxByzantine quorum
  rcases hmod with h0 | h1 | h2
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
    subst hk; omega
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
    subst hk; omega
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
    subst hk; omega

theorem blockAt_index_le_of_slot_le {c : Chain} (hS : StrictSlots c)
    {k m : Nat} {A B : Block}
    (hA : blockAt? c k = some A) (hB : blockAt? c m = some B)
    (hslot : A.slot ≤ B.slot) : k ≤ m := by
  by_contra hlt
  have hlt' : m < k := Nat.lt_of_not_ge hlt
  have := strictSlots_lt hS hB hA hlt'
  omega

theorem availableAt_of_slot_le {n : Nat} {Adm : Block → Prop} {exposed : Exposure}
    {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {m : Nat} {B : Block} (hB : blockAt? c m = some B) {r : Nat} (hr : B ∈ log r)
    {A : Block} (hA : A ∈ c) (hslot : A.slot ≤ B.slot) :
    AvailableAt log G A r := by
  obtain ⟨k, hk⟩ := exists_blockAt_of_mem hA
  have hkm := blockAt_index_le_of_slot_le hc.2.1 hk hB hslot
  exact ancestor_availableAt hexec hc hHead hAvail hkm hB hr hk

open Classical in
theorem chainSlotsIn_subset_classification {n σ φ : Nat}
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hClock : HonestClock σ exposed log)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {m : Nat} {B : Block} (hB : blockAt? c m = some B)
    {r : Nat} (hr : B ∈ log r) (v : Nat) (hv : v + n ≤ B.slot + 1)
    (hr_lt : r < v + n + φ) :
    chainSlotsIn c v n ⊆
      insert G.slot
        (((Finset.Ico v (v + n)).filter (fun s => ∃ r', r' < v + n + φ ∧ exposed s r')) ∪
         ((Finset.Ico v (v + n)).filter (fun s => s ≤ r + σ))) := by
  intro s hs
  obtain ⟨A, hA_in_c, ⟨hwin_lo, hwin_hi⟩, rfl⟩ := mem_chainSlotsIn.mp hs
  by_cases hAG : A = G
  · subst hAG
    exact Finset.mem_insert_self _ _
  · have hslotle : A.slot ≤ B.slot := by omega
    have hAvailA := availableAt_of_slot_le hexec.toOn hc hHead hAvail hB hr hA_in_c hslotle
    rcases hAvailA with rfl | ⟨rA, hrA, hrAlog⟩
    · contradiction
    · apply Finset.mem_insert_of_mem
      have hIco : A.slot ∈ Finset.Ico v (v + n) := Finset.mem_Ico.mpr ⟨hwin_lo, hwin_hi⟩
      by_cases hexp : exposed A.slot rA
      · apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨hIco, ⟨rA, by omega, hexp⟩⟩
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        have hA_le := hClock hrAlog hexp
        refine ⟨hIco, by omega⟩

theorem genesis_slot_not_mem_chainSlotsIn_of_ne {c : Chain} (hS : StrictSlots c)
    {G : Block} (hHead : blockAt? c 0 = some G)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G) :
    G.slot ∉ chainSlotsIn c B.slot 1 := by
  intro hmem
  obtain ⟨A, _, ⟨hlo, hhi⟩, hslot⟩ := mem_chainSlotsIn.mp hmem
  obtain ⟨m, hm⟩ := exists_blockAt_of_mem hB
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : B = G := Option.some.inj (hm.symm.trans hHead)
    exact hBG this
  have hpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hGltB := strictSlots_lt hS hHead hm hpos
  omega

theorem honest_filter_card_le (v n r σ : Nat) :
    (((Finset.Ico v (v + n)).filter (fun s => s ≤ r + σ)).card) ≤ r + σ + 1 - v := by
  have hsub : ((Finset.Ico v (v + n)).filter (fun s => s ≤ r + σ)) ⊆ Finset.Ico v (r + σ + 1) := by
    intro s hs
    have hs' := Finset.mem_filter.mp hs
    have hIco := Finset.mem_Ico.mp hs'.1
    exact Finset.mem_Ico.mpr ⟨hIco.1, by omega⟩
  have hle := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hle
  exact hle

open Classical in
theorem exposure_no_early_signing_ever {n σ φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hClock : HonestClock σ exposed log)
    (hBudget : ExposureBoundedEver n φ exposed)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G) (hSlot : n - 1 ≤ B.slot)
    {r : Nat} (hr : B ∈ log r) :
    B.slot ≤ r + (n + maxByzantine n + σ + 1 - quorum n) := by
  by_contra hgt
  have hgt' : r + (n + maxByzantine n + σ + 1 - quorum n) < B.slot := Nat.lt_of_not_ge hgt
  let v := B.slot + 1 - n
  have hv : v + n ≤ B.slot + 1 := by omega
  have hr_lt : r < v + n + φ := by omega
  obtain ⟨m, hm⟩ := exists_blockAt_of_mem hB
  have hDense := hc.2.2.2 hm v hv
  have hcard_eq := chainSlotsIn_card hc.2.1 v n
  have hq_le : quorum n ≤ (chainSlotsIn c v n).card := by omega
  have hE_card :
      ((Finset.Ico v (v + n)).filter (fun s => ∃ r', r' < v + n + φ ∧ exposed s r')).card ≤
        maxByzantine n :=
    hBudget v
  have hH_card : ((Finset.Ico v (v + n)).filter (fun s => s ≤ r + σ)).card ≤ r + σ + 1 - v :=
    honest_filter_card_le v n r σ
  have hsub := chainSlotsIn_subset_classification hexec hClock hc hHead hAvail hm hr v hv hr_lt
  rcases Nat.eq_or_lt_of_le hn with rfl | hn2
  · have hnotmem := genesis_slot_not_mem_chainSlotsIn_of_ne hc.2.1 hHead hB hBG
    have hsub' : chainSlotsIn c v 1 ⊆
        ((Finset.Ico v (v + 1)).filter (fun s => ∃ r', r' < v + 1 + φ ∧ exposed s r')) ∪
        ((Finset.Ico v (v + 1)).filter (fun s => s ≤ r + σ)) := by
      intro s hs
      have hmem := hsub hs
      rcases Finset.mem_insert.mp hmem with heq | hmem'
      · subst heq; contradiction
      · exact hmem'
    have hcard_le := calc
      (chainSlotsIn c v 1).card ≤
          (((Finset.Ico v (v + 1)).filter (fun s => ∃ r', r' < v + 1 + φ ∧ exposed s r')) ∪
            ((Finset.Ico v (v + 1)).filter (fun s => s ≤ r + σ))).card :=
        Finset.card_le_card hsub'
      _ ≤ ((Finset.Ico v (v + 1)).filter (fun s => ∃ r', r' < v + 1 + φ ∧ exposed s r')).card +
          ((Finset.Ico v (v + 1)).filter (fun s => s ≤ r + σ)).card := Finset.card_union_le _ _
    unfold maxByzantine quorum at *
    omega
  · have hcard_le := calc
      (chainSlotsIn c v n).card ≤
          (insert G.slot (((Finset.Ico v (v + n)).filter
            (fun s => ∃ r', r' < v + n + φ ∧ exposed s r')) ∪
            ((Finset.Ico v (v + n)).filter (fun s => s ≤ r + σ)))).card :=
        Finset.card_le_card hsub
      _ ≤ (((Finset.Ico v (v + n)).filter (fun s => ∃ r', r' < v + n + φ ∧ exposed s r')) ∪
            ((Finset.Ico v (v + n)).filter (fun s => s ≤ r + σ))).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ ((Finset.Ico v (v + n)).filter (fun s => ∃ r', r' < v + n + φ ∧ exposed s r')).card +
          ((Finset.Ico v (v + n)).filter (fun s => s ≤ r + σ)).card + 1 := by
        have := Finset.card_union_le
          ((Finset.Ico v (v + n)).filter (fun s => ∃ r', r' < v + n + φ ∧ exposed s r'))
          ((Finset.Ico v (v + n)).filter (fun s => s ≤ r + σ))
        omega
    have hq_add2 := quorum_ge_maxByzantine_add_two n hn2
    omega

theorem common_prefix_step {n : Nat} {Adm : Block → Prop} {exposed : Exposure}
    {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {k : Nat} {B : Block}
    (hB : blockAt? c (k + 1) = some B) (hB' : blockAt? c' (k + 1) = some B) :
    blockAt? c k = blockAt? c' k := by
  have hPL : ParentLinked c := hc.2.2.1
  have hPL' : ParentLinked c' := hc'.2.2.1
  obtain ⟨P, hP, hprev⟩ := hPL hB
  obtain ⟨P', hP', hprev'⟩ := hPL' hB'
  have hid : P.id = P'.id := by
    have : some P.id = some P'.id := hprev.symm.trans hprev'
    exact Option.some.inj this
  have hPmem : P ∈ c := mem_of_blockAt hP
  have hP'mem : P' ∈ c' := mem_of_blockAt hP'
  have hPsigned : SignedEver log G P := signedEver_of_availableAt (hAvail P hPmem)
  have hP'signed : SignedEver log G P' := signedEver_of_availableAt (hAvail' P' hP'mem)
  have hEq : P = P' := hexec.id_inj hPsigned hP'signed hid
  rw [hP, hP', hEq]

theorem common_prefix_of_common_block {n : Nat} {Adm : Block → Prop} {exposed : Exposure}
    {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {j : Nat} {X : Block}
    (hX : blockAt? c j = some X) (hX' : blockAt? c' j = some X) :
    ∀ k ≤ j, blockAt? c k = blockAt? c' k := by
  intro k hk
  have hdiff : ∃ d, k + d = j := ⟨j - k, by omega⟩
  obtain ⟨d, hd⟩ := hdiff
  clear hk
  induction d generalizing k with
  | zero =>
    have : k = j := by omega
    subst this
    rw [hX, hX']
  | succ d ih =>
    have hsucc_le : k + 1 ≤ j := by omega
    have hsucc_eq : (k + 1) + d = j := by omega
    have ih_applied := ih (k + 1) hsucc_eq
    obtain ⟨B, hB⟩ := exists_blockAt_of_le hsucc_le hX
    have hB' : blockAt? c' (k + 1) = some B := ih_applied ▸ hB
    exact common_prefix_step hexec hc hc' hAvail hAvail' hB hB'

theorem common_prefix_of_mem_both {n : Nat} {Adm : Block → Prop} {exposed : Exposure}
    {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {j j' : Nat} {X : Block}
    (hX : blockAt? c j = some X) (hX' : blockAt? c' j' = some X) :
    j = j' ∧ ∀ k ≤ j, blockAt? c k = blockAt? c' k := by
  have hj : X.height = j := hc.1 hX
  have hj' : X.height = j' := hc'.1 hX'
  have heq : j = j' := hj.symm.trans hj'
  subst heq
  exact ⟨rfl, common_prefix_of_common_block hexec hc hc' hAvail hAvail' hX hX'⟩

theorem blockAt_getLast {ch : Chain} {tip : Block}
    (hTip : ch.getLast? = some tip) :
    blockAt? ch (ch.length - 1) = some tip := by
  unfold blockAt?
  rw [← List.getLast?_eq_getElem?]
  exact hTip

theorem slot_ge_of_height_gap {c : Chain} (hS : StrictSlots c)
    {i : Nat} {Bi : Block} (hi : blockAt? c i = some Bi) :
    ∀ {j : Nat} {Bj : Block}, blockAt? c j = some Bj → i ≤ j →
      Bi.slot + (j - i) ≤ Bj.slot := by
  intro j
  induction j with
  | zero =>
    intro Bj hj hij
    have hiz : i = 0 := Nat.eq_zero_of_le_zero hij
    subst hiz; rw [hi] at hj; simp [Option.some.inj hj]
  | succ j' ih =>
    intro Bj hj hij
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · rw [hi] at hj; simp [Option.some.inj hj]
    · have hij' : i ≤ j' := Nat.lt_succ_iff.mp hlt
      obtain ⟨Bj', hBj'⟩ := exists_blockAt_of_le (Nat.le_succ j') hj
      have hIH := ih hBj' hij'
      have hStep : Bj'.slot < Bj.slot := strictSlots_lt hS hBj' hj (Nat.lt_succ_self j')
      omega

open Classical in
theorem exposure_agreement_of_filter {n : Nat} {Adm : Block → Prop} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    (hHead : blockAt? c 0 = some G) (hHead' : blockAt? c' 0 = some G)
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    {h : Nat} (hDeep : h + n < c.length) (hDeep' : h + n < c'.length)
    {F : Finset Nat} (hF_card : F.card ≤ maxByzantine n)
    (hConflict : ∀ s ∈ chainSlotsIn c (min tip.slot tip'.slot + 1 - n) n ∩
                          chainSlotsIn c' (min tip.slot tip'.slot + 1 - n) n,
      (∀ X ∈ c, ∀ X' ∈ c', X.slot = s → X'.slot = s → X = X') ∨ s ∈ F) :
    blockAt? c h = blockAt? c' h := by
  let m := min tip.slot tip'.slot
  let v := m + 1 - n
  have hTipAt : blockAt? c (c.length - 1) = some tip := blockAt_getLast hTip
  have hTipAt' : blockAt? c' (c'.length - 1) = some tip' := blockAt_getLast hTip'
  have hclen : n ≤ c.length - 1 := by omega
  have hclen' : n ≤ c'.length - 1 := by omega
  have htip_ge : n ≤ tip.slot := by
    have hgap := slot_ge_of_height_gap hc.2.1 hHead hTipAt (by omega)
    omega
  have htip'_ge : n ≤ tip'.slot := by
    have hgap := slot_ge_of_height_gap hc'.2.1 hHead' hTipAt' (by omega)
    omega
  have hm_ge : n ≤ m := by omega
  have hvn : v + n = m + 1 := by omega
  have hv_le : v + n ≤ tip.slot + 1 := by omega
  have hv_le' : v + n ≤ tip'.slot + 1 := by omega
  have hDense := hc.2.2.2 hTipAt v hv_le
  have hDense' := hc'.2.2.2 hTipAt' v hv_le'
  have hcard_eq := chainSlotsIn_card hc.2.1 v n
  have hcard_eq' := chainSlotsIn_card hc'.2.1 v n
  have hS_card : quorum n ≤ (chainSlotsIn c v n).card := by omega
  have hS'_card : quorum n ≤ (chainSlotsIn c' v n).card := by omega
  set S := chainSlotsIn c v n
  set S' := chainSlotsIn c' v n
  have hUnionSub : S ∪ S' ⊆ Finset.Ico v (v + n) :=
    Finset.union_subset chainSlotsIn_subset_Ico chainSlotsIn_subset_Ico
  have hUnionCard : (S ∪ S').card ≤ n := by
    have := Finset.card_le_card hUnionSub
    rw [Nat.card_Ico] at this
    omega
  have hInterCard : maxByzantine n + 1 ≤ (S ∩ S').card := by
    have := Finset.card_inter_add_card_union S S'
    have h2q := two_quorum_sub_n_ge n hn
    omega
  have hCommon : ∃ s ∈ S ∩ S', ∀ X ∈ c, ∀ X' ∈ c', X.slot = s → X'.slot = s → X = X' := by
    by_contra hNone
    push Not at hNone
    have hSubF : S ∩ S' ⊆ F := by
      intro s hs
      rcases hConflict s hs with hAgree | hsF
      · obtain ⟨X, hXc, X', hX'c, hXslot, hX'slot, hNe⟩ := hNone s hs
        have := hAgree X hXc X' hX'c hXslot hX'slot
        contradiction
      · exact hsF
    have hle := Finset.card_le_card hSubF
    omega
  obtain ⟨s, hs, hAgree⟩ := hCommon
  have hsS : s ∈ S := (Finset.mem_inter.mp hs).1
  have hsS' : s ∈ S' := (Finset.mem_inter.mp hs).2
  obtain ⟨X, hXc, ⟨_, _⟩, rfl⟩ := mem_chainSlotsIn.mp hsS
  obtain ⟨X', hX'c, ⟨_, _⟩, hX's⟩ := mem_chainSlotsIn.mp hsS'
  have hXX' : X = X' := hAgree X hXc X' hX'c rfl hX's
  subst hXX'
  obtain ⟨j, hj⟩ := exists_blockAt_of_mem hXc
  obtain ⟨j', hj'⟩ := exists_blockAt_of_mem hX'c
  have ⟨hjj', hPrefix⟩ := common_prefix_of_mem_both hexec hc hc' hAvail hAvail' hj hj'
  subst hjj'
  rcases le_total tip.slot tip'.slot with hmin | hmin
  · have hmeq : m = tip.slot := min_eq_left hmin
    have hj_le : j ≤ c.length - 1 := by
      unfold blockAt? at hj
      obtain ⟨hlen, _⟩ := List.getElem?_eq_some_iff.mp hj
      omega
    have hgap := slot_ge_of_height_gap hc.2.1 hj hTipAt hj_le
    have hj_ge : c.length - n ≤ j := by omega
    have hle_j : h ≤ j := by omega
    exact hPrefix h hle_j
  · have hmeq : m = tip'.slot := min_eq_right hmin
    have hj'_le : j ≤ c'.length - 1 := by
      unfold blockAt? at hj'
      obtain ⟨hlen, _⟩ := List.getElem?_eq_some_iff.mp hj'
      omega
    have hgap := slot_ge_of_height_gap hc'.2.1 hj' hTipAt' hj'_le
    have hj_ge : c'.length - n ≤ j := by omega
    have hle_j : h ≤ j := by omega
    exact hPrefix h hle_j

open Classical in
theorem exposure_agreement_ever {n φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hBudget : ExposureBoundedEver n φ exposed)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    (hHead : blockAt? c 0 = some G) (hHead' : blockAt? c' 0 = some G)
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ) (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat} (hDeep : h + n < c.length) (hDeep' : h + n < c'.length) :
    blockAt? c h = blockAt? c' h := by
  let m := min tip.slot tip'.slot
  let v := m + 1 - n
  let F := (Finset.Ico v (v + n)).filter (fun s => ∃ r', r' < v + n + φ ∧ exposed s r')
  have hF_card : F.card ≤ maxByzantine n := hBudget v
  apply exposure_agreement_of_filter hn hexec.toOn hc hc' hHead hHead' hAvail hAvail'
    hTip hTip' hDeep hDeep' hF_card
  intro s hs
  by_cases hAgree : ∀ X ∈ c, ∀ X' ∈ c', X.slot = s → X'.slot = s → X = X'
  · exact Or.inl hAgree
  · right
    have hsS : s ∈ chainSlotsIn c v n := (Finset.mem_inter.mp hs).1
    have hIco : s ∈ Finset.Ico v (v + n) := chainSlotsIn_subset_Ico hsS
    push Not at hAgree
    obtain ⟨X, hXc, X', hX'c, hXslot, hX'slot, hNe⟩ := hAgree
    have hX_ne_G : X ≠ G := by
      intro hXG
      have hG_in_c' : G ∈ c' := mem_of_blockAt hHead'
      obtain ⟨k, hk⟩ := exists_blockAt_of_mem hX'c
      rcases k with rfl | k
      · have : X' = G := Option.some.inj (hk.symm.trans hHead')
        have : X = X' := by rw [hXG, this]
        exact hNe this
      · have hlt := strictSlots_lt hc'.2.1 hHead' hk (by omega)
        have : G.slot = X'.slot := by rw [← hXG, hXslot, hX'slot]
        omega
    have hX'_ne_G : X' ≠ G := by
      intro hX'G
      have hG_in_c : G ∈ c := mem_of_blockAt hHead
      obtain ⟨k, hk⟩ := exists_blockAt_of_mem hXc
      rcases k with rfl | k
      · have : X = G := Option.some.inj (hk.symm.trans hHead)
        have : X = X' := by rw [this, hX'G]
        exact hNe this
      · have hlt := strictSlots_lt hc.2.1 hHead hk (by omega)
        have : G.slot = X.slot := by rw [← hX'G, hX'slot, hXslot]
        omega
    have hAvailX := hAvail X hXc
    have hAvailX' := hAvail' X' hX'c
    obtain ⟨r, hrle, hrlog⟩ : ∃ r ≤ R, X ∈ log r := by
      rcases hAvailX with rfl | ⟨r, hrle, hrlog⟩
      · contradiction
      · exact ⟨r, hrle, hrlog⟩
    obtain ⟨r', hr'le, hr'log⟩ : ∃ r' ≤ R, X' ∈ log r' := by
      rcases hAvailX' with rfl | ⟨r', hr'le, hr'log⟩
      · contradiction
      · exact ⟨r', hr'le, hr'log⟩
    have hExp : exposed s r ∨ exposed s r' := by
      by_contra hNotExp
      push Not at hNotExp
      have hslotEq : X.slot = X'.slot := by rw [hXslot, hX'slot]
      have hNot1 : ¬ exposed X.slot r := by rw [hXslot]; exact hNotExp.1
      have hNot2 : ¬ exposed X.slot r' := by rw [hXslot]; exact hNotExp.2
      have hEq := hexec.honest_once hrlog hr'log hslotEq hNot1 hNot2
      exact hNe hEq
    have hR_lt : R < v + n + φ := by
      have htip_ge : n ≤ tip.slot := by
        have hTipAt : blockAt? c (c.length - 1) = some tip := blockAt_getLast hTip
        have hgap := slot_ge_of_height_gap hc.2.1 hHead hTipAt (by omega)
        omega
      have htip'_ge : n ≤ tip'.slot := by
        have hTipAt' : blockAt? c' (c'.length - 1) = some tip' := blockAt_getLast hTip'
        have hgap := slot_ge_of_height_gap hc'.2.1 hHead' hTipAt' (by omega)
        omega
      omega
    apply Finset.mem_filter.mpr
    refine ⟨hIco, ?_⟩
    rcases hExp with hexp | hexp
    · exact ⟨r, by omega, hexp⟩
    · exact ⟨r', by omega, hexp⟩

theorem quorum_le_n_add_maxByzantine (n : Nat) (hn : 1 ≤ n) :
    quorum n ≤ n + maxByzantine n := by
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  unfold maxByzantine quorum
  rcases hmod with h0 | h1 | h2
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
    subst hk; omega
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
    subst hk; omega
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
    subst hk; omega

theorem head_slot_min {c : Chain} (hS : StrictSlots c) {G : Block}
    (hHead : blockAt? c 0 = some G) : ∀ B ∈ c, G.slot ≤ B.slot := by
  intro B hB
  obtain ⟨k, hk⟩ := exists_blockAt_of_mem hB
  cases k with
  | zero => rw [hHead] at hk; injection hk with hk; rw [hk]
  | succ k => exact Nat.le_of_lt (strictSlots_lt hS hHead hk (Nat.succ_pos k))

theorem genesis_slot_lt {n : Nat} (hn : 1 ≤ n)
    {c : Chain} (hc : ValidChain n c) {G : Block} (hHead : blockAt? c 0 = some G)
    {m : Nat} {B : Block} (hm : blockAt? c m = some B) (hslot : n - 1 ≤ B.slot) :
    G.slot < n := by
  have hv : 0 + n ≤ B.slot + 1 := by omega
  have hDense := hc.2.2.2 hm 0 hv
  have hcard_eq := chainSlotsIn_card hc.2.1 0 n
  have hpos : 0 < (chainSlotsIn c 0 n).card := by
    unfold quorum at hDense; omega
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  obtain ⟨A, hAc, ⟨_, hlt⟩, rfl⟩ := mem_chainSlotsIn.mp hs
  have hmin := head_slot_min hc.2.1 hHead A hAc
  omega

open Classical in
theorem exposure_no_early_signing_at_index_on {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {Adm : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    (hClock : HonestClockOn Adm σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    (hAdm : ∀ B ∈ c, B ≠ G → Adm B)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (m : Nat) :
    ∀ {B : Block} (hm : blockAt? c m = some B) (hBG : B ≠ G)
    {r : Nat} (hr : B ∈ log r),
    B.slot ≤ r + ℓ := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro B hm hBG r hr
    by_contra hgt
    have hgt' : r + ℓ < B.slot := Nat.lt_of_not_ge hgt
    have hql := quorum_le_n_add_maxByzantine n hn
    have hsigma_le : σ ≤ ℓ := by omega
    have hexp_B : exposed B.slot r := by
      by_contra hnot_exp
      have hclock := hClock hr (hAdm B (mem_of_blockAt hm) hBG) hnot_exp
      omega
    rcases Nat.eq_or_lt_of_le hn with rfl | hn2
    · -- n = 1
      have hl_ge : 1 ≤ ℓ := by
        unfold maxByzantine quorum at hL'
        omega
      have hs_ge : 2 ≤ B.slot := by omega
      let v' := B.slot - 1
      have hv' : v' + 1 ≤ B.slot + 1 := by omega
      have hDense := hc.2.2.2 hm v' hv'
      have hcard_eq := chainSlotsIn_card hc.2.1 v' 1
      have hpos : 0 < (chainSlotsIn c v' 1).card := by
        unfold quorum at hDense; omega
      obtain ⟨s_prev, hs_prev⟩ := Finset.card_pos.mp hpos
      obtain ⟨A, hAc, ⟨hwin_lo, hwin_hi⟩, rfl⟩ := mem_chainSlotsIn.mp hs_prev
      have hAslot : A.slot = B.slot - 1 := by omega
      obtain ⟨k, hk⟩ := exists_blockAt_of_mem hAc
      have hkm : k < m := by
        have hle := blockAt_index_le_of_slot_le hc.2.1 hk hm (by omega)
        have hne : k ≠ m := by
          rintro rfl
          rw [hk] at hm
          have : A.slot = B.slot := congrArg Block.slot (Option.some.inj hm)
          omega
        omega
      by_cases hAG : A = G
      · subst hAG
        have hG_lt := genesis_slot_lt (by omega) hc hHead hm (by omega)
        omega
      · have hAvailA := availableAt_of_slot_le hexec hc hHead hAvail hm hr hAc (by omega)
        rcases hAvailA with rfl | ⟨rA, hrAle, hrAlog⟩
        · contradiction
        · by_cases hexpA : exposed A.slot rA
          · have hAIH := ih k hkm hk hAG hrAlog
            let F' := (Finset.Ico v' (v' + 1)).filter
              (fun t => ∃ r', v' ≤ r' + ℓ ∧ r' < v' + 1 + φ ∧ exposed t r')
            have hBudget' : F'.card ≤ maxByzantine 1 := hBudget v'
            have hmemF' : A.slot ∈ F' := by
              apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ⟨rA, by omega, by omega, hexpA⟩⟩
            have hposF' : 0 < F'.card := Finset.card_pos.mpr ⟨A.slot, hmemF'⟩
            unfold maxByzantine at hBudget'
            omega
          · have hClockA := hClock hrAlog (hAdm A hAc hAG) hexpA
            unfold maxByzantine quorum at hL'
            omega
    · -- n ≥ 2
      let s := B.slot
      let v := s + 1 - n
      have hsn : n ≤ s := by omega
      have hv : v + n ≤ s + 1 := by omega
      have hDense := hc.2.2.2 hm v hv
      have hcard_eq := chainSlotsIn_card hc.2.1 v n
      have hq_le : quorum n ≤ (chainSlotsIn c v n).card := by omega
      let F := (Finset.Ico v (v + n)).filter (fun t => ∃ r', v ≤ r' + ℓ ∧ r' < v + n + φ ∧ exposed t r')
      have hF_card : F.card ≤ maxByzantine n := hBudget v
      let H := (Finset.Ico v (v + n)).filter (fun t => t ≤ r + σ)
      have hH_card : H.card ≤ r + σ + 1 - v := honest_filter_card_le v n r σ
      by_cases hv_le : v ≤ r + ℓ
      · -- Case (i): v ≤ r + ℓ
        have hsub : chainSlotsIn c v n ⊆ insert G.slot (F ∪ H) := by
          intro t ht
          obtain ⟨A, hAc, ⟨hwin_lo, hwin_hi⟩, rfl⟩ := mem_chainSlotsIn.mp ht
          by_cases hAG : A = G
          · subst hAG; exact Finset.mem_insert_self _ _
          · apply Finset.mem_insert_of_mem
            have hAvailA := availableAt_of_slot_le hexec hc hHead hAvail hm hr hAc (by omega)
            rcases hAvailA with rfl | ⟨rA, hrAle, hrAlog⟩
            · contradiction
            · by_cases hexpA : exposed A.slot rA
              · apply Finset.mem_union_left
                apply Finset.mem_filter.mpr
                refine ⟨Finset.mem_Ico.mpr ⟨hwin_lo, hwin_hi⟩, ?_⟩
                by_cases hAB : A = B
                · subst hAB
                  refine ⟨r, hv_le, by omega, hexp_B⟩
                · obtain ⟨k, hk⟩ := exists_blockAt_of_mem hAc
                  have hkm : k < m := by
                    have hle := blockAt_index_le_of_slot_le hc.2.1 hk hm (by omega)
                    have hne : k ≠ m := by
                      rintro rfl
                      rw [hk] at hm
                      have : A = B := Option.some.inj hm
                      contradiction
                    omega
                  have hAIH := ih k hkm hk hAG hrAlog
                  refine ⟨rA, by omega, by omega, hexpA⟩
              · apply Finset.mem_union_right
                apply Finset.mem_filter.mpr
                have hClockA := hClock hrAlog (hAdm A hAc hAG) hexpA
                refine ⟨Finset.mem_Ico.mpr ⟨hwin_lo, hwin_hi⟩, by omega⟩
        have hcard_le := calc
          (chainSlotsIn c v n).card ≤ (insert G.slot (F ∪ H)).card := Finset.card_le_card hsub
          _ ≤ (F ∪ H).card + 1 := Finset.card_insert_le _ _
          _ ≤ F.card + H.card + 1 := by
            have := Finset.card_union_le F H; omega
        have hq_add2 := quorum_ge_maxByzantine_add_two n hn2
        omega
      · -- Case (ii): r + ℓ < v
        push Not at hv_le
        have hG_not_mem : G.slot ∉ chainSlotsIn c v n := by
          intro hmem
          obtain ⟨A, hAc, ⟨hwin_lo, _⟩, heq⟩ := mem_chainSlotsIn.mp hmem
          have hG_lt := genesis_slot_lt (by omega) hc hHead hm (by omega)
          omega
        have hsub : chainSlotsIn c v n ⊆ insert B.slot F := by
          intro t ht
          obtain ⟨A, hAc, ⟨hwin_lo, hwin_hi⟩, rfl⟩ := mem_chainSlotsIn.mp ht
          by_cases hAB : A = B
          · subst hAB; exact Finset.mem_insert_self _ _
          · apply Finset.mem_insert_of_mem
            by_cases hAG : A = G
            · subst hAG
              have := genesis_slot_lt (by omega) hc hHead hm (by omega)
              omega
            · have hAvailA := availableAt_of_slot_le hexec hc hHead hAvail hm hr hAc (by omega)
              rcases hAvailA with rfl | ⟨rA, hrAle, hrAlog⟩
              · contradiction
              · by_cases hexpA : exposed A.slot rA
                · apply Finset.mem_filter.mpr
                  refine ⟨Finset.mem_Ico.mpr ⟨hwin_lo, hwin_hi⟩, ?_⟩
                  obtain ⟨k, hk⟩ := exists_blockAt_of_mem hAc
                  have hkm : k < m := by
                    have hle := blockAt_index_le_of_slot_le hc.2.1 hk hm (by omega)
                    have hne : k ≠ m := by
                      rintro rfl
                      rw [hk] at hm
                      have : A = B := Option.some.inj hm
                      contradiction
                    omega
                  have hAIH := ih k hkm hk hAG hrAlog
                  refine ⟨rA, by omega, by omega, hexpA⟩
                · have hClockA := hClock hrAlog (hAdm A hAc hAG) hexpA
                  omega
        have hcard_le := calc
          (chainSlotsIn c v n).card ≤ (insert B.slot F).card := Finset.card_le_card hsub
          _ ≤ F.card + 1 := Finset.card_insert_le _ _
        have hq_add2 := quorum_ge_maxByzantine_add_two n hn2
        omega

open Classical in
theorem exposure_no_early_signing_on {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {Adm : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    (hClock : HonestClockOn Adm σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    (hAdm : ∀ B ∈ c, B ≠ G → Adm B)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G)
    {r : Nat} (hr : B ∈ log r) :
    B.slot ≤ r + ℓ := by
  obtain ⟨m, hm⟩ := exists_blockAt_of_mem hB
  exact exposure_no_early_signing_at_index_on hn hexec hClock hBudget hL hL'
    hc hHead hAdm hAvail m hm hBG hr

open Classical in
theorem exposure_no_early_signing {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hClock : HonestClock σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G)
    {r : Nat} (hr : B ∈ log r) :
    B.slot ≤ r + ℓ :=
  exposure_no_early_signing_on hn hexec.toOn hClock.toOn hBudget hL hL'
    hc hHead (fun _ _ _ => trivial) hAvail hB hBG hr

open Classical in
theorem exposure_agreement_on {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {Adm : Block → Prop} {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecutionOn Adm exposed log G)
    (hClock : HonestClockOn Adm σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    (hHead : blockAt? c 0 = some G) (hHead' : blockAt? c' 0 = some G)
    (hAdm : ∀ B ∈ c, B ≠ G → Adm B) (hAdm' : ∀ B ∈ c', B ≠ G → Adm B)
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ) (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat} (hDeep : h + n < c.length) (hDeep' : h + n < c'.length) :
    blockAt? c h = blockAt? c' h := by
  let m := min tip.slot tip'.slot
  let v := m + 1 - n
  let F := (Finset.Ico v (v + n)).filter (fun s => ∃ r', v ≤ r' + ℓ ∧ r' < v + n + φ ∧ exposed s r')
  have hF_card : F.card ≤ maxByzantine n := hBudget v
  apply exposure_agreement_of_filter hn hexec hc hc' hHead hHead' hAvail hAvail'
    hTip hTip' hDeep hDeep' hF_card
  intro s hs
  by_cases hAgree : ∀ X ∈ c, ∀ X' ∈ c', X.slot = s → X'.slot = s → X = X'
  · exact Or.inl hAgree
  · right
    have hsS : s ∈ chainSlotsIn c v n := (Finset.mem_inter.mp hs).1
    have hIco : s ∈ Finset.Ico v (v + n) := chainSlotsIn_subset_Ico hsS
    push Not at hAgree
    obtain ⟨X, hXc, X', hX'c, hXslot, hX'slot, hNe⟩ := hAgree
    have hX_ne_G : X ≠ G := by
      intro hXG
      have hG_in_c' : G ∈ c' := mem_of_blockAt hHead'
      obtain ⟨k, hk⟩ := exists_blockAt_of_mem hX'c
      rcases k with rfl | k
      · have : X' = G := Option.some.inj (hk.symm.trans hHead')
        have : X = X' := by rw [hXG, this]
        exact hNe this
      · have hlt := strictSlots_lt hc'.2.1 hHead' hk (by omega)
        have : G.slot = X'.slot := by rw [← hXG, hXslot, hX'slot]
        omega
    have hX'_ne_G : X' ≠ G := by
      intro hX'G
      have hG_in_c : G ∈ c := mem_of_blockAt hHead
      obtain ⟨k, hk⟩ := exists_blockAt_of_mem hXc
      rcases k with rfl | k
      · have : X = G := Option.some.inj (hk.symm.trans hHead)
        have : X = X' := by rw [this, hX'G]
        exact hNe this
      · have hlt := strictSlots_lt hc.2.1 hHead hk (by omega)
        have : G.slot = X.slot := by rw [← hX'G, hX'slot, hXslot]
        omega
    have hAvailX := hAvail X hXc
    have hAvailX' := hAvail' X' hX'c
    obtain ⟨r, hrle, hrlog⟩ : ∃ r ≤ R, X ∈ log r := by
      rcases hAvailX with rfl | ⟨r, hrle, hrlog⟩
      · contradiction
      · exact ⟨r, hrle, hrlog⟩
    obtain ⟨r', hr'le, hr'log⟩ : ∃ r' ≤ R, X' ∈ log r' := by
      rcases hAvailX' with rfl | ⟨r', hr'le, hr'log⟩
      · contradiction
      · exact ⟨r', hr'le, hr'log⟩
    have hExp : exposed s r ∨ exposed s r' := by
      by_contra hNotExp
      push Not at hNotExp
      have hslotEq : X.slot = X'.slot := by rw [hXslot, hX'slot]
      have hNot1 : ¬ exposed X.slot r := by rw [hXslot]; exact hNotExp.1
      have hNot2 : ¬ exposed X.slot r' := by rw [hXslot]; exact hNotExp.2
      have hEq := hexec.honest_once hrlog hr'log (hAdm X hXc hX_ne_G) (hAdm' X' hX'c hX'_ne_G)
        hslotEq hNot1 hNot2
      exact hNe hEq
    have hR_lt : R < v + n + φ := by
      have htip_ge : n ≤ tip.slot := by
        have hTipAt : blockAt? c (c.length - 1) = some tip := blockAt_getLast hTip
        have hgap := slot_ge_of_height_gap hc.2.1 hHead hTipAt (by omega)
        omega
      have htip'_ge : n ≤ tip'.slot := by
        have hTipAt' : blockAt? c' (c'.length - 1) = some tip' := blockAt_getLast hTip'
        have hgap := slot_ge_of_height_gap hc'.2.1 hHead' hTipAt' (by omega)
        omega
      omega
    have hX_early := exposure_no_early_signing_on hn hexec hClock hBudget hL hL'
      hc hHead hAdm hAvail hXc hX_ne_G hrlog
    have hX'_early := exposure_no_early_signing_on hn hexec hClock hBudget hL hL'
      hc' hHead' hAdm' hAvail' hX'c hX'_ne_G hr'log
    have ⟨hs_lo, _⟩ := Finset.mem_Ico.mp hIco
    apply Finset.mem_filter.mpr
    refine ⟨hIco, ?_⟩
    rcases hExp with hexp | hexp
    · refine ⟨r, by omega, by omega, hexp⟩
    · refine ⟨r', by omega, by omega, hexp⟩

open Classical in
theorem exposure_agreement {n σ ℓ φ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hClock : HonestClock σ exposed log)
    (hBudget : ExposureBounded n ℓ φ exposed)
    (hL : n ≤ ℓ + 1) (hL' : n + maxByzantine n + σ + 1 ≤ quorum n + ℓ)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    (hHead : blockAt? c 0 = some G) (hHead' : blockAt? c' 0 = some G)
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hRecent : R ≤ tip.slot + φ) (hRecent' : R ≤ tip'.slot + φ)
    {h : Nat} (hDeep : h + n < c.length) (hDeep' : h + n < c'.length) :
    blockAt? c h = blockAt? c' h :=
  exposure_agreement_on hn hexec.toOn hClock.toOn hBudget hL hL'
    hc hc' hHead hHead' (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    hAvail hAvail' hTip hTip' hRecent hRecent' hDeep hDeep'

end MoltPetit.Model
