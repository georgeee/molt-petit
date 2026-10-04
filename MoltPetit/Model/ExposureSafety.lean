import MoltPetit.Model.Model

/-!
# Light-client safety under arbitrary-time key exposure

The core of the timed model. Keys are exposed (Byzantine seats, stolen keys)
at arbitrary real times and sign whatever stamps they verify. If, of any `n`
consecutive stamps, at most `maxByzantine n` have a key exposed before the
window is `ρ` slots old, two quorum-dense chains that are fresh (their tips
within `ρ` slots of the real time `R` at which every one of their blocks
exists) agree at every height at least `n` below both tips
(`exposure_agreement`). And no block of a valid chain is signed more than
`n + maxByzantine n + σ + 1 - quorum n` slots ahead of real time, when honest
clocks run at most `σ` ahead (`exposure_no_early_signing`).

THE STATEMENTS OF `exposure_agreement` AND `exposure_no_early_signing` ARE
FIXED. Their exact types are pinned by `Molt/AxiomsExposureSafety.lean`. Prove
them; do not change them. See `docs/CORE_V2_SPEC.md` for the proof plan.
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

theorem availableAt_parent_of_signed {n : Nat} {exposed : Exposure}
    {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
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

theorem step_A_ancestor_available {n : Nat} {exposed : Exposure}
    {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
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
theorem ancestor_availableAt {n : Nat} {exposed : Exposure}
    {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
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

theorem availableAt_of_slot_le {n : Nat} {exposed : Exposure}
    {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {m : Nat} {B : Block} (hB : blockAt? c m = some B) {r : Nat} (hr : B ∈ log r)
    {A : Block} (hA : A ∈ c) (hslot : A.slot ≤ B.slot) :
    AvailableAt log G A r := by
  obtain ⟨k, hk⟩ := exists_blockAt_of_mem hA
  have hkm := blockAt_index_le_of_slot_le hc.2.1 hk hB hslot
  exact ancestor_availableAt hexec hc hHead hAvail hkm hB hr hk

theorem exposure_no_early_signing {n σ ρ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hClock : HonestClock σ exposed log)
    (hBudget : ExposureBounded n ρ exposed)
    {c : Chain} (hc : ValidChain n c) (hHead : blockAt? c 0 = some G)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {B : Block} (hB : B ∈ c) (hBG : B ≠ G) (hSlot : n - 1 ≤ B.slot)
    {r : Nat} (hr : B ∈ log r) :
    B.slot ≤ r + (n + maxByzantine n + σ + 1 - quorum n) := by
  sorry

theorem exposure_agreement {n ρ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution exposed log G)
    (hBudget : ExposureBounded n ρ exposed)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    (hHead : blockAt? c 0 = some G) (hHead' : blockAt? c' 0 = some G)
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hRecent : R ≤ tip.slot + ρ) (hRecent' : R ≤ tip'.slot + ρ)
    {h : Nat} (hDeep : h + n < c.length) (hDeep' : h + n < c'.length) :
    blockAt? c h = blockAt? c' h := by
  sorry

end MoltPetit.Model
