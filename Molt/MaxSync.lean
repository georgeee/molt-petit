import Molt.ClientRule

/-!
# The maximum sync period (paper §6.3, mode 1)

Both directions of "how rarely may the client sync", formal:

* **Upward** (`max_sync_period`): a client syncing every `F` slots is safe
  whenever rent plus the theft census stays within the fault budget on
  every window **starting** in the trailing `F + 4n` slots **or later**
  (later-starting windows are load-bearing only against chains dated
  beyond the clock). So a deployment able to cap `ρ + T` per window over
  every such stretch of `S` slots supports `F ≤ S - 4n`.

* **Downward** (`census_accumulates`, `no_budget_beyond`): the census at a
  window is at least the number of distinct producers whose
  not-yet-retired-there versions are *ever* stolen — healing does not
  subtract. Hence once a stretch holds more than `faultBudget n` victims,
  **no** instantiation of the budget hypothesis covers it: choosing a
  larger `F` is not an assumption trade, it is the accumulation attack.

Together: `F_max = S - 4n`, and with the minimal credible cap-span of a
reactive deployment (`S = 5n`), the sync rule `F = n`.
-/

namespace Molt

/-- Every roster seat owns exactly one slot in any `n`-slot window; this
constructs it. -/
theorem producer_slot_in_window {n : Nat} (hn : 1 ≤ n)
    {i : Nat} (hi : i < n) (u : Nat) :
    ∃ s, u ≤ s ∧ s < u + n ∧ producer n s = i := by
  have h1 : n * (u / n) + u % n = u := Nat.div_add_mod u n
  have h2 : u % n < n := Nat.mod_lt u (by omega)
  by_cases hcase : u % n ≤ i
  · refine ⟨n * (u / n) + i, by omega, by omega, ?_⟩
    show (n * (u / n) + i) % n = i
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hi
  · refine ⟨n * (u / n) + (n + i), by omega, by omega, ?_⟩
    show (n * (u / n) + (n + i)) % n = i
    rw [Nat.mul_add_mod, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt hi

private theorem foldl_max_le' :
    ∀ {L : List Nat} {a B : Nat}, a ≤ B → (∀ x ∈ L, x ≤ B) →
      L.foldl max a ≤ B
  | [], _, _, ha, _ => ha
  | x :: xs, a, B, ha, hx =>
    foldl_max_le' (L := xs) (a := max a x)
      (max_le ha (hx x (List.mem_cons_self ..)))
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))

private theorem acc_le_foldl_max :
    ∀ (L : List Nat) (a : Nat), a ≤ L.foldl max a
  | [], a => Nat.le_refl a
  | x :: xs, a =>
    Nat.le_trans (Nat.le_max_left a x) (acc_le_foldl_max xs (max a x))

private theorem mem_le_foldl_max' {x : Nat} :
    ∀ {L : List Nat} (a : Nat), x ∈ L → x ≤ L.foldl max a
  | [], _, hx => by simp at hx
  | y :: ys, a, hx => by
    rcases List.mem_cons.mp hx with rfl | hxs
    · exact Nat.le_trans (Nat.le_max_right a x)
        (acc_le_foldl_max ys (max a x))
    · exact mem_le_foldl_max' (max a y) hxs

private theorem foldl_max_zero_mono' {L L' : List Nat}
    (h : ∀ x ∈ L, x ∈ L') : L.foldl max 0 ≤ L'.foldl max 0 :=
  foldl_max_le' (Nat.zero_le _)
    (fun x hx => mem_le_foldl_max' 0 (h x hx))

/-- **Floors never fall as the viewpoint advances**: the in-force version
at a later slot is at least the one at an earlier slot — the confirmed
prefix only grows. This is the machine-checked glue behind "a theft
charges every earlier window": a version at-or-above the floor at its
theft slot is at-or-above the floor at every earlier slot too. -/
theorem inForce_mono {n Δconf : Nat} {c : Chain} {i : Nat} {s s' : Nat}
    (h : s ≤ s') :
    inForce n Δconf c i s ≤ inForce n Δconf c i s' := by
  unfold inForce keyFloor confirmedPrefix
  apply foldl_max_zero_mono'
  intro x hx
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hx ⊢
  obtain ⟨b, ⟨⟨hbc, hslot⟩, hprod⟩, hkey⟩ := hx
  exact ⟨b, ⟨⟨hbc, by omega⟩, hprod⟩, hkey⟩

/-- **The census accumulates** (the formal kernel of the long-cadence
attack). If each producer in `P` has, at its own slot of window
`[u, u+n)`, some stolen version at-or-above the floor there — no matter
when the theft happens, and regardless of any later healing — then the
window's bad-slot count is at least `P.card`. Healing raises floors only
at *later* slots; it never removes a theft from this window's books. -/
theorem census_accumulates
    {n Δconf : Nat} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {c₀ : Chain} {u : Nat}
    {P : Finset Nat}
    (hP : ∀ i ∈ P, ∃ s, u ≤ s ∧ s < u + n ∧ producer n s = i ∧
      ∃ j, inForce n Δconf c₀ i s ≤ j ∧ Stolen i j) :
    P.card ≤ (badSlotsIn (badKeyrot n Δconf rented Stolen c₀) u n).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun i => if h : i ∈ P then (hP i h).choose else 0)
  · intro i hiS
    have hmem : i ∈ P := Finset.mem_coe.mp hiS
    obtain ⟨hlo, hhi, hprod, j, hfloor, hstolen⟩ := (hP i hmem).choose_spec
    have hred : (if h : i ∈ P then (hP i h).choose else 0)
        = (hP i hmem).choose := dif_pos hmem
    show (if h : i ∈ P then (hP i h).choose else 0)
        ∈ badSlotsIn (badKeyrot n Δconf rented Stolen c₀) u n
    rw [hred]
    have hbad : badKeyrot n Δconf rented Stolen c₀ ((hP i hmem).choose) := by
      unfold badKeyrot
      rw [hprod]
      exact Or.inr ⟨j, hfloor, hstolen⟩
    unfold badSlotsIn
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hlo, hhi⟩, hbad⟩
  · intro i hiS i' hiS' heq
    have hmem : i ∈ P := Finset.mem_coe.mp hiS
    have hmem' : i' ∈ P := Finset.mem_coe.mp hiS'
    simp only [dif_pos hmem, dif_pos hmem'] at heq
    have h1 := (hP i hmem).choose_spec.2.2.1
    have h2 := (hP i' hmem').choose_spec.2.2.1
    rw [← h1, ← h2, heq]

/-- **A theft at-or-after a window charges the window** — the
machine-checked form of "including windows before the theft itself".
If each producer in `P` has some version stolen while at-or-above the
floor at any slot from the window's last slot onward, the window's
bad-slot count is at least `P.card`: floors are monotone
(`inForce_mono`), so the stolen version dominates the window's own
floor too. -/
theorem census_accumulates_later_thefts
    {n Δconf : Nat} (hn : 1 ≤ n) {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {c₀ : Chain} {u : Nat}
    {P : Finset Nat}
    (hP : ∀ i ∈ P, i < n ∧ ∃ sτ j, u + n ≤ sτ + 1 ∧
      inForce n Δconf c₀ i sτ ≤ j ∧ Stolen i j) :
    P.card ≤ (badSlotsIn (badKeyrot n Δconf rented Stolen c₀) u n).card := by
  apply census_accumulates
  intro i hi
  obtain ⟨hin, sτ, j, hτ, hfloor, hstolen⟩ := hP i hi
  obtain ⟨s, hlo, hhi, hprod⟩ := producer_slot_in_window hn hin u
  exact ⟨s, hlo, hhi, hprod, j,
    Nat.le_trans (inForce_mono (by omega)) hfloor, hstolen⟩

/-- **No budget exists beyond the accumulation bound.** Once more than
`faultBudget n` producers have an ever-stolen, not-yet-retired-at-`u`
version, the budget hypothesis of every mode-1 safety theorem is
violated at window `u` — for any rent predicate. Choosing a sync period
whose trailing stretch admits that many victims therefore leaves nothing
to instantiate: the long cadence is not a weaker assumption, it is no
assumption. -/
theorem no_budget_beyond
    {n Δconf : Nat} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {c₀ : Chain} {u : Nat}
    {P : Finset Nat}
    (hP : ∀ i ∈ P, ∃ s, u ≤ s ∧ s < u + n ∧ producer n s = i ∧
      ∃ j, inForce n Δconf c₀ i s ≤ j ∧ Stolen i j)
    (hbig : faultBudget n < P.card) :
    ¬ (badSlotsIn (badKeyrot n Δconf rented Stolen c₀) u n).card
        ≤ faultBudget n := by
  have := census_accumulates (rented := rented) hP
  omega

/-- **The maximum sync period** (paper §6.3). Fully parametric in the
sync period `F`: a client that re-verifies at least every `F` slots,
anchoring the `n`-deep block, is safe provided rent plus the theft
census stays within the fault budget on every window **starting** in
the trailing `F + 4n` slots **or later**. Read with `no_budget_beyond`:
beyond `F = S - 4n` (with `S` the deployment's defendable cap-stretch)
the hypothesis is unsatisfiable; the sync rule is the `F = n`, `S = 5n`
instance. -/
theorem max_sync_period
    {n Δconf F : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block}
    {sc sc' scPrev : SignedChain Sig} {A : Block}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen
      honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    {t : Nat} {tipPrev : Block}
    (hVPrev : validSignedChainK' n Δconf ops registry scPrev = true)
    (hTipPrev : (stripSigs scPrev).getLast? = some tipPrev)
    (hRecPrev : t ≤ tipPrev.slot + n)
    (hLongPrev : n < (stripSigs scPrev).length)
    (hAnchor : blockAt? (stripSigs scPrev)
      ((stripSigs scPrev).length - 1 - n) = some A)
    (hCadence : now ≤ t + F)
    (hA : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    (hBudget : ∀ u, now < u + F + 4 * n →
      (badSlotsIn (badKeyrot n Δconf rented Stolen (stripSigs sc)) u n).card
        ≤ faultBudget n)
    (hVal : validSignedChainK' n Δconf ops registry sc = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc )
      ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc')
      ((stripSigs sc').length - 1 - n) = some B') :
    B = B' := by
  have hVPrev' := hVPrev
  rw [validSignedChainK'_eq_core] at hVPrev'
  rw [MoltPetit.Model.validSignedChainK', Bool.and_eq_true] at hVPrev'
  have hVc : MoltPetit.Model.ValidChain n (stripSigs scPrev) :=
    (MoltPetit.Model.validChainK'_sound hVPrev'.2).1
  have hTipIdx : MoltPetit.Model.blockAt? (stripSigs scPrev)
      ((stripSigs scPrev).length - 1) = some tipPrev :=
    MoltPetit.Model.blockAt_getLast hTipPrev
  have hidx : ((stripSigs scPrev).length - 1 - n) + n
      = (stripSigs scPrev).length - 1 := by omega
  have hspan : tipPrev.slot < A.slot + 2 * n :=
    deep_block_span hn hVc hAnchor (by rw [hidx]; exact hTipIdx)
  have hFresh : now ≤ A.slot + (F + 3 * n - 1) := by omega
  exact client_refresh_rule hn hΔ hEUF hHash hA hA' hFresh
    (fun u hu => hBudget u (by omega)) hVal hVal' hTipS hTipS'
    hRecent hRecent' hLong hLong' hTipHeight hB hB'

end Molt
