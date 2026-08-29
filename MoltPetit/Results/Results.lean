import MoltPetit.Model.Grounded
import MoltPetit.Model.Timed

/-!
# MoltPetit — main results

The protocol is defined in TypeScript (`moltPetit.ts`, compiled to
the Lean sidecar `MoltPetit/TS/Emitted.lean` by thales); everything below is
about the artifacts a node actually runs: `produceBlockCert` (sign →
compact against the certificate store → validate → ship) and
`validateCertifiedChain` (certificate verification, per-block signature
checks, structural suffix validation).

## Safety — the light-client theorems

* `ts_recent_tip_ancestor_agreement` — two certified chains accepted by
  `validateCertifiedChain`, suffixes longer than `n`, both tips passing
  the **tight recency rule** (`now ≤ tip.slot + n`) and at equal height,
  have the **same** ancestor `n` blocks below the tip.
* `ts_recent_tip_ancestor_mem` — the consistency form, without equal
  heights: the `n`-deep ancestor of the recent chain with the lower tip
  *is a block of* every other recent chain, at least `n` deep there too.
  All recent chains agree on their common prefix up to `n` below the
  lower tip.
* `ts_recent_produced_tip_ancestor_agreement` — the production side: a
  chain shipped by `produceBlockCert` agrees the same way with any
  validated recent chain.

Assumptions: `ByzantineBounded` (≤ `⌊(n-1)/3⌋` adversarial slots per
`n`-window), `SigUnforgeableRecent` (EUF-CMA + honest signing
discipline, scoped to recency-passing valid chains — the scope the timed
bounds below justify), `SignedHashInjective` (id collision resistance
over occurring blocks), and per-node certificate unforgeability
(verifying certificates carry claims grounded in the genesis, over
*signed* blocks).

## The timed bounds — why recency works

* `forged_suffix_time_bound` / `forged_suffix_lag` — **no adversary can
  forge a chain at slot `B + s` before slot `≈ B + 2s`**: in the
  real-time signing model (`TimedExecution`), a valid chain forged above
  a fork block first signed at real slot `r₀` cannot reach tip stamp
  `r₀ + s` before real slot `≈ r₀ + 2s`.
* `forged_chain_time_bound` / `forged_chain_lag` — the from-genesis
  form: a fully forged chain with tip stamp `T` needs `≈ 2T` of real
  time.

These rate limits are what make the recency rule sound: a fork meeting
the `Δ = n` bar carries at most `≈ 2·maxByzantine ≈ 2n/3` harvested
blocks — short of the `n + 1` needed to fake an `n`-deep ancestor
(breakeven at `Δ ≈ 1.5n`).

## Liveness — the chain grows

* `liveness_produce_block` / `liveness_produce_signed_block` — in an
  honest participant's slot, production *succeeds*: the extension passes
  the validator, so the chain keeps growing and blocks keep maturing
  toward finality (under `HonestBlocksCover` delivery).

All results depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace MoltPetit.Model

-- ---------------------------------------------------------------------------
-- Model safety (proved in Safety.lean, surfaced here as the model results
-- that the per-implementation corollaries in Results_ts / Results_rust rest on)
-- ---------------------------------------------------------------------------

/-- No two semantically valid chains fork `n`-deep (model form). -/
alias model_no_deep_fork := no_deep_fork

/-- Any block `n`-deep on two semantically valid chains is identical (model form). -/
alias model_deep_block_agreement := deep_block_agreement

/-- A chain the executable validator `validChain` accepts is semantically valid
(`ValidChain`); this is the hinge both implementations transfer through. -/
alias model_validChain_sound := validChain_sound

-- ---------------------------------------------------------------------------
-- The forged-suffix time bound (relative form)
-- ---------------------------------------------------------------------------

open Classical in
/--
**Forged suffixes take twice their span in real time.** Let `F` be a
chain block (index `k₀ ≥ 1`) first signed at real slot `r₀` — for an
honestly produced fork point, `r₀ = F.slot`. If every chain block above
`F`'s slot was only ever signed at *bad* real slots (the suffix is
forged by coercion), and the chain is available at real slot `R` with
tip stamp `T = tip.slot`, then

    quorum n * ((T - F.slot) / n)  ≤  maxByzantine n * ((R - r₀) / n + 1).

Density forces `quorum` forged blocks per stamped window above `F`; each
is first-signed at a distinct bad real slot in `[r₀, R]` (monotonicity
from `F` plus `one_real_slot_one_block`), and the budget admits only
`maxByzantine` such slots per real window. With
`quorum ≈ 2·maxByzantine`: **a chain cannot be forged to slot `B + s`
before real slot `≈ B + 2s`** (`forged_suffix_lag`).
-/
theorem forged_suffix_time_bound {n : Nat} (hn : 2 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    (hBudget : ByzantineBounded n bad)
    {c : Chain} (hValid : ValidChain n c)
    (hGprev : G.prev = none)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {k₀ : Nat} (hk₀ : 1 ≤ k₀) {F : Block} (hF : blockAt? c k₀ = some F)
    {r₀ : Nat} (hFr : F ∈ log r₀) (hFmin : ∀ r < r₀, F ∉ log r)
    (hForged : ∀ B ∈ c, F.slot < B.slot → ∀ r, B ∈ log r → bad r)
    {tip : Block} (hTip : c.getLast? = some tip) :
    quorum n * ((tip.slot - F.slot) / n) ≤
      maxByzantine n * ((R - r₀) / n + 1) := by
  obtain ⟨hSeq, hS, hPL, hMat⟩ := hValid
  have hTipAt : blockAt? c (c.length - 1) = some tip := blockAt_getLast hTip
  have hFmem : F ∈ c := by
    unfold blockAt? at hF
    exact List.mem_of_getElem? hF
  have hFs : F.slot ≤ tip.slot := slot_le_tip_of_mem hS hTip hFmem
  set s := tip.slot - F.slot with hsdef
  set m := s / n with hmdef
  -- (a) density: at least q·m blocks above F, so the chain is long
  have hwin : ∀ j < m, quorum n ≤ windowCount c ((F.slot + 1) + j * n) n := by
    intro j hj
    apply hMat hTipAt
    calc (F.slot + 1) + j * n + n
        = (F.slot + 1) + (j + 1) * n := by ring
      _ ≤ (F.slot + 1) + m * n :=
          Nat.add_le_add_left (Nat.mul_le_mul_right n (by omega)) _
      _ ≤ (F.slot + 1) + s := Nat.add_le_add_left (Nat.div_mul_le_self s n) _
      _ = tip.slot + 1 := by omega
  have hcount : (k₀ + 1) + quorum n * m ≤ c.length :=
    calc (k₀ + 1) + quorum n * m
        ≤ belowCount c (F.slot + 1) + quorum n * m :=
          Nat.add_le_add_right (belowCount_prefix hS hF) _
      _ ≤ belowCount c ((F.slot + 1) + m * n) :=
          belowCount_windows c (F.slot + 1) n (quorum n) m hwin
      _ ≤ c.length := belowCount_le _ _
  -- (b) each block above F is first-signed at its own bad slot in [r₀, R]
  have hFsigex : ∃ r, F ∈ log r := ⟨r₀, hFr⟩
  have hFfind : Nat.find hFsigex = r₀ := (Nat.find_eq_iff hFsigex).mpr ⟨hFr, hFmin⟩
  have hsig : ∀ k, ∃ r, k₀ < k → k < c.length →
      (r₀ ≤ r ∧ r ≤ R ∧ bad r ∧ ∃ B, blockAt? c k = some B ∧ B ∈ log r ∧
        ∀ r' < r, B ∉ log r') := by
    intro k
    by_cases hk : k₀ < k ∧ k < c.length
    · obtain ⟨hk1, hk2⟩ := hk
      have hB : blockAt? c k = some (getElem c k hk2) := by
        unfold blockAt?
        exact List.getElem?_eq_getElem hk2
      obtain ⟨hBne, rB, hrBle, hrBmem⟩ := block_signed hGprev hPL hAvail
        (by omega) hB
      have hBsig : ∃ r, (getElem c k hk2) ∈ log r := ⟨rB, hrBmem⟩
      have hmemc : (getElem c k hk2) ∈ c := by
        unfold blockAt? at hB
        exact List.mem_of_getElem? hB
      have hslotgt : F.slot < (getElem c k hk2).slot := strictSlots_lt hS hF hB hk1
      have hmono := sigTime_mono_chain hexec hGprev hPL hAvail (k - k₀) hk₀ hF
        (show blockAt? c (k₀ + (k - k₀)) = some (getElem c k hk2) by
          rw [show k₀ + (k - k₀) = k by omega]; exact hB) hFsigex hBsig
      refine ⟨Nat.find hBsig, fun _ _ => ⟨?_, ?_, ?_, getElem c k hk2, hB,
        Nat.find_spec hBsig, fun r' hr' => Nat.find_min hBsig hr'⟩⟩
      · rw [← hFfind]
        exact hmono
      · exact le_trans (Nat.find_min' hBsig hrBmem) hrBle
      · exact hForged _ hmemc hslotgt _ (Nat.find_spec hBsig)
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose σ hσ using hsig
  -- the indices above k₀ inject into bad slots of [r₀, R]
  have hcard : c.length - (k₀ + 1) ≤
      ((Finset.Ico r₀ (R + 1)).filter fun s => bad s).card := by
    have hmaps : ∀ a ∈ Finset.Ico (k₀ + 1) c.length,
        σ a ∈ (Finset.Ico r₀ (R + 1)).filter fun s => bad s := by
      intro a ha
      rw [Finset.mem_Ico] at ha
      obtain ⟨h0, h1, h2, -⟩ := hσ a (by omega) ha.2
      rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨h0, by omega⟩, h2⟩
    have hinj : Set.InjOn σ (Finset.Ico (k₀ + 1) c.length) := by
      intro a ha b hb hab
      simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
      by_contra hne
      rcases Nat.lt_or_ge a b with h | h
      · obtain ⟨-, -, -, B, hBat, hBr, hBmin⟩ := hσ a (by omega) ha.2
        obtain ⟨-, -, -, B', hB'at, hB'r, hB'min⟩ := hσ b (by omega) hb.2
        rw [hab] at hBr hBmin
        exact one_real_slot_one_block hn hexec hGprev ⟨hSeq, hS, hPL, hMat⟩
          hAvail (by omega) h hBat hB'at hBr hBmin hB'r hB'min
      · have h' : b < a := by omega
        obtain ⟨-, -, -, B, hBat, hBr, hBmin⟩ := hσ a (by omega) ha.2
        obtain ⟨-, -, -, B', hB'at, hB'r, hB'min⟩ := hσ b (by omega) hb.2
        rw [hab] at hBr hBmin
        exact one_real_slot_one_block hn hexec hGprev ⟨hSeq, hS, hPL, hMat⟩
          hAvail (by omega) h' hB'at hBat hB'r hB'min hBr hBmin
    have := Finset.card_le_card_of_injOn σ hmaps hinj
    rwa [Nat.card_Ico] at this
  -- (c) the budget caps bad slots in [r₀, R]
  have hbad : ((Finset.Ico r₀ (R + 1)).filter fun s => bad s).card ≤
      maxByzantine n * ((R - r₀) / n + 1) := by
    have hbound : R + 1 ≤ r₀ + ((R - r₀) / n + 1) * n := by
      rcases Nat.le_total r₀ R with hle | hle
      · have hX := le_div_succ_mul (R - r₀) n (by omega)
        calc R + 1 = r₀ + ((R - r₀) + 1) := by omega
          _ ≤ r₀ + ((R - r₀) / n + 1) * n := Nat.add_le_add_left hX r₀
      · have hX : n ≤ ((R - r₀) / n + 1) * n := Nat.le_mul_of_pos_left n (Nat.succ_pos _)
        calc R + 1 ≤ r₀ + 1 := by omega
          _ ≤ r₀ + n := by omega
          _ ≤ r₀ + ((R - r₀) / n + 1) * n := Nat.add_le_add_left hX r₀
    calc ((Finset.Ico r₀ (R + 1)).filter fun s => bad s).card
        ≤ ((Finset.Ico r₀ (r₀ + ((R - r₀) / n + 1) * n)).filter
            fun s => bad s).card :=
          Finset.card_le_card (Finset.filter_subset_filter _
            (Finset.Ico_subset_Ico le_rfl hbound))
      _ ≤ maxByzantine n * ((R - r₀) / n + 1) := bad_budget_Ico hBudget r₀ _
  have hcount' : quorum n * m + (k₀ + 1) ≤ c.length := by
    rw [Nat.add_comm (quorum n * m) (k₀ + 1)]
    exact hcount
  calc quorum n * m ≤ c.length - (k₀ + 1) := Nat.le_sub_of_add_le hcount'
    _ ≤ ((Finset.Ico r₀ (R + 1)).filter fun s => bad s).card := hcard
    _ ≤ maxByzantine n * ((R - r₀) / n + 1) := hbad

/--
**Readable corollary — "no forging `B + s` before `B + 2s`".** With at
least one Byzantine slot per window allowed, a chain forged above a fork
block `F` (first signed at `r₀`; `= F.slot = B` for an honest fork
point) satisfies `2 · (s/n) ≤ (R − r₀)/n + 1` where `s` is the forged
stamped span — i.e. `R ⪆ r₀ + 2s − 3n`: reaching stamp `B + s` takes
until real slot `≈ B + 2s`, up to three windows of boundary slop.
-/
theorem forged_suffix_lag {n : Nat} (hn : 2 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    (hBudget : ByzantineBounded n bad)
    {c : Chain} (hValid : ValidChain n c)
    (hGprev : G.prev = none)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    {k₀ : Nat} (hk₀ : 1 ≤ k₀) {F : Block} (hF : blockAt? c k₀ = some F)
    {r₀ : Nat} (hFr : F ∈ log r₀) (hFmin : ∀ r < r₀, F ∉ log r)
    (hForged : ∀ B ∈ c, F.slot < B.slot → ∀ r, B ∈ log r → bad r)
    {tip : Block} (hTip : c.getLast? = some tip)
    (hf : 1 ≤ maxByzantine n) :
    2 * ((tip.slot - F.slot) / n) ≤ (R - r₀) / n + 1 := by
  have hmain := forged_suffix_time_bound hn hexec hBudget hValid hGprev
    hAvail hk₀ hF hFr hFmin hForged hTip
  have hqf : 2 * maxByzantine n + 1 ≤ quorum n := by
    unfold quorum maxByzantine
    omega
  have h1 : (2 * maxByzantine n + 1) * ((tip.slot - F.slot) / n) ≤
      maxByzantine n * ((R - r₀) / n + 1) :=
    le_trans (Nat.mul_le_mul_right _ hqf) hmain
  generalize (tip.slot - F.slot) / n = a at h1 ⊢
  generalize (R - r₀) / n = b at h1 ⊢
  generalize maxByzantine n = f at h1 hf
  have h2 : 2 * a * f ≤ (b + 1) * f := by
    have e1 : (2 * f + 1) * a = 2 * a * f + a := by ring
    have e2 : f * (b + 1) = b * f + f := by ring
    have e3 : (b + 1) * f = b * f + f := by ring
    rw [e1, e2] at h1
    rw [e3]
    generalize 2 * a * f = X at h1 ⊢
    generalize b * f = Y at h1 ⊢
    omega
  exact Nat.le_of_mul_le_mul_right h2 (by omega)

-- ---------------------------------------------------------------------------
-- The absolute (from-genesis) form
-- ---------------------------------------------------------------------------

open Classical in
/--
**Fully forged chains take real time.** A valid chain none of whose
blocks was honestly produced — every signing event of every non-genesis
block happened at a *bad* real slot — and which exists by real slot `R`
with tip stamp `T`, satisfies

    quorum n * ((T + 1) / n)  ≤  maxByzantine n * (R / n + 1) + 1.

With `quorum ≈ 2·maxByzantine`, the adversary needs about **twice `T` of
real time** to forge a chain claiming to reach slot `T` — so a chain
with a *recent* tip cannot be a from-scratch forgery, which is what
makes light-client recency rules meaningful. (`forged_suffix_time_bound`
is the relative version, for chains forged above an honest fork point.)
-/
theorem forged_chain_time_bound {n : Nat} (hn : 2 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    (hBudget : ByzantineBounded n bad)
    {c : Chain} (hValid : ValidChain n c)
    (hGprev : G.prev = none)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hForged : ∀ B ∈ c, B ≠ G → ∀ r, B ∈ log r → bad r)
    {tip : Block} (hTip : c.getLast? = some tip) :
    quorum n * ((tip.slot + 1) / n) ≤ maxByzantine n * (R / n + 1) + 1 := by
  obtain ⟨hSeq, hS, hPL, hMat⟩ := hValid
  have hTipAt : blockAt? c (c.length - 1) = some tip := blockAt_getLast hTip
  set m := (tip.slot + 1) / n with hmdef
  -- (a) density: the chain has at least quorum blocks per window below the tip
  have hwin : ∀ j < m, quorum n ≤ windowCount c (0 + j * n) n := by
    intro j hj
    apply hMat hTipAt
    calc 0 + j * n + n = (j + 1) * n := by ring
      _ ≤ m * n := Nat.mul_le_mul_right n (by omega)
      _ ≤ tip.slot + 1 := Nat.div_mul_le_self _ _
  have hlen : quorum n * m ≤ c.length := by
    have h := belowCount_windows c 0 n (quorum n) m hwin
    rw [belowCount_zero] at h
    calc quorum n * m = 0 + quorum n * m := by omega
      _ ≤ belowCount c (0 + m * n) := h
      _ ≤ c.length := belowCount_le _ _
  -- (b) each non-genesis block is first-signed at its own bad slot ≤ R
  have hsig : ∀ k, ∃ r, 1 ≤ k → k < c.length →
      (r ≤ R ∧ bad r ∧ ∃ B, blockAt? c k = some B ∧ B ∈ log r ∧
        ∀ r' < r, B ∉ log r') := by
    intro k
    by_cases hk : 1 ≤ k ∧ k < c.length
    · obtain ⟨hk1, hk2⟩ := hk
      have hB : blockAt? c k = some (getElem c k hk2) := by
        unfold blockAt?
        exact List.getElem?_eq_getElem hk2
      obtain ⟨hBne, rB, hrBle, hrBmem⟩ := block_signed hGprev hPL hAvail hk1 hB
      have hBsig : ∃ r, (getElem c k hk2) ∈ log r := ⟨rB, hrBmem⟩
      have hmemc : (getElem c k hk2) ∈ c := by
        unfold blockAt? at hB
        exact List.mem_of_getElem? hB
      refine ⟨Nat.find hBsig, fun _ _ => ⟨?_, ?_, getElem c k hk2, hB,
        Nat.find_spec hBsig, fun r' hr' => Nat.find_min hBsig hr'⟩⟩
      · exact le_trans (Nat.find_min' hBsig hrBmem) hrBle
      · exact hForged _ hmemc hBne _ (Nat.find_spec hBsig)
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose σ hσ using hsig
  have hcard : c.length - 1 ≤
      ((Finset.Ico 0 (R + 1)).filter fun s => bad s).card := by
    have hmaps : ∀ a ∈ Finset.Ico 1 c.length,
        σ a ∈ (Finset.Ico 0 (R + 1)).filter fun s => bad s := by
      intro a ha
      rw [Finset.mem_Ico] at ha
      obtain ⟨h1, h2, -⟩ := hσ a ha.1 ha.2
      rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨Nat.zero_le _, by omega⟩, h2⟩
    have hinj : Set.InjOn σ (Finset.Ico 1 c.length) := by
      intro a ha b hb hab
      simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
      by_contra hne
      rcases Nat.lt_or_ge a b with h | h
      · obtain ⟨-, -, B, hBat, hBr, hBmin⟩ := hσ a ha.1 ha.2
        obtain ⟨-, -, B', hB'at, hB'r, hB'min⟩ := hσ b hb.1 hb.2
        rw [hab] at hBr hBmin
        exact one_real_slot_one_block hn hexec hGprev ⟨hSeq, hS, hPL, hMat⟩
          hAvail ha.1 h hBat hB'at hBr hBmin hB'r hB'min
      · have h' : b < a := by omega
        obtain ⟨-, -, B, hBat, hBr, hBmin⟩ := hσ a ha.1 ha.2
        obtain ⟨-, -, B', hB'at, hB'r, hB'min⟩ := hσ b hb.1 hb.2
        rw [hab] at hBr hBmin
        exact one_real_slot_one_block hn hexec hGprev ⟨hSeq, hS, hPL, hMat⟩
          hAvail hb.1 h' hB'at hBat hB'r hB'min hBr hBmin
    have := Finset.card_le_card_of_injOn σ hmaps hinj
    rwa [Nat.card_Ico] at this
  -- (c) the budget caps bad slots ≤ R
  have hbad : ((Finset.Ico 0 (R + 1)).filter fun s => bad s).card ≤
      maxByzantine n * (R / n + 1) := by
    have hbound : R + 1 ≤ 0 + (R / n + 1) * n := by
      have hX := le_div_succ_mul R n (by omega)
      omega
    calc ((Finset.Ico 0 (R + 1)).filter fun s => bad s).card
        ≤ ((Finset.Ico 0 (0 + (R / n + 1) * n)).filter fun s => bad s).card :=
          Finset.card_le_card (Finset.filter_subset_filter _
            (Finset.Ico_subset_Ico le_rfl hbound))
      _ ≤ maxByzantine n * (R / n + 1) := bad_budget_Ico hBudget 0 _
  have hlen1 : 1 ≤ c.length := by
    cases c with
    | nil => simp at hTip
    | cons _ _ => simp
  calc quorum n * m ≤ c.length := hlen
    _ ≤ (c.length - 1) + 1 := by omega
    _ ≤ ((Finset.Ico 0 (R + 1)).filter fun s => bad s).card + 1 :=
        Nat.add_le_add_right hcard 1
    _ ≤ maxByzantine n * (R / n + 1) + 1 := Nat.add_le_add_right hbad 1

/--
**Readable corollary: fully forged chains lag by half.** With at least
one Byzantine slot per window allowed, a fully forged chain's tip window
index is at most about *half* the real window index:
`2 · (T+1)/n ≤ R/n + 3`.
-/
theorem forged_chain_lag {n : Nat} (hn : 2 ≤ n)
    {bad : ByzantineSlots} {log : TimedLog} {G : Block}
    (hexec : TimedExecution n bad log G)
    (hBudget : ByzantineBounded n bad)
    {c : Chain} (hValid : ValidChain n c)
    (hGprev : G.prev = none)
    {R : Nat} (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hForged : ∀ B ∈ c, B ≠ G → ∀ r, B ∈ log r → bad r)
    {tip : Block} (hTip : c.getLast? = some tip)
    (hf : 1 ≤ maxByzantine n) :
    2 * ((tip.slot + 1) / n) ≤ R / n + 3 := by
  have hmain := forged_chain_time_bound hn hexec hBudget hValid hGprev
    hAvail hForged hTip
  have hqf : 2 * maxByzantine n + 1 ≤ quorum n := by
    unfold quorum maxByzantine
    omega
  have h1 : (2 * maxByzantine n + 1) * ((tip.slot + 1) / n) ≤
      maxByzantine n * (R / n + 1) + 1 :=
    le_trans (Nat.mul_le_mul_right _ hqf) hmain
  generalize (tip.slot + 1) / n = a at h1 ⊢
  generalize R / n = b at h1 ⊢
  generalize maxByzantine n = f at h1 hf
  have h2 : 2 * a * f ≤ (b + 3) * f := by
    have e1 : (2 * f + 1) * a = 2 * a * f + a := by ring
    have e2 : f * (b + 1) = b * f + f := by ring
    have e3 : (b + 3) * f = b * f + 3 * f := by ring
    rw [e1, e2] at h1
    rw [e3]
    generalize 2 * a * f = X at h1 ⊢
    generalize b * f = Y at h1 ⊢
    omega
  exact Nat.le_of_mul_le_mul_right h2 (by omega)


-- ---------------------------------------------------------------------------
-- Liveness: production succeeds
-- ---------------------------------------------------------------------------

/--
**Liveness, abstract chain.** When slot `slot` belongs to honest
participant `me`, production succeeds: `produceBlock?` returns the new
block — the honest producer never skips its slot.
-/
theorem liveness_produce_block
    {n me slot newId : Nat} {contentsHash keyIndex : Nat}
    {bad : ByzantineSlots} {record : SlotRecord}
    {c : Chain} {tip : Block}
    (hBudget   : ByzantineBounded n bad)
    (hValid    : validChain n c = true)
    (hTipEq    : c.getLast? = some tip)
    (hTipLt    : tip.slot < slot)
    (hMine     : producerForSlot n slot = me)
    (hSCorrect : ∀ s (B : Block), B ∈ record s → B.slot = s)
    (hCover    : ∀ u, tip.slot + 1 < u + n → u + n ≤ slot + 1 →
        HonestBlocksCover bad record (c ++ [nextBlock slot newId contentsHash keyIndex tip]) u n) :
    produceBlock? n me slot newId contentsHash keyIndex c
      = some (nextBlock slot newId contentsHash keyIndex tip) := by
  have hExt := liveness_valid_extension hBudget hValid hTipEq hTipLt
    hSCorrect hCover
  simp [produceBlock?, hMine, hTipEq, hExt]

/--
**Liveness, wire level.** The signed variant also succeeds, additionally
assuming signature-scheme correctness (`SigCorrect`), a full registry
(`registry.size = n`), and that the producer signs with its own key.
This is exactly where the "standard assumption about the signature
primitive" discharges the self-check `produceSignedBlock?` performs on
its own signature.
-/
theorem liveness_produce_signed_block {σ sk pk : Type}
    {n me slot newId : Nat} {contentsHash keyIndex : Nat} (hn : 1 ≤ n)
    {ops : SigOps σ sk pk} {registry : KeyRegistry pk} {keyPair : Nat → Nat → sk}
    {bad : ByzantineSlots} {record : SlotRecord}
    {sc : SignedChain σ} {tip : Block}
    (hSig      : SigCorrect n ops registry keyPair)
    (hBudget   : ByzantineBounded n bad)
    (hValid    : validSignedChain n ops registry sc = true)
    (hTipEq    : (stripSigs sc).getLast? = some tip)
    (hTipLt    : tip.slot < slot)
    (hMine     : producerForSlot n slot = me)
    (hSCorrect : ∀ s (B : Block), B ∈ record s → B.slot = s)
    (hCover    : ∀ u, tip.slot + 1 < u + n → u + n ≤ slot + 1 →
        HonestBlocksCover bad record
          (stripSigs sc ++ [nextBlock slot newId contentsHash keyIndex tip]) u n) :
    produceSignedBlock? n me slot newId contentsHash keyIndex ops registry (keyPair me keyIndex) sc =
      some ⟨nextBlock slot newId contentsHash keyIndex tip,
            ops.sign (keyPair me keyIndex) (nextBlock slot newId contentsHash keyIndex tip)⟩ := by
  set b := nextBlock slot newId contentsHash keyIndex tip with hb
  set sb : SignedBlock σ := ⟨b, ops.sign (keyPair me keyIndex) b⟩ with hsb
  rw [validSignedChain, Bool.and_eq_true] at hValid
  obtain ⟨hSigs, hChain⟩ := hValid
  -- the new block's signature verifies against the versioned directory at
  -- the producer's current index (`b.keyIndex = keyIndex` by construction)
  have hbProducer : producerForSlot n b.slot = me := hMine
  have hbIndex : b.keyIndex = keyIndex := rfl
  have hSigOk : sigOk n ops registry sb = true := by
    rw [sigOk]
    show ops.verify (registry (producerForSlot n b.slot) b.keyIndex)
      b (ops.sign (keyPair me keyIndex) b) = true
    rw [hbProducer, hbIndex]
    exact hSig.verify_sign me keyIndex b hbProducer hbIndex
  -- all signatures of the extension verify
  have hSigsExt : sigsOk n ops registry (sc ++ [sb]) = true := by
    rw [sigsOk, List.all_append]
    rw [sigsOk] at hSigs
    simp [hSigs, hSigOk]
  -- the stripped extension passes the structural validator
  have hStrip : stripSigs (sc ++ [sb]) = stripSigs sc ++ [b] := by
    simp only [stripSigs, List.map_append, List.map_cons, List.map_nil]
    rfl
  have hExt : validChain n (stripSigs (sc ++ [sb])) = true := by
    rw [hStrip]
    exact liveness_valid_extension hBudget hChain hTipEq hTipLt
      hSCorrect hCover
  have hValidExt : validSignedChain n ops registry (sc ++ [sb]) = true := by
    rw [validSignedChain, Bool.and_eq_true]
    exact ⟨hSigsExt, hExt⟩
  simp [produceSignedBlock?, hMine, hTipEq, ← hb, ← hsb, hValidExt]


-- ---------------------------------------------------------------------------
-- Slot duration from certificate-prover throughput
-- ---------------------------------------------------------------------------

namespace ProverTiming

/-- One cycle preserves the budget: a backlog within `n/2` folds into a
backlog within `n/2`, provided the slot meets the recommendation. -/
theorem nextBacklog_le {n baseline perBlock τ : ℚ}
    (hn : 0 < n) (hpb : 0 ≤ perBlock) (hτpos : 0 < τ)
    (hτ : recommendedSlot n baseline perBlock ≤ τ)
    {u : ℚ} (hu : 0 ≤ u) (hub : u ≤ n / 2) :
    nextBacklog baseline perBlock τ u ≤ n / 2 := by
  unfold nextBacklog certTime
  rw [div_le_iff₀ hτpos]
  unfold recommendedSlot at hτ
  have h2 : 2 * baseline ≤ (τ - perBlock) * n := by
    have := (div_le_iff₀ hn).mp (by linarith : 2 * baseline / n ≤ τ - perBlock)
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hub hpb, mul_pos hτpos hn]

/-- Backlogs are never negative. -/
theorem nextBacklog_nonneg {baseline perBlock τ : ℚ}
    (hb : 0 ≤ baseline) (hpb : 0 ≤ perBlock) (hτpos : 0 < τ)
    {u : ℚ} (hu : 0 ≤ u) :
    0 ≤ nextBacklog baseline perBlock τ u := by
  unfold nextBacklog certTime
  positivity

/--
**The recommendation is sufficient.** At any slot duration meeting
`recommendedSlot`, a single prover that starts within budget
(`u₀ ≤ n/2`) keeps, for every future run `j`:

* the backlog at most `n/2`, and
* the peak uncovered suffix at most `n` — the node always holds a
  certificate plus at most `n` slots' worth of blocks.
-/
theorem recommended_slot_sufficient {n baseline perBlock τ : ℚ}
    (hn : 0 < n) (hb : 0 ≤ baseline) (hpb : 0 ≤ perBlock) (hτpos : 0 < τ)
    (hτ : recommendedSlot n baseline perBlock ≤ τ)
    {u₀ : ℚ} (hu₀ : 0 ≤ u₀) (hub₀ : u₀ ≤ n / 2) :
    ∀ j, backlog baseline perBlock τ u₀ j ≤ n / 2 ∧
      peakSuffix baseline perBlock τ (backlog baseline perBlock τ u₀ j) ≤ n := by
  have hstep : ∀ j, 0 ≤ backlog baseline perBlock τ u₀ j ∧
      backlog baseline perBlock τ u₀ j ≤ n / 2 := by
    intro j
    induction j with
    | zero => exact ⟨hu₀, hub₀⟩
    | succ j ih =>
      exact ⟨nextBacklog_nonneg hb hpb hτpos ih.1,
        nextBacklog_le hn hpb hτpos hτ ih.1 ih.2⟩
  intro j
  refine ⟨(hstep j).2, ?_⟩
  have hnext := nextBacklog_le hn hpb hτpos hτ (hstep j).1 (hstep j).2
  unfold peakSuffix
  linarith [(hstep j).2]

/--
**The recommendation is necessary.** At any slot duration strictly
between `perBlock` and `recommendedSlot`, the pipeline's steady state
(the backlog the prover converges to, where each fold leaves exactly the
backlog it started with) already overflows the window: its peak
uncovered suffix exceeds `n` slots' worth of blocks.
-/
theorem recommended_slot_necessary {n baseline perBlock τ : ℚ}
    (hn : 0 < n) (hpb0 : 0 ≤ perBlock) (hpb : perBlock < τ)
    (hτ : τ < recommendedSlot n baseline perBlock)
    {u : ℚ} (hsteady : nextBacklog baseline perBlock τ u = u) :
    n < peakSuffix baseline perBlock τ u := by
  have hτpos : 0 < τ := lt_of_le_of_lt hpb0 hpb
  have hfix : baseline + u * perBlock = u * τ := by
    have := hsteady
    unfold nextBacklog certTime at this
    field_simp at this
    linarith
  unfold peakSuffix
  rw [hsteady]
  -- goal: n < u + u; from u·(τ − perBlock) = baseline and τ − perBlock < 2·baseline/n
  unfold recommendedSlot at hτ
  have h2 : (τ - perBlock) * n < 2 * baseline := by
    have := (lt_div_iff₀ hn).mp (by linarith : τ - perBlock < 2 * baseline / n)
    linarith
  nlinarith

/--
**Slots at or below the per-block cost diverge.** If `τ ≤ perBlock`, the
prover falls behind by at least `baseline/τ` blocks every cycle — no
batching schedule keeps up, regardless of `n`.
-/
theorem backlog_diverges {baseline perBlock τ : ℚ}
    (hb : 0 ≤ baseline) (hτpos : 0 < τ) (hpb : τ ≤ perBlock)
    {u₀ : ℚ} (hu₀ : 0 ≤ u₀) :
    ∀ j : ℕ, u₀ + j * (baseline / τ) ≤ backlog baseline perBlock τ u₀ j := by
  have hstep : ∀ {u : ℚ}, 0 ≤ u →
      u + baseline / τ ≤ nextBacklog baseline perBlock τ u := by
    intro u hu
    unfold nextBacklog certTime
    have key : (u + baseline / τ) * τ = u * τ + baseline := by
      field_simp
    rw [le_div_iff₀ hτpos, key]
    nlinarith [mul_le_mul_of_nonneg_left hpb hu]
  intro j
  induction j with
  | zero => simp [backlog]
  | succ j ih =>
    have hnn : (0 : ℚ) ≤ backlog baseline perBlock τ u₀ j := by
      have hge := ih
      have : (0 : ℚ) ≤ u₀ + j * (baseline / τ) := by positivity
      linarith
    have := hstep hnn
    have hcast : ((j + 1 : ℕ) : ℚ) = (j : ℚ) + 1 := by push_cast; ring
    calc u₀ + ((j + 1 : ℕ) : ℚ) * (baseline / τ)
        = (u₀ + (j : ℚ) * (baseline / τ)) + baseline / τ := by rw [hcast]; ring
      _ ≤ backlog baseline perBlock τ u₀ j + baseline / τ := by linarith
      _ ≤ backlog baseline perBlock τ u₀ (j + 1) := this


end ProverTiming

end MoltPetit.Model
