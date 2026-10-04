import MoltPetit.Model.KeyStealingCert
import Spec.Model

/-!
# MoltPetit — the scheduled-rotation variant (the anchor-discharging device)

`georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md` §10 records two optional operational packages
(A: fixed scheduled/shadow rotation without erasure; B: erasure + lockstep
forced rotation) that discharge the recency anchor `H-ANCHOR`, restoring a
**stateless, genesis-only light client**. §10.0 shows both license the *same*
formal device: replace the chain-local in-force index `inForce(c₀, i, s)` by a
**position-determined** generation `schedule s` — a pure function of the slot,
identical for every chain. This file is that device.

The payoff is a genuine **contraction** of the default development: because the
corruption predicate is now chain-independent, the two chains' schedules agree
*definitionally*, so the finality↔uniqueness cycle disappears — no
`confirmed_mem_iff_le`, no strong slot-induction, and **no `Δconf ≥ 2n` gate**.
Honest-slot uniqueness follows directly from the pin + registry EUF-CMA.

* `schedPinned` / `validSignedChainSched` — the schedule-pinned signed validator
  (`schedule s ≤ b.keyIndex`: no block signs under a rotated-out version, where
  "rotated-out" is judged by the public schedule, not the chain's own prefix).
* `rotated_key_dead_sched` — an accepted block verifies under its declared entry,
  whose version is at-or-above `schedule s` (so a rotated-out key is rejected).
* `SchedUnforgeable` — the transparent registry EUF-CMA (same surface as
  `KeyStealingEUFCMA`, over the scheduled validator).
* `badSched` — the induced corruption, **chain-independent by construction**.
* `honestSlotsUnique_sched` — honest-slot uniqueness, proved **directly** (the
  contraction: the `cross` helper needs no `hAgree` step).
* `sched_deep_block_agreement` — the genesis-shared deep-agreement headline: two
  scheduled-validated chains sharing genesis agree on any block `n`-deep in both,
  with a **chain-independent** budget. The recency anchor is discharged — a
  light client trusts only genesis (see §10.1/§10.2 for the two assumption
  packages that justify treating `schedule` as a legitimate function of slot).
-/

namespace MoltPetit.Model

-- ===========================================================================
-- The schedule-pinned validator
-- ===========================================================================

theorem validChain_of_validSignedChainSched {σ sk pk : Type} {n : Nat}
    {schedule : Nat → Nat} {ops : SigOps σ sk pk} {registry : KeyRegistry pk}
    {sc : SignedChain σ} (h : validSignedChainSched n schedule ops registry sc = true) :
    ValidChain n (stripSigs sc) := by
  rw [validSignedChainSched, Bool.and_eq_true, Bool.and_eq_true] at h
  exact (validChainK_sound h.1.2).1

/-- **A rotated-out key is dead (scheduled, validator side).** Every block of an
accepted scheduled chain verifies under its **declared** registry entry, and its
declared index is **at-or-above the scheduled version** — never a rotated-out
one. -/
theorem rotated_key_dead_sched {σ sk pk : Type} {n : Nat} {schedule : Nat → Nat}
    {ops : SigOps σ sk pk} {registry : KeyRegistry pk} {sc : SignedChain σ}
    (h : validSignedChainSched n schedule ops registry sc = true)
    {sb : SignedBlock σ} (hmem : sb ∈ sc) :
    ops.verify (registry (producerForSlot n sb.block.slot) sb.block.keyIndex)
        sb.block sb.sig = true ∧
    schedule sb.block.slot ≤ sb.block.keyIndex := by
  rw [validSignedChainSched, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hSig, _hK⟩, hPin⟩ := h
  have hmemBlock : sb.block ∈ stripSigs sc :=
    List.mem_map.mpr ⟨sb, hmem, rfl⟩
  have hsb : sigOk n ops registry sb = true := by
    rw [sigsOk, List.all_eq_true] at hSig; exact hSig sb hmem
  rw [sigOk] at hsb
  rw [schedPinned, List.all_eq_true] at hPin
  have hp := hPin sb.block hmemBlock
  rw [decide_eq_true_eq] at hp
  exact ⟨hsb, hp⟩

/-- Genesis-or-signed coverage is discharged from the scheduled validator, just
as `keyStealingSigned_of_mem` is from `validSignedChainK'`. -/
theorem signedDeclared_of_mem_sched {σ sk pk : Type} {n : Nat} {schedule : Nat → Nat}
    {ops : SigOps σ sk pk} {registry : KeyRegistry pk} {sc : SignedChain σ}
    (h : validSignedChainSched n schedule ops registry sc = true)
    {B : Block} (hB : B ∈ stripSigs sc) :
    SignedDeclared n ops registry B := by
  obtain ⟨sb, hsbmem, hsbeq⟩ := List.mem_map.mp hB
  obtain ⟨hverify, _⟩ := rotated_key_dead_sched h hsbmem
  exact ⟨sb.sig, by rw [hsbeq] at hverify; exact hverify⟩

-- ===========================================================================
-- The EUF-CMA surface and the chain-independent corruption
-- ===========================================================================

-- ===========================================================================
-- Honest-slot uniqueness — DIRECT (the contraction)
-- ===========================================================================

/-- **Honest-slot uniqueness under the scheduled adversary — proved directly.**
Contrast `honestSlotsUnique_keyrot`, which needed a strong slot-induction and
`confirmed_mem_iff_le` purely to reconcile the two chains' *chain-local* in-force
indices. Here the schedule is chain-independent, so no reconciliation is needed:
`¬ badSched s` gives `∀ j ≥ schedule s, ¬ Stolen i j`, and each chain's block at
slot `s` declares an index `≥ schedule s` (the scheduled pin) and verifies under
it — so registry EUF-CMA pins **both** to the one honest `honestSigned i s`. No
`hAgree`, no induction, **no `Δconf ≥ 2n`**. -/
theorem honestSlotsUnique_sched
    {n : Nat} {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    (hUnf : SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    {sc sc' : SignedChain Sig}
    (hVal  : validSignedChainSched n schedule ops registry sc  = true)
    (hVal' : validSignedChainSched n schedule ops registry sc' = true)
    (hRecent  : ∃ t,  (stripSigs sc ).getLast? = some t ∧ now ≤ t.slot + Δ)
    (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ) :
    HonestSlotsUnique (badSched n schedule rented Stolen) (chainUnionRecord sc sc') := by
  have hVc  : ValidChain n (stripSigs sc)  := validChain_of_validSignedChainSched hVal
  have hVc' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSched hVal'
  intro s hbad B B' hB hB'
  rw [mem_chainUnionRecord] at hB hB'
  obtain ⟨hBmem, hBs⟩ := hB
  obtain ⟨hB'mem, hB's⟩ := hB'
  simp only [badSched, not_or] at hbad
  obtain ⟨hNotRent, hNotStolen⟩ := hbad
  push Not at hNotStolen  -- ∀ j, schedule s ≤ j → ¬ Stolen (producerForSlot n s) j
  -- cross-chain: X ∈ sc at s, Y ∈ sc' at s ⊢ X = Y — no agreement step needed
  have cross : ∀ (X Y : Block), X ∈ stripSigs sc → Y ∈ stripSigs sc' →
      X.slot = s → Y.slot = s → X = Y := by
    intro X Y hXc hYc' hXs hYs
    obtain ⟨sbx, hsbxmem, hsbxeq⟩ := List.mem_map.mp hXc
    obtain ⟨sby, hsbymem, hsbyeq⟩ := List.mem_map.mp hYc'
    have hDx := rotated_key_dead_sched hVal  hsbxmem
    have hDy := rotated_key_dead_sched hVal' hsbymem
    have hsbxslot : sbx.block.slot = s := by rw [hsbxeq]; exact hXs
    have hsbyslot : sby.block.slot = s := by rw [hsbyeq]; exact hYs
    have h1 : honestSigned (producerForSlot n s) s = some X := by
      have := hUnf.unforgeable hVal hsbxmem hRecent hDx.1
        (by rw [hsbxslot]; exact hNotRent)
        (by
          rw [hsbxslot]
          exact hNotStolen sbx.block.keyIndex (by rw [← hsbxslot]; exact hDx.2))
      rwa [hsbxslot, hsbxeq] at this
    have h2 : honestSigned (producerForSlot n s) s = some Y := by
      have := hUnf.unforgeable hVal' hsbymem hRecent' hDy.1
        (by rw [hsbyslot]; exact hNotRent)
        (by
          rw [hsbyslot]
          exact hNotStolen sby.block.keyIndex (by rw [← hsbyslot]; exact hDy.2))
      rwa [hsbyslot, hsbyeq] at this
    rw [h1] at h2; exact Option.some.inj h2
  rcases hBmem with hBc | hBc' <;> rcases hB'mem with hB'c | hB'c'
  · exact strictSlots_unique hVc.2.1 hBc hB'c (hBs.trans hB's.symm)
  · exact cross B B' hBc hB'c' hBs hB's
  · exact (cross B' B hB'c hBc' hB's hBs).symm
  · exact strictSlots_unique hVc'.2.1 hBc' hB'c' (hBs.trans hB's.symm)

-- ===========================================================================
-- The genesis-shared deep-agreement headline — anchor discharged
-- ===========================================================================

/-- **Scheduled deep-block agreement (the anchor-discharged headline).** Two
chains accepted by the scheduled signed validator, sharing genesis, with recent
tips, agree on any block `n`-deep in both — under key theft with the
**chain-independent** budget `ByzantineBounded n (badSched …)`. Because the
corruption predicate is a pure function of the slot, this budget is a global fact
a light client accepts without trusting either chain, and the theorem needs no
`Δconf`, no confirmed-prefix reconciliation, and no anchor beyond the shared
genesis. This is the formal content of `georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md` §10 — the two
operational packages (A/B) are the two assumptions that license treating
`schedule` as a legitimate function of the slot. -/
theorem sched_deep_block_agreement
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hUnf : SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    (hBudget : ByzantineBounded n (badSched n schedule rented Stolen))
    (hVal  : validSignedChainSched n schedule ops registry sc  = true)
    (hVal' : validSignedChainSched n schedule ops registry sc' = true)
    (hHead  : blockAt? (stripSigs sc ) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    (hRecent  : ∃ t,  (stripSigs sc ).getLast? = some t ∧ now ≤ t.slot + Δ)
    (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ)
    {k m m' : Nat} {B B' D D' : Block}
    (hB  : blockAt? (stripSigs sc ) k  = some B)  (hB' : blockAt? (stripSigs sc') k  = some B')
    (hD  : blockAt? (stripSigs sc ) m  = some D)  (hD' : blockAt? (stripSigs sc') m' = some D')
    (hDeep  : k + n ≤ m) (hDeep' : k + n ≤ m') :
    B = B' := by
  have hVc  : ValidChain n (stripSigs sc)  := validChain_of_validSignedChainSched hVal
  have hVc' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSched hVal'
  have hSig  : ∀ b ∈ stripSigs sc,  b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_sched hVal  hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_sched hVal' hb)
  have hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hHash hSig hSig'
  have hUniq : HonestSlotsUnique (badSched n schedule rented Stolen) (chainUnionRecord sc sc') :=
    honestSlotsUnique_sched hUnf hVal hVal' hRecent hRecent'
  have hGenesis : CommonPrefixUpTo (stripSigs sc) (stripSigs sc') 0 := by
    intro i hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    exact ⟨G, hHead, hHead'⟩
  exact deep_block_agreement_of_height_depth hn hBudget hUniq hId hVc hVc'
    chainInRecord_left chainInRecord_right hGenesis hB hB' hD hD' hDeep hDeep'

end MoltPetit.Model
