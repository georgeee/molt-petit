import MoltPetit.Results.KeyStealingScheduleResults
import Spec.Model

/-!
# MoltPetit — the scheduled certificate (no floor snapshot)

The certificate wrapper for the scheduled-rotation variant, mirroring
`KeyStealingCert.lean` — but **strictly simpler**, in exactly the way
`georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md` §10 promises:

**The scheduled certificate carries NO floor snapshot.** In the default model
the certificate had to thread an authenticated per-producer floor vector
(`GroundedCertK`) because the in-force index is chain-local: the only way a
`cert + suffix` verifier can check the rotation rules is to be handed the floor
the history built up. That floor was *security-critical* wire data — the
documented `(claim, floors)` authentication contract, with a concrete attack if
the floor arrives unauthenticated. Under the schedule, the in-force generation
is a **pure function of the slot**: the verifier computes `schedule b.slot`
itself and checks `schedule b.slot ≤ b.keyIndex` per suffix block. The
certificate carries exactly what the plain (non-rotation) certificate carries —
tip data + the tail buffer — and **the wire authentication contract
disappears**.

A second simplification, same cause: the corruption budget is a **single global
hypothesis** `ByzantineBounded n (badSched …)`. The default certificate theorem
had to quantify the budget over every attestable history (`AttestedHistoryK`)
because `badKeyrotOn` reads the chain under test; `badSched` takes no chain
argument, so there is nothing to quantify over.

**The core validator (honest accounting — read this).** The full scheduled
validator `validSignedChainSched` includes `validChainK = validChain ∧
keyMonoOk` — the in-band monotone-index bookkeeping inherited from the default
model (kept there for composition: emergency early rotation under
`max(gen s, inForce)`, §10.1 A1). Reconstructing `keyMonoOk` across a
certificate boundary is precisely what forces a floor snapshot — and it is the
**only** validator component that does. But the monotone rule is *not*
load-bearing for scheduled safety: in the default model its safety role was to
imply the in-force pin (`inForcePinned_of_validChainK`); here the pin is
supplied by the schedule directly. So the certificate path runs over the
**core** scheduled validator

    validSignedChainSchedCore = sigsOk ∧ validChain ∧ schedPinned

(signatures + structure/density + the scheduled pin, no `keyMonoOk`), and this
module mirrors the uniqueness/agreement chain at core level — the mirrors are
verbatim, because none of the scheduled proofs ever used `keyMonoOk`. The
EUF-CMA surface is restated over core acceptance (`SchedCoreUnforgeable`):
formally this scopes the same crypto content to a **superset** of accepted
chains (full validity implies core validity, `schedCore_of_validSignedChainSched`),
so it is a (mildly) stronger named assumption — recorded, not hidden:
`schedUnforgeable_of_core` proves it delivers the full-validator surface. Its
plausibility argument is untouched, because the full→core delta is only
`keyMonoOk`, which never entered that argument: the surface's obligation is
per-`(block, sig, j)` — a faithful instantiation (a verifying signature under
a non-stolen registered version is the honest holder's unique slot block)
satisfies it for arbitrary chains, monotone or not, since embedding a
signature in a non-monotone chain manufactures no new verifying pairs. In the
*consumers*, the **pin** is what discharges `¬ Stolen` at the declared index
(`rotated_key_dead_schedCore` bounds the declared index below by the
scheduled generation); the surface's breadth over arbitrary verifying `j` is
unchanged from the full surface and is covered by the registry
version-separation obligation (`KeyStealingScheduleResults.lean`, honest
scope). A deployment that keeps the in-band monotone rule simply also checks
it on the suffix; the safety statement does not need it. (Note the limit of
that option: a suffix-side `keyMonoOk` restores *intra-suffix* monotonicity
only — cross-boundary monotonicity against the certified prefix is exactly
the floor snapshot being dropped, so a certificate-syncing verifier runs at
core scope for the prefix permanently. Safety is unaffected: agreement over
the core superset is strictly stronger, and `badSched` is chain-independent,
so no accounting shifts.)

Contents:

* `validSignedChainSchedCore` + `schedCore_of_validSignedChainSched` — the core
  validator and the full→core implication.
* `rotated_key_dead_schedCore` / `signedDeclared_of_mem_schedCore` — the pin
  and coverage lemmas at core level (the proofs only ever used sigs + pin).
* `sched_oldkey_fork_stale_core` — the tip-staleness corollary (§10.0 claim 2)
  at core scope, certificate-path parity.
* `SchedCoreUnforgeable` + `schedUnforgeable_of_core` — the core EUF-CMA
  surface, and the proof that it implies the full-validator surface.
* `honestSlotsUnique_schedCore`, `sched_deep_block_agreement_core`
  (+ `_of_length`) — the scheduled safety chain at core level (verbatim
  mirrors; the contraction survives: no `Δconf`, no reconciliation induction).
* `GroundedCertSched` — the scheduled certificate derivation: fold checks are
  link + signed + density + the pin `schedule b.slot ≤ b.keyIndex`. Pure
  per-block, **no threaded floor** — the state is exactly the plain
  certificate's (`GroundedCert`) state.
* `groundedCertSched_history` / `groundedCertSched_suffix_history` — history
  reconstruction: a grounded-sched claim + a validated suffix (links, density,
  **the pin**, blockwise declared signatures) rebuild a full core-accepted
  chain rooted at `G`.
* `sched_recent_certified_suffix_agreement` — the certificate-level headline:
  two verifying scheduled certificates grounded in the same genesis, each
  extended by a validated recent suffix, agree on every block `n`-deep in both
  suffixes — global budget, no `Δconf`, no floor, no anchor beyond genesis.
-/

namespace MoltPetit.Model

-- ===========================================================================
-- The core scheduled validator
-- ===========================================================================

/-- Full scheduled validity implies core validity (the core drops `keyMonoOk`). -/
theorem schedCore_of_validSignedChainSched {σ sk pk : Type} {n : Nat}
    {schedule : Nat → Nat} {ops : SigOps σ sk pk} {registry : KeyRegistry pk}
    {sc : SignedChain σ} (h : validSignedChainSched n schedule ops registry sc = true) :
    validSignedChainSchedCore n schedule ops registry sc = true := by
  rw [validSignedChainSched, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hSig, hK⟩, hPin⟩ := h
  rw [validChainK, Bool.and_eq_true] at hK
  rw [validSignedChainSchedCore, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨hSig, hK.1⟩, hPin⟩

theorem validChain_of_validSignedChainSchedCore {σ sk pk : Type} {n : Nat}
    {schedule : Nat → Nat} {ops : SigOps σ sk pk} {registry : KeyRegistry pk}
    {sc : SignedChain σ}
    (h : validSignedChainSchedCore n schedule ops registry sc = true) :
    ValidChain n (stripSigs sc) := by
  rw [validSignedChainSchedCore, Bool.and_eq_true, Bool.and_eq_true] at h
  exact validChain_sound h.1.2

/-- `rotated_key_dead_sched` at core level — the proof only ever used the
signature layer and the pin, so nothing changes. -/
theorem rotated_key_dead_schedCore {σ sk pk : Type} {n : Nat} {schedule : Nat → Nat}
    {ops : SigOps σ sk pk} {registry : KeyRegistry pk} {sc : SignedChain σ}
    (h : validSignedChainSchedCore n schedule ops registry sc = true)
    {sb : SignedBlock σ} (hmem : sb ∈ sc) :
    ops.verify (registry (producerForSlot n sb.block.slot) sb.block.keyIndex)
        sb.block sb.sig = true ∧
    schedule sb.block.slot ≤ sb.block.keyIndex := by
  rw [validSignedChainSchedCore, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hSig, _hV⟩, hPin⟩ := h
  have hmemBlock : sb.block ∈ stripSigs sc :=
    List.mem_map.mpr ⟨sb, hmem, rfl⟩
  have hsb : sigOk n ops registry sb = true := by
    rw [sigsOk, List.all_eq_true] at hSig; exact hSig sb hmem
  rw [sigOk] at hsb
  rw [schedPinned, List.all_eq_true] at hPin
  have hp := hPin sb.block hmemBlock
  rw [decide_eq_true_eq] at hp
  exact ⟨hsb, hp⟩

/-- `sched_oldkey_fork_stale` at core scope (certificate-path parity): an
accepted **core**-valid chain whose tip declares a generation whose era ended
more than `Δ` ago fails the plain recency check — no budget, no honesty
consumed. Tip-only, so hybrid forks (honest prefix + retired-key extension)
are covered; see the full-validator twin's docstring. -/
theorem sched_oldkey_fork_stale_core {σ sk pk : Type} {n : Nat}
    {schedule : Nat → Nat} {ops : SigOps σ sk pk} {registry : KeyRegistry pk}
    {sc : SignedChain σ} {J now Δ : Nat}
    (hVal : validSignedChainSchedCore n schedule ops registry sc = true)
    (hEraOver : ∀ s, schedule s ≤ J → s + Δ < now)
    {t : Block} (hTip : (stripSigs sc).getLast? = some t)
    (hJt : t.keyIndex ≤ J) :
    ¬ now ≤ t.slot + Δ := by
  intro hRec
  have htmem : t ∈ stripSigs sc := by
    have h := blockAt_getLast hTip
    unfold blockAt? at h
    exact List.mem_of_getElem? h
  obtain ⟨sb, hsbmem, hsbeq⟩ := List.mem_map.mp htmem
  have hpin := (rotated_key_dead_schedCore hVal hsbmem).2
  rw [hsbeq] at hpin
  have hgen : schedule t.slot ≤ J := le_trans hpin hJt
  have := hEraOver t.slot hgen
  omega

/-- Declared-signature coverage from the core validator. -/
theorem signedDeclared_of_mem_schedCore {σ sk pk : Type} {n : Nat}
    {schedule : Nat → Nat} {ops : SigOps σ sk pk} {registry : KeyRegistry pk}
    {sc : SignedChain σ}
    (h : validSignedChainSchedCore n schedule ops registry sc = true)
    {B : Block} (hB : B ∈ stripSigs sc) :
    SignedDeclared n ops registry B := by
  obtain ⟨sb, hsbmem, hsbeq⟩ := List.mem_map.mp hB
  obtain ⟨hverify, _⟩ := rotated_key_dead_schedCore h hsbmem
  exact ⟨sb.sig, by rw [hsbeq] at hverify; exact hverify⟩

-- ===========================================================================
-- The core EUF-CMA surface
-- ===========================================================================

/-- The core surface delivers the full-validator surface (full validity implies
core validity, so the core assumption's scope covers every fully-valid chain). -/
theorem schedUnforgeable_of_core {n : Nat} {schedule : Nat → Nat} {Sig sk pk : Type}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    (h : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ) :
    SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ :=
  ⟨fun hVal hmem hRecent hverify hrent hstolen =>
    h.unforgeable (schedCore_of_validSignedChainSched hVal) hmem hRecent hverify
      hrent hstolen⟩

-- ===========================================================================
-- The scheduled safety chain at core level (verbatim mirrors)
-- ===========================================================================

/-- `honestSlotsUnique_sched` at core level — the direct contraction proof,
unchanged: it never consulted `keyMonoOk`. -/
theorem honestSlotsUnique_schedCore
    {n : Nat} {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    (hUnf : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    {sc sc' : SignedChain Sig}
    (hVal  : validSignedChainSchedCore n schedule ops registry sc  = true)
    (hVal' : validSignedChainSchedCore n schedule ops registry sc' = true)
    (hRecent  : ∃ t,  (stripSigs sc ).getLast? = some t ∧ now ≤ t.slot + Δ)
    (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ) :
    HonestSlotsUnique (badSched n schedule rented Stolen) (chainUnionRecord sc sc') := by
  have hVc  : ValidChain n (stripSigs sc)  := validChain_of_validSignedChainSchedCore hVal
  have hVc' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSchedCore hVal'
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
    have hDx := rotated_key_dead_schedCore hVal  hsbxmem
    have hDy := rotated_key_dead_schedCore hVal' hsbymem
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

/-- `sched_deep_block_agreement` at core level: two **core**-accepted chains
sharing genesis, with recent tips, agree on any block `n`-deep in both — the
chain-independent budget, no `Δconf`, no anchor beyond genesis, and now no
`keyMonoOk` either. This is the form the certificate path consumes. -/
theorem sched_deep_block_agreement_core
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hUnf : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    (hBudget : ByzantineBounded n (badSched n schedule rented Stolen))
    (hVal  : validSignedChainSchedCore n schedule ops registry sc  = true)
    (hVal' : validSignedChainSchedCore n schedule ops registry sc' = true)
    (hHead  : blockAt? (stripSigs sc ) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    (hRecent  : ∃ t,  (stripSigs sc ).getLast? = some t ∧ now ≤ t.slot + Δ)
    (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ)
    {k m m' : Nat} {B B' D D' : Block}
    (hB  : blockAt? (stripSigs sc ) k  = some B)  (hB' : blockAt? (stripSigs sc') k  = some B')
    (hD  : blockAt? (stripSigs sc ) m  = some D)  (hD' : blockAt? (stripSigs sc') m' = some D')
    (hDeep  : k + n ≤ m) (hDeep' : k + n ≤ m') :
    B = B' := by
  have hVc  : ValidChain n (stripSigs sc)  := validChain_of_validSignedChainSchedCore hVal
  have hVc' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSchedCore hVal'
  have hSig  : ∀ b ∈ stripSigs sc,  b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_schedCore hVal  hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ SignedDeclared n ops registry b :=
    fun b hb => Or.inr (signedDeclared_of_mem_schedCore hVal' hb)
  have hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hHash hSig hSig'
  have hUniq : HonestSlotsUnique (badSched n schedule rented Stolen) (chainUnionRecord sc sc') :=
    honestSlotsUnique_schedCore hUnf hVal hVal' hRecent hRecent'
  have hGenesis : CommonPrefixUpTo (stripSigs sc) (stripSigs sc') 0 := by
    intro i hi
    have hi0 : i = 0 := Nat.le_zero.mp hi
    subst hi0
    exact ⟨G, hHead, hHead'⟩
  exact deep_block_agreement_of_height_depth hn hBudget hUniq hId hVc hVc'
    chainInRecord_left chainInRecord_right hGenesis hB hB' hD hD' hDeep hDeep'

/-- Depth-from-length form of `sched_deep_block_agreement_core`. -/
theorem sched_deep_block_agreement_core_of_length
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hUnf : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    (hBudget : ByzantineBounded n (badSched n schedule rented Stolen))
    (hVal  : validSignedChainSchedCore n schedule ops registry sc  = true)
    (hVal' : validSignedChainSchedCore n schedule ops registry sc' = true)
    (hHead  : blockAt? (stripSigs sc ) 0 = some G)
    (hHead' : blockAt? (stripSigs sc') 0 = some G)
    (hRecent  : ∃ t,  (stripSigs sc ).getLast? = some t ∧ now ≤ t.slot + Δ)
    (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ)
    {k : Nat} {B B' : Block}
    (hB  : blockAt? (stripSigs sc ) k = some B)
    (hB' : blockAt? (stripSigs sc') k = some B')
    (hLen  : k + n < (stripSigs sc ).length)
    (hLen' : k + n < (stripSigs sc').length) :
    B = B' := by
  obtain ⟨D, hD⟩ : ∃ D, blockAt? (stripSigs sc) (k + n) = some D := by
    unfold blockAt?
    exact ⟨(stripSigs sc)[k + n]'hLen, List.getElem?_eq_getElem hLen⟩
  obtain ⟨D', hD'⟩ : ∃ D', blockAt? (stripSigs sc') (k + n) = some D' := by
    unfold blockAt?
    exact ⟨(stripSigs sc')[k + n]'hLen', List.getElem?_eq_getElem hLen'⟩
  exact sched_deep_block_agreement_core hn hUnf hHash hBudget hVal hVal' hHead hHead'
    hRecent hRecent' hB hB' hD hD' (Nat.le_refl _) (Nat.le_refl _)

-- ===========================================================================
-- The scheduled certificate derivation — no threaded floor
-- ===========================================================================

/-- **History reconstruction for the scheduled certificate** (mirrors
`groundedCertK_history` minus every floor step, plus pin propagation). -/
theorem groundedCertSched_history {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Signed : Block → Prop} {G : Block} {cl : CertClaim}
    (h : GroundedCertSched n schedule Signed G cl) :
    ∃ c : Chain, GroundedHistorySched n schedule Signed G cl c := by
  induction h with
  | genesis hG hSlot hSig hPin =>
    refine ⟨[G], ?_, ?_, by simp [blockAt?], ⟨G, by simp, rfl, rfl, rfl⟩, rfl, ?_,
      fun B hB => by rw [List.mem_singleton] at hB; exact hB ▸ hSig⟩
    · -- validChain n [G]
      rw [validChain, show ([G] : Chain).getLast? = some G from rfl,
        Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨hG, rfl⟩, ?_⟩
      show maturedWindowsDense n [G] G.slot = true
      rw [maturedWindowsDense, List.all_eq_true]
      intro u hu
      have hu' := List.mem_range.mp hu
      have hn1 : n = 1 ∧ u = 0 := by omega
      obtain ⟨rfl, rfl⟩ := hn1
      rw [windowDense, decide_eq_true_eq]
      have : windowCount [G] 0 1 = 1 := by
        simp [windowCount, blockInWindow, hSlot]
      rw [this]
      unfold quorum
      omega
    · -- schedPinned schedule [G]
      simp [schedPinned, hPin]
    · -- length
      have : G.height = 0 := by
        rw [genesisOk, decide_eq_true_eq] at hG
        exact hG.1
      simp [this]
  | extend cl b hcl hH hS hP hSig hPin hD ih =>
    obtain ⟨c, hist⟩ := ih
    obtain ⟨t, hTipEq, htId, htSlot, htHeight⟩ := hist.tip
    have hChild : childOk t b = true := by
      rw [childOk, decide_eq_true_eq]
      exact ⟨by omega, by omega, by rw [hP, htId]⟩
    have hMat := (validChain_sound hist.valid).2.2.2
    have hTipAt : blockAt? c (c.length - 1) = some t := blockAt_getLast hTipEq
    have hAllDense : ∀ u : Nat, u + n ≤ b.slot + 1 →
        windowDense n (c ++ [b]) u = true := by
      intro u hu
      rw [windowDense, decide_eq_true_eq]
      by_cases hOld : u + n ≤ t.slot + 1
      · calc quorum n ≤ windowCount c u n := hMat hTipAt u hOld
          _ ≤ windowCount (c ++ [b]) u n :=
              windowCount_mono (List.sublist_append_left c [b])
      · have hcount := hD u (by omega) hu
        have heq : windowCount (cl.tail ++ [b]) u n = windowCount (c ++ [b]) u n := by
          rw [windowCount_append, windowCount_append, hist.tail_eq,
            windowCount_filter_low (by omega)]
        omega
    refine ⟨c ++ [b], ?_, ?_, ?_, ⟨b, by simp, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
    · exact validChain_append_one hist.valid hTipEq hChild hAllDense
    · -- pin propagation
      rw [schedPinned, List.all_append, Bool.and_eq_true]
      constructor
      · have hPinC := hist.pinned
        rw [schedPinned] at hPinC
        exact hPinC
      · simp [hPin]
    · -- head preserved
      have hcLen : 0 < c.length := by
        have := hist.len_eq
        omega
      have hHead := hist.head
      unfold blockAt? at hHead ⊢
      rw [List.getElem?_append_left hcLen]
      exact hHead
    · -- tail re-filtering
      show (cl.tail ++ [b]).filter (fun x => decide (b.slot + 2 - n ≤ x.slot)) =
        (c ++ [b]).filter fun x => decide (b.slot + 2 - n ≤ x.slot)
      rw [List.filter_append, List.filter_append, hist.tail_eq, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro x _
      by_cases hx : b.slot + 2 - n ≤ x.slot
      · have hlo : cl.tipSlot + 2 - n ≤ x.slot := by omega
        simp [hx, hlo]
      · simp [hx]
    · simp [hist.len_eq, hH]
    · -- every block signed
      intro B hB
      rcases List.mem_append.mp hB with hBc | hBb
      · exact hist.signed B hBc
      · rw [List.mem_singleton] at hBb
        exact hBb ▸ hSig

/-- **Grounded-sched prefix + validated suffix = full core-accepted chain.**
Mirrors `groundedCertK_suffix_history`; the suffix-side rotation check is the
**pin alone** (`schedPinned` over the suffix — computable from each block's own
slot), replacing the default certificate's `keyMonoFrom` against a carried
floor snapshot. -/
theorem groundedCertSched_suffix_history {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Signed : Block → Prop} {G : Block} {cl : CertClaim}
    (hG : GroundedCertSched n schedule Signed G cl)
    {s₁ : Block} {srest : Chain} {sTip : Block}
    (hTipS : (s₁ :: srest).getLast? = some sTip)
    (hLink : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) → u + n ≤ sTip.slot + 1 →
      quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hPinS : schedPinned schedule (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, Signed B) :
    ∃ c : Chain,
      validChain n (c ++ s₁ :: srest) = true ∧
      schedPinned schedule (c ++ s₁ :: srest) = true ∧
      blockAt? (c ++ s₁ :: srest) 0 = some G ∧
      c.length = cl.tipHeight + 1 ∧
      (∀ B ∈ c ++ s₁ :: srest, Signed B) := by
  obtain ⟨c, hist⟩ := groundedCertSched_history hn hG
  obtain ⟨t, hTipEq, htId, htSlot, htHeight⟩ := hist.tip
  have hMat := (validChain_sound hist.valid).2.2.2
  have hTipAt : blockAt? c (c.length - 1) = some t := blockAt_getLast hTipEq
  have hSuffixStrict : StrictSlots (s₁ :: srest) :=
    strictSlots_of_checks (linksOk_isChain hLinks)
  have hSlotsLe : ∀ x ∈ s₁ :: srest, x.slot ≤ sTip.slot := fun x hx =>
    slot_le_tip_of_mem hSuffixStrict hTipS hx
  have hs₁Tip : s₁.slot ≤ sTip.slot := hSlotsLe s₁ (List.mem_cons_self ..)
  have hFullDense : ∀ u, u + n ≤ sTip.slot + 1 →
      quorum n ≤ windowCount (c ++ s₁ :: srest) u n := by
    intro u hu
    by_cases hOld : u + n ≤ t.slot + 1
    · calc quorum n ≤ windowCount c u n := hMat hTipAt u hOld
        _ ≤ windowCount (c ++ s₁ :: srest) u n :=
            windowCount_mono (List.sublist_append_left ..)
    · have hcount := hDense u (by push_cast; omega) hu
      have heq : windowCount (cl.tail ++ s₁ :: srest) u n =
          windowCount (c ++ s₁ :: srest) u n := by
        rw [windowCount_append, windowCount_append, hist.tail_eq,
          windowCount_filter_low (by omega)]
      omega
  have hLinksT : linksOk (t :: s₁ :: srest) = true := by
    rw [show linksOk (t :: s₁ :: srest) =
      (childOk t s₁ && linksOk (s₁ :: srest)) from rfl, Bool.and_eq_true]
    refine ⟨?_, hLinks⟩
    rw [childOk, decide_eq_true_eq]
    exact ⟨by omega, by omega, by rw [hLink.2.2, htId]⟩
  refine ⟨c, ?_, ?_, ?_, hist.len_eq, ?_⟩
  · exact validChain_append_suffix hFullDense (s₁ :: srest) c t rfl
      hist.valid hTipEq hLinksT hSlotsLe
  · -- the pin over the full chain: prefix from the derivation, suffix as checked
    rw [schedPinned, List.all_append, Bool.and_eq_true]
    constructor
    · have hPinC := hist.pinned
      rw [schedPinned] at hPinC
      exact hPinC
    · have hPinS' := hPinS
      rw [schedPinned] at hPinS'
      exact hPinS'
  · have hcLen : 0 < c.length := by
      have := hist.len_eq
      omega
    have hHead := hist.head
    unfold blockAt? at hHead ⊢
    rw [List.getElem?_append_left hcLen]
    exact hHead
  · intro B hB
    rcases List.mem_append.mp hB with hBc | hBs
    · exact hist.signed B hBc
    · exact hSigned B hBs

-- ===========================================================================
-- The certificate-level headline — no floor, global budget, no anchor
-- ===========================================================================

/-- **Certificate-level light-client safety under the scheduled adversary**
(the scheduled analogue of `keyrot_recent_certified_suffix_agreement` — and
strictly simpler, in all three of the promised ways):

1. **No floor snapshot.** The certificate carries the claim alone (tip data +
   tail buffer); the suffix rotation check is `schedPinned` — the verifier
   computes `schedule b.slot` from each block's own slot. The default
   certificate's `(claim, floors)` wire-authentication contract **disappears**:
   there is no floor to authenticate, hence no unauthenticated-floor attack
   surface.
2. **Global budget.** `hBudget` is a single chain-independent hypothesis —
   `badSched` reads no chain, so the default theorem's quantification over
   every attestable history (`AttestedHistoryK`) has nothing to range over.
3. **No `Δconf`.** The scheduled uniqueness proof needs no confirmation gate.

A light client runs this from `O(n)` blocks: claim (tip data + tail of `≤ n−1`
blocks), suffix, and a clock — with `schedule` a public protocol parameter
(e.g. `fun s => s / R`), not wire data.

**Residual static contract (the dynamic one is gone, this one is not).** In
this statement one `schedule` binder couples the certificate derivation
(`hcl`), the suffix pin (`hPinS`), the EUF-CMA surface (`hUnf`), and the
budget (`hBudget`). At the wire level that means: `schedule` is a deployment
constant baked into the verifier alongside `n`, `G`, and the registry — a
verifier that let a certificate or peer *supply* `schedule*` would
reintroduce exactly the attack this theorem removes (with `schedule* ≡ 0`, a
suffix block signed with a stolen retired-generation key passes the pin, and
the budget hypothesis silently becomes near-unsatisfiable). What disappeared
is the **per-certificate dynamic** authentication contract (the floor
vector); the static parameter contract is the same one every deployment
already has for `n` and `G`.

Budget read retroactively — see the honest-scope note in
`KeyStealingScheduleResults.lean` (early windows accumulate later-generation
thefts; the anchor *hypothesis* is what is removed).

Crypto surface: `SchedCoreUnforgeable` (registry EUF-CMA over the **core**
scheduled validator — see the module doc for the honest accounting of core vs
full) + collision resistance over the `SignedDeclared` domain. The corruption
predicate is `badSched` — a pure function of the slot; the two certificates'
histories and both suffixes are judged by the *same* predicate, which is the
anchor-removal device in certificate form. -/
theorem sched_recent_certified_suffix_agreement
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    (hUnf : SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    (hBudget : ByzantineBounded n (badSched n schedule rented Stolen))
    {cl cl' : CertClaim}
    (hcl  : GroundedCertSched n schedule (SignedDeclared n ops registry) G cl)
    (hcl' : GroundedCertSched n schedule (SignedDeclared n ops registry) G cl')
    {s₁ s₁' : Block} {srest srest' : Chain} {sTip sTip' : Block}
    (hTipS  : (s₁  :: srest ).getLast? = some sTip)
    (hTipS' : (s₁' :: srest').getLast? = some sTip')
    (hLink  : s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧
        s₁.prev = some cl.tipId)
    (hLinks : linksOk (s₁ :: srest) = true)
    (hDense : ∀ u : Nat, (cl.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n)
    (hPinS : schedPinned schedule (s₁ :: srest) = true)
    (hSigned : ∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B)
    (hLink' : s₁'.height = cl'.tipHeight + 1 ∧ cl'.tipSlot < s₁'.slot ∧
        s₁'.prev = some cl'.tipId)
    (hLinks' : linksOk (s₁' :: srest') = true)
    (hDense' : ∀ u : Nat, (cl'.tipSlot : Int) + 2 - n ≤ (u : Int) →
        u + n ≤ sTip'.slot + 1 → quorum n ≤ windowCount (cl'.tail ++ s₁' :: srest') u n)
    (hPinS' : schedPinned schedule (s₁' :: srest') = true)
    (hSigned' : ∀ B ∈ s₁' :: srest', SignedDeclared n ops registry B)
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    {i i' : Nat} {B B' : Block}
    (hB  : blockAt? (s₁  :: srest ) i  = some B)
    (hB' : blockAt? (s₁' :: srest') i' = some B')
    (hHeight : cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i')
    (hDeep  : i  + n < (s₁  :: srest ).length)
    (hDeep' : i' + n < (s₁' :: srest').length) :
    B = B' := by
  -- reconstruct the two full core-accepted chains
  obtain ⟨c, hV, hPin, hHead, hLen, hCov⟩ :=
    groundedCertSched_suffix_history hn hcl hTipS hLink hLinks hDense hPinS hSigned
  obtain ⟨c', hV', hPin', hHead', hLen', hCov'⟩ :=
    groundedCertSched_suffix_history hn hcl' hTipS' hLink' hLinks' hDense' hPinS' hSigned'
  -- materialize the signed chains
  obtain ⟨sc, hstrip, hsigs⟩ :=
    exists_signedChain_of_covered (Sig := Sig) fun B hB => hCov B hB
  obtain ⟨sc', hstrip', hsigs'⟩ :=
    exists_signedChain_of_covered (Sig := Sig) fun B hB => hCov' B hB
  have hVal : validSignedChainSchedCore n schedule ops registry sc = true := by
    rw [validSignedChainSchedCore, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨hsigs, by rw [hstrip]; exact hV⟩, by rw [hstrip]; exact hPin⟩
  have hVal' : validSignedChainSchedCore n schedule ops registry sc' = true := by
    rw [validSignedChainSchedCore, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨hsigs', by rw [hstrip']; exact hV'⟩, by rw [hstrip']; exact hPin'⟩
  -- recent tips of the full chains
  have hfullTip : (c ++ s₁ :: srest).getLast? = some sTip := by
    rw [List.getLast?_append, hTipS]
    rfl
  have hfullTip' : (c' ++ s₁' :: srest').getLast? = some sTip' := by
    rw [List.getLast?_append, hTipS']
    rfl
  -- locate the blocks at their global heights
  have hBfull : blockAt? (c ++ s₁ :: srest) (c.length + i) = some B := by
    unfold blockAt? at hB ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hB
  have hB'full : blockAt? (c' ++ s₁' :: srest') (c'.length + i') = some B' := by
    unfold blockAt? at hB' ⊢
    rw [List.getElem?_append_right (by omega)]
    simpa using hB'
  have hkEq : c'.length + i' = c.length + i := by omega
  rw [hkEq] at hB'full
  -- assemble via the core deep-block agreement, at the common global index
  refine sched_deep_block_agreement_core_of_length hn hUnf hHash hBudget hVal hVal'
    (by rw [hstrip]; exact hHead) (by rw [hstrip']; exact hHead')
    ⟨sTip, by rw [hstrip]; exact hfullTip, hRecent⟩
    ⟨sTip', by rw [hstrip']; exact hfullTip', hRecent'⟩
    (k := c.length + i)
    (by rw [hstrip]; exact hBfull)
    (by rw [hstrip']; exact hB'full)
    ?_ ?_
  · rw [hstrip, List.length_append]
    omega
  · rw [hstrip', List.length_append]
    omega

end MoltPetit.Model
