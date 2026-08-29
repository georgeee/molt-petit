import MoltPetit.Model.KeyStealingSchedule

/-!
# MoltPetit — the scheduled main-theorem set (anchor-free light-client safety)

`KeyStealingSchedule.lean` established the anchor-discharging device (the
position-determined generation `schedule s`, the chain-independent `badSched`)
and proved the genesis-shared **deep-block** headline
`sched_deep_block_agreement` directly — no `confirmed_mem_iff_le`, no strong
slot-induction, and **no `Δconf ≥ 2n`**.

This module derives the rest of the main-theorem set in the scheduled model,
mirroring `KeyStealingResults.lean` over `validSignedChainSched`/`badSched`. The
statements read **without any anchor assumption** — only shared genesis, recency
(as the domain scope of `SchedUnforgeable`), and the **chain-independent** global
budget `ByzantineBounded n (badSched …)`:

* `sched_deep_block_agreement_of_length` — the verifier-facing depth-from-length
  form (block `n`-deep in both means `k + n < length`).
* `sched_recent_tip_ancestor_agreement` — the stateless-client statement: two
  scheduled-validated chains sharing genesis, with recent equal-height tips,
  agree on the block `n` below each tip. **No anchor hypothesis beyond genesis.**
* `sched_recent_tip_ancestor_mem` — the consistency (unequal-height) form: the
  `n`-deep ancestor of the lower chain is a block of the other chain too.

Contrast the default-model `keyrot_*` theorems: they carry a confirmation gate
(`hΔ : n ≤ Δconf`, lowered from `2 * n` by the σ-localized route of
`KeyStealingHorizonCore.lean`) and key the budget to a *specific* chain
(`badKeyrotOn … (stripSigs sc)`), reconciled by the confirmed-prefix
induction. Here neither is present —
`badSched` takes no chain argument, so the two chains are judged by the *same*
corruption predicate by construction, which is the entire formal content of
"the recency anchor is discharged" (`KEY_ROTATION_SOUND.md` §10.0).

## Honest scope (read before relying on the anchor-free reading)

* **The budget's retroactive reading.** `Stolen` has no time index, so
  `ByzantineBounded n (badSched …)` must hold in the same retroactive reading
  the default model documents for its budget (`KeyStealingResults.lean`,
  "operational reading"): slot `s` is charged for a theft of ANY generation
  `j ≥ schedule s` *whenever it occurs* — early windows therefore accumulate
  the thefts of all later generations (`j ≥ schedule s` is upward-unbounded,
  reflecting the real capability that a stolen current-generation key can
  forge old slots: the pin is a lower bound, and monotonicity permits a fork
  to start high). A genesis-only stateless client is covered exactly when the
  deployment can assert the budget in this cumulative reading; one that cannot
  keeps the default model's rolling re-anchor. What the schedule removes is
  the **anchor hypothesis** — the fork is judged by the same predicate as the
  real chain, so no checkpoint appears in any statement — not the budget's
  reading. §10.1's "retired-key secrecy is not required" is delivered in its
  precise formal scope: (i) a theft of generation `j` charges exactly the
  slots `s` with `schedule s ≤ j` — the schedule-free per-slot form; for a
  *monotone* schedule that reads "no window at-or-after the generation's
  retirement" (nothing constrains `schedule` in the statements, so the
  per-slot form is the precise one) — and (ii) any accepted chain whose
  **tip** declares a generation whose era ended more than `Δ` ago fails the
  plain recency check with no budget consulted — `sched_oldkey_fork_stale`
  below (tip-only, so hybrid forks that copy an honest prefix and extend with
  retired keys are covered), the formal §10.0 "old-key forks have old tips".
* **Recency.** `hRecent`/`hRecent'` are consumed *only* as the domain scope of
  `SchedUnforgeable` (verified: no other use); the recency premise itself is
  assumed, not derived from a timed model — the §10.4 seam, same as the
  default development. "Anchor discharged" is a statement-level fact: recency
  is a stateless clock check, not a persisted checkpoint.
* **Instantiation obligations** (transfer verbatim from `KeyStealingEUFCMA`,
  `KeyStealingUnique.lean`): the `SchedUnforgeable` conclusion must hold for
  every version `j` the total registry reaches (a registry reusing key
  material across versions makes the surface unsatisfiable — silently
  vacating the theorems), and block ids must commit `keyIndex` (else
  `SignedHashInjective` is uninstantiable once a producer has two live
  versions).
-/

namespace MoltPetit.Model

/-- **Scheduled deep-block agreement, depth from length.** The verifier-facing
shape of `sched_deep_block_agreement`: the explicit `n`-deep descendant
witnesses are discharged from the chains' own lengths. Two chains accepted by
the scheduled signed validator, sharing genesis and with recent tips, agree on
any block `B`/`B'` at the same global height `k` that is at least `n` blocks from
the end of **both** chains (`k + n < length`). Chain-independent budget; no
`Δconf`, no anchor beyond genesis. -/
theorem sched_deep_block_agreement_of_length
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
  exact sched_deep_block_agreement hn hUnf hHash hBudget hVal hVal' hHead hHead'
    hRecent hRecent' hB hB' hD hD' (Nat.le_refl _) (Nat.le_refl _)

-- ===========================================================================
-- The scheduled final light-client theorem: tip-ancestor agreement, no anchor
-- ===========================================================================

/-- **The scheduled light-client safety theorem — anchor-free.** Two chains
accepted by the scheduled signed validator (`validSignedChainSched`) descending
from a shared genesis `G`, each with a tip recent within `Δ` of the verifier's
clock `now`, and the two tips at **equal height**, **agree on the block `n` below
each tip** — the `n`-confirmed ancestor a light client commits to.

This is the scheduled analogue of `keyrot_recent_tip_ancestor_agreement`, but the
statement is strictly leaner: there is **no `Δconf ≥ 2n`** and the budget
`ByzantineBounded n (badSched …)` takes **no chain argument** — the two chains
are judged by the same, position-determined corruption predicate. Beyond the
shared genesis and recency (the domain scope of `SchedUnforgeable`) there is
**no anchor hypothesis** (`KEY_ROTATION_SOUND.md` §10). The defense is entirely
the scheduled index pin (`schedPinned`) plus recency; no key-evolving
signatures. The two operational packages A/B (see `KeyStealingScheduleBudget`)
are what license treating `schedule` as a legitimate function of the slot.

Proof: equal tip heights + `SequentialHeights` (height = list index on a
genesis-rooted chain) force the two chains to the **same length**, so the two
`n`-deep ancestors sit at the **same global height/index**;
`sched_deep_block_agreement_of_length` then collapses them. -/
theorem sched_recent_tip_ancestor_agreement
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
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLong' : n < (stripSigs sc').length)
    (hTipHeight : sTip.height = sTip'.height)
    {B B' : Block}
    (hB  : blockAt? (stripSigs sc ) ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc') ((stripSigs sc').length - 1 - n) = some B') :
    B = B' := by
  have hVc  : ValidChain n (stripSigs sc)  := validChain_of_validSignedChainSched hVal
  have hVc' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSched hVal'
  -- height = list index (SequentialHeights), so equal tip heights ⇒ equal length
  have hTipIdx  : sTip.height  = (stripSigs sc ).length - 1 := hVc.1  (blockAt_getLast hTipS)
  have hTipIdx' : sTip'.height = (stripSigs sc').length - 1 := hVc'.1 (blockAt_getLast hTipS')
  have hLenEq : (stripSigs sc).length - 1 - n = (stripSigs sc').length - 1 - n := by omega
  -- realign the second ancestor to the common global index
  rw [← hLenEq] at hB'
  exact sched_deep_block_agreement_of_length hn hUnf hHash hBudget hVal hVal'
    hHead hHead' ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩ hB hB'
    (by omega) (by omega)

/-- **Consistency form of the scheduled final theorem.** When two recent
scheduled-validated chains have **unequal** tip heights, the `n`-deep ancestor
`B` of the chain with the **lower-or-equal** tip is a **block of the other chain
too**, at least `n` deep there. Scheduled analogue of
`keyrot_recent_tip_ancestor_mem`; same anchor-free budget. -/
theorem sched_recent_tip_ancestor_mem
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
    {sTip sTip' : Block}
    (hTipS  : (stripSigs sc ).getLast? = some sTip)
    (hTipS' : (stripSigs sc').getLast? = some sTip')
    (hRecent  : now ≤ sTip.slot  + Δ)
    (hRecent' : now ≤ sTip'.slot + Δ)
    (hLong  : n < (stripSigs sc ).length)
    (hLe : sTip.height ≤ sTip'.height)
    {B : Block}
    (hB : blockAt? (stripSigs sc) ((stripSigs sc).length - 1 - n) = some B) :
    ∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B := by
  have hVc  : ValidChain n (stripSigs sc)  := validChain_of_validSignedChainSched hVal
  have hVc' : ValidChain n (stripSigs sc') := validChain_of_validSignedChainSched hVal'
  have hTipIdx  : sTip.height  = (stripSigs sc ).length - 1 := hVc.1  (blockAt_getLast hTipS)
  have hTipIdx' : sTip'.height = (stripSigs sc').length - 1 := hVc'.1 (blockAt_getLast hTipS')
  -- the ancestor index k is also n-deep in the taller chain sc'
  set k : Nat := (stripSigs sc).length - 1 - n with hk
  have hkn' : k + n < (stripSigs sc').length := by omega
  obtain ⟨X, hX⟩ : ∃ X, blockAt? (stripSigs sc') k = some X := by
    unfold blockAt?
    exact ⟨(stripSigs sc')[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hBX : B = X :=
    sched_deep_block_agreement_of_length hn hUnf hHash hBudget hVal hVal'
      hHead hHead' ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩ hB hX
      (by omega) hkn'
  exact ⟨k, hkn', by rw [hBX]; exact hX⟩

-- ===========================================================================
-- §10.0 claim 2, formal: a retired-generation fork is stale
-- ===========================================================================

/-- **An old-generation tip is stale** — the formal content of
`KEY_ROTATION_SOUND.md` §10.0's second consequence ("a rotated-out key is
rule-dead at recent slots ⇒ old-key forks have old tips"), and the precise
formal scope of §10.1's "A2 harmless — retired-key secrecy is not required".

**Tip-only** (review-strengthened): if an accepted scheduled chain's tip
declares an index at-or-below `J`, and every era-`≤ J` slot is more than `Δ`
old (`hEraOver`; for `schedule s = s / R` with `R ≥ 1` this is exactly "era
`J` ended more than `Δ` ago" — for a schedule that stops advancing it is
unsatisfiable, correctly: no staleness argument exists then), the tip **fails
the client's plain recency check**. Interior indices are irrelevant, so this
covers the realistic *hybrid* fork — an honest prefix (arbitrary indices)
extended with retired-generation keys: its TIP still declares a retired
generation. In particular it covers a fork built entirely from generations
`≤ J`. The rejection consumes NO corruption budget and no honesty assumption:
it is the pin (`rotated_key_dead_sched`) plus arithmetic — retired-key theft
never threatens a recent-tip client. What such theft still charges is only
the *historical* windows of the budget's retroactive reading (module doc).
Core-validator form (certificate-path parity): `sched_oldkey_fork_stale_core`
in `KeyStealingScheduleCert.lean`. -/
theorem sched_oldkey_fork_stale {σ sk pk : Type} {n : Nat} {schedule : Nat → Nat}
    {ops : SigOps σ sk pk} {registry : KeyRegistry pk} {sc : SignedChain σ}
    {J now Δ : Nat}
    (hVal : validSignedChainSched n schedule ops registry sc = true)
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
  have hpin := (rotated_key_dead_sched hVal hsbmem).2
  rw [hsbeq] at hpin
  have hgen : schedule t.slot ≤ J := le_trans hpin hJt
  have := hEraOver t.slot hgen
  omega

end MoltPetit.Model
