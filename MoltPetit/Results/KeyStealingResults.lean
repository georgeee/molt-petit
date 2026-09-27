import MoltPetit.Model.KeyStealingUnique
import MoltPetit.Model.KeyStealingHorizonCore

/-!
# MoltPetit — light-client safety under the key-stealing adversary
(Phase 3 core)

This module assembles the Phase-2 pieces into the light-client deep-block-agreement
**core** under the **strong key-stealing adversary** (`georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md`
v3): two **index-pinned signed chains** (`validSignedChainK'`) with recent tips
and a shared genesis agree on every block that is `n`-deep in both — even though
a stolen delegate key can sign anything, at any slot, forever. The defense rests
entirely on the validator's **in-force index pin** (`validChainK'`) plus
**recency**, never on forward security.

The theorem is the key-rotation strengthening of the model deep-block agreement
`deep_block_agreement_of_height_depth` (`Safety.lean`). It consumes, over the
**same** corruption predicate `badKeyrotOn … (stripSigs sc)` and record
`chainUnionRecord sc sc'`:

* **P2-A** the induced Byzantine budget `ByzantineBounded n (badKeyrotOn …)` — a
  named hypothesis here (its rent-budget + per-window-theft-rate justification is
  off the light-client critical path; see `georgeee/mini-consensus-lean: PHASE2_DESIGN.md` increment I3);
* **P2-B** honest-slot uniqueness, consumed in its σ-localized strengthening
  `honestSlotsUnique_keyrot_horizon` (`KeyStealingHorizonCore.lean`, this module's
  import), which needs only `n ≤ Δconf` — the cycle-breaking result;
* **P2-C** record id-injectivity `idInjective_keyrot` from collision resistance.

**Honest scope (no overclaim).** The landed result is `keyrot_deep_block_agreement`
— the deep-block-agreement **core**, stated directly over the two signed chains
with explicit `n`-deep witnesses. (Historical note: the certificate suffix
wrapper this header once recorded as future work has since landed —
`keyrot_recent_certified_suffix_agreement` in `Model/KeyStealingCert.lean` —
so seam (i) below is CLOSED; it is kept for the record.) Two seams were
isolated as named hypotheses / future work:
(i) [closed, see above] the constant-size-certificate *suffix* wrapper — a
`GroundedCertK'` reconstruction analogous to `grounded_suffix_history`, which
lets a light client run this off a recursive certificate rather than the full
chain; and
(ii) the Role-B long-range / old-key-fork exclusion from the weak-subjectivity
anchor `H-ANCHOR` (increment I4), which is what makes the strong-model story
honest beyond the confirmed/recent zone and is **not** derivable from uniqueness.
Neither is folded in silently: this theorem's conclusion is exactly the
deep-block agreement its hypotheses support (recent/confirmed-zone agreement —
long-range old-key forks are excluded only by the named `H-ANCHOR` seam, not
proved here).

## Assumptions ledger for `keyrot_recent_tip_ancestor_agreement` (read before relying on it)

Every hypothesis, and why it faithfully represents the model — nothing else is
assumed, and the conclusion `B = B'` (the two recent chains agree on the
`n`-confirmed ancestor below each tip) holds for *any* instantiation satisfying
them:

* `hEUF : KeyStealingEUFCMA …` — **the only crypto trust surface.** Plain
  existential-unforgeability over the *static versioned key directory*: a
  signature verifying a block under participant `i`'s registered key at version
  `j`, with `dk(i,j)` **not stolen** and the slot not rented, on a recent accepted
  chain, *is* `i`'s honest unique slot-block. The verifying version `j` is
  **explicit** — `inForce` is **not** baked in; the link "the verified version is
  never a rotated-out one" (`inForce ≤ j`) is the *proven* theorem
  `rotated_key_dead`, wired in by `versionedUnforgeable_of_keyStealingEUFCMA`.
  **No forward security**: `Stolen i j`
  is not time-indexed (a stolen key forges forever). **Provenance:** this surface is
  *assumed* (a named primitive), **not** reduced to the timed model the way the
  classical `SigUnforgeableRecent` is (`sigUnforgeableRecent_of_timed`) — because
  the strong adversary refuses `NoBackdate`/forward security, that reduction is
  unavailable by design. The index-pin half *is* proven (`rotated_key_dead`); only
  the bare recency-scoped registry EUF-CMA is assumed.
* `hHash : SignedHashInjective (KeyStealingSigned n ops registry) G` — hash
  collision-resistance, scoped to the *concrete* domain of genesis-or-actually-
  signed blocks (`KeyStealingSigned` = "carries a verifying registry signature").
* `hBudget : ByzantineBounded n (badKeyrotOn …(stripSigs sc))` — the **standard
  `1/3` BFT bound** over the honest induced corruption `badKeyrotOn = rented ∨
  some-not-yet-rotated-out-key-stolen (∃ j ≥ inForce, Stolen i j)`. This is the
  **healing budget**: a theft of the producer's *live* key makes its slots bad
  until the emergency rotation confirms — an exposure of announcement-delay
  plus `Δconf` slots (the announcement must first land in an owned,
  non-censored slot; the theorems need only `n ≤ Δconf`, and with
  `Δconf = 2n` the exposure is ≤ 2 of the producer's own slots, one per
  window), after which the stolen version drops below the
  in-force floor and the slots heal. Arithmetic sanity: a producer owns one
  slot per `n`-window, so a single live-key theft costs ≤ 1 bad slot per window
  during exposure — within `maxByzantine n = ⌊(n-1)/3⌋` for `n ≥ 4` (for
  `n ≤ 3` the budget is zero and *any* corruption voids `hBudget`). Note the
  **future-version branch**: a stolen `j > inForce` also counts bad — until the
  floor passes `j`, which no rotation is forced to do — so the healing narrative
  covers live-key theft; theft of *future* keys is excluded in practice by the
  named `H-IND` instantiation property (a theft of `dk(i,j)` yields no
  `dk(i,j')` for `j' > j`), which is exactly what keeps `hBudget` satisfiable.
  `H-IND` appears in the Lean only through this hypothesis — it is the
  instantiation-level justification of `hBudget`, not a formalized premise.
  Keying the predicate to `sc`'s in-force schedule (rather than `sc'`'s) is
  reconciled inside the proof by the opt-A strong slot-induction: at each slot
  the two chains' in-force indices are *proved equal* on the confirmed zone
  (`confirmed_mem_iff_le` → `inForce_agreement_of_confirmed_eq`) before the
  budgeted predicate is consulted — the choice of witness chain does not change
  which slots the proof treats as corrupt. **I3 is closed**: `hBudget` need not
  be assumed jointly — `induced_byzantine_bounded`
  (`KeyStealingBudget.lean`) derives it from a rent budget `R` (slots per
  window) plus a theft rate `T` (exposed producers per window) with
  `R + T ≤ ⌊(n-1)/3⌋`, via the union no-double-count bound and the per-window
  producer↔slot injection.
* `hVal`, `hVal'` — the validator (`validSignedChainK'`: signatures + structure +
  index pin) accepts both chains. **From these, genesis-or-signed coverage is
  *derived*, not assumed** (`keyStealingSigned_of_mem`): every block of an accepted
  chain — genesis included, as `sigsOk` requires — carries a verifying signature.
* `hHead`, `hHead'` — both chains' block at height 0 is the same genesis `G`.
* `hRecent`, `hRecent'` — both tips are within `Δ` of the clock. **Load-bearing
  only as the domain scope of `hEUF`** (the `H-ANCHOR` weak-subjectivity
  boundary). Recency *scopes* the crypto bundle to a `Δ`-fresh window — it does
  not by itself make the bundle derivable (see the `KeyStealingEUFCMA`
  provenance note: the honest-signing-discipline half is assumed, and the
  repo's own `noBackdate_independent` shows such discipline is not free); the
  agreement argument itself uses no recency. Read the theorem's strength as
  exactly that of the recency-scoped surface — long-range old-key forks are out
  of scope by this premise, not refuted. **The scope of that exclusion is now
  pinned down** (`KeyStealingLongRange.lean`): an accepted fork carrying a
  rotated-out-key block `Δconf` past the rotation announcement provably shares
  *no* prefix reaching the announcement (`recent_oldkey_fork_is_longrange`) —
  it branched strictly before it. `H-ANCHOR` therefore reduces to its
  irreducible weak-subjectivity content: ruling out pre-anchor branches.
  **Operational reading — no per-rotation re-anchoring.** The theorem's only
  root hypothesis is the shared *genesis*: a genesis-only client is covered
  provided `hBudget` holds in its honest **retroactive** reading (`Stolen` has
  no time index, so the budget bounds, per *historical* window, the then-live
  keys that *ever* leak — including retired versions leaking years later). A
  deployment unwilling to assume retired keys stay secret forever keeps a
  rolling anchor instead: a running client re-anchors implicitly at every
  verified certificate; only an offline/fresh client needs a checkpoint
  younger than the deployment's key-leak horizon. The horizon is set by
  leakage risk over time, not rotation frequency — rotations never force
  re-anchoring.
* `hLong`, `hLong'`, `hTipHeight`, `hB`, `hB'` — structural: each chain is longer
  than `n`, the two tips are at equal height, and `B`/`B'` are the blocks `n` below
  each tip.

The free parameters `Stolen`, `rented`, `honestSigned` are universally quantified
model inputs; instantiating any of them adversarially only makes the *hypotheses*
harder to meet, never the conclusion easier — so none can trivialise the theorem.
The index pin is a **proven theorem** (`rotated_key_dead`), not a hypothesis.
-/

namespace MoltPetit.Model

-- ===========================================================================
-- The genesis-or-signed coverage is not a free assumption: it is what the
-- validator already checks. We make `Signed` concrete and discharge it.
-- ===========================================================================

/-- **The faithful "this block carries a verifying signature" predicate.** `B` is
signed iff some signature verifies it under its designated producer's registered
key at **some** version `j`. This is exactly the domain of blocks an adversary
(honest or holding a stolen key) can ever put on the wire — the honest domain over
which hash collision-resistance (`SignedHashInjective`) is assumed; it is **not** a
free predicate a caller could weaken. The signature layer's `sigsOk`
(`sigOk = ops.verify (registry (producer, keyIndex)) …`) is precisely this. -/
def KeyStealingSigned {Sig sk pk : Type} (n : Nat) (ops : SigOps Sig sk pk)
    (registry : KeyRegistry pk) (B : Block) : Prop :=
  ∃ (sig : Sig) (j : Nat),
    ops.verify (registry (producerForSlot n B.slot) j) B sig = true

/-- **The validator discharges genesis-or-signed coverage.** Every block of an
accepted index-pinned signed chain is `KeyStealingSigned` — directly from the
`sigsOk` half of `validSignedChainK'`. So `hSig`/`hSig'` in the headline theorems
are not an extra assumption: with `Signed := KeyStealingSigned n ops registry` they
follow from validator acceptance (this lemma), and only collision-resistance over
this concrete domain remains. -/
theorem keyStealingSigned_of_mem {Sig sk pk : Type} {n Δconf : Nat}
    {ops : SigOps Sig sk pk} {registry : KeyRegistry pk} {sc : SignedChain Sig}
    (hVal : validSignedChainK' n Δconf ops registry sc = true)
    {B : Block} (hB : B ∈ stripSigs sc) :
    KeyStealingSigned n ops registry B := by
  obtain ⟨sb, hsbmem, hsbeq⟩ := List.mem_map.mp hB
  rw [validSignedChainK', Bool.and_eq_true] at hVal
  have hsig : sigOk n ops registry sb = true := by
    have h := hVal.1
    rw [sigsOk, List.all_eq_true] at h
    exact h sb hsbmem
  rw [sigOk] at hsig
  refine ⟨sb.sig, B.keyIndex, ?_⟩
  rw [hsbeq] at hsig
  exact hsig


/-- **Light-client safety under the key-stealing adversary (deep-block core).**
Two index-pinned signed chains (`validSignedChainK'`) sharing genesis, with tips
recent within `Δ` of `now`, agree on any block `B`/`B'` sitting at the same global
height `k` that is `n`-deep in both chains (each has a descendant `m`, `m'` at
height `≥ k + n`). The corruption witness chain is fixed to `stripSigs sc`, so the
`sc`-side in-force premise of `VersionedUnforgeable` is reflexive; the `sc'`-side
is reconciled by the confirmed-prefix agreement inside
`honestSlotsUnique_keyrot_horizon` (the σ-localized route: `n ≤ Δconf`
suffices).

Hypotheses, in order: `hEUF` the **primitive registry-level EUF-CMA**
(`KeyStealingEUFCMA` — a verifying signature under a non-stolen key version is the
honest block; no forward security; the index pin is supplied internally by
`rotated_key_dead` via `versionedUnforgeable_of_keyStealingEUFCMA`); `hHash`
collision resistance on genesis-or-signed blocks; `hBudget` the induced Byzantine
budget (P2-A, named); validator acceptance
of both chains; the genesis-or-signed coverage of each chain; recent tips; shared
genesis; and the two same-height blocks with their `n`-deep witnesses. -/
theorem keyrot_deep_block_agreement
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    {Signed : Block → Prop} {G : Block}
    {sc sc' : SignedChain Sig}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective Signed G)
    (hBudget : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc)))
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    (hSig  : ∀ B ∈ stripSigs sc,  B = G ∨ Signed B)
    (hSig' : ∀ B ∈ stripSigs sc', B = G ∨ Signed B)
    (hRecent  : ∃ t,  (stripSigs sc ).getLast? = some t ∧ now ≤ t.slot + Δ)
    (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ)
    (hGenesis : CommonPrefixUpTo (stripSigs sc) (stripSigs sc') 0)
    {k m m' : Nat} {B B' D D' : Block}
    (hB  : blockAt? (stripSigs sc)  k  = some B)
    (hB' : blockAt? (stripSigs sc') k  = some B')
    (hD  : blockAt? (stripSigs sc)  m  = some D)
    (hD' : blockAt? (stripSigs sc') m' = some D')
    (hDeep  : k + n ≤ m)
    (hDeep' : k + n ≤ m') :
    B = B' := by
  have hVc  : ValidChain n (stripSigs sc) := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal;  exact (validChainK'_sound hVal.2).1
  have hVc' : ValidChain n (stripSigs sc') := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal'; exact (validChainK'_sound hVal'.2).1
  have hId : IdInjective (chainUnionRecord sc sc') := idInjective_keyrot hHash hSig hSig'
  have hUniq : HonestSlotsUnique (badKeyrotOn n Δconf rented Stolen (stripSigs sc))
      (chainUnionRecord sc sc') :=
    honestSlotsUnique_keyrot_horizon hn hΔ
      (versionedUnforgeable_of_keyStealingEUFCMA hEUF)
      hBudget hId hVal hVal' hRecent hRecent'
  exact deep_block_agreement_of_height_depth hn hBudget hUniq hId hVc hVc'
    chainInRecord_left chainInRecord_right hGenesis hB hB' hD hD' hDeep hDeep'

/-- **Directly-consumable form: depth from chain length.** The verifier-facing
shape of `keyrot_deep_block_agreement`: it discharges the explicit `n`-deep depth
witnesses from the chains' own lengths. Two index-pinned signed chains with recent
tips and shared genesis agree on any block `B`/`B'` sitting at the same height `k`
that is at least `n` blocks from the end of **both** chains (`k + n < length`) —
the in-chain analogue of "`B` is `n`-confirmed". Same named hypotheses as
`keyrot_deep_block_agreement`; the only change is `hLen`/`hLen'` (block-is-deep
stated by length) replacing the supplied descendant witnesses. -/
theorem keyrot_deep_block_agreement_of_length
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    {Signed : Block → Prop} {G : Block}
    {sc sc' : SignedChain Sig}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective Signed G)
    (hBudget : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc)))
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    (hSig  : ∀ B ∈ stripSigs sc,  B = G ∨ Signed B)
    (hSig' : ∀ B ∈ stripSigs sc', B = G ∨ Signed B)
    (hRecent  : ∃ t,  (stripSigs sc ).getLast? = some t ∧ now ≤ t.slot + Δ)
    (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ)
    (hGenesis : CommonPrefixUpTo (stripSigs sc) (stripSigs sc') 0)
    {k : Nat} {B B' : Block}
    (hB  : blockAt? (stripSigs sc)  k = some B)
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
  exact keyrot_deep_block_agreement hn hΔ hEUF hHash hBudget hVal hVal'
    hSig hSig' hRecent hRecent' hGenesis hB hB' hD hD' (Nat.le_refl _) (Nat.le_refl _)

-- ===========================================================================
-- The final light-client theorem: tip-ancestor agreement under key theft +
-- confirmation-gated key rotation (n ≤ Δconf)
-- ===========================================================================

/-- **The final light-client safety theorem under the key-stealing adversary.**
Two **index-pinned signed chains** (`validSignedChainK'`) descending from a shared
genesis `G`, each with a tip recent within `Δ` of the verifier's clock `now` and
the two tips at **equal height**, **agree on the block `n` below each tip** — the
`n`-confirmed ancestor a light client commits to.

This is the natural endpoint of the development: it integrates, in one statement,
the **strong key-stealing adversary** (a stolen delegate key `dk(i,j)` signs
anything, any slot, forever — captured by `Stolen`/`badKeyrotOn`, with `hEUF` the
primitive registry-level EUF-CMA that re-assumes **no** forward security) and the
**`n ≤ Δconf` confirmation-gated key rotation** (`hΔ`: a rotation only takes
force once `Δconf`-deep; the σ-localized horizon route of
`KeyStealingHorizonCore.lean` strengthened the opt-A `2n` gate to `n`). The
defense is
entirely the validator's **in-force index pin** (`validChainK'`) plus **recency**;
no key-evolving signatures. It is the key-rotation analogue of the audited
`ts_recent_tip_ancestor_agreement`, stated over the model's signed pinned
validator (the compact-certificate *presentation* of a chain is an orthogonal
optimisation and is not part of the adversary model).

Proof: equal tip heights + `SequentialHeights` (height = list index on a
genesis-rooted chain) force the two chains to the **same length**, so the two
`n`-deep ancestors sit at the **same global height/index**;
`keyrot_deep_block_agreement_of_length` then collapses them.

What is and isn't assumed. The **only** crypto trust surface is `hEUF`
(`KeyStealingEUFCMA`, the transparent registry-level EUF-CMA — the index pin is the
*proven* `rotated_key_dead`, not an assumption) and `hHash` (collision resistance,
over the concrete signed domain `KeyStealingSigned`). Genesis-or-signed coverage is
**not** assumed: it is discharged inside the proof from `hVal`/`hVal'`
(`keyStealingSigned_of_mem`). `hBudget` is the standard `1/3` Byzantine bound over
the honest induced corruption `badKeyrotOn`. **Recency** (`hRecent`/`hRecent'`) is
load-bearing **only** as the *domain scope* of `hEUF` — it is the `H-ANCHOR`
weak-subjectivity boundary that makes the EUF-CMA assumption admissible (an old,
patiently-harvested signature is out of scope); the agreement argument itself
(`confirmed_mem_iff_le`) uses **no** recency. So a reader should read the strength
of this theorem as exactly the strength of a recency-scoped EUF-CMA.

Remaining named seams (not folded in, see the module doc): the induced budget
`hBudget` (I3), and the `H-ANCHOR`/I4 long-range exclusion above — so this is
recent/confirmed-zone safety, exactly as its hypotheses state. -/
theorem keyrot_recent_tip_ancestor_agreement
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    (hBudget : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc)))
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
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
  have hVc  : ValidChain n (stripSigs sc) := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal;  exact (validChainK'_sound hVal.2).1
  have hVc' : ValidChain n (stripSigs sc') := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal'; exact (validChainK'_sound hVal'.2).1
  -- genesis-or-signed coverage is discharged from the validator (not assumed)
  have hSig  : ∀ b ∈ stripSigs sc,  b = G ∨ KeyStealingSigned n ops registry b :=
    fun b hb => Or.inr (keyStealingSigned_of_mem hVal  hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ KeyStealingSigned n ops registry b :=
    fun b hb => Or.inr (keyStealingSigned_of_mem hVal' hb)
  -- shared genesis from the two genesis blocks
  have hGenesis : CommonPrefixUpTo (stripSigs sc) (stripSigs sc') 0 := by
    intro k hk
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    exact ⟨G, hHead, hHead'⟩
  -- height = list index (SequentialHeights), so equal tip heights ⇒ equal length
  have hTipIdx  : sTip.height  = (stripSigs sc ).length - 1 := hVc.1  (blockAt_getLast hTipS)
  have hTipIdx' : sTip'.height = (stripSigs sc').length - 1 := hVc'.1 (blockAt_getLast hTipS')
  have hLenEq : (stripSigs sc).length - 1 - n = (stripSigs sc').length - 1 - n := by omega
  -- realign the second ancestor to the common global index
  rw [← hLenEq] at hB'
  exact keyrot_deep_block_agreement_of_length hn hΔ hEUF hHash hBudget hVal hVal'
    hSig hSig' ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩ hGenesis hB hB'
    (by omega) (by omega)

/-- **Consistency form of the final theorem: the `n`-confirmed ancestor of the
lower chain lies on the other chain.** When two recent index-pinned signed chains
(`validSignedChainK'`) have **unequal** tip heights, pointwise ancestor equality is
false for a benign reason — they are the same history observed at different depths,
so their respective `n`-deep ancestors are parent/child, not equal. What holds, and
what a light client uses: the `n`-deep ancestor `B` of the chain with the
**lower-or-equal** tip is a **block of the other chain too**, at least `n` deep
there. Same strong key-stealing adversary + `n ≤ Δconf` confirmation-gated
rotation (the σ-localized horizon strengthening); key-rotation analogue of
`ts_recent_tip_ancestor_mem`.

Proof: with `sc` the lower-or-equal chain, its `n`-deep ancestor sits at global
index `k = |sc| − 1 − n`, which (because `sc'` is at least as tall) is also `n`-deep
in `sc'`; the block `sc'` carries there equals `B` by
`keyrot_deep_block_agreement_of_length`, witnessing membership. -/
theorem keyrot_recent_tip_ancestor_mem
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    (hBudget : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc)))
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
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
  have hVc  : ValidChain n (stripSigs sc) := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal;  exact (validChainK'_sound hVal.2).1
  have hVc' : ValidChain n (stripSigs sc') := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal'; exact (validChainK'_sound hVal'.2).1
  have hSig  : ∀ b ∈ stripSigs sc,  b = G ∨ KeyStealingSigned n ops registry b :=
    fun b hb => Or.inr (keyStealingSigned_of_mem hVal  hb)
  have hSig' : ∀ b ∈ stripSigs sc', b = G ∨ KeyStealingSigned n ops registry b :=
    fun b hb => Or.inr (keyStealingSigned_of_mem hVal' hb)
  have hGenesis : CommonPrefixUpTo (stripSigs sc) (stripSigs sc') 0 := by
    intro k hk
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    exact ⟨G, hHead, hHead'⟩
  have hTipIdx  : sTip.height  = (stripSigs sc ).length - 1 := hVc.1  (blockAt_getLast hTipS)
  have hTipIdx' : sTip'.height = (stripSigs sc').length - 1 := hVc'.1 (blockAt_getLast hTipS')
  -- the ancestor index k is also n-deep in the taller chain sc'
  set k : Nat := (stripSigs sc).length - 1 - n with hk
  have hkn' : k + n < (stripSigs sc').length := by omega
  obtain ⟨X, hX⟩ : ∃ X, blockAt? (stripSigs sc') k = some X := by
    unfold blockAt?
    exact ⟨(stripSigs sc')[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hBX : B = X :=
    keyrot_deep_block_agreement_of_length hn hΔ hEUF hHash hBudget hVal hVal'
      hSig hSig' ⟨sTip, hTipS, hRecent⟩ ⟨sTip', hTipS', hRecent'⟩ hGenesis hB hX
      (by omega) hkn'
  exact ⟨k, hkn', by rw [hBX]; exact hX⟩

-- ===========================================================================
-- The loss-only adversary: prophylactic rotation is anchor-free
-- ===========================================================================

/-!
## Rotation without theft

The headline theorems above are stated against an adversary that **exports**
keys. A deployment that rotates *prophylactically*, or because an operator
**lost** a key, faces a strictly weaker adversary: losing a key hands the
adversary nothing, and the loser's response is an ordinary index bump the
validator already supports. That adversary is this model at
`Stolen := fun _ _ => False`, so it needs no separate development — but it
does deserve its own statement, because the hypotheses that survive are
markedly fewer.

By `badKeyrotOn_lossOnly` the induced corruption collapses to `rented`, which
carries **no chain argument**. That is the whole point. The anchor `H-ANCHOR`
exists because `badKeyrotOn` reads the in-force index off a witness chain, so
a from-genesis fork is judged by a different predicate than the real chain;
with the theft clause gone the two predicates coincide and the asymmetry
disappears. Concretely, the corollaries below consume:

* a plain **rent budget** `ByzantineBounded n rented` — no healing budget, no
  retroactive reading of retired-key secrecy over all of history;
* the EUF-CMA surface with its theft premise trivial;

and consume **no** `H-IND` (nothing cascades from a theft that never happens)
and **no** key-leak horizon. A genesis-only client is covered outright: there
is no anchor to hold, hence no checkpoint to fetch and no software update
needed to keep rotation safe. What is *not* claimed: this says nothing about a
deployment that also suffers theft — the moment one key is exported, the
`Stolen` clause returns and so does the anchor.
-/

/-- **Prophylactic/loss-driven rotation is anchor-free (equal-tip form).**
`keyrot_recent_tip_ancestor_agreement` specialised to the loss-only adversary
(`Stolen := fun _ _ => False`): two recent index-pinned signed chains rooted in
one genesis agree on the block `n` below each tip, from a **plain rent budget**
alone. -/
theorem keyrot_lossonly_recent_tip_ancestor_agreement
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented (fun _ _ => False)
      honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    (hBudget : ByzantineBounded n rented)
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
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
    B = B' :=
  keyrot_recent_tip_ancestor_agreement hn hΔ hEUF hHash
    (by rw [badKeyrotOn_lossOnly]; exact hBudget)
    hVal hVal' hHead hHead' hTipS hTipS' hRecent hRecent' hLong hLong'
    hTipHeight hB hB'

/-- **Prophylactic/loss-driven rotation is anchor-free (membership form).**
The loss-only specialisation of `keyrot_recent_tip_ancestor_mem`: the `n`-deep
ancestor of the lower-tipped chain is a block of the other chain too, at least
`n` deep there — again from a plain rent budget. -/
theorem keyrot_lossonly_recent_tip_ancestor_mem
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented (fun _ _ => False)
      honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    (hBudget : ByzantineBounded n rented)
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
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
    ∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B :=
  keyrot_recent_tip_ancestor_mem hn hΔ hEUF hHash
    (by rw [badKeyrotOn_lossOnly]; exact hBudget)
    hVal hVal' hHead hHead' hTipS hTipS' hRecent hRecent' hLong hLe hB

end MoltPetit.Model
