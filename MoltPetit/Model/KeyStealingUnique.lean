import MoltPetit.Model.KeyStealing
import MoltPetit.Model.KeyStealingSafety

/-!
# MoltPetit — honest-slot uniqueness under the key-stealing adversary
(Phase 2, increments I2b + I2c)

This module closes the finality↔uniqueness cycle for the strong key-stealing
adversary (`georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md` v3). The cross-chain honest-slot uniqueness
property `honestSlotsUnique_keyrot` is derived by a **single strong induction on
the slot** (opt-A, `georgeee/mini-consensus-lean: PHASE2_DESIGN.md` §7.5), discharged by the bounded safety
core of `KeyStealingSafety.lean`.

* `chainUnionRecord` / `mem_chainUnionRecord` / `chainInRecord_left` /
  `chainInRecord_right` — the slot record built from the two stripped signed
  chains under test (mirrors the `set record` of `Grounded.lean`).
* `idInjective_keyrot` — id injectivity over that record, from hash collision
  resistance on genesis-or-signed blocks.
* `VersionedUnforgeable` — the named **versioned-EUF-CMA + honest-signing**
  crypto surface. The honest-signing map is **version-free**
  (`Nat → Nat → Option Block`): the version enters only through the `¬ Stolen`
  premise, which quantifies over the **not-yet-rotated-out versions** (all
  `j` at-or-above the chain-local `inForce n Δconf (stripSigs sc) …`). That the
  *verifying* version is one of those — never a rotated-out one — is justified by
  `rotated_key_dead` (the validator-side `≤`-pin), through which this surface is
  derived from the primitive. Strictly weaker than v2's `NoBackdate`; it does
  **not** re-assume forward security.
* `honestSlotsUnique_keyrot` — **P2-B**: cross-chain honest-slot uniqueness under
  the key-stealing adversary, with the corruption witness chain fixed to
  `stripSigs sc` (so the `sc`-side in-force premise is reflexive). The `sc'`-side
  in-force premise is reconciled across the two chains by `confirmed_mem_iff_le`
  applied to the strong-induction hypothesis at slots strictly below the
  coexistence slot.
-/

namespace MoltPetit.Model

-- ===========================================================================
-- I2b — the slot record over the two chains under test
-- ===========================================================================

/-- The slot record built from the two stripped signed chains under test: the
blocks of `stripSigs sc` and `stripSigs sc'`, bucketed by slot (mirrors the
`set record` in `Grounded.lean`). -/
def chainUnionRecord {σ : Type} (sc sc' : SignedChain σ) : SlotRecord :=
  fun s => ((stripSigs sc ++ stripSigs sc').filter (fun b => b.slot == s)).toFinset

theorem mem_chainUnionRecord {σ : Type} {sc sc' : SignedChain σ} {s : Nat} {x : Block} :
    x ∈ chainUnionRecord sc sc' s ↔
      (x ∈ stripSigs sc ∨ x ∈ stripSigs sc') ∧ x.slot = s := by
  unfold chainUnionRecord
  simp only [List.mem_toFinset, List.mem_filter, List.mem_append, beq_iff_eq]

theorem chainInRecord_left {σ : Type} {sc sc' : SignedChain σ} :
    ChainInRecord (chainUnionRecord sc sc') (stripSigs sc) := by
  intro k B hk
  unfold blockAt? at hk
  exact mem_chainUnionRecord.mpr ⟨Or.inl (List.mem_of_getElem? hk), rfl⟩

theorem chainInRecord_right {σ : Type} {sc sc' : SignedChain σ} :
    ChainInRecord (chainUnionRecord sc sc') (stripSigs sc') := by
  intro k B hk
  unfold blockAt? at hk
  exact mem_chainUnionRecord.mpr ⟨Or.inr (List.mem_of_getElem? hk), rfl⟩

/-- **Id injectivity over the union record**, from collision resistance on
genesis-or-signed blocks (mirror of `Grounded.lean`'s `hInj`). `Signed`/`G` and
the genesis-or-signed facts are threaded from the certificate plumbing in
Phase 3. -/
theorem idInjective_keyrot {σ : Type} {sc sc' : SignedChain σ}
    {Signed : Block → Prop} {G : Block}
    (hHash : SignedHashInjective Signed G)
    (hSig  : ∀ B ∈ stripSigs sc,  B = G ∨ Signed B)
    (hSig' : ∀ B ∈ stripSigs sc', B = G ∨ Signed B) :
    IdInjective (chainUnionRecord sc sc') := by
  intro s t x x' hxr hx'r hid
  rw [mem_chainUnionRecord] at hxr hx'r
  obtain ⟨hxm, -⟩ := hxr
  obtain ⟨hx'm, -⟩ := hx'r
  exact hHash (hxm.elim (hSig x) (hSig' x)) (hx'm.elim (hSig x') (hSig' x')) hid

-- ===========================================================================
-- I2c — the versioned unforgeability surface + honest-slot uniqueness
-- ===========================================================================

/-- **Primitive registry-level EUF-CMA + honest-signing discipline in the
key-stealing model** — the single, transparent crypto assumption the whole
development rests on. Read literally: *if a signature `sb.sig` verifies a block
`sb.block` under participant `i`'s registered key at **some** version `j`
(`ops.verify (registry i j) …`), the block sits in an accepted index-pinned chain
with a recent tip, `i`'s slot is not rented, and the key `dk(i,j)` is **not
stolen**, then the block is `i`'s honest, unique slot-`sb.block.slot` block.*

Two ingredients are bundled, and naming them separately is important: (1)
**existential unforgeability** over the static versioned key directory — the only
way to obtain a verifying signature under a key you do not hold is to steal it
(`Stolen i j`); and (2) **honest signing discipline within the recent window** —
the honest holder's oracle emits exactly one block per owned slot and no
cross-stamped residue that could land at another slot. (2) is *not* free: the
timed layer explicitly grants a rented node's oracle coerced, cross-stamped
signatures, and `noBackdate_independent` machine-proves that discipline-style
surfaces are **not** derivable from `TimedExecution` alone. Recency is what makes
the bundle *plausible* (only a `Δ`-fresh window must be clean), not what derives
it. Two further instantiation obligations: the conclusion must hold for **every**
version `j` the total registry `KeyRegistry pk = Nat → Nat → pk` reaches (an
instantiation whose registry defaults unregistered versions to a degenerate key
cannot satisfy this surface — under the `≤`-pin any `j ≥ inForce` is reachable
on-chain); and blocks differing only in `keyIndex` must hash differently (the
block id must commit `keyIndex`, as the plonky2 prototype's `block_id` does), or
`SignedHashInjective` is uninstantiable once a producer has two versions.

It is **faithful and minimal**: the verifying version `j` is **explicit** (no
`inForce` is baked in — the connection "the verified version is never a
rotated-out one" (`inForce ≤ j`) is the *separate, proven* theorem
`rotated_key_dead`, wired in by `versionedUnforgeable_of_keyStealingEUFCMA`
below, not assumed here). It re-assumes **no** forward security — `Stolen i j`
is not time-indexed, so a stolen key forges forever; the only defence is the
index pin + recency: theft of a live key is harmful (budgeted) only until the
emergency rotation is `Δconf` deep, after which the stolen version is below the
in-force floor and dead. Recency-scoped (the tip within `Δ` of `now`) marks the
weak-subjectivity boundary `H-ANCHOR`.

**Provenance — the exact boundary of trust.** This surface is **assumed**, not
reduced to the timed model. The classical-adversary analogue
`SigUnforgeableRecent` is *derived* (`sigUnforgeableRecent_of_timed`) from a
`TimedExecution` plus `NoBackdate`, with `noBackdate_independent` witnessing that
the extra assumption has real content. The key-stealing adversary deliberately
**refuses** `NoBackdate`/forward security (`georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md` §1–2), so that
derivation is unavailable by design; `KeyStealingEUFCMA` is therefore taken as a
named primitive. What the development **does** prove on top of it is the index-pin
half: `versionedUnforgeable_of_keyStealingEUFCMA` discharges the "the verifying
version is never rotated-out" step via the proven `rotated_key_dead`, so *only*
the bare recency-scoped registry EUF-CMA is assumed, never the pin. A reader
should read every headline keyrot theorem's strength as exactly "this registry
EUF-CMA assumption holds for recent chains." -/
structure KeyStealingEUFCMA (n Δconf : Nat) {Sig sk pk : Type} (ops : SigOps Sig sk pk)
    (registry : KeyRegistry pk) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop)
    (honestSigned : Nat → Nat → Option Block) (now Δ : Nat) : Prop where
  unforgeable :
    ∀ {sc : SignedChain Sig} {sb : SignedBlock Sig} {j : Nat},
      validSignedChainK' n Δconf ops registry sc = true →
      sb ∈ sc →
      (∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) →
      ops.verify (registry (producerForSlot n sb.block.slot) j) sb.block sb.sig = true →
      ¬ rented sb.block.slot →
      ¬ Stolen (producerForSlot n sb.block.slot) j →
      honestSigned (producerForSlot n sb.block.slot) sb.block.slot = some sb.block

/-- **Versioned-EUF-CMA + honest-signing surface** (an *intermediate* — it is
**derived** from the primitive `KeyStealingEUFCMA` by
`versionedUnforgeable_of_keyStealingEUFCMA`, not assumed independently). It
specialises the unforgeability conclusion to the versions **at-or-above the
in-force index** at the block's slot: for a block of an accepted index-pinned
signed chain with a recent tip, whose producer is not rented and **none of whose
not-yet-rotated-out keys** (chain-local `inForce ≤ j`) is stolen, a verifying
signature came from the honest producer's unique slot call. The specialisation is
exactly where the index pin enters — discharged by `rotated_key_dead` (the
verifying version is the *declared* one, and the pin bounds it below by the
in-force index, so the `∀ j ≥ inForce` premise covers it) — so unlike the raw
primitive this surface needs no explicit `ops.verify` premise. -/
structure VersionedUnforgeable (n Δconf : Nat) {Sig sk pk : Type} (ops : SigOps Sig sk pk)
    (registry : KeyRegistry pk) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop)
    (honestSigned : Nat → Nat → Option Block) (now Δ : Nat) : Prop where
  verified_was_signed :
    ∀ {sc : SignedChain Sig} {sb : SignedBlock Sig},
      validSignedChainK' n Δconf ops registry sc = true →
      sb ∈ sc →
      (∃ t, (stripSigs sc).getLast? = some t ∧ now ≤ t.slot + Δ) →
      ¬ rented sb.block.slot →
      (∀ j, inForce n Δconf (stripSigs sc)
              (producerForSlot n sb.block.slot) sb.block.slot ≤ j →
        ¬ Stolen (producerForSlot n sb.block.slot) j) →
      honestSigned (producerForSlot n sb.block.slot) sb.block.slot = some sb.block

/-- **The index pin makes the primitive EUF-CMA usable: `VersionedUnforgeable`
follows from `KeyStealingEUFCMA`.** This is the step that *uses* the proven
validator pin `rotated_key_dead`: an accepted index-pinned signed block verifies
under its **declared** registry entry, and the pin bounds the declared version
below by the in-force index — so the `∀ j ≥ inForce, ¬ Stolen i j` premise of
`VersionedUnforgeable` covers the declared version, and the primitive's explicit
`ops.verify` premise is discharged by `rotated_key_dead`. Hence the headline
safety theorems can rest on the **transparent** registry-level EUF-CMA assumption,
with the pin genuinely load-bearing rather than silently assumed. -/
theorem versionedUnforgeable_of_keyStealingEUFCMA
    {n Δconf : Nat} {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ) :
    VersionedUnforgeable n Δconf ops registry rented Stolen honestSigned now Δ where
  verified_was_signed hVal hmem hRecent hNotRent hNotStolen :=
    have hDead := rotated_key_dead _ _ _ _ hVal hmem
    hEUF.unforgeable hVal hmem hRecent hDead.1 hNotRent (hNotStolen _ hDead.2)

/-- **P2-B: honest-slot uniqueness under the key-stealing adversary.** With the
corruption witness chain fixed to `stripSigs sc` (so the `sc`-side in-force
premise is reflexive with `¬ badKeyrotOn … s`), the two chains under test agree
on the produced block of every honest slot. Proof: strong induction on the slot
(opt-A) — the `sc'`-side in-force index is reconciled to the `sc`-side via
`confirmed_mem_iff_le`, whose uniqueness obligations land strictly below the
current slot (`Δconf ≥ 2n`), exactly the induction hypothesis. -/
theorem honestSlotsUnique_keyrot
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : 2 * n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat}
    (hUnf : VersionedUnforgeable n Δconf ops registry rented Stolen honestSigned now Δ)
    {sc sc' : SignedChain Sig}
    (hBudget : ByzantineBounded n (badKeyrotOn n Δconf rented Stolen (stripSigs sc)))
    (hId : IdInjective (chainUnionRecord sc sc'))
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
    (hVal' : validSignedChainK' n Δconf ops registry sc' = true)
    (hRecent  : ∃ t,  (stripSigs sc ).getLast? = some t ∧ now ≤ t.slot + Δ)
    (hRecent' : ∃ t', (stripSigs sc').getLast? = some t' ∧ now ≤ t'.slot + Δ)
    (hGenesis : CommonPrefixUpTo (stripSigs sc) (stripSigs sc') 0) :
    HonestSlotsUnique (badKeyrotOn n Δconf rented Stolen (stripSigs sc))
      (chainUnionRecord sc sc') := by
  have hVc  : ValidChain n (stripSigs sc) := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal;  exact (validChainK'_sound hVal.2).1
  have hVc' : ValidChain n (stripSigs sc') := by
    rw [validSignedChainK', Bool.and_eq_true] at hVal'; exact (validChainK'_sound hVal'.2).1
  have hRec  : ChainInRecord (chainUnionRecord sc sc') (stripSigs sc)  := chainInRecord_left
  have hRec' : ChainInRecord (chainUnionRecord sc sc') (stripSigs sc') := chainInRecord_right
  intro s
  induction s using Nat.strongRecOn with
  | ind s IH =>
    intro hbad B B' hB hB'
    rw [mem_chainUnionRecord] at hB hB'
    obtain ⟨hBmem, hBs⟩ := hB
    obtain ⟨hB'mem, hB's⟩ := hB'
    simp only [badKeyrotOn, not_or] at hbad
    obtain ⟨hNotRent, hNotStolen⟩ := hbad
    -- hNotStolen : ¬ ∃ j, inForce … ≤ j ∧ Stolen i j  →  ∀-form
    push_neg at hNotStolen
    -- cross-chain helper: X∈c at s, Y∈c' at s, ¬bad s ⊢ X = Y
    have cross : ∀ (X Y : Block), X ∈ stripSigs sc → Y ∈ stripSigs sc' →
        X.slot = s → Y.slot = s → X = Y := by
      intro X Y hXc hYc' hXs hYs
      obtain ⟨sbx, hsbxmem, hsbxeq⟩ := List.mem_map.mp hXc   -- sbx ∈ sc,  sbx.block = X
      obtain ⟨sby, hsbymem, hsbyeq⟩ := List.mem_map.mp hYc'  -- sby ∈ sc', sby.block = Y
      -- agreement: inForce c' i s = inForce c i s  (via confirmed_mem_iff_le + IH)
      have hAgree : inForce n Δconf (stripSigs sc') (producerForSlot n s) s
                  = inForce n Δconf (stripSigs sc)  (producerForSlot n s) s := by
        apply inForce_agreement_of_confirmed_eq
        intro b hbconf
        exact confirmed_mem_iff_le hn hΔ hBudget hId hVc' hVc hRec' hRec
          (fun k hk => (hGenesis k hk).imp fun _ h => ⟨h.2, h.1⟩)
          hYc' hYs hXc hXs IH b hbconf
      have hsbxslot : sbx.block.slot = s := by rw [hsbxeq]; exact hXs
      have hsbyslot : sby.block.slot = s := by rw [hsbyeq]; exact hYs
      have h1 : honestSigned (producerForSlot n s) s = some X := by
        have := hUnf.verified_was_signed hVal hsbxmem hRecent
          (by rw [hsbxslot]; exact hNotRent)
          (by rw [hsbxslot]; exact hNotStolen)
        rwa [hsbxslot, hsbxeq] at this
      have hNotStolen' : ∀ j, inForce n Δconf (stripSigs sc') (producerForSlot n s) s ≤ j →
          ¬ Stolen (producerForSlot n s) j := by
        rw [hAgree]; exact hNotStolen
      have h2 : honestSigned (producerForSlot n s) s = some Y := by
        have := hUnf.verified_was_signed hVal' hsbymem hRecent'
          (by rw [hsbyslot]; exact hNotRent)
          (by rw [hsbyslot]; exact hNotStolen')
        rwa [hsbyslot, hsbyeq] at this
      rw [h1] at h2; exact Option.some.inj h2
    -- four membership cases
    rcases hBmem with hBc | hBc' <;> rcases hB'mem with hB'c | hB'c'
    · exact strictSlots_unique hVc.2.1 hBc hB'c (hBs.trans hB's.symm)
    · exact cross B B' hBc hB'c' hBs hB's
    · exact (cross B' B hB'c hBc' hB's hBs).symm
    · exact strictSlots_unique hVc'.2.1 hBc' hB'c' (hBs.trans hB's.symm)

end MoltPetit.Model
