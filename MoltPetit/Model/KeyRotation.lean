import MoltPetit.Model.KeyIndex

/-!
# MoltPetit — sound key rotation under a key-stealing adversary (Phase 1)

This module strengthens the *cheap* index reduction of `KeyIndex.lean`
(`indexed_reduces_to_static`, whose hypothesis `keyIndex = e(producer)` is
assumed) into a **discharged validator rule**: the in-force index a block may
sign under is read off the chain's own **confirmed prefix**, so a rotated-out key
cannot extend a chain past its rotation.

See `georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md` for the model and the full proof DAG. Phase 1 (this
file, no adversary yet):

* `inForce` — the in-force delegate index, a pure function of the **confirmed**
  prefix (blocks at least `Δconf` slots back).
* `validChainK'` — `validChainK` plus the in-band pin `inForce ≤ keyIndex`
  (no block signs under a rotated-out version).
* `validChainK'_sound` — `validChainK'` is stronger than `ValidChain`,
  so every original theorem *about accepted chains* (safety, the forged-time
  bound) still applies. Liveness needs the converse (the honest producer's next
  block passes the *stricter* validator), proven in `KeyRotationLiveness.lean`
  as a sharp iff: the extension is accepted exactly when the declared version
  clears the producer's chain floor.
* `deep_block_shared` — membership finality: a block buried `n` slots behind both
  tips is shared across valid chains of one execution (Phase 1c).
* `inForce_agreement` — therefore `inForce` is **execution-global** on the
  confirmed zone, with no assumed agreement hypothesis. This is what makes the
  schedule-keyed corruption predicate `badKeyrot` chain-independent (§2.1).
-/

namespace MoltPetit.Model

-- ===========================================================================
-- The confirmed prefix and the in-force index
-- ===========================================================================

/-- The **confirmed prefix** of `c` as seen from slot `s`: the blocks at least
`Δconf` slots in the past. `Δconf ≥ n` makes these blocks finalized (buried under
a matured, dense window), so all valid chains in one execution agree on them
(`inForce_agreement`, Phase 1b). -/
def confirmedPrefix (Δconf : Nat) (c : Chain) (s : Nat) : Chain :=
  c.filter (fun b => decide (b.slot + Δconf ≤ s))

/-- The **in-force delegate index** of participant `i` as seen from slot `s`:
participant `i`'s key floor over the confirmed prefix. Because it reads only the
confirmed (finalized) prefix, it is the *same* across all valid chains of one
execution in the confirmed zone — the property that pins a rotated-out key dead. -/
def inForce (n Δconf : Nat) (c : Chain) (i s : Nat) : Nat :=
  keyFloor n (confirmedPrefix Δconf c s) i

-- ===========================================================================
-- The index-pinned validator
-- ===========================================================================

/-- The in-band **pin**: no block signs under a **rotated-out** index — every
block's declared `keyIndex` is at least the index in force (by the schedule the
chain itself records) at its slot.

**Why `≤` and not `=`.** An equality pin (`keyIndex = inForce`) would make
rotation *impossible*: the in-force floor only rises when a block carrying a
higher index becomes `Δconf`-deep, and an equality pin forbids any block from
ever carrying a higher index — by induction every producer would be frozen at
its initial index forever, and "a rotated-out key is dead" would be vacuous
(nothing is ever rotated out). The `≤` pin is the faithful rule: a producer
**announces** a rotation by signing under the new, higher index (allowed —
`inForce ≤ new`), the announcement confirms after `Δconf` slots, the floor
rises, and from then on the **old** index is below the floor and every block
declaring it is rejected. Theft of the in-force key is thus harmful only for
the ≤ `Δconf` window until the emergency rotation confirms; the corruption
budget (`badKeyrotOn`) accounts for exactly that window.

On a full chain the `≤` pin is implied by the monotone rule (`keyMonoOk`) —
an earlier same-producer block carries the floor's index and monotonicity
lifts it to the current block. It is enforced separately because it is the
**locally checkable** form: a certificate/suffix verifier that never sees the
announcement block can still check a suffix block's index against a carried
floor snapshot, where scanning for monotonicity would need the full history. -/
def inForcePinned (n Δconf : Nat) (c : Chain) : Bool :=
  c.all (fun b => decide (inForce n Δconf c (producerForSlot n b.slot) b.slot ≤ b.keyIndex))

/-- The **index-pinned validator**: structural validity, the monotone-index rule,
**and** the in-force pin (no rotated-out index). This is the "true" reduction —
the pin is enforced, not assumed (cf. the assumed hypothesis of
`indexed_reduces_to_static`).

This is the *unsigned* (model-level) pin. The signature conjunct `sigsOk` — that
each block actually verifies under `registry (producer, keyIndex)` — lives on the
signed layer (`validSignedChain`) and is woven in at Phase 2/3. The pin + `sigsOk`
give the *validator-side* half (`rotated_key_dead`: an accepted block verifies
under its declared registry entry, which is never a rotated-out version); the
rotated-out key is fully killed only once the Phase-2 *unforgeability* half (the
adversary cannot forge under a non-stolen entry) is added. -/
def validChainK' (n Δconf : Nat) (c : Chain) : Bool :=
  validChainK n c && inForcePinned n Δconf c

-- ===========================================================================
-- (B) The pinned validator is sound for the original model
-- ===========================================================================

/-- **The pinned validator is stronger than `ValidChain`.** Any chain it
accepts satisfies the semantic `ValidChain` the safety proof consumes and is
key-index monotone — so light-client safety and the forged-time bound (theorems
*about accepted chains*) transport to index-pinned chains unchanged. The pin adds
an obligation; it removes none.

**Liveness (proven, with a sharp condition).** Liveness does *not* transport by
this direction — it needs the converse, that the honest producer's next block
passes the *stricter* validator. That converse is proven in
`KeyRotationLiveness.lean` as a two-sided characterization: production succeeds
and the extension is `validChainK'`-accepted **iff** the declared version
clears the producer's chain floor (`liveness_produce_blockK` /
`liveness_produce_signed_blockK`; converse `extension_rejected_below_floor`).
The floor-clearance condition is exactly the index-inflation surface: the
`≤`-pin admits arbitrary upward jumps, so a single rented slot of producer `i`
can legally declare a huge `keyIndex`; once confirmed, every later honest
`i`-block must clear it. Whether the honest producer can still sign at such a
version is an instantiation property (fine for unbounded hash-derived key
trees, fatal for a bounded committed tree) — **safety-irrelevant** (raising the
floor only shrinks the corruption set and rejects more chains), a quantified
liveness condition rather than an open question. -/
theorem validChainK'_sound {n Δconf : Nat} {c : Chain}
    (h : validChainK' n Δconf c = true) :
    ValidChain n c ∧ KeyIndexMonotone n c := by
  rw [validChainK', Bool.and_eq_true] at h
  exact validChainK_sound h.1

/-- The pin itself, in usable form: no block of an accepted chain signs under a
rotated-out index — every declared index is at least the in-force one. -/
theorem validChainK'_pinned {n Δconf : Nat} {c : Chain}
    (h : validChainK' n Δconf c = true) :
    ∀ b ∈ c, inForce n Δconf c (producerForSlot n b.slot) b.slot ≤ b.keyIndex := by
  rw [validChainK', Bool.and_eq_true, inForcePinned, List.all_eq_true] at h
  intro b hb
  have := h.2 b hb
  rwa [decide_eq_true_eq] at this

-- ===========================================================================
-- (A) inForce agreement — the fold-over-filtered-prefix core
-- ===========================================================================

/-! `keyFloor` is `foldl max 0` over a producer-filtered list, so it depends only
on the *set* of key indices present — not on order or multiplicity. These helpers
make that precise, then lift it to `inForce`: two chains that agree on their
**confirmed-prefix membership** carry the same in-force index. The membership
hypothesis is discharged from finality in part (C) below (`deep_block_shared`);
this is the reusable core (its own induction, as the review noted — not a
one-line corollary). -/

private theorem le_foldl_max : ∀ {a : Nat} (L : List Nat), a ≤ L.foldl max a := by
  intro a L
  induction L generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons]; exact le_trans (le_max_left a x) (ih)

private theorem mem_le_foldl_max {a x : Nat} {L : List Nat} (hx : x ∈ L) :
    x ≤ L.foldl max a := by
  induction L generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hxs
    · exact le_trans (le_max_right a x) (le_foldl_max ys)
    · exact ih hxs

private theorem foldl_max_le {M : Nat} {L : List Nat} :
    ∀ {a : Nat}, a ≤ M → (∀ x ∈ L, x ≤ M) → L.foldl max a ≤ M := by
  induction L with
  | nil => intro a ha _; exact ha
  | cons x xs ih =>
    intro a ha hx
    simp only [List.foldl_cons]
    exact ih (max_le ha (hx x (List.mem_cons_self ..)))
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))

private theorem foldl_max_zero_mono {L L' : List Nat} (h : ∀ x ∈ L, x ∈ L') :
    L.foldl max 0 ≤ L'.foldl max 0 :=
  foldl_max_le (Nat.zero_le _) (fun x hx => mem_le_foldl_max (h x hx))

/-- **`keyFloor` depends only on the producer's block-set.** Two chains containing
the same producer-`i` blocks (membership-equal) have the same floor. -/
theorem keyFloor_eq_of_mem_iff {n : Nat} {c c' : Chain} {i : Nat}
    (h : ∀ b : Block, producerForSlot n b.slot = i → (b ∈ c ↔ b ∈ c')) :
    keyFloor n c i = keyFloor n c' i := by
  unfold keyFloor
  refine Nat.le_antisymm (foldl_max_zero_mono ?_) (foldl_max_zero_mono ?_) <;>
    · intro x hx
      rw [List.mem_map] at hx ⊢
      obtain ⟨b, hb, hbx⟩ := hx
      rw [List.mem_filter] at hb
      refine ⟨b, ?_, hbx⟩
      rw [List.mem_filter]
      first
        | exact ⟨(h b (of_decide_eq_true hb.2)).mp hb.1, hb.2⟩
        | exact ⟨(h b (of_decide_eq_true hb.2)).mpr hb.1, hb.2⟩

/-- **In-force agreement from confirmed-prefix agreement.** If two chains agree on
membership of every block in the confirmed zone (`slot + Δconf ≤ s`), their
in-force index at `s` is identical. The hypothesis is discharged from finality
by `confirmed_mem_iff` (part (C) below). -/
theorem inForce_agreement_of_confirmed_eq {n Δconf : Nat} {c c' : Chain} {i s : Nat}
    (hAgree : ∀ b : Block, b.slot + Δconf ≤ s → (b ∈ c ↔ b ∈ c')) :
    inForce n Δconf c i s = inForce n Δconf c' i s := by
  unfold inForce
  apply keyFloor_eq_of_mem_iff
  intro b _hpi
  unfold confirmedPrefix
  rw [List.mem_filter, List.mem_filter]
  constructor
  · rintro ⟨hbc, hs⟩; exact ⟨(hAgree b (of_decide_eq_true hs)).mp hbc, hs⟩
  · rintro ⟨hbc, hs⟩; exact ⟨(hAgree b (of_decide_eq_true hs)).mpr hbc, hs⟩

-- ===========================================================================
-- (C) Phase 1c — discharge the agreement hypothesis from finality
-- ===========================================================================

/-! The membership hypothesis of `inForce_agreement_of_confirmed_eq` is exactly
**finality at the level of membership**: a block buried in the confirmed prefix
of one valid chain is present in every other valid chain of the same execution.
This is a strengthening of `deep_block_agreement` (`Safety.lean`) — that theorem
compares the height-`k` blocks once *both* chains are already known to reach
height `k`; here we also rule out the case where the other chain is too **short**
to reach height `k`. A short chain that nonetheless observed a deep slot would
place an observed block *below* `b`'s height yet at a *larger* slot, which
`StrictSlots` forbids. With this, `inForce` becomes execution-global on the
confirmed zone with no assumed agreement — the property `georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md`
§2.1 needs to make `badKeyrot` a genuine, chain-independent slot predicate. -/

/-- A block addressed at height `k` of `c` is a member of `c`. -/
private theorem mem_of_blockAt {c : Chain} {k : Nat} {b : Block}
    (h : blockAt? c k = some b) : b ∈ c := by
  unfold blockAt? at h
  obtain ⟨hLen, hEq⟩ := List.getElem?_eq_some_iff.mp h
  exact List.mem_iff_getElem.mpr ⟨k, hLen, hEq⟩

/-- `CommonPrefixUpTo` is symmetric. -/
private theorem commonPrefix_symm {c c' : Chain} {h : Nat}
    (hG : CommonPrefixUpTo c c' h) : CommonPrefixUpTo c' c h :=
  fun k hk => (hG k hk).imp fun _ hB => ⟨hB.2, hB.1⟩

/-- **Deep blocks are shared (membership finality).** A block `b` at height `k`
of a valid chain `c` that lies at least `n` slots behind an observed block of
`c` **and** of a second valid chain `c'` (same execution record, shared genesis)
sits at the **same height** `k` of `c'`. -/
theorem deep_block_shared
    {n : Nat} (hn : 1 ≤ n)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hBudget : ByzantineBounded n bad)
    (hHonest : HonestSlotsUnique bad record)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hGenesis : CommonPrefixUpTo c c' 0)
    {k mD mD' : Nat} {b D D' : Block}
    (hb : blockAt? c k = some b)
    (hD : blockAt? c mD = some D) (hD' : blockAt? c' mD' = some D')
    (hDeep : b.slot + n ≤ D.slot) (hDeep' : b.slot + n ≤ D'.slot) :
    blockAt? c' k = some b := by
  cases hck : blockAt? c' k with
  | some B' =>
    by_cases hbB' : b = B'
    · rw [hbB']
    · -- a genuine divergence at height `k`: killed by `no_deep_fork`
      obtain ⟨h, hhk, hLast⟩ :=
        exists_lastCommonHeight hId hRec hRec' hValid.2.2.1 hValid'.2.2.1
          hGenesis hb hck hbB'
      obtain ⟨F, hFc, -⟩ := hLast.1 h le_rfl
      have hFb : F.slot < b.slot := strictSlots_lt hValid.2.1 hFc hb hhk
      exact (no_deep_fork hn hBudget hHonest hValid hValid' hRec hRec'
        hLast hFc hD hD' (by omega) (by omega)).elim
  | none =>
    -- `c'` is too short to reach height `k`; derive a contradiction.
    exfalso
    have hmD'len : mD' < c'.length := by
      have h' := hD'; unfold blockAt? at h'
      obtain ⟨hlen, -⟩ := List.getElem?_eq_some_iff.mp h'
      exact hlen
    have hklen : c'.length ≤ k := by
      have h' := hck; unfold blockAt? at h'
      exact List.getElem?_eq_none_iff.mp h'
    have hmD'k : mD' < k := lt_of_lt_of_le hmD'len hklen
    obtain ⟨Bc, hBc⟩ := exists_blockAt_of_le (Nat.le_of_lt hmD'k) hb
    by_cases hsh : Bc = D'
    · -- `D'` lies at height `mD' < k` of `c` too, so `D'.slot < b.slot` — but
      -- `D'` was a deep witness `b.slot + n ≤ D'.slot`.
      have hlt : D'.slot < b.slot := by
        have := strictSlots_lt hValid.2.1 hBc hb hmD'k
        rwa [hsh] at this
      omega
    · -- `c` and `c'` diverge at height `mD'`: killed by `no_deep_fork`
      obtain ⟨h, hhm, hLast⟩ :=
        exists_lastCommonHeight hId hRec hRec' hValid.2.2.1 hValid'.2.2.1
          hGenesis hBc hD' hsh
      obtain ⟨F, hFc, -⟩ := hLast.1 h le_rfl
      have hFb : F.slot < b.slot :=
        strictSlots_lt hValid.2.1 hFc hb (lt_trans hhm hmD'k)
      exact no_deep_fork hn hBudget hHonest hValid hValid' hRec hRec'
        hLast hFc hD hD' (by omega) (by omega)

/-- **Confirmed-block membership agreement.** If both chains observed a block at
slot `≥ s` (both tips reached the confirmation horizon) and `n ≤ Δconf`, then a
block at least `Δconf` slots back belongs to `c` iff it belongs to `c'`. This is
the hypothesis `inForce_agreement_of_confirmed_eq` assumed; here it is proved. -/
theorem confirmed_mem_iff
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hBudget : ByzantineBounded n bad)
    (hHonest : HonestSlotsUnique bad record)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hGenesis : CommonPrefixUpTo c c' 0)
    {s mD mD' : Nat} {D D' : Block}
    (hD : blockAt? c mD = some D) (hD' : blockAt? c' mD' = some D')
    (hsD : s ≤ D.slot) (hsD' : s ≤ D'.slot) :
    ∀ b : Block, b.slot + Δconf ≤ s → (b ∈ c ↔ b ∈ c') := by
  -- one direction, then symmetrise (the hypotheses are symmetric in c, c')
  have key : ∀ {x x' : Chain} {p p' : Nat} {E E' : Block},
      ValidChain n x → ValidChain n x' →
      ChainInRecord record x → ChainInRecord record x' →
      CommonPrefixUpTo x x' 0 →
      blockAt? x p = some E → blockAt? x' p' = some E' →
      s ≤ E.slot → s ≤ E'.slot →
      ∀ b : Block, b.slot + Δconf ≤ s → b ∈ x → b ∈ x' := by
    intro x x' p p' E E' hVx hVx' hRx hRx' hGen hE hE' hsE hsE' b hbconf hbx
    obtain ⟨kk, hkk⟩ := exists_blockAt_of_mem hbx
    have hbE  : b.slot + n ≤ E.slot  := by omega
    have hbE' : b.slot + n ≤ E'.slot := by omega
    exact mem_of_blockAt
      (deep_block_shared hn hBudget hHonest hId hVx hVx' hRx hRx' hGen
        hkk hE hE' hbE hbE')
  intro b hb
  constructor
  · intro hbc
    exact key hValid hValid' hRec hRec' hGenesis hD hD' hsD hsD' b hb hbc
  · intro hbc'
    exact key hValid' hValid hRec' hRec (commonPrefix_symm hGenesis)
      hD' hD hsD' hsD b hb hbc'

/-- **In-force agreement (full).** Two valid chains of one execution that have
both observed past the confirmation horizon `s` carry the **same in-force index**
for every participant at `s` — with **no agreement hypothesis assumed**, it is
discharged from finality (`deep_block_shared`). With `Δconf ≥ n` the confirmed
prefix is finalized, so the in-force schedule it records is execution-global.
This is the Phase-1 node that lets `georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md` §2.1 define
`badKeyrot` as a genuine, chain-independent `ByzantineSlots` predicate. -/
theorem inForce_agreement
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {bad : ByzantineSlots} {record : SlotRecord}
    (hBudget : ByzantineBounded n bad)
    (hHonest : HonestSlotsUnique bad record)
    (hId : IdInjective record)
    {c c' : Chain}
    (hValid : ValidChain n c) (hValid' : ValidChain n c')
    (hRec : ChainInRecord record c) (hRec' : ChainInRecord record c')
    (hGenesis : CommonPrefixUpTo c c' 0)
    {s mD mD' : Nat} {D D' : Block}
    (hD : blockAt? c mD = some D) (hD' : blockAt? c' mD' = some D')
    (hsD : s ≤ D.slot) (hsD' : s ≤ D'.slot)
    (i : Nat) :
    inForce n Δconf c i s = inForce n Δconf c' i s :=
  inForce_agreement_of_confirmed_eq
    (confirmed_mem_iff hn hΔ hBudget hHonest hId hValid hValid' hRec hRec'
      hGenesis hD hD' hsD hsD')

-- ===========================================================================
-- (D) Phase 1c — the signed layer: a rotated-out key is dead
-- ===========================================================================

/-! The unsigned pin `validChainK'` bounds each block's declared `keyIndex` from
below by the in-force index. On the **signed** layer the signature is additionally
checked against `registry (producer, keyIndex)` (`sigOk`). Composing the two:
every block of an accepted index-pinned signed chain verifies under its
**declared** registry entry, which is **never a rotated-out version** (declared ≥
in-force). A block keyed to a rotated-out version cannot be accepted. This is the
validator-side half of `georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md` §4A; Phase 2 supplies the crypto
half — an adversary holding only stolen keys, none of them at-or-above the
in-force index, cannot produce a verifying signature under any acceptable entry,
by unforgeability. -/

/-- The index-pinned **signed** validator: versioned-registry signatures + the
structural, monotone-index, in-force-pinned chain. -/
def validSignedChainK' {σ sk pk : Type} (n Δconf : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChainK' n Δconf (stripSigs sc)

/-- **A rotated-out key is dead (validator side).** Every block of an accepted
index-pinned signed chain verifies under its **declared** registry entry
`registry (i, keyIndex)`, and its declared index is **at-or-above the in-force
index** — never a rotated-out version. (`sigsOk` gives the verification at the
declared index; the pin `validChainK'_pinned` bounds the declared index from
below by the in-force one.)

Note the in-force index here is read off **this chain's** confirmed prefix
(`inForce n Δconf (stripSigs sc) …`); `inForce_agreement` (Phase 1c) globalizes it
to the execution-wide schedule the Phase-2 EUF-CMA argument is stated against.
That globalization (and discharging its recent-tip hypothesis) is the Phase-2
uniqueness derivation — `rotated_key_dead` itself is deliberately chain-local. -/
theorem rotated_key_dead {σ sk pk : Type} (n Δconf : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk)
    {sc : SignedChain σ}
    (h : validSignedChainK' n Δconf ops registry sc = true)
    {sb : SignedBlock σ} (hmem : sb ∈ sc) :
    ops.verify
        (registry (producerForSlot n sb.block.slot) sb.block.keyIndex)
        sb.block sb.sig = true ∧
    inForce n Δconf (stripSigs sc) (producerForSlot n sb.block.slot) sb.block.slot
      ≤ sb.block.keyIndex := by
  rw [validSignedChainK', Bool.and_eq_true] at h
  obtain ⟨hSig, hPin⟩ := h
  have hsb : sigOk n ops registry sb = true := by
    rw [sigsOk, List.all_eq_true] at hSig
    exact hSig sb hmem
  have hmemBlock : sb.block ∈ stripSigs sc := by
    unfold stripSigs
    exact List.mem_map.mpr ⟨sb, hmem, rfl⟩
  have hpinned := validChainK'_pinned hPin sb.block hmemBlock
  unfold sigOk at hsb
  exact ⟨hsb, hpinned⟩

/-- **A block keyed to a rotated-out version is rejected.** If any block of a
signed chain declares an index **below** the one in force at its slot — a
rotated-out version — the index-pinned signed validator rejects the whole chain,
the "fail the pin" half of the dichotomy (the "fail `sigsOk`" half is Phase 2,
via unforgeability). This is the contrapositive of `validChainK'_pinned` lifted
to the signed validator; it adds no strength over the pin, but states the
rejection sharply for the paper. -/
theorem rotated_index_rejected {σ sk pk : Type} (n Δconf : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk)
    {sc : SignedChain σ} {sb : SignedBlock σ} (hmem : sb ∈ sc)
    (hRot : sb.block.keyIndex
      < inForce n Δconf (stripSigs sc) (producerForSlot n sb.block.slot) sb.block.slot) :
    validSignedChainK' n Δconf ops registry sc = false := by
  cases h : validSignedChainK' n Δconf ops registry sc with
  | false => rfl
  | true =>
    rw [validSignedChainK', Bool.and_eq_true] at h
    have hmemBlock : sb.block ∈ stripSigs sc := by
      unfold stripSigs
      exact List.mem_map.mpr ⟨sb, hmem, rfl⟩
    exact absurd (validChainK'_pinned h.2 sb.block hmemBlock) (Nat.not_le.mpr hRot)

end MoltPetit.Model
