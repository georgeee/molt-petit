import MoltPetit.Model.KeyRotation

/-!
# MoltPetit — the key-stealing adversary (Phase 2, increment I1)

The strong adversary of `georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md` (v3): a stolen delegate key
`dk(i,j)` signs **anything, at any slot, forever** — no forward security. This
module lays the foundation (see `georgeee/mini-consensus-lean: PHASE2_DESIGN.md`, increment I1):

* `badKeyrotOn` — the induced corruption as a **chain-independent slot predicate**,
  keyed on the in-force index read off a **fixed** witness chain `c₀`'s finalized
  prefix: `rented s ∨ ∃ j ≥ inForce c₀ i s, Stolen i j` (any stolen
  not-yet-rotated-out key corrupts the slot; a stolen rotated-out key never does).
* `timedExecution_of_bad_iff` — `TimedExecution` transports across a pointwise-iff
  swap of its `bad` predicate (the structure mentions `bad` only negatively).
* `KeyStealingExecution` — the timed core over the enriched `badKeyrotOn`, **plus**
  the bridge that a stolen-key block consumes a bad real slot. The signed registry
  lives on the `SignedChain` side; the timed (bare-`Block`) layer sees only the
  abstract `StolenMint : Block → Prop` predicate, exactly as `TimedSig` bridges the
  timed and signed worlds through an abstract `Signed`.
* `keyStealing_refines_timed` — with no *in-force* key stolen the model refines to
  the plain `TimedExecution n rented`, witnessing the strict-superset claim (instr.
  1). A stolen rotated-out key is harmless (`H-IND`), so it need not be excluded.
-/

namespace MoltPetit.Model

-- ===========================================================================
-- The induced corruption predicate
-- ===========================================================================

/-- The **key-stealing corruption** as seen through a fixed witness chain `c₀`:
slot `s` is bad if its producer is rented, or if **any not-yet-rotated-out key**
of the producer — any version at-or-above the index **in force** at `s` (read
off `c₀`'s confirmed prefix) — is stolen. Chain-independent on the confirmed
zone by `inForce_agreement`, so a genuine `ByzantineSlots` predicate.

This is the predicate that expresses the **healing** story: stealing the
producer's current key makes its slots bad, but only until the emergency
rotation (a block declaring a higher index) becomes `Δconf`-deep — from then on
the stolen version sits *below* the in-force index and no longer satisfies
`inForce ≤ j`, so the slots heal. A stolen **rotated-out** key never counts.
The `∃ j ≥ inForce` form (rather than `Stolen _ inForce` alone) is forced by
the `≤`-pin: an accepted block may sign under any not-yet-rotated-out version
(that is what makes announcing a rotation possible at all), so a slot is only
honest if *none* of those versions is compromised. -/
def badKeyrotOn (n Δconf : Nat) (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop)
    (c₀ : Chain) (s : Nat) : Prop :=
  rented s ∨ ∃ j, inForce n Δconf c₀ (producerForSlot n s) s ≤ j ∧
    Stolen (producerForSlot n s) j

/-- **The loss-only adversary: with nothing stolen, the corruption predicate is
just rent — and is chain-independent.**

Key *loss* is not key *theft*: losing a delegate key gives the adversary no
signing power, and the loser simply rotates, which the validator already
supports. So the loss-only adversary is this model at `Stolen := fun _ _ =>
False`, and no new development is needed for it.

The payoff is the `c₀` argument disappearing. `badKeyrotOn` reads the in-force
index off a witness chain, which is exactly why a from-genesis fork (whose
floor never advances) is judged by a *different* predicate than the real chain
— the gap that `H-ANCHOR` exists to close. With no theft the existential is
vacuous, the predicate collapses to `rented`, and that asymmetry has nothing
to attach to: prophylactic and loss-driven rotation need no anchor, no
key-leak horizon, and no update mechanism. -/
theorem badKeyrotOn_lossOnly (n Δconf : Nat) (rented : ByzantineSlots) (c₀ : Chain) :
    badKeyrotOn n Δconf rented (fun _ _ => False) c₀ = rented := by
  funext s
  simp [badKeyrotOn]

-- ===========================================================================
-- TimedExecution transports across a pointwise-iff bad swap
-- ===========================================================================

/-- `TimedExecution` depends on `bad` only through the negated guards of
`honest_stamp`/`honest_once`, so it transports across any pointwise-equivalent
`bad`. -/
theorem timedExecution_of_bad_iff {n : Nat} {bad bad' : ByzantineSlots}
    {log : TimedLog} {G : Block}
    (hiff : ∀ s, bad s ↔ bad' s)
    (h : TimedExecution n bad log G) :
    TimedExecution n bad' log G := by
  refine ⟨h.key_match, ?_, ?_, h.chain_order, h.id_inj⟩
  · intro r hr B hB
    exact h.honest_stamp (fun hb => hr ((hiff r).mp hb)) hB
  · intro r hr B B' hB hB'
    exact h.honest_once (fun hb => hr ((hiff r).mp hb)) hB hB'

-- ===========================================================================
-- The key-stealing execution
-- ===========================================================================

/-- The **key-stealing execution**. The unsigned timed core holds over the enriched
`badKeyrotOn` corruption, and every stolen-key block consumes a bad real slot
(`steal_bad`). `StolenMint : Block → Prop` is the unsigned image of "verifies under
a stolen registry version"; the actual `ops`/`registry`/`sig` content lives on the
`SignedChain` side (where `VersionedUnforgeable` is stated) and is connected to this
predicate by a separate bridge hypothesis in Phase 3 — keeping the timed and signed
encodings disjoint but bridged (cf. `TimedSig`). -/
structure KeyStealingExecution (n Δconf : Nat)
    (rented : ByzantineSlots) (Stolen : Nat → Nat → Prop) (StolenMint : Block → Prop)
    (c₀ : Chain) (log : TimedLog) (G : Block) : Prop where
  /-- The timed core, over the enriched key-stealing corruption. -/
  toTimed : TimedExecution n (badKeyrotOn n Δconf rented Stolen c₀) log G
  /-- A stolen-key block is logged only at a bad real slot (the theft consumes one). -/
  steal_bad : ∀ ⦃r : Nat⦄ ⦃B : Block⦄, B ∈ log r → StolenMint B →
    badKeyrotOn n Δconf rented Stolen c₀ r

/-- **The key-stealing adversary is a strict superset of the slot-based one.** When
no **not-yet-rotated-out** key is stolen, the corruption is exactly `rented` and the
model refines to the plain `TimedExecution n rented`. Witnesses instruction 1 (keep
"rent a slot", add key theft). The hypothesis is the at-or-above-in-force pointwise
form, not "no key ever stolen": a stolen *rotated-out* key (`Stolen i j` with
`j < inForce c₀ i s`) does **not** inflate the corruption — the rotated-out key is
harmless. So `Stolen = ∅` is the special case `hNoStealLive := fun _ _ _ => …`. -/
theorem keyStealing_refines_timed {n Δconf : Nat}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop} {StolenMint : Block → Prop}
    {c₀ : Chain} {log : TimedLog} {G : Block}
    (hNoStealLive :
      ∀ s j, inForce n Δconf c₀ (producerForSlot n s) s ≤ j →
        ¬ Stolen (producerForSlot n s) j)
    (h : KeyStealingExecution n Δconf rented Stolen StolenMint c₀ log G) :
    TimedExecution n rented log G := by
  refine timedExecution_of_bad_iff ?_ h.toTimed
  intro s
  unfold badKeyrotOn
  constructor
  · rintro (hr | ⟨j, hj, hst⟩)
    · exact hr
    · exact absurd hst (hNoStealLive s j hj)
  · exact Or.inl

end MoltPetit.Model
