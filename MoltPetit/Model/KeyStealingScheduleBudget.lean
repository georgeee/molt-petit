import MoltPetit.Model.KeyStealingScheduleCert
import MoltPetit.Model.KeyStealingBudget

/-!
# MoltPetit — the scheduled budget, decomposed, and the two operational packages

Two results, closing the schedule variant's assumption story
(`georgeee/mini-consensus-lean: KEY_ROTATION_SOUND.md` §10.1/§10.2):

**1. The scheduled I3** (`induced_byzantine_bounded_sched`): the
chain-independent budget `ByzantineBounded n (badSched …)` that every scheduled
safety theorem consumes is *derived* from a rent budget `R` (slots per
`n`-window) plus a **current-generation theft rate** `T` (exposed producers per
window: producers holding a stolen key of the scheduled-current-or-later
generation while their window slot comes up), with `R + T ≤ ⌊(n-1)/3⌋`. Same
two ingredients as the default-model `induced_byzantine_bounded`: the union
no-double-count bound and the per-window producer↔slot injection. The one
difference is the payoff: the derived budget takes **no chain argument**, so it
is a single global hypothesis — the anchor-removal device at the budget level.

**2. The two packages** (`PackageA` / `PackageB`): each of §10's operational
assumption sets as an explicit Lean structure that *delivers* the hypotheses of
every scheduled main theorem — and hence the anchor-free light-client
conclusions (`packageA_recent_tip_ancestor_agreement`,
`packageA_recent_certified_suffix_agreement`, and the `packageB_*` twins).

* **Package A — fixed scheduled ("shadow") rotation, WITHOUT erasure** (§10.1).
  Fields: the registry EUF-CMA surface over the schedule-pinned validator
  (`SchedCoreUnforgeable` — A1's formal licensing of `schedule` as the in-force
  generation), hash collision resistance on the declared-signed domain, and the
  `R`/`T` rate bounds. **A2 (theft anytime, no erasure) is visible as the
  absence of any erasure field**: `Stolen i j` may hold for arbitrarily many
  retired generations `j` without touching any field — `exposedProducersSched`
  counts only `j ≥ schedule s`, so retired-key leaks are excluded *by the
  predicate*, not by a secrecy assumption. A3 (no premature exposure —
  just-in-time per-generation root delegation) and A0 (cold root) are the
  instantiation-level justifications of `exposedBound`, exactly as `H-IND`
  justifies the default model's `hBudget`: named in prose, not formalized
  premises (the temporal "steal only while live" content is the §10.4 seam).

* **Package B — erasure + lockstep forced rotation** (§10.2). `PackageB
  extends PackageA` with one extra field, `erasure_freeze`: for every
  generation `j`, at most `T` producers ever have their generation-`j` key
  stolen — the **timeless shadow of B2** ("per-generation compromise freezes at
  the live budget": erasure prevents a generation's stolen set from growing
  after retirement, so its eternal census is its while-live census). The field
  is consumed by no proof, and for full-window schedules it is implied by
  `exposedBound` (`erasure_freeze_of_exposedBound`) — see the `PackageB`
  docstring for the full honest accounting of what it does and does not weigh.

* **The A-vs-B trade, as landed.** `PackageB extends PackageA`, so
  `PackageB.toPackageA` records the **assumption-set inclusion** "B assumes A
  plus erasure" (with forced advancement, B's generation is a function of
  position): every `packageB_*` conclusion is literally the `packageA_*`
  theorem applied to `hPB.toPackageA`. Package A is the weaker-or-equal
  assumption set; binding the generation to the slot is what makes the
  erasure field dispensable. The inclusion is documentary rather than a
  nontrivial reduction — for the flagship schedule the field is redundant
  (`erasure_freeze_of_exposedBound`), and §10.2's *distinctive* discharge
  route (no-mixing ⇒ single-generation forks ⇒ per-generation census with no
  cumulative reading) needs the unmodeled B1 no-mixing rule.

**Honest reading of the rates (the same retroactive reading the default model
documents — carried over, not silently dropped).** `Stolen` has no time index,
so `exposedBound` bounds, per **historical** window, the producers whose
then-current-**or-later** generation key *ever* leaks. Early windows therefore
accumulate the thefts of all later generations: `j ≥ schedule s` is
upward-unbounded, reflecting the real capability that a stolen
current-generation key can forge old slots (the pin is a lower bound, and
monotonicity permits a fork to start high). A genesis-only stateless client
needs the rates in this cumulative reading; a deployment unwilling to assert
that keeps a rolling anchor, exactly as the default model prescribes
(`KeyStealingResults.lean`, "operational reading"). What §10.1's "retired-key
secrecy is not required" means formally is narrower, and is **proven**, not
assumed: (i) a theft of generation `j` charges exactly the slots `s` with
`schedule s ≤ j` — for a *monotone* schedule, no window at-or-after the
generation's retirement (the statements constrain `schedule` in no way, so
the per-slot form is the precise one) — and (ii) any accepted chain whose
**tip** declares a generation whose era ended more than `Δ` ago fails the
plain recency check with no budget consulted (`sched_oldkey_fork_stale`,
`KeyStealingScheduleResults.lean`; core form in `KeyStealingScheduleCert`).

**Validator scope note.** The landed pin is schedule-only: §10.1 A1's composed
emergency floor (`max(gen s, inForce)`) and §10.2 B1's no-mixing rule are not
modeled — the packages license the shared §10.0 device, whose validator is the
pin alone. Consequence for the rates: without the composed floor, a stolen
current-generation key stays usable (its producer exposed) until the schedule
itself advances — up to a full generation period rather than `Δconf` slots —
so `T` must be sized to generation-length exposure. A deployment running the
composed (stricter) validator is still covered: its accepted chains pass the
schedule-only validator too, so every theorem here applies to them unchanged.
-/

namespace MoltPetit.Model

open Classical

-- ===========================================================================
-- The scheduled I3: the chain-independent budget, decomposed
-- ===========================================================================

/-- The theft half of `badSched`: the slot's producer holds a stolen key of the
scheduled-current-or-later generation. A pure function of the slot. -/
def theftSched (n : Nat) (schedule : Nat → Nat) (Stolen : Nat → Nat → Prop)
    (s : Nat) : Prop :=
  ∃ j, schedule s ≤ j ∧ Stolen (producerForSlot n s) j

theorem badSched_iff_or {n : Nat} {schedule : Nat → Nat} {rented : ByzantineSlots}
    {Stolen : Nat → Nat → Prop} (s : Nat) :
    badSched n schedule rented Stolen s ↔ rented s ∨ theftSched n schedule Stolen s :=
  Iff.rfl

/-- The **exposed producers** of a window, scheduled form: producers holding a
stolen current-or-later-generation key at their (unique) slot in `[u, u+n)`.
Unlike the default `exposedProducers`, this reads no chain — the generation
floor is `schedule s`, a function of the slot. -/
noncomputable def exposedProducersSched (n : Nat) (schedule : Nat → Nat)
    (Stolen : Nat → Nat → Prop) (u : Nat) : Finset Nat :=
  (Finset.Ico u (u + n)).filter (fun s => theftSched n schedule Stolen s) |>.image
    (producerForSlot n)

/-- Two slots of one `n`-window with the same producer are the same slot —
the producer↔slot correspondence is injective per window. (Local copy of the
`KeyStealingBudget` lemma, which is private there.) -/
private theorem window_producer_inj {n u : Nat} {s s' : Nat}
    (hs : s ∈ Finset.Ico u (u + n)) (hs' : s' ∈ Finset.Ico u (u + n))
    (h : producerForSlot n s = producerForSlot n s') : s = s' := by
  rw [Finset.mem_Ico] at hs hs'
  unfold producerForSlot at h
  have h1 := Nat.div_add_mod s n
  have h2 := Nat.div_add_mod s' n
  rcases Nat.lt_trichotomy (s / n) (s' / n) with hlt | heq | hgt
  · exfalso
    have hmul : n * (s / n) + n ≤ n * (s' / n) :=
      calc n * (s / n) + n = n * (s / n + 1) := by ring
        _ ≤ n * (s' / n) := Nat.mul_le_mul (Nat.le_refl n) (Nat.succ_le_of_lt hlt)
    omega
  · rw [heq] at h1
    omega
  · exfalso
    have hmul : n * (s' / n) + n ≤ n * (s / n) :=
      calc n * (s' / n) + n = n * (s' / n + 1) := by ring
        _ ≤ n * (s / n) := Nat.mul_le_mul (Nat.le_refl n) (Nat.succ_le_of_lt hgt)
    omega

/-- **The producer↔slot bijection, scheduled form**: theft-corrupt slots per
window are bounded by the exposed producers per window. -/
theorem theftSlotsSched_card_le_exposed (n : Nat) (schedule : Nat → Nat)
    (Stolen : Nat → Nat → Prop) (u : Nat) :
    (badSlotsIn (theftSched n schedule Stolen) u n).card ≤
      (exposedProducersSched n schedule Stolen u).card := by
  unfold badSlotsIn exposedProducersSched
  refine Finset.card_le_card_of_injOn (producerForSlot n) (fun s hs => ?_) ?_
  · exact Finset.mem_image_of_mem _ hs
  · intro s hs s' hs' h
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hs hs'
    exact window_producer_inj hs.1 hs'.1 h

/-- **The scheduled induced budget, decomposed** (the scheduled I3). A rent
budget of `R` slots per window and a current-generation theft rate of `T`
exposed producers per window, with `R + T` within the `1/3` bound, give the
**chain-independent** `ByzantineBounded` over `badSched` that every scheduled
safety theorem consumes — one global hypothesis, no chain to key it to. -/
theorem induced_byzantine_bounded_sched {n : Nat} {schedule : Nat → Nat}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop} {R T : Nat}
    (hRent : ∀ u, (badSlotsIn rented u n).card ≤ R)
    (hExposed : ∀ u, (exposedProducersSched n schedule Stolen u).card ≤ T)
    (hRT : R + T ≤ maxByzantine n) :
    ByzantineBounded n (badSched n schedule rented Stolen) := by
  intro u
  have hsplit := badSlotsIn_union_le rented (theftSched n schedule Stolen) u n
  have htheft := theftSlotsSched_card_le_exposed n schedule Stolen u
  have : (badSlotsIn (badSched n schedule rented Stolen) u n).card =
      (badSlotsIn (fun s => rented s ∨ theftSched n schedule Stolen s) u n).card := rfl
  rw [this]
  calc (badSlotsIn (fun s => rented s ∨ theftSched n schedule Stolen s) u n).card
      ≤ (badSlotsIn rented u n).card
          + (badSlotsIn (theftSched n schedule Stolen) u n).card := hsplit
    _ ≤ R + T := Nat.add_le_add (hRent u) (le_trans htheft (hExposed u))
    _ ≤ maxByzantine n := hRT

-- ===========================================================================
-- Package A — fixed scheduled ("shadow") rotation, WITHOUT erasure (§10.1)
-- ===========================================================================

/-- **Package A** (§10.1): the assumption set of *fixed scheduled rotation
without erasure*, as one structure. Its fields deliver every hypothesis of the
scheduled main theorems beyond the structural ones:

* `unforgeable` — the registry EUF-CMA surface over the schedule-pinned
  validator (core scope; delivers the full-validator surface via
  `schedUnforgeable_of_core`). This is A1's formal licensing: the public
  schedule *is* the in-force generation, enforced by the pin.
* `hashInj` — collision resistance on the declared-signed domain.
* `rentBound` / `exposedBound` / `budget_le` — the operational rates: `R`
  rented slots and `T` exposed producers per window, `R + T ≤ ⌊(n-1)/3⌋`.

**No erasure field** — that is A2: retired-key leaks are harmless by the
`j ≥ schedule s` floor in the exposure predicate, not assumed away. A3
(just-in-time provisioning: no theft of not-yet-live generations) and A0 (cold
root) are the instantiation-level justifications of `exposedBound` — named
here, formalized nowhere (the §10.4 temporal seam, same as the default
model's `H-IND`). -/
structure PackageA (n : Nat) (schedule : Nat → Nat) {Sig sk pk : Type}
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (rented : ByzantineSlots)
    (Stolen : Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block)
    (now Δ : Nat) (G : Block) (R T : Nat) : Prop where
  unforgeable :
    SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ
  hashInj : SignedHashInjective (SignedDeclared n ops registry) G
  rentBound : ∀ u, (badSlotsIn rented u n).card ≤ R
  exposedBound : ∀ u, (exposedProducersSched n schedule Stolen u).card ≤ T
  budget_le : R + T ≤ maxByzantine n

/-- Package A delivers the chain-independent budget. -/
theorem packageA_byzantine_bounded {n : Nat} {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hA : PackageA n schedule ops registry rented Stolen honestSigned now Δ G R T) :
    ByzantineBounded n (badSched n schedule rented Stolen) :=
  induced_byzantine_bounded_sched hA.rentBound hA.exposedBound hA.budget_le

/-- **Package A ⊢ anchor-free light-client safety (tip-ancestor form).** Under
Package A alone, two scheduled-validated chains sharing genesis with recent
equal-height tips agree on the `n`-confirmed ancestor — no anchor, no `Δconf`,
no chain-keyed budget. This is the §10.1 discharge as one implication. -/
theorem packageA_recent_tip_ancestor_agreement
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hA : PackageA n schedule ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
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
    B = B' :=
  sched_recent_tip_ancestor_agreement hn (schedUnforgeable_of_core hA.unforgeable)
    hA.hashInj (packageA_byzantine_bounded hA) hVal hVal' hHead hHead'
    hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'

/-- **Package A ⊢ anchor-free light-client safety (certificate form).** Under
Package A alone, two verifying scheduled certificates (no floor snapshot)
grounded in the same genesis, each extended by a validated recent suffix,
agree on every block `n`-deep in both suffixes. -/
theorem packageA_recent_certified_suffix_agreement
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hA : PackageA n schedule ops registry rented Stolen honestSigned now Δ G R T)
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
    B = B' :=
  sched_recent_certified_suffix_agreement hn hA.unforgeable hA.hashInj
    (packageA_byzantine_bounded hA) hcl hcl' hTipS hTipS' hLink hLinks hDense
    hPinS hSigned hLink' hLinks' hDense' hPinS' hSigned' hRecent hRecent'
    hB hB' hHeight hDeep hDeep'

-- ===========================================================================
-- Package B — erasure + lockstep forced rotation (§10.2)
-- ===========================================================================

/-- **Package B** (§10.2): erasure + lockstep forced rotation. With forced
advancement (B1), the roster-wide generation is a function of position — so B
licenses the *same* device as A, and formally **B assumes A plus one field**:

* `erasure_freeze` — the timeless shadow of B2 (honest erasure): for every
  generation `j`, at most `T` producers ever have their generation-`j` key
  stolen. Erasure is what freezes a generation's stolen census at its
  while-live value (the live-`1/3` budget); without it the census could keep
  growing after retirement.

**Honest weight of the field (review-driven).** `erasure_freeze` is consumed
by no proof — and for schedules in which every generation contains a full
`n`-window (the flagship `s / R` with `R ≥ n`) it is **implied** by
`exposedBound` (proven: `erasure_freeze_of_exposedBound`), so there `PackageB`
is logically `PackageA`. `PackageB.toPackageA` therefore records an
**assumption-set inclusion** (B assumes at least A) — documentary, not a
nontrivial reduction; its value is stating B's mechanism. The genuinely-B
discharge of §10.2 — no-mixing forces any fork to a single generation, so a
per-generation census suffices *without* the cumulative reading — is a
different proof shape requiring the unmodeled B1 no-mixing rule (validator
scope note). Nor would a timed model derive the current `exposedBound` from
`erasure_freeze`: even in a faithful-B world (thefts only while live), letting
*different* producers lose keys in *different* generations satisfies
`erasure_freeze` yet falsifies the cumulative `exposedBound` at genesis-era
windows; a timed model would instead replace the budget's *shape* by a
horizon-scoped one — the §10.4 seam. Both packages, like the default model,
assume the budget in its cumulative reading. B3/B0 are as A3/A0: prose-level
instantiation justifications. -/
structure PackageB (n : Nat) (schedule : Nat → Nat) {Sig sk pk : Type}
    (ops : SigOps Sig sk pk) (registry : KeyRegistry pk) (rented : ByzantineSlots)
    (Stolen : Nat → Nat → Prop) (honestSigned : Nat → Nat → Option Block)
    (now Δ : Nat) (G : Block) (R T : Nat)
    extends PackageA n schedule ops registry rented Stolen honestSigned now Δ G R T :
    Prop where
  erasure_freeze : ∀ j : Nat, ((Finset.range n).filter (fun i => Stolen i j)).card ≤ T

/-- The flagship schedule `fun s => s / R` satisfies the full-window premise
of `erasure_freeze_of_exposedBound` whenever `R ≥ n`: generation `j`'s era
starts at `j * R` and contains the `n` consecutive slots `[j * R, j * R + n)`.
(For `R < n` the premise genuinely fails — a generation has fewer than `n`
slots, so some producer never produces in it.) -/
theorem schedule_div_full_window {n R : Nat} (hR : n ≤ R) (hR0 : 0 < R) :
    ∀ j : Nat, ∃ u, ∀ s, u ≤ s → s < u + n → s / R = j := by
  intro j
  refine ⟨j * R, fun s hsl hsu => ?_⟩
  have h2 : s < (j + 1) * R := by
    have : (j + 1) * R = j * R + R := by ring
    omega
  have hle : j ≤ s / R := (Nat.le_div_iff_mul_le hR0).mpr hsl
  have hlt : s / R < j + 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h2)
  omega

/-- **`erasure_freeze` carries no independent formal weight for full-window
schedules.** Under any schedule in which every generation contains a full
`n`-window of slots (true of the flagship `fun s => s / R` whenever `R ≥ n` —
`schedule_div_full_window`), the per-generation frozen census is already
implied by the exposure rate: every producer owns a slot in generation `j`'s
full window, and a stolen generation-`j` key exposes it there
(`j ≥ schedule s = j`). So for such schedules `PackageB` is logically
`PackageA`, and the `extends` relation records an assumption-set inclusion,
not a nontrivial reduction (see the `PackageB` docstring). -/
theorem erasure_freeze_of_exposedBound {n : Nat} {schedule : Nat → Nat}
    {Stolen : Nat → Nat → Prop} {T : Nat}
    (hExposed : ∀ u, (exposedProducersSched n schedule Stolen u).card ≤ T)
    (hFull : ∀ j : Nat, ∃ u, ∀ s, u ≤ s → s < u + n → schedule s = j) :
    ∀ j : Nat, ((Finset.range n).filter (fun i => Stolen i j)).card ≤ T := by
  intro j
  obtain ⟨u, hu⟩ := hFull j
  refine le_trans (Finset.card_le_card ?_) (hExposed u)
  intro i hi
  rw [Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨hin, hSt⟩ := hi
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hin
  -- the full window contains producer i's slot: some s ∈ [u, u+n) with s % n = i
  obtain ⟨s, hsl, hsu, hmod⟩ : ∃ s, u ≤ s ∧ s < u + n ∧ s % n = i := by
    have hdm := Nat.div_add_mod u n
    have hum : u % n < n := Nat.mod_lt _ hn
    by_cases hcase : u % n ≤ i
    · refine ⟨n * (u / n) + i, by omega, by omega, ?_⟩
      rw [Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hin
    · have hexp : n * (u / n + 1) = n * (u / n) + n := Nat.mul_succ n (u / n)
      refine ⟨n * (u / n + 1) + i, by omega, by omega, ?_⟩
      rw [Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hin
  unfold exposedProducersSched
  refine Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ⟨hsl, hsu⟩, ?_⟩, ?_⟩
  · exact ⟨j, le_of_eq (hu s hsl hsu), by unfold producerForSlot; rw [hmod]; exact hSt⟩
  · unfold producerForSlot
    exact hmod

/-- Package B delivers the chain-independent budget (via its Package-A core). -/
theorem packageB_byzantine_bounded {n : Nat} {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hPB : PackageB n schedule ops registry rented Stolen honestSigned now Δ G R T) :
    ByzantineBounded n (badSched n schedule rented Stolen) :=
  packageA_byzantine_bounded hPB.toPackageA

/-- **Package B ⊢ anchor-free light-client safety (tip-ancestor form)** —
literally Package A's theorem through the `toPackageA` reduction. -/
theorem packageB_recent_tip_ancestor_agreement
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hPB : PackageB n schedule ops registry rented Stolen honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
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
    B = B' :=
  packageA_recent_tip_ancestor_agreement hn hPB.toPackageA hVal hVal' hHead hHead'
    hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'

/-- **Package B ⊢ anchor-free light-client safety (certificate form)** —
Package A's theorem through the `toPackageA` reduction. -/
theorem packageB_recent_certified_suffix_agreement
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : Nat → Nat → Option Block} {now Δ : Nat} {G : Block} {R T : Nat}
    (hPB : PackageB n schedule ops registry rented Stolen honestSigned now Δ G R T)
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
    B = B' :=
  packageA_recent_certified_suffix_agreement hn hPB.toPackageA hcl hcl'
    hTipS hTipS' hLink hLinks hDense hPinS hSigned hLink' hLinks' hDense'
    hPinS' hSigned' hRecent hRecent' hB hB' hHeight hDeep hDeep'

end MoltPetit.Model
