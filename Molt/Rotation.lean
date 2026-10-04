import Molt.Results
import MoltPetit.Results.KeyStealingResults
import MoltPetit.Results.KeyStealingScheduleResults
import MoltPetit.Model.KeyStealingHorizon
import MoltPetit.Model.KeyStealingLockstep
import MoltPetit.Model.KeyStealingCert
import MoltPetit.Model.KeyStealingScheduleCert
import MoltPetit.Model.KeyStealingScheduleTimed
import MoltPetit.Model.KeyRotationLoss
import MoltPetit.Model.KeyRotationLossSchedLock
import MoltPetit.Model.KeyStealingScheduleCertHorizon
import MoltPetit.Model.SchedExposure

/-!
# Key rotation (paper §6.3)

The three rotation modes' validators, the key-stealing corruption
predicate, and the mode-1 client rule — including the paper's new
formulation of the refresh horizon:

* `client_refresh_rule` (mode 1): a client whose anchor is younger than
  the horizon `H` needs the corruption budget only on the trailing
  `≈ H + n` slots of history. Wrapper over
  `MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored` with the
  anchor's *age* made explicit.
* `scheduled_client_safety` (mode 2) and `lockstep_client_safety`
  (mode 3): anchor-free safety, transported.
-/

namespace Molt

/-! ## The in-band key index (all modes) -/

/-- The in-band **monotone rule**: scanning from genesis, no earlier block
of a producer carries a higher key version than a later block of the same
producer — a rotation only ever moves forward, ordered by consensus like
any other block. -/
def keyMonoOk (n : Nat) : Chain → Bool
  | [] => true
  | b :: rest =>
      rest.all (fun b' =>
        decide (producer n b.slot = producer n b'.slot →
          b.keyIndex ≤ b'.keyIndex))
      && keyMonoOk n rest

/-- The indexed validator: structural validity plus the monotone rule.
This — with signatures and a per-mode pin — is the one protocol of the
paper; there is no rotation-free variant. -/
def validChainK (n : Nat) (c : Chain) : Bool :=
  validChain n c && keyMonoOk n c

/-- Every chain the protocol accepts passes the structural validator, so
the static-key safety results (paper §6.1–6.2) hold for the full
protocol a fortiori. -/
theorem validChainK_structural {n : Nat} {c : Chain}
    (h : validChainK n c = true) : validChain n c = true := by
  rw [validChainK, Bool.and_eq_true] at h
  exact h.1

/-- Seat `i`'s **floor**: the highest key version it has used anywhere in
the chain — the in-band counter. -/
def keyFloor (n : Nat) (c : Chain) (i : Nat) : Nat :=
  ((c.filter (fun b => decide (producer n b.slot = i))).map
    MoltPetit.Model.Block.keyIndex).foldl max 0

/-! ## Mode 1: reactive (in-band) rotation -/

/-- The **confirmed prefix** of `c` seen from slot `s`: blocks at least
`Δconf` slots in the past. With `n ≤ Δconf` these are finalized, so all
valid chains of one execution agree on them. -/
def confirmedPrefix (Δconf : Nat) (c : Chain) (s : Nat) : Chain :=
  c.filter (fun b => decide (b.slot + Δconf ≤ s))

/-- The version **in force** for seat `i` at slot `s`: its floor over the
confirmed prefix. A rotation takes force exactly when its announcing block
is `Δconf` deep. -/
def inForce (n Δconf : Nat) (c : Chain) (i s : Nat) : Nat :=
  keyFloor n (confirmedPrefix Δconf c s) i

/-- The **pin**: no block declares a version below the one in force at its
slot — i.e. no block signs under a rotated-out key. `≤`, not `=`: a
producer announces a rotation by signing under a *higher* version; once
the announcement is `Δconf` deep the floor rises and the old version is
dead. -/
def inForcePinned (n Δconf : Nat) (c : Chain) : Bool :=
  c.all (fun b =>
    decide (inForce n Δconf c (producer n b.slot) b.slot ≤ b.keyIndex))

/-- Mode 1's full unsigned validator: indexed validity plus the pin. -/
def validChainK' (n Δconf : Nat) (c : Chain) : Bool :=
  validChainK n c && inForcePinned n Δconf c

/-- Mode 1's signed validator. -/
def validSignedChainK' {σ sk pk : Type} (n Δconf : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk)
    (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChainK' n Δconf (stripSigs sc)

/-- The key-stealing corruption predicate, and the **healing** story in
one definition: slot `s` is bad if it is rented, or if *some* version at
or above the one in force for its producer is stolen. A stolen current key
makes its producer's slots bad only until the emergency rotation is
`Δconf` deep — then the stolen version drops below the floor and the slots
heal. A stolen rotated-out key never counts. -/
def badKeyrot (n Δconf : Nat) (rented : ByzantineSlots)
    (Stolen : Nat → Nat → Prop) (c₀ : Chain) (s : Nat) : Prop :=
  rented s ∨ ∃ j, inForce n Δconf c₀ (producer n s) s ≤ j ∧
    Stolen (producer n s) j

/-- The key-stealing unforgeability surface (mode 1): stolen keys of any
version sign anything forever; only non-stolen, non-rented entries pin
honest slots. -/
abbrev KeyStealingEUFCMA := @MoltPetit.Model.KeyStealingEUFCMA

/-- The genesis-or-carries-a-verifying-signature domain of hash
injectivity, mode-1 form. -/
abbrev KeyStealingSigned := @MoltPetit.Model.KeyStealingSigned

/-! ## Mode 2: scheduled rotation -/

/-- Mode 2's pin: no block declares a version below its slot's scheduled
one, `gen(slot) ≤ keyIndex`. The schedule is a pure function of the slot —
identical on every chain, pinned at the verifier, never peer-supplied. -/
def schedPin (schedule : Nat → Nat) (c : Chain) : Bool :=
  c.all (fun b => decide (schedule b.slot ≤ b.keyIndex))

/-- Mode 2's signed validator: signatures + indexed validity + the
scheduled pin. No confirmation depth, no floor. -/
def validSignedChainSched {σ sk pk : Type} (n : Nat) (schedule : Nat → Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk)
    (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChainK n (stripSigs sc)
    && schedPin schedule (stripSigs sc)

/-- Mode 2's unforgeability surface. -/
abbrev SchedUnforgeable := @MoltPetit.Model.SchedUnforgeable

/-- Mode 2's chain-independent corruption predicate. -/
abbrev badSched := @MoltPetit.Model.badSched

/-- Hash-injectivity domain, scheduled form. -/
abbrev SignedDeclared := @MoltPetit.Model.SignedDeclared

/-! ## Mode 3: free-cadence lockstep -/

/-- Mode 3's **no-mixing rule**: the declared version is constant within
each `n`-slot window and non-decreasing across windows. Roster-wide —
unlike `keyMonoOk` it compares all pairs, not only same-producer pairs. -/
def noMixing (n : Nat) : Chain → Bool
  | [] => true
  | b :: rest =>
      rest.all (fun b' =>
        decide ((b.slot / n = b'.slot / n → b.keyIndex = b'.keyIndex) ∧
          b.keyIndex ≤ b'.keyIndex))
      && noMixing n rest

/-- Mode 3's signed validator: signatures + indexed validity + no-mixing.
No schedule parameter anywhere — the verifier never learns when the roster
advanced. -/
def validSignedChainLock {σ sk pk : Type} (n : Nat)
    (ops : SigOps σ sk pk) (registry : KeyRegistry pk)
    (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChainK n (stripSigs sc)
    && noMixing n (stripSigs sc)

/-- Mode 3's hypothesis package: the roster counter (behavioural, monotone,
declared by honest signatures), the unforgeability surface, and the
budget. -/
abbrev LockstepPackage := @MoltPetit.Model.LockstepPackage

/-! ## Bridge to the core development -/

theorem keyMonoOk_eq_core : keyMonoOk = MoltPetit.Model.keyMonoOk := by
  funext n c
  induction c with
  | nil => rfl
  | cons b rest ih =>
    simp only [keyMonoOk, MoltPetit.Model.keyMonoOk, producer_eq_core, ih]
    rfl

theorem keyFloor_eq_core : keyFloor = MoltPetit.Model.keyFloor := rfl
theorem confirmedPrefix_eq_core :
    confirmedPrefix = MoltPetit.Model.confirmedPrefix := rfl
theorem inForce_eq_core : inForce = MoltPetit.Model.inForce := rfl
theorem inForcePinned_eq_core :
    inForcePinned = MoltPetit.Model.inForcePinned := rfl
theorem badKeyrot_eq_core : badKeyrot = MoltPetit.Model.badKeyrotOn := rfl
theorem schedPin_eq_core : schedPin = MoltPetit.Model.schedPinned := rfl

theorem validChainK_eq_core : validChainK = MoltPetit.Model.validChainK := by
  funext n c
  simp only [validChainK, MoltPetit.Model.validChainK, validChain_eq_core,
    keyMonoOk_eq_core]

theorem validChainK'_eq_core :
    validChainK' = MoltPetit.Model.validChainK' := by
  funext n Δconf c
  simp only [validChainK', MoltPetit.Model.validChainK', validChainK_eq_core,
    inForcePinned_eq_core]

theorem validSignedChainK'_eq_core {σ sk pk : Type} :
    (validSignedChainK' (σ := σ) (sk := sk) (pk := pk))
      = MoltPetit.Model.validSignedChainK' := by
  funext n Δconf ops registry sc
  simp only [validSignedChainK', MoltPetit.Model.validSignedChainK',
    sigsOk_eq_core, validChainK'_eq_core, stripSigs_eq_core]

theorem validSignedChainSched_eq_core {σ sk pk : Type} :
    (validSignedChainSched (σ := σ) (sk := sk) (pk := pk))
      = MoltPetit.Model.validSignedChainSched := by
  funext n schedule ops registry sc
  simp only [validSignedChainSched, MoltPetit.Model.validSignedChainSched,
    sigsOk_eq_core, validChainK_eq_core, schedPin_eq_core, stripSigs_eq_core]

theorem noMixing_eq_core : noMixing = MoltPetit.Model.lockstepOk := by
  funext n c
  induction c with
  | nil => rfl
  | cons b rest ih =>
    simp only [noMixing, MoltPetit.Model.lockstepOk, ih]

theorem validSignedChainLock_eq_core {σ sk pk : Type} :
    (validSignedChainLock (σ := σ) (sk := sk) (pk := pk))
      = MoltPetit.Model.validSignedChainLock := by
  funext n ops registry sc
  simp only [validSignedChainLock, MoltPetit.Model.validSignedChainLock,
    sigsOk_eq_core, validChainK_eq_core, noMixing_eq_core, stripSigs_eq_core]

/-! ## Mode 1: loss is not theft -/

/-- **Loss-only collapse.** With nothing stolen (`Stolen := ⊥`), the
corruption predicate is rent alone: key *loss* gives the adversary no
signing power, the loser rotates, and no anchor, horizon, or refresh rule
is needed at all. -/
theorem badKeyrot_lossOnly (n Δconf : Nat) (rented : ByzantineSlots)
    (c₀ : Chain) :
    badKeyrot n Δconf rented (fun _ _ => False) c₀ = rented :=
  MoltPetit.Model.badKeyrotOn_lossOnly n Δconf rented c₀

/-- Mode 2's census collapses the same way with nothing stolen — and
mode 3 consumes mode 2's census, so the collapse covers all three pins:
this is the paper's **mode 0** (loss without theft), where every mode
gives the same guarantees to a genesis-and-clock client. -/
theorem badSched_lossOnly (n : Nat) (schedule : Nat → Nat)
    (rented : ByzantineSlots) :
    badSched n schedule rented (fun _ _ => False) = rented := by
  funext s
  simp [MoltPetit.Model.badSched]

/-- Mode 3's exposure census is empty with nothing stolen: the third
loss-only anchor, completing mode 0's "every mode" claim name-for-name
(mode 3's package consumes this census at the lagged counter). -/
theorem exposedSched_lossOnly (n : Nat) (schedule : Nat → Nat) (u : Nat) :
    MoltPetit.Model.exposedProducersSched n schedule
      (fun _ _ => False) u = ∅ := by
  unfold MoltPetit.Model.exposedProducersSched
  simp [MoltPetit.Model.theftSched]

/-! ## Mode 1: the client refresh rule -/

/-- **The client refresh rule** (paper Theorem 3). Pick a horizon `H` —
a deployment choice. A light client that refreshes at least every `H`
slots (its anchor block `A` satisfies `now ≤ A.slot + H`, and it accepts
only chains containing `A`) is safe with the corruption budget consulted
**only on windows overlapping the trailing `H + n` slots**: for all older
history nothing is assumed — no budget, no key secrecy, nothing.

Wrapper over `keyrot_recent_tip_ancestor_agreement_anchored` with the
anchor's age made explicit: `now < u + n + H` follows from
`now ≤ A.slot + H` and the core's guard `A.slot + 1 ≤ u + n`, so the
H-guarded budget covers every window the anchored core consults. -/
theorem client_refresh_rule
    {n Δconf : Nat} (hn : 1 ≤ n) (hΔ : n ≤ Δconf)
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig} {A : Block} {H : Nat}
    (hEUF : KeyStealingEUFCMA n Δconf ops registry rented Stolen
      honestSigned now Δ)
    (hHash : SignedHashInjective (KeyStealingSigned n ops registry) G)
    (hA : A ∈ stripSigs sc) (hA' : A ∈ stripSigs sc')
    (hFresh : now ≤ A.slot + H)
    (hBudget : ∀ u, now < u + n + H →
      (badSlotsIn (badKeyrot n Δconf rented Stolen (stripSigs sc)) u n).card
        ≤ faultBudget n)
    (hVal  : validSignedChainK' n Δconf ops registry sc  = true)
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
  rw [validSignedChainK'_eq_core] at hVal hVal'
  exact MoltPetit.Model.keyrot_recent_tip_ancestor_agreement_anchored hn hΔ
    hEUF hHash hA hA'
    (fun u hu => hBudget u (by omega))
    hVal hVal' hTipS hTipS' hRecent hRecent' hLong hLong' hTipHeight hB hB'

/-- Mode 1's certificate-level safety: the agreement of
`client_refresh_rule`'s family at the certificate presentation, with the
floor carried as a snapshot in the claim — under the global, all-window
budget (the anchored, trailing-window form is future work at this
presentation). -/
alias keyrot_recent_certified_suffix_agreement :=
  MoltPetit.Model.keyrot_recent_certified_suffix_agreement

/-- The strengthened certificate grounding for mode 1: each fold also
checks the per-producer floor, and the certificate must attest claim and
floor together (paper §6.3). -/
abbrev GroundedCertK := @MoltPetit.Model.GroundedCertK

/-! ## Modes 2 and 3: anchor-free safety -/

/-- Mode 2's certificate-level safety: the scheduled agreement at the
certificate presentation — no floor snapshot, since the pin is computed
from each block's own slot. -/
alias sched_recent_certified_suffix_agreement :=
  MoltPetit.Model.sched_recent_certified_suffix_agreement

/-- Mode 2's **horizon-scoped** safety: the budget is consulted only on
windows from a horizon at most one window below the tips — under the
tight recency rule, no slot more than `2n - 1` before the clock is ever
budgeted, and genesis agreement becomes a consequence rather than a
hypothesis. The realistic sleeping-wallet form. -/
alias sched_recent_tip_ancestor_agreement_horizon :=
  MoltPetit.Model.sched_recent_tip_ancestor_agreement_horizon

/-- Mode 2's genesis agreement as a conclusion, under the horizon budget. -/
alias sched_recent_genesis_agreement_horizon :=
  MoltPetit.Model.sched_recent_genesis_agreement_horizon

/-- Mode 2 at the certificate presentation, under the horizon budget. -/
alias sched_recent_certified_suffix_agreement_horizon :=
  MoltPetit.Model.sched_recent_certified_suffix_agreement_horizon

/-- Mode 1 against key loss: Theorem 1 for the mode-1 validator (paper Theorem
`thm:keyloss`). No theft guarantee. -/
alias keyrot_loss_agreement :=
  MoltPetit.Model.keyrot_loss_agreement

/-- Mode 2 against key loss: Theorem 1 for the scheduled validator. -/
alias sched_loss_agreement :=
  MoltPetit.Model.sched_loss_agreement

/-- What the mode-2 validator admits, per block: a signature verifying under
the declared version, and a declared version meeting the schedule. -/
abbrev SchedAdmissible := @MoltPetit.Model.SchedAdmissible

/-- Mode-2 exposure: a stamp is exposed when its seat is controlled, or a
version of its key at or above the stamp's scheduled floor is stolen. -/
abbrev schedExposed := MoltPetit.Model.schedExposed

/-- Mode 2 against key theft (paper Theorem `thm:sched`): Theorem 1 for the
scheduled validator, with custody assumed only for admissible blocks and
exposure read at the schedule. -/
alias sched_exposure_agreement :=
  MoltPetit.Model.sched_exposure_agreement

/-- Mode 2 against key theft at the certificate presentation. -/
alias sched_exposure_certified_agreement :=
  MoltPetit.Model.sched_exposure_certified_agreement

/-- Mode 3 against key loss: Theorem 1 for the lockstep validator. -/
alias lockstep_loss_agreement :=
  MoltPetit.Model.lockstep_loss_agreement

/-- Mode 2's membership form (unequal tip heights), under the global
budget. -/
alias sched_recent_tip_ancestor_mem :=
  MoltPetit.Model.sched_recent_tip_ancestor_mem

/-- Mode 2's membership form under the **horizon-scoped** budget — the
unequal-height companion of the sleeping-wallet theorem. -/
alias sched_recent_tip_ancestor_mem_horizon :=
  MoltPetit.Model.sched_recent_tip_ancestor_mem_horizon

/-- Mode 3's membership form (unequal tip heights). -/
alias lockstep_recent_tip_ancestor_mem :=
  MoltPetit.Model.lockstep_recent_tip_ancestor_mem

/-- A shared block at one index drags the shared prefix down to every
lower index — the parent-id chaining step the deployment cards cite. -/
alias same_block_same_prefix := MoltPetit.Model.same_block_same_prefix

/-- Mode 2's strengthened certificate grounding: each fold also checks
the scheduled pin. -/
abbrev GroundedCertSched := @MoltPetit.Model.GroundedCertSched

/-- A chain whose tip declares a generation whose era ended more than `Δ`
ago fails the recency check — no budget consulted (paper §6.3, mode 2). -/
alias sched_oldkey_fork_stale := MoltPetit.Model.sched_oldkey_fork_stale

/-- The pinning theorem: on an accepted recent lockstep chain, every
matured window declares exactly the roster's counter (paper §6.3,
mode 3). -/
alias lockstep_declares_rosterGen :=
  MoltPetit.Model.lockstep_declares_rosterGen

/-- **Scheduled safety** (mode 2, paper Theorem 4). Under the scheduled
validator, a chain-independent budget, and the scheduled unforgeability
surface: two accepted chains rooted in one genesis with recent equal-height
tips agree on the block `n` below each tip — no anchor, no refresh rule,
no confirmation depth. The client is genesis plus a clock. -/
theorem scheduled_client_safety
    {n : Nat} (hn : 1 ≤ n) {schedule : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block}
    {sc sc' : SignedChain Sig}
    (hUnf : SchedUnforgeable n schedule ops registry rented Stolen
      honestSigned now Δ)
    (hHash : SignedHashInjective (SignedDeclared n ops registry) G)
    (hBudget : FaultBounded n (badSched n schedule rented Stolen))
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
    (hB  : blockAt? (stripSigs sc )
      ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc')
      ((stripSigs sc').length - 1 - n) = some B') :
    B = B' := by
  rw [validSignedChainSched_eq_core] at hVal hVal'
  exact MoltPetit.Model.sched_recent_tip_ancestor_agreement hn hUnf hHash
    hBudget hVal hVal' hHead hHead' hTipS hTipS' hRecent hRecent'
    hLong hLong' hTipHeight hB hB'

/-- **Lockstep safety** (mode 3, paper Theorem 5). Under the schedule-free
lockstep validator and the lockstep package alone: the same anchor-free
agreement, at a freely-timed rotation cadence. The client holds even less
than mode 2's — genesis and a clock, with no schedule constant to pin. -/
theorem lockstep_client_safety
    {n : Nat} (hn : 1 ≤ n) {rosterGen : Nat → Nat}
    {Sig sk pk : Type} {ops : SigOps Sig sk pk} {registry : KeyRegistry pk}
    {rented : ByzantineSlots} {Stolen : Nat → Nat → Prop}
    {honestSigned : SigningLog} {now Δ : Nat} {G : Block} {R T : Nat}
    (hP : LockstepPackage n rosterGen ops registry rented Stolen
      honestSigned now Δ G R T)
    {sc sc' : SignedChain Sig}
    (hVal  : validSignedChainLock n ops registry sc  = true)
    (hVal' : validSignedChainLock n ops registry sc' = true)
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
    (hB  : blockAt? (stripSigs sc )
      ((stripSigs sc ).length - 1 - n) = some B)
    (hB' : blockAt? (stripSigs sc')
      ((stripSigs sc').length - 1 - n) = some B') :
    B = B' := by
  rw [validSignedChainLock_eq_core] at hVal hVal'
  exact MoltPetit.Model.lockstep_recent_tip_ancestor_agreement hn hP
    hVal hVal' hHead hHead' hTipS hTipS' hRecent hRecent'
    hLong hLong' hTipHeight hB hB'


/-- Core unforgeability surface for mode 2 and mode 3 (paper §6.3, Assumption 6). -/
abbrev SchedCoreUnforgeable := @MoltPetit.Model.SchedCoreUnforgeable

/-- Not-before: a generation's key cannot be stolen before it is derived
(paper §6.3, mode 2). -/
abbrev NoPrematureTheft := @MoltPetit.Model.NoPrematureTheft

end Molt
