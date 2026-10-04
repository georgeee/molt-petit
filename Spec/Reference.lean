import Spec.Model

/-!
# The reference verifier and the paper-vocabulary names over the model.

Definitions only: no theorem, no proof. The development imports this file.
-/

/-! ### From `Molt.Protocol` -/

namespace Molt

/-- Quorum: the window-density threshold, `⌈2n/3⌉` of the `n` roster seats
(computed as `⌊(2n+2)/3⌋`). -/
def quorum (n : Nat) : Nat := (2 * n + 2) / 3

/-- Fault budget: the number of slots per `n`-slot window the adversary may
control, `⌊(n-1)/3⌋`. -/
def faultBudget (n : Nat) : Nat := (n - 1) / 3

/-- Slot `s` belongs to roster seat `s % n`: leadership is deterministic and
public. -/
def producer (n slot : Nat) : Nat := slot % n

/-- A block (shared type; see the module comment). -/
abbrev Block := MoltPetit.Model.Block

/-- A chain: blocks lowest height first. -/
abbrev Chain := MoltPetit.Model.Chain

/-- A genesis block: height 0 and no parent. -/
def genesisOk (b : Block) : Bool :=
  decide (b.height = 0 ∧ b.prev = none)

/-- `child` extends `parent`: height up by one, slot strictly later, `prev`
pointing at the parent's id. -/
def childOk (parent child : Block) : Bool :=
  decide (child.height = parent.height + 1 ∧
          parent.slot < child.slot ∧
          child.prev = some parent.id)

/-- Every adjacent pair of the chain links correctly. -/
def linksOk : Chain → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => childOk a b && linksOk (b :: rest)

/-- Does block `b` occupy a slot in the half-open window `[u, u + len)`? -/
def blockInWindow (u len : Nat) (b : Block) : Bool :=
  decide (u ≤ b.slot ∧ b.slot < u + len)

/-- How many chain blocks occupy slots in `[u, u + len)`. -/
def windowCount (c : Chain) (u len : Nat) : Nat :=
  (c.filter (blockInWindow u len)).length

/-- Window `[u, u + n)` meets the quorum-density bound. -/
def windowDense (n : Nat) (c : Chain) (u : Nat) : Bool :=
  decide (quorum n ≤ windowCount c u n)

/-- All windows matured at tip slot `t` are dense. A window `[u, u + n)` has
matured once `u + n ≤ t + 1`, so the matured starts are exactly
`0, …, t + 1 - n`. -/
def denseSoFar (n : Nat) (c : Chain) (t : Nat) : Bool :=
  (List.range (t + 2 - n)).all fun u => windowDense n c u

/-- Full chain validity, replayed from genesis: a well-formed genesis block,
correct links throughout, and every matured window dense. This is the rule
every node applies to a candidate chain before adopting it. -/
def validChain (n : Nat) (c : Chain) : Bool :=
  match c with
  | [] => true
  | g :: rest =>
    genesisOk g &&
    linksOk (g :: rest) &&
    (match (g :: rest).getLast? with
     | some tip => denseSoFar n (g :: rest) tip.slot
     | none => true)
end Molt

/-! ### From `Molt.Verifier` -/

namespace Molt

/-- Abstract signature operations over signature type `σ`, secret-key type
`sk`, and public-key type `pk`: `sign` and `verify`. -/
abbrev SigOps (σ sk pk : Type) := MoltPetit.Model.SigOps σ sk pk

/-- The versioned public-key directory: `registry i j` is seat `i`'s public
key at version `j`, written `dk(i, j)` in the paper. Deployments realize it
inside the signature bundle (paper §3), not as a service. -/
abbrev KeyRegistry (pk : Type) := MoltPetit.Model.KeyRegistry pk

/-- A block on the wire: content plus a detached signature. -/
abbrev SignedBlock (σ : Type) := MoltPetit.Model.SignedBlock σ

/-- A signed chain. -/
abbrev SignedChain (σ : Type) := MoltPetit.Model.SignedChain σ

/-- Forget the signatures. -/
def stripSigs {σ : Type} (sc : SignedChain σ) : Chain :=
  sc.map MoltPetit.Model.SignedBlock.block

/-- One block's signature verifies, under the key of its slot's producer at
the block's declared version. -/
def sigOk {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk)
    (registry : KeyRegistry pk) (sb : SignedBlock σ) : Bool :=
  ops.verify (registry (producer n sb.block.slot) sb.block.keyIndex)
    sb.block sb.sig

/-- Every block's signature verifies. -/
def sigsOk {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk)
    (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sc.all (sigOk n ops registry)

/-- What a certificate claims: the tip it vouches for (id, slot, height)
plus a boundary buffer of near-tip stripped blocks, so window density can
be counted across the certificate/suffix seam. -/
abbrev CertClaim := MoltPetit.Model.CertClaim

/-- Abstract certificate operations: read the `claim`, `verify` the
certificate (e.g. verify a recursive ZK proof), `generate` an extension by
one validated block. -/
abbrev CertOps (α : Type) := MoltPetit.Model.CertOps α

/-- What a node holds: a certificate for the prefix plus a signed suffix. -/
abbrev CertifiedChain (α σ : Type) := MoltPetit.Model.CertifiedChain α σ

/-- Effective tip height: the suffix tip's if the suffix is nonempty, else
the claim's. -/
def tipHeight {α σ : Type} (ops : CertOps α) (cc : CertifiedChain α σ) : Nat :=
  cc.suffix.getLast?.map (·.block.height) |>.getD (ops.claim cc.cert).tipHeight

/-- Validate a signed suffix as a continuation of a certified prefix:
signatures; the structural link from claim tip to first suffix block; links
within the suffix; density of every window maturing inside the suffix,
counted over the boundary buffer plus the suffix. -/
def validSuffix {α σ sk pk : Type} (n : Nat)
    (sigOps : SigOps σ sk pk) (registry : KeyRegistry pk)
    (certOps : CertOps α) (cert : α)
    (suffix : SignedChain σ) : Bool :=
  let chain := stripSigs suffix
  sigsOk n sigOps registry suffix &&
  match chain with
  | [] => true
  | first :: rest =>
    let c := certOps.claim cert
    decide (first.height = c.tipHeight + 1 ∧
            c.tipSlot < first.slot ∧
            first.prev = some c.tipId) &&
    linksOk (first :: rest) &&
    (match (first :: rest).getLast? with
     | none   => true
     | some t =>
         let buf := c.tail ++ (first :: rest)
         let lo  := c.tipSlot + 2 - n
         let hi  := t.slot + 2 - n
         (List.range (hi - lo)).all fun d => windowDense n buf (lo + d))

/-- **Validate**: the certificate verifies and the suffix continues it. -/
def validCertifiedChain {α σ sk pk : Type} (n : Nat)
    (sigOps : SigOps σ sk pk) (registry : KeyRegistry pk)
    (certOps : CertOps α) (cc : CertifiedChain α σ) : Bool :=
  certOps.verify cc.cert &&
  validSuffix n sigOps registry certOps cc.cert cc.suffix

/-- **Produce**: only in the caller's own slot — build the next block on
the current tip, sign it, append it, and ship the result only if it passes
the same suffix validation every other node runs. -/
def produceBlock? {α σ sk pk : Type} (n me slot newId : Nat)
    (contentsHash keyIndex : Nat)
    (sigOps : SigOps σ sk pk) (registry : KeyRegistry pk) (myKey : sk)
    (certOps : CertOps α) (cc : CertifiedChain α σ) :
    Option (SignedBlock σ × CertifiedChain α σ) :=
  if producer n slot ≠ me then none
  else
    let c   := certOps.claim cc.cert
    let tip : Block :=
      cc.suffix.getLast?.map (·.block) |>.getD
        { slot := c.tipSlot, height := c.tipHeight, prev := none,
          id := c.tipId, contentsHash := 0, keyIndex := 0 }
    let b  : Block         :=
      { slot, height := tip.height + 1, prev := some tip.id, id := newId,
        contentsHash, keyIndex }
    let sb : SignedBlock σ := { block := b, sig := sigOps.sign myKey b }
    let newSuffix := cc.suffix ++ [sb]
    if validSuffix n sigOps registry certOps cc.cert newSuffix then
      some (sb, { cert := cc.cert, suffix := newSuffix })
    else none

/-- **Select**: adopt a candidate only if it validates and its tip is
strictly higher. Safety never depends on this rule (the theorems quantify
over arbitrary accepted chains); only liveness does. -/
def selectChain {α σ sk pk : Type} (n : Nat)
    (sigOps : SigOps σ sk pk) (registry : KeyRegistry pk)
    (certOps : CertOps α) (current candidate : CertifiedChain α σ) :
    CertifiedChain α σ :=
  if validCertifiedChain n sigOps registry certOps candidate &&
     tipHeight certOps candidate > tipHeight certOps current
  then candidate
  else current
end Molt

/-! ### From `Molt.Assumptions` -/

namespace Molt

/-- What was produced at each slot, as the safety proof sees it. -/
abbrev SlotRecord := MoltPetit.Model.SlotRecord

/-- An adversary schedule: `bad s` means the adversary owns slot `s`. -/
abbrev ByzantineSlots := MoltPetit.Model.ByzantineSlots

/-- The per-participant signing log: at most one block signed per slot by
the honest signing path. -/
abbrev SigningLog := MoltPetit.Model.SigningLog

/-- **Assumption 3 (hash collision resistance over occurring blocks).**
Two blocks that each are the genesis or carry a verifying signature, with
equal ids, are equal. -/
def SignedHashInjective (Signed : Block → Prop) (G : Block) : Prop :=
  ∀ ⦃B B' : Block⦄,
    (B = G ∨ Signed B) → (B' = G ∨ Signed B') →
    B.id = B'.id → B = B'

/-- **Assumption 4 (certificate grounding).** A verifying certificate's
claim was assembled from the genesis claim by fold steps that each check
the link rules, the density of newly matured windows, and a verifying
producer signature on the folded block. Re-exported inductive. -/
abbrev GroundedCert := @MoltPetit.Model.GroundedCert

/-- **Assumption 6 (honest delivery — liveness only).** Every honest slot
of the window has a produced block already incorporated in the chain. -/
def HonestBlocksCover (bad : ByzantineSlots) (record : SlotRecord)
    (c : Chain) (u n : Nat) : Prop :=
  ∀ s, ¬ bad s → u ≤ s → s < u + n → ∃ B : Block, B ∈ record s ∧ B ∈ c
end Molt

/-! ### From `Molt.Results` -/

namespace Molt

/-- What was signed at each **real** slot: `log r` is the set of blocks
whose producer signature was created at real slot `r`. -/
abbrev TimedLog := MoltPetit.Model.TimedLog

/-- The adversary's slot budget (untimed model). -/
abbrev ByzantineBounded := MoltPetit.Model.ByzantineBounded

/-- Key exposure: `exposed s r` — at real slot `r` someone other than its
honest holder can sign under the key that verifies stamp `s`. -/
abbrev Exposure := MoltPetit.Model.Exposure

/-- The exposure budget with freshness `φ`. -/
abbrev ExposureBounded := MoltPetit.Model.ExposureBounded

/-- The cumulative exposure budget: every exposure before the window's
freshness deadline counts, however early. -/
abbrev ExposureBoundedEver := MoltPetit.Model.ExposureBoundedEver

/-- The signing execution restricted to blocks satisfying an admissibility
predicate `Adm` (custody is claimed only for admissible blocks). -/
abbrev SigningExecutionOn := MoltPetit.Model.SigningExecutionOn

/-- Honest clocks, for admissible blocks only. -/
abbrev HonestClockOn := MoltPetit.Model.HonestClockOn

/-- `B` is the genesis or occurs in the log at some real slot. -/
abbrev SignedEver := MoltPetit.Model.SignedEver

/-- Semantic grounded history of a certificate claim. -/
abbrev GroundedHistory := MoltPetit.Model.GroundedHistory

/-- The block at a given height (list indexing). -/
def blockAt? (c : Chain) (h : Nat) : Option Block := getElem? c h
end Molt

/-! ### From `Molt.Rotation` -/

namespace Molt

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

/-- Seat `i`'s **floor**: the highest key version it has used anywhere in
the chain — the in-band counter. -/
def keyFloor (n : Nat) (c : Chain) (i : Nat) : Nat :=
  ((c.filter (fun b => decide (producer n b.slot = i))).map
    MoltPetit.Model.Block.keyIndex).foldl max 0

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

/-- What the mode-2 validator admits, per block: a signature verifying under
the declared version, and a declared version meeting the schedule. -/
abbrev SchedAdmissible := @MoltPetit.Model.SchedAdmissible

/-- Mode-2 exposure: a stamp is exposed when its seat is controlled, or a
version of its key at or above the stamp's scheduled floor is stolen. -/
abbrev schedExposed := MoltPetit.Model.schedExposed

/-- Mode 2's strengthened certificate grounding: each fold also checks
the scheduled pin. -/
abbrev GroundedCertSched := @MoltPetit.Model.GroundedCertSched

/-- What the scheduled grounding reconstructs: an accepted, schedule-pinned
history matching the claim, every block signed. -/
abbrev GroundedHistorySched := @MoltPetit.Model.GroundedHistorySched

/-- The horizon budget: at most `f` bad slots in every `n`-slot window
starting at or after `H` (untimed mode-2 form). -/
abbrev ByzantineBoundedFrom := MoltPetit.Model.ByzantineBoundedFrom

/-- Core unforgeability surface for mode 2 and mode 3 (paper §6.3, Assumption 6). -/
abbrev SchedCoreUnforgeable := @MoltPetit.Model.SchedCoreUnforgeable
end Molt

/-! ### From `Molt.LockstepGen` -/

namespace Molt

/-- The D1′-full lockstep package: per-generation budget, no `mono`/
`genesis_gen` (unconsumed by the non-inductive, genesis-free pinning route). -/
abbrev LockstepPackageGen := @MoltPetit.Model.LockstepPackageGen

/-- Mode 3 with its temporal content formalized: theft is time-stamped,
erasure (`notAfter`) is load-bearing here — the mirror of mode 2's
`PackageBTimed`, where erasure is documentary. -/
abbrev LockstepPackageTimed := @MoltPetit.Model.LockstepPackageTimed

/-- The temporal erasure hypothesis for mode 3: no generation is stolen after
the roster moves past it (paper §6.3, mode 3). -/
abbrev ErasureTimedLock := @MoltPetit.Model.ErasureTimedLock
end Molt
