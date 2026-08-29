import MoltPetit.Model.Definitions

/-!
# The protocol: blocks, chains, and the density rule (paper §3)

Fresh, paper-ordered presentation of the data model and the chain-validity
rule. Every definition here is written out in full so the paper can quote
it; a `Bridge` section at the bottom proves each one definitionally equal
to its counterpart in the original `MoltPetit.Model` development, which is
what lets the original theorems transport to these names unchanged.

The block/chain *types* are shared with the core development (re-exported,
not re-declared): a re-declared structure would be a different type and
nothing would transport. Everything that *computes* is re-stated fresh.
-/

namespace Molt

/-! ## Setting -/

/-- Quorum: the window-density threshold, `⌈2n/3⌉` of the `n` roster seats
(computed as `⌊(2n+2)/3⌋`). -/
def quorum (n : Nat) : Nat := (2 * n + 2) / 3

/-- Fault budget: the number of slots per `n`-slot window the adversary may
control, `⌊(n-1)/3⌋`. -/
def faultBudget (n : Nat) : Nat := (n - 1) / 3

/-- Slot `s` belongs to roster seat `s % n`: leadership is deterministic and
public. -/
def producer (n slot : Nat) : Nat := slot % n

/-! ## Blocks and chains

A block carries six fields — `slot`, `height`, `prev`, `id`,
`contentsHash`, `keyIndex`. The type is the core development's
`MoltPetit.Model.Block`, re-exported. `id` is a collision-resistant hash of
the block supplied by the deployment's hashing layer under the paper's
id-formation contract; `contentsHash` commits to the out-of-band payload;
`keyIndex` is the signing-key version the producer signed under (paper §6's
rotation machinery rides on it). -/

/-- A block (shared type; see the module comment). -/
abbrev Block := MoltPetit.Model.Block

/-- A chain: blocks lowest height first. -/
abbrev Chain := MoltPetit.Model.Chain

/-- The genesis block of a fresh deployment: slot 0, height 0, no parent,
key index 0. -/
def genesisBlock (id : Nat) : Block :=
  { slot := 0, height := 0, prev := none, id, contentsHash := 0, keyIndex := 0 }

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

/-! ## The density rule -/

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

/-! ## Bridge to the core development

Each paper-facing name is definitionally the original. These lemmas are the
transport rails: any `MoltPetit.Model` theorem about the right-hand sides
is, verbatim, a theorem about the left-hand sides. -/

theorem quorum_eq_core : quorum = MoltPetit.Model.quorum := rfl
theorem faultBudget_eq_core : faultBudget = MoltPetit.Model.maxByzantine := rfl
theorem producer_eq_core : producer = MoltPetit.Model.producerForSlot := rfl
theorem genesisBlock_eq_core : genesisBlock = MoltPetit.Model.genesisBlock := rfl
theorem genesisOk_eq_core : genesisOk = MoltPetit.Model.genesisOk := rfl
theorem childOk_eq_core : childOk = MoltPetit.Model.childOk := rfl
theorem windowDense_eq_core : windowDense = MoltPetit.Model.windowDense := rfl
theorem denseSoFar_eq_core : denseSoFar = MoltPetit.Model.maturedWindowsDense := rfl

theorem linksOk_eq_core : linksOk = MoltPetit.Model.linksOk := by
  funext c
  induction c with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      simp only [linksOk, MoltPetit.Model.linksOk, childOk_eq_core, ih]

theorem validChain_eq_core : validChain = MoltPetit.Model.validChain := by
  funext n c
  cases c with
  | nil => rfl
  | cons g rest =>
    cases h : (g :: rest).getLast? with
    | none =>
      simp only [validChain, MoltPetit.Model.validChain, h, genesisOk_eq_core,
        linksOk_eq_core]
    | some tip =>
      simp only [validChain, MoltPetit.Model.validChain, h, genesisOk_eq_core,
        linksOk_eq_core, denseSoFar_eq_core]

end Molt
