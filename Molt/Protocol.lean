import MoltPetit.Model.Definitions
import Spec.Reference

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

/-! ## Blocks and chains

A block carries six fields — `slot`, `height`, `prev`, `id`,
`contentsHash`, `keyIndex`. The type is the core development's
`MoltPetit.Model.Block`, re-exported. `id` is a collision-resistant hash of
the block supplied by the deployment's hashing layer under the paper's
id-formation contract; `contentsHash` commits to the out-of-band payload;
`keyIndex` is the signing-key version the producer signed under (paper §6's
rotation machinery rides on it). -/

/-- The genesis block of a fresh deployment: slot 0, height 0, no parent,
key index 0. -/
def genesisBlock (id : Nat) : Block :=
  { slot := 0, height := 0, prev := none, id, contentsHash := 0, keyIndex := 0 }

/-! ## The density rule -/

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
