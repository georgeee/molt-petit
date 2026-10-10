import Spec.TS

/-!
# Pass 24 Task (d) Guard Test

Regression test: at n = 7, the genesis certificate followed by one block at
slot 1 (height 1, prev = genesis id, correct key index, floor snapshot accepting it)
is accepted by `validateSuffix` (and `validateSuffixK`), confirming the density
window clamp at slot 0.
-/

namespace MoltPetit

private def genesisBlock : Chain :=
  .cons 0 0 none 100 0 0 .nil

private def genesisClaim : CertClaim :=
  { tipSlot := 0, tipHeight := 0, tipId := 100, tail := genesisBlock }

private def suffixBlock : Chain :=
  .cons 1 1 (some 100) 101 0 0 .nil

private def fl0 : FloorList :=
  .fcons 0 0 (.fcons 1 0 (.fcons 2 0 (.fcons 3 0 (.fcons 4 0 (.fcons 5 0 (.fcons 6 0 .fnil))))))

#guard validateSuffix 7 genesisClaim suffixBlock == true
#guard validateSuffixK 7 genesisClaim fl0 suffixBlock == true

end MoltPetit
