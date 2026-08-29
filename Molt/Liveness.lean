import Molt.Rotation
import MoltPetit.Results.Results
import MoltPetit.Model.KeyRotationLiveness

/-!
# Liveness (paper §6.4)

Paper-facing names for the liveness results. These are aliases rather
than restatements: the theorems quantify over the model-level production
and selection functions, which the paper does not re-present, so there is
nothing to rename in their statements.
-/

namespace Molt

/-- **Production never skips an honest slot** (paper Theorem 6, unsigned
form): an honest producer holding an accepted chain extends it and the
extension passes the validator. -/
alias production_liveness := MoltPetit.Model.liveness_produce_block

/-- Signed form of `production_liveness`. -/
alias signed_production_liveness := MoltPetit.Model.liveness_produce_signed_block

/-- Mode-1 recovery is also a liveness fact: a rotated extension passes
the pinned validator when its declared version clears the floor
(paper §2, mode 0). -/
alias liveness_produce_blockK := MoltPetit.Model.liveness_produce_blockK

/-- **Global liveness under synchrony** (paper Theorem 6, global form): a
synchronous honest run under the fault budget over the run's span is
validator-accepted with one block per honest slot, so the chain reaches
any height. -/
alias global_liveness := MoltPetit.Model.liveness_global

/-- The slot-duration rule (sufficiency): at or above the recommended
slot time, the certificate pipeline keeps the uncovered suffix within `n`
blocks forever. The paper states the rule qualitatively; the formula
lives here. -/
alias slot_time_sufficient := MoltPetit.Model.ProverTiming.recommended_slot_sufficient

/-- The slot-duration rule (necessity): below the recommended slot time,
every steady state of the pipeline overflows. -/
alias slot_time_necessary := MoltPetit.Model.ProverTiming.recommended_slot_necessary

end Molt
