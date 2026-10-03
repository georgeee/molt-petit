import Molt.Rotation
import MoltPetit.Model.KeyStealingLockstepCert

/-!
# Molt — mode 3 (free-cadence lockstep) at the certificate presentation

The paper-namespace re-presentation of W1: mode 3's certificate form,
discharging the honest-scope bound that its theorems were full-chains-only.
Re-export idiom of `Molt/Rotation.lean`'s `GroundedCertSched`/
`sched_recent_certified_suffix_agreement` pair — the statements below mention
only re-exported names (`LockstepPackage`, `SignedDeclared`) plus core
`linksOk`/`lockstepFrom`, exactly as the mode-2 certificate alias does.
-/

namespace Molt

/-- The lockstep certificate grounding: each fold also checks the no-mixing
rule against the threaded tip generation. The certificate attests claim and
tip generation together; for `n ≥ 2` the generation is read off the tail
buffer (`MoltPetit.Model.groundedCertLock_gen_of_tail`), so nothing beyond
the plain claim crosses the wire in that regime — only `n = 1` (empty tail)
needs the extra counter. -/
abbrev GroundedCertLock := @MoltPetit.Model.GroundedCertLock

/-- The suffix-side no-mixing check a certificate-syncing verifier runs. -/
abbrev lockstepFrom := @MoltPetit.Model.lockstepFrom

/-- Mode 3's certificate-level pinning: the certificate's own tip counter
equals the roster's counter for its grid window once the suffix matures that
window (paper §6.3). -/
alias lockstep_cert_gen_pinned := MoltPetit.Model.lockstep_cert_gen_pinned

/-- Mode 3's certificate-level pinning census, over every verifier-visible
block. -/
alias lockstep_cert_declares_rosterGen := MoltPetit.Model.lockstep_cert_declares_rosterGen

/-- Mode 3's certificate-level safety: the agreement of
`lockstep_recent_tip_ancestor_agreement`'s family at the certificate
presentation, under the lockstep package alone (paper §6.3). -/
alias lockstep_recent_certified_suffix_agreement :=
  MoltPetit.Model.lockstep_recent_certified_suffix_agreement


/-- For n ≥ 2 the tip generation of a certificate is determined by the tail buffer
(paper §6.3). -/
alias groundedCertLock_gen_of_tail := MoltPetit.Model.groundedCertLock_gen_of_tail

/-- Uniqueness of the tip generation determined by the tail buffer for n ≥ 2
(paper §6.3). -/
alias groundedCertLock_gen_unique := MoltPetit.Model.groundedCertLock_gen_unique

end Molt
