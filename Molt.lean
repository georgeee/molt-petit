import Molt.Protocol
import Molt.Verifier
import Molt.Assumptions
import Molt.Results
import Molt.Rotation
import Molt.KeyStealingTimedScope
import Molt.ClientRule
import Molt.CertClientRule
import Molt.LockstepGen
import Molt.LockstepCert
import Molt.SyncInduction
import Molt.SyncRuleTimed
import Molt.MaxSync
import Molt.MaxSyncSignatureTimed
import Molt.Liveness
import Molt.Axioms
import Molt.AxiomsKeyStealingTimedScope
import Molt.AxiomsSyncInduction
import Molt.AxiomsSyncRuleTimed
import Molt.AxiomsMaxSyncSignatureTimed
import Molt.AxiomsCertAnchored
import Molt.AxiomsLockstepGen
import Molt.LockstepCertAxioms
import Molt.AxiomsTimedSafety

/-!
# Molt — the paper-aligned codebase

This library re-presents the Molt Petit development in the order and
vocabulary of the rewritten paper (`paper/molt.tex`): one module per paper
section, definitions written out fresh so the paper can quote them, and the
headline theorems restated in the paper's terms.

Proof engine: each fresh definition is bridged to its counterpart in the
original `MoltPetit` development by a `rfl`-lemma, and every theorem is
transported across those bridges — so everything here is machine-checked
against the same core, and the axiom guards apply unchanged.

Modules grow section by section with the paper; the imports above are the
current frontier.
-/
