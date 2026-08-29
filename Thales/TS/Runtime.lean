/-
Stub for the Thales runtime module.

The emitted sidecar `MoltPetit/TS/Emitted.lean` opens with
`import Thales.TS.Runtime` (every thales-emitted file does), but our
protocol source `moltPetit.ts` deliberately avoids everything that
lowers to a runtime helper or prelude type — no `number` arithmetic, no
`%` (jsMod), no console, no refinement types (cryptographic material is
opaque bigint handles, emitted as `Int`). So an empty namespace
satisfies the import without pulling in the runtime's Float/IEEE-754
axioms.

If a future re-emission of the TypeScript starts referencing a runtime
helper, the build breaks here loudly — at that point vendor the real
runtime (thales repo, `Thales/TS/Runtime.lean`, MIT) or excerpt the
needed definitions.
-/

namespace Thales.TS

end Thales.TS
