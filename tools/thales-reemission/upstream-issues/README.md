# Ready-to-file upstream issues for jessealama/thales

Found while re-emitting `moltPetit.ts` (Thales at commit
`55b03fb3fbbcca615cb438b2492d6a1c115d0394`, lean4 v4.29.0). Issues 1-3
block compilation and carry working fixes (hunks in
`../thales-fixes.patch`); issues 4-5 are emitter-output bugs found by
reconciling the emission against a hand-verified vendored file. Issue 4
is the highest-severity: the emitted Lean *elaborates cleanly with
changed semantics* — the failure mode a verification pipeline most needs
to hear about.

Every repro was run and its quoted output captured verbatim: issues 1-3
against the pristine pinned commit, issues 4-5 against it plus the three
fixes (which do not touch the emitter paths involved). File as five separate issues; titles are the `#` headers.
