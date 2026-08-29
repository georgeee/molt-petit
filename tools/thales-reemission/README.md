# Thales re-emission record (2026-07-11)

The vendored `MoltPetit/TS.lean` header long carried the caveat that the
indexed-validator functions and the certificate-boundary floor machinery
were *hand-mirrored* "pending re-emission through the Thales toolchain
(unavailable in the development environment)". This directory records the
re-emission that discharged that caveat.

## Toolchain

- Thales (https://github.com/jessealama/thales) at commit
  `55b03fb3fbbcca615cb438b2492d6a1c115d0394` (2026-06-30, lean4 v4.29.0),
  **plus** `thales-fixes.patch` (three compiler fixes, minimal repros were
  kept out of the repo; each is described in the patch hunks):
  1. `Parser/Pratt.lean` — `parseParenExpr` consumed `: T` after `(x)` as an
     arrow return annotation even with no `=>`, so any parenthesized ternary
     consequent (`c ? (x) : y`, `moltPetit.ts:468`) failed to parse.
  2. `TypeCheck/Synth.lean` — ternary synthesis built `.union [T, T]`, which
     assignability degraded to `object` for the named recursive union
     `FloorList` (TS2322 at `moltPetit.ts:470`); equal arms now collapse.
  3. `Emit/SubsetCheck.lean` — TH0086 rejected `c.prev === null` inside
     `switch (c.kind)` arms although the emitter rewrites the scrutinee
     field to the destructured binder; switch scrutinees are now tracked.

## Commands

    export PATH=/work/.elan/toolchains/leanprover--lean4---v4.29.0/bin:$PATH HOME=/work
    cd <thales checkout> && git apply thales-fixes.patch && lake build
    .lake/build/bin/thales -o <outdir> moltPetit.ts    # -> MoltPetit.lean

`MoltPetit.emitted.lean` is the raw, unedited emission.

## Reconciliation verdict

The emission agrees with the vendored `MoltPetit/TS.lean` body on every
previously hand-mirrored function, up to the header's documented deviation
classes (derive-clause fixes) and block ordering, and **differs at exactly
three sites where the raw emitter output is itself wrong** — the vendored
text carries the corrected, TS-faithful form:

1. `monoAgainst`: the emitted match binder `slot` shadows the enclosing
   `slot` parameter, collapsing `producerForSlot n slot == producerForSlot
   n slot'` to a tautology (semantics change!). Vendored uses `slot'`.
2. `produceBlock`: same shadowing class — the emitted binder `keyIndex`
   shadows the parameter, making the new block sign under the tip's version
   instead of the requested one. Vendored uses `keyIndex'`.
3. `floorBump`: the emitted union literal reads `(.fcons fl.producer f
   rest)` — the scrutinee→binder substitution is skipped inside
   union-literal field values, and unions have no `.producer` projection,
   so the raw emission does not elaborate. Vendored uses the binder.

(1) and (2) are one emitter deficiency: match binders take the union
declaration's field names verbatim and can capture enclosing parameters.
All three are upstream-reportable; none affects the vendored file, whose
bridge lemmas (`ts_keyMonoOk`, `ts_validChainK_sound`, `ts_keyMonoFromTs`,
`ts_validateSuffixK_sound`) pin the corrected text to the Lean model.

## Re-verification (2026-08-28), and the machine-enforced ledger

The toolchain was rebuilt from scratch at the same pin (`55b03fb` +
`thales-fixes.patch`, lean4 v4.29.0) and re-run on `moltPetit.ts`: the fresh
emission is **byte-identical** to `MoltPetit.emitted.lean`
(sha256 `39f7326c6d9cfd6d5d84140057e12c3d2ef9503dff9fef0295f056f3f5b37b9f`).

The comparison against the vendored `MoltPetit/TS/Emitted.lean` found, besides
the deviations documented above, **four cosmetic, semantics-neutral sites** the
prose list had not recorded: a `deriving Repr, BEq` on `FloorList` (same class
as the `Chain` derive deviation, but at an unlisted site), and three
redundant-paren removals (`floorBump`'s inner conditional,
`floorsShapeFrom (i + 1)`, `keyMonoFromTs`'s `floorBump` argument).

As of the same date the deviation set is no longer prose-only: the exact
golden-emission → vendored-body diff is checked in as
`vendored-deviations.patch` (this directory) and enforced by the flake check
`ts-vendored-deviations` (see `NIX.md`) — the vendored file must equal the
golden emission plus exactly that patch, so any new deviation, however small,
fails the build instead of joining this list silently.
