## What

`parseParenExpr` unconditionally consumes `: T` after a parenthesized
expression as an arrow return-type annotation, even when no `=>`
follows — so any conditional whose consequent is parenthesized fails to
parse.

## Repro (at pristine 55b03fb)

```ts
/** @total */
function pick(a: bigint, b: bigint): bigint {
  const f = a === b ? (a < b ? a : b) : a;
  return f;
}
```

```
Parse error: Expected ':' in ternary at line 3, got Thales.Parser.TokenKind.semicolon
```

(The outer ternary's `:` was eaten as an annotation after `(a < b ? a : b)`.)

## Fix

After parsing `( expr )` and speculatively consuming `: T`, rewind
unless the next token is `=>`.

## Regression test

`tests/conformance/accept/ternary-paren-consequent.ts` (included).
Verified against the conformance contract on both sides: Node
(`--experimental-strip-types`) and `thales` + `lake env lean` print the
identical `true` / `true`.

Found while re-emitting a ~750-line consensus reference implementation
written in the Thales subset; two companion PRs fix the further issues
that file surfaced.
