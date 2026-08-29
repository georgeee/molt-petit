# Parser: parenthesized ternary consequent fails with "Expected ':' in ternary"

`parseParenExpr` unconditionally consumes `: T` after a parenthesized
expression as an arrow return-type annotation, even when no `=>`
follows, so any conditional whose consequent is parenthesized fails to
parse.

## Repro (`repro.ts`)

```ts
/** @total */
function pick(a: bigint, b: bigint): bigint {
  const f = a === b ? (a < b ? a : b) : a;
  return f;
}
```

`thales repro.ts` at pristine 55b03fb (verbatim):

```
Parse error: Expected ':' in ternary at line 3, got Thales.Parser.TokenKind.semicolon
```

The outer ternary's `:` was eaten as an annotation after
`(a < b ? a : b)`.

## Fix

After parsing `( expr )` and speculatively consuming `: T`, rewind
unless the next token is `=>`. Working patch: the `Parser/Pratt.lean`
hunk of `thales-fixes.patch` in this directory's parent.
