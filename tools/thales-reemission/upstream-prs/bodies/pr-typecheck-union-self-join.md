## What

Ternary type synthesis joins the arm types as `.union [T, T]` even when
both arms have the same type. For a named recursive union, downstream
assignability then rejects the degenerate self-union.

## Repro (at pristine 55b03fb)

```ts
type L = { kind: 'nil' } | { kind: 'cons'; v: bigint; tail: L };

/** @total */
function idTail(a: bigint, b: bigint, l: L): L {
  switch (l.kind) {
    case 'nil':
      return l;
    case 'cons': {
      const r = a === b ? l.tail : l.tail;
      return r;
    }
  }
}
```

```
repro.ts(10,14): error TS2322: Type 'L | L' is not assignable to type 'L'
```

(`tsc --strict` accepts the file; the self-union in the message is the
bug. On larger inputs the degenerate union degrades further — the
original site reported assignability against `object`.)

## Fix

Collapse the join when both arm types are equal.

## Regression test

`tests/conformance/accept/ternary-equal-arms-recursive-union.ts`
(included). Verified on both conformance sides; both print `true`.

Companion to the parenthesized-ternary parser fix; found on the same
re-emission corpus.
