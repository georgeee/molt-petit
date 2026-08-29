# Typechecker: ternary with equal-typed arms builds `.union [T, T]`, breaking assignability for named recursive unions

Ternary synthesis joins the arm types as `.union [T, T]` even when both
arms have the same type. For a named recursive union, downstream
assignability degrades that degenerate union to `object`, producing a
false TS2322.

## Repro (`repro.ts`)

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

At pristine 55b03fb (verbatim — note the degenerate self-union in the
message):

```
repro.ts(10,14): error TS2322: Type 'L | L' is not assignable to type 'L'
```

On larger inputs the degenerate union also degrades further (the
original site, a recursive union threaded through a ternary, reported
assignability against `object`).

## Fix

Collapse the join when both arm types are equal. Working patch: the
`TypeCheck/Synth.lean` hunk of `thales-fixes.patch`.
