# SubsetCheck: TH0086 false positive on scrutinee field access inside switch arms

`c.prev === null` inside a `switch (c.kind)` arm is rejected by TH0086,
although the emitter itself rewrites scrutinee field access to the
destructured binder in exactly this position (the emitted Lean is fine
when the check is bypassed).

## Repro (`repro.ts`)

```ts
type C = { kind: 'nil' } | { kind: 'cons'; prev: bigint | null; tail: C };

/** @total */
function headHasPrev(c: C): boolean {
  switch (c.kind) {
    case 'nil':
      return false;
    case 'cons':
      return !(c.prev === null);
  }
}
```

At pristine 55b03fb (verbatim):

```
repro.ts(9,16): error TH0086: A definedness test against 'undefined'/'null' is only supported when its subject is a variable; bind this expression to a variable first
```

## Fix

Track switch scrutinees and exempt `scrut.field` subjects inside the
corresponding arms. Working patch: the `Emit/SubsetCheck.lean` hunk of
`thales-fixes.patch` (adds `MutCtx.unionScruts`).
