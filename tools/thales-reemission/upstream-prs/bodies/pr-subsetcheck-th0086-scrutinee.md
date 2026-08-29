## What

TH0086 ("definedness test subject must be a variable") fires on
`c.prev === null` inside a `switch (c.kind)` arm — although the emitter
itself rewrites scrutinee field access to the destructured binder in
exactly this position, so the emitted Lean is fine.

## Repro (at pristine 55b03fb)

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

```
repro.ts(9,16): error TH0086: A definedness test against 'undefined'/'null' is only supported when its subject is a variable; bind this expression to a variable first
```

## Fix

Track switch scrutinees (a `MutCtx.unionScruts` set) and exempt
`scrut.field` subjects inside the corresponding arms.

## Regression test

`tests/conformance/accept/switch-scrutinee-null-test.ts` (included).
Verified on both conformance sides; both print `true` / `false`.

Companion to the other two fixes from the same re-emission corpus. Note
for reviewers: the test initializes the nullable field from a variable
rather than a literal deliberately — literals in nullable positions hit
a separate emitter issue filed alongside these PRs.
