# Emitter: numeric literal in a `T | null` position emits a bare numeral that fails `OfNat (Option Int)`

A literal written directly into a nullable-typed position survives into
the emitted Lean as a bare numeral, where the expected type is
`Option Int`; Lean's polymorphic numerals then fail with
`OfNat (Option Int) 7`. Values arriving via variables are fine (the
runtime's coercion handles them) — only literals trip it.

## Repro (`option-literal.ts`)

```ts
type C = { kind: 'nil' } | { kind: 'cons'; prev: bigint | null; tail: C };

/** @total */
function isNil(c: C): boolean {
  switch (c.kind) {
    case 'nil':
      return true;
    case 'cons':
      return false;
  }
}

const one: C = { kind: 'cons', prev: 7n, tail: { kind: 'nil' } };
console.log(isNil(one));
```

## Emitted + elaboration (55b03fb + the three fixes; verbatim)

The union literal emits `prev := 7` into the field typed
`(prev : (Option Int))`:

```
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  OfNat (Option Int) 7
numerals are polymorphic in Lean, but the numeral `7` cannot be used in a
context where the expected type is Option Int
```

## Suggested fix

Wrap literals flowing into nullable positions (`.some 7`), or ascribe
(`(7 : Int)`) so the runtime coercion that already covers variables
applies.
