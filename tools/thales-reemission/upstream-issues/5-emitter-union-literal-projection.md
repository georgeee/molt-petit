# Emitter: union-literal field values skip the scrutinee-to-binder substitution

Inside a switch arm, scrutinee field access is normally rewritten to
the destructured binder — except when it appears as a *field value of a
union literal*, where the raw projection survives into the emitted
Lean. Lean unions (inductives) have no field projections, so the output
does not elaborate.

## Repro (`unionlit.ts`)

```ts
type List = { kind: 'nil' } | { kind: 'cons'; v: bigint; tail: List };

/** @total */
function keep(l: List): List {
  switch (l.kind) {
    case 'nil':
      return { kind: 'nil' };
    case 'cons': {
      const rest = keep(l.tail);
      return { kind: 'cons', v: l.v, tail: rest };
    }
  }
}
```

## Emitted (55b03fb + the three fixes; verbatim)

```lean
def keep (l : List) : List :=
  match l with
    | .nil => .nil
    | .cons v tail => let rest := (keep tail)
    (.cons l.v rest)
```

Elaboration fails:

```
error(lean.invalidField): Invalid field `v`: The environment does not
contain `Unionlit.List.v`, so it is not possible to project the field
`v` from an expression l of type `List`
```

Expected: `(.cons v rest)`. Note `keep l.tail` in the same arm IS
correctly rewritten to `keep tail` — the substitution is skipped only
for union-literal field values.
