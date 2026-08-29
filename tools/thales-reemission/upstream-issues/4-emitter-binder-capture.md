# Emitter: match binders take union field names verbatim and capture enclosing bindings — silent miscompilation

The emitter names each match binder after the union field it
destructures. When a field name coincides with an enclosing parameter
or local, the binder captures it, and the emitted Lean *elaborates
cleanly with different semantics than the TypeScript source*. For a
compiler used in verification trusted bases this is the worst failure
class: no error, wrong program.

## Repro (`shadow.ts`)

```ts
type List = { kind: 'nil' } | { kind: 'cons'; slot: bigint; tail: List };

/** @total */
function count(slot: bigint, l: List): bigint {
  switch (l.kind) {
    case 'nil':
      return 0n;
    case 'cons': {
      const hit = slot === l.slot ? 1n : 0n;
      return hit + count(slot, l.tail);
    }
  }
}
```

## Emitted (55b03fb + the three fixes; verbatim)

```lean
def count (slot : Int) (l : List) : Int :=
  match l with
    | .nil => 0
    | .cons slot tail => let hit := if (slot == slot) then 1 else 0
    (hit + (count slot tail))
```

Two semantic changes, both silent: `slot == slot` is a tautology (the
parameter is captured), and the recursion passes the *head's* slot
instead of the parameter. The file elaborates with no diagnostics
(checked against lean4 v4.29.0 with the Thales runtime; exit 0).

Real-world instance: emitting a consensus validator, the produced
`monoAgainst` collapsed its producer-equality test to a tautology and
`produceBlock` signed under the tip's key version instead of the
requested one.

## Suggested fix

Freshen match binders whenever the field name is already bound in
scope (e.g. `slot'`), or alpha-rename the enclosing binding in the
emitted body.
