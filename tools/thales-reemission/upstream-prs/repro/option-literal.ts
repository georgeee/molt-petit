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
