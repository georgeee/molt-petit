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

const seven: bigint = 7n;
const withPrev: C = { kind: 'cons', prev: seven, tail: { kind: 'nil' } };
const noPrev: C = { kind: 'cons', prev: null, tail: { kind: 'nil' } };
console.log(headHasPrev(withPrev));
console.log(headHasPrev(noPrev));
