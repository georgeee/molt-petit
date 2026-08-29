type L = { kind: 'nil' } | { kind: 'cons'; v: bigint; tail: L };

/** @total */
function tailOf(a: bigint, b: bigint, l: L): L {
  switch (l.kind) {
    case 'nil':
      return l;
    case 'cons': {
      const r = a === b ? l.tail : l.tail;
      return r;
    }
  }
}

/** @total */
function headIsTwo(l: L): boolean {
  switch (l.kind) {
    case 'nil':
      return false;
    case 'cons':
      return l.v === 2n;
  }
}

const two: L = { kind: 'cons', v: 1n, tail: { kind: 'cons', v: 2n, tail: { kind: 'nil' } } };
console.log(headIsTwo(tailOf(0n, 0n, two)));
