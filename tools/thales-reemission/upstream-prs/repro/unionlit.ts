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
