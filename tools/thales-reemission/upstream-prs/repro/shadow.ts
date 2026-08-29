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
