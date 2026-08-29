/** @total */
function pick(a: bigint, b: bigint): bigint {
  const f = a === b ? (a < b ? a : b) : a;
  return f;
}
console.log(pick(3n, 3n) === 3n);
console.log(pick(5n, 2n) === 5n);
