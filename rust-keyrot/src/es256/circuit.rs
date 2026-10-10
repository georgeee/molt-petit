//! In-circuit ES256 (ECDSA-P256) verification in **plonky2** (Goldilocks):
//! foreign-field bignum arithmetic, affine EC ops, Shamir scalar multiplication,
//! and the full ECDSA verify relation. The plonky2 counterpart of
//! `rust-keyrot-p3/src/p256/{mod_circuit,ec_circuit}.rs`.
//!
//! ## Limb / field sizing (soundness)
//! Goldilocks' prime is `P ≈ 2^64` (`P/2 ≈ 2^63`). With **B=26 bits, K=10 limbs**
//! (`260 ≥ 256`):
//!   * a product column `Σ aᵢ·bⱼ` (`≤ K` terms `< 2^{2B}`) is `< 10·2^{52} =
//!     2^{55.3} < P/2`, so it is representable without wraparound and within the
//!     signed range;
//!   * the signed inter-column carry is `< 2^{31}`, and `carry·2^B < 2^{57} <
//!     P/2`, so the per-column carry constraint `diff = carry·2^B` is injective
//!     modulo `P` (a wrong carry cannot alias).
//!
//! plonky2 needs no `WitnessChecks`-style materialization (unlike p3-circuit):
//! a virtual target is used directly, and witness values are recorded as we build
//! (build and prove are coupled — one circuit per signature, as the structure is
//! value-independent so its `CircuitData` is reusable for aggregation).

use anyhow::Result;
use num_bigint::BigUint;
use num_traits::Zero;
use plonky2::field::types::Field;
#[cfg(test)]
use plonky2::field::types::PrimeField64;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::proof::ProofWithPublicInputs;

use crate::es256::native::{self, Point};
use crate::types::{C, D, F};

/// Bits per limb.
pub const B: usize = 26;
/// Number of limbs (`K·B = 260 ≥ 256`).
pub const K: usize = 10;
/// Product columns in a `K×K` convolution.
pub const COLS: usize = 2 * K - 1;
const LIMB_MASK: u64 = (1 << B) - 1;
/// Signed-carry magnitude bound for `mulmod` (honest carries `< 2^{31}`).
const CARRY_BITS: usize = 31;

/// Every witnessed value in this circuit is non-negative (limbs, biased carries,
/// quotients, remainders, bits), so a plain `u64 → F` map suffices; the only
/// signed quantities are the `i128` carry computations, which never reach a
/// witness target directly.
fn fe(x: u64) -> F {
    F::from_canonical_u64(x)
}

/// Split a non-negative integer into `K` base-`2^B` limbs (little-endian).
pub fn to_limbs(x: &BigUint) -> Vec<u64> {
    let mut v = x.clone();
    let mask = BigUint::from(LIMB_MASK);
    let mut out = Vec::with_capacity(K);
    for _ in 0..K {
        let limb: u64 = (&v & &mask).try_into().unwrap_or(0);
        out.push(limb);
        v >>= B;
    }
    debug_assert!(v.is_zero(), "value exceeds K·B bits");
    out
}

/// An emulated field element: `K` limb targets plus its concrete value.
#[derive(Clone)]
pub struct Big {
    pub limbs: Vec<Target>,
    pub val: BigUint,
}

/// Records witness assignments and public-input targets while a circuit is built
/// (build/prove coupled). All recorded targets are set at prove time.
pub struct Wit {
    assign: Vec<(Target, F)>,
    public: Vec<Target>,
}

impl Wit {
    pub fn new() -> Self {
        Self { assign: Vec::new(), public: Vec::new() }
    }
    /// A fresh witnessed target carrying `v`.
    fn priv_t(&mut self, b: &mut CircuitBuilder<F, D>, v: F) -> Target {
        let t = b.add_virtual_target();
        self.assign.push((t, v));
        t
    }
    /// A fresh witnessed boolean target carrying `v` (asserted boolean).
    fn priv_bool(&mut self, b: &mut CircuitBuilder<F, D>, v: bool) -> BoolTarget {
        let bt = b.add_virtual_bool_target_unsafe();
        b.assert_bool(bt);
        self.assign.push((bt.target, if v { F::ONE } else { F::ZERO }));
        bt
    }
}

impl Default for Wit {
    fn default() -> Self {
        Self::new()
    }
}

/// Range-check a target to `[0, 2^nbits)`.
fn range_check(b: &mut CircuitBuilder<F, D>, t: Target, nbits: usize) {
    b.range_check(t, nbits);
}

/// Witness a private big value: `K` range-checked limbs.
pub fn witness_big(b: &mut CircuitBuilder<F, D>, w: &mut Wit, val: &BigUint) -> Big {
    let limbs: Vec<Target> = to_limbs(val)
        .into_iter()
        .map(|lv| {
            let t = w.priv_t(b, fe(lv));
            range_check(b, t, B);
            t
        })
        .collect();
    Big { limbs, val: val.clone() }
}

/// A public-input big value: `K` range-checked public-input limbs.
pub fn public_big(b: &mut CircuitBuilder<F, D>, w: &mut Wit, val: &BigUint) -> Big {
    let limbs: Vec<Target> = to_limbs(val)
        .into_iter()
        .map(|lv| {
            let t = w.priv_t(b, fe(lv));
            w.public.push(t);
            range_check(b, t, B);
            t
        })
        .collect();
    Big { limbs, val: val.clone() }
}

/// A constant big value: `K` constant limbs.
pub fn const_big(b: &mut CircuitBuilder<F, D>, val: &BigUint) -> Big {
    let limbs = to_limbs(val).into_iter().map(|lv| b.constant(fe(lv))).collect();
    Big { limbs, val: val.clone() }
}

fn const_limbs(b: &mut CircuitBuilder<F, D>, val: &BigUint) -> Vec<Target> {
    to_limbs(val).into_iter().map(|lv| b.constant(fe(lv))).collect()
}

/// Assert two canonical `Big`s equal (limb-wise).
pub fn assert_eq_big(b: &mut CircuitBuilder<F, D>, x: &Big, y: &Big) {
    for i in 0..K {
        b.connect(x.limbs[i], y.limbs[i]);
    }
}

/// Convolution columns `Σ_{i+j=c} a_i·b_j`.
fn convolution(b: &mut CircuitBuilder<F, D>, a: &[Target], bb: &[Target]) -> Vec<Target> {
    let zero = b.zero();
    let mut cols = vec![zero; COLS];
    for i in 0..K {
        for j in 0..K {
            cols[i + j] = b.mul_add(a[i], bb[j], cols[i + j]);
        }
    }
    cols
}

fn int_convolution(a: &[u64], b: &[u64]) -> Vec<i128> {
    let mut cols = vec![0i128; COLS];
    for i in 0..K {
        for j in 0..K {
            cols[i + j] += a[i] as i128 * b[j] as i128;
        }
    }
    cols
}

/// Assert `Σ lhs[c]·2^{Bc} = Σ rhs[c]·2^{Bc}` by carry-propagating `lhs − rhs` to
/// zero; `carry_bits` bounds the signed inter-column carry.
fn assert_cols_equal(
    b: &mut CircuitBuilder<F, D>,
    w: &mut Wit,
    lhs: &[Target],
    rhs: &[Target],
    int_lhs: &[i128],
    int_rhs: &[i128],
    carry_bits: usize,
) {
    let ncols = lhs.len();
    debug_assert_eq!(ncols, rhs.len());
    let offset = 1i128 << carry_bits;
    let offset_c = b.constant(fe(offset as u64));
    let limb_base = b.constant(fe(1u64 << B));
    let zero = b.zero();
    let mut carry_t = zero;
    let mut carry_int: i128 = 0;
    let two_b = 1i128 << B;
    for c in 0..ncols {
        let t = b.add(lhs[c], carry_t);
        let diff = b.sub(t, rhs[c]);
        let int_diff = int_lhs[c] + carry_int - int_rhs[c];
        if c + 1 < ncols {
            debug_assert_eq!(int_diff & (two_b - 1), 0, "column not divisible by 2^B");
            let newcarry = int_diff / two_b;
            let shifted = newcarry + offset;
            debug_assert!(
                shifted >= 0 && shifted < (1i128 << (carry_bits + 1)),
                "carry {newcarry} out of ±2^{carry_bits}"
            );
            let shifted_t = w.priv_t(b, fe(shifted as u64));
            range_check(b, shifted_t, carry_bits + 1);
            let nc_t = b.sub(shifted_t, offset_c);
            let nc_scaled = b.mul(nc_t, limb_base);
            b.connect(diff, nc_scaled);
            carry_t = nc_t;
            carry_int = newcarry;
        } else {
            debug_assert_eq!(int_diff, 0, "final carry nonzero");
            b.connect(diff, zero);
        }
    }
}

/// `r < modulus` for a canonical `Big` `r` (verify `r + d = m − 1` with `d ≥ 0`).
fn assert_lt_modulus(b: &mut CircuitBuilder<F, D>, w: &mut Wit, r: &Big, m: &BigUint) {
    let m_minus_1 = m - 1u32;
    let m_l = to_limbs(&m_minus_1);
    let d_val = &m_minus_1 - &r.val;
    let d_l = to_limbs(&d_val);
    let r_l = to_limbs(&r.val);
    let mut lhs = Vec::with_capacity(K);
    let mut rhs = Vec::with_capacity(K);
    let mut int_lhs = Vec::with_capacity(K);
    let mut int_rhs = Vec::with_capacity(K);
    for c in 0..K {
        let d_t = w.priv_t(b, fe(d_l[c]));
        range_check(b, d_t, B);
        lhs.push(b.add(r.limbs[c], d_t));
        rhs.push(b.constant(fe(m_l[c])));
        int_lhs.push(r_l[c] as i128 + d_l[c] as i128);
        int_rhs.push(m_l[c] as i128);
    }
    assert_cols_equal(b, w, &lhs, &rhs, &int_lhs, &int_rhs, 2);
}

/// `R = A·B mod M`. Witnesses quotient + remainder, range-checks both, asserts
/// `R < M`, and enforces `A·B = Q·M + R`.
pub fn mulmod(b: &mut CircuitBuilder<F, D>, w: &mut Wit, a: &Big, bb: &Big, m: &BigUint) -> Big {
    let prod = &a.val * &bb.val;
    let q_val = &prod / m;
    let r_val = &prod % m;
    let q = witness_big(b, w, &q_val);
    let r = witness_big(b, w, &r_val);
    assert_lt_modulus(b, w, &r, m);

    let m_limbs = const_limbs(b, m);
    let ab = convolution(b, &a.limbs, &bb.limbs);
    let qm = convolution(b, &q.limbs, &m_limbs);
    let mut rhs = qm.clone();
    for c in 0..K {
        rhs[c] = b.add(qm[c], r.limbs[c]);
    }
    let int_ab = int_convolution(&to_limbs(&a.val), &to_limbs(&bb.val));
    let mut int_rhs = int_convolution(&to_limbs(&q_val), &to_limbs(m));
    let r_l = to_limbs(&r_val);
    for c in 0..K {
        int_rhs[c] += r_l[c] as i128;
    }
    assert_cols_equal(b, w, &ab, &rhs, &int_ab, &int_rhs, CARRY_BITS);
    r
}

/// `R = (A + B) mod M`, `A,B` canonical.
pub fn addmod(b: &mut CircuitBuilder<F, D>, w: &mut Wit, a: &Big, bb: &Big, m: &BigUint) -> Big {
    let sum = &a.val + &bb.val;
    let carry = if &sum >= m { 1u64 } else { 0u64 };
    let r_val = &sum - BigUint::from(carry) * m;
    let r = witness_big(b, w, &r_val);
    assert_lt_modulus(b, w, &r, m);
    let co = w.priv_bool(b, carry == 1);
    let m_limbs = const_limbs(b, m);
    let (a_l, b_l, m_l, r_l) = (to_limbs(&a.val), to_limbs(&bb.val), to_limbs(m), to_limbs(&r_val));
    let mut lhs = Vec::with_capacity(K);
    let mut rhs = Vec::with_capacity(K);
    let mut il = Vec::with_capacity(K);
    let mut ir = Vec::with_capacity(K);
    for c in 0..K {
        lhs.push(b.add(a.limbs[c], bb.limbs[c]));
        let com = b.mul(co.target, m_limbs[c]);
        rhs.push(b.add(com, r.limbs[c]));
        il.push(a_l[c] as i128 + b_l[c] as i128);
        ir.push(carry as i128 * m_l[c] as i128 + r_l[c] as i128);
    }
    assert_cols_equal(b, w, &lhs, &rhs, &il, &ir, 3);
    r
}

/// `R = (A − B) mod M`, `A,B` canonical (`A + borrow·M = B + R`).
pub fn submod(b: &mut CircuitBuilder<F, D>, w: &mut Wit, a: &Big, bb: &Big, m: &BigUint) -> Big {
    let borrow = if a.val >= bb.val { 0u64 } else { 1u64 };
    let r_val = (&a.val + BigUint::from(borrow) * m) - &bb.val;
    let r = witness_big(b, w, &r_val);
    assert_lt_modulus(b, w, &r, m);
    let bw = w.priv_bool(b, borrow == 1);
    let m_limbs = const_limbs(b, m);
    let (a_l, b_l, m_l, r_l) = (to_limbs(&a.val), to_limbs(&bb.val), to_limbs(m), to_limbs(&r_val));
    let mut lhs = Vec::with_capacity(K);
    let mut rhs = Vec::with_capacity(K);
    let mut il = Vec::with_capacity(K);
    let mut ir = Vec::with_capacity(K);
    for c in 0..K {
        let bm = b.mul(bw.target, m_limbs[c]);
        lhs.push(b.add(a.limbs[c], bm));
        rhs.push(b.add(bb.limbs[c], r.limbs[c]));
        il.push(a_l[c] as i128 + borrow as i128 * m_l[c] as i128);
        ir.push(b_l[c] as i128 + r_l[c] as i128);
    }
    assert_cols_equal(b, w, &lhs, &rhs, &il, &ir, 3);
    r
}

/// Reduce `a` (known `< 2·m`) modulo `m`: witnesses a quotient bit and `a = q·m + r`.
pub fn mod_reduce_le2(b: &mut CircuitBuilder<F, D>, w: &mut Wit, a: &Big, m: &BigUint) -> Big {
    debug_assert!(a.val < BigUint::from(2u32) * m);
    let q = if &a.val >= m { 1u64 } else { 0u64 };
    let r_val = &a.val - BigUint::from(q) * m;
    let r = witness_big(b, w, &r_val);
    assert_lt_modulus(b, w, &r, m);
    let qw = w.priv_bool(b, q == 1);
    let m_limbs = const_limbs(b, m);
    let (a_l, m_l, r_l) = (to_limbs(&a.val), to_limbs(m), to_limbs(&r_val));
    let mut rhs = Vec::with_capacity(K);
    let mut il = Vec::with_capacity(K);
    let mut ir = Vec::with_capacity(K);
    for c in 0..K {
        let qm = b.mul(qw.target, m_limbs[c]);
        rhs.push(b.add(qm, r.limbs[c]));
        il.push(a_l[c] as i128);
        ir.push(q as i128 * m_l[c] as i128 + r_l[c] as i128);
    }
    assert_cols_equal(b, w, &a.limbs, &rhs, &il, &ir, 3);
    r
}

// --- elliptic-curve layer -----------------------------------------------------

/// An affine point with an infinity flag (sentinel `(0,1)` when at infinity).
#[derive(Clone)]
pub struct EcPoint {
    pub x: Big,
    pub y: Big,
    pub inf: BoolTarget,
    pub inf_val: bool,
}

fn p_mod() -> &'static BigUint {
    &native::params().p
}
fn n_mod() -> &'static BigUint {
    &native::params().n
}

fn const_point(b: &mut CircuitBuilder<F, D>, pt: &Point) -> EcPoint {
    match pt {
        Point::Infinity => EcPoint {
            x: const_big(b, &BigUint::from(0u32)),
            y: const_big(b, &BigUint::from(1u32)),
            inf: BoolTarget::new_unsafe(b.one()),
            inf_val: true,
        },
        Point::Affine { x, y } => EcPoint {
            x: const_big(b, x),
            y: const_big(b, y),
            inf: BoolTarget::new_unsafe(b.zero()),
            inf_val: false,
        },
    }
}

fn public_point(b: &mut CircuitBuilder<F, D>, w: &mut Wit, pt: &Point) -> EcPoint {
    let (x, y) = pt.xy().expect("public key finite");
    EcPoint {
        x: public_big(b, w, x),
        y: public_big(b, w, y),
        inf: BoolTarget::new_unsafe(b.zero()),
        inf_val: false,
    }
}

fn select_big(b: &mut CircuitBuilder<F, D>, sel: BoolTarget, sv: bool, a: &Big, q: &Big) -> Big {
    let limbs = (0..K).map(|c| b.select(sel, a.limbs[c], q.limbs[c])).collect();
    Big { limbs, val: if sv { a.val.clone() } else { q.val.clone() } }
}

fn select_point(b: &mut CircuitBuilder<F, D>, sel: BoolTarget, sv: bool, p: &EcPoint, q: &EcPoint) -> EcPoint {
    let inf_t = b.select(sel, p.inf.target, q.inf.target);
    EcPoint {
        x: select_big(b, sel, sv, &p.x, &q.x),
        y: select_big(b, sel, sv, &p.y, &q.y),
        inf: BoolTarget::new_unsafe(inf_t),
        inf_val: if sv { p.inf_val } else { q.inf_val },
    }
}

/// Point doubling `2·acc` (handles `acc = ∞`).
pub fn point_double(b: &mut CircuitBuilder<F, D>, w: &mut Wit, acc: &EcPoint) -> EcPoint {
    let p = p_mod().clone();
    let (xu, yu) = (&acc.x, &acc.y);
    let x2 = mulmod(b, w, xu, xu, &p);
    let two_x2 = addmod(b, w, &x2, &x2, &p);
    let three_x2 = addmod(b, w, &two_x2, &x2, &p);
    let a = const_big(b, &native::params().a);
    let num = addmod(b, w, &three_x2, &a, &p);
    let den = addmod(b, w, yu, yu, &p);
    let lam_val = native::mul_mod(&num.val, &native::inv_mod(&den.val, &p), &p);
    let lam = witness_big(b, w, &lam_val);
    let check = mulmod(b, w, &lam, &den, &p);
    assert_eq_big(b, &check, &num);
    let lam2 = mulmod(b, w, &lam, &lam, &p);
    let two_x = addmod(b, w, xu, xu, &p);
    let x3 = submod(b, w, &lam2, &two_x, &p);
    let x_m_x3 = submod(b, w, xu, &x3, &p);
    let l = mulmod(b, w, &lam, &x_m_x3, &p);
    let y3 = submod(b, w, &l, yu, &p);
    let sent0 = const_big(b, &BigUint::from(0u32));
    let sent1 = const_big(b, &BigUint::from(1u32));
    let rx = select_big(b, acc.inf, acc.inf_val, &sent0, &x3);
    let ry = select_big(b, acc.inf, acc.inf_val, &sent1, &y3);
    EcPoint { x: rx, y: ry, inf: acc.inf, inf_val: acc.inf_val }
}

/// Incomplete affine addition `acc + addend` (`addend` finite); `acc = ∞` → addend.
pub fn point_add(b: &mut CircuitBuilder<F, D>, w: &mut Wit, acc: &EcPoint, addend: &EcPoint) -> EcPoint {
    let p = p_mod().clone();
    let (x1, y1, x2, y2) = (&acc.x, &acc.y, &addend.x, &addend.y);
    let num = submod(b, w, y2, y1, &p);
    let den = submod(b, w, x2, x1, &p);
    let lam_val = native::mul_mod(&num.val, &native::inv_mod(&den.val, &p), &p);
    let lam = witness_big(b, w, &lam_val);
    let check = mulmod(b, w, &lam, &den, &p);
    assert_eq_big(b, &check, &num);
    let lam2 = mulmod(b, w, &lam, &lam, &p);
    let x3a = submod(b, w, &lam2, x1, &p);
    let x3 = submod(b, w, &x3a, x2, &p);
    let x1_m_x3 = submod(b, w, x1, &x3, &p);
    let l = mulmod(b, w, &lam, &x1_m_x3, &p);
    let y3 = submod(b, w, &l, y1, &p);
    let rx = select_big(b, acc.inf, acc.inf_val, &addend.x, &x3);
    let ry = select_big(b, acc.inf, acc.inf_val, &addend.y, &y3);
    // result is finite (acc=∞ → addend finite; else affine sum of distinct pts).
    let zero = b.zero();
    let r_inf = b.select(acc.inf, addend.inf.target, zero);
    EcPoint {
        x: rx,
        y: ry,
        inf: BoolTarget::new_unsafe(r_inf),
        inf_val: if acc.inf_val { addend.inf_val } else { false },
    }
}

/// Little-endian bit-targets of a `Big` scalar (`K·B` bits, tied to its limbs).
fn scalar_bits(b: &mut CircuitBuilder<F, D>, big: &Big) -> Vec<BoolTarget> {
    let mut bits = Vec::with_capacity(K * B);
    for c in 0..K {
        bits.extend(b.split_le(big.limbs[c], B));
    }
    bits
}

/// `u1·G + u2·Q` via Shamir's trick over `nbits` doublings (MSB-first).
pub fn shamir(
    b: &mut CircuitBuilder<F, D>,
    w: &mut Wit,
    g: &EcPoint,
    q: &EcPoint,
    gq: &EcPoint,
    u1: &Big,
    u2: &Big,
    nbits: usize,
) -> EcPoint {
    let u1_bits = scalar_bits(b, u1);
    let u2_bits = scalar_bits(b, u2);
    let u1_int = &u1.val;
    let u2_int = &u2.val;
    let mut acc = EcPoint {
        x: const_big(b, &BigUint::from(0u32)),
        y: const_big(b, &BigUint::from(1u32)),
        inf: BoolTarget::new_unsafe(b.one()),
        inf_val: true,
    };
    for i in (0..nbits).rev() {
        acc = point_double(b, w, &acc);
        let (b1, b2) = (u1_bits[i], u2_bits[i]);
        let b1v = u1_int.bit(i as u64);
        let b2v = u2_int.bit(i as u64);
        // addend = b2 ? (b1 ? G+Q : Q) : G  (G is the b1=0,b2=0 don't-care)
        let inner = select_point(b, b1, b1v, gq, q);
        let addend = select_point(b, b2, b2v, &inner, g);
        let do_add = b.or(b1, b2);
        let do_add_val = b1v || b2v;
        let cand = point_add(b, w, &acc, &addend);
        acc = select_point(b, do_add, do_add_val, &cand, &acc);
    }
    acc
}

/// Build the full ES256 verification circuit for `(Q, r, s, z)` and record the
/// witness; satisfiable iff the signature is valid. `(Q,r,s,z)` are public inputs.
pub fn build_verify_circuit(
    pk: &native::PublicKey,
    sig: &native::Signature,
    z: &BigUint,
) -> (CircuitBuilder<F, D>, Wit, EcPoint) {
    let n = n_mod().clone();
    let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    let mut w = Wit::new();

    let q_pt = public_point(&mut b, &mut w, &pk.0);
    let r_pub = public_big(&mut b, &mut w, &sig.r);
    let s_pub = public_big(&mut b, &mut w, &sig.s);
    let z_red = z % &n;
    let z_pub = public_big(&mut b, &mut w, &z_red);

    // w = s⁻¹ mod n  (constraint s·w ≡ 1).
    let w_val = native::inv_mod(&sig.s, &n);
    let w_big = witness_big(&mut b, &mut w, &w_val);
    let sw = mulmod(&mut b, &mut w, &s_pub, &w_big, &n);
    let one_big = const_big(&mut b, &BigUint::from(1u32));
    assert_eq_big(&mut b, &sw, &one_big);

    // u1 = z·w, u2 = r·w  (mod n).
    let u1 = mulmod(&mut b, &mut w, &z_pub, &w_big, &n);
    let u2 = mulmod(&mut b, &mut w, &r_pub, &w_big, &n);

    // R = u1·G + u2·Q.
    let g_pt = const_point(&mut b, &native::params().g);
    let gq_native = native::point_add(&native::params().g, &pk.0);
    let gq_pt = const_point(&mut b, &gq_native);
    let r_point = shamir(&mut b, &mut w, &g_pt, &q_pt, &gq_pt, &u1, &u2, 256);

    // rx mod n == r (rx < p < 2n ⇒ quotient ∈ {0,1}).
    let rx_modn = mod_reduce_le2(&mut b, &mut w, &r_point.x, &n);
    assert_eq_big(&mut b, &rx_modn, &r_pub);

    b.register_public_inputs(&w.public);
    (b, w, r_point)
}

/// Build + prove one ES256 verification. Returns the circuit data (reusable for
/// aggregation — the structure is signature-independent) and the proof.
pub fn build_and_prove(
    pk: &native::PublicKey,
    sig: &native::Signature,
    z: &BigUint,
) -> Result<(CircuitData<F, C, D>, ProofWithPublicInputs<F, C, D>)> {
    let (b, w, _r) = build_verify_circuit(pk, sig, z);
    let data = b.build::<C>();
    let mut pw = PartialWitness::new();
    for (t, v) in &w.assign {
        pw.set_target(*t, *v)?;
    }
    let proof = data.prove(pw)?;
    Ok((data, proof))
}

/// A fixed, reproducible P-256 key + valid ES256 signature (for benches/tests).
pub fn demo_signature() -> (native::PublicKey, native::Signature, BigUint) {
    use num_traits::Num;
    let n = n_mod();
    let d = BigUint::from_str_radix(
        "519b423d715f8b581f4fa8ee59f4771a5b44c8130b4e3eacca54a56dda72b464",
        16,
    )
    .unwrap()
        % n;
    let q = native::PublicKey(native::scalar_mul(&d, &native::params().g));
    let z = BigUint::from_str_radix(
        "44acf6b7e36c1342c2c5897204fe09504e1e2efb1a900377dbc4e7a6a133ec56",
        16,
    )
    .unwrap()
        % n;
    let k = BigUint::from_str_radix(
        "94a1bbb14b906a61a280f245f9e93c7f3b4a6247824f5d33b9670787642a68de",
        16,
    )
    .unwrap()
        % n;
    let kg = native::scalar_mul(&k, &native::params().g);
    let r = kg.xy().unwrap().0 % n;
    let s = native::mul_mod(
        &native::inv_mod(&k, n),
        &native::add_mod(&z, &native::mul_mod(&r, &d, n), n),
        n,
    );
    let sig = native::Signature { r, s };
    debug_assert!(native::verify(&q, &sig, &z));
    (q, sig, z)
}

#[cfg(test)]
mod tests {
    use super::*;
    use plonky2::iop::witness::PartialWitness;

    /// Run the partial witness through the circuit (no proving) and read a target.
    fn eval(
        build: impl FnOnce(&mut CircuitBuilder<F, D>, &mut Wit) -> Vec<Target>,
    ) -> Vec<u64> {
        let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
        let mut w = Wit::new();
        let probes = build(&mut b, &mut w);
        // Make probes public so we can read them out of the proof's public inputs.
        let base = w.public.len();
        b.register_public_inputs(&probes);
        let data = b.build::<C>();
        let mut pw = PartialWitness::new();
        for (t, v) in &w.assign {
            pw.set_target(*t, *v).unwrap();
        }
        let proof = data.prove(pw).expect("prove eval");
        // public_inputs = [w.public..., probes...]
        proof.public_inputs[base..base + probes.len()]
            .iter()
            .map(|f| f.to_canonical_u64())
            .collect()
    }

    fn big_from_limbs(vals: &[u64]) -> BigUint {
        let mut acc = BigUint::from(0u32);
        for (i, &l) in vals.iter().enumerate() {
            acc += BigUint::from(l) << (B * i);
        }
        acc
    }

    #[test]
    fn mulmod_matches_native() {
        let p = p_mod();
        let a = &demo_signature().1.r % p;
        let bb = BigUint::from(123456789u64);
        let expect = (&a * &bb) % p;
        let got = eval(|b, w| {
            let ae = witness_big(b, w, &a);
            let be = witness_big(b, w, &bb);
            mulmod(b, w, &ae, &be, p).limbs
        });
        assert_eq!(big_from_limbs(&got), expect);
    }

    #[test]
    fn ec_double_add_matches_native() {
        let g = &native::params().g;
        let p2 = native::point_double(g);
        let p3 = native::point_add(&p2, g);
        let got = eval(|b, w| {
            let gp = const_point(b, g);
            let d = point_double(b, w, &gp);
            let a = point_add(b, w, &d, &gp);
            let mut v = a.x.limbs.clone();
            v.extend(a.y.limbs.clone());
            v
        });
        assert_eq!(big_from_limbs(&got[0..K]), *p3.xy().unwrap().0, "3G.x");
        assert_eq!(big_from_limbs(&got[K..2 * K]), *p3.xy().unwrap().1, "3G.y");
        let _ = p2;
    }

    #[test]
    fn shamir_matches_native_small() {
        let g = &native::params().g;
        let q = native::scalar_mul(&BigUint::from(7u32), g);
        let u1 = BigUint::from(19u32);
        let u2 = BigUint::from(5u32);
        let expect = native::shamir(&u1, g, &u2, &q);
        let got = eval(|b, w| {
            let gp = const_point(b, g);
            let qp = const_point(b, &q);
            let gqp = const_point(b, &native::point_add(g, &q));
            let u1b = witness_big(b, w, &u1);
            let u2b = witness_big(b, w, &u2);
            shamir(b, w, &gp, &qp, &gqp, &u1b, &u2b, 8).x.limbs
        });
        assert_eq!(big_from_limbs(&got), *expect.xy().unwrap().0, "shamir small");
    }

    /// Heavy: one genuine ES256 signature proves; report circuit size + timing.
    #[test]
    #[ignore = "heavy (~minutes); run with --ignored --nocapture"]
    fn es256_verify_proves() {
        let (q, sig, z) = demo_signature();
        let t = std::time::Instant::now();
        let (data, proof) = build_and_prove(&q, &sig, &z).expect("prove");
        let dt = t.elapsed();
        data.verify(proof.clone()).expect("verify");
        println!(
            "[ES256-plonky2] one verification: degree 2^{}, build+PROVE {:.1} s, proof {} KB",
            data.common.degree_bits(),
            dt.as_secs_f64(),
            proof.to_bytes().len() / 1024
        );
    }

    /// Heavy: a forged signature (tampered r) has no satisfying witness.
    #[test]
    #[ignore = "heavy (~minutes); run with --ignored"]
    fn es256_forgery_unprovable() {
        let (q, sig, z) = demo_signature();
        let forged = native::Signature { r: (&sig.r + 1u32) % n_mod(), s: sig.s.clone() };
        assert!(!native::verify(&q, &forged, &z));
        // A forged signature has no satisfying witness: the final `rx mod n == r`
        // copy constraint conflicts, which plonky2 surfaces as a prove-time error
        // or a witness-generation panic — either counts as "unprovable".
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            build_and_prove(&q, &forged, &z).is_ok()
        }));
        assert!(matches!(res, Ok(false) | Err(_)), "a forged ES256 signature must not be provable");
    }
}
