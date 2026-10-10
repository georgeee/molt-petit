//! Native (out-of-circuit) ECDSA over NIST P-256 and the big-integer helpers the
//! circuit witness generation builds on. Everything here is plain `BigUint`
//! arithmetic; the circuit gadgets mirror it limb-for-limb.

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::Zero;
use std::sync::OnceLock;

/// Parse a big-endian hex constant (no `0x` prefix).
fn h(s: &str) -> BigUint {
    BigUint::parse_bytes(s.as_bytes(), 16).expect("valid hex")
}

/// The fixed P-256 domain parameters (computed once).
pub struct Params {
    /// Base field prime.
    pub p: BigUint,
    /// Group order.
    pub n: BigUint,
    /// Curve coefficient `a = p − 3`.
    pub a: BigUint,
    /// Curve coefficient `b`.
    pub b: BigUint,
    /// Base point `G`.
    pub g: Point,
}

fn params_cell() -> &'static Params {
    static P: OnceLock<Params> = OnceLock::new();
    P.get_or_init(|| {
        let p = h("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff");
        let n = h("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
        let a = &p - 3u32;
        let b = h("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b");
        let gx = h("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296");
        let gy = h("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5");
        let g = Point::affine(gx, gy);
        Params { p, n, a, b, g }
    })
}

/// P-256 domain parameters.
pub fn params() -> &'static Params {
    params_cell()
}

/// An affine point on P-256, or the point at infinity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Point {
    Infinity,
    Affine { x: BigUint, y: BigUint },
}

impl Point {
    pub fn affine(x: BigUint, y: BigUint) -> Self {
        Point::Affine { x, y }
    }
    pub fn is_infinity(&self) -> bool {
        matches!(self, Point::Infinity)
    }
    pub fn xy(&self) -> Option<(&BigUint, &BigUint)> {
        match self {
            Point::Affine { x, y } => Some((x, y)),
            Point::Infinity => None,
        }
    }
}

// --- modular arithmetic helpers (mod the supplied modulus `m`) ----------------

pub fn add_mod(a: &BigUint, b: &BigUint, m: &BigUint) -> BigUint {
    (a + b) % m
}
pub fn sub_mod(a: &BigUint, b: &BigUint, m: &BigUint) -> BigUint {
    // (a - b) mod m, with a,b already reduced.
    let am = a % m;
    let bm = b % m;
    if am >= bm {
        (&am - &bm) % m
    } else {
        (m + &am - &bm) % m
    }
}
pub fn mul_mod(a: &BigUint, b: &BigUint, m: &BigUint) -> BigUint {
    (a * b) % m
}
/// Modular inverse via Fermat (valid because both `p` and `n` are prime).
pub fn inv_mod(a: &BigUint, m: &BigUint) -> BigUint {
    let exp = m - 2u32;
    a.modpow(&exp, m)
}

// --- EC group law (affine, short Weierstrass `y² = x³ + a·x + b`) --------------

/// Point addition `P + Q` over the base field, handling all exceptional cases
/// (identity, doubling, vertical line → infinity). Reference for the in-circuit
/// (incomplete-formula + edge handling) version.
pub fn point_add(pt: &Point, q: &Point) -> Point {
    let pr = params();
    let p = &pr.p;
    match (pt, q) {
        (Point::Infinity, _) => q.clone(),
        (_, Point::Infinity) => pt.clone(),
        (Point::Affine { x: x1, y: y1 }, Point::Affine { x: x2, y: y2 }) => {
            if x1 == x2 {
                if y1 == y2 && !y1.is_zero() {
                    return point_double(pt);
                }
                // P + (−P) = O (also covers y1 = y2 = 0).
                return Point::Infinity;
            }
            // λ = (y2 − y1) / (x2 − x1)
            let num = sub_mod(y2, y1, p);
            let den = sub_mod(x2, x1, p);
            let lam = mul_mod(&num, &inv_mod(&den, p), p);
            let lam2 = mul_mod(&lam, &lam, p);
            // x3 = λ² − x1 − x2
            let x3 = sub_mod(&sub_mod(&lam2, x1, p), x2, p);
            // y3 = λ·(x1 − x3) − y1
            let y3 = sub_mod(&mul_mod(&lam, &sub_mod(x1, &x3, p), p), y1, p);
            Point::Affine { x: x3, y: y3 }
        }
    }
}

/// Point doubling `2·P`.
pub fn point_double(pt: &Point) -> Point {
    let pr = params();
    let p = &pr.p;
    match pt {
        Point::Infinity => Point::Infinity,
        Point::Affine { x, y } => {
            if y.is_zero() {
                return Point::Infinity;
            }
            // λ = (3x² + a) / (2y)
            let three = BigUint::from(3u32);
            let x2 = mul_mod(x, x, p);
            let num = add_mod(&mul_mod(&three, &x2, p), &pr.a, p);
            let den = add_mod(y, y, p);
            let lam = mul_mod(&num, &inv_mod(&den, p), p);
            let lam2 = mul_mod(&lam, &lam, p);
            // x3 = λ² − 2x
            let x3 = sub_mod(&lam2, &add_mod(x, x, p), p);
            // y3 = λ·(x − x3) − y
            let y3 = sub_mod(&mul_mod(&lam, &sub_mod(x, &x3, p), p), y, p);
            Point::Affine { x: x3, y: y3 }
        }
    }
}

/// Scalar multiplication `k·P` (double-and-add, MSB-first).
pub fn scalar_mul(k: &BigUint, pt: &Point) -> Point {
    let mut acc = Point::Infinity;
    let bits = k.bits();
    for i in (0..bits).rev() {
        acc = point_double(&acc);
        if k.bit(i) {
            acc = point_add(&acc, pt);
        }
    }
    acc
}

/// Simultaneous `u1·G + u2·Q` via Shamir's trick (shared doublings).
pub fn shamir(u1: &BigUint, g: &Point, u2: &BigUint, q: &Point) -> Point {
    let gq = point_add(g, q);
    let mut acc = Point::Infinity;
    let bits = u1.bits().max(u2.bits());
    for i in (0..bits).rev() {
        acc = point_double(&acc);
        let b1 = u1.bit(i);
        let b2 = u2.bit(i);
        let addend = match (b1, b2) {
            (false, false) => None,
            (true, false) => Some(g),
            (false, true) => Some(q),
            (true, true) => Some(&gq),
        };
        if let Some(pt) = addend {
            acc = point_add(&acc, pt);
        }
    }
    acc
}

/// A P-256 public key (a curve point) and an ECDSA signature.
#[derive(Clone, Debug)]
pub struct PublicKey(pub Point);

#[derive(Clone, Debug)]
pub struct Signature {
    pub r: BigUint,
    pub s: BigUint,
}

/// The intermediate ECDSA verification values — exactly the witnesses the
/// circuit re-derives and constrains.
pub struct VerifyTrace {
    pub w: BigUint,
    pub u1: BigUint,
    pub u2: BigUint,
    pub r_point: Point,
    pub rx_mod_n: BigUint,
    pub accept: bool,
}

/// Native ECDSA verification. `z` is the (already reduced into the integers)
/// message hash; callers pass `SHA-256(msg)` truncated to 256 bits.
pub fn verify(pk: &PublicKey, sig: &Signature, z: &BigUint) -> bool {
    verify_trace(pk, sig, z).accept
}

/// Full verification producing the intermediate trace (for circuit witnesses).
pub fn verify_trace(pk: &PublicKey, sig: &Signature, z: &BigUint) -> VerifyTrace {
    let pr = params();
    let n = &pr.n;
    let zero = BigUint::zero();
    let bad = || VerifyTrace {
        w: zero.clone(),
        u1: zero.clone(),
        u2: zero.clone(),
        r_point: Point::Infinity,
        rx_mod_n: zero.clone(),
        accept: false,
    };
    // r, s must be in [1, n−1].
    if sig.r.is_zero() || &sig.r >= n || sig.s.is_zero() || &sig.s >= n {
        return bad();
    }
    let z = z % n;
    let w = inv_mod(&sig.s, n);
    let u1 = mul_mod(&z, &w, n);
    let u2 = mul_mod(&sig.r, &w, n);
    let r_point = shamir(&u1, &pr.g, &u2, &pk.0);
    let rx = match r_point.xy() {
        Some((x, _)) => x.clone(),
        None => return bad(),
    };
    let rx_mod_n = &rx % n;
    let accept = rx_mod_n == sig.r;
    VerifyTrace { w, u1, u2, r_point, rx_mod_n, accept }
}

/// Whether a point satisfies the curve equation (sanity check for keys).
pub fn on_curve(pt: &Point) -> bool {
    let pr = params();
    let p = &pr.p;
    match pt {
        Point::Infinity => true,
        Point::Affine { x, y } => {
            let lhs = mul_mod(y, y, p);
            let x3 = mul_mod(&mul_mod(x, x, p), x, p);
            let rhs = add_mod(&add_mod(&x3, &mul_mod(&pr.a, x, p), p), &pr.b, p);
            lhs == rhs
        }
    }
}

/// Greatest-common-divisor helper exposed for tests.
pub fn gcd(a: &BigUint, b: &BigUint) -> BigUint {
    a.gcd(b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Num;
    use p256::ecdsa::signature::{Signer, Verifier};
    use p256::ecdsa::{Signature as P256Sig, SigningKey, VerifyingKey};
    use p256::elliptic_curve::sec1::ToEncodedPoint;
    use rand_core::OsRng;

    fn big(bytes: &[u8]) -> BigUint {
        BigUint::from_bytes_be(bytes)
    }

    #[test]
    fn base_point_on_curve() {
        assert!(on_curve(&params().g), "G must satisfy the curve equation");
        assert!(!params().n.is_zero());
    }

    #[test]
    fn scalar_mul_matches_p256_crate() {
        // k·G for a fixed scalar, compared against the RustCrypto p256 crate.
        let k_hex = "0123456789abcdeffedcba98765432100f1e2d3c4b5a69788796a5b4c3d2e1f0";
        let k = BigUint::from_str_radix(k_hex, 16).unwrap();
        let mine = scalar_mul(&k, &params().g);

        use p256::elliptic_curve::PrimeField;
        let scalar =
            p256::Scalar::from_repr(p256::FieldBytes::from(to_fixed_32(&k))).unwrap();
        let pt = (p256::ProjectivePoint::GENERATOR * scalar).to_affine();
        let enc = pt.to_encoded_point(false);
        let (rx, ry) = (big(enc.x().unwrap()), big(enc.y().unwrap()));
        assert_eq!(mine, Point::affine(rx, ry), "k·G must match p256 crate");
    }

    fn to_fixed_32(x: &BigUint) -> [u8; 32] {
        let v = x.to_bytes_be();
        let mut out = [0u8; 32];
        out[32 - v.len()..].copy_from_slice(&v);
        out
    }

    #[test]
    fn verify_real_p256_signature() {
        // Generate a key + signature with the trusted crate, then verify with OUR
        // native verifier (and confirm the crate agrees).
        let signing = SigningKey::random(&mut OsRng);
        let verifying = VerifyingKey::from(&signing);
        let msg = b"passkey assertion: molt-petit es256";
        let sig: P256Sig = signing.sign(msg);
        assert!(verifying.verify(msg, &sig).is_ok(), "crate self-check");

        // z = SHA-256(msg) as an integer (computed by the crate's hasher path:
        // recompute via sha2 through the prehash the crate uses).
        let z = sha256_int(msg);

        let enc = verifying.to_encoded_point(false);
        let pk = PublicKey(Point::affine(
            big(enc.x().unwrap()),
            big(enc.y().unwrap()),
        ));
        let r = big(&sig.r().to_bytes());
        let s = big(&sig.s().to_bytes());
        let mine = verify(&pk, &Signature { r: r.clone(), s: s.clone() }, &z);
        assert!(mine, "our native verifier must accept a real P-256 signature");

        // Forgery: flip a bit of s -> reject.
        let bad_s = (&s + 1u32) % &params().n;
        assert!(!verify(&pk, &Signature { r, s: bad_s }, &z), "tampered s must reject");
    }

    /// SHA-256 of a message as a big integer (matches ECDSA's z derivation).
    fn sha256_int(msg: &[u8]) -> BigUint {
        use sha2::{Digest, Sha256};
        let d = Sha256::digest(msg);
        BigUint::from_bytes_be(&d)
    }
}
