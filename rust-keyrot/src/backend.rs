//! A small arithmetic/boolean **backend** abstraction so the consensus
//! validator (see [`crate::spec`]) is written ONCE and instantiated two ways:
//!
//! * [`Native`] — `Num = F`, `Bool = bool`: the validator *executes*, returning
//!   the validity bit. This is the function running natively.
//! * [`Circuit`] — `Num` = a plonky2 `Target` (plus its concrete value for hint
//!   generation), `Bool` = a `BoolTarget`: the *same* validator emits the
//!   plonky2 circuit and, because we always prove a concrete chain, records the
//!   witness as it goes.
//!
//! Because both instantiations run the identical generic code, the circuit
//! cannot drift from the native logic — there is a single source of truth.
//!
//! The op set is the minimum the validator needs: field add/sub/mul, Poseidon,
//! equality, a sound bounded less-than, boolean connectives, conditional
//! select, little-endian bit decomposition, and `assert` (require a bool true).

use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::config::Hasher;
use plonky2::plonk::proof::ProofWithPublicInputs;

use crate::types::{C, D, F};

/// Bit width for the bounded comparisons (slots/heights/counts are far smaller).
pub const CMP_BITS: usize = 40;

pub trait Backend {
    type Num: Copy;
    type Bool: Copy;

    // --- value introduction ---
    fn constant(&mut self, x: u64) -> Self::Num;
    /// Lift a witness field element (e.g. a key or signature element).
    fn input(&mut self, v: F) -> Self::Num;
    /// Lift a witness boolean (e.g. a one-hot selector bit).
    fn input_bool(&mut self, v: bool) -> Self::Bool;
    fn bool_const(&mut self, b: bool) -> Self::Bool;

    // --- field arithmetic ---
    fn add(&mut self, a: Self::Num, b: Self::Num) -> Self::Num;
    fn sub(&mut self, a: Self::Num, b: Self::Num) -> Self::Num;
    fn mul(&mut self, a: Self::Num, b: Self::Num) -> Self::Num;
    fn poseidon(&mut self, inputs: &[Self::Num]) -> [Self::Num; 4];

    // --- comparisons / logic ---
    fn is_eq(&mut self, a: Self::Num, b: Self::Num) -> Self::Bool;
    /// `a < b`, sound for values in `[0, 2^CMP_BITS)`.
    fn lt(&mut self, a: Self::Num, b: Self::Num) -> Self::Bool;
    fn and(&mut self, a: Self::Bool, b: Self::Bool) -> Self::Bool;
    fn or(&mut self, a: Self::Bool, b: Self::Bool) -> Self::Bool;
    fn not(&mut self, a: Self::Bool) -> Self::Bool;
    fn select(&mut self, c: Self::Bool, t: Self::Num, f: Self::Num) -> Self::Num;
    fn bool_to_num(&mut self, b: Self::Bool) -> Self::Num;
    fn bits_le(&mut self, x: Self::Num, n_bits: usize) -> Vec<Self::Bool>;

    /// Require `b` to hold. Native: AND into the running verdict. Circuit:
    /// constrain the bool to 1 (so a satisfying witness exists iff it holds).
    fn assert(&mut self, b: Self::Bool);
}

// ---------------------------------------------------------------------------
// Native backend: the validator just runs.
// ---------------------------------------------------------------------------

pub struct Native {
    ok: bool,
}

impl Native {
    pub fn new() -> Self {
        Self { ok: true }
    }
    /// The accumulated verdict after running the validator.
    pub fn verdict(&self) -> bool {
        self.ok
    }
}

impl Default for Native {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for Native {
    type Num = F;
    type Bool = bool;

    fn constant(&mut self, x: u64) -> F {
        F::from_canonical_u64(x)
    }
    fn input(&mut self, v: F) -> F {
        v
    }
    fn input_bool(&mut self, v: bool) -> bool {
        v
    }
    fn bool_const(&mut self, b: bool) -> bool {
        b
    }

    fn add(&mut self, a: F, b: F) -> F {
        a + b
    }
    fn sub(&mut self, a: F, b: F) -> F {
        a - b
    }
    fn mul(&mut self, a: F, b: F) -> F {
        a * b
    }
    fn poseidon(&mut self, inputs: &[F]) -> [F; 4] {
        PoseidonHash::hash_no_pad(inputs).elements
    }

    fn is_eq(&mut self, a: F, b: F) -> bool {
        a == b
    }
    fn lt(&mut self, a: F, b: F) -> bool {
        a.to_canonical_u64() < b.to_canonical_u64()
    }
    fn and(&mut self, a: bool, b: bool) -> bool {
        a && b
    }
    fn or(&mut self, a: bool, b: bool) -> bool {
        a || b
    }
    fn not(&mut self, a: bool) -> bool {
        !a
    }
    fn select(&mut self, c: bool, t: F, f: F) -> F {
        if c {
            t
        } else {
            f
        }
    }
    fn bool_to_num(&mut self, b: bool) -> F {
        if b {
            F::ONE
        } else {
            F::ZERO
        }
    }
    fn bits_le(&mut self, x: F, n_bits: usize) -> Vec<bool> {
        let v = x.to_canonical_u64();
        (0..n_bits).map(|i| (v >> i) & 1 == 1).collect()
    }
    fn assert(&mut self, b: bool) {
        self.ok &= b;
    }
}

// ---------------------------------------------------------------------------
// Circuit backend: the same validator emits the plonky2 circuit.
// ---------------------------------------------------------------------------

/// A circuit number: the wire plus its concrete value (kept so hint-bearing
/// gadgets like `lt` can witness their advice).
#[derive(Clone, Copy)]
pub struct CNum {
    t: Target,
    v: F,
}

#[derive(Clone, Copy)]
pub struct CBool {
    t: BoolTarget,
    v: bool,
}

pub struct Circuit {
    b: CircuitBuilder<F, D>,
    pw: PartialWitness<F>,
}

impl Circuit {
    pub fn new() -> Self {
        Self {
            b: CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config()),
            pw: PartialWitness::new(),
        }
    }

    /// Register numbers as the proof's public inputs.
    pub fn register_public_inputs(&mut self, nums: &[CNum]) {
        let ts: Vec<Target> = nums.iter().map(|n| n.t).collect();
        self.b.register_public_inputs(&ts);
    }

    /// Finish: build the circuit and prove it with the recorded witness.
    pub fn into_data_and_proof(self) -> anyhow::Result<(CircuitData<F, C, D>, ProofWithPublicInputs<F, C, D>)> {
        let data = self.b.build::<C>();
        let proof = data.prove(self.pw)?;
        Ok((data, proof))
    }
}

impl Default for Circuit {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for Circuit {
    type Num = CNum;
    type Bool = CBool;

    fn constant(&mut self, x: u64) -> CNum {
        let v = F::from_canonical_u64(x);
        CNum { t: self.b.constant(v), v }
    }
    fn input(&mut self, v: F) -> CNum {
        let t = self.b.add_virtual_target();
        self.pw.set_target(t, v).expect("set input");
        CNum { t, v }
    }
    fn input_bool(&mut self, v: bool) -> CBool {
        let t = self.b.add_virtual_bool_target_safe();
        self.pw.set_bool_target(t, v).expect("set bool input");
        CBool { t, v }
    }
    fn bool_const(&mut self, b: bool) -> CBool {
        CBool { t: self.b.constant_bool(b), v: b }
    }

    fn add(&mut self, a: CNum, b: CNum) -> CNum {
        CNum { t: self.b.add(a.t, b.t), v: a.v + b.v }
    }
    fn sub(&mut self, a: CNum, b: CNum) -> CNum {
        CNum { t: self.b.sub(a.t, b.t), v: a.v - b.v }
    }
    fn mul(&mut self, a: CNum, b: CNum) -> CNum {
        CNum { t: self.b.mul(a.t, b.t), v: a.v * b.v }
    }
    fn poseidon(&mut self, inputs: &[CNum]) -> [CNum; 4] {
        let ts: Vec<Target> = inputs.iter().map(|n| n.t).collect();
        let vs: Vec<F> = inputs.iter().map(|n| n.v).collect();
        let out_t = self.b.hash_n_to_hash_no_pad::<PoseidonHash>(ts).elements;
        let out_v = PoseidonHash::hash_no_pad(&vs).elements;
        [
            CNum { t: out_t[0], v: out_v[0] },
            CNum { t: out_t[1], v: out_v[1] },
            CNum { t: out_t[2], v: out_v[2] },
            CNum { t: out_t[3], v: out_v[3] },
        ]
    }

    fn is_eq(&mut self, a: CNum, b: CNum) -> CBool {
        CBool { t: self.b.is_equal(a.t, b.t), v: a.v == b.v }
    }
    fn lt(&mut self, a: CNum, b: CNum) -> CBool {
        // Witness the bit, then range-check the branch-selected difference so the
        // witness is forced correct (sound for a, b in [0, 2^CMP_BITS)).
        let v = a.v.to_canonical_u64() < b.v.to_canonical_u64();
        let lt = self.b.add_virtual_bool_target_safe();
        self.pw.set_bool_target(lt, v).expect("set lt bit");
        let one = self.b.one();
        let b_minus_a = self.b.sub(b.t, a.t);
        let b_minus_a_m1 = self.b.sub(b_minus_a, one);
        let a_minus_b = self.b.sub(a.t, b.t);
        let chosen = self.b.select(lt, b_minus_a_m1, a_minus_b);
        self.b.split_le(chosen, CMP_BITS);
        CBool { t: lt, v }
    }
    fn and(&mut self, a: CBool, b: CBool) -> CBool {
        CBool { t: self.b.and(a.t, b.t), v: a.v && b.v }
    }
    fn or(&mut self, a: CBool, b: CBool) -> CBool {
        // or(a,b) = not(and(not a, not b))
        let na = self.b.not(a.t);
        let nb = self.b.not(b.t);
        let nand = self.b.and(na, nb);
        CBool { t: self.b.not(nand), v: a.v || b.v }
    }
    fn not(&mut self, a: CBool) -> CBool {
        CBool { t: self.b.not(a.t), v: !a.v }
    }
    fn select(&mut self, c: CBool, t: CNum, f: CNum) -> CNum {
        CNum {
            t: self.b.select(c.t, t.t, f.t),
            v: if c.v { t.v } else { f.v },
        }
    }
    fn bool_to_num(&mut self, b: CBool) -> CNum {
        CNum { t: b.t.target, v: if b.v { F::ONE } else { F::ZERO } }
    }
    fn bits_le(&mut self, x: CNum, n_bits: usize) -> Vec<CBool> {
        let bits_t = self.b.split_le(x.t, n_bits);
        let v = x.v.to_canonical_u64();
        bits_t
            .into_iter()
            .enumerate()
            .map(|(i, t)| CBool { t, v: (v >> i) & 1 == 1 })
            .collect()
    }
    fn assert(&mut self, b: CBool) {
        let one = self.b.one();
        self.b.connect(b.t.target, one);
    }
}
