//! Run the **verified** `molt_petit::valid_chain_be` as a plonky2 circuit.
//!
//! `molt_petit::valid_chain_be` is the backend-generic consensus validator in
//! the verified crate — the one Lean proves sound (`Rust.valid_chain_be_validChain`).
//! Here we instantiate `molt_petit::Backend` with a plonky2 circuit, so the
//! circuit literally executes that verified function: the certificate's
//! structural-validity + window-density check is the proven code, not a
//! re-transcription.
//!
//! `molt_petit::Backend`'s methods take `&self` (the native `U64Backend` is
//! stateless), so the circuit builder lives behind `RefCell` interior
//! mutability. Each `Num`/`Bool` carries its concrete value alongside the wire
//! so the hint-bearing `lt` gadget can witness its advice (same trick as
//! [`crate::backend`]).

use std::cell::RefCell;

use anyhow::Result;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget};

use plonky2::hash::hash_types::HashOutTarget;

use molt_petit::{valid_chain_be, Backend as MpBackend, BackendK as MpBackendK, BlockG, ChainG, Hash, HashG};

use crate::backend::CMP_BITS;
use crate::sphincs;
use crate::types::{C, D, F};
use crate::xmss;

#[derive(Clone, Copy)]
pub struct MNum {
    t: Target,
    v: F,
}

#[derive(Clone, Copy)]
pub struct MBool {
    t: BoolTarget,
    v: bool,
}

/// A plonky2 circuit that implements `molt_petit::Backend`.
pub struct MpCircuit {
    pub(crate) b: RefCell<CircuitBuilder<F, D>>,
    pub(crate) pw: RefCell<PartialWitness<F>>,
}

impl MpCircuit {
    pub fn new() -> Self {
        Self {
            b: RefCell::new(CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config())),
            pw: RefCell::new(PartialWitness::new()),
        }
    }

    /// A circuit constant (fixed in the circuit, not chosen by the prover).
    pub fn constant(&self, v: F) -> MNum {
        let t = self.b.borrow_mut().constant(v);
        MNum { t, v }
    }

    /// Wrap an existing wire whose value the witness already determines.
    pub fn wrap(&self, t: Target, v: F) -> MNum {
        MNum { t, v }
    }

    /// The wire of a number (to connect or register it).
    pub fn target(x: &MNum) -> Target {
        x.t
    }

    /// The value of a number.
    pub fn value(x: &MNum) -> F {
        x.v
    }

    /// Lift a witness field element to a wire.
    pub fn input(&self, v: F) -> MNum {
        let t = self.b.borrow_mut().add_virtual_target();
        self.pw.borrow_mut().set_target(t, v).expect("set target");
        MNum { t, v }
    }

    fn input_hash(&self, h: &Hash) -> HashG<MNum> {
        HashG {
            a: self.input(F::from_canonical_u64(h.a)),
            b: self.input(F::from_canonical_u64(h.b)),
            c: self.input(F::from_canonical_u64(h.c)),
            d: self.input(F::from_canonical_u64(h.d)),
        }
    }

    /// Require a boolean to hold (constrain the wire to 1).
    pub fn assert(&self, x: MBool) {
        let mut b = self.b.borrow_mut();
        let one = b.one();
        b.connect(x.t.target, one);
    }

    /// Build the circuit and prove it with the recorded witness.
    pub fn into_data_and_proof(
        self,
    ) -> Result<(CircuitData<F, C, D>, ProofWithPublicInputs<F, C, D>)> {
        let data = self.b.into_inner().build::<C>();
        let proof = data.prove(self.pw.into_inner())?;
        Ok((data, proof))
    }
}

impl Default for MpCircuit {
    fn default() -> Self {
        Self::new()
    }
}

impl MpBackend for MpCircuit {
    type Num = MNum;
    type Bool = MBool;

    fn zero(&self) -> MNum {
        MNum { t: self.b.borrow_mut().zero(), v: F::ZERO }
    }
    fn one(&self) -> MNum {
        MNum { t: self.b.borrow_mut().one(), v: F::ONE }
    }
    fn add(&self, a: MNum, b: MNum) -> MNum {
        MNum { t: self.b.borrow_mut().add(a.t, b.t), v: a.v + b.v }
    }
    fn lt(&self, a: MNum, b: MNum) -> MBool {
        // Sound `a < b` for values in [0, 2^CMP_BITS): witness the bit, then
        // range-check the branch-selected difference (same gadget as backend.rs).
        let v = a.v.to_canonical_u64() < b.v.to_canonical_u64();
        let mut builder = self.b.borrow_mut();
        let lt = builder.add_virtual_bool_target_safe();
        self.pw.borrow_mut().set_bool_target(lt, v).expect("set lt");
        let one = builder.one();
        let b_minus_a = builder.sub(b.t, a.t);
        let b_minus_a_m1 = builder.sub(b_minus_a, one);
        let a_minus_b = builder.sub(a.t, b.t);
        let chosen = builder.select(lt, b_minus_a_m1, a_minus_b);
        builder.split_le(chosen, CMP_BITS);
        MBool { t: lt, v }
    }
    fn eq(&self, a: MNum, b: MNum) -> MBool {
        MBool { t: self.b.borrow_mut().is_equal(a.t, b.t), v: a.v == b.v }
    }
    fn and(&self, a: MBool, b: MBool) -> MBool {
        MBool { t: self.b.borrow_mut().and(a.t, b.t), v: a.v && b.v }
    }
    fn or(&self, a: MBool, b: MBool) -> MBool {
        let mut builder = self.b.borrow_mut();
        let na = builder.not(a.t);
        let nb = builder.not(b.t);
        let nand = builder.and(na, nb);
        MBool { t: builder.not(nand), v: a.v || b.v }
    }
    fn not(&self, a: MBool) -> MBool {
        MBool { t: self.b.borrow_mut().not(a.t), v: !a.v }
    }
    fn bool_const(&self, b: bool) -> MBool {
        MBool { t: self.b.borrow_mut().constant_bool(b), v: b }
    }
    fn bool_to_num(&self, b: MBool) -> MNum {
        MNum { t: b.t.target, v: if b.v { F::ONE } else { F::ZERO } }
    }
}

impl MpCircuit {
    /// Witnessed floor division: `a = q * d + r`, `r < d`, `q < 2^CMP_BITS`.
    /// Sound for `a < 2^CMP_BITS` and `0 < d < 2^20` (so `q * d + r` does not
    /// wrap the Goldilocks field); the fold step only divides by `n` and `era`.
    fn divmod(&self, a: MNum, d: MNum) -> (MNum, MNum) {
        let (av, dv) = (a.v.to_canonical_u64(), d.v.to_canonical_u64());
        let (qv, rv) = if dv == 0 { (0, 0) } else { (av / dv, av % dv) };
        let (q, r) = {
            let mut b = self.b.borrow_mut();
            let q = b.add_virtual_target();
            let r = b.add_virtual_target();
            let qd = b.mul(q, d.t);
            let s = b.add(qd, r);
            b.connect(s, a.t);
            b.range_check(q, CMP_BITS);
            (q, r)
        };
        self.pw.borrow_mut().set_target(q, F::from_canonical_u64(qv)).expect("set q");
        self.pw.borrow_mut().set_target(r, F::from_canonical_u64(rv)).expect("set r");
        let rq = MNum { t: r, v: F::from_canonical_u64(rv) };
        let below = self.lt(rq, d);
        self.assert(below);
        (MNum { t: q, v: F::from_canonical_u64(qv) }, rq)
    }
}

impl MpBackendK for MpCircuit {
    fn div(&self, a: MNum, d: MNum) -> MNum {
        self.divmod(a, d).0
    }
    fn rem(&self, a: MNum, d: MNum) -> MNum {
        self.divmod(a, d).1
    }
    fn select(&self, c: MBool, a: MNum, b: MNum) -> MNum {
        let t = self.b.borrow_mut().select(c.t, a.t, b.t);
        MNum { t, v: if c.v { a.v } else { b.v } }
    }
    fn monus(&self, a: MNum, b: MNum) -> MNum {
        let below = self.lt(a, b);
        let diff = {
            let mut bl = self.b.borrow_mut();
            bl.sub(a.t, b.t)
        };
        let dv = if a.v.to_canonical_u64() < b.v.to_canonical_u64() { F::ZERO } else { a.v - b.v };
        let zero = self.zero();
        let t = self.b.borrow_mut().select(below.t, zero.t, diff);
        MNum { t, v: dv }
    }
}

/// One block's structural data (the validity check ignores the payload).
pub struct BlockData {
    pub slot: u64,
    pub height: u64,
    pub prev: Option<Hash>,
    pub id: Hash,
}

/// Build a `molt_petit::ChainG` of circuit wires from block data.
fn build_chaing(be: &MpCircuit, blocks: &[BlockData]) -> ChainG<MNum> {
    let mut chain = ChainG::NilG;
    for blk in blocks.iter().rev() {
        let (has_prev, prev) = match &blk.prev {
            Some(p) => (true, *p),
            None => (false, Hash { a: 0, b: 0, c: 0, d: 0 }),
        };
        let block = BlockG {
            slot: be.input(F::from_canonical_u64(blk.slot)),
            height: be.input(F::from_canonical_u64(blk.height)),
            has_prev,
            prev: be.input_hash(&prev),
            id: be.input_hash(&blk.id),
        };
        chain = ChainG::ConsG(block, Box::new(chain));
    }
    chain
}

/// Build and prove the circuit `molt_petit::valid_chain_be(n, q, chain) = true`.
/// The returned proof witnesses that the verified validator *accepts* the chain.
pub fn prove_valid_chain_be(
    n: u64,
    q: u64,
    blocks: &[BlockData],
) -> Result<(CircuitData<F, C, D>, ProofWithPublicInputs<F, C, D>)> {
    let be = MpCircuit::new();
    let chain = build_chaing(&be, blocks);
    let n_m = be.input(F::from_canonical_u64(n));
    let q_m = be.input(F::from_canonical_u64(q));
    // The verified function, executed as a circuit:
    let valid = valid_chain_be(&be, n_m, q_m, &chain);
    be.assert(valid);
    be.into_data_and_proof()
}

/// The privacy-preserving batch: each signer (consensus + application, per block)
/// hands in a signature *subproof* — a plonky2 proof that their SPHINCS+
/// signature verifies (never revealing the secret key) — and this single batch
/// proof **recursively verifies all of them** alongside the verified consensus
/// rule over the chain. `inner` is the subproof circuit (a
/// [`sphincs::VerifierCircuit`]'s data); `sigs` are the submitted subproofs
/// (e.g. 2 per block × `blocks.len()`); each is verified with one in-circuit
/// `verify_proof`. Returns the one aggregate proof.
pub fn prove_batch_recursive(
    inner: &CircuitData<F, C, D>,
    sigs: &[ProofWithPublicInputs<F, C, D>],
    n: u64,
    q: u64,
    blocks: &[BlockData],
) -> Result<(CircuitData<F, C, D>, ProofWithPublicInputs<F, C, D>)> {
    let be = MpCircuit::new();
    // Recursively verify each submitted signature subproof.
    for s in sigs {
        let pt = {
            let mut b = be.b.borrow_mut();
            let pt = b.add_virtual_proof_with_pis(&inner.common);
            let vd = b.constant_verifier_data(&inner.verifier_only);
            b.verify_proof::<C>(&pt, &vd, &inner.common);
            pt
        };
        be.pw.borrow_mut().set_proof_with_pis_target(&pt, s).expect("set subproof");
    }
    // The verified consensus rule (structure + window density) over the chain.
    let chain = build_chaing(&be, blocks);
    let n_m = be.input(F::from_canonical_u64(n));
    let q_m = be.input(F::from_canonical_u64(q));
    let valid = valid_chain_be(&be, n_m, q_m, &chain);
    be.assert(valid);
    be.into_data_and_proof()
}

/// Aggregate `sigs` signature subproofs into ONE proof (verify them all in a
/// single circuit, no consensus). The result can then be fed to
/// [`big_over_inner`] so the big circuit verifies just one proof regardless of
/// signature count. `inner` is the subproof circuit's data.
pub fn aggregate_n(
    inner: &CircuitData<F, C, D>,
    sigs: &[ProofWithPublicInputs<F, C, D>],
) -> Result<(CircuitData<F, C, D>, ProofWithPublicInputs<F, C, D>)> {
    let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    let mut pw = PartialWitness::new();
    for s in sigs {
        let pt = b.add_virtual_proof_with_pis(&inner.common);
        let vd = b.constant_verifier_data(&inner.verifier_only);
        b.verify_proof::<C>(&pt, &vd, &inner.common);
        pw.set_proof_with_pis_target(&pt, s)?;
    }
    let data = b.build::<C>();
    let proof = data.prove(pw)?;
    Ok((data, proof))
}

/// The **inline** regime: one certificate circuit that verifies each SPHINCS+
/// signature *directly* (its `verify_signature` gates, no per-signature
/// subproof) alongside the verified consensus rule over the chain. The prover
/// holds the signature blobs. `sigs` are `(pk, digest, sig)` triples.
pub fn prove_chain_with_inline_sphincs(
    p: &sphincs::Params,
    sigs: &[(Vec<F>, [F; 4], sphincs::Sig)],
    n: u64,
    q: u64,
    blocks: &[BlockData],
) -> Result<(CircuitData<F, C, D>, ProofWithPublicInputs<F, C, D>)> {
    let be = MpCircuit::new();
    for (pk, digest, sig) in sigs {
        let (pk_t, dg_t, st) = {
            let mut b = be.b.borrow_mut();
            let pk_t = b.add_virtual_targets(p.n_fe);
            let dg_t = [
                b.add_virtual_target(),
                b.add_virtual_target(),
                b.add_virtual_target(),
                b.add_virtual_target(),
            ];
            let st = sphincs::add_signature_targets(&mut b, p);
            sphincs::verify_signature(&mut b, &pk_t, HashOutTarget { elements: dg_t }, &st, p);
            (pk_t, dg_t, st)
        };
        {
            let mut pw = be.pw.borrow_mut();
            for (t, v) in pk_t.iter().zip(pk) {
                pw.set_target(*t, *v)?;
            }
            for i in 0..4 {
                pw.set_target(dg_t[i], digest[i])?;
            }
            sphincs::set_signature(&mut pw, &st, sig)?;
        }
    }
    let chain = build_chaing(&be, blocks);
    let n_m = be.input(F::from_canonical_u64(n));
    let q_m = be.input(F::from_canonical_u64(q));
    let valid = valid_chain_be(&be, n_m, q_m, &chain);
    be.assert(valid);
    be.into_data_and_proof()
}

/// The **inline** regime for **XMSS** signatures: the `sphincs` analogue, one
/// certificate circuit verifying each XMSS signature's gates directly (a single
/// WOTS+ check plus the `h`-node Merkle climb, no FORS/hypertree) alongside the
/// verified consensus rule. `sigs` are `(pk, digest, xmss::Sig)` triples.
pub fn prove_chain_with_inline_xmss(
    p: &sphincs::Params,
    sigs: &[(Vec<F>, [F; 4], xmss::Sig)],
    n: u64,
    q: u64,
    blocks: &[BlockData],
) -> Result<(CircuitData<F, C, D>, ProofWithPublicInputs<F, C, D>)> {
    let be = MpCircuit::new();
    for (pk, digest, sig) in sigs {
        let (pk_t, dg_t, st) = {
            let mut b = be.b.borrow_mut();
            let pk_t = b.add_virtual_targets(p.n_fe);
            let dg_t = [
                b.add_virtual_target(),
                b.add_virtual_target(),
                b.add_virtual_target(),
                b.add_virtual_target(),
            ];
            let st = xmss::add_signature_targets(&mut b, p);
            xmss::verify_signature(&mut b, &pk_t, HashOutTarget { elements: dg_t }, &st, p);
            (pk_t, dg_t, st)
        };
        {
            let mut pw = be.pw.borrow_mut();
            for (t, v) in pk_t.iter().zip(pk) {
                pw.set_target(*t, *v)?;
            }
            for i in 0..4 {
                pw.set_target(dg_t[i], digest[i])?;
            }
            xmss::set_signature(&mut pw, &st, sig)?;
        }
    }
    let chain = build_chaing(&be, blocks);
    let n_m = be.input(F::from_canonical_u64(n));
    let q_m = be.input(F::from_canonical_u64(q));
    let valid = valid_chain_be(&be, n_m, q_m, &chain);
    be.assert(valid);
    be.into_data_and_proof()
}

/// The big circuit verifying ONE inner (aggregate) proof + the verified
/// consensus rule over the chain.
pub fn big_over_inner(
    inner: &CircuitData<F, C, D>,
    inner_proof: &ProofWithPublicInputs<F, C, D>,
    n: u64,
    q: u64,
    blocks: &[BlockData],
) -> Result<(CircuitData<F, C, D>, ProofWithPublicInputs<F, C, D>)> {
    let be = MpCircuit::new();
    {
        let pt = {
            let mut b = be.b.borrow_mut();
            let pt = b.add_virtual_proof_with_pis(&inner.common);
            let vd = b.constant_verifier_data(&inner.verifier_only);
            b.verify_proof::<C>(&pt, &vd, &inner.common);
            pt
        };
        be.pw.borrow_mut().set_proof_with_pis_target(&pt, inner_proof)?;
    }
    let chain = build_chaing(&be, blocks);
    let n_m = be.input(F::from_canonical_u64(n));
    let q_m = be.input(F::from_canonical_u64(q));
    let valid = valid_chain_be(&be, n_m, q_m, &chain);
    be.assert(valid);
    be.into_data_and_proof()
}

/// A 2-to-1 aggregation node: verifies two proofs of the same inner circuit.
/// Building a tree of these keeps every circuit small (verify 2, ~2^12) instead
/// of one big circuit verifying all 8 (~2^14).
pub struct Agg2 {
    pub data: CircuitData<F, C, D>,
    pt1: ProofWithPublicInputsTarget<D>,
    pt2: ProofWithPublicInputsTarget<D>,
}

impl Agg2 {
    pub fn build(inner: &CircuitData<F, C, D>) -> Self {
        let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
        let pt1 = b.add_virtual_proof_with_pis(&inner.common);
        let vd1 = b.constant_verifier_data(&inner.verifier_only);
        b.verify_proof::<C>(&pt1, &vd1, &inner.common);
        let pt2 = b.add_virtual_proof_with_pis(&inner.common);
        let vd2 = b.constant_verifier_data(&inner.verifier_only);
        b.verify_proof::<C>(&pt2, &vd2, &inner.common);
        let data = b.build::<C>();
        Self { data, pt1, pt2 }
    }

    pub fn prove(
        &self,
        p1: &ProofWithPublicInputs<F, C, D>,
        p2: &ProofWithPublicInputs<F, C, D>,
    ) -> Result<ProofWithPublicInputs<F, C, D>> {
        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&self.pt1, p1)?;
        pw.set_proof_with_pis_target(&self.pt2, p2)?;
        self.data.prove(pw)
    }
}
