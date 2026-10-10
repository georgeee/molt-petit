//! The **recursive certificate**: one cyclic plonky2 circuit whose step is the
//! verified fold step of `molt_petit` (`cert_step_k_be`, `cert_step_sched_be`,
//! `cert_step_lock_be`), the code `Rust/FoldStep.lean` proves against the
//! model's `GroundedCertK` / `GroundedCertSched` / `GroundedCertLock`.
//!
//! A proof at step `k` has the fold state after `k` blocks as its public
//! inputs: tip id, tip slot, tip height, the `n - 1` entry tail buffer, and
//! the mode's extra state (the `n` per-producer floors in mode 1, the
//! generation `g` in mode 3, nothing in mode 2), followed by the circuit's own
//! verifier data. Each step verifies the previous step's proof of the SAME
//! circuit (or, at step 1, starts from the genesis state, a circuit constant),
//! runs the verified step on one block, and exposes the next state.
//!
//! `n`, `q = quorum(n)` and `era` are circuit constants. Signatures are NOT
//! checked here yet: the statements take `Signed` per block as the signature
//! gadget's guarantee, and wiring a signature subproof into the step is the
//! next increment.
//!
//! [`MpCircuit`] records witness values while it builds, so every step
//! rebuilds the circuit. The structure never depends on the values, and
//! [`FoldProver::step`] asserts that every rebuild has the same circuit digest.

use anyhow::{bail, ensure, Result};
use plonky2::field::types::{Field, PrimeField64};
use plonky2::gates::noop::NoopGate;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, CommonCircuitData};
use plonky2::plonk::circuit_data::VerifierCircuitTarget;
use plonky2::plonk::proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget};
use plonky2::recursion::cyclic_recursion::check_cyclic_proof_verifier_data;
use plonky2::recursion::dummy_circuit::cyclic_base_proof;

use molt_petit::{
    cert_next_floors_be, cert_next_tail_be, cert_step_k_be, cert_step_lock_be, cert_step_sched_be,
    BlockG, CertStateG, FloorsG, HashG, TailG, U64Backend,
};

use crate::backend::CMP_BITS;
use crate::mp_circuit::{MNum, MpCircuit};
use crate::types::{C, D, F};

/// Which fold step the certificate runs.
#[derive(Clone, Copy, Debug)]
pub enum Mode {
    /// Mode 1: per-producer key floor (`GroundedCertK`).
    K,
    /// Mode 2: the schedule pin `slot / era <= key_index` (`GroundedCertSched`).
    Sched { era: u64 },
    /// Mode 3: no mixing against the threaded generation (`GroundedCertLock`).
    Lock,
}

/// One block as the fold sees it.
#[derive(Clone, Copy, Debug)]
pub struct FoldBlock {
    pub slot: u64,
    pub height: u64,
    pub prev: [u64; 4],
    pub id: [u64; 4],
    pub key_index: u64,
}

/// The fold state (native): what a step's proof exposes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldState {
    pub tip_id: [u64; 4],
    pub tip_slot: u64,
    pub tip_height: u64,
    /// `(flag, slot)`, oldest first, length `n - 1`.
    pub tail: Vec<(u64, u64)>,
    /// Mode 1: the `n` floors; mode 3: `[g]`; mode 2: empty.
    pub extra: Vec<u64>,
}

impl FoldState {
    /// The genesis state (the genesis block has slot 0, height 0).
    pub fn genesis(n: usize, mode: Mode, g: &FoldBlock) -> Self {
        let mut tail = vec![(0u64, 0u64); n.saturating_sub(1)];
        if let Some(last) = tail.last_mut() {
            *last = (1, g.slot);
        }
        let extra = match mode {
            Mode::K => (0..n).map(|i| if i == 0 { g.key_index } else { 0 }).collect(),
            Mode::Sched { .. } => vec![],
            Mode::Lock => vec![g.key_index],
        };
        Self { tip_id: g.id, tip_slot: g.slot, tip_height: g.height, tail, extra }
    }

    /// Field encoding, in public-input order.
    pub fn to_fields(&self) -> Vec<F> {
        let mut v: Vec<u64> = self.tip_id.to_vec();
        v.push(self.tip_slot);
        v.push(self.tip_height);
        for (f, s) in &self.tail {
            v.push(*f);
            v.push(*s);
        }
        v.extend(&self.extra);
        v.into_iter().map(F::from_canonical_u64).collect()
    }

    fn len_for(n: usize, mode: Mode) -> usize {
        6 + 2 * n.saturating_sub(1)
            + match mode {
                Mode::K => n,
                Mode::Sched { .. } => 0,
                Mode::Lock => 1,
            }
    }
}

fn hashg_u64(h: &[u64; 4]) -> HashG<u64> {
    HashG { a: h[0], b: h[1], c: h[2], d: h[3] }
}

fn tail_of(v: &[(u64, u64)]) -> TailG<u64> {
    let mut t = TailG::TNil;
    for (f, s) in v.iter().rev() {
        t = TailG::TCons(*f, *s, Box::new(t));
    }
    t
}

fn tail_vec(t: &TailG<u64>) -> Vec<(u64, u64)> {
    let mut out = vec![];
    let mut cur = t;
    while let TailG::TCons(f, s, tl) = cur {
        out.push((*f, *s));
        cur = tl;
    }
    out
}

fn floors_of(v: &[u64]) -> FloorsG<u64> {
    let mut fl = FloorsG::FNil;
    for x in v.iter().rev() {
        fl = FloorsG::FCons(*x, Box::new(fl));
    }
    fl
}

fn floors_vec(fl: &FloorsG<u64>) -> Vec<u64> {
    let mut out = vec![];
    let mut cur = fl;
    while let FloorsG::FCons(x, tl) = cur {
        out.push(*x);
        cur = tl;
    }
    out
}

/// The native fold step, through the same `molt_petit` functions at
/// `U64Backend`: `Some(next)` when the step accepts.
pub fn native_step(n: u64, mode: Mode, st: &FoldState, b: &FoldBlock) -> Option<FoldState> {
    let be = U64Backend;
    let q = molt_petit::quorum(n);
    let cs = CertStateG { tip_id: hashg_u64(&st.tip_id), tip_slot: st.tip_slot, tip_height: st.tip_height, tail: tail_of(&st.tail) };
    let bg = BlockG { slot: b.slot, height: b.height, has_prev: true, prev: hashg_u64(&b.prev), id: hashg_u64(&b.id) };
    let (ok, extra) = match mode {
        Mode::K => {
            let fl = floors_of(&st.extra);
            let ok = cert_step_k_be(&be, n, q, &cs, &fl, &bg, b.key_index);
            (ok, floors_vec(&cert_next_floors_be(&be, n, &fl, &bg, b.key_index)))
        }
        Mode::Sched { era } => (cert_step_sched_be(&be, n, q, era, &cs, &bg, b.key_index), vec![]),
        Mode::Lock => (cert_step_lock_be(&be, n, q, &cs, st.extra[0], &bg, b.key_index), vec![b.key_index]),
    };
    if !ok {
        return None;
    }
    let tail = tail_vec(&cert_next_tail_be(&be, &cs.tail, b.slot));
    Some(FoldState { tip_id: b.id, tip_slot: b.slot, tip_height: b.height, tail, extra })
}

/// `CommonCircuitData` for a cyclic circuit of `2^bits` gates: a recursive
/// verifier padded to that size (plonky2's own construction; the step
/// circuit is padded to the same size and must use only gates it contains).
fn common_data_for_recursion(bits: usize) -> CommonCircuitData<F, D> {
    let config = CircuitConfig::standard_recursion_config();
    let builder = CircuitBuilder::<F, D>::new(config);
    let data = builder.build::<C>();
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let proof = builder.add_virtual_proof_with_pis(&data.common);
    let verifier_data = builder.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    let data = builder.build::<C>();

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let proof = builder.add_virtual_proof_with_pis(&data.common);
    let verifier_data = builder.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    while builder.num_gates() < 1 << bits {
        builder.add_gate(NoopGate, vec![]);
    }
    builder.build::<C>().common
}

/// Drives the cyclic certificate: genesis, then one proof per block.
pub struct FoldProver {
    pub n: usize,
    pub mode: Mode,
    genesis: FoldState,
    common: CommonCircuitData<F, D>,
    digest: Option<Vec<F>>,
    /// Gate count of the step circuit before padding (for the bench).
    pub step_gates: usize,
    /// Wall-clock of the last step's circuit build and of its proof.
    pub last_build: std::time::Duration,
    pub last_prove: std::time::Duration,
}

impl FoldProver {
    /// Fix the recursion shape: the inner proof's `CommonCircuitData` must be
    /// the step circuit's own, and the step circuit contains the verifier for
    /// that shape. Start from a padded recursive verifier and rebuild until
    /// the shape is a fixed point.
    pub fn new(n: usize, mode: Mode, genesis_block: &FoldBlock, bits: usize) -> Result<Self> {
        let mut fp = Self {
            n,
            mode,
            genesis: FoldState::genesis(n, mode, genesis_block),
            common: common_data_for_recursion(bits),
            digest: None,
            step_gates: 0,
            last_build: Default::default(),
            last_prove: Default::default(),
        };
        let g = fp.genesis.clone();
        let probe = FoldBlock { slot: g.tip_slot + 1, height: g.tip_height + 1, prev: g.tip_id, id: [0; 4], key_index: 0 };
        for _ in 0..8 {
            let built = fp.build(&fp.common, &g, &probe)?;
            fp.step_gates = built.gates;
            if built.success {
                return Ok(fp);
            }
            fp.common = built.data.common;
        }
        bail!("recursion shape did not converge")
    }

    pub fn genesis_state(&self) -> &FoldState {
        &self.genesis
    }

    /// Build the step circuit for `(prev, b)` and prove it. `inner` is the
    /// previous step's proof (`None` at the first step, which starts from the
    /// genesis constant). Returns the circuit data and the new proof.
    pub fn step(
        &mut self,
        prev: &FoldState,
        inner: Option<&ProofWithPublicInputs<F, C, D>>,
        b: &FoldBlock,
    ) -> Result<(CircuitData<F, C, D>, ProofWithPublicInputs<F, C, D>)> {
        let t = std::time::Instant::now();
        let Built { data, pw, vd_t, cond, inner_t, success, .. } = self.build(&self.common, prev, b)?;
        self.last_build = t.elapsed();
        ensure!(success, "step circuit does not have the recursion shape");
        let gen_f = self.genesis.to_fields();
        let mut pw = pw;
        let digest: Vec<F> = data.verifier_only.circuit_digest.elements.to_vec();
        match &self.digest {
            None => self.digest = Some(digest),
            Some(d) => ensure!(*d == digest, "step circuit changed between builds"),
        }
        // (6) Witness the recursion and prove.
        match inner {
            None => {
                pw.set_bool_target(cond, false)?;
                // The base case's public inputs are the genesis state.
                pw.set_proof_with_pis_target::<C, D>(
                    &inner_t,
                    &cyclic_base_proof(
                        &data.common,
                        &data.verifier_only,
                        gen_f.iter().copied().enumerate().collect(),
                    ),
                )?;
            }
            Some(p) => {
                pw.set_bool_target(cond, true)?;
                pw.set_proof_with_pis_target(&inner_t, p)?;
            }
        }
        pw.set_verifier_data_target(&vd_t, &data.verifier_only)?;
        let t = std::time::Instant::now();
        let proof = data.prove(pw)?;
        self.last_prove = t.elapsed();
        check_cyclic_proof_verifier_data(&proof, &data.verifier_only, &data.common)?;
        data.verify(proof.clone())?;
        Ok((data, proof))
    }

    /// Build the step circuit for `(prev, b)` against the inner shape `common`.
    fn build(&self, common: &CommonCircuitData<F, D>, prev: &FoldState, b: &FoldBlock) -> Result<Built> {
        let mut common = common.clone();
        let n = self.n;
        let mode = self.mode;
        let slen = FoldState::len_for(n, mode);
        let be = MpCircuit::new();

        // (1) Public outputs first (connected to the computed next state below),
        // then the verifier data, then the inner proof target.
        let (outs, vd_t, cond, inner_t) = {
            let mut bl = be.b.borrow_mut();
            let outs: Vec<Target> = (0..slen).map(|_| bl.add_virtual_public_input()).collect();
            let vd_t = bl.add_verifier_data_public_inputs();
            common.num_public_inputs = bl.num_public_inputs();
            let cond = bl.add_virtual_bool_target_safe();
            let inner_t = bl.add_virtual_proof_with_pis(&common);
            (outs, vd_t, cond, inner_t)
        };

        // (2) The previous state: the inner proof's state, or the genesis.
        let gen_f = self.genesis.to_fields();
        let prev_f = prev.to_fields();
        let prev_m: Vec<MNum> = (0..slen)
            .map(|i| {
                let t = {
                    let mut bl = be.b.borrow_mut();
                    let g = bl.constant(gen_f[i]);
                    bl.select(cond, inner_t.public_inputs[i], g)
                };
                be.wrap(t, prev_f[i])
            })
            .collect();
        let tail_m: TailG<MNum> = {
            let mut t = TailG::TNil;
            for j in (0..n.saturating_sub(1)).rev() {
                t = TailG::TCons(prev_m[6 + 2 * j], prev_m[6 + 2 * j + 1], Box::new(t));
            }
            t
        };
        let st = CertStateG {
            tip_id: HashG { a: prev_m[0], b: prev_m[1], c: prev_m[2], d: prev_m[3] },
            tip_slot: prev_m[4],
            tip_height: prev_m[5],
            tail: tail_m,
        };
        let extra0 = 6 + 2 * n.saturating_sub(1);

        // (3) The block (prover's witness) and the circuit constants.
        let inp = |v: u64| be.input(F::from_canonical_u64(v));
        let bg = BlockG {
            slot: inp(b.slot),
            height: inp(b.height),
            has_prev: true,
            prev: HashG { a: inp(b.prev[0]), b: inp(b.prev[1]), c: inp(b.prev[2]), d: inp(b.prev[3]) },
            id: HashG { a: inp(b.id[0]), b: inp(b.id[1]), c: inp(b.id[2]), d: inp(b.id[3]) },
        };
        let ki = inp(b.key_index);
        // `lt` and `divmod` are sound below 2^CMP_BITS. Every number in the
        // step is built from these three, the hash limbs (compared only by
        // `eq`), small constants, and the previous step's outputs, which were
        // built the same way; so range-checking the block's scalars suffices.
        {
            let mut bl = be.b.borrow_mut();
            for x in [&bg.slot, &bg.height, &ki] {
                bl.range_check(MpCircuit::target(x), CMP_BITS);
            }
        }
        let n_m = be.constant(F::from_canonical_u64(n as u64));
        let q_m = be.constant(F::from_canonical_u64(molt_petit::quorum(n as u64)));

        // (4) The verified step, executed as a circuit; then the next state.
        let mut next_extra: Vec<MNum> = vec![];
        let ok = match mode {
            Mode::K => {
                let fl = {
                    let mut f = FloorsG::FNil;
                    for i in (0..n).rev() {
                        f = FloorsG::FCons(prev_m[extra0 + i], Box::new(f));
                    }
                    f
                };
                let ok = cert_step_k_be(&be, n_m, q_m, &st, &fl, &bg, ki);
                let mut cur = cert_next_floors_be(&be, n_m, &fl, &bg, ki);
                while let FloorsG::FCons(x, tl) = cur {
                    next_extra.push(x);
                    cur = *tl;
                }
                ok
            }
            Mode::Sched { era } => {
                let era_m = be.constant(F::from_canonical_u64(era));
                cert_step_sched_be(&be, n_m, q_m, era_m, &st, &bg, ki)
            }
            Mode::Lock => {
                next_extra.push(ki);
                cert_step_lock_be(&be, n_m, q_m, &st, prev_m[extra0], &bg, ki)
            }
        };
        be.assert(ok);
        let next_tail = cert_next_tail_be(&be, &st.tail, bg.slot);
        let mut next: Vec<MNum> = vec![bg.id.a, bg.id.b, bg.id.c, bg.id.d, bg.slot, bg.height];
        let mut cur = next_tail;
        while let TailG::TCons(f, s, tl) = cur {
            next.push(f);
            next.push(s);
            cur = *tl;
        }
        next.extend(next_extra);
        ensure!(next.len() == slen, "state length {} != {}", next.len(), slen);

        // (5) Expose the next state; verify the inner proof (or a dummy).
        {
            let mut bl = be.b.borrow_mut();
            for (o, x) in outs.iter().zip(&next) {
                bl.connect(*o, MpCircuit::target(x));
            }
            bl.conditionally_verify_cyclic_proof_or_dummy::<C>(cond, &inner_t, &common)?;
        }
        let MpCircuit { b: bl, pw } = be;
        let bl = bl.into_inner();
        let gates = bl.num_gates();
        let (data, success) = bl.try_build_with_options::<C>(true);
        Ok(Built { data, pw: pw.into_inner(), vd_t, cond, inner_t, success, gates })
    }
}

struct Built {
    data: CircuitData<F, C, D>,
    pw: PartialWitness<F>,
    vd_t: VerifierCircuitTarget,
    cond: BoolTarget,
    inner_t: ProofWithPublicInputsTarget<D>,
    success: bool,
    gates: usize,
}


/// A demo chain: genesis at slot 0, then `len` blocks at slots 1, 2, ...,
/// each by key index `slot / n` (accepted by all three modes, with
/// `era = n` in mode 2). Ids are opaque to the fold step.
pub fn demo_chain(n: usize, len: u64) -> (FoldBlock, Vec<FoldBlock>) {
    let id = |slot: u64| [slot * 7 + 1, slot + 11, 0xabc, 0xdef];
    let g = FoldBlock { slot: 0, height: 0, prev: [0; 4], id: id(0), key_index: 0 };
    let bs = (1..=len)
        .map(|s| FoldBlock { slot: s, height: s, prev: id(s - 1), id: id(s), key_index: s / n as u64 })
        .collect();
    (g, bs)
}

/// The state a certificate proof exposes, decoded.
pub fn exposed_state(n: usize, mode: Mode, proof: &ProofWithPublicInputs<F, C, D>) -> Result<FoldState> {
    let slen = FoldState::len_for(n, mode);
    if proof.public_inputs.len() < slen {
        bail!("short public inputs");
    }
    let v: Vec<u64> = proof.public_inputs[..slen].iter().map(|x| x.to_canonical_u64()).collect();
    let tl = n.saturating_sub(1);
    Ok(FoldState {
        tip_id: [v[0], v[1], v[2], v[3]],
        tip_slot: v[4],
        tip_height: v[5],
        tail: (0..tl).map(|j| (v[6 + 2 * j], v[7 + 2 * j])).collect(),
        extra: v[6 + 2 * tl..].to_vec(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Recursion shape used by the tests and the bench.
    pub const BITS: usize = 13;

    fn blk(slot: u64, height: u64, prev: [u64; 4], key_index: u64) -> FoldBlock {
        let id = [slot * 7 + 1, height + 11, key_index + 3, 0xabc];
        FoldBlock { slot, height, prev, id, key_index }
    }

    /// A chain of `len` blocks after genesis, slots 1, 2, ..., with key
    /// indices from `kis`.
    fn chain(kis: &[u64]) -> (FoldBlock, Vec<FoldBlock>) {
        let g = blk(0, 0, [0; 4], 0);
        let mut out = vec![];
        let mut prev = g.id;
        for (i, ki) in kis.iter().enumerate() {
            let b = blk(i as u64 + 1, i as u64 + 1, prev, *ki);
            prev = b.id;
            out.push(b);
        }
        (g, out)
    }

    fn run(n: usize, mode: Mode, kis: &[u64]) {
        let (g, bs) = chain(kis);
        let mut fp = FoldProver::new(n, mode, &g, BITS).unwrap();
        let mut st = fp.genesis_state().clone();
        let mut proof = None;
        for b in &bs {
            let next = native_step(n as u64, mode, &st, b).expect("native fold accepts");
            let (_, p) = fp.step(&st, proof.as_ref(), b).expect("circuit step");
            assert_eq!(exposed_state(n, mode, &p).unwrap(), next, "circuit state == native state");
            st = next;
            proof = Some(p);
        }
    }

    #[test]
    fn fold_k_matches_native() {
        // Floors: producer slot%3; key indices rise per producer.
        run(3, Mode::K, &[0, 1, 1, 2, 2]);
    }

    #[test]
    fn fold_sched_matches_native() {
        // era 2: slot/2 <= ki.
        run(3, Mode::Sched { era: 2 }, &[0, 1, 1, 2, 2]);
    }

    #[test]
    fn fold_lock_matches_native() {
        // n = 3: slots 1,2 share era 0 with genesis (g = 0), slot 3 moves to 1.
        run(3, Mode::Lock, &[0, 0, 1, 1, 1]);
    }

    fn fails<T>(f: impl FnOnce() -> Result<T>) -> bool {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
            Ok(r) => r.is_err(),
            Err(_) => true,
        }
    }

    #[test]
    fn rejected_block_has_no_proof() {
        let (g, bs) = chain(&[0, 1]);
        let mode = Mode::Lock;
        let mut fp = FoldProver::new(3, mode, &g, BITS).unwrap();
        let st0 = fp.genesis_state().clone();
        // Key index 0 then 1 inside one n-era breaks lock-step (slots 1, 2 < 3).
        let st1 = native_step(3, mode, &st0, &bs[0]).unwrap();
        assert!(native_step(3, mode, &st1, &bs[1]).is_none());
        let (_, p1) = fp.step(&st0, None, &bs[0]).unwrap();
        assert!(fails(|| fp.step(&st1, Some(&p1), &bs[1])));
    }

    #[test]
    fn forged_previous_state_has_no_proof() {
        let (g, bs) = chain(&[0, 0]);
        let mode = Mode::Sched { era: 4 };
        let mut fp = FoldProver::new(3, mode, &g, BITS).unwrap();
        let st0 = fp.genesis_state().clone();
        let st1 = native_step(3, mode, &st0, &bs[0]).unwrap();
        let (_, p1) = fp.step(&st0, None, &bs[0]).unwrap();
        // Claim a different previous tip height than the inner proof exposes.
        let mut forged = st1.clone();
        forged.tip_height += 1;
        let mut b = bs[1];
        b.height += 1;
        assert!(native_step(3, mode, &forged, &b).is_some());
        assert!(fails(|| fp.step(&forged, Some(&p1), &b)));
    }
}
