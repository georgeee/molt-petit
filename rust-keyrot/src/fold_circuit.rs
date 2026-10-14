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
//! `n`, `q = quorum(n)` and `era` are circuit constants. With a
//! [`SigBinding`], each step also verifies the block's signature subproof (a
//! proof of the signature circuit, a constant), requires its digest to be the
//! block id, and requires its public key to be the leaf of
//! `(slot % n, key_index)` in a committed key registry (the root, a constant).
//! That is the `Signed b` premise of the fold statements.
//!
//! The block id is computed in-circuit via Poseidon hash from the block's
//! fields: slot, height, constant 1 for has_prev, the four prev limbs, four
//! contents_hash witness targets, and the key_index target, with each u64
//! field split into 32-bit halves (lo then hi) via `split_low_high(t, 32, 64)`
//! and constrained to be canonical (if hi == 2^32 - 1 then lo == 0).
//! Connecting the computed digest to the block id wire ensures that what the
//! signature signs is bound to the key version wire used in the step and
//! registry lookup.
//!
//! [`MpCircuit`] records witness values while it builds, so every step
//! rebuilds the circuit. The structure never depends on the values, and
//! [`FoldProver::step`] asserts that every rebuild has the same circuit digest.

use anyhow::{bail, ensure, Result};
use plonky2::field::types::{Field, PrimeField64};
use plonky2::gates::noop::NoopGate;
use plonky2::hash::hash_types::HashOut;
use plonky2::hash::merkle_proofs::{MerkleProof, MerkleProofTarget};
use plonky2::hash::merkle_tree::MerkleTree;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, CommonCircuitData, VerifierCircuitData};
use plonky2::plonk::circuit_data::VerifierCircuitTarget;
use plonky2::plonk::proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget};
use plonky2::recursion::cyclic_recursion::check_cyclic_proof_verifier_data;
use plonky2::recursion::dummy_circuit::cyclic_base_proof;

use molt_petit::{
    cert_next_floors_be, cert_next_tail_be, cert_step_k_be, cert_step_lock_be, cert_step_sched_be,
    BlockG, CertStateG, FloorsG, HashG, TailG, U64Backend,
};

pub use crate::poseidon_util::fold_block_id;
use crate::backend::CMP_BITS;
use crate::mp_circuit::{MNum, MpCircuit};
use molt_petit::BackendK as MpBackendK;
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
    pub sig: [u64; 4],
    pub contents_hash: [u64; 4],
    pub key_index: u64,
}

/// The fold state (native): what a step's proof exposes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldState {
    pub tip_id: [u64; 4],
    pub tip_slot: u64,
    pub tip_height: u64,
    pub tip_sig: [u64; 4],
    /// `(flag, slot)`, oldest first, length `n - 1`.
    pub tail: Vec<(u64, u64)>,
    /// Mode 1: the `n` floors; mode 3: `[g]`; mode 2: empty.
    pub extra: Vec<u64>,
}

impl FoldState {
    /// The genesis state (the genesis block has slot 0, height 0).
    pub fn genesis(n: usize, mode: Mode, g: &FoldBlock, genesis_sig: [u64; 4]) -> Self {
        let mut tail = vec![(0u64, 0u64); n.saturating_sub(1)];
        if let Some(last) = tail.last_mut() {
            *last = (1, g.slot);
        }
        let extra = match mode {
            Mode::K => (0..n).map(|i| if i == 0 { g.key_index } else { 0 }).collect(),
            Mode::Sched { .. } => vec![],
            Mode::Lock => vec![g.key_index],
        };
        Self {
            tip_id: g.id,
            tip_slot: g.slot,
            tip_height: g.height,
            tip_sig: genesis_sig,
            tail,
            extra,
        }
    }

    /// Field encoding, in public-input order.
    pub fn to_fields(&self) -> Vec<F> {
        let mut v: Vec<u64> = self.tip_id.to_vec();
        v.push(self.tip_slot);
        v.push(self.tip_height);
        v.extend_from_slice(&self.tip_sig);
        for (f, s) in &self.tail {
            v.push(*f);
            v.push(*s);
        }
        v.extend(&self.extra);
        v.into_iter().map(F::from_canonical_u64).collect()
    }

    fn len_for(n: usize, mode: Mode) -> usize {
        10 + 2 * n.saturating_sub(1)
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
    Some(FoldState { tip_id: b.id, tip_slot: b.slot, tip_height: b.height, tip_sig: b.sig, tail, extra })
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

/// The key registry: a Poseidon Merkle tree whose leaf at
/// `producer << kbits | key_index` is that key's public key (the signature
/// circuit's `pk` public input). Its root is a circuit constant, so the
/// certificate is about this registry and no other.
pub struct KeyRegistry {
    pub tree: MerkleTree<F, PoseidonHash>,
    pub pbits: usize,
    pub kbits: usize,
}

impl KeyRegistry {
    /// `pk(p, ki)` for every producer `p < n` and key index `ki < 2^kbits`;
    /// the unused leaves (`p >= n`) are unreachable, since the step proves
    /// `p = slot % n < n`.
    pub fn new(n: usize, kbits: usize, n_fe: usize, pk: impl Fn(usize, u64) -> Vec<F>) -> Self {
        let pbits = (usize::BITS - (n.max(2) - 1).leading_zeros()) as usize;
        let leaves = (0..1usize << (pbits + kbits))
            .map(|i| {
                let (p, ki) = (i >> kbits, (i & ((1 << kbits) - 1)) as u64);
                if p < n { pk(p, ki) } else { vec![F::ZERO; n_fe] }
            })
            .collect();
        Self { tree: MerkleTree::new(leaves, 0), pbits, kbits }
    }

    pub fn root(&self) -> HashOut<F> {
        self.tree.cap.0[0]
    }

    pub fn path(&self, p: usize, ki: u64) -> MerkleProof<F, PoseidonHash> {
        self.tree.prove((p << self.kbits) | ki as usize)
    }
}

/// What binds a step to a signature: the signature circuit (public inputs
/// `pk` then the 4-limb digest), its verifier data (a constant), and the
/// registry root.
pub struct SigBinding {
    pub verifier: CircuitData<F, C, D>,
    pub n_fe: usize,
    pub root: HashOut<F>,
    pub pbits: usize,
    pub kbits: usize,
}

/// One block's signature evidence: a proof of the signature circuit on
/// `(pk, block id)`, and `pk`'s registry path.
pub struct BlockSig {
    pub proof: ProofWithPublicInputs<F, C, D>,
    pub path: MerkleProof<F, PoseidonHash>,
}

/// Drives the cyclic certificate: genesis, then one proof per block.
pub struct FoldProver {
    /// `None` only for structure tests: such a certificate says nothing about
    /// who signed.
    pub sig: Option<SigBinding>,
    pub n: usize,
    pub mode: Mode,
    genesis: FoldState,
    common: CommonCircuitData<F, D>,
    digest: Option<Vec<F>>,
    pub verifier_data: Option<VerifierCircuitData<F, C, D>>,
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
    pub fn new(n: usize, mode: Mode, genesis_block: &FoldBlock, bits: usize, sig: Option<SigBinding>) -> Result<Self> {
        let mut fp = Self {
            sig,
            n,
            mode,
            genesis: FoldState::genesis(n, mode, genesis_block, genesis_block.sig),
            common: common_data_for_recursion(bits),
            digest: None,
            verifier_data: None,
            step_gates: 0,
            last_build: Default::default(),
            last_prove: Default::default(),
        };
        let g = fp.genesis.clone();
        let probe_ch = [0u64; 4];
        let probe_id = fold_block_id(g.tip_slot + 1, g.tip_height + 1, true, g.tip_id, true, g.tip_sig, probe_ch, 0);
        let probe = FoldBlock {
            slot: g.tip_slot + 1,
            height: g.tip_height + 1,
            prev: g.tip_id,
            id: probe_id,
            sig: [0u64; 4],
            contents_hash: probe_ch,
            key_index: 0,
        };
        for _ in 0..8 {
            let built = fp.build(&fp.common, &g, &probe, None)?;
            fp.step_gates = built.gates;
            if built.success {
                fp.verifier_data = Some(built.data.verifier_data());
                fp.digest = Some(built.data.verifier_only.circuit_digest.elements.to_vec());
                return Ok(fp);
            }
            fp.common = built.data.common;
        }
        bail!("recursion shape did not converge")
    }

    pub fn verifier_data(&self) -> &VerifierCircuitData<F, C, D> {
        self.verifier_data.as_ref().expect("verifier data initialized")
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
        sig: Option<&BlockSig>,
    ) -> Result<(CircuitData<F, C, D>, ProofWithPublicInputs<F, C, D>)> {
        ensure!(self.sig.is_some() == sig.is_some(), "signature evidence must match the binding");
        let t = std::time::Instant::now();
        let Built { data, pw, vd_t, cond, inner_t, success, .. } = self.build(&self.common, prev, b, sig)?;
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
    /// With a binding, `sig` is the witness (`None` while fixing the shape:
    /// targets only, never proved).
    fn build(
        &self,
        common: &CommonCircuitData<F, D>,
        prev: &FoldState,
        b: &FoldBlock,
        sig: Option<&BlockSig>,
    ) -> Result<Built> {
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
                t = TailG::TCons(prev_m[10 + 2 * j], prev_m[10 + 2 * j + 1], Box::new(t));
            }
            t
        };
        let st = CertStateG {
            tip_id: HashG { a: prev_m[0], b: prev_m[1], c: prev_m[2], d: prev_m[3] },
            tip_slot: prev_m[4],
            tip_height: prev_m[5],
            tail: tail_m,
        };
        let extra0 = 10 + 2 * n.saturating_sub(1);

        // (3) The block (prover's witness) and the circuit constants.
        let inp = |v: u64| be.input(F::from_canonical_u64(v));
        let bg = BlockG {
            slot: inp(b.slot),
            height: inp(b.height),
            has_prev: true,
            prev: HashG { a: inp(b.prev[0]), b: inp(b.prev[1]), c: inp(b.prev[2]), d: inp(b.prev[3]) },
            id: HashG { a: inp(b.id[0]), b: inp(b.id[1]), c: inp(b.id[2]), d: inp(b.id[3]) },
        };
        let sig_w = [
            inp(b.sig[0]),
            inp(b.sig[1]),
            inp(b.sig[2]),
            inp(b.sig[3]),
        ];
        let ki = inp(b.key_index);
        let ch = [
            inp(b.contents_hash[0]),
            inp(b.contents_hash[1]),
            inp(b.contents_hash[2]),
            inp(b.contents_hash[3]),
        ];
        // `lt` and `divmod` are sound below 2^CMP_BITS. Every number in the
        // step is built from these three, the hash limbs (compared only by
        // `eq`), small constants, and the previous step's outputs, which were
        // built the same way; so range-checking the block's scalars suffices.
        {
            let mut bl = be.b.borrow_mut();
            for x in [&bg.slot, &bg.height, &ki] {
                bl.range_check(MpCircuit::target(x), CMP_BITS);
            }
            let split_canonical = |bl: &mut CircuitBuilder<F, D>, t: Target| -> [Target; 2] {
                let (lo, hi) = bl.split_low_high(t, 32, 64);
                let max_u32 = bl.constant(F::from_canonical_u64(0xffff_ffff));
                let is_max = bl.is_equal(hi, max_u32);
                let bad = bl.mul(is_max.target, lo);
                let zero = bl.zero();
                bl.connect(bad, zero);
                [lo, hi]
            };
            for limb in &sig_w {
                split_canonical(&mut bl, MpCircuit::target(limb));
            }
            let mut hash_targets = Vec::with_capacity(32);
            hash_targets.extend_from_slice(&split_canonical(&mut bl, MpCircuit::target(&bg.slot)));
            hash_targets.extend_from_slice(&split_canonical(&mut bl, MpCircuit::target(&bg.height)));
            hash_targets.push(bl.one());
            for limb in [&bg.prev.a, &bg.prev.b, &bg.prev.c, &bg.prev.d] {
                hash_targets.extend_from_slice(&split_canonical(&mut bl, MpCircuit::target(limb)));
            }
            hash_targets.push(bl.one());
            for limb in [&prev_m[6], &prev_m[7], &prev_m[8], &prev_m[9]] {
                hash_targets.extend_from_slice(&split_canonical(&mut bl, MpCircuit::target(limb)));
            }
            for limb in &ch {
                hash_targets.extend_from_slice(&split_canonical(&mut bl, MpCircuit::target(limb)));
            }
            hash_targets.extend_from_slice(&split_canonical(&mut bl, MpCircuit::target(&ki)));

            let computed_id = bl.hash_n_to_hash_no_pad::<PoseidonHash>(hash_targets);
            bl.connect(computed_id.elements[0], MpCircuit::target(&bg.id.a));
            bl.connect(computed_id.elements[1], MpCircuit::target(&bg.id.b));
            bl.connect(computed_id.elements[2], MpCircuit::target(&bg.id.c));
            bl.connect(computed_id.elements[3], MpCircuit::target(&bg.id.d));
        }
        let n_m = be.constant(F::from_canonical_u64(n as u64));
        let q_m = be.constant(F::from_canonical_u64(molt_petit::quorum(n as u64)));

        // (3b) The block's signature: a proof of the signature circuit whose
        // digest is the block id and whose pk is the registry leaf of
        // (slot % n, key_index).
        if let Some(sb) = &self.sig {
            let p = MpBackendK::rem(&be, bg.slot, n_m);
            let mut bl = be.b.borrow_mut();
            let st = bl.add_virtual_proof_with_pis(&sb.verifier.common);
            let vd = bl.constant_verifier_data(&sb.verifier.verifier_only);
            bl.verify_proof::<C>(&st, &vd, &sb.verifier.common);
            let pk = st.public_inputs[..sb.n_fe].to_vec();
            for (i, x) in [&bg.id.a, &bg.id.b, &bg.id.c, &bg.id.d].into_iter().enumerate() {
                bl.connect(st.public_inputs[sb.n_fe + i], MpCircuit::target(x));
            }
            for (i, x) in sig_w.iter().enumerate() {
                bl.connect(st.public_inputs[sb.n_fe + 4 + i], MpCircuit::target(x));
            }
            bl.range_check(MpCircuit::target(&ki), sb.kbits);
            let shift = bl.constant(F::from_canonical_u64(1 << sb.kbits));
            let idx = bl.mul_add(MpCircuit::target(&p), shift, MpCircuit::target(&ki));
            let bits = bl.split_le(idx, sb.pbits + sb.kbits);
            let path = MerkleProofTarget {
                siblings: (0..sb.pbits + sb.kbits).map(|_| bl.add_virtual_hash()).collect(),
            };
            let root = bl.constant_hash(sb.root);
            bl.verify_merkle_proof::<PoseidonHash>(pk, &bits, root, &path);
            if let Some(w) = sig {
                let mut pw = be.pw.borrow_mut();
                pw.set_proof_with_pis_target(&st, &w.proof)?;
                ensure!(w.path.siblings.len() == path.siblings.len(), "registry path length");
                for (t, h) in path.siblings.iter().zip(&w.path.siblings) {
                    pw.set_hash_target(*t, *h)?;
                }
            }
        }

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
        let mut next: Vec<MNum> = vec![
            bg.id.a, bg.id.b, bg.id.c, bg.id.d,
            bg.slot, bg.height,
            sig_w[0], sig_w[1], sig_w[2], sig_w[3],
        ];
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
/// `era = n` in mode 2). Ids are computed natively with `fold_block_id`.
pub fn demo_chain(n: usize, len: u64) -> (FoldBlock, Vec<FoldBlock>) {
    let contents_hash = [0u64; 4];
    let g_sig = [0u64; 4];
    let g = FoldBlock {
        slot: 0,
        height: 0,
        prev: [0; 4],
        id: fold_block_id(0, 0, false, [0; 4], false, [0; 4], contents_hash, 0),
        sig: g_sig,
        contents_hash,
        key_index: 0,
    };
    let mut bs = Vec::with_capacity(len as usize);
    let mut prev = g.id;
    let mut prev_sig = g.sig;
    for s in 1..=len {
        let ki = s / n as u64;
        let sig = [s, 0, 0, 0];
        let id = fold_block_id(s, s, true, prev, true, prev_sig, contents_hash, ki);
        let b = FoldBlock {
            slot: s,
            height: s,
            prev,
            id,
            sig,
            contents_hash,
            key_index: ki,
        };
        prev = id;
        prev_sig = sig;
        bs.push(b);
    }
    (g, bs)
}

/// The client's view of a certificate state (`stateView` in
/// `Spec/RustBridge.lean`): tip id, slot, height, and the present tail slots
/// `s` with `tip_slot + 2 - n <= s`. This is what a decoder hands the client
/// as its `CertClaim` (tip fields, and tail blocks right in their slots).
pub fn state_view(n: usize, st: &FoldState) -> ([u64; 4], u64, u64, Vec<u64>) {
    let lo = (st.tip_slot + 2).saturating_sub(n as u64);
    let tail = st.tail.iter().filter(|(f, s)| *f == 1 && lo <= *s).map(|(_, s)| *s).collect();
    (st.tip_id, st.tip_slot, st.tip_height, tail)
}

/// The view of the claim the model derives from a history
/// (`claimView (modelClaimOf n G bs)`).
pub fn history_view(n: usize, g: &FoldBlock, bs: &[FoldBlock]) -> ([u64; 4], u64, u64, Vec<u64>) {
    let t = bs.last().unwrap_or(g);
    let lo = (t.slot + 2).saturating_sub(n as u64);
    let tail = std::iter::once(g).chain(bs).map(|b| b.slot).filter(|s| lo <= *s).collect();
    (t.id, t.slot, t.height, tail)
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
        tip_sig: [v[6], v[7], v[8], v[9]],
        tail: (0..tl).map(|j| (v[10 + 2 * j], v[11 + 2 * j])).collect(),
        extra: v[10 + 2 * tl..].to_vec(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Recursion shape used by the tests and the bench.
    pub const BITS: usize = 13;

    /// A chain of `len` blocks after genesis, slots 1, 2, ..., with key
    /// indices from `kis`.
    fn chain(kis: &[u64]) -> (FoldBlock, Vec<FoldBlock>) {
        let g_ch = [1, 11, 3, 0xabc];
        let g_sig = [100, 200, 300, 400];
        let g = FoldBlock {
            slot: 0,
            height: 0,
            prev: [0; 4],
            id: fold_block_id(0, 0, false, [0; 4], false, [0; 4], g_ch, 0),
            sig: g_sig,
            contents_hash: g_ch,
            key_index: 0,
        };
        let mut out = vec![];
        let mut prev = g.id;
        let mut parent_sig = g.sig;
        for (i, ki) in kis.iter().enumerate() {
            let slot = i as u64 + 1;
            let height = i as u64 + 1;
            let contents_hash = [slot * 7 + 1, height + 11, *ki + 3, 0xabc];
            let sig = [slot * 10 + 1, 2, 3, 4];
            let id = fold_block_id(slot, height, true, prev, true, parent_sig, contents_hash, *ki);
            let b = FoldBlock {
                slot,
                height,
                prev,
                id,
                sig,
                contents_hash,
                key_index: *ki,
            };
            prev = b.id;
            parent_sig = b.sig;
            out.push(b);
        }
        (g, out)
    }

    fn run(n: usize, mode: Mode, kis: &[u64]) {
        let (g, bs) = chain(kis);
        let mut fp = FoldProver::new(n, mode, &g, BITS, None).unwrap();
        let mut st = fp.genesis_state().clone();
        let mut proof = None;
        for b in &bs {
            let next = native_step(n as u64, mode, &st, b).expect("native fold accepts");
            let (_, p) = fp.step(&st, proof.as_ref(), b, None).expect("circuit step");
            assert_eq!(exposed_state(n, mode, &p).unwrap(), next, "circuit state == native state");
            let k = bs.iter().position(|x| x.slot == b.slot).unwrap();
            assert_eq!(state_view(n, &next), history_view(n, &g, &bs[..=k]), "stateView == claimView (modelClaimOf)");
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
        let mut fp = FoldProver::new(3, mode, &g, BITS, None).unwrap();
        let st0 = fp.genesis_state().clone();
        // Key index 0 then 1 inside one n-era breaks lock-step (slots 1, 2 < 3).
        let st1 = native_step(3, mode, &st0, &bs[0]).unwrap();
        assert!(native_step(3, mode, &st1, &bs[1]).is_none());
        let (_, p1) = fp.step(&st0, None, &bs[0], None).unwrap();
        assert!(fails(|| fp.step(&st1, Some(&p1), &bs[1], None)));
    }

    #[test]
    fn forged_previous_state_has_no_proof() {
        let (g, bs) = chain(&[0, 0]);
        let mode = Mode::Sched { era: 4 };
        let mut fp = FoldProver::new(3, mode, &g, BITS, None).unwrap();
        let st0 = fp.genesis_state().clone();
        let st1 = native_step(3, mode, &st0, &bs[0]).unwrap();
        let (_, p1) = fp.step(&st0, None, &bs[0], None).unwrap();
        // Claim a different previous tip height than the inner proof exposes.
        let mut forged = st1.clone();
        forged.tip_height += 1;
        let mut b = bs[1];
        b.height += 1;
        b.id = fold_block_id(b.slot, b.height, true, b.prev, true, st1.tip_sig, b.contents_hash, b.key_index);
        assert!(native_step(3, mode, &forged, &b).is_some());
        assert!(fails(|| fp.step(&forged, Some(&p1), &b, None)));
    }

    /// XMSS keys for every (producer, key index): small trees, one leaf per
    /// signed block (each key signs one block in `demo_chain`).
    struct Keys {
        keys: Vec<Vec<crate::xmss::Key>>,
        vc: crate::xmss::VerifierCircuit,
        reg: KeyRegistry,
    }

    fn keys(n: usize, kbits: usize) -> Keys {
        let p = crate::sphincs::Params::xmss("t", 2, 3);
        let keys: Vec<Vec<_>> = (0..n)
            .map(|pr| (0..1u64 << kbits).map(|ki| crate::xmss::Key::keygen(p.clone(), 1000 * pr as u64 + ki)).collect())
            .collect();
        let reg = KeyRegistry::new(n, kbits, 2, |pr, ki| keys[pr][ki as usize].public_key());
        let vc = crate::xmss::VerifierCircuit::build(p);
        Keys { keys, vc, reg }
    }

    fn dig(id: [u64; 4]) -> [F; 4] {
        id.map(F::from_canonical_u64)
    }

    /// Signature evidence for `b`, signed by key `(pr, ki)` over `msg`.
    fn evidence(k: &Keys, pr: usize, ki: u64, msg: [u64; 4]) -> (BlockSig, [u64; 4]) {
        let key = &k.keys[pr][ki as usize];
        let sig = key.sign(&dig(msg), 0);
        let sdig = crate::xmss::sig_digest(&sig, &k.vc.p);
        (
            BlockSig {
                proof: k.vc.prove(&key.public_key(), &dig(msg), &sig).unwrap(),
                path: k.reg.path(pr, ki),
            },
            sdig,
        )
    }

    #[test]
    fn signed_fold_binds_signer_and_block() {
        let (n, kbits) = (3usize, 2usize);
        let k = keys(n, kbits);
        let mode = Mode::Sched { era: 3 };
        let g_ch = [0u64; 4];
        let g_sig = [0u64; 4];
        let g = FoldBlock {
            slot: 0,
            height: 0,
            prev: [0; 4],
            id: fold_block_id(0, 0, false, [0; 4], false, [0; 4], g_ch, 0),
            sig: g_sig,
            contents_hash: g_ch,
            key_index: 0,
        };
        let mut bs = Vec::new();
        let mut evs = Vec::new();
        let mut prev = g.id;
        let mut prev_sig = g.sig;
        for s in 1..=4u64 {
            let ki = s / n as u64;
            let pr = (s % n as u64) as usize;
            let id = fold_block_id(s, s, true, prev, true, prev_sig, g_ch, ki);
            let (ev, sdig) = evidence(&k, pr, ki, id);
            let b = FoldBlock {
                slot: s,
                height: s,
                prev,
                id,
                sig: sdig,
                contents_hash: g_ch,
                key_index: ki,
            };
            prev = b.id;
            prev_sig = b.sig;
            bs.push(b);
            evs.push(ev);
        }
        let binding = |k: &Keys| SigBinding {
            verifier: crate::xmss::VerifierCircuit::build(crate::sphincs::Params::xmss("t", 2, 3)).data,
            n_fe: 2,
            root: k.reg.root(),
            pbits: k.reg.pbits,
            kbits,
        };
        let mut fp = FoldProver::new(n, mode, &g, BITS, Some(binding(&k))).unwrap();
        let mut st = fp.genesis_state().clone();
        let mut proof = None;
        for (b, ev) in bs[..3].iter().zip(&evs[..3]) {
            let next = native_step(n as u64, mode, &st, b).unwrap();
            let (_, p) = fp.step(&st, proof.as_ref(), b, Some(ev)).expect("signed step");
            assert_eq!(exposed_state(n, mode, &p).unwrap(), next);
            st = next;
            proof = Some(p);
        }
        let b = bs[3];
        let pr = (b.slot % n as u64) as usize;
        assert!(native_step(n as u64, mode, &st, &b).is_some());
        // Signed by the producer's key at another index: no proof.
        let (wrong_key, _) = evidence(&k, pr, b.key_index + 1, b.id);
        assert!(fails(|| fp.step(&st, proof.as_ref(), &b, Some(&wrong_key))));
        // Signed by another producer's key at the right index: no proof.
        let (wrong_prod, _) = evidence(&k, (pr + 1) % n, b.key_index, b.id);
        assert!(fails(|| fp.step(&st, proof.as_ref(), &b, Some(&wrong_prod))));
        // The right key, over another message: no proof.
        let (wrong_msg, _) = evidence(&k, pr, b.key_index, [9, 9, 9, 9]);
        assert!(fails(|| fp.step(&st, proof.as_ref(), &b, Some(&wrong_msg))));
        // The right evidence: proof.
        let ok = &evs[3];
        fp.step(&st, proof.as_ref(), &b, Some(ok)).expect("signed step");
    }

    #[test]
    fn fold_block_ids_bound() {
        let (g, bs) = chain(&[0]);
        let mode = Mode::K;
        let mut fp = FoldProver::new(3, mode, &g, BITS, None).unwrap();
        let st0 = fp.genesis_state().clone();
        let mut bad_b = bs[0];
        bad_b.id[0] ^= 1;
        assert!(fails(|| fp.step(&st0, None, &bad_b, None)));
    }

    #[test]
    fn fold_key_index_bound() {
        let (n, kbits) = (3usize, 2usize);
        let k = keys(n, kbits);
        let mode = Mode::Sched { era: 3 };
        let g_ch = [0u64; 4];
        let g_sig = [0u64; 4];
        let g = FoldBlock {
            slot: 0,
            height: 0,
            prev: [0; 4],
            id: fold_block_id(0, 0, false, [0; 4], false, [0; 4], g_ch, 0),
            sig: g_sig,
            contents_hash: g_ch,
            key_index: 0,
        };
        let binding = |k: &Keys| SigBinding {
            verifier: crate::xmss::VerifierCircuit::build(crate::sphincs::Params::xmss("t", 2, 3)).data,
            n_fe: 2,
            root: k.reg.root(),
            pbits: k.reg.pbits,
            kbits,
        };
        let mut fp = FoldProver::new(n, mode, &g, BITS, Some(binding(&k))).unwrap();
        let st0 = fp.genesis_state().clone();

        let honest_ki = 0;
        let forged_ki = honest_ki + 1;
        let pr = (1 % n as u64) as usize;
        let honest_id = fold_block_id(1, 1, true, g.id, true, g.sig, g_ch, honest_ki);
        let (honest_ev, honest_sdig) = evidence(&k, pr, honest_ki, honest_id);

        let honest_b = FoldBlock {
            slot: 1,
            height: 1,
            prev: g.id,
            id: honest_id,
            sig: honest_sdig,
            contents_hash: g_ch,
            key_index: honest_ki,
        };

        // Block whose id was hashed with honest_ki, but step ki is forged_ki
        let (forged_ev, forged_sdig) = evidence(&k, pr, forged_ki, honest_id);
        let forged_b = FoldBlock {
            slot: 1,
            height: 1,
            prev: g.id,
            id: honest_id,
            sig: forged_sdig,
            contents_hash: g_ch,
            key_index: forged_ki,
        };
        assert!(fails(|| fp.step(&st0, None, &forged_b, Some(&forged_ev))));

        // Honest block proves
        fp.step(&st0, None, &honest_b, Some(&honest_ev)).expect("honest signed step proves");
    }

    #[test]
    fn native_block_id_matches_circuit() {
        let (g, bs) = chain(&[0]);
        let mode = Mode::K;
        let mut fp = FoldProver::new(3, mode, &g, BITS, None).unwrap();
        let st0 = fp.genesis_state().clone();
        let b = bs[0];
        let (_, p) = fp.step(&st0, None, &b, None).unwrap();
        let state = exposed_state(3, mode, &p).unwrap();
        let expected_id = fold_block_id(b.slot, b.height, true, b.prev, true, g.sig, b.contents_hash, b.key_index);
        assert_eq!(state.tip_id, expected_id, "circuit tip_id matches native fold_block_id");
        assert_eq!(state.tip_id, b.id, "circuit tip_id matches block id");
    }

    #[test]
    fn parent_sig_bound() {
        let (g, bs) = chain(&[0, 0]);
        let mode = Mode::K;
        let mut fp = FoldProver::new(3, mode, &g, BITS, None).unwrap();
        let st0 = fp.genesis_state().clone();
        let (_, p0) = fp.step(&st0, None, &bs[0], None).unwrap();
        let st1 = exposed_state(3, mode, &p0).unwrap();

        // Block 1 with id hashed with wrong parent_sig
        let mut bad_b = bs[1];
        let mut wrong_parent_sig = st1.tip_sig;
        wrong_parent_sig[0] ^= 1;
        bad_b.id = fold_block_id(bad_b.slot, bad_b.height, true, bad_b.prev, true, wrong_parent_sig, bad_b.contents_hash, bad_b.key_index);

        assert!(fails(|| fp.step(&st1, Some(&p0), &bad_b, None)));

        // Honest block proves
        fp.step(&st1, Some(&p0), &bs[1], None).expect("honest block proves");
    }

    #[test]
    fn tip_sig_chained() {
        let (g, bs) = chain(&[0]);
        let mode = Mode::K;
        let mut fp = FoldProver::new(3, mode, &g, BITS, None).unwrap();
        let st0 = fp.genesis_state().clone();
        let b = bs[0];
        let (_, p) = fp.step(&st0, None, &b, None).unwrap();
        let state = exposed_state(3, mode, &p).unwrap();
        assert_eq!(state.tip_sig, b.sig, "exposed tip_sig equals block sig");
    }

    #[test]
    fn sig_digest_bound() {
        let (n, kbits) = (3usize, 2usize);
        let k = keys(n, kbits);
        let mode = Mode::Sched { era: 3 };
        let g_ch = [0u64; 4];
        let g_sig = [0u64; 4];
        let g = FoldBlock {
            slot: 0,
            height: 0,
            prev: [0; 4],
            id: fold_block_id(0, 0, false, [0; 4], false, [0; 4], g_ch, 0),
            sig: g_sig,
            contents_hash: g_ch,
            key_index: 0,
        };
        let binding = |k: &Keys| SigBinding {
            verifier: crate::xmss::VerifierCircuit::build(crate::sphincs::Params::xmss("t", 2, 3)).data,
            n_fe: 2,
            root: k.reg.root(),
            pbits: k.reg.pbits,
            kbits,
        };
        let mut fp = FoldProver::new(n, mode, &g, BITS, Some(binding(&k))).unwrap();
        let st0 = fp.genesis_state().clone();

        let ki = 0;
        let pr = (1 % n as u64) as usize;
        let id = fold_block_id(1, 1, true, g.id, true, g.sig, g_ch, ki);
        let (ev, sdig) = evidence(&k, pr, ki, id);

        let honest_b = FoldBlock {
            slot: 1,
            height: 1,
            prev: g.id,
            id,
            sig: sdig,
            contents_hash: g_ch,
            key_index: ki,
        };

        // Block whose sig wire differs from signature subproof digest
        let mut forged_b = honest_b;
        forged_b.sig[0] ^= 1;
        assert!(fails(|| fp.step(&st0, None, &forged_b, Some(&ev))));

        // Honest block proves
        fp.step(&st0, None, &honest_b, Some(&ev)).expect("honest signed step proves");
    }
}
