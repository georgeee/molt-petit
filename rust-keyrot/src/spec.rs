//! The consensus validator, written ONCE over the [`Backend`] abstraction.
//!
//! [`run`] is a single generic function. Instantiated with [`crate::backend::Native`]
//! it *executes* (returning the validity bit, matching `molt_petit::valid_chain`);
//! instantiated with [`crate::backend::Circuit`] it *emits the plonky2 circuit*.
//! Same source, so the circuit cannot diverge from the native logic.
//!
//! It mirrors the proven Rust `molt_petit::valid_chain` clause for clause:
//!
//! * `genesis_ok` — block 0 has height 0 and no parent (modelled by giving it
//!   height `0` and the zero parent-id);
//! * `child_ok` — `height == parent.height + 1`, `parent.slot < child.slot`, and
//!   `prev == parent.id` (the last is enforced by *defining* each id as the
//!   Poseidon commitment of its fields including the parent id);
//! * `matured_dense` — every matured window `[u, u+n)` (base `u = 0` plus the
//!   anchors `u = slot_i + 1`) has at least `quorum(n)` blocks.
//!
//! Folded in (the application layer, not part of the Lean proof): each rotation
//! block's content is the transition digest of a threshold-signed `old -> new`
//! replacement, and the committed key set evolves accordingly.

use plonky2::field::types::Field;

use crate::backend::Backend;
use crate::types::F;

/// Public-input layout the circuit exposes: the proven tip + committed state.
pub const TIP_SLOT_OFFSET: usize = 0;
pub const TIP_HEIGHT_OFFSET: usize = 1;
pub const TIP_ID_OFFSET: usize = 2; // .. 6
pub const SET_COMM_OFFSET: usize = 6; // .. 10
pub const STATE_LEN: usize = 10;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Genesis,
    Rotation,
    Noop,
}

/// Witness for one rotation block. The threshold authorization is by proof of
/// knowledge of secret keys: `signer_secrets[k]` is the secret whose public key
/// `Poseidon(sk)[0]` must equal current member `signer_idxs[k]`.
pub struct RotData {
    pub prev_slots: Vec<F>,
    pub new_slots: Vec<F>,
    pub old_pk: F,
    pub new_pk: F,
    pub replace_idx: usize,
    pub signer_secrets: Vec<F>,
    pub signer_idxs: Vec<usize>,
}

/// Full witness for the chain being validated.
pub struct ChainWitness {
    pub init_slots: Vec<F>,
    pub block_slots: Vec<u64>,
    pub rotations: Vec<RotData>, // one per Rotation block, in order
}

/// The validated tip + committed key set (the circuit registers these).
pub struct Tip<B: Backend> {
    pub slot: B::Num,
    pub height: B::Num,
    pub id: [B::Num; 4],
    pub commitment: [B::Num; 4],
}

/// `quorum(n) = ceil(2n/3)`, as in `molt_petit::quorum`.
pub fn quorum(n: usize) -> u64 {
    (n as u64 + n as u64 + 2) / 3
}

/// Run the validator. Asserts every clause; returns the tip.
pub fn run<B: Backend>(
    be: &mut B,
    n: usize,
    threshold: usize,
    kinds: &[Kind],
    w: &ChainWitness,
) -> Tip<B> {
    assert_eq!(kinds[0], Kind::Genesis);
    let len = kinds.len();
    let q = quorum(n);

    let zero = be.constant(0);
    let one = be.constant(1);

    let init_keys: Vec<B::Num> = w.init_slots.iter().map(|k| be.input(*k)).collect();
    let mut running = be.poseidon(&init_keys);

    let mut slots: Vec<B::Num> = Vec::with_capacity(len);
    let mut prev_height = zero;
    let mut prev_slot = zero;
    let mut prev_id = [zero; 4];
    let mut rot_i = 0usize;

    for (i, kind) in kinds.iter().enumerate() {
        let slot = be.input(F::from_canonical_u64(w.block_slots[i]));
        slots.push(slot);

        // genesis_ok / child_ok structural transition.
        let height = if i == 0 {
            zero // genesis_ok: height 0
        } else {
            let slot_ok = be.lt(prev_slot, slot); // parent.slot < child.slot
            be.assert(slot_ok);
            be.add(prev_height, one) // height == parent.height + 1
        };

        // Application-state update imposed by this block's content.
        let contents: [B::Num; 4] = match kind {
            Kind::Genesis | Kind::Noop => running,
            Kind::Rotation => {
                let r = &w.rotations[rot_i];
                rot_i += 1;
                apply_rotation(be, n, threshold, r, &running)
                    .map(|(c, new_running)| {
                        running = new_running;
                        c
                    })
                    .expect("rotation arity")
            }
        };

        // Block id = Poseidon(slot, height, prev_id, contents). Defining the id
        // this way *is* the `prev == parent.id` clause of child_ok.
        let mut idin = vec![slot, height];
        idin.extend_from_slice(&prev_id);
        idin.extend_from_slice(&contents);
        let id = be.poseidon(&idin);

        prev_height = height;
        prev_slot = slot;
        prev_id = id;
    }

    let tip = Tip {
        slot: prev_slot,
        height: prev_height,
        id: prev_id,
        commitment: running,
    };

    // matured_dense(c, lo = 0, tip_slot, n): base window u = 0 plus the anchors.
    enforce_window(be, zero, &slots, n, q, tip.slot);
    for i in 0..len {
        let u = be.add(slots[i], one);
        enforce_window(be, u, &slots, n, q, tip.slot);
    }

    tip
}

/// One rotation step: bind prev keys to the running commitment, apply a single
/// threshold-signed `old -> new` replacement, return `(content, new_running)`.
/// `content` is the transition digest. Returns `None` only on witness arity bugs.
fn apply_rotation<B: Backend>(
    be: &mut B,
    n: usize,
    threshold: usize,
    r: &RotData,
    running: &[B::Num; 4],
) -> Option<([B::Num; 4], [B::Num; 4])> {
    if r.prev_slots.len() != n || r.new_slots.len() != n {
        return None;
    }
    let zero = be.constant(0);
    let one = be.constant(1);

    let prev_keys: Vec<B::Num> = r.prev_slots.iter().map(|k| be.input(*k)).collect();
    let new_keys: Vec<B::Num> = r.new_slots.iter().map(|k| be.input(*k)).collect();
    let old_pk = be.input(r.old_pk);
    let new_pk = be.input(r.new_pk);

    // prev_keys hash to the running commitment.
    let comp = be.poseidon(&prev_keys);
    for j in 0..4 {
        let eq = be.is_eq(comp[j], running[j]);
        be.assert(eq);
    }

    // One-hot replacement selector.
    let sel: Vec<B::Bool> = (0..n).map(|j| be.input_bool(j == r.replace_idx)).collect();
    let sel_sum = sum_bools(be, &sel);
    let one_hot_ok = be.is_eq(sel_sum, one);
    be.assert(one_hot_ok);

    // Selected slot holds old_pk; new_keys = prev with that slot set to new_pk.
    let sel_old = dot(be, &sel, &prev_keys);
    let sel_old_ok = be.is_eq(sel_old, old_pk);
    be.assert(sel_old_ok);
    for j in 0..n {
        let delta = be.sub(new_pk, prev_keys[j]);
        let bn = be.bool_to_num(sel[j]);
        let sd = be.mul(bn, delta);
        let expected = be.add(prev_keys[j], sd);
        let eq = be.is_eq(new_keys[j], expected);
        be.assert(eq);
    }

    // Transition digest = content = Poseidon(old, new, prev_commitment).
    let mut din = vec![old_pk, new_pk];
    din.extend_from_slice(running);
    let digest = be.poseidon(&din);

    // Threshold authorization by proof of knowledge: q distinct current members
    // each demonstrate knowledge of the secret key behind their public key
    // (pk = Poseidon(sk)[0]). The knowledge — proven inside this certificate,
    // whose public inputs bind this very transition — IS the signature; there
    // is no dedicated signature scheme.
    let mut usage: Vec<B::Num> = vec![zero; n];
    for k in 0..threshold {
        let ssel: Vec<B::Bool> = (0..n).map(|j| be.input_bool(j == r.signer_idxs[k])).collect();
        let ssum = sum_bools(be, &ssel);
        let ssum_ok = be.is_eq(ssum, one);
        be.assert(ssum_ok);
        let signer_pk = dot(be, &ssel, &prev_keys);
        let sk = be.input(r.signer_secrets[k]);
        let pk_computed = be.poseidon(&[sk])[0];
        let knows = be.is_eq(pk_computed, signer_pk);
        be.assert(knows);
        for j in 0..n {
            let bn = be.bool_to_num(ssel[j]);
            usage[j] = be.add(usage[j], bn);
        }
    }
    // Each member used at most once: usage * (usage - 1) == 0.
    for u in &usage {
        let um1 = be.sub(*u, one);
        let prod = be.mul(*u, um1);
        let z = be.is_eq(prod, zero);
        be.assert(z);
    }

    let new_running = be.poseidon(&new_keys);
    Some((digest, new_running))
}

/// Enforce one `matured_dense` clause: matured window => dense.
fn enforce_window<B: Backend>(
    be: &mut B,
    u: B::Num,
    slots: &[B::Num],
    n: usize,
    quorum: u64,
    tip_slot: B::Num,
) {
    let one = be.constant(1);
    let zero = be.constant(0);
    let n_t = be.constant(n as u64);
    let q = be.constant(quorum);
    let u_plus_n = be.add(u, n_t);

    // window_count(u) = Σ_j [ u <= slot_j < u + n ]
    let mut count = zero;
    for s in slots {
        let s_lt_u = be.lt(*s, u);
        let ge_u = be.not(s_lt_u);
        let s_lt_un = be.lt(*s, u_plus_n);
        let in_w = be.and(ge_u, s_lt_un);
        let in_w_n = be.bool_to_num(in_w);
        count = be.add(count, in_w_n);
    }

    // matured = (u + n <= tip_slot + 1) = not(tip_slot < u + n - 1)
    let u_plus_n_m1 = be.sub(u_plus_n, one);
    let not_matured = be.lt(tip_slot, u_plus_n_m1);
    // dense = (quorum <= count) = not(count < quorum)
    let cnt_lt_q = be.lt(count, q);
    let dense = be.not(cnt_lt_q);
    // matured => dense  ==  (not matured) or dense
    let implied = be.or(not_matured, dense);
    be.assert(implied);
}

fn sum_bools<B: Backend>(be: &mut B, bs: &[B::Bool]) -> B::Num {
    let mut acc = be.constant(0);
    for b in bs {
        let bn = be.bool_to_num(*b);
        acc = be.add(acc, bn);
    }
    acc
}

fn dot<B: Backend>(be: &mut B, sel: &[B::Bool], vals: &[B::Num]) -> B::Num {
    let mut acc = be.constant(0);
    for (b, v) in sel.iter().zip(vals) {
        let bn = be.bool_to_num(*b);
        let p = be.mul(bn, *v);
        acc = be.add(acc, p);
    }
    acc
}
