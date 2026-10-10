//! End-to-end demo: the Molt Petit consensus carrying signed key-rotation
//! transitions in block content, where the certificate is produced by running
//! ONE validator (see `spec.rs`) — the same generic code runs natively (the
//! proven function executing, matching `molt_petit::valid_chain`) and emits the
//! plonky2 circuit. Window density is fully included; no zkVM, pure plonky2 DSL.
//!
//! Run with (this machine's stable rustup toolchain; see `.cargo/config.toml`):
//!   ~/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/cargo run --release

use std::time::Instant;

use anyhow::Result;

use plonky2::field::types::PrimeField64;

use molt_petit::{
    produce_block_cert, quorum as mp_quorum, sigs_ok, valid_chain, validate_certified_chain,
    CertifiedChain, Chain, Crypto, Hash, SignedChain,
};

use plonky2::field::types::Field;

use molt_petit_keyrot::backend::{Circuit, Native};
use molt_petit_keyrot::crypto::{BlockRec, KeyRotCrypto};
use molt_petit_keyrot::keyset::KeySet;
use molt_petit_keyrot::poseidon_util::*;
use molt_petit_keyrot::pq_chain::transition_digest;
use molt_petit_keyrot::spec::{self, ChainWitness, Kind, RotData};
use molt_petit_keyrot::types::F;

const N: usize = 7;

/// The initial committee's secret keys (a key is just a field element; its
/// public key is `Poseidon(sk)[0]`).
fn initial_secrets() -> Vec<F> {
    (0..N as u64).map(|i| F::from_canonical_u64(100 + i)).collect()
}

fn build_chain(recs: &[BlockRec]) -> Chain {
    let mut chain = Chain::Nil;
    for rec in recs.iter().rev() {
        chain = Chain::Cons(rec.to_block(), Box::new(chain));
    }
    chain
}

fn catch<T>(f: impl FnOnce() -> Result<T>) -> bool {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).map_or(true, |r| r.is_err())
}

fn main() -> Result<()> {
    let n = N as u64;
    let threshold = mp_quorum(n) as usize; // ceil(2n/3) = 5 for n = 7
    assert_eq!(threshold as u64, spec::quorum(N));
    println!("Molt Petit x plonky2 key rotation  (n = {N}, quorum q = {threshold})");
    println!("one validator, two backends: native execution + plonky2 circuit\n");

    // ----- (1) Build the rotation witnesses (this also drives the key set). ----
    let mut secrets = initial_secrets();
    let mut set = KeySet::from_field_keys(N, secrets.iter().map(|sk| pk_of(*sk)));
    let init_slots = set.padded();
    let init_commitment = digest_to_hash(set.commitment().elements);
    let signer_idxs: Vec<usize> = (0..threshold).collect();

    let plan = [(6usize, 9001u64), (5, 9002), (6, 9003)];
    let mut rotations: Vec<RotData> = Vec::new();
    let mut rotation_contents: Vec<Hash> = Vec::new();
    for &(slot_idx, seed) in &plan {
        let prev_slots = set.padded();
        let prev_commitment = set.commitment();
        let old_pk = prev_slots[slot_idx];
        let new_sk = F::from_canonical_u64(seed);
        let new_pk = pk_of(new_sk);
        let digest = transition_digest(old_pk, new_pk, &prev_commitment);
        rotation_contents.push(digest_to_hash(digest));
        // The q signing members reveal knowledge of their secret keys (in the
        // certificate), captured before the replacement.
        let signer_secrets: Vec<F> = signer_idxs.iter().map(|&s| secrets[s]).collect();
        set.replace(old_pk, new_pk).expect("old key present");
        secrets[slot_idx] = new_sk;
        rotations.push(RotData {
            prev_slots,
            new_slots: set.padded(),
            old_pk,
            new_pk,
            replace_idx: slot_idx,
            signer_secrets,
            signer_idxs: signer_idxs.clone(),
        });
    }
    let final_commitment = digest_to_hash(set.commitment().elements);

    // Certified prefix: slots 0..=6. Block 0 genesis, 1..=3 rotations, 4..=6 no-op.
    let kinds = [
        Kind::Genesis,
        Kind::Rotation,
        Kind::Rotation,
        Kind::Rotation,
        Kind::Noop,
        Kind::Noop,
        Kind::Noop,
    ];
    let block_slots: Vec<u64> = vec![0, 1, 2, 3, 4, 5, 6];
    let witness = ChainWitness {
        init_slots: init_slots.clone(),
        block_slots: block_slots.clone(),
        rotations,
    };

    // ----- (2) Run the SAME validator natively. -----
    let mut nat = Native::new();
    let _ = spec::run(&mut nat, N, threshold, &kinds, &witness);
    let native_valid = nat.verdict();
    println!("native run of the validator (spec::run on Native backend) = {native_valid}");
    assert!(native_valid);

    // Cross-check the structural verdict against the proven molt_petit::valid_chain.
    let recs = build_recs(&block_slots, &kinds, init_commitment, &rotation_contents, final_commitment);
    let chain8 = {
        // full 8-block chain (prefix + the slot-7 suffix block) for valid_chain
        let mut all = recs.clone();
        let id7 = block_id(7, 7, Some(&recs[6].id), &final_commitment);
        all.push(BlockRec { slot: 7, height: 7, prev: Some(recs[6].id), id: id7, contents: final_commitment, key_index: 0 });
        all
    };
    let mp_valid = valid_chain(n, &build_chain(&chain8));
    println!("  molt_petit::valid_chain on the same chain = {mp_valid}  (agrees)");
    assert_eq!(native_valid, mp_valid);

    // ----- (3) Run the SAME validator as a plonky2 circuit -> the certificate. --
    println!("\nbuilding + proving the validator as a plonky2 circuit ...");
    let t = Instant::now();
    let mut cir = Circuit::new();
    let tip = spec::run(&mut cir, N, threshold, &kinds, &witness);
    cir.register_public_inputs(&[
        tip.slot, tip.height, tip.id[0], tip.id[1], tip.id[2], tip.id[3],
        tip.commitment[0], tip.commitment[1], tip.commitment[2], tip.commitment[3],
    ]);
    let (data, proof) = cir.into_data_and_proof()?;
    println!("  built + proved in {:.1?}", t.elapsed());
    println!("  proof size = {} bytes", proof.to_bytes().len());

    // The proof's public inputs prove the tip + committed key set.
    let tip_block = &chain8[6];
    assert_eq!(proof.public_inputs[spec::TIP_SLOT_OFFSET].to_canonical_u64(), tip_block.slot);
    assert_eq!(proof.public_inputs[spec::TIP_ID_OFFSET].to_canonical_u64(), tip_block.id.a);
    assert_eq!(proof.public_inputs[spec::SET_COMM_OFFSET].to_canonical_u64(), final_commitment.a);
    println!("  proof public inputs prove tip (slot {}, height {}) and committed key set \u{2713}", tip_block.slot, tip_block.height);

    // ----- (4) The certified light-client path. -----
    let producer_sk: Vec<F> = (0..N as u64).map(|i| F::from_canonical_u64(900 + i)).collect();
    let crypto = KeyRotCrypto::new(n, producer_sk, data.verifier_data());

    let chain_ok = valid_chain(n, &build_chain(&chain8));
    println!("\nconsensus chain: 8 blocks, slots 0..=7, 3 carry key rotations");
    println!("  valid_chain(n, chain) = {chain_ok}");
    assert!(chain_ok);

    let mut schain = SignedChain::SNil;
    for rec in chain8.iter().rev() {
        let b = rec.to_block();
        let sig = crypto.sign(&sk_handle(rec.slot % n), &b);
        schain = SignedChain::SCons(b, sig, Box::new(schain));
    }
    let sigs = sigs_ok(n, &crypto, &schain);
    println!("  sigs_ok(n, crypto, signed-chain) = {sigs}  (all 8 producer signatures verify)");
    assert!(sigs);

    let cert_handle = digest_to_hash(poseidon4(&[final_commitment_first(&set)]));
    let tail: Vec<BlockRec> = recs[1..=6].to_vec();
    crypto.register_cert(cert_handle, proof.clone(), tail);
    println!("\ncertificate = the validator proof (structure + window density + app-state)");
    println!("  cert_verify(cert) = {}", crypto.cert_verify(&cert_handle));

    let slot7 = &chain8[7];
    let produced = produce_block_cert(
        n, 0, slot7.slot, slot7.id, slot7.contents, slot7.key_index, sk_handle(0), &crypto, cert_handle,
        SignedChain::SNil,
    );
    let cc = match produced {
        CertifiedChain::Invalid => panic!("certified production failed"),
        cc => cc,
    };
    println!("  produce_block_cert -> certified chain produced");
    let cc_ok = validate_certified_chain(n, &crypto, &cc);
    println!("  validate_certified_chain(n, crypto, cc) = {cc_ok}  (light-client check)");
    assert!(cc_ok);

    // ----- (5) Negative: a sparse chain fails density in BOTH backends. -----
    println!("\n== same validator rejects bad chains in both modes ==");
    let sparse_kinds = [Kind::Genesis, Kind::Noop, Kind::Noop, Kind::Noop, Kind::Noop, Kind::Noop, Kind::Noop];
    let sparse = ChainWitness {
        init_slots: init_slots.clone(),
        block_slots: vec![0, 7, 8, 9, 10, 11, 12], // window [0,7) holds only block 0
        rotations: vec![],
    };
    let mut nat2 = Native::new();
    let _ = spec::run(&mut nat2, N, threshold, &sparse_kinds, &sparse);
    println!("  native verdict on sparse (density-violating) chain = {}  (want false)", nat2.verdict());
    assert!(!nat2.verdict());
    let circuit_accepts_sparse = !catch(|| {
        let mut c = Circuit::new();
        let _ = spec::run(&mut c, N, threshold, &sparse_kinds, &sparse);
        c.into_data_and_proof().map(|_| ())
    });
    println!("  plonky2 proof of the sparse chain succeeds = {circuit_accepts_sparse}  (want false)");
    assert!(!circuit_accepts_sparse);

    // ----- (6) Fool-proofs. -----
    println!("\n== fool-proofs ==");
    let b0 = recs[0].to_block();
    let sig0 = crypto.sign(&sk_handle(0), &b0);
    let wrong_key = crypto.verify(&crypto.key_for(1, 0), &b0, &sig0);
    println!("  block signature under wrong producer key accepted: {wrong_key}  (want false)");
    assert!(!wrong_key);
    let bogus = Hash { a: 1, b: 2, c: 3, d: 4 };
    println!("  cert_verify(unknown) = {}  (want false)", crypto.cert_verify(&bogus));
    assert!(!crypto.cert_verify(&bogus));

    // A forged transition signature is rejected by BOTH backends (same code).
    let forged = forged_rotation_witness(&signer_idxs);
    let forged_kinds = [Kind::Genesis, Kind::Rotation];
    let mut nat3 = Native::new();
    let _ = spec::run(&mut nat3, N, threshold, &forged_kinds, &forged);
    println!("  native verdict with a forged transition signature = {}  (want false)", nat3.verdict());
    assert!(!nat3.verdict());
    let circuit_accepts_forged = !catch(|| {
        let mut c = Circuit::new();
        let _ = spec::run(&mut c, N, threshold, &forged_kinds, &forged);
        c.into_data_and_proof().map(|_| ())
    });
    println!("  plonky2 proof with a forged transition signature succeeds = {circuit_accepts_forged}  (want false)");
    assert!(!circuit_accepts_forged);

    // ----- (7) The VERIFIED validator, run as a plonky2 circuit. -----
    // molt_petit::valid_chain_be is the backend-generic consensus validator in
    // the verified crate (Lean: Rust.valid_chain_be_validChain). Instantiated
    // with a plonky2 backend, the circuit literally executes that proven code.
    use molt_petit_keyrot::mp_circuit::{prove_valid_chain_be, BlockData};
    println!("\n== verified validator as a plonky2 circuit (molt_petit::valid_chain_be) ==");
    let blocks: Vec<BlockData> = chain8
        .iter()
        .map(|r| BlockData { slot: r.slot, height: r.height, prev: r.prev, id: r.id })
        .collect();
    let (vdata, vproof) = prove_valid_chain_be(n, threshold as u64, &blocks)?;
    vdata.verify(vproof.clone())?;
    println!("  proved valid_chain_be(chain) ✓  ({} bytes) \u{2014} the proven function ran in-circuit", vproof.to_bytes().len());

    // A density-violating chain: the verified validator circuit is unsatisfiable.
    let sparse_slots = [0u64, 7, 8, 9, 10, 11, 12];
    let mut sparse_blocks: Vec<BlockData> = Vec::new();
    let mut prev: Option<Hash> = None;
    for (h, &s) in sparse_slots.iter().enumerate() {
        let id = block_id(s, h as u64, prev.as_ref(), &final_commitment);
        sparse_blocks.push(BlockData { slot: s, height: h as u64, prev, id });
        prev = Some(id);
    }
    let rejected = catch(|| prove_valid_chain_be(n, threshold as u64, &sparse_blocks).map(|_| ()));
    println!("  sparse chain rejected by the verified validator circuit: {rejected}  (want true)");
    assert!(rejected);

    println!("\nall checks passed \u{2713}");
    Ok(())
}

/// Build the 7 prefix block records (native), mirroring what the circuit hashes.
fn build_recs(
    block_slots: &[u64],
    kinds: &[Kind],
    init_commitment: Hash,
    rotation_contents: &[Hash],
    final_commitment: Hash,
) -> Vec<BlockRec> {
    let mut recs = Vec::new();
    let mut prev_id: Option<Hash> = None;
    let mut rot_i = 0usize;
    for (i, kind) in kinds.iter().enumerate() {
        let slot = block_slots[i];
        let contents = match kind {
            Kind::Genesis => init_commitment,
            Kind::Rotation => {
                let c = rotation_contents[rot_i];
                rot_i += 1;
                c
            }
            Kind::Noop => final_commitment,
        };
        let id = block_id(slot, slot, prev_id.as_ref(), &contents);
        recs.push(BlockRec { slot, height: slot, prev: prev_id, id, contents, key_index: 0 });
        prev_id = Some(id);
    }
    recs
}

fn final_commitment_first(set: &KeySet) -> F {
    set.commitment().elements[0]
}

/// A one-rotation witness whose first co-signer's secret is forged (the attacker
/// does not know member 0's secret, so `Poseidon(sk)` won't match its pk).
fn forged_rotation_witness(signer_idxs: &[usize]) -> ChainWitness {
    let secrets = initial_secrets();
    let set = KeySet::from_field_keys(N, secrets.iter().map(|sk| pk_of(*sk)));
    let prev_slots = set.padded();
    let old_pk = prev_slots[6];
    let new_pk = pk_of(F::from_canonical_u64(7777));
    let mut signer_secrets: Vec<F> = vec![F::from_canonical_u64(666_666)]; // forged signer 0
    for &s in &signer_idxs[1..] {
        signer_secrets.push(secrets[s]);
    }
    let mut new_slots = prev_slots.clone();
    new_slots[6] = new_pk;
    ChainWitness {
        init_slots: set.padded(),
        block_slots: vec![0, 1],
        rotations: vec![RotData {
            prev_slots,
            new_slots,
            old_pk,
            new_pk,
            replace_idx: 6,
            signer_secrets,
            signer_idxs: signer_idxs.to_vec(),
        }],
    }
}
