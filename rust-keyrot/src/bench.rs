//! Performance benchmark: the Molt Petit consensus bundled with plonky2 and
//! **production-shaped SPHINCS+ (over Poseidon)** signatures — the post-quantum,
//! hash-based, NIST SLH-DSA parameter sets (see [`molt_petit_keyrot::sphincs`]).
//!
//! A signature is now a real SPHINCS+ blob (WOTS+ / FORS / hypertree), not a
//! proof-of-knowledge. Signing is a cheap host operation; *verification* is the
//! heavy side, done inside the circuit. Two regimes, as in the paper:
//!   * INLINE   — the certificate verifies each signature's gates directly.
//!   * RECURSIVE — each signer submits a plonky2 subproof that their signature
//!                 verifies (secret key never shared); the certificate
//!                 recursively verifies those subproofs. Privacy-preserving and
//!                 the unit that aggregation trees scale.
//!
//! Measures, for n = 7, q = ceil(2n/3) = 5:
//!   0. Per-signature cost across NIST sets (host sign, in-circuit verify).
//!   1. Block creation = host SPHINCS+ sign (no proof).
//!   2. One signature subproof (the recursively-verified unit).
//!   3. Recursively verifying one subproof (the recursion floor).
//!   4. Inline certificate over 4 blocks (consensus + density + K verifies).
//!   5. Recursive certificate over 4 blocks (consensus + K subproofs).
//!   6-10. Medians, recursive-batch scaling, aggregation strategies (8/64/2048).
//!   BENCH_FOLD=1: the fold certificate (one cyclic proof per block).
//!
//! Run:  ~/.rustup/.../bin/cargo run --release --bin bench

use std::time::{Duration, Instant};

use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::Hasher;
use plonky2::plonk::proof::ProofWithPublicInputs;

use molt_petit::{quorum, Hash};
use molt_petit_keyrot::mp_circuit::{
    aggregate_n, big_over_inner, prove_batch_recursive, prove_chain_with_inline_sphincs,
    prove_chain_with_inline_xmss, prove_valid_chain_be, Agg2, BlockData,
};
use molt_petit_keyrot::poseidon_util::block_id;
use molt_petit_keyrot::sphincs::{self, Key, Params, Sig, VerifierCircuit};
use molt_petit_keyrot::types::{C, D, F};
use molt_petit_keyrot::xmss;

const N: usize = 7;
type Pf = ProofWithPublicInputs<F, C, D>;

fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}
fn median(mut v: Vec<Duration>) -> Duration {
    v.sort();
    v[v.len() / 2]
}
fn digest(i: u64) -> [F; 4] {
    PoseidonHash::hash_no_pad(&[F::from_canonical_u64(i), F::from_canonical_u64(2)]).elements
}

/// A short chain of `nb` blocks (consensus structure; window density vacuous for
/// nb < n). The block ids chain via `block_id` so the link rules hold.
fn chain(nb: u64) -> Vec<BlockData> {
    let mut prev: Option<Hash> = None;
    let mut v = Vec::new();
    for s in 0..nb {
        let id = block_id(s, s, prev.as_ref(), &Hash { a: s + 1, b: 0, c: 0, d: 0 });
        v.push(BlockData { slot: s, height: s, prev, id });
        prev = Some(id);
    }
    v
}

/// Per-signature SPHINCS+ cost for one NIST set: host sign + in-circuit verify.
fn sig_table_row(p: Params) -> Result<()> {
    // median host keygen
    let mut kg = Vec::new();
    for s in 0..5u64 {
        let t = Instant::now();
        let _ = Key::keygen(p.clone(), s);
        kg.push(t.elapsed());
    }
    let keygen = median(kg);
    let key = Key::keygen(p.clone(), 12345);
    let pk = key.public_key();
    let d = digest(1);
    // median host sign
    let mut ts = Vec::new();
    for _ in 0..5 {
        let t = Instant::now();
        let _ = key.sign(&d);
        ts.push(t.elapsed());
    }
    let sign = median(ts);
    let sig = key.sign(&d);
    assert!(sphincs::verify(&pk, &d, &sig, &p), "native verify");
    let nfe: usize = sig.fors_sk.iter().map(|x| x.len()).sum::<usize>()
        + sig.fors_auth.iter().flatten().map(|x| x.len()).sum::<usize>()
        + sig.wots_sig.iter().flatten().map(|x| x.len()).sum::<usize>()
        + sig.hyper_auth.iter().flatten().map(|x| x.len()).sum::<usize>();
    let t = Instant::now();
    let vc = VerifierCircuit::build(p.clone());
    let build = t.elapsed();
    let _ = vc.prove(&pk, &d, &sig)?; // warm
    let t = Instant::now();
    let proof = vc.prove(&pk, &d, &sig)?;
    let prove = t.elapsed();
    println!(
        "   {:>5}: keygen {:>6.0} ms, sign {:>7.0} ms, sig {:>3} KiB | verify 2^{:<2} build {:>5.0} ms prove {:>6.0} ms ({} KB)",
        p.name,
        ms(keygen),
        ms(sign),
        nfe * 8 / 1024,
        vc.data.common.degree().trailing_zeros(),
        ms(build),
        ms(prove),
        proof.to_bytes().len() / 1024,
    );
    Ok(())
}

/// Per-signature **XMSS** cost (host keygen/sign + in-circuit verify), to
/// compare against the SPHINCS+ rows. XMSS keygen builds the whole tree of
/// `2^h` WOTS+ leaves (timed once — it is the stateful scheme's real cost),
/// whereas the in-circuit verify is a single WOTS+ check plus an `h`-node
/// Merkle climb — no FORS, no hypertree.
fn xmss_table_row(label: &str, p: Params) -> Result<()> {
    let t = Instant::now();
    let key = xmss::Key::keygen(p.clone(), 12345);
    let keygen = t.elapsed();
    let pk = key.public_key();
    let d = digest(1);
    let mut ts = Vec::new();
    for leaf in 0..5u64 {
        let t = Instant::now();
        let _ = key.sign(&d, leaf);
        ts.push(t.elapsed());
    }
    let sign = median(ts);
    let sig = key.sign(&d, 0);
    assert!(xmss::verify(&pk, &d, &sig, &p), "native verify");
    let nfe: usize = sig.wots_sig.iter().map(|x| x.len()).sum::<usize>()
        + sig.auth.iter().map(|x| x.len()).sum::<usize>();
    let t = Instant::now();
    let vc = xmss::VerifierCircuit::build(p.clone());
    let build = t.elapsed();
    let _ = vc.prove(&pk, &d, &sig)?; // warm
    let t = Instant::now();
    let proof = vc.prove(&pk, &d, &sig)?;
    let prove = t.elapsed();
    println!(
        "   {:>12}: keygen {:>7.0} ms, sign {:>4.1} ms, sig {:>4.1} KiB | verify 2^{:<2} build {:>5.0} ms prove {:>6.0} ms ({} KB)",
        label,
        ms(keygen),
        ms(sign),
        nfe as f64 * 8.0 / 1024.0,
        vc.data.common.degree().trailing_zeros(),
        ms(build),
        ms(prove),
        proof.to_bytes().len() / 1024,
    );
    Ok(())
}

/// Full XMSS-over-Poseidon benchmark mirroring the SPHINCS+ integration sections
/// (subproof, recursion floor, inline + recursive certificate, aggregation tree),
/// using the SAME recursion/aggregation machinery with the much smaller XMSS
/// verifier as the leaf circuit. XMSS-128, height 11 → 2048 one-time leaves (so a
/// single key covers the 2048-subproof test; distinct messages need distinct
/// leaves, as XMSS is one-time). Gated by BENCH_XMSS=1.
fn xmss_bench() -> Result<()> {
    let threshold = quorum(N as u64) as usize;
    let p = Params::xmss("xmss-128 h11", 2, 11);
    println!("\n=== XMSS over Poseidon — full benchmark ({}, SPHINCS+-table analogue) ===", p.name);
    let key = xmss::Key::keygen(p.clone(), 999);
    let pk = key.public_key();

    let mut sg = Vec::new();
    for i in 0..9u64 {
        let t = Instant::now();
        let _ = key.sign(&digest(i), i);
        sg.push(t.elapsed());
    }
    println!("1. Block creation — host XMSS sign (median): {:.2} ms", ms(median(sg)));

    let t = Instant::now();
    let vc = xmss::VerifierCircuit::build(p.clone());
    let vc_build = t.elapsed();
    let leaf: Pf = vc.prove(&pk, &digest(0), &key.sign(&digest(0), 0))?;
    let _ = vc.prove(&pk, &digest(1), &key.sign(&digest(1), 1))?; // warm
    let t = Instant::now();
    let sp = vc.prove(&pk, &digest(2), &key.sign(&digest(2), 2))?;
    println!(
        "2. One signature SUBPROOF: degree 2^{}, build {:.0} ms, PROVE {:.0} ms, proof {} KB",
        vc.data.common.degree().trailing_zeros(),
        ms(vc_build),
        ms(t.elapsed()),
        sp.to_bytes().len() / 1024
    );

    let (rb, rp, rd) = {
        let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
        let pt = b.add_virtual_proof_with_pis(&vc.data.common);
        let vd = b.constant_verifier_data(&vc.data.verifier_only);
        b.verify_proof::<C>(&pt, &vd, &vc.data.common);
        let t = Instant::now();
        let data = b.build::<C>();
        let build = t.elapsed();
        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&pt, &leaf)?;
        let t = Instant::now();
        let _ = data.prove(pw)?;
        (build, t.elapsed(), data.common.degree())
    };
    println!(
        "3. Verify ONE subproof recursively (recursion floor): degree 2^{}, build {:.0} ms, PROVE {:.0} ms",
        rd.trailing_zeros(),
        ms(rb),
        ms(rp)
    );

    let xtriples = |k: usize| -> Vec<(Vec<F>, [F; 4], xmss::Sig)> {
        (0..k as u64).map(|i| (pk.clone(), digest(i), key.sign(&digest(i), i))).collect()
    };
    let xsubproofs = |k: usize| -> Result<Vec<Pf>> {
        (0..k as u64).map(|i| vc.prove(&pk, &digest(i), &key.sign(&digest(i), i))).collect()
    };

    let c7 = chain(7);
    for &spb in &[1usize, 2] {
        let sigs = xtriples(4 * spb);
        let t = Instant::now();
        let (data, proof) = prove_chain_with_inline_xmss(&p, &sigs, N as u64, threshold as u64, &c7)?;
        if spb == 1 {
            println!("4. INLINE certificate — 4 blocks, consensus + density + K inline XMSS verifies");
        }
        println!(
            "   {} sig/block ({} total): build+PROVE {:.1} s, degree 2^{}, proof {} KB",
            spb,
            4 * spb,
            t.elapsed().as_secs_f64(),
            data.common.degree().trailing_zeros(),
            proof.to_bytes().len() / 1024
        );
    }

    let c4 = chain(4);
    let sp8 = xsubproofs(8)?;
    let t = Instant::now();
    let (data, proof) = prove_batch_recursive(&vc.data, &sp8, N as u64, threshold as u64, &c4)?;
    println!(
        "5. RECURSIVE certificate — 4 blocks, 8 subproofs verified + consensus: build+PROVE {:.1} s, degree 2^{}, proof {} KB",
        t.elapsed().as_secs_f64(),
        data.common.degree().trailing_zeros(),
        proof.to_bytes().len() / 1024
    );

    println!("6. Aggregation tree (one leaf reused — timing is leaf-independent):");
    for &leaves in &[8usize, 64, 2048] {
        let levels = (leaves as f64).log2() as usize;
        let mut cur = leaf.clone();
        let mut spine: Vec<Agg2> = Vec::new();
        let mut node_times = Vec::new();
        let mut build_total = Duration::ZERO;
        for _ in 0..levels {
            let tb = Instant::now();
            let agg = if spine.is_empty() {
                Agg2::build(&vc.data)
            } else {
                Agg2::build(&spine.last().unwrap().data)
            };
            build_total += tb.elapsed();
            let t = Instant::now();
            let pnode = agg.prove(&cur, &cur)?;
            node_times.push(t.elapsed());
            cur = pnode;
            spine.push(agg);
        }
        let t = Instant::now();
        let _ = big_over_inner(&spine.last().unwrap().data, &cur, N as u64, threshold as u64, &c4)?;
        let c_big = t.elapsed();
        let crit = node_times.iter().map(|d| d.as_secs_f64()).sum::<f64>() + c_big.as_secs_f64();
        println!(
            "   {:>4} subproofs: {} levels, node 2^{}, tree build {:.1} s (one-time), parallel critical path ≈ {:.1} s",
            leaves,
            levels,
            spine.last().unwrap().data.common.degree().trailing_zeros(),
            build_total.as_secs_f64(),
            crit
        );
    }
    Ok(())
}

/// The recursive (fold) certificate: one cyclic proof per block, each running
/// the verified `cert_step_*_be` and verifying the previous proof. Prints a
/// recursion-floor calibration row first, so the fold rows can be read against
/// the published table on other hardware.
fn fold_bench() -> Result<()> {
    use molt_petit_keyrot::fold_circuit::{demo_chain, exposed_state, native_step, FoldProver, Mode};
    use plonky2::gates::noop::NoopGate;

    println!("\nFold certificate (cyclic recursion, verified cert_step_*_be per block)");
    // Calibration: verify one 2^13-row proof inside a 2^12-row circuit, as in
    // the table's recursion-floor row.
    let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    while b.num_gates() < (1 << 13) - 200 {
        b.add_gate(NoopGate, vec![]);
    }
    let inner = b.build::<C>();
    let ip = inner.prove(PartialWitness::new())?;
    let mut ob = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    let pt = ob.add_virtual_proof_with_pis(&inner.common);
    let vd = ob.constant_verifier_data(&inner.verifier_only);
    ob.verify_proof::<C>(&pt, &vd, &inner.common);
    let outer = ob.build::<C>();
    let mut v = vec![];
    for _ in 0..5 {
        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&pt, &ip)?;
        let t = Instant::now();
        outer.prove(pw)?;
        v.push(t.elapsed());
    }
    println!(
        "   calibration: recursion floor (verify one 2^{} proof): degree 2^{}, PROVE {:.3} s (median of 5)",
        inner.common.degree_bits(),
        outer.common.degree_bits(),
        median(v).as_secs_f64()
    );

    let steps = 2 * N as u64 + 2;
    for (label, mode) in [("mode 1 (K)", Mode::K), ("mode 2 (Sched, era = n)", Mode::Sched { era: N as u64 }), ("mode 3 (Lock)", Mode::Lock)] {
        let (g, bs) = demo_chain(N, steps);
        let t = Instant::now();
        let mut fp = FoldProver::new(N, mode, &g, 12)?;
        let shape = t.elapsed();
        let mut st = fp.genesis_state().clone();
        let mut proof: Option<Pf> = None;
        let (mut tb, mut tp, mut tv) = (vec![], vec![], vec![]);
        let mut degree = 0;
        for blk in &bs {
            let next = native_step(N as u64, mode, &st, blk).expect("native accepts");
            let (data, p) = fp.step(&st, proof.as_ref(), blk)?;
            tb.push(fp.last_build);
            tp.push(fp.last_prove);
            let t = Instant::now();
            data.verify(p.clone())?;
            tv.push(t.elapsed());
            degree = data.common.degree_bits();
            assert_eq!(exposed_state(N, mode, &p)?, next);
            st = next;
            proof = Some(p);
        }
        let bytes = proof.as_ref().map(|p| p.to_bytes().len()).unwrap_or(0);
        println!(
            "   {label}: n = {N}, {steps} blocks, step circuit {} gates -> degree 2^{degree}; shape fixed in {:.1} s; \
             per block PROVE {:.2} s (median; circuit rebuild {:.2} s, a prototype artifact), verify {:.1} ms, proof {} KiB; state == native fold at every block",
            fp.step_gates,
            shape.as_secs_f64(),
            median(tp).as_secs_f64(),
            median(tb).as_secs_f64(),
            ms(median(tv)),
            bytes / 1024
        );
    }
    Ok(())
}

fn main() -> Result<()> {
    // BENCH_FOLD=1 runs ONLY the fold-certificate section.
    if std::env::var("BENCH_FOLD").is_ok() {
        return fold_bench();
    }
    let threshold = quorum(N as u64) as usize;
    println!("Molt Petit × plonky2 — performance (n = {N}, quorum q = {threshold})");
    println!("SPHINCS+ over Poseidon (NIST SLH-DSA sets), Poseidon-Goldilocks\n");

    // -- 0. Per-signature cost across ALL FOUR NIST parameter sets -------------
    // Threads are governed by RAYON_NUM_THREADS (no in-code cap), so run.sh can
    // sweep this table at 1 core and at all cores. BENCH_SIGTABLE=1 runs *only*
    // this section (a cheap single-core pass without the heavy integration).
    let nthreads = std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "all".into());
    println!("0. Per-signature SPHINCS+ cost (host sign + single in-circuit verify)");
    println!("   [RAYON_NUM_THREADS = {nthreads}]");
    for p in [Params::s128s(), Params::s128f(), Params::s256s(), Params::s256f()] {
        sig_table_row(p)?;
    }
    println!(
        "\n   XMSS over Poseidon (single Merkle tree of WOTS+ leaves; no FORS, no hypertree)"
    );
    println!("   — same WOTS+/Merkle gadgets, for an apples-to-apples comparison:");
    for (label, n_fe, h) in
        [("xmss-128 h10", 2, 10), ("xmss-128 h16", 2, 16), ("xmss-256 h10", 4, 10)]
    {
        xmss_table_row(label, Params::xmss(label, n_fe, h))?;
    }
    if std::env::var("BENCH_XMSS").is_ok() {
        xmss_bench()?;
        return Ok(());
    }
    if std::env::var("BENCH_SIGTABLE").is_ok() {
        return Ok(());
    }

    // -- ES256 (ECDSA P-256 / passkey signature) verification in-circuit --------
    // The CLASSICAL signature behind passkeys / FIDO2 / WebAuthn (COSE alg -7), a
    // foreign-field circuit (256-bit P-256 emulated over Goldilocks). Mirrors the
    // Plonky3 ES256 section so the two stacks compare apples-to-apples.
    // BENCH_ES256=1 runs ONLY this section (skips the heavy SPHINCS+ pipeline).
    if std::env::var("BENCH_ES256").is_ok() {
        use molt_petit_keyrot::es256::circuit as es256;
        println!("\nES256 = ECDSA over NIST P-256 + SHA-256 (passkey / FIDO2 / WebAuthn, COSE alg -7)");
        println!(
            "  foreign-field circuit: 256-bit P-256 emulated over Goldilocks, B={} bits/limb, K={} limbs",
            es256::B,
            es256::K
        );
        println!("  (SHA-256 of the message is NOT in-circuit — z is a public input)");
        let (eq, esig, ez) = es256::demo_signature();

        // one verification subproof (build + prove are coupled per signature)
        let t = Instant::now();
        let (edata, eproof) = es256::build_and_prove(&eq, &esig, &ez)?;
        let leaf_dt = t.elapsed();
        edata.verify(eproof.clone())?;
        println!(
            "  verify ONE ES256 signature: degree 2^{}, build+PROVE {:.1} s, proof {} KB",
            edata.common.degree().trailing_zeros(),
            leaf_dt.as_secs_f64(),
            eproof.to_bytes().len() / 1024
        );

        // recursion floor: recursively verify one ES256 subproof
        let (rec_build, rec_prove, rec_deg) = {
            let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
            let pt = b.add_virtual_proof_with_pis(&edata.common);
            let vd = b.constant_verifier_data(&edata.verifier_only);
            b.verify_proof::<C>(&pt, &vd, &edata.common);
            let t = Instant::now();
            let data = b.build::<C>();
            let build = t.elapsed();
            let mut pw = PartialWitness::new();
            pw.set_proof_with_pis_target(&pt, &eproof)?;
            let t = Instant::now();
            let _ = data.prove(pw)?;
            (build, t.elapsed(), data.common.degree())
        };
        println!(
            "  recursion floor (verify one ES256 subproof): degree 2^{}, build {:.1} s, PROVE {:.1} s",
            rec_deg.trailing_zeros(),
            rec_build.as_secs_f64(),
            rec_prove.as_secs_f64()
        );

        // one 2-to-1 aggregation node (ES256 leaves) + extrapolation to 64 / 2048
        let node = Agg2::build(&edata);
        let _ = node.prove(&eproof, &eproof)?; // warm
        let t = Instant::now();
        let nproof = node.prove(&eproof, &eproof)?;
        let node_dt = t.elapsed();
        println!(
            "  one 2-to-1 aggregation node (ES256 leaves): degree 2^{}, PROVE {:.1} s, node proof {} KB",
            node.data.common.degree().trailing_zeros(),
            node_dt.as_secs_f64(),
            nproof.to_bytes().len() / 1024
        );
        let (leaf_s, node_s) = (leaf_dt.as_secs_f64(), node_dt.as_secs_f64());
        for k in [64usize, 2048] {
            let depth = (k as f64).log2().ceil() as usize;
            let seq = k as f64 * leaf_s + (k - 1) as f64 * node_s;
            let crit = leaf_s + depth as f64 * node_s;
            println!(
                "  aggregate {k} ES256 verifications ({depth}-level tree, extrap.): sequential \u{2248} {:.0} s, parallel critical-path \u{2248} {:.0} s",
                seq, crit
            );
        }
        return Ok(());
    }

    // The primary parameter set for the integration sections: NIST L1 "small"
    // (the smallest in-circuit verifier, 2^13 — the practical choice).
    let p = Params::s128s();
    let key = Key::keygen(p.clone(), 999);
    let pk = key.public_key();
    let sig0 = key.sign(&digest(0));

    // -- 1. Block creation: just the host SPHINCS+ signature -------------------
    let mut s = Vec::new();
    for i in 0..9u64 {
        let t = Instant::now();
        let _ = key.sign(&digest(i));
        s.push(t.elapsed());
    }
    println!("\n1. Block creation (no proof) — host SPHINCS+-{} signature", p.name);
    println!("   SIGN (median): {:.0} ms   (post-quantum, hash-based; no proving at sign time)", ms(median(s)));

    // The per-signature subproof circuit (built once, reused as the inner
    // circuit for every recursive verification and aggregation node).
    let t = Instant::now();
    let vc = VerifierCircuit::build(p.clone());
    let vc_build = t.elapsed();
    let leaf: Pf = vc.prove(&pk, &digest(0), &sig0)?;

    // -- 2. One signature subproof (the recursively-verified unit) -------------
    let _ = vc.prove(&pk, &digest(0), &sig0)?; // warm
    let t = Instant::now();
    let sp = vc.prove(&pk, &digest(0), &sig0)?;
    let sp_prove = t.elapsed();
    println!("\n2. One signature SUBPROOF (plonky2 proof that the sig verifies)");
    println!(
        "   circuit degree 2^{}, build {:.0} ms (one-time), PROVE {:.0} ms, proof {} KB",
        vc.data.common.degree().trailing_zeros(),
        ms(vc_build),
        ms(sp_prove),
        sp.to_bytes().len() / 1024
    );

    // Core-scaling probe: how many cores does ONE tree node use?
    if std::env::var("BENCH_CORES").is_ok() {
        let node = Agg2::build(&vc.data); // verify two signature subproofs
        let _ = node.prove(&leaf, &leaf)?; // warm
        let mut ts = Vec::new();
        for _ in 0..5 {
            let t = Instant::now();
            let _ = node.prove(&leaf, &leaf)?;
            ts.push(t.elapsed());
        }
        ts.sort();
        let thr = std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "all".into());
        println!(
            "CORE-SCALING RAYON_NUM_THREADS={thr}: node 2^{} prove median {:.0} ms",
            node.data.common.degree().trailing_zeros(),
            ms(ts[2])
        );
        return Ok(());
    }

    // -- 3. Recursively verifying one subproof (the recursion floor) -----------
    let (rec_build, rec_prove, rec_deg) = {
        let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
        let pt = b.add_virtual_proof_with_pis(&vc.data.common);
        let vd = b.constant_verifier_data(&vc.data.verifier_only);
        b.verify_proof::<C>(&pt, &vd, &vc.data.common);
        let t = Instant::now();
        let data = b.build::<C>();
        let build = t.elapsed();
        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&pt, &leaf)?;
        let t = Instant::now();
        let _ = data.prove(pw)?;
        (build, t.elapsed(), data.common.degree())
    };
    println!("\n3. Verify ONE signature subproof recursively (recursion floor)");
    println!(
        "   circuit degree 2^{}, build {:.0} ms, PROVE {:.0} ms",
        rec_deg.trailing_zeros(),
        ms(rec_build),
        ms(rec_prove)
    );

    // Helpers producing inline triples and recursive subproofs.
    let triples = |k: usize| -> Vec<(Vec<F>, [F; 4], Sig)> {
        (0..k as u64).map(|i| (pk.clone(), digest(i), key.sign(&digest(i)))).collect()
    };
    let subproofs = |k: usize| -> Result<Vec<Pf>> {
        (0..k as u64).map(|i| vc.prove(&pk, &digest(i), &key.sign(&digest(i)))).collect()
    };

    // -- 4. INLINE certificate over 4 blocks -----------------------------------
    // The certificate verifies each signature's gates directly (prover holds
    // the blobs), alongside the verified consensus rule + window density.
    let c7 = chain(7);
    for &spb in &[1usize, 2] {
        let sigs = triples(4 * spb);
        let t = Instant::now();
        let (data, proof) =
            prove_chain_with_inline_sphincs(&p, &sigs, N as u64, threshold as u64, &c7)?;
        let dt = t.elapsed();
        if spb == 1 {
            println!("\n4. INLINE certificate — 4 blocks, consensus + density + K inline verifies");
        }
        println!(
            "   {} sig/block ({} total): build+PROVE {:.1} s, degree 2^{}, proof {} KB",
            spb,
            4 * spb,
            dt.as_secs_f64(),
            data.common.degree().trailing_zeros(),
            proof.to_bytes().len() / 1024
        );
    }

    // -- 5. RECURSIVE certificate over 4 blocks --------------------------------
    // 4 blocks × 2 sigs (1 consensus + 1 application) = 8 subproofs, recursively
    // verified; secret keys never shared with the prover.
    let sp8 = subproofs(8)?;
    let c4 = chain(4);
    let t = Instant::now();
    let (data, proof) = prove_batch_recursive(&vc.data, &sp8, N as u64, threshold as u64, &c4)?;
    let dt = t.elapsed();
    println!("\n5. RECURSIVE certificate — 4 blocks, 8 subproofs verified + consensus");
    println!(
        "   (secret keys NOT shared) build+PROVE {:.1} s, degree 2^{}, proof {} KB",
        dt.as_secs_f64(),
        data.common.degree().trailing_zeros(),
        proof.to_bytes().len() / 1024
    );

    // -- 4b. The VERIFIED consensus validator as a circuit (no signatures) -----
    {
        let mut prev: Option<Hash> = None;
        let mut blocks = Vec::new();
        for sl in 0u64..8 {
            let id = block_id(sl, sl, prev.as_ref(), &Hash { a: sl, b: 0, c: 0, d: 0 });
            blocks.push(BlockData { slot: sl, height: sl, prev, id });
            prev = Some(id);
        }
        let t = Instant::now();
        let (data, proof) = prove_valid_chain_be(N as u64, threshold as u64, &blocks)?;
        let dt = t.elapsed();
        println!("\n4b. Verified consensus validator in-circuit (molt_petit::valid_chain_be,");
        println!("    the Lean-proven function; 8-block chain, structure + window density)");
        println!(
            "    degree 2^{}, build+PROVE {:.0} ms, proof {} KB",
            data.common.degree().trailing_zeros(),
            ms(dt),
            proof.to_bytes().len() / 1024
        );
    }

    // -- 6. Medians: sign + minimal certificate --------------------------------
    let mut sg = Vec::new();
    for i in 0..9u64 {
        let t = Instant::now();
        let _ = key.sign(&digest(i));
        sg.push(t.elapsed());
    }
    let sign = median(sg);
    // inline batch, 1 sig/block over 4 blocks + consensus + density
    let sigs4 = triples(4);
    let mut bi = Vec::new();
    for _ in 0..3 {
        let t = Instant::now();
        let _ = prove_chain_with_inline_sphincs(&p, &sigs4, N as u64, threshold as u64, &c7)?;
        bi.push(t.elapsed());
    }
    println!("\n========================================================");
    println!("6. minimal signing + single 4-block certificate (medians)");
    println!("   (a) SIGN a block (host SPHINCS+-{}):  {:.0} ms", p.name, ms(sign));
    println!(
        "   (b) INLINE certificate, 1 sig/block + consensus + density:  {:.1} s",
        median(bi).as_secs_f64()
    );
    println!("========================================================");

    // -- 7. Recursive-verify batch scaling -------------------------------------
    println!("\n7. RECURSIVE-verify batch scaling (secret keys NOT shared)");
    for &(blocks, sigs) in &[(2u64, 4usize), (4, 8), (8, 16)] {
        let sps = subproofs(sigs)?;
        let c = chain(blocks.max(1));
        let t = Instant::now();
        let (data, _) = prove_batch_recursive(&vc.data, &sps, N as u64, threshold as u64, &c)?;
        println!(
            "   {blocks} blocks, {sigs} subproofs verified + consensus: build+PROVE {:.1} s, degree 2^{}",
            t.elapsed().as_secs_f64(),
            data.common.degree().trailing_zeros()
        );
    }

    // -- 8. Aggregating 8 subproofs (4 blocks × 2) — strategies ----------------
    {
        let sps = subproofs(8)?;
        println!("\n8. Aggregating 8 signature subproofs (4 blocks × 2) — strategies");

        let t = Instant::now();
        let (fa, _) = prove_batch_recursive(&vc.data, &sps, N as u64, threshold as u64, &c4)?;
        println!(
            "   A) flat (cert verifies 8): {:.1} s, degree 2^{}",
            t.elapsed().as_secs_f64(),
            fa.common.degree().trailing_zeros()
        );

        let t = Instant::now();
        let (agg_d, agg_p) = aggregate_n(&vc.data, &sps)?;
        let b_agg = t.elapsed();
        let t = Instant::now();
        let (bo_d, _) = big_over_inner(&agg_d, &agg_p, N as u64, threshold as u64, &c4)?;
        let b_big = t.elapsed();
        println!(
            "   B) aggregate-8 {:.1} s (2^{}) + cert-verifies-1 {:.1} s (2^{}) = {:.1} s",
            b_agg.as_secs_f64(),
            agg_d.common.degree().trailing_zeros(),
            b_big.as_secs_f64(),
            bo_d.common.degree().trailing_zeros(),
            (b_agg + b_big).as_secs_f64()
        );

        let tb = Instant::now();
        let l1 = Agg2::build(&vc.data);
        let l2 = Agg2::build(&l1.data);
        let l3 = Agg2::build(&l2.data);
        let tree_build = tb.elapsed();
        let mut lt = [Duration::ZERO; 3];
        let t = Instant::now();
        let l1p: Vec<_> = (0..4).map(|i| l1.prove(&sps[2 * i], &sps[2 * i + 1])).collect::<Result<_>>()?;
        lt[0] = t.elapsed();
        let t = Instant::now();
        let l2p = vec![l2.prove(&l1p[0], &l1p[1])?, l2.prove(&l1p[2], &l1p[3])?];
        lt[1] = t.elapsed();
        let t = Instant::now();
        let l3p = l3.prove(&l2p[0], &l2p[1])?;
        lt[2] = t.elapsed();
        let t = Instant::now();
        let (bo2_d, _) = big_over_inner(&l3.data, &l3p, N as u64, threshold as u64, &c4)?;
        let c_big = t.elapsed();
        let crit = lt[0].as_secs_f64() / 4.0 + lt[1].as_secs_f64() / 2.0 + lt[2].as_secs_f64();
        println!(
            "   C) binary tree: build {:.1} s (one-time, 2^{}), prove 7 nodes {:.1} s seq",
            tree_build.as_secs_f64(),
            l1.data.common.degree().trailing_zeros(),
            lt.iter().sum::<Duration>().as_secs_f64()
        );
        println!(
            "        + cert-verifies-1 {:.1} s (2^{})  → parallel critical path (1 node/level + cert) ≈ {:.1} s",
            c_big.as_secs_f64(),
            bo2_d.common.degree().trailing_zeros(),
            crit + c_big.as_secs_f64()
        );
    }

    // -- 9. 8 blocks × 8 = 64 subproofs ----------------------------------------
    {
        // Aggregation timing is independent of which valid subproof each leaf is,
        // so we reuse one subproof (each distinct one would cost ~0.5 s to make).
        let sps: Vec<Pf> = vec![leaf.clone(); 64];
        let c8 = chain(8);
        println!("\n9. 8 blocks × 8 = 64 signature subproofs (consensus + density over 8 blocks)");

        let t = Instant::now();
        let (fa, _) = prove_batch_recursive(&vc.data, &sps, N as u64, threshold as u64, &c8)?;
        println!(
            "   A) flat (cert verifies 64): {:.1} s, degree 2^{}",
            t.elapsed().as_secs_f64(),
            fa.common.degree().trailing_zeros()
        );

        // binary tree 64→…→1
        let mut levels: Vec<Agg2> = Vec::new();
        let mut proofs = sps.clone();
        let mut tbuild = Duration::ZERO;
        let mut ttimes = Vec::new();
        while proofs.len() > 1 {
            let tb = Instant::now();
            let agg = if levels.is_empty() {
                Agg2::build(&vc.data)
            } else {
                Agg2::build(&levels.last().unwrap().data)
            };
            tbuild += tb.elapsed();
            let tp = Instant::now();
            let mut next = Vec::new();
            let mut i = 0;
            while i + 1 < proofs.len() {
                next.push(agg.prove(&proofs[i], &proofs[i + 1])?);
                i += 2;
            }
            ttimes.push(tp.elapsed());
            proofs = next;
            levels.push(agg);
        }
        let root = proofs.pop().unwrap();
        let t = Instant::now();
        let _ = big_over_inner(&levels.last().unwrap().data, &root, N as u64, threshold as u64, &c8)?;
        let c_big = t.elapsed();
        let crit: f64 = ttimes
            .iter()
            .enumerate()
            .map(|(lvl, d)| d.as_secs_f64() / 2f64.powi((ttimes.len() - 1 - lvl) as i32))
            .sum();
        println!(
            "   C) tree: {} levels, build {:.1} s (one-time), prove 63 nodes {:.1} s seq + cert-1 {:.1} s",
            levels.len(),
            tbuild.as_secs_f64(),
            ttimes.iter().sum::<Duration>().as_secs_f64(),
            c_big.as_secs_f64()
        );
        println!("        parallel critical path (1 node/level + cert) ≈ {:.1} s", crit + c_big.as_secs_f64());
    }

    // -- 10. 4 blocks × 512 = 2048 subproofs (tree spine) ----------------------
    {
        let leaves = 2048usize;
        let levels = (leaves as f64).log2() as usize; // 11
        let mut cur = leaf.clone();
        let mut spine: Vec<Agg2> = Vec::new();
        let mut node_times: Vec<Duration> = Vec::new();
        let mut build_total = Duration::ZERO;
        for _ in 0..levels {
            let tb = Instant::now();
            let agg = if spine.is_empty() {
                Agg2::build(&vc.data)
            } else {
                Agg2::build(&spine.last().unwrap().data)
            };
            build_total += tb.elapsed();
            let t = Instant::now();
            let pnode = agg.prove(&cur, &cur)?;
            node_times.push(t.elapsed());
            cur = pnode;
            spine.push(agg);
        }
        let t = Instant::now();
        let _ = big_over_inner(&spine.last().unwrap().data, &cur, N as u64, threshold as u64, &c4)?;
        let c_big = t.elapsed();
        let crit: f64 = node_times.iter().map(|d| d.as_secs_f64()).sum::<f64>() + c_big.as_secs_f64();
        let seq: f64 = node_times
            .iter()
            .enumerate()
            .map(|(l, d)| d.as_secs_f64() * (leaves as f64 / 2f64.powi((l + 1) as i32)))
            .sum::<f64>()
            + c_big.as_secs_f64();
        println!("\n10. 4 blocks × 512 = 2048 signature subproofs (binary tree, {levels} levels, 2047 nodes)");
        println!("    flat: INFEASIBLE (~2^22 circuit, tens of GB / many minutes)");
        println!("    per-level node prove (ms): {:?}", node_times.iter().map(|d| ms(*d).round() as u32).collect::<Vec<_>>());
        println!(
            "    node circuit ≈ 2^{}, tree build {:.1} s (one-time)",
            spine.last().unwrap().data.common.degree().trailing_zeros(),
            build_total.as_secs_f64()
        );
        println!("    PARALLEL critical path (1 node/level + cert-verifies-1) ≈ {:.1} s", crit);
        println!("    fully sequential (all 2047 nodes, extrapolated) ≈ {:.0} s", seq);
        println!("    + each submitter's host sign + leaf subproof (all parallel)");
    }

    // Reference: a single Poseidon hash (host).
    let t = Instant::now();
    for _ in 0..10_000 {
        let _ = PoseidonHash::hash_no_pad(&[F::from_canonical_u64(7)]);
    }
    let _ = std::hint::black_box(());
    println!("\nreference: host Poseidon hash ≈ {:.2} µs", t.elapsed().as_secs_f64() / 10_000.0 * 1e6);
    Ok(())
}
