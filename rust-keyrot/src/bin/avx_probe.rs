//! Focused probe for the SIMD / codegen-flag A/B: build + prove ONE SPHINCS+-128s
//! verification subproof (the table's headline 2^13 row), report prove time, and
//! print which packed Goldilocks field plonky2 selected at compile time
//! (scalar `GoldilocksField` width 1 vs `Avx2GoldilocksField` width 4).
use std::time::Instant;
use plonky2::field::types::Field;
use plonky2::field::packable::Packable;
use plonky2::field::packed::PackedField;
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::Hasher;
use molt_petit_keyrot::sphincs::{Key, Params, VerifierCircuit};
use molt_petit_keyrot::types::F;

fn digest(i: u64) -> [F; 4] {
    PoseidonHash::hash_no_pad(&[F::from_canonical_u64(i), F::from_canonical_u64(2)]).elements
}

fn main() -> anyhow::Result<()> {
    let width = <<GoldilocksField as Packable>::Packing as PackedField>::WIDTH;
    let simd = if width == 1 { "scalar" } else { "AVX2" };
    let threads = std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "all".into());
    println!("packed Goldilocks WIDTH = {width} ({simd});  RAYON_NUM_THREADS = {threads}");

    let p = Params::s128s();
    let key = Key::keygen(p.clone(), 999);
    let pk = key.public_key();
    let sig0 = key.sign(&digest(0));
    let vc = VerifierCircuit::build(p.clone());
    let _ = vc.prove(&pk, &digest(0), &sig0)?; // warm

    let mut ts = Vec::new();
    for _ in 0..5 {
        let t = Instant::now();
        let _ = vc.prove(&pk, &digest(0), &sig0)?;
        ts.push(t.elapsed().as_secs_f64() * 1e3);
    }
    ts.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!(
        "SPHINCS+-128s verify subproof (2^{}): PROVE median {:.0} ms (min {:.0}, max {:.0})",
        vc.data.common.degree().trailing_zeros(),
        ts[2], ts[0], ts[4]
    );
    Ok(())
}
