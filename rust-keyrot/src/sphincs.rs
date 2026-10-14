//! Production-shaped SPHINCS+ over Poseidon, parameterised by the NIST sets and
//! the security level (node width `n_fe` field elements: 2 = 128-bit, 4 = 256-bit).
//!
//! Real composite construction: WOTS+ chains, FORS few-time trees, and a
//! `d`-layer hypertree of XMSS subtrees generated **on the fly** while signing
//! (so keygen builds only the top subtree, never all `2^h` leaves). Signing is
//! parallelised with rayon.
//!
//! Used to *measure* host signing and in-circuit verification at production
//! parameters. Remaining simplifications vs the standard (security, not cost):
//! plain Winternitz (no WOTS+ bitmask), no per-call ADRS tweak, no randomizer R.

use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::hash_types::HashOutTarget;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::{BoolTarget, Target};
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::config::Hasher;
use plonky2::plonk::proof::ProofWithPublicInputs;
use rayon::prelude::*;

use crate::types::{C, D, F};

/// A node: `n_fe` Goldilocks elements (`n_fe*64`-bit hash output).
pub type Dig = Vec<F>;

#[derive(Clone)]
pub struct Params {
    pub name: &'static str,
    pub n_fe: usize, // field elements per hash output (2=128-bit, 4=256-bit)
    pub w: usize,
    pub len1: usize,
    pub len2: usize,
    pub len: usize,
    pub k: usize,
    pub a: usize,
    pub d: usize,
    pub sub_h: usize,
}

impl Params {
    fn make(name: &'static str, n_fe: usize, k: usize, a: usize, d: usize, sub_h: usize) -> Self {
        let w = 16;
        let len1 = 16 * n_fe; // base-16 digits of the n_fe-element WOTS message
        let len2 = 3; // checksum digits (len1*(w-1) < 16^3 for our sizes)
        Self { name, n_fe, w, len1, len2, len: len1 + len2, k, a, d, sub_h }
    }
    /// NIST SLH-DSA-128s.
    pub fn s128s() -> Self { Self::make("128s", 2, 14, 12, 7, 9) }
    /// NIST SLH-DSA-128f.
    pub fn s128f() -> Self { Self::make("128f", 2, 33, 6, 22, 3) }
    /// NIST SLH-DSA-256s.
    pub fn s256s() -> Self { Self::make("256s", 4, 22, 14, 8, 8) }
    /// NIST SLH-DSA-256f.
    pub fn s256f() -> Self { Self::make("256f", 4, 35, 9, 17, 4) }
    /// Tiny set for fast unit tests.
    pub fn tiny() -> Self { Self::make("tiny", 2, 3, 3, 2, 2) }

    /// Parameters for a standalone **XMSS** (single Merkle tree of WOTS+ leaves,
    /// no FORS, one hypertree layer of height `h`). Reuses the same WOTS+ /
    /// Merkle machinery; `k = a = 0`, `d = 1`, `sub_h = h`. Used by `crate::xmss`.
    pub fn xmss(name: &'static str, n_fe: usize, h: usize) -> Self {
        Self::make(name, n_fe, 0, 0, 1, h)
    }

    pub fn h(&self) -> usize { self.d * self.sub_h }
    /// Number of FORS message-digest elements needed for k*a bits.
    fn md_fe(&self) -> usize { (self.k * self.a + 63) / 64 }
}

// ---------- hashing (host) ----------
pub(crate) fn hf(xs: &[F], n_fe: usize) -> Dig {
    PoseidonHash::hash_no_pad(xs).elements[..n_fe].to_vec()
}
fn f1(x: &[F], n_fe: usize) -> Dig {
    hf(x, n_fe)
}
fn node(a: &[F], b: &[F], n_fe: usize) -> Dig {
    let mut v = a.to_vec();
    v.extend_from_slice(b);
    hf(&v, n_fe)
}
fn thash(xs: &[Dig], n_fe: usize) -> Dig {
    let flat: Vec<F> = xs.iter().flatten().copied().collect();
    hf(&flat, n_fe)
}
fn prf(seed: &[F], idxs: &[u64], n_fe: usize) -> Dig {
    let mut v = seed.to_vec();
    v.extend(idxs.iter().map(|&x| F::from_canonical_u64(x)));
    hf(&v, n_fe)
}
fn chain(mut x: Dig, steps: usize, n_fe: usize) -> Dig {
    for _ in 0..steps {
        x = f1(&x, n_fe);
    }
    x
}

// ---------- message expansion / indices ----------
fn expand(digest: &[F; 4], count: usize) -> Vec<F> {
    let mut out = Vec::with_capacity(count + 4);
    let mut chunk = 0u64;
    while out.len() < count {
        let mut inp = digest.to_vec();
        inp.push(F::from_canonical_u64(chunk));
        out.extend_from_slice(&PoseidonHash::hash_no_pad(&inp).elements);
        chunk += 1;
    }
    out.truncate(count);
    out
}
fn fors_indices(digest: &[F; 4], p: &Params) -> Vec<usize> {
    let md = expand(digest, p.md_fe());
    let bit = |b: usize| (md[b / 64].to_canonical_u64() >> (b % 64)) & 1;
    (0..p.k)
        .map(|t| (0..p.a).fold(0usize, |acc, j| acc | ((bit(t * p.a + j) as usize) << j)))
        .collect()
}
const ID: u64 = 0xD51;

fn derive_idx(digest: &[F; 4], h: usize) -> u128 {
    let mut inp = digest.to_vec();
    inp.push(F::from_canonical_u64(ID));
    let e = PoseidonHash::hash_no_pad(&inp).elements;
    let v = (e[0].to_canonical_u64() as u128) | ((e[1].to_canonical_u64() as u128) << 64);
    v & ((1u128 << h) - 1)
}

// ---------- WOTS+ ----------
fn wots_digits(msg: &[F], p: &Params) -> Vec<usize> {
    let mut d = Vec::with_capacity(p.len);
    for limb in msg {
        let v = limb.to_canonical_u64();
        for nib in 0..16 {
            d.push(((v >> (4 * nib)) & 0xF) as usize);
        }
    }
    let csum: usize = d.iter().map(|&x| (p.w - 1) - x).sum();
    for nib in 0..p.len2 {
        d.push((csum >> (4 * nib)) & 0xF);
    }
    d
}
fn wots_sk(seed: &[F], layer: u64, tree: u64, leaf: u64, i: u64, n_fe: usize) -> Dig {
    prf(seed, &[1, layer, tree, leaf, i], n_fe)
}
fn wots_pk(seed: &[F], layer: u64, tree: u64, leaf: u64, p: &Params) -> Dig {
    let tops: Vec<Dig> = (0..p.len as u64)
        .map(|i| chain(wots_sk(seed, layer, tree, leaf, i, p.n_fe), p.w - 1, p.n_fe))
        .collect();
    thash(&tops, p.n_fe)
}
pub(crate) fn wots_sign(seed: &[F], layer: u64, tree: u64, leaf: u64, msg: &[F], p: &Params) -> Vec<Dig> {
    let digits = wots_digits(msg, p);
    (0..p.len as u64)
        .map(|i| chain(wots_sk(seed, layer, tree, leaf, i, p.n_fe), digits[i as usize], p.n_fe))
        .collect()
}
pub(crate) fn wots_pk_from_sig(sig: &[Dig], msg: &[F], p: &Params) -> Dig {
    let digits = wots_digits(msg, p);
    let tops: Vec<Dig> = (0..p.len)
        .map(|i| chain(sig[i].clone(), (p.w - 1) - digits[i], p.n_fe))
        .collect();
    thash(&tops, p.n_fe)
}

// ---------- Merkle ----------
fn build_tree(leaves: Vec<Dig>, n_fe: usize) -> Vec<Vec<Dig>> {
    let mut layers = vec![leaves];
    while layers.last().unwrap().len() > 1 {
        let prev = layers.last().unwrap();
        let next: Vec<Dig> = prev.chunks(2).map(|c| node(&c[0], &c[1], n_fe)).collect();
        layers.push(next);
    }
    layers
}
pub(crate) fn auth_path(layers: &[Vec<Dig>], mut idx: usize) -> Vec<Dig> {
    let mut path = Vec::with_capacity(layers.len() - 1);
    for level in &layers[..layers.len() - 1] {
        path.push(level[idx ^ 1].clone());
        idx >>= 1;
    }
    path
}
pub(crate) fn merkle_climb(mut cur: Dig, auth: &[Dig], mut idx: usize, n_fe: usize) -> Dig {
    for sib in auth {
        cur = if idx & 1 == 0 { node(&cur, sib, n_fe) } else { node(sib, &cur, n_fe) };
        idx >>= 1;
    }
    cur
}
/// Build a hypertree subtree on the fly (leaf WOTS keys in parallel).
pub(crate) fn build_subtree(seed: &[F], layer: u64, tree: u64, p: &Params) -> Vec<Vec<Dig>> {
    let leaves: Vec<Dig> = (0..(1u64 << p.sub_h))
        .into_par_iter()
        .map(|leaf| wots_pk(seed, layer, tree, leaf, p))
        .collect();
    build_tree(leaves, p.n_fe)
}

#[derive(Clone)]
pub struct Sig {
    pub fors_sk: Vec<Dig>,
    pub fors_auth: Vec<Vec<Dig>>,
    pub wots_sig: Vec<Vec<Dig>>,
    pub hyper_auth: Vec<Vec<Dig>>,
}

pub struct Key {
    seed: Vec<F>,
    pk: Dig,
    pub p: Params,
}

impl Key {
    pub fn keygen(p: Params, seed_u64: u64) -> Self {
        let seed: Vec<F> = (0..p.n_fe).map(|i| F::from_canonical_u64(seed_u64 ^ (0x5555 * i as u64 + 1))).collect();
        let top = build_subtree(&seed, (p.d - 1) as u64, 0, &p);
        let pk = top.last().unwrap()[0].clone();
        Self { seed, pk, p }
    }

    pub fn public_key(&self) -> Dig {
        self.pk.clone()
    }

    pub fn sign(&self, digest: &[F; 4]) -> Sig {
        let p = &self.p;
        let idx = derive_idx(digest, p.h());
        let fors_idx = fors_indices(digest, p);

        // FORS keypair `idx`: build each tree's leaves in parallel.
        let fors: Vec<(Dig, Vec<Dig>, Dig)> = (0..p.k)
            .into_par_iter()
            .map(|t| {
                let leaves: Vec<Dig> = (0..(1u64 << p.a))
                    .into_par_iter()
                    .map(|l| f1(&prf(&self.seed, &[0, idx as u64, t as u64, l], p.n_fe), p.n_fe))
                    .collect();
                let layers = build_tree(leaves, p.n_fe);
                let root = layers.last().unwrap()[0].clone();
                let auth = auth_path(&layers, fors_idx[t]);
                let sk = prf(&self.seed, &[0, idx as u64, t as u64, fors_idx[t] as u64], p.n_fe);
                (sk, auth, root)
            })
            .collect();
        let fors_sk: Vec<Dig> = fors.iter().map(|x| x.0.clone()).collect();
        let fors_auth: Vec<Vec<Dig>> = fors.iter().map(|x| x.1.clone()).collect();
        let roots: Vec<Dig> = fors.iter().map(|x| x.2.clone()).collect();
        let fors_pk = thash(&roots, p.n_fe);

        // Hypertree: build all subtrees (parallel leaves), get roots + auth paths.
        let mask = (1u128 << p.sub_h) - 1;
        let subtrees: Vec<(Vec<Vec<Dig>>, u64, u64)> = (0..p.d)
            .map(|j| {
                let leaf = ((idx >> (j * p.sub_h)) & mask) as u64;
                let tree = (idx >> ((j + 1) * p.sub_h)) as u64;
                let layers = build_subtree(&self.seed, j as u64, tree, p);
                (layers, leaf, tree)
            })
            .collect();

        // Value WOTS-signed at each layer: fors_pk, then each subtree root.
        let mut cur_vals = Vec::with_capacity(p.d);
        let mut cur = fors_pk;
        for (layers, _, _) in &subtrees {
            cur_vals.push(cur.clone());
            cur = layers.last().unwrap()[0].clone();
        }

        let wots_sig: Vec<Vec<Dig>> = (0..p.d)
            .into_par_iter()
            .map(|j| {
                let (_, leaf, tree) = &subtrees[j];
                wots_sign(&self.seed, j as u64, *tree, *leaf, &cur_vals[j], p)
            })
            .collect();
        let hyper_auth: Vec<Vec<Dig>> = (0..p.d)
            .map(|j| auth_path(&subtrees[j].0, subtrees[j].1 as usize))
            .collect();

        Sig { fors_sk, fors_auth, wots_sig, hyper_auth }
    }
}

/// Native verification (mirrors the in-circuit logic).
pub fn verify(pk: &[F], digest: &[F; 4], sig: &Sig, p: &Params) -> bool {
    let idx = derive_idx(digest, p.h());
    let fors_idx = fors_indices(digest, p);

    let roots: Vec<Dig> = (0..p.k)
        .map(|t| {
            let leaf = f1(&sig.fors_sk[t], p.n_fe);
            merkle_climb(leaf, &sig.fors_auth[t], fors_idx[t], p.n_fe)
        })
        .collect();
    let mut cur = thash(&roots, p.n_fe);

    let mask = (1u128 << p.sub_h) - 1;
    for j in 0..p.d {
        let wpk = wots_pk_from_sig(&sig.wots_sig[j], &cur, p);
        let leaf = ((idx >> (j * p.sub_h)) & mask) as usize;
        cur = merkle_climb(wpk, &sig.hyper_auth[j], leaf, p.n_fe);
    }
    cur == pk
}

// ===================== In-circuit verification =====================

pub struct SigTargets {
    pub fors_sk: Vec<Vec<Target>>,
    pub fors_auth: Vec<Vec<Vec<Target>>>,
    pub wots_sig: Vec<Vec<Vec<Target>>>,
    pub hyper_auth: Vec<Vec<Vec<Target>>>,
}

pub(crate) fn add_dig(builder: &mut CircuitBuilder<F, D>, n: usize) -> Vec<Target> {
    builder.add_virtual_targets(n)
}

pub fn add_signature_targets(builder: &mut CircuitBuilder<F, D>, p: &Params) -> SigTargets {
    let n = p.n_fe;
    SigTargets {
        fors_sk: (0..p.k).map(|_| add_dig(builder, n)).collect(),
        fors_auth: (0..p.k).map(|_| (0..p.a).map(|_| add_dig(builder, n)).collect()).collect(),
        wots_sig: (0..p.d).map(|_| (0..p.len).map(|_| add_dig(builder, n)).collect()).collect(),
        hyper_auth: (0..p.d).map(|_| (0..p.sub_h).map(|_| add_dig(builder, n)).collect()).collect(),
    }
}

pub(crate) fn chf(builder: &mut CircuitBuilder<F, D>, xs: Vec<Target>, n: usize) -> Vec<Target> {
    builder.hash_n_to_hash_no_pad::<PoseidonHash>(xs).elements[..n].to_vec()
}
fn cf1(builder: &mut CircuitBuilder<F, D>, x: &[Target], n: usize) -> Vec<Target> {
    chf(builder, x.to_vec(), n)
}
fn cnode(builder: &mut CircuitBuilder<F, D>, a: &[Target], b: &[Target], n: usize) -> Vec<Target> {
    let mut v = a.to_vec();
    v.extend_from_slice(b);
    chf(builder, v, n)
}
fn cthash(builder: &mut CircuitBuilder<F, D>, xs: &[Vec<Target>], n: usize) -> Vec<Target> {
    let flat: Vec<Target> = xs.iter().flatten().copied().collect();
    chf(builder, flat, n)
}
fn nibble(builder: &mut CircuitBuilder<F, D>, bits: &[BoolTarget]) -> Target {
    let mut acc = builder.zero();
    for (j, b) in bits.iter().enumerate() {
        acc = builder.mul_const_add(F::from_canonical_u64(1 << j), b.target, acc);
    }
    acc
}
fn cselect_dig(builder: &mut CircuitBuilder<F, D>, b: BoolTarget, x: &[Target], y: &[Target]) -> Vec<Target> {
    x.iter().zip(y).map(|(&xi, &yi)| builder.select(b, xi, yi)).collect()
}
pub(crate) fn cclimb(builder: &mut CircuitBuilder<F, D>, mut cur: Vec<Target>, auth: &[Vec<Target>], bits: &[BoolTarget], n: usize) -> Vec<Target> {
    for (sib, bit) in auth.iter().zip(bits) {
        let left = cselect_dig(builder, *bit, sib, &cur);
        let right = cselect_dig(builder, *bit, &cur, sib);
        cur = cnode(builder, &left, &right, n);
    }
    cur
}
pub(crate) fn cwots_pk_from_sig(builder: &mut CircuitBuilder<F, D>, sig: &[Vec<Target>], msg: &[Target], p: &Params) -> Vec<Target> {
    let mut digits: Vec<Target> = Vec::with_capacity(p.len);
    for limb in msg {
        let bits = builder.split_le(*limb, 64);
        for nib in 0..16 {
            digits.push(nibble(builder, &bits[4 * nib..4 * nib + 4]));
        }
    }
    let sum = builder.add_many(digits.clone());
    let max = builder.constant(F::from_canonical_u64(((p.w - 1) * p.len1) as u64));
    let csum = builder.sub(max, sum);
    let cbits = builder.split_le(csum, 4 * p.len2);
    for nib in 0..p.len2 {
        digits.push(nibble(builder, &cbits[4 * nib..4 * nib + 4]));
    }

    let top = builder.constant(F::from_canonical_u64((p.w - 1) as u64));
    let mut tops = Vec::with_capacity(p.len);
    for i in 0..p.len {
        let mut cur = sig[i].clone();
        let mut height = digits[i];
        for _ in 0..(p.w - 1) {
            let at_top = builder.is_equal(height, top);
            let step = builder.not(at_top);
            let hashed = cf1(builder, &cur, p.n_fe);
            cur = cur.iter().zip(&hashed).map(|(&c, &h)| builder.select(step, h, c)).collect();
            height = builder.add(height, step.target);
        }
        tops.push(cur);
    }
    cthash(builder, &tops, p.n_fe)
}

/// In-circuit expansion of the message digest (mirrors `expand`).
fn cexpand(builder: &mut CircuitBuilder<F, D>, digest: &[Target; 4], count: usize) -> Vec<Target> {
    let mut out = Vec::with_capacity(count + 4);
    let mut chunk = 0u64;
    while out.len() < count {
        let mut inp = digest.to_vec();
        inp.push(builder.constant(F::from_canonical_u64(chunk)));
        let h = builder.hash_n_to_hash_no_pad::<PoseidonHash>(inp);
        out.extend_from_slice(&h.elements);
        chunk += 1;
    }
    out.truncate(count);
    out
}

pub fn verify_signature(builder: &mut CircuitBuilder<F, D>, pk: &[Target], digest: HashOutTarget, s: &SigTargets, p: &Params) {
    let dg: [Target; 4] = digest.elements;

    // FORS message bits.
    let md = cexpand(builder, &dg, p.md_fe());
    let md_bits: Vec<BoolTarget> = md.iter().flat_map(|&e| builder.split_le(e, 64)).collect();

    let roots: Vec<Vec<Target>> = (0..p.k)
        .map(|t| {
            let leaf = cf1(builder, &s.fors_sk[t], p.n_fe);
            let bits = &md_bits[t * p.a..t * p.a + p.a];
            cclimb(builder, leaf, &s.fors_auth[t], bits, p.n_fe)
        })
        .collect();
    let mut cur = cthash(builder, &roots, p.n_fe);

    // Hypertree index bits.
    let mut idx_inp = dg.to_vec();
    idx_inp.push(builder.constant(F::from_canonical_u64(ID)));
    let ih = builder.hash_n_to_hash_no_pad::<PoseidonHash>(idx_inp);
    let mut idx_bits: Vec<BoolTarget> = Vec::new();
    idx_bits.extend(builder.split_le(ih.elements[0], 64));
    idx_bits.extend(builder.split_le(ih.elements[1], 64));

    for j in 0..p.d {
        let wpk = cwots_pk_from_sig(builder, &s.wots_sig[j], &cur, p);
        let bits = &idx_bits[j * p.sub_h..(j + 1) * p.sub_h];
        cur = cclimb(builder, wpk, &s.hyper_auth[j], bits, p.n_fe);
    }
    for i in 0..p.n_fe {
        builder.connect(cur[i], pk[i]);
    }
}

pub fn set_signature(pw: &mut PartialWitness<F>, s: &SigTargets, sig: &Sig) -> anyhow::Result<()> {
    let set = |pw: &mut PartialWitness<F>, t: &[Target], v: &[F]| -> anyhow::Result<()> {
        for (ti, vi) in t.iter().zip(v) {
            pw.set_target(*ti, *vi)?;
        }
        Ok(())
    };
    for t in 0..s.fors_sk.len() {
        set(pw, &s.fors_sk[t], &sig.fors_sk[t])?;
        for j in 0..s.fors_auth[t].len() {
            set(pw, &s.fors_auth[t][j], &sig.fors_auth[t][j])?;
        }
    }
    for j in 0..s.wots_sig.len() {
        for i in 0..s.wots_sig[j].len() {
            set(pw, &s.wots_sig[j][i], &sig.wots_sig[j][i])?;
        }
        for i in 0..s.hyper_auth[j].len() {
            set(pw, &s.hyper_auth[j][i], &sig.hyper_auth[j][i])?;
        }
    }
    Ok(())
}

pub fn sig_digest(sig: &Sig) -> [u64; 4] {
    let mut elements = Vec::new();
    for sk in &sig.fors_sk {
        elements.extend_from_slice(sk);
    }
    for tree in &sig.fors_auth {
        for node in tree {
            elements.extend_from_slice(node);
        }
    }
    for layer in &sig.wots_sig {
        for dig in layer {
            elements.extend_from_slice(dig);
        }
    }
    for layer in &sig.hyper_auth {
        for node in layer {
            elements.extend_from_slice(node);
        }
    }
    let d = PoseidonHash::hash_no_pad(&elements).elements;
    [
        d[0].to_canonical_u64(),
        d[1].to_canonical_u64(),
        d[2].to_canonical_u64(),
        d[3].to_canonical_u64(),
    ]
}

pub struct VerifierCircuit {
    pub data: CircuitData<F, C, D>,
    pk: Vec<Target>,
    digest: [Target; 4],
    sig: SigTargets,
    pub p: Params,
}

impl VerifierCircuit {
    pub fn build(p: Params) -> Self {
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
        let pk = builder.add_virtual_targets(p.n_fe);
        let digest = [
            builder.add_virtual_target(),
            builder.add_virtual_target(),
            builder.add_virtual_target(),
            builder.add_virtual_target(),
        ];
        let sig = add_signature_targets(&mut builder, &p);
        verify_signature(&mut builder, &pk, HashOutTarget { elements: digest }, &sig, &p);
        let mut sig_targets = Vec::new();
        for sk in &sig.fors_sk {
            sig_targets.extend_from_slice(sk);
        }
        for tree in &sig.fors_auth {
            for node in tree {
                sig_targets.extend_from_slice(node);
            }
        }
        for layer in &sig.wots_sig {
            for dig in layer {
                sig_targets.extend_from_slice(dig);
            }
        }
        for layer in &sig.hyper_auth {
            for node in layer {
                sig_targets.extend_from_slice(node);
            }
        }
        let sig_digest = builder.hash_n_to_hash_no_pad::<PoseidonHash>(sig_targets);
        builder.register_public_inputs(&pk);
        builder.register_public_inputs(&digest);
        builder.register_public_inputs(&sig_digest.elements);
        let data = builder.build::<C>();
        Self { data, pk, digest, sig, p }
    }

    pub fn prove(&self, pk: &[F], digest: &[F; 4], sig: &Sig) -> anyhow::Result<ProofWithPublicInputs<F, C, D>> {
        let mut pw = PartialWitness::new();
        for (t, v) in self.pk.iter().zip(pk) {
            pw.set_target(*t, *v)?;
        }
        for i in 0..4 {
            pw.set_target(self.digest[i], digest[i])?;
        }
        set_signature(&mut pw, &self.sig, sig)?;
        self.data.prove(pw)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn digest(a: u64, b: u64) -> [F; 4] {
        PoseidonHash::hash_no_pad(&[F::from_canonical_u64(a), F::from_canonical_u64(b)]).elements
    }

    #[test]
    fn host_roundtrip_tiny() {
        let p = Params::tiny();
        let key = Key::keygen(p.clone(), 7);
        let pk = key.public_key();
        for m in 0..4u64 {
            let d = digest(m, 99);
            let sig = key.sign(&d);
            assert!(verify(&pk, &d, &sig, &p), "valid (m={m})");
            assert!(!verify(&pk, &digest(m + 1000, 99), &sig, &p), "wrong message");
        }
    }
}
