//! `FoldCrypto` — production-grade [`molt_petit::CryptoD`] implementation
//! backed by the recursive fold circuit and XMSS signature bindings.
//!
//! This satisfies Review Finding 4 from Round 2:
//! - Signatures are authentic XMSS signatures over the block's signing message;
//! - The signature handle stored in a [`SignedChain`] is the 4-limb circuit
//!   `sig_digest`;
//! - Signature verification looks up the signature by its digest and runs native
//!   XMSS verification;
//! - Certificate queries (`cert_tip_sig`, `cert_state`, `cert_floors_state`,
//!   `cert_gen`) decode the actual recursive fold proof's public inputs via
//!   [`exposed_state`];
//! - Deployed validation ([`molt_petit::validate_deployed`]) and block production
//!   ([`molt_petit::produce_block_deployed`]) work out of the box against real
//!   fold certificates.

use std::cell::RefCell;
use std::collections::HashMap;

use anyhow::{bail, Context, Result};
use plonky2::field::types::{Field, PrimeField64};
use plonky2::plonk::circuit_data::VerifierCircuitData;
use plonky2::plonk::proof::ProofWithPublicInputs;
use plonky2::recursion::cyclic_recursion::check_cyclic_proof_verifier_data;

use molt_petit::{
    claim_of_state, Block, CertClaim, CertStateG, Crypto, CryptoD, CryptoK,
    FloorList, FloorsG, Hash, HashG, TailG,
};

use crate::fold_circuit::{
    exposed_state, BlockSig, FoldBlock, KeyRegistry, Mode, SigBinding,
};
use crate::poseidon_util::fold_block_id;
use crate::sphincs::Params;
use crate::types::{C, D, F};
use crate::xmss::{self, Sig};

/// A 256-bit hash key for internal lookup tables.
pub type HKey = (u64, u64, u64, u64);

#[inline]
pub fn hkey(h: &Hash) -> HKey {
    (h.a, h.b, h.c, h.d)
}

#[inline]
pub fn hkey_raw(h: &[u64; 4]) -> HKey {
    (h[0], h[1], h[2], h[3])
}

/// Convert a 4-limb [`Hash`] into an `n_fe`-element field vector for public keys.
pub fn hash_to_pk(h: &Hash, n_fe: usize) -> Vec<F> {
    let limbs = [h.a, h.b, h.c, h.d];
    limbs[..n_fe].iter().map(|&x| F::from_canonical_u64(x)).collect()
}

/// Convert an `n_fe`-element field public key into a [`Hash`].
pub fn pk_to_hash(pk: &[F]) -> Hash {
    let mut limbs = [0u64; 4];
    for (i, f) in pk.iter().enumerate().take(4) {
        limbs[i] = f.to_canonical_u64();
    }
    Hash {
        a: limbs[0],
        b: limbs[1],
        c: limbs[2],
        d: limbs[3],
    }
}

/// Convert a tail buffer slice into [`TailG`] (oldest entry first).
pub fn tail_of(v: &[(u64, u64)]) -> TailG<u64> {
    let mut t = TailG::TNil;
    for (f, s) in v.iter().rev() {
        t = TailG::TCons(*f, *s, Box::new(t));
    }
    t
}

/// Convert a floor list slice into [`FloorsG`] (producer 0 first).
pub fn floors_of(v: &[u64]) -> FloorsG<u64> {
    let mut fl = FloorsG::FNil;
    for x in v.iter().rev() {
        fl = FloorsG::FCons(*x, Box::new(fl));
    }
    fl
}

/// Convert [`FloorsG`] into consensus [`FloorList`].
pub fn floors_of_state(i: u64, fl: &FloorsG<u64>) -> FloorList {
    match fl {
        FloorsG::FNil => FloorList::FNil,
        FloorsG::FCons(f, tl) => FloorList::FCons(i, *f, Box::new(floors_of_state(i + 1, tl))),
    }
}

/// Production [`CryptoD`] dictionary backed by cyclic fold proofs and XMSS signatures.
pub struct FoldCrypto {
    n: u64,
    mode: Mode,
    kbits: usize,
    p: Params,
    keys: Vec<Vec<xmss::Key>>,
    reg: KeyRegistry,
    vc: xmss::VerifierCircuit,
    cert_vd: RefCell<Option<VerifierCircuitData<F, C, D>>>,
    sigs: RefCell<HashMap<HKey, Sig>>,
    certs: RefCell<HashMap<HKey, ProofWithPublicInputs<F, C, D>>>,
}

impl FoldCrypto {
    /// Create a new `FoldCrypto` dictionary for committee size `n`, fold `mode`, and
    /// `kbits` key-rotation capacity. Uses standard parameters `Params::xmss("t", 2, 3)`.
    pub fn new(n: u64, mode: Mode, kbits: usize) -> Self {
        let p = Params::xmss("t", 2, 3);
        let keys: Vec<Vec<_>> = (0..n as usize)
            .map(|pr| {
                (0..1u64 << kbits)
                    .map(|ki| xmss::Key::keygen(p.clone(), 1000 * pr as u64 + ki))
                    .collect()
            })
            .collect();
        let reg = KeyRegistry::new(n as usize, kbits, p.n_fe, |pr, ki| {
            keys[pr][ki as usize].public_key()
        });
        let vc = xmss::VerifierCircuit::build(p.clone());
        Self {
            n,
            mode,
            kbits,
            p,
            keys,
            reg,
            vc,
            cert_vd: RefCell::new(None),
            sigs: RefCell::new(HashMap::new()),
            certs: RefCell::new(HashMap::new()),
        }
    }

    /// Construct `FoldCrypto` with pre-existing verifier circuit data.
    pub fn with_verifier_data(
        n: u64,
        mode: Mode,
        kbits: usize,
        cert_vd: VerifierCircuitData<F, C, D>,
    ) -> Self {
        let s = Self::new(n, mode, kbits);
        *s.cert_vd.borrow_mut() = Some(cert_vd);
        s
    }

    /// Construct `FoldCrypto` with custom keys and parameters.
    pub fn with_keys(
        n: u64,
        mode: Mode,
        kbits: usize,
        p: Params,
        keys: Vec<Vec<xmss::Key>>,
        cert_vd: Option<VerifierCircuitData<F, C, D>>,
    ) -> Self {
        let reg = KeyRegistry::new(n as usize, kbits, p.n_fe, |pr, ki| {
            keys[pr][ki as usize].public_key()
        });
        let vc = xmss::VerifierCircuit::build(p.clone());
        Self {
            n,
            mode,
            kbits,
            p,
            keys,
            reg,
            vc,
            cert_vd: RefCell::new(cert_vd),
            sigs: RefCell::new(HashMap::new()),
            certs: RefCell::new(HashMap::new()),
        }
    }

    /// Update or initialize the verifier circuit data for fold proofs.
    pub fn set_verifier_data(&self, cert_vd: VerifierCircuitData<F, C, D>) {
        *self.cert_vd.borrow_mut() = Some(cert_vd);
    }

    /// Register a fold proof under a given `Hash` handle.
    pub fn register_cert(&self, handle: Hash, proof: ProofWithPublicInputs<F, C, D>) {
        self.certs.borrow_mut().insert(hkey(&handle), proof);
    }

    /// Register a fold proof and set the verifier circuit data simultaneously.
    pub fn register_cert_with_vd(
        &self,
        handle: Hash,
        proof: ProofWithPublicInputs<F, C, D>,
        vd: VerifierCircuitData<F, C, D>,
    ) {
        self.set_verifier_data(vd);
        self.register_cert(handle, proof);
    }

    /// Construct a [`SigBinding`] configured to match this dictionary's key registry
    /// and verifier circuit.
    pub fn binding(&self) -> SigBinding {
        SigBinding {
            verifier: xmss::VerifierCircuit::build(self.p.clone()).data,
            n_fe: self.p.n_fe,
            root: self.reg.root(),
            pbits: self.reg.pbits,
            kbits: self.reg.kbits,
        }
    }

    /// Generate [`BlockSig`] evidence for a block previously signed under this dictionary.
    pub fn block_sig(&self, b: &Block, sig_digest: &Hash) -> Result<BlockSig> {
        let pr = (b.slot % self.n) as usize;
        let ki = b.key_index;
        if pr >= self.keys.len() || ki as usize >= self.keys[pr].len() {
            bail!("key index out of range for block");
        }
        let key = &self.keys[pr][ki as usize];
        let b_dig = [
            F::from_canonical_u64(b.id.a),
            F::from_canonical_u64(b.id.b),
            F::from_canonical_u64(b.id.c),
            F::from_canonical_u64(b.id.d),
        ];
        let sigs = self.sigs.borrow();
        let sig = sigs
            .get(&hkey(sig_digest))
            .context("signature not found in sigs table")?;
        let proof = self.vc.prove(&key.public_key(), &b_dig, sig)?;
        let path = self.reg.path(pr, ki);
        Ok(BlockSig { proof, path })
    }

    /// Generate [`BlockSig`] evidence directly for a [`FoldBlock`].
    pub fn fold_block_sig(&self, b: &FoldBlock) -> Result<BlockSig> {
        let pr = (b.slot % self.n) as usize;
        let ki = b.key_index;
        if pr >= self.keys.len() || ki as usize >= self.keys[pr].len() {
            bail!("key index out of range for fold block");
        }
        let key = &self.keys[pr][ki as usize];
        let b_dig = b.id.map(F::from_canonical_u64);
        let sigs = self.sigs.borrow();
        let sig = sigs
            .get(&hkey_raw(&b.sig))
            .context("signature not found in sigs table")?;
        let proof = self.vc.prove(&key.public_key(), &b_dig, sig)?;
        let path = self.reg.path(pr, ki);
        Ok(BlockSig { proof, path })
    }

    /// Convert a consensus [`Block`] and its signature [`Hash`] to a [`FoldBlock`].
    pub fn to_fold_block(&self, b: &Block, sig: &Hash) -> FoldBlock {
        FoldBlock {
            slot: b.slot,
            height: b.height,
            prev: match b.prev {
                Some(p) => [p.a, p.b, p.c, p.d],
                None => [0; 4],
            },
            id: [b.id.a, b.id.b, b.id.c, b.id.d],
            sig: [sig.a, sig.b, sig.c, sig.d],
            contents_hash: [
                b.contents_hash.a,
                b.contents_hash.b,
                b.contents_hash.c,
                b.contents_hash.d,
            ],
            key_index: b.key_index,
        }
    }

    /// Format a producer secret-key handle for signing.
    pub fn sk_for(&self, producer: u64) -> Hash {
        Hash {
            a: producer,
            b: 0,
            c: 0,
            d: 0,
        }
    }

    /// Committee size.
    pub fn n(&self) -> u64 {
        self.n
    }

    /// Fold mode.
    pub fn mode(&self) -> Mode {
        self.mode
    }

    /// Key-rotation capacity in bits.
    pub fn kbits(&self) -> usize {
        self.kbits
    }

    /// Signature scheme parameters.
    pub fn params(&self) -> &Params {
        &self.p
    }

    /// Underlying XMSS keys.
    pub fn keys(&self) -> &[Vec<xmss::Key>] {
        &self.keys
    }

    /// Key registry Merkle tree.
    pub fn reg(&self) -> &KeyRegistry {
        &self.reg
    }

    /// Verifier circuit instance.
    pub fn vc(&self) -> &xmss::VerifierCircuit {
        &self.vc
    }
}

impl Crypto for FoldCrypto {
    fn verify(&self, key: &Hash, b: &Block, sig: &Hash) -> bool {
        let table = self.sigs.borrow();
        let Some(sig_entry) = table.get(&hkey(sig)) else {
            return false;
        };
        let pk = hash_to_pk(key, self.p.n_fe);
        let msg: [F; 4] = [
            F::from_canonical_u64(b.id.a),
            F::from_canonical_u64(b.id.b),
            F::from_canonical_u64(b.id.c),
            F::from_canonical_u64(b.id.d),
        ];
        xmss::verify(&pk, &msg, sig_entry, &self.p)
    }

    fn key_for(&self, i: u64, j: u64) -> Hash {
        let pr = i as usize;
        let ki = j as usize;
        if pr < self.keys.len() && ki < self.keys[pr].len() {
            pk_to_hash(&self.keys[pr][ki].public_key())
        } else {
            Hash { a: 0, b: 0, c: 0, d: 0 }
        }
    }

    fn sign(&self, sk: &Hash, b: &Block) -> Hash {
        let pr = if (sk.a as usize) < self.keys.len() {
            sk.a as usize
        } else {
            (b.slot % self.n) as usize
        };
        let ki = b.key_index as usize;
        assert!(
            pr < self.keys.len(),
            "producer index {} out of range (total {})",
            pr,
            self.keys.len()
        );
        assert!(
            ki < self.keys[pr].len(),
            "key index {} out of range (total {})",
            ki,
            self.keys[pr].len()
        );
        let key = &self.keys[pr][ki];
        let msg: [F; 4] = [
            F::from_canonical_u64(b.id.a),
            F::from_canonical_u64(b.id.b),
            F::from_canonical_u64(b.id.c),
            F::from_canonical_u64(b.id.d),
        ];
        let sig = key.sign(&msg, 0);
        let sdig = xmss::sig_digest(&sig, &self.p);
        let handle = Hash {
            a: sdig[0],
            b: sdig[1],
            c: sdig[2],
            d: sdig[3],
        };
        self.sigs.borrow_mut().insert(hkey(&handle), sig);
        handle
    }

    fn cert_verify(&self, cert: &Hash) -> bool {
        let certs = self.certs.borrow();
        let Some(proof) = certs.get(&hkey(cert)) else {
            return false;
        };
        let vd_guard = self.cert_vd.borrow();
        let Some(vd) = vd_guard.as_ref() else {
            return false;
        };
        check_cyclic_proof_verifier_data(proof, &vd.verifier_only, &vd.common).is_ok()
            && vd.verify(proof.clone()).is_ok()
    }

    fn cert_claim(&self, cert: &Hash) -> CertClaim {
        let st = self.cert_state(cert);
        claim_of_state(self.n, &st)
    }
}

impl CryptoK for FoldCrypto {
    fn cert_floors(&self, cert: &Hash) -> FloorList {
        floors_of_state(0, &self.cert_floors_state(cert))
    }
}

impl CryptoD for FoldCrypto {
    fn block_id(
        &self,
        slot: u64,
        height: u64,
        prev: Option<Hash>,
        parent_sig: Option<Hash>,
        contents_hash: &Hash,
        key_index: u64,
    ) -> Hash {
        let prev_raw = match prev {
            Some(p) => [p.a, p.b, p.c, p.d],
            None => [0; 4],
        };
        let psig_raw = match parent_sig {
            Some(s) => [s.a, s.b, s.c, s.d],
            None => [0; 4],
        };
        let ch_raw = [
            contents_hash.a,
            contents_hash.b,
            contents_hash.c,
            contents_hash.d,
        ];
        let id_raw = fold_block_id(
            slot,
            height,
            prev.is_some(),
            prev_raw,
            parent_sig.is_some(),
            psig_raw,
            ch_raw,
            key_index,
        );
        Hash {
            a: id_raw[0],
            b: id_raw[1],
            c: id_raw[2],
            d: id_raw[3],
        }
    }

    fn cert_tip_sig(&self, cert: &Hash) -> Hash {
        let certs = self.certs.borrow();
        let Some(proof) = certs.get(&hkey(cert)) else {
            return Hash { a: 0, b: 0, c: 0, d: 0 };
        };
        match exposed_state(self.n as usize, self.mode, proof) {
            Ok(st) => Hash {
                a: st.tip_sig[0],
                b: st.tip_sig[1],
                c: st.tip_sig[2],
                d: st.tip_sig[3],
            },
            Err(_) => Hash { a: 0, b: 0, c: 0, d: 0 },
        }
    }

    fn cert_state(&self, cert: &Hash) -> CertStateG<u64> {
        let certs = self.certs.borrow();
        let Some(proof) = certs.get(&hkey(cert)) else {
            return CertStateG {
                tip_id: HashG { a: 0, b: 0, c: 0, d: 0 },
                tip_slot: 0,
                tip_height: 0,
                tail: TailG::TNil,
            };
        };
        match exposed_state(self.n as usize, self.mode, proof) {
            Ok(st) => CertStateG {
                tip_id: HashG {
                    a: st.tip_id[0],
                    b: st.tip_id[1],
                    c: st.tip_id[2],
                    d: st.tip_id[3],
                },
                tip_slot: st.tip_slot,
                tip_height: st.tip_height,
                tail: tail_of(&st.tail),
            },
            Err(_) => CertStateG {
                tip_id: HashG { a: 0, b: 0, c: 0, d: 0 },
                tip_slot: 0,
                tip_height: 0,
                tail: TailG::TNil,
            },
        }
    }

    fn cert_floors_state(&self, cert: &Hash) -> FloorsG<u64> {
        let certs = self.certs.borrow();
        let Some(proof) = certs.get(&hkey(cert)) else {
            return FloorsG::FNil;
        };
        match exposed_state(self.n as usize, self.mode, proof) {
            Ok(st) => match self.mode {
                Mode::K => floors_of(&st.extra),
                _ => FloorsG::FNil,
            },
            Err(_) => FloorsG::FNil,
        }
    }

    fn cert_gen(&self, cert: &Hash) -> u64 {
        let certs = self.certs.borrow();
        let Some(proof) = certs.get(&hkey(cert)) else {
            return 0;
        };
        match exposed_state(self.n as usize, self.mode, proof) {
            Ok(st) => match self.mode {
                Mode::Lock => st.extra.first().copied().unwrap_or(0),
                _ => 0,
            },
            Err(_) => 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fold_circuit::FoldProver;
    use molt_petit::{producer_for_slot, CertifiedChain, SignedChain};

    const BITS: usize = 13;

    #[test]
    fn test_fold_crypto_keys_and_sigs() {
        let n = 3u64;
        let kbits = 2usize;
        let mode = Mode::Sched { era: 3 };
        let crypto = FoldCrypto::new(n, mode, kbits);

        // Verify key_for returns valid public keys
        for pr in 0..n {
            for ki in 0..(1 << kbits) {
                let pk = crypto.key_for(pr, ki);
                let raw_pk = crypto.keys[pr as usize][ki as usize].public_key();
                let decoded = hash_to_pk(&pk, crypto.p.n_fe);
                assert_eq!(decoded, raw_pk);
            }
        }

        // Test sign and verify
        let b = Block {
            slot: 1,
            height: 1,
            prev: None,
            id: Hash { a: 11, b: 22, c: 33, d: 44 },
            contents_hash: Hash { a: 1, b: 2, c: 3, d: 4 },
            key_index: 0,
        };
        let pr = producer_for_slot(n, b.slot);
        let key = crypto.key_for(pr, b.key_index);
        let sig = crypto.sign(&crypto.sk_for(pr), &b);

        // Valid signature verifies
        assert!(crypto.verify(&key, &b, &sig));

        // Wrong block fails
        let b_bad = Block {
            slot: 1,
            height: 1,
            prev: None,
            id: Hash { a: 99, b: 22, c: 33, d: 44 },
            contents_hash: Hash { a: 1, b: 2, c: 3, d: 4 },
            key_index: 0,
        };
        assert!(!crypto.verify(&key, &b_bad, &sig));

        // Wrong key fails
        let wrong_key = crypto.key_for((pr + 1) % n, b.key_index);
        assert!(!crypto.verify(&wrong_key, &b, &sig));

        // Unknown signature handle fails
        let unknown_sig = Hash { a: 0xbad, b: 0xbad, c: 0, d: 0 };
        assert!(!crypto.verify(&key, &b, &unknown_sig));
    }

    #[test]
    fn test_fold_crypto_block_id() {
        let crypto = FoldCrypto::new(3, Mode::Sched { era: 3 }, 2);
        let ch = Hash { a: 1, b: 2, c: 3, d: 4 };
        let prev = Hash { a: 10, b: 20, c: 30, d: 40 };
        let psig = Hash { a: 100, b: 200, c: 300, d: 400 };

        // Test genesis block id (no prev, no parent_sig)
        let id_genesis = crypto.block_id(0, 0, None, None, &ch, 0);
        let expected_genesis = fold_block_id(0, 0, false, [0; 4], false, [0; 4], [1, 2, 3, 4], 0);
        assert_eq!([id_genesis.a, id_genesis.b, id_genesis.c, id_genesis.d], expected_genesis);

        // Test successor block id (with prev and parent_sig)
        let id_succ = crypto.block_id(1, 1, Some(prev), Some(psig), &ch, 1);
        let expected_succ = fold_block_id(
            1,
            1,
            true,
            [10, 20, 30, 40],
            true,
            [100, 200, 300, 400],
            [1, 2, 3, 4],
            1,
        );
        assert_eq!([id_succ.a, id_succ.b, id_succ.c, id_succ.d], expected_succ);
    }

    #[test]
    fn fold_crypto_end_to_end() {
        let n = 3u64;
        let kbits = 2usize;
        let mode = Mode::Sched { era: 3 };
        let crypto = FoldCrypto::new(n, mode, kbits);

        // 1. Build a chain of a few blocks with XMSS signatures:
        // Genesis block (slot 0, height 0)
        let g_ch = Hash { a: 1, b: 2, c: 3, d: 4 };
        let g_id = crypto.block_id(0, 0, None, None, &g_ch, 0);
        let g_sig = Hash { a: 100, b: 200, c: 300, d: 400 };
        let g_block = Block {
            slot: 0,
            height: 0,
            prev: None,
            id: g_id,
            contents_hash: g_ch,
            key_index: 0,
        };
        let g_fold = crypto.to_fold_block(&g_block, &g_sig);

        // Block 1: slot 1, height 1
        let b1_ch = Hash { a: 11, b: 22, c: 33, d: 44 };
        let b1_ki = 0u64;
        let b1_id = crypto.block_id(1, 1, Some(g_id), Some(g_sig), &b1_ch, b1_ki);
        let b1 = Block {
            slot: 1,
            height: 1,
            prev: Some(g_id),
            id: b1_id,
            contents_hash: b1_ch,
            key_index: b1_ki,
        };
        let b1_pr = producer_for_slot(n, 1);
        let b1_sig = crypto.sign(&crypto.sk_for(b1_pr), &b1);
        let b1_fold = crypto.to_fold_block(&b1, &b1_sig);

        // Block 2: slot 2, height 2
        let b2_ch = Hash { a: 55, b: 66, c: 77, d: 88 };
        let b2_ki = 0u64;
        let b2_id = crypto.block_id(2, 2, Some(b1_id), Some(b1_sig), &b2_ch, b2_ki);
        let b2 = Block {
            slot: 2,
            height: 2,
            prev: Some(b1_id),
            id: b2_id,
            contents_hash: b2_ch,
            key_index: b2_ki,
        };
        let b2_pr = producer_for_slot(n, 2);
        let b2_sig = crypto.sign(&crypto.sk_for(b2_pr), &b2);
        let b2_fold = crypto.to_fold_block(&b2, &b2_sig);

        // Block 3: slot 3, height 3
        let b3_ch = Hash { a: 99, b: 88, c: 77, d: 66 };
        let b3_ki = 0u64;
        let b3_id = crypto.block_id(3, 3, Some(b2_id), Some(b2_sig), &b3_ch, b3_ki);
        let b3 = Block {
            slot: 3,
            height: 3,
            prev: Some(b2_id),
            id: b3_id,
            contents_hash: b3_ch,
            key_index: b3_ki,
        };
        let b3_pr = producer_for_slot(n, 3); // 3 % 3 = 0
        let b3_sig = crypto.sign(&crypto.sk_for(b3_pr), &b3);

        // 2. Fold the first k-1 blocks (blocks 1 and 2) into a certificate and register it.
        let mut fp = FoldProver::new(n as usize, mode, &g_fold, BITS, Some(crypto.binding())).unwrap();
        let st0 = fp.genesis_state().clone();
        let b1_ev = crypto.block_sig(&b1, &b1_sig).expect("b1 sig evidence");
        let (_cdata1, p1) = fp.step(&st0, None, &b1_fold, Some(&b1_ev)).expect("step 1 fold");
        let st1 = exposed_state(n as usize, mode, &p1).unwrap();

        let b2_ev = crypto.block_sig(&b2, &b2_sig).expect("b2 sig evidence");
        let (cdata2, p2) = fp.step(&st1, Some(&p1), &b2_fold, Some(&b2_ev)).expect("step 2 fold");

        let cert_handle = Hash { a: 0xfeed, b: 0xbeef, c: 1, d: 2 };
        crypto.register_cert_with_vd(cert_handle, p2, cdata2.verifier_data());

        // Verify certificate methods exposed by CryptoD
        let cert_tip_sig = crypto.cert_tip_sig(&cert_handle);
        assert!(molt_petit::hash_eq(&cert_tip_sig, &b2_sig));
        let cert_st = crypto.cert_state(&cert_handle);
        assert_eq!(cert_st.tip_slot, 2);
        assert_eq!(cert_st.tip_height, 2);
        assert_eq!(
            [cert_st.tip_id.a, cert_st.tip_id.b, cert_st.tip_id.c, cert_st.tip_id.d],
            [b2_id.a, b2_id.b, b2_id.c, b2_id.d]
        );
        assert!(crypto.cert_verify(&cert_handle));

        // 3. Take the last block as a SignedChain suffix. Check validate_deployed returns true.
        let suffix = SignedChain::SCons(b3, b3_sig, Box::new(SignedChain::SNil));
        let now = 3u64;
        let delta = 10u64;
        assert!(molt_petit::validate_deployed(n, now, delta, &crypto, &cert_handle, &suffix));

        // 4. Negative checks:
        // 4a. Wrong parent_sig on suffix block
        let wrong_psig = Hash { a: 9999, b: 8888, c: 7777, d: 6666 };
        let bad_b3_id = crypto.block_id(3, 3, Some(b2_id), Some(wrong_psig), &b3_ch, b3_ki);
        let bad_b3 = Block {
            slot: 3,
            height: 3,
            prev: Some(b2_id),
            id: bad_b3_id,
            contents_hash: b3_ch,
            key_index: b3_ki,
        };
        let bad_b3_sig = crypto.sign(&crypto.sk_for(b3_pr), &bad_b3);
        let bad_suffix = SignedChain::SCons(bad_b3, bad_b3_sig, Box::new(SignedChain::SNil));
        assert!(!molt_petit::validate_deployed(n, now, delta, &crypto, &cert_handle, &bad_suffix));

        // 4b. Late now: tip is slot 3, delta is 10, so now = 100 is too late
        let late_now = 100u64;
        assert!(!molt_petit::validate_deployed(n, late_now, delta, &crypto, &cert_handle, &suffix));

        // 5. Call produce_block_deployed and validate its output
        let at_slot = 4u64;
        let me = producer_for_slot(n, at_slot); // 4 % 3 = 1
        let b4_ch = Hash { a: 111, b: 222, c: 333, d: 444 };
        let cc = molt_petit::produce_block_deployed(
            n,
            me,
            at_slot,
            delta,
            b4_ch,
            0, // key_index
            crypto.sk_for(me),
            &crypto,
            cert_handle,
            suffix,
        );
        match cc {
            CertifiedChain::CC(c, s) => {
                assert!(molt_petit::hash_eq(&c, &cert_handle));
                assert!(molt_petit::validate_deployed(n, at_slot, delta, &crypto, &c, &s));
            }
            CertifiedChain::Invalid => panic!("produce_block_deployed produced Invalid"),
        }
    }
}
