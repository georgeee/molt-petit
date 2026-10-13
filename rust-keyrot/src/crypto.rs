//! `KeyRotCrypto` — the concrete [`molt_petit::Crypto`] dictionary for the
//! integration.
//!
//! It instantiates the consensus's opaque cryptographic interface with real
//! primitives:
//!
//! * **block-producer signatures** — a signature is a plonky2 proof of
//!   knowledge of the secret key behind `pk = Poseidon(sk)[0]` (see
//!   [`crate::pok`]); no dedicated signature scheme;
//! * **certificates** — the validator proof ([`crate::spec`]), verified by
//!   re-running the verifier.
//!
//! Proofs are far wider than 256 bits, while the consensus passes them around
//! as opaque `Hash` handles. So the handle is a Poseidon commitment and the
//! real object lives in a side table here — exactly the "the protocol never
//! inspects them, it only passes them to the dictionary" contract of the trait.
//! Interior mutability (`RefCell`) lets `&self` methods populate the tables.

use std::cell::RefCell;
use std::collections::HashMap;

use plonky2::field::types::{Field, PrimeField64};
use plonky2::plonk::circuit_data::VerifierCircuitData;
use plonky2::plonk::proof::ProofWithPublicInputs;

use molt_petit::{
    Block, CertClaim, CertStateG, Chain, Crypto, CryptoD, FloorsG, Hash, HashG, TailG,
};

use crate::pok::{self, PokSig};
use crate::poseidon_util::*;
use crate::spec;
use crate::types::{C, D, F};

/// A `Hash` flattened to a hashable/orderable key for the side tables.
type HKey = (u64, u64, u64, u64);

fn hkey(h: &Hash) -> HKey {
    (h.a, h.b, h.c, h.d)
}

/// A boundary-buffer block, stored so `cert_claim` can rebuild the claim's tail
/// `Chain` on demand (the consensus `Chain`/`CertClaim` are not `Clone`).
#[derive(Clone)]
pub struct BlockRec {
    pub slot: u64,
    pub height: u64,
    pub prev: Option<Hash>,
    pub id: Hash,
    pub contents: Hash,
    /// Declared key version (`Block::key_index`). The demo gives each producer
    /// one key, so every block declares version 0.
    pub key_index: u64,
}

impl BlockRec {
    pub fn of(b: &Block) -> Self {
        Self {
            slot: b.slot,
            height: b.height,
            prev: b.prev,
            id: b.id,
            contents: b.contents_hash,
            key_index: b.key_index,
        }
    }
    pub fn to_block(&self) -> Block {
        Block {
            slot: self.slot,
            height: self.height,
            prev: self.prev,
            id: self.id,
            contents_hash: self.contents,
            key_index: self.key_index,
        }
    }
}

/// What a registered certificate carries: the recursive proof to verify (whose
/// public inputs *prove* the consensus tip and the committed application state)
/// and the boundary buffer the claim covers (needed only for the native
/// window-density recheck, which is not part of the proof).
struct CertEntry {
    proof: ProofWithPublicInputs<F, C, D>,
    tail: Vec<BlockRec>,
}

pub struct KeyRotCrypto {
    n: u64,
    /// Fixed block-producer secret keys (one per participant `0..n`).
    producer_sk: Vec<F>,
    producer_pk: Vec<F>,
    /// The proof-of-knowledge signature circuit (built once, reused).
    pok: PokSig,
    /// Verifier for the certificate proof (the validator circuit).
    cert_vd: VerifierCircuitData<F, C, D>,
    /// handle -> the PoK proof that is the signature.
    sigs: RefCell<HashMap<HKey, ProofWithPublicInputs<F, C, D>>>,
    /// handle -> registered certificate.
    certs: RefCell<HashMap<HKey, CertEntry>>,
}

impl KeyRotCrypto {
    pub fn new(
        n: u64,
        producer_sk: Vec<F>,
        cert_vd: VerifierCircuitData<F, C, D>,
    ) -> Self {
        let producer_pk = producer_sk.iter().map(|sk| pk_of(*sk)).collect();
        Self {
            n,
            producer_sk,
            producer_pk,
            pok: PokSig::build(),
            cert_vd,
            sigs: RefCell::new(HashMap::new()),
            certs: RefCell::new(HashMap::new()),
        }
    }

    /// Deterministic signature handle from the signer and the signed block id.
    fn sig_handle(i: u64, block_id: &Hash) -> Hash {
        let mut xs = vec![pk_of(F::from_canonical_u64(i))];
        xs.extend_from_slice(&hash_to_digest(block_id));
        digest_to_hash(poseidon4(&xs))
    }

    /// Register the validator proof (see [`crate::spec`]) as a certificate over
    /// a consensus prefix. The proof's public inputs prove the tip and the
    /// committed key set; `tail` is the boundary buffer (recent prefix blocks)
    /// the claim exposes for the native density recheck.
    pub fn register_cert(
        &self,
        handle: Hash,
        proof: ProofWithPublicInputs<F, C, D>,
        tail: Vec<BlockRec>,
    ) {
        self.certs
            .borrow_mut()
            .insert(hkey(&handle), CertEntry { proof, tail });
    }
}

impl Crypto for KeyRotCrypto {
    fn verify(&self, key: &Hash, b: &Block, sig: &Hash) -> bool {
        let table = self.sigs.borrow();
        let Some(proof) = table.get(&hkey(sig)) else {
            return false;
        };
        // The signature is a PoK proof; it must be bound to this key and block,
        // and verify under the PoK circuit.
        let expected_pk = hash_to_pk(key);
        let msg = block_signing_digest(b);
        let pis = &proof.public_inputs;
        if pis.len() != pok::PIS_LEN || pis[pok::PK_OFFSET] != expected_pk {
            return false;
        }
        for i in 0..4 {
            if pis[pok::MSG_OFFSET + i] != msg[i] {
                return false;
            }
        }
        self.pok.data.verify(proof.clone()).is_ok()
    }

    /// One key per producer in this demo: the version argument is ignored
    /// (every block declares version 0, see [`BlockRec::key_index`]).
    fn key_for(&self, i: u64, _j: u64) -> Hash {
        pk_to_hash(self.producer_pk[i as usize])
    }

    fn sign(&self, sk: &Hash, b: &Block) -> Hash {
        let i = sk_index(sk);
        let msg = block_signing_digest(b);
        let proof = self.pok.prove(self.producer_sk[i as usize], &msg).expect("pok prove");
        let handle = Self::sig_handle(i, &b.id);
        self.sigs.borrow_mut().insert(hkey(&handle), proof);
        handle
    }

    fn cert_verify(&self, cert: &Hash) -> bool {
        let table = self.certs.borrow();
        match table.get(&hkey(cert)) {
            Some(e) => self.cert_vd.verify(e.proof.clone()).is_ok(),
            None => false,
        }
    }

    fn cert_claim(&self, cert: &Hash) -> CertClaim {
        let table = self.certs.borrow();
        match table.get(&hkey(cert)) {
            Some(e) => {
                // The tip slot/height/id come straight from the proof's public
                // inputs, so the claim is *derived from what the proof attests*
                // (not unverified bookkeeping).
                let pis = &e.proof.public_inputs;
                let tip_id = Hash {
                    a: pis[spec::TIP_ID_OFFSET].to_canonical_u64(),
                    b: pis[spec::TIP_ID_OFFSET + 1].to_canonical_u64(),
                    c: pis[spec::TIP_ID_OFFSET + 2].to_canonical_u64(),
                    d: pis[spec::TIP_ID_OFFSET + 3].to_canonical_u64(),
                };
                let mut tail = Chain::Nil;
                for rec in e.tail.iter().rev() {
                    tail = Chain::Cons(rec.to_block(), Box::new(tail));
                }
                CertClaim {
                    tip_slot: pis[spec::TIP_SLOT_OFFSET].to_canonical_u64(),
                    tip_height: pis[spec::TIP_HEIGHT_OFFSET].to_canonical_u64(),
                    tip_id,
                    tail,
                }
            }
            // Unknown certificate: a benign empty claim. `cert_verify` returns
            // false for the same handle, so validation fails regardless.
            None => CertClaim {
                tip_slot: 0,
                tip_height: 0,
                tip_id: Hash { a: 0, b: 0, c: 0, d: 0 },
                tail: Chain::Nil,
            },
        }
    }
}

/// `n` here is the consensus committee size; unused field guard for clippy.
impl KeyRotCrypto {
    pub fn n(&self) -> u64 {
        self.n
    }
}

impl CryptoD for KeyRotCrypto {
    fn block_id(
        &self,
        slot: u64,
        height: u64,
        prev: Option<Hash>,
        contents_hash: &Hash,
        key_index: u64,
    ) -> Hash {
        let prev_raw = match prev {
            Some(p) => [p.a, p.b, p.c, p.d],
            None => [0; 4],
        };
        let ch_raw = [
            contents_hash.a,
            contents_hash.b,
            contents_hash.c,
            contents_hash.d,
        ];
        let id_raw = fold_block_id(slot, height, prev.is_some(), prev_raw, ch_raw, key_index);
        Hash {
            a: id_raw[0],
            b: id_raw[1],
            c: id_raw[2],
            d: id_raw[3],
        }
    }

    fn cert_state(&self, _cert: &Hash) -> CertStateG<u64> {
        CertStateG {
            tip_id: HashG { a: 0, b: 0, c: 0, d: 0 },
            tip_slot: 0,
            tip_height: 0,
            tail: TailG::TNil,
        }
    }

    fn cert_floors_state(&self, _cert: &Hash) -> FloorsG<u64> {
        FloorsG::FNil
    }

    fn cert_gen(&self, _cert: &Hash) -> u64 {
        0
    }
}

