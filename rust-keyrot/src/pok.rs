//! "Native plonky2 signatures" — a signature is a **proof of knowledge of a
//! secret key**, with no dedicated signature scheme.
//!
//! A public key is `pk = Poseidon(sk)[0]`. A signature on a 256-bit message
//! digest `msg` under `pk` is a plonky2 proof for the statement *"I know `sk`
//! with `Poseidon(sk)[0] = pk`"*, with `pk` and `msg` as public inputs. The
//! proof is bound to that exact `(pk, msg)` (a verifier checks the proof against
//! them), and forging one for a fresh message needs `sk` — so it is a signature.
//!
//! This is used for the block-producer signatures the consensus carries in its
//! signed suffix. (The threshold authorization inside the certificate is the
//! same idea, but folded directly into the certificate circuit — see
//! [`crate::spec`].)

use anyhow::Result;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::iop::target::Target;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData, VerifierCircuitData};
use plonky2::plonk::proof::ProofWithPublicInputs;

use crate::types::{C, D, F};

/// Public-input layout of a PoK signature: `[ pk, msg(4) ]`.
pub const PK_OFFSET: usize = 0;
pub const MSG_OFFSET: usize = 1;
pub const PIS_LEN: usize = 5;

/// The proof-of-knowledge signature circuit (built once, reused per signature).
pub struct PokSig {
    pub data: CircuitData<F, C, D>,
    sk: Target,
    msg: [Target; 4],
}

impl PokSig {
    pub fn build() -> Self {
        let mut b = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
        let sk = b.add_virtual_target();
        let msg = [
            b.add_virtual_target(),
            b.add_virtual_target(),
            b.add_virtual_target(),
            b.add_virtual_target(),
        ];
        // pk = Poseidon(sk)[0]; expose it (and the message) as public inputs.
        let pk = b.hash_n_to_hash_no_pad::<PoseidonHash>(vec![sk]).elements[0];
        b.register_public_inputs(&[pk]);
        b.register_public_inputs(&msg);
        let data = b.build::<C>();
        Self { data, sk, msg }
    }

    pub fn verifier(&self) -> VerifierCircuitData<F, C, D> {
        self.data.verifier_data()
    }

    /// Sign `msg` with `sk` (produce the PoK proof). Its public inputs are
    /// `[Poseidon(sk)[0], msg]`.
    pub fn prove(&self, sk: F, msg: &[F; 4]) -> Result<ProofWithPublicInputs<F, C, D>> {
        let mut pw = PartialWitness::new();
        pw.set_target(self.sk, sk)?;
        for i in 0..4 {
            pw.set_target(self.msg[i], msg[i])?;
        }
        self.data.prove(pw)
    }
}
