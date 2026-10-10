//! Shared Plonky2 type aliases.

use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::plonk::config::PoseidonGoldilocksConfig;

/// Extension degree for the recursion-friendly config.
pub const D: usize = 2;

/// The proof config: Poseidon over Goldilocks (recursion-friendly).
pub type C = PoseidonGoldilocksConfig;

/// The base field.
pub type F = GoldilocksField;
