//! The set of public keys that control a resource.
//!
//! Slot-based: a fixed-capacity vector where `F::ZERO` marks an empty slot.
//! `add` fills the first empty slot, `remove` zeroes a slot in place. This
//! positional model is what the transition circuits check (a transition
//! touches exactly one slot), and the commitment is `Poseidon(slots)`, which
//! matches the in-circuit hash. Key id `0` is reserved for "empty".

use plonky2::field::types::Field;
use plonky2::hash::hash_types::HashOut;
use plonky2::hash::poseidon::PoseidonHash;
use plonky2::plonk::config::Hasher;

use crate::types::F;

#[derive(Clone)]
pub struct KeySet {
    slots: Vec<F>,
}

impl KeySet {
    /// Map a u64 key id into the field.
    pub fn field_key(id: u64) -> F {
        F::from_canonical_u64(id)
    }

    pub fn new(capacity: usize) -> Self {
        Self {
            slots: vec![F::ZERO; capacity],
        }
    }

    pub fn from_keys(capacity: usize, ids: impl IntoIterator<Item = u64>) -> Self {
        let mut set = Self::new(capacity);
        for id in ids {
            set.add(id);
        }
        set
    }

    /// Insert `id` into the first empty slot. Returns the slot index, or `None`
    /// if the set is full, the key is already present, or `id == 0`.
    pub fn add(&mut self, id: u64) -> Option<usize> {
        if id == 0 || self.contains(id) {
            return None;
        }
        let idx = self.slots.iter().position(|x| *x == F::ZERO)?;
        self.slots[idx] = Self::field_key(id);
        Some(idx)
    }

    /// Clear the slot holding `id`. Returns the slot index, or `None` if absent.
    pub fn remove(&mut self, id: u64) -> Option<usize> {
        let idx = self.slot_of(id)?;
        self.slots[idx] = F::ZERO;
        Some(idx)
    }

    pub fn slot_of(&self, id: u64) -> Option<usize> {
        let k = Self::field_key(id);
        self.slots.iter().position(|x| *x == k)
    }

    // --- Field-valued key API (used when keys are public keys, not u64 ids) ---

    /// Build a (possibly full) set directly from field-valued keys.
    pub fn from_field_keys(capacity: usize, keys: impl IntoIterator<Item = F>) -> Self {
        let mut slots: Vec<F> = keys.into_iter().collect();
        assert!(slots.len() <= capacity, "more keys than capacity");
        slots.resize(capacity, F::ZERO);
        Self { slots }
    }

    pub fn slot_of_field(&self, pk: F) -> Option<usize> {
        self.slots.iter().position(|x| *x == pk)
    }

    pub fn contains_field(&self, pk: F) -> bool {
        self.slot_of_field(pk).is_some()
    }

    /// Replace `old` with `new` in place. Returns the slot index, or `None` if
    /// `old` is not present.
    pub fn replace(&mut self, old: F, new: F) -> Option<usize> {
        let idx = self.slot_of_field(old)?;
        self.slots[idx] = new;
        Some(idx)
    }

    pub fn contains(&self, id: u64) -> bool {
        self.slot_of(id).is_some()
    }

    pub fn capacity(&self) -> usize {
        self.slots.len()
    }

    pub fn len(&self) -> usize {
        self.slots.iter().filter(|x| **x != F::ZERO).count()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The slot vector (length == capacity) — exactly what the circuit hashes.
    pub fn padded(&self) -> Vec<F> {
        self.slots.clone()
    }

    /// Poseidon commitment to the set (matches the in-circuit hash).
    pub fn commitment(&self) -> HashOut<F> {
        PoseidonHash::hash_no_pad(&self.slots)
    }
}
