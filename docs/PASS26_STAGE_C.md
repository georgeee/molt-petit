# Pass 26, Stage C: from the circuit's public state to the client theorems

Stage A proves that the verified fold step, run from the genesis block over `bs`, yields a `GroundedCert*` claim for `modelClaimOf n G bs`. Stage B (`rust-keyrot/src/fold_circuit.rs`) is a recursive certificate that runs that step and exposes the fold state:

- the tip;
- the tail buffer, as `(flag, slot)` entries;
- the floors (mode 1) or the generation `g` (mode 3).

Stage C connects that state to what a client checks.

## The gap

`CertClaim.tail` is a list of blocks, and `GroundedCert*` fixes it exactly: the tail is the real blocks of the history. The certificate exposes only their slots. A client decoding the public inputs therefore holds a claim whose tail blocks are right in their slots and arbitrary elsewhere.

Every client check reads the tail only through `windowCount`, which reads only slots. So the claim a client holds is as good as the grounded one, provided the two agree on the **view**:

    claimView cl := (cl.tipId, cl.tipSlot, cl.tipHeight, cl.tail.map (·.slot))

## Definitions (reviewer)

- `Spec/Model.lean`: `claimView`.
- `Spec/RustBridge.lean`:
  - `stateView n st : Nat × Nat × Nat × List Nat`: `hashToNat` of the tip id, the slot, the height, and `presentSlots st.tail`.
  - `floorListOf (fl : FloorsG U64) : molt_petit.FloorList`: entries `(i, fl_i)` for `i = 0..n-1`, which is the canonical shape `floors_shape_ok` wants.
- Rust (`rust/src/lib.rs`, appended):
  - `pub trait CryptoK: Crypto { fn cert_floors(&self, cert: &Hash) -> FloorList; }`
  - `validate_certified_chain_k<C: CryptoK>`: it runs `cert_verify`, `sigs_ok`, and `validate_suffix_k(n, cl, crypto.cert_floors(cert), stripped)`.
  - Floors come from the certificate, never from the caller.
  - Additive. `Crypto` and `validate_certified_chain` are unchanged, so no existing proof moves.

## The certificate assumption (what a deployment provides)

Today `thm_rust_timed_certified_agreement` takes `hUnf`: a verifying certificate's claim is `GroundedCert`. That is a protocol-level property assumed of a cryptographic object. The replacement is the proof system's knowledge soundness, about the fold:

    hFoldK : ∀ cert, I.cert_verify crypto cert = ok true →
      ∃ bs out cl, (∀ b ∈ bs, Signed (toModelBlock b)) ∧
        FoldK n q (genesisState n G) (initFloors n G.key_index) bs out ∧
        I.cert_claim crypto cert = ok cl ∧
        claimView (toModelClaim cl) = claimView (modelClaimOf n (toModelBlock G) (bs.map toModelBlock)) ∧
        IK.cert_floors crypto cert = ok (floorListOf out)

This is exactly what a plonky2 proof of `fold_circuit` attests, given:

- the genesis and `n` as constants;
- `Signed` as the per-step signature subproof plus the registry path;
- `cert_claim` / `cert_floors` decoding the public inputs.

## Statements

1. `thm_validate_suffix_k_view`: `validate_suffix_k n cl fl s` depends on `cl` only through `claimView (toModelClaim cl)`. If two claims have the same view, the results are equal. The same holds for `validate_suffix`.
2. `thm_claimView_modelClaimOf`: under `FoldK`/`FoldSched`/`FoldLock` with the genesis start, `stateView n out_state = claimView (modelClaimOf …)`. This is Stage A's `TailRepr`, read off at the end.
3. `thm_cert_fold_k_client`: from `hFoldK` and `validate_certified_chain_k I n crypto (.CC cert suffix) = ok true` there is a claim `cl₀` such that:
   - `GroundedCertK n Signed G cl₀ (floorsFun out)` holds;
   - `claimView cl₀ = claimView (toModelClaim cl)`;
   - the conclusions of `thm_validate_suffix_k_sound` hold against `cl₀` with `g = floorsFun out`.

   These are the premises of the mode-1 certified agreement (`KeyStealingCert`, `hcl` + `hMono`), with the floor now the certificate's. **N2 closed.**
4. Modes 2 and 3: the same with `FoldSched` / `FoldLock` and `validate_certified_chain`. The result is a `cl₀` with `GroundedCertSched` / `GroundedCertLock` and the same view. That is the hypothesis of the mode-2/3 certified theorems, now from the circuit's knowledge soundness. **N5 closed.**

## Paper (free sections; nothing before "What a deployment must provide")

- Section rotation (about line 1040): "the shipped certificate claim carries no version floors … future work" becomes a statement that the fold certificate carries them and the boundary check uses them, with theorem 3 cited.
- Section impl (about line 1576): the same, and say that `validate_certified_chain_k` takes its floors from the certificate.
- Lines 1268 and 1460: the `GroundedCertSched` / `GroundedCertLock` hypotheses are discharged by the fold circuit (theorem 4).
- Measurements: one fold step, unsigned and signed, measured on the reference host, with the recursion floor in the same run.
- New disclosure: the older batch/inline prototype circuits are cost measurements only. They bind neither chain nor signatures.
- Section "What a deployment must provide": the certificate assumption is now `hFold*`, knowledge soundness of the fold circuit, not `GroundedCert` of the claim.
