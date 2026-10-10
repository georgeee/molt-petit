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
  - `stateView n st : Nat × Nat × Nat × List Nat`: `hashToNat` of the tip id, the slot, the height, and the present slots `s` of `st.tail` with `tip_slot + 2 - n ≤ s`. The buffer is a superset of the claim's tail, so the view must filter the same way `modelClaimOf` does.
  - `tailSlots`, `hashGToNat`.
  - `FoldKOut`, `FoldSchedOut`, `FoldLockOut`: the drivers, also naming the final state, which is the circuit's public state.
- Rust (`rust/src/lib.rs`, appended):
  - `pub trait CryptoK: Crypto { fn cert_floors(&self, cert: &Hash) -> FloorList; }`
  - `validate_certified_chain_k<C: CryptoK>`: it runs `cert_verify`, `sigs_ok`, and `validate_suffix_k(n, cl, crypto.cert_floors(cert), stripped)`.
  - Floors come from the certificate, never from the caller.
  - Additive. `Crypto` and `validate_certified_chain` are unchanged, so no existing proof moves.

## The certificate assumption (what a deployment provides)

Today `thm_rust_timed_certified_agreement` takes `hUnf`: a verifying certificate's claim is `GroundedCert`. That is a protocol-level property assumed of a cryptographic object. The replacement is the proof system's knowledge soundness, about the fold:

    hFoldK : ∀ cert, cert_verify crypto cert = ok true →
      ∃ bs stO out cl fl, (∀ b ∈ bs, Signed (toModelBlock b)) ∧
        FoldKOut n q (genesisState n G) (initFloors n G.key_index) bs stO out ∧
        cert_claim crypto cert = ok cl ∧ claimView (toModelClaim cl) = stateView n stO ∧
        cert_floors crypto cert = ok fl ∧ (∀ j < n, floor_lookup fl j = floorsFun out j)

This is exactly what a plonky2 proof of `fold_circuit` attests, given:

- the genesis and `n` as constants;
- `Signed` as the per-step signature subproof plus the registry path;
- `cert_claim` / `cert_floors` decoding the public inputs.

## Statements

The three statements below are in `Spec/Statements.lean`. The helper facts (the final state's view is `modelClaimOf`'s; `windowCount` reads only slots) are proof steps, not statements.

3. `thm_cert_fold_k_client`: from `hFoldK` and `validate_certified_chain_k I n crypto (.CC cert suffix) = ok true` there is a claim `cl₀` such that:
   - `GroundedCertK n Signed G cl₀ g` holds, and `g` is the certificate's floor list (`floor_lookup (cert_floors cert) j = g j` for `j < n`);
   - `claimView cl₀ = claimView (toModelClaim cl)`;
   - the conclusions of `thm_validate_suffix_k_sound` hold against `cl₀` with that `g`.

   These are the premises of the mode-1 certified agreement (`KeyStealingCert`, `hcl` + `hMono`), with the floor now the certificate's. **N2 closed.**
4. Modes 2 and 3: the same with `FoldSched` / `FoldLock` and `validate_certified_chain`. The result is a `cl₀` with `GroundedCertSched` / `GroundedCertLock` and the same view. That is the hypothesis of the mode-2/3 certified theorems, now from the circuit's knowledge soundness. **N5 closed.**

## Paper (free sections; nothing before "What a deployment must provide")

- Section rotation (about line 1040): "the shipped certificate claim carries no version floors … future work" becomes a statement that the fold certificate carries them and the boundary check uses them, with theorem 3 cited.
- Section impl (about line 1576): the same, and say that `validate_certified_chain_k` takes its floors from the certificate.
- Lines 1268 and 1460: the `GroundedCertSched` / `GroundedCertLock` hypotheses are discharged by the fold circuit (theorem 4).
- Measurements: one fold step, unsigned and signed, measured on the reference host, with the recursion floor in the same run.
- New disclosure: the older batch/inline prototype circuits are cost measurements only. They bind neither chain nor signatures.
- Section "What a deployment must provide": the certificate assumption is now `hFold*`, knowledge soundness of the fold circuit, not `GroundedCert` of the claim.

## Proof steps (Archon, after Stage A; one per turn, in `Rust/FoldStep.lean`)

11. **Final state.** Prove `FoldKOut … → FoldK …`, and the same for Sched and Lock (forget the final state). Then prove that under the genesis start, `TailRepr n stO (modelClaimOf n G bs)` holds, using steps 5 and 6. Then `stateView n.val stO = claimView (modelClaimOf …)`:
    - `hashGToNat (toHashG h) = hashToNat h`;
    - `tailSlots = presentSlots`;
    - the filter equation of `TailRepr`.
12. **Mode 1 client.** Prove `cert_fold_k_client : MoltPaper.thm_cert_fold_k_client`.
    - Unfold `validate_certified_chain_k` (`hval`, as `validate_certified_chain` is unfolded in the existing certified proofs) to get `cert_verify`, and `validate_suffix_k n cl fl (.Cons s1 tl) = ok true`.
    - `hFoldK` gives `bs stO out cl fl`.
    - Take `cl₀ := modelClaimOf …` and `g := floorsFun out`.
    - `GroundedCertK` is `cert_fold_k_sound` applied after step 11.
    - The suffix conclusions come from `validate_suffix_k_sound` against `cl`, rewritten to `cl₀` through `claimView` equality. The tip fields are equal. `windowCount (A ++ s) u n` depends only on `A.map slot`; prove that lemma once.
13. **Modes 2 and 3.** Prove `cert_fold_sched_client` and `cert_fold_lock_client` the same way. They are shorter, with no suffix part.
14. **Aliases.** Add the three to `Paper/Proofs.lean`, then run the full check.
