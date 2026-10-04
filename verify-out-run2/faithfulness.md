# Faithfulness Audit

Adversarial audit of formal and prose claims in `paper/molt.tex` against Lean 4 definitions and theorems (`verify-out/lean-statements.txt`, `verify-out/claims.json`, and source files in `Molt/`, `MoltPetit/`, and `Rust/`).

---

### C1

a. **Hypotheses**: The paper states: *"All safety claims are machine-checked in Lean~4 --- the core claims about the imported Rust validator source itself, proved sound against the model and re-used as the recursive-proof circuit, and today's key-rotation results at model level."* The Lean formalizations of safety require substantial undisclosed hypotheses: Byzantine quorum bounds (`ByzantineBounded n bad`), cryptographic unforgeability (`SigUnforgeableRecent`), signature hash injectivity (`SignedHashInjective`), certificate grounding (`GroundedCert`), tip recency (`now ≤ sTip.slot + n`), and suffix length/overlap bounds. Most critically, the statement asserts that the imported Rust source is *"re-used as the recursive-proof circuit"*, but Lean does **not** verify the Plonky2 recursive circuit backend (`Rust/Equiv.lean:15` explicitly notes: *"that the plonky2 circuit's CircuitBackend faithfully implements arithmetic is an external trust assumption, not a theorem"*).

b. **Conclusion**: Overclaim. The claim asserts without qualification that *"All safety claims are machine-checked in Lean 4"* and that the verified Rust source serves as the recursive-proof circuit. The Lean development proves soundness of the Rust AST under `U64Backend` against the Lean model, but does not prove the soundness or arithmetic faithfulness of the Plonky2 constraint circuit.

c. **Quantifiers, parameter ranges and definitions**: Parameter constraints ( \ge 1$, f < n$, synchrony bound $\Delta$) are entirely omitted from the abstract prose.

d. **Convenience assumptions**: The faithfulness of the circuit backend is an external trust assumption admitted outside the Lean kernel. Cryptographic security (unforgeability, collision resistance) is hypothesized rather than reduced to standard hard problems.

e. **Do the Lean definitions mean what the prose says?** Only partially. The Rust validator code is verified against the model, but the recursive circuit is not machine-checked.

Severity: MAJOR
Fix: Qualify that safety theorems hold under standard cryptographic and synchrony assumptions and that circuit backend equivalence is an external trust assumption.

---

### C2

a. **Hypotheses**: The paper states: *"If the certificate verifies and its tip is recent, the client may act on everything $ blocks deep --- and that guarantee is a machine-checked theorem about the shipped validator code, not a design argument."*
Lean's ground-truth theorem (`@Rust.rust_recent_tip_ancestor_mem`) requires extensive undisclosed hypotheses:
1. `1 ≤ ↑n`
2. Byzantine fault budget: `MoltPetit.Model.ByzantineBounded (↑n) bad`
3. Cryptographic unforgeability: `MoltPetit.Model.SigUnforgeableRecent (↑n) bad (Rust.RustSigned I crypto n) signed now ↑n`
4. Hash injectivity: `MoltPetit.Model.SignedHashInjective (Rust.RustSigned I crypto n) G`
5. Verifier signature monotonicity: `∀ (b : MoltPetit.Model.Block), Rust.RustSigned I crypto' n b → Rust.RustSigned I crypto n b`
6. Certificate grounding for both verifiers: `∀ cert, I.cert_verify crypto cert = ok true → ∃ cl, I.cert_claim crypto cert = ok cl ∧ MoltPetit.Model.GroundedCert (↑n) ...`
7. Validation success on two certified chains: `molt_petit.validate_certified_chain` returns ok true for both
8. Non-empty stripped suffixes: `molt_petit.strip_sigs suffix = ok (Cons sr1 srtl)` and for `suffix'`
9. Tip recency for both tips: `now ≤ sTip.slot + ↑n` and `now ≤ sTip'.slot + ↑n`
10. Length and suffix overlap bounds: `↑n < suffix.length`, `sTip.height ≤ sTip'.height`, and `(toModelBlock sr1').height + ↑n ≤ sTip.height`.

b. **Conclusion**: Overclaim. The prose states *"the client may act on everything $ blocks deep"*, implying prefix agreement for the entire chain up to depth $. Lean's theorem only proves agreement for the single ancestor block at index `length - 1 - n` in the suffix, and requires the competing chain's suffix to start at or before that height (`(toModelBlock sr1').height + ↑n ≤ sTip.height`).

c. **Quantifiers, parameter ranges and definitions**: In Lean, $ is a `U64` with  \ge 1$. The prose "everything $ blocks deep" conflates a set of blocks with a single ancestor index `length - 1 - n`.

d. **Convenience assumptions**: `GroundedCert` assumes that any SNARK-verified certificate was created from an honest execution trace of grounded blocks, bypassing proof of SNARK argument system soundness. The suffix overlap condition `(toModelBlock sr1').height + ↑n ≤ sTip.height` assumes competing suffixes overlap at the confirmation boundary.

e. **Do the Lean definitions mean what the prose says?** The Lean theorem proves ancestor agreement for the block at offset $ from tip within the suffix under the stated hypotheses, but the prose elides all cryptographic, Byzantine, and suffix-overlap requirements.

Severity: MAJOR
Fix: State that the guarantee holds subject to Byzantine fault bounds, cryptographic unforgeability/grounding, and competing suffix overlap.

---

### C3

a. **Hypotheses**: The paper states: *"The validator is one Rust file; it is \emph{imported} into Lean~4 (via Charon + Aeneas) and proved sound against the model, so the core safety theorems are about the code that runs (the rotation pins are checked at model level today, Section~
ef{sec:impl}); the same source is re-used as the recursive-proof circuit, so the prover proves the predicate that was verified; and a separate TypeScript implementation is proved sound against that \emph{same} Lean model..."*
For Rust validator soundness (`Rust.rust_valid_chain_sound` and `Rust.rust_valid_chain_k_sound`), the Lean hypotheses are `valid_chain = ok true` and `0 < n ∧ valid_chain_k = ok true`. For TypeScript (`MoltPetit.TS.Bridge.ts_valid_chain_sound`), it requires `validChain = true`. However, the assertion *"the prover proves the predicate that was verified"* rests on the undisclosed assumption that the Plonky2 circuit backend faithfully implements the Rust logic.

b. **Conclusion**: Overclaim regarding the prover circuit. While the Rust and TypeScript native validators are proved sound against `MoltPetit.Model.ValidChain`, the circuit implementation is not verified in Lean. Asserting *"the prover proves the predicate that was verified"* implies verified compilation or equivalence to the circuit gates, which is not machine-checked.

c. **Quantifiers, parameter ranges and definitions**: /bin/bash < n$ is required for hBcsoundness in Lean.

d. **Convenience assumptions**: The translation chains (Charon + Aeneas for Rust; Thales for TypeScript) and the Plonky2 constraint backend are external unverified trust assumptions.

e. **Do the Lean definitions mean what the prose says?** For the software validators (Rust and TypeScript), yes: the Lean soundness theorems prove that any chain accepted by either implementation satisfies the mathematical `ValidChain` specification. For the circuit prover, no.

Severity: MAJOR
Fix: Clarify that the recursive-proof circuit reuses the backend-generic Rust source, but that circuit backend faithfulness is an external audit assumption rather than a Lean-verified equivalence.

---

### C4

a. **Hypotheses**: The paper states: *"The loser recovers by its mode's own discipline --- an in-band rotation in mode 1, a later scheduled generation in mode 2, the next lockstep switch in mode 3 --- at the price of its missed slots (operational discipline; mode 1's half is also checked in the core, \code{liveness\_produce\_blockK})."*
Lean's `liveness_produce_blockK` requires:
- `ByzantineBounded n bad`
- `validChainK n c = true`
- `c.getLast? = some tip`
- `tip.slot < slot`
- `producerForSlot n slot = me`
- `∀ s (B : Block), B ∈ record s → B.slot = s`
- `∀ u, tip.slot + 1 < u + n → u + n ≤ slot + 1 → HonestBlocksCover bad record (c ++ [nextBlock ...]) u n`
- `keyFloor n c me ≤ keyIndex`
None of these hypotheses are disclosed in lines 174-178.

b. **Conclusion**: Overclaim. The prose presents this as a proof that an honest node recovers from key loss (*"The loser recovers by its mode's own discipline... at the price of its missed slots"*). Lean's theorem only proves a local step: if an eligible producer whose slot has arrived chooses a `keyIndex` above `keyFloor` and the density condition is already satisfied across the missed slots (`hCover`), then `produceBlock?` produces a block that passes `validChainK'`. It does not model protocol liveness or prove dynamic recovery after key loss.

c. **Quantifiers, parameter ranges and definitions**: Quantifiers match the local block production step.

d. **Convenience assumptions**: `HonestBlocksCover bad record ... u n` is a major convenience assumption for a liveness theorem: it posits that during the gap of missed slots, honest blocks already satisfy the density quorum in every window.

e. **Do the Lean definitions mean what the prose says?** No. The prose describes dynamic protocol recovery, but the Lean definition is merely a local block production consistency lemma assuming density is preserved.

Severity: MAJOR
Fix: Clarify that `liveness_produce_blockK` is a local single-block production lemma that takes continued density coverage as a hypothesis, not a dynamic protocol recovery theorem.

---

### C5

a. **Hypotheses**: The paper states: *"And in every mode the corruption the theorems count shrinks back to the plain controlled-slot budget of Section~
ef{sec:assumptions} (Lean \code{badKeyrot\_lossOnly}, \code{badSched\_lossOnly}, \code{exposedSched\_lossOnly})."*
In Lean (`Molt.badKeyrot_lossOnly`, `Molt.badSched_lossOnly`, `Molt.exposedSched_lossOnly`), the hypothesis is `Stolen := fun _ _ => False` (no keys are stolen). This is disclosed in the text (*"when keys can be lost but not stolen"*).

b. **Conclusion**: Lean proves that under `Stolen := ⊥`, `badKeyrot` equals `rented`, `badSched` equals `rented`, and `exposedSched` equals `∅`. The paper conclusion matches Lean exactly.

c. **Quantifiers, parameter ranges and definitions**: Quantifiers and definitions match across all parameters ($, $\Delta_{	ext{conf}}$, $	ext{rented}$, $, $	ext{schedule}$, $).

d. **Convenience assumptions**: None; setting `Stolen := ⊥` simplifies definitions directly without artificial or circular axioms.

e. **Do the Lean definitions mean what the prose says?** Yes. The Lean theorems prove that in the absence of theft, corruption counting in all three modes reduces exactly to the rented Byzantine slots.

Verdict: FAITHFUL

---

### C6

a. **Hypotheses**: The paper states: *"A client that misses its cadence must stop acting and re-join from a fresh trusted checkpoint, exactly as if it were new --- operational discipline the theorems force rather than state: past the cadence the theorems' fault-budget assumption becomes one no deployment can stand behind --- quiet thefts accumulate until nothing satisfies it (\code{no\_budget\_beyond}), and re-joining is a fresh trust event outside the formal development."*
In Lean, `@Molt.no_budget_beyond` requires:
- `hP : ∀ i ∈ P, ∃ s, u ≤ s ∧ s < u + n ∧ Molt.producer n s = i ∧ ∃ j, Molt.inForce n Δconf c₀ i s ≤ j ∧ Stolen i j`
- `hbig : Molt.faultBudget n < P.card`
These hypotheses state that $ is a set of distinct producers with active stolen keys in window $ whose cardinality exceeds `faultBudget n`. This is disclosed conceptually in the prose.

b. **Conclusion**: Lean proves `¬ (Molt.badSlotsIn (Molt.badKeyrot n Δconf rented Stolen c₀) u n).card ≤ Molt.faultBudget n`. This matches the prose statement that the fault budget is violated.

c. **Quantifiers, parameter ranges and definitions**: Quantifiers and ranges match Lean.

d. **Convenience assumptions**: None. The theorem is a straightforward counting lemma showing that accumulating more compromised producers in a window than the fault budget necessarily exceeds the window's allowed corrupted slot count.

e. **Do the Lean definitions mean what the prose says?** Yes. The Lean theorem formalizes that when thefts exceed the budget in a window, no rent predicate can satisfy the Byzantine bound.

Verdict: FAITHFUL

---

### C7

a. **Hypotheses**: The paper states: *"(Mode 3's guarantees hold at the certificate presentation as well as for full chains (\code{lockstep\_recent\_certified\_suffix\_agreement})."*
Lean's ground-truth theorem (`@MoltPetit.Model.lockstep_recent_certified_suffix_agreement`) requires extensive undisclosed hypotheses:
1. `1 ≤ n`
2. `LockstepPackage n rosterGen ops registry rented Stolen honestSigned now Δ G R T` (bundles monotonic roster generations, cryptographic unforgeability `SchedCoreUnforgeable`, declared key discipline `honestSigned i s = some B → B.keyIndex = rosterGen (s / n)`, signature hash injectivity `SignedHashInjective`, genesis generation alignment `G.keyIndex = rosterGen (G.slot / n)`, rented slot bound $R$, exposed stolen producers bound $T$, and Byzantine budget bound $R + T \le \lfloor (n-1)/3 \rfloor$).
3. Shared genesis grounding: both certificates must be grounded from the *same* genesis block $G$ (`GroundedCertLock n ... G cl g` and `GroundedCertLock n ... G cl' g').
4. Suffix block linkage to certificate tips: `s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId` (and for $s_1'$).
5. Chain structure: `linksOk (s₁ :: srest) = true` (and for $s_1'$).
6. Quorum density across all windows covering the certificates and suffixes: `∀ u, ↑cl.tipSlot + 2 - ↑n ≤ ↑u → u + n ≤ sTip.slot + 1 → quorum n ≤ windowCount (cl.tail ++ s₁ :: srest) u n` (and for $cl'$).
7. Lockstep generation monotonicity on suffixes: `lockstepFrom n cl.tipSlot g (s₁ :: srest) = true` (and for $cl'$).
8. Signature validity: all suffix blocks signed under declared keys (`∀ B ∈ s₁ :: srest, SignedDeclared n ops registry B`).
9. Tip recency for both suffix tips: `now ≤ sTip.slot + Δ` and `now ≤ sTip' .slot + Δ`.
10. Confirmation depth: both blocks must be at depth $\ge n$ within their respective suffixes (`i + n < (s₁ :: srest).length` and `i' + n < (s₁' :: srest').length`).
11. Absolute height alignment: `cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i'`.

b. **Conclusion**: Overclaim. The prose asserts broadly that *"Mode 3's guarantees hold at the certificate presentation as well as for full chains"*. But Lean only proves agreement for a single block at matching height that is at least $n$ blocks deep inside the suffix presentation ($i + n < \text{length}$), extending certificates that share the same genesis $G$. It does not establish agreement for arbitrary blocks in the certified prefix or full prefix agreement across arbitrary certificate presentations.

c. **Quantifiers, parameter ranges and definitions**: $1 \le n$. Confirmation depth is $\ge n$ within the suffix. The prose parenthetical omits all parameter ranges and side conditions.

d. **Convenience assumptions**: `GroundedCertLock` assumes that certified prefixes are generated by valid executions from a shared genesis $G$, bypassing proof of SNARK argument system soundness.

e. **Do the Lean definitions mean what the prose says?** Only partially. The theorem guarantees single-block agreement at depth $\ge n$ in suffixes extending grounded certificates rooted at a shared genesis, but does not prove the full battery of Mode 3 guarantees for arbitrary certificate presentations.

Severity: MAJOR
Fix: Clarify that certificate presentation guarantees apply to blocks confirmed at depth $\ge n$ within suffixes extending grounded certificates rooted at a shared genesis under the Mode 3 lockstep package.

---

### C8

a. **Hypotheses**: The paper states: *"Erasure's per-generation credit against the budget is machine-checked: under a per-generation census --- for each generation $j$ separately, at most $T$ seats whose generation-$j$ key is stolen --- the same agreement holds at confirmation depth $2n$ instead of $n$, and with no shared-genesis hypothesis (\code{lockstep\_client\_safety\_gen}); the cumulative, depth-$n$ form remains available. Section~\ref{sec:rotation}."*
In Lean (`@MoltPetit.Model.lockstepGen_recent_tip_ancestor_agreement`, aliased as `Molt.lockstep_client_safety_gen`), the hypotheses include:
- `1 ≤ n`
- `LockstepPackageGen n rosterGen ops registry rented Stolen honestSigned now Δ G R T` (unforgeability, declared key discipline, signature hash injectivity, rented slot bound $R$, per-generation stolen key bound $T$, and Byzantine budget $R + T \le \lfloor (n-1)/3 \rfloor$)
- Valid signed chains: `validSignedChainLock n ops registry sc = true` and for `sc'`
- Tip recency for both chains: `now ≤ sTip.slot + Δ` and `now ≤ sTip'.slot + Δ`
- Chain length bounds: `2 * n < (stripSigs sc).length` and `2 * n < (stripSigs sc').length`
- Equal tip height: `sTip.height = sTip'.height`.
The paper discloses the per-generation bound and absence of shared-genesis hypothesis, but omits the equal-tip-height premise in `lockstep_client_safety_gen`.

b. **Conclusion**: Mild overclaim. Stating *"the same agreement holds at confirmation depth $2n$ instead of $n$"* implies general prefix agreement between arbitrary competing chains. However, `lockstep_client_safety_gen` only proves equality of the single ancestor block at index `length - 1 - 2n` under the condition `sTip.height = sTip'.height`. For unequal tip heights, agreement is captured by `lockstepGen_recent_tip_ancestor_mem` (which proves ancestor membership in the competing chain).

c. **Quantifiers, parameter ranges and definitions**: Parameter ranges match: confirmation depth is $2n$, and per-generation thefts are bounded by $T$.

d. **Convenience assumptions**: None beyond standard cryptographic unforgeability and Byzantine bounds. As claimed, the genesis parameter $G$ in `LockstepPackageGen` is unused in the proof, confirming that no shared-genesis hypothesis is required.

e. **Do the Lean definitions mean what the prose says?** Yes. `LockstepPackageGen.genBound` captures the per-generation stolen key census ($\le T$ for each generation $j$), and the theorem establishes depth-$2n$ agreement without requiring a shared genesis.

Severity: MINOR
Fix: Note that `lockstep_client_safety_gen` establishes depth-$2n$ agreement for equal-height tips, while general unequal-height prefix agreement is established by `lockstepGen_recent_tip_ancestor_mem`.

---

### C9

a. **Hypotheses**: None (definitional).
The paper states: *"Slot $s$ belongs to roster seat $s \bmod n$ (\code{producer}): who may produce, and when, is deterministic and public; there is no leader election."*

b. **Conclusion**: Matches Lean's definition (`MoltPetit.Model.producerForSlot n slot = slot % n`, aliased as `Molt.producer`).

c. **Quantifiers, parameter ranges and definitions**: Exact match ($s \bmod n$).

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `producerForSlot n slot` computes `slot % n` deterministically.

Verdict: FAITHFUL

---

### C10

a. **Hypotheses**: None (notational definition).
The paper defines in Table 1: *"$\mathit{keyFor}(i,j)$, \code{keyIndex} & seat $i$'s public key at version $j$; the version a block declares & \S\ref{sec:protocol}"*.

b. **Conclusion**: Matches Lean's structural definition (`MoltPetit.Model.Block.keyIndex : MoltPetit.Model.Block → ℕ`).

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `keyIndex` is a natural number record field on `Block` representing the key version declared by the block's producer.

Verdict: FAITHFUL

---

### C11

a. **Hypotheses**: None (definitional / protocol design description).
The paper states: *"The payload (transactions, in a deployment) travels out of band; \code{contentsHash} commits to it, and no consensus rule ever looks inside it."*

b. **Conclusion**: Matches Lean's definition (`MoltPetit.Model.Block.contentsHash : MoltPetit.Model.Block → ℕ`), which is an uninterpreted commitment field never inspected by `ValidChain` or any consensus rule.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `contentsHash` commits to external payload data without participating in validation logic.

Verdict: FAITHFUL

---

### C12

a. **Hypotheses**: None (definitional / protocol description).
The paper states: *"\code{keyIndex} is the version of the signing key the producer used: key rotation is part of the consensus state, carried in band, and Section~\ref{sec:results} builds on it."*

b. **Conclusion**: Matches Lean's definition (`MoltPetit.Model.Block.keyIndex : MoltPetit.Model.Block → ℕ`).

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `keyIndex` is carried in-band on each block and checked by the key registry and rotation validator rules.

Verdict: FAITHFUL

---

### C13

a. **Hypotheses**: None (definitional / external hashing contract specification).
The paper states: *"\code{prev} is the parent's id, and \code{id} is a hash of the block itself, computed and checked by the deployment's hashing layer under a fixed contract: \[ \mathit{id} \;=\; H(\mathit{slot},\ \mathit{height},\ \mathit{prev},\ \mathit{parentSig},\ \mathit{contentsHash},\ \mathit{keyIndex}). \]"*

b. **Conclusion**: In Lean (`MoltPetit.Model.Block.prev : Option ℕ` and `Block.id : ℕ`), `id` and `prev` are abstract fields. Lean does not implement or compute $H$; the hashing contract is an external specification whose formal residue in Lean is collision resistance (`SignedHashInjective`) and chronological ordering constraints (`TimedExecution`). Additionally, `parentSig` is not a field of `Block` in Lean, but appears when blocks are bundled into `SignedBlock`.

c. **Quantifiers, parameter ranges and definitions**: The paper explicitly attributes the hash computation to "the deployment's hashing layer under a fixed contract", matching its status as an external specification outside Lean's kernel.

d. **Convenience assumptions**: Collision resistance is assumed via `SignedHashInjective` rather than proven from a concrete hash function.

e. **Do the Lean definitions mean what the prose says?** Yes. `prev` represents the optional parent block ID and `id` represents the block hash identifier.

Verdict: FAITHFUL

---

### C14

a. **Hypotheses**: None (definitional).
The paper states: *"A chain is a sequence of blocks with heights increasing by one, slots strictly increasing, and each block linking to its parent's id, rooted at a genesis block --- height zero, no parent (\code{linksOk}, \code{genesisOk}); that the root is the deployment's genesis is what the theorems hypothesize (Section~\ref{sec:assumptions})."*

b. **Conclusion**: Matches Lean's formal definitions:
- `genesisOk b` requires `b.height = 0 ∧ b.prev = none`.
- `childOk parent child` requires `child.height = parent.height + 1 ∧ parent.slot < child.slot ∧ child.prev = some parent.id`.
- `linksOk` checks `childOk` pairwise down the list of blocks.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `linksOk` and `genesisOk` formally capture the exact structural chain criteria described in the prose.

Verdict: FAITHFUL

---

### C15

a. **Hypotheses**: None (definitional).
The paper states: *"A chain must be \emph{dense} (\code{validChain} names the combined structure-and-density checks): every matured window of $n$ consecutive slots must contain at least $\quorum$ blocks of the chain, where a window $[u, u+n)$ has matured once the tip has reached its end, $u + n \le \mathit{tip.slot} + 1$ (\code{denseSoFar})."*

b. **Conclusion**: Matches Lean's formal definitions:
- `denseSoFar n c tip.slot` checks that for all $u$ with $u + n \le tip.slot + 1$ (i.e. $u \in [0, tip.slot + 1 - n]$), $\mathit{quorum}(n) \le \mathit{windowCount}(c, u, n)$.
- `validChain n c` combines `genesisOk`, `linksOk`, and `denseSoFar n c tip.slot`.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The window maturity condition $u + n \le tip.slot + 1$ corresponds directly to Lean's `u ∈ List.range (t + 2 - n)`.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `denseSoFar` checks that every matured window $[u, u+n)$ contains at least $\quorum(n)$ blocks, and `validChain` combines structural linkage with matured window density.

Verdict: FAITHFUL

---

### C16

a. **Hypotheses**: The prose describes the combinatorial intuition of quorum intersection ($2\quorum > n + max$ and honest single-signer discipline). However, the actual Lean safety theorems in Section~
ef{sec:results} require numerous formal hypotheses not mentioned here:
- Cryptographic unforgeability packages (`KeyrotCoreUnforgeable`, `SchedCoreUnforgeable`, `LockstepPackage`).
- Hash collision resistance (`SignedHashInjective`).
- Grounded certificates (`GroundedCertKeyrot`, `GroundedCertSched`, `GroundedCertLock`).
- Client clock synchrony / tip recency (`now ≤ sTip.slot + Δ`).
- Overlap and depth conditions (`i + n < suffix.length`, `s₁.height = cl.tipHeight + 1`).
- Bounded Byzantine corruptions (`ByzantineBounded`).

b. **Conclusion**: Overclaim. Characterizing all safety theorems in Section~
ef{sec:results} as simply *"this counting argument made precise and machine-checked"* reduces multi-layered cryptographic, synchrony, and certificate-grounding theorems to a purely combinatorial intersection lemma.

c. **Quantifiers, parameter ranges and definitions**: N/A (informal prose summary).

d. **Convenience assumptions**: Oversimplification in prose that elides cryptographic and certificate grounding assumptions.

e. **Do the Lean definitions mean what the prose says?** No. While the combinatorial counting argument (`honest_overlap` / pigeonhole) is the core lemma, the safety theorems in Section 4 are complete protocol safety proofs requiring substantial cryptographic and inductive grounding infrastructure.

Severity: MINOR
Fix: Clarify that the counting argument is the core combinatorial engine around which cryptographic unforgeability, certificate grounding, and rotation pin mechanisms are layered.

---

### C17

a. **Hypotheses**: None (definitional).
The paper states: *"Chain validity has one more condition, riding on the \code{keyIndex} field: along the chain, a producer's declared key version never decreases (\code{keyMonoOk}) --- rotation only ever moves forward, and the chain's order is the agreed order in which rotations happen."*

b. **Conclusion**: Matches Lean's formal definitions:
- `keyMonoOk n c` verifies pairwise that for every block pair in the chain, if `producer n b.slot = producer n b'.slot`, then `b.keyIndex ≤ b'.keyIndex`.
- `keyMonoOk_sound` proves that `keyMonoOk n c = true ↔ KeyIndexMonotone n c`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `keyMonoOk` precisely implements monotonic progression of key version indices along the chain for each roster seat.

Verdict: FAITHFUL

---

### C18

a. **Hypotheses**: None (definitional).
The paper states: *"Structure, density, and this monotone rule together are \code{validChainK}: \emph{the} chain validity of this paper."*

b. **Conclusion**: Matches Lean's formal definition:
`validChainK n c := validChain n c && keyMonoOk n c`. Since `validChain` combines structural checks (`genesisOk`, `linksOk`) and density (`denseSoFar`), `validChainK` is literally the boolean conjunction of structure, density, and `keyMonoOk`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `validChainK` conjuncts `validChain` and `keyMonoOk`.

Verdict: FAITHFUL

---

### C19

a. **Hypotheses**: None (interface specifications).
The paper states:
*"The rules touch cryptography only through two small interfaces that a deployment implements:
egin{itemize}
\item \code{SigOps} --- $\mathit{sign}$ and $\mathit{verify}$ --- together with the versioned key map $\mathit{keyFor}(i,j)$, the public key of seat $i$'s signing key at version $j$ (a separate parameter, \code{KeyRegistry}, in the model; the implementation's dictionary folds it into \code{SigOps});
\item \code{CertOps} --- verify a certificate, read its claim, and extend it by one validated block; the implementation's dictionary (Section~
ef{sec:impl}) also exposes a by-tip-id lookup of locally held certificates, which compaction uses.
\end{itemize}"*

b. **Conclusion**: Matches Lean's abstract structures:
- `SigOps σ sk pk`: `sign : sk → Block → σ`, `verify : pk → Block → σ → Bool`.
- `KeyRegistry pk`: `Nat → Nat → pk`.
- `CertOps α`: `claim : α → CertClaim`, `verify : α → Bool`, `generate : α → Block → α`.
The paper explicitly points out that `KeyRegistry` is a separate parameter in the model, and notes the additional `lookupCert` method in the implementation dictionary.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `SigOps`, `KeyRegistry`, and `CertOps` formalize the abstract cryptographic and certification interfaces over generic types $(\sigma, sk, pk, lpha)$.

Verdict: FAITHFUL

---

### C20

a. **Hypotheses**: None (client acceptance rule specification).
The paper states:
*"Accept a certified chain if and only if:
egin{enumerate}
\item it \emph{validates}: the five checks of Section~
ef{sec:rules} --- certificate, signatures at declared versions, linkage, density, and the key-version discipline with the deployment's pin (\code{validCertifiedChain} plus the mode's key checks);
\item it is \emph{recent}: $\mathit{now} \le \mathit{tip.slot} + n$ on the verifier's own clock.
\end{enumerate}"*
The text explicitly discloses that recency is checked against the verifier's own clock outside the validator function.

b. **Conclusion**: Matches Lean's formalization: validation is computed by `validateCertifiedChain` combined with mode-specific pin predicates (e.g. `keyFloor` / `schedPinned` / `lockstepFrom`), and recency is formalized as the hypothesis `now ≤ sTip.slot + Δ` (with $\Delta = n$ in client theorems).

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `validateCertifiedChain` and the recency premise together form the exact precondition under which client safety is guaranteed.

Verdict: FAITHFUL

---

### C21

a. **Hypotheses**: None (definitional header).
The paper states: *"\paragraph{Validate} (\code{validCertifiedChain})."*

b. **Conclusion**: Matches Lean's `validateCertifiedChain` declaration (`MoltPetit.Model.validateCertifiedChain`), which encapsulates the validation logic for a certified chain.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `validateCertifiedChain` is the pure predicate that validates a certified chain by checking the certificate and the suffix.

Verdict: FAITHFUL

---

### C22

a. **Hypotheses**: None (specification of the five certified chain validation checks).
The paper states:
*"Accept a certified chain only if all of the following hold:
egin{enumerate}
\item the certificate verifies (\code{CertOps.verify} --- one cheap check, e.g.\ of a recursive proof);
\item every suffix block's signature verifies under $\mathit{keyFor}(	ext{slot's producer},\ 	ext{declared version})$;
\item the first suffix block extends the claim's tip: height one up, slot strictly later, \code{prev} equal to the tip id --- and every adjacent suffix pair links the same way;
\item every window that matures within the suffix is dense, counted over the claim's boundary buffer plus the suffix (\code{validSuffix});
\item the key-version discipline holds: a producer's declared versions never decrease (\code{keyMonoOk}, Section~
ef{sec:protocol}), and every block's declared version satisfies the deployment's rotation \emph{pin} (a floor in modes 1--2, exact per grid window in mode 3) --- the one mode-specific check, fixed at deployment.
\end{enumerate}"*

b. **Conclusion**: Matches Lean's definitions: Checks 1--4 are implemented in `validateCertifiedChain` via `CertOps.verify` and `validateSuffix` (`sigsOk`, linkage to tip, internal `linksOk`, and matured window density over `claim.tail ++ suffix`). Check 5 is enforced via `keyMonoOk` and rotation pin predicates.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `validateCertifiedChain` and the rotation pin predicates formalize these exact criteria.

Verdict: FAITHFUL

---

### C23

a. **Hypotheses**: The prose refers to the full-chain validators and certificate-level theorems. In Lean, the certificate-level theorems require:
- $1 \le n$,
- Unforgeability packages (`KeyrotCoreUnforgeable`, `SchedCoreUnforgeable`, `LockstepPackage`),
- Hash collision resistance (`SignedHashInjective`),
- Byzantine fault bounds (`ByzantineBounded`),
- Grounded certificates (`GroundedCertKeyrot`, `GroundedCertSched`, `GroundedCertLock`),
- Tip recency (`now ≤ sTip.slot + Δ`),
- Suffix length bounds (`i + n < suffix.length`),
- Linkage and density over `tail ++ suffix`,
- Shared genesis / anchor alignment.

b. **Conclusion**: The prose accurately identifies the structural placement of the rotation pins (in `validSignedChainK'` for full chains, and proven at certificate level in the three named theorems: `keyrot_recent_certified_suffix_agreement`, `sched_recent_certified_suffix_agreement`, and `lockstep_recent_certified_suffix_agreement`).

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Certificate grounding (`GroundedCert*`) is an inductive abstraction rather than an end-to-end verified arithmetic circuit.

e. **Do the Lean definitions mean what the prose says?** Yes. The three named theorems prove certified suffix agreement under each mode's rotation pin.

Verdict: FAITHFUL

---

### C24

a. **Hypotheses**: None (architectural explanation of reference specification vs. incremental implementation).
The paper states:
*"The model replays the structural checks from genesis (\code{validChain}); a deployed node checks only the windows that mature with each arriving block. The two are equivalent --- earlier windows were checked when the parent was validated --- so the incremental check is an optimization, not a loosening."*

b. **Conclusion**: Matches Lean's formalization: `validChain` is the replayed-from-genesis specification, while `validateSuffix` and production code check only windows that mature with arriving blocks.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `validChain` formalizes the complete chain replay specification.

Verdict: FAITHFUL

---

### C25

a. **Hypotheses**: None (definitional header).
The paper states: *"\paragraph{Produce} (\code{produceBlock?})."*

b. **Conclusion**: Matches Lean's `produceBlockCert?` / `Molt.produceBlock?`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `produceBlock?` formalizes the block production function for certified chains.

Verdict: FAITHFUL

---

### C26

a. **Hypotheses**: None (specification of `produceBlock?`).
The paper states:
*"Only in the caller's own slot: build the next block on the current tip, sign it, append it to the suffix --- and ship the result only if it passes the same \code{validSuffix} every other node runs."*

b. **Conclusion**: Matches Lean's `produceBlockCert?` (`MoltPetit.Model.produceBlockCert?`), which checks `producerForSlot n slot = me`, constructs the signed block on the tip, appends it to the suffix, and returns `some (sb, updated_chain)` if and only if `validateSuffix` evaluates to `true`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. The function constructs the candidate block, signs it, and guards output by running `validateSuffix`.

Verdict: FAITHFUL

---

### C27

a. **Hypotheses**: None (definitional header).
The paper states: *"\paragraph{Select} (\code{selectChain})."*

b. **Conclusion**: Matches Lean's `selectCertifiedChain` / `Molt.selectChain`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. `selectChain` adopts a candidate chain over the current chain if and only if the candidate validates and has strictly greater tip height.

Verdict: FAITHFUL

---

### C28

a. **Hypotheses**: None (architectural specification of compaction verification).
The paper states:
*"The compacted chain must then pass \code{validCertifiedChain} like anything else; compaction, like production, is outside the trusted base."*

b. **Conclusion**: Matches the formal and TypeScript implementation (`compact?` / `MoltPetit.TS.Emitted`), where the compacted certificate is verified with `validateCertifiedChain` before being adopted.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. Compaction output is untrusted and must pass `validateCertifiedChain`.

Verdict: FAITHFUL

---

### C29

a. **Hypotheses**: Definitional assumption.
The paper states:
*"At most $\lfloor(n-1)/3\rfloor$ slots in any window of $n$ consecutive slots are Byzantine: in those slots the adversary may deviate arbitrarily from the protocol; in all other slots the designated producer is honest. In a bad slot the adversary fully controls that slot's producer, including feeding it arbitrary content to sign. Corruption is per \emph{slot}, not per participant --- the same participant may be controlled in one of its slots and honest in the next. \quad\textit{(Lean: \code{FaultBounded}.)}"*
Lean defines `ByzantineBounded` (`Molt.FaultBounded`):
`def ByzantineBounded (n : Nat) (bad : ByzantineSlots) : Prop := ∀ u, (badSlotsIn bad u n).card ≤ maxByzantine n` where `maxByzantine n := (n - 1) / 3`. Parameterized by window size `n` and Byzantine slot predicate `bad`, fully disclosed in the text.

b. **Conclusion**: Matches Lean's definition exactly.

c. **Quantifiers, parameter ranges and definitions**: Exact match ($\forall u, |[u, u+n) \cap \text{bad}| \le \lfloor(n-1)/3\rfloor$).

d. **Convenience assumptions**: None; standard sliding-window Byzantine fault budget ($< 1/3$).

e. **Do the Lean definitions mean what the prose says?** Yes. Lean's `ByzantineBounded` bounds the number of Byzantine slots in any window of length $n$ to $\lfloor(n-1)/3\rfloor$.

Verdict: FAITHFUL

---

### C30

a. **Hypotheses**: Definitional assumption.
The paper states:
*"The model gives each participant a \emph{signing log}: at most one block per slot, the one its honest signing path signed (\code{SigningLog})."*
Lean defines `SigningLog` (`Molt.SigningLog`):
`abbrev SigningLog := Nat → Nat → Option Block`.

b. **Conclusion**: Matches Lean's definition. The partial function type `Nat → Nat → Option Block` (mapping participant and slot to an optional block) enforces the constraint that an honest node signs at most one block per slot.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None. Accurately formalizes the single-signing honest node operational discipline.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C31

a. **Hypotheses**: All hypotheses are disclosed in the text.
The paper states:
*"and \emph{(c) freshness} --- on any valid chain \emph{whose tip is recent}, produced in an honest slot and carrying a verifying signature, that block is the unique entry of its producer's signing log for that slot. \quad\textit{(Lean: \code{SigUnforgeableRecent}.)}"*
Lean's `SigUnforgeableRecent` requires:
- `ValidChain n c` ("on any valid chain")
- `∃ t, c.getLast? = some t ∧ now ≤ t.slot + Δ` ("whose tip is recent")
- `¬ bad B.slot` ("produced in an honest slot")
- `Signed B` ("carrying a verifying signature")
All conditions correspond directly to fields of Lean's `verified_was_signed`.

b. **Conclusion**: Matches Lean. Lean establishes `signed (producerForSlot n B.slot) B.slot = some B`. Since `signed` is a partial function returning `Option Block`, the block is indeed the unique entry for that slot.

c. **Quantifiers, parameter ranges and definitions**: Exact match across parameters $n, \text{bad}, \text{Signed}, \text{signed}, \text{now}, \Delta$.

d. **Convenience assumptions**: The recency condition scopes unforgeability to chains whose tip is within $\Delta$ slots of the verifier's clock `now`. As the text explicitly explains in lines 539–541, this scoping prevents stale signature accumulation attacks and is later justified in the timed model (Theorem~\ref{thm:forge}).

e. **Do the Lean definitions mean what the prose says?** Yes. Lean's `SigUnforgeableRecent` formalizes recency-scoped signature unforgeability on valid chains.

Verdict: FAITHFUL

---

### C32

a. **Hypotheses**: Definitional exposition.
The paper states:
*"We call this \emph{hash injectivity}; under rotation the domain is version-stamped signed blocks --- for the chain-level sync-rule results (Theorem~\ref{thm:refresh}), blocks verifying under \emph{some} registered version of their producer (Lean \code{KeyStealingSigned}); for the scheduled, lockstep, and certified results it narrows to blocks verifying under their \emph{declared} version (\code{SignedDeclared}), a strictly weaker assumption --- Section~\ref{sec:protocol} explains why \code{keyIndex} is in the preimage. \quad\textit{(Lean: \code{SignedHashInjective}.)}"*

b. **Conclusion**: Matches Lean.
`KeyStealingSigned` requires verification under some registered version `j`:
`∃ (sig : Sig) (j : Nat), ops.verify (registry (producerForSlot n B.slot) j) B sig = true`.
`SignedDeclared` narrows verification to the block's declared index `B.keyIndex`:
`∃ sig : Sig, ops.verify (registry (producerForSlot n B.slot) B.keyIndex) B sig = true`.
Since `SignedDeclared B → KeyStealingSigned B`, the domain $\{B \mid B = G \lor \text{SignedDeclared } B\}$ is a subset of $\{B \mid B = G \lor \text{KeyStealingSigned } B\}$, making collision resistance over `SignedDeclared` a strictly weaker premise.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C33

a. **Hypotheses**: Definitional assumption.
The paper states:
*"For any two blocks $B, B'$ in the protocol's domain, if $B.\id = B'.\id$ then $B = B'$... We call this \emph{hash injectivity}; under rotation the domain is version-stamped signed blocks... \quad\textit{(Lean: \code{SignedHashInjective}.)}"*
Lean defines:
`def SignedHashInjective (Signed : Block → Prop) (G : Block) : Prop := ∀ ⦃B B' : Block⦄, (B = G ∨ Signed B) → (B' = G ∨ Signed B') → B.id = B'.id → B = B'`.

b. **Conclusion**: Matches Lean's definition.

c. **Quantifiers, parameter ranges and definitions**: Exact match on block identifiers and domain restriction to $\{G\} \cup \text{Signed}$.

d. **Convenience assumptions**: Assumes no collisions occur within the execution domain. Standard cryptographic modeling idealization.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C34

a. **Hypotheses**: All hypotheses are disclosed.
The paper states:
*"Deliberately minimal: it does \emph{not} posit a valid chain behind the certificate --- a proved lemma reconstructs the prefix chain from the fold steps, so the chain's existence is a consequence, not a hypothesis. \quad\textit{(Lean: \code{GroundedCert}.)}"*
Lean's theorem `groundedCert_history` requires:
- `1 ≤ n` (global parameter assumption $n \ge 1$)
- `GroundedCert n Signed G cl`

b. **Conclusion**: Matches Lean. Lean's `groundedCert_history` proves `∃ c : Chain, GroundedHistory n Signed G cl c`, where `GroundedHistory` includes `validChain n c = true`, `blockAt? c 0 = some G`, tip matching, length equality, and signedness of every block. The existence of a valid chain is indeed a proved consequence of certificate grounding rather than an assumption.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; constructive inductive proof in Lean reconstructing the chain witness from inductive certificate extension steps.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C35

a. **Hypotheses**: Definitional assumption.
The paper states:
*"A certificate that verifies carries a claim built from the deployment genesis by folding in one block at a time, where each fold checks the link rules, the density of newly matured windows, and a verifying producer signature on the folded block. Deliberately minimal: it does \emph{not} posit a valid chain behind the certificate --- a proved lemma reconstructs the prefix chain from the fold steps, so the chain's existence is a consequence, not a hypothesis. \quad\textit{(Lean: \code{GroundedCert}.)}"*
Lean defines `inductive GroundedCert` with constructors `genesis` and `extend`. All fold checks (parent link, strictly increasing slots, height increments, signature verification `Signed b`, and window quorum density) are explicitly stated in the paper.

b. **Conclusion**: Matches Lean's inductive definition.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: As noted in C2, `GroundedCert` abstracts SNARK argument system soundness by positing that verified certificates correspond to inductive sequence folds. The paper explicitly identifies this as Assumption~\ref{ass:cert} ("Certificate grounding").

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C36

a. **Hypotheses**: Definitional assumption for liveness.
The paper states:
*"For the liveness theorem only: the honest producers of each newly maturing window were live, and their blocks reached the current producer in time to be built on. \quad\textit{(Lean: \code{HonestBlocksCover}.)}"*
Lean defines:
`def HonestBlocksCover (bad : ByzantineSlots) (record : SlotRecord) (c : Chain) (u n : Nat) : Prop := ∀ s, ¬ bad s → u ≤ s → s < u + n → ∃ B : Block, B ∈ record s ∧ B ∈ c`.

b. **Conclusion**: Matches Lean's definition.

c. **Quantifiers, parameter ranges and definitions**: Exact match ($\forall s \in [u, u+n), \neg \text{bad } s \implies \exists B \in \text{record } s \land B \in c$).

d. **Convenience assumptions**: Strong assumption for liveness: assuming honest blocks are already present in chain $c$ sidesteps network delay and consensus fork-choice dynamics. The paper explicitly restricts this assumption to the liveness theorem only.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C37

a. **Hypotheses**: Fully disclosed.
The paper states:
*"First, light-client safety (Theorem~\ref{thm:lc}). It is proved about the protocol's structural core, and it covers the full validator because every chain the full validator accepts also passes those structural checks (\code{validChainK\_structural})."*
Lean's theorem `validChainK_sound` (`Molt.validChainK_structural`):
`theorem validChainK_sound {n : Nat} {c : Chain} (h : validChainK n c = true) : ValidChain n c ∧ KeyIndexMonotone n c`.

b. **Conclusion**: Matches Lean. The paper claims that any chain accepted by `validChainK` passes the structural checks (`ValidChain n c`), which is the first conjunct of Lean's theorem.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; constructive soundness theorem.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C38

a. **Hypotheses**: Lean's theorem `keyrot_recent_certified_suffix_agreement` requires extensive structural, cryptographic, and synchrony hypotheses:
- Window length and confirmation parameter:  \le n \le \Delta_{\mathrm{conf}}$.
- Cryptographic unforgeability game: `KeyStealingEUFCMA n Δconf ops registry rented Stolen honestSigned now Δ`.
- Collision-free signatures on declared keys: `SignedHashInjective (SignedDeclared n ops registry) G`.
- Inductive certificate grounding for both claims: `GroundedCertK n ... cl fl` and `GroundedCertK n ... cl' fl'`.
- Suffix validity matching the full validator: links, height/slot monotonicity, tip attachment, window quorum density, and key monotonicity (`keyMonoFrom n fl suffix = true`).
- Declared signatures across all suffix blocks: `∀ B ∈ suffix, SignedDeclared n ops registry B`.
- Verifier clock recency on tips: `now ≤ sTip.slot + Δ` and `now ≤ sTip'.slot + Δ`.
- Byzantine corruption bounds quantified over all possible attested histories: `∀ c, AttestedHistoryK n Δconf ops registry G cl.tipHeight suffix c → ByzantineBounded n (badKeyrotOn n Δconf rented Stolen c)`.
- Mutual exposure depth: matching heights `cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i'` with depth bounds `i + n < suffix.length` and `i' + n < suffix'.length`.
The paper prose here is an introductory roadmap sentence (*"Its counterpart at the certificate presentation, under the full validator with its key discipline and pin, is each mode's certified theorem in Section~\ref{sec:rotation}..."*) that explicitly defers the formal statements to Section~ef{sec:rotation}. All operational validator rules are covered by referencing the full validator, while the heavy adversarial premise (`AttestedHistoryK`) is introduced in Section~ef{sec:rotation}.

b. **Conclusion**: Equal to Lean's conclusion ( = B'$, agreement on common exposed blocks). The prose accurately identifies this as the certificate-presentation counterpart theorem.

c. **Quantifiers, parameter ranges and definitions**: Exact match ( \le n \le \Delta_{\mathrm{conf}}$, recency $\Delta$).

d. **Convenience assumptions**: The hypothesis `∀ c, AttestedHistoryK ... c → ByzantineBounded n (badKeyrotOn ... c)` requires the Byzantine corruption budget to hold across *all* chains that could have generated the certificate claim's fold, rather than assuming a single objective reality of honest/Byzantine participants.

e. **Do the Lean definitions mean what the prose says?** Yes. `keyrot_recent_certified_suffix_agreement` formalizes suffix agreement for certified chains under dynamic key rotation.

Verdict: FAITHFUL

---

### C39

a. **Hypotheses**: Significant undisclosed hypothesis in the prose.
The paper states:
*"Next, the timed model, where forged chains take real time (Theorem~\ref{thm:forge}); this timed model is also where the recency scoping of Assumption~\ref{ass:sig} stops being an assumption and becomes a theorem (a separate derivation, \code{sigUnforgeableRecent\_of\_timed})."*
Lean's `sigUnforgeableRecent_of_timed` requires:
- `hexec : TimedExecution n bad log G`
- `hNB : NoBackdate bad log`
- `hbridge : ∀ ⦃B : Block⦄, Signed B → ∃ r, B ∈ log r`
The hypothesis `NoBackdate bad log` (`∀ r B, B ∈ log r → ¬ bad B.slot → B.slot = r`) is completely omitted from this prose sentence. While later mentioned in line 756 and Appendix A, asserting here that recency scoping becomes a theorem in the timed model obscures that `TimedExecution` alone is insufficient: `noBackdate_independent` formally proves that `NoBackdate` is logically independent of `TimedExecution`.

b. **Conclusion**: Overclaim. The prose asserts that the timed model is where the recency scoping of Assumption~ef{ass:sig} *"stops being an assumption and becomes a theorem"*. In Lean, `sigUnforgeableRecent_of_timed` does not derive recency scoping from the timed model; rather, recency is completely unused in the proof (`_hrec` is ignored), and the property holds for *any* `now` and `Δ` solely because `NoBackdate` directly pins each honest-stamped block to its stamped real slot.

c. **Quantifiers, parameter ranges and definitions**: In Lean, `now` and `Δ` are universally quantified without restriction ($\forall now, \Delta$), confirming that recency scoping is vacuous under `NoBackdate`.

d. **Convenience assumptions**: `NoBackdate` is a powerful convenience assumption. It posits that an adversary signing at a bad real slot can never produce a block stamped with an honest slot, directly assuming away cross-slot forgery and stockpiling on honest slots. As `TimedSig.lean` notes, per-block pinning does not follow from recency or `TimedExecution` alone, but is injected via `NoBackdate`.

e. **Do the Lean definitions mean what the prose says?** No. The Lean theorem derives `SigUnforgeableRecent` by assuming `NoBackdate` rather than by deriving recency from the timed model.

Severity: MAJOR
Fix: Clarify that recency-scoped unforgeability is derived by assuming NoBackdate (forward-secure custody) in addition to the timed model, which renders recency slack rather than deducing it from real-time delay.

---

### C40

a. **Hypotheses**: Meta-claim regarding the formalization. All underlying Lean theorems depend only on Lean 4's standard foundational axioms (`Classical.choice`, `Quot.sound`, `propext`), verified in `Molt/Axioms.lean`.

b. **Conclusion**: Matches Lean. All theorems presented in Section 4 are proved against the Lean model without unproved conjectures or custom axioms.

c. **Quantifiers, parameter ranges and definitions**: N/A (meta-statement).

d. **Convenience assumptions**: None for this meta-claim.

e. **Do the Lean definitions mean what the prose says?** Yes. All results in the section are machine-checked Lean theorems.

Verdict: FAITHFUL

---

### C41

a. **Hypotheses**: Fully disclosed. The paper states:
*"The light-client and timed results (Theorems~\ref{thm:lc} and~\ref{thm:forge}) are carried to each implementation by that implementation's soundness bridge (Section~\ref{sec:impl}), which also covers the validator's key-discipline conjunct; the rotation-mode results of Section~\ref{sec:rotation} and the liveness theorem are, today, proved at model level."*
The formal developments in `Rust/Results_rust.lean` and `MoltPetit/TS/Results.lean` prove:
- `rust_recent_tip_ancestor_mem` and `ts_recent_tip_ancestor_mem` (Theorem 1 bridged via `rust_valid_chain_sound` and `ts_validChain_sound`).
- `rust_forged_chain_time_bound` and `ts_forged_chain_time_bound` (Theorem 2 bridged).
The prose accurately notes that rotation-mode results and liveness remain model-level.

b. **Conclusion**: Matches Lean. The paper precisely scopes which theorems are bridged to implementations and which are model-level only.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: The implementation bridges assume that the AST definitions faithfully represent the external codebases and that `U64Backend` semantics hold.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C42

a. **Hypotheses**: Stated and fully disclosed in the text:
-  \ge 1$ (`1 ≤ n`).
- Deployment genesis (`G : Block`, `SignedHashInjective Signed G`).
- Verifier clock $\mathit{now}$ (`now : ℕ`).
- Assumptions~ef{ass:budget}--ef{ass:cert}:
  - Assumption 1: Byzantine budget (`ByzantineBounded n bad`).
  - Assumption 2: Hash injectivity (`SignedHashInjective Signed G`).
  - Assumption 3: Signature freshness (`SigUnforgeableRecent n bad Signed signed now n`).
  - Assumption 5: Certificate grounding (`GroundedCert n Signed G cl` and `cl'`).
- Validator checks on suffixes:
  - Valid tips: `(s₁ :: srest).getLast? = some sTip` and `(s₁' :: srest').getLast? = some sTip'`.
  - Tip linkage: `s₁.height = cl.tipHeight + 1 ∧ cl.tipSlot < s₁.slot ∧ s₁.prev = some cl.tipId` (and for '$).
  - Chain links: `linksOk (s₁ :: srest) = true` (and for ' :: srest'$).
  - Quorum window density: $\forall u \in [\mathit{tipSlot} + 2 - n, \mathit{sTip.slot} + 1 - n]$, `quorum n ≤ windowCount ...`.
  - Producer signatures: $\forall B \in \text{suffix}, \text{Signed } B$.
- Recent tips: $\mathit{now} \le \mathit{sTip.slot} + n$ and $\mathit{now} \le \mathit{sTip'.slot} + n$.
- Mutual exposure and depth: `cl.tipHeight + 1 + i = cl'.tipHeight + 1 + i'` with  + n < \text{suffix.length}$ and ' + n < \text{suffix'.length}$.

b. **Conclusion**: Matches Lean. Lean establishes  = B'$ for blocks , B'$ at index , i'$ in the two suffixes. The paper explicitly qualifies the agreement to heights exposed by both suffixes with at least $ blocks above them: *"whenever the second chain's suffix exposes that height with $ blocks above it too. In particular, all recent accepted chains agree on their common prefix up to $ blocks below the lower tip, at every height both presentations expose."*

c. **Quantifiers, parameter ranges and definitions**: Exact match ( \ge 1, \Delta = n$).

d. **Convenience assumptions**:
- Certificate grounding (`GroundedCert`) abstracts SNARK recursive verification by positing that verified certificates correspond to valid inductive chain folds.
- The requirement that both presentations expose the block in their uncertified suffixes is an operational restriction of the presentation format; lines 659–664 explicitly disclose that the ability to re-present chains with deeper suffixes is an unproven production-side property (*"argued, not proved (the representability lemmas are production-side), which is why the hypothesis stays in the statement"*).

e. **Do the Lean definitions mean what the prose says?** Yes. Lean's `recent_certified_suffix_agreement` proves safety (agreement on common exposed deep prefix) for light clients verifying certified presentations.

Verdict: FAITHFUL

---

### C43

a. **Hypotheses**: Fully disclosed. The paper states:
*"The exposes that height'' hypothesis is a restriction of presentation, not of operation: a certificate-plus-$n$-block chain can always be re-presented as a certificate$'$-plus-$2n$-block chain (grounding attests a claim at every fold), so a holder can re-expose as many blocks as a comparison needs --- argued, not proved (the representability lemmas are production-side), which is why the hypothesis stays in the statement."*
The text explicitly concedes that re-presentation is an informal argument, explaining why the Lean theorem `recent_certified_suffix_agreement` retains the mutual exposure hypothesis (`i + n < (s₁ :: srest).length` and `i' + n < (s₁' :: srest').length`).

b. **Conclusion**: Matches Lean scoping. The text accurately clarifies that the mutual exposure condition in Theorem~ef{thm:lc} is kept in the formal theorem because representability is unproved in Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: The claim that chains can always be re-presented with deeper uncertified suffixes is unverified; the paper explicitly acknowledges that this is an informal production-side argument omitted from the Lean kernel.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C44

a. **Hypotheses**: Stated and disclosed.
The paper introduces the timed model:
*"The \emph{timed model} (\code{TimedExecution}) adds a real-time axis: a log of what each real slot's producer signed --- at an honest real slot, at most its own current block; at a bad real slot, arbitrarily many blocks of the adversary's choosing under that producer's key --- arbitrary content, and stamped with any slot at all, not only the real slot at which the signing happens."*
Lean's `TimedExecution n bad log G` formalizes this via:
- `key_match`: signatures at real slot $r$ carry stamps $B.\mathit{slot} \equiv r \pmod n$ (matching the producer's key).
- `honest_stamp`: $
eg \mathit{bad}(r) \implies B.\mathit{slot} = r$.
- `honest_once`: $
eg \mathit{bad}(r) \implies$ at most one block signed.
- `chain_order`: parent block must be available at signing time (detailed in C45).
- `id_inj`: hash injectivity across all signed blocks.

b. **Conclusion**: Matches Lean. At bad real slots, the adversary can sign arbitrarily many blocks with arbitrary slot stamps satisfying $B.\mathit{slot} \equiv r \pmod n$.

c. **Quantifiers, parameter ranges and definitions**: The prose notes "stamped with any slot at all"; under the protocol's key discipline, this is formally constrained to any slot belonging to that producer ($B.\mathit{slot} \equiv r \pmod n$, via `key_match`), which matches "under that producer's key".

d. **Convenience assumptions**: `TimedExecution` abstracts the network and CPU scheduling into discrete real slots, and posits `id_inj` (global hash collision resistance across signed blocks) and `chain_order`.

e. **Do the Lean definitions mean what the prose says?** Yes. `TimedExecution` directly formalizes the described real-time signing model.

Verdict: FAITHFUL

---

### C45

a. **Hypotheses**: Disclosed.
The paper states:
*"The id-formation contract of Section~ef{sec:protocol} appears as the field \code{chain\_order}: a block can be signed only once its parent is \emph{available}, because the parent's id preimage contains the parent's signature, and predicting another party's signature on a known message is exactly an EUF-CMA forgery."*
Lean's `TimedExecution.chain_order` formalizes:
`∀ ⦃r⦄ ⦃B⦄, B ∈ log r → ∀ ⦃i⦄, B.prev = some i → ∃ P, P.id = i ∧ AvailableAt log G P r`.

b. **Conclusion**: Matches Lean. If a block $B$ signed at real slot $r$ points to parent id $i$, a block $P$ with $P.\mathit{id} = i$ must have been available at or before real slot $r$.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: In Lean, `chain_order` is an axiomatic field of the `TimedExecution` structure rather than a theorem reduced to cryptographic primitives, justified in the prose by the EUF-CMA unforgeability of the parent's signature embedded in the parent block ID preimage.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C46

a. **Hypotheses**: Fully disclosed in the theorem statement and text:
- $n \ge 2$ (explicitly disclosed: *"The Lean statements carry non-degeneracy side conditions --- $n \ge 2$, $F$ not the first block"*).
- Timed execution: `TimedExecution n bad log G`.
- Byzantine budget: `ByzantineBounded n bad`.
- Valid chain: `ValidChain n c`.
- Genesis without parent: `G.prev = none`.
- Chain availability: `∀ B ∈ c, AvailableAt log G B R` ($R = r_{\mathrm{now}}$).
- Fork block $F$: index $k_0 \ge 1$ with `blockAt? c k₀ = some F`.
- First-signing of $F$: $F \in \log(r_0)$ and $orall r < r_0, F 
otin \log(r)$.
- Bad suffix: $orall B \in c, F.\mathit{slot} < B.\mathit{slot} 	o orall r, B \in \log(r) 	o \mathit{bad}(r)$.
- Tip block: `c.getLast? = some tip`.

b. **Conclusion**: Matches Lean.
Lean proves `forged_suffix_time_bound`:
\[
\quorum \cdot \lfloor (\mathit{tip.slot} - F.\mathit{slot}) / n floor \le max \cdot (\lfloor (R - r_0) / n floor + 1).
\]
And `forged_chain_time_bound`:
\[
\quorum \cdot \lfloor (\mathit{tip.slot} + 1) / n floor \le max \cdot (\lfloor R / n floor + 1) + 1.
\]
The paper's displayed equation and corollary match Lean's integer arithmetic bounds exactly.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None beyond the stated timed execution model and fault budget. The result is a combinatorial consequence of density and signing time monotonicity.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C47

a. **Hypotheses**: None (informal proof summary of Lemma `one_real_slot_one_block`).
The paper states:
*"At real slot $r$ only $r$'s producer's key can be made to sign, so two chain blocks first-signed at $r$ belong to one producer and their slot stamps differ by at least $n$; density puts some other seat's block between those stamps; and signing order (\code{chain\_order}: a block cannot be signed before its parent exists) forces that middle block's first signing back to $r$ as well --- under a key that real slot cannot reach."*

b. **Conclusion**: Matches Lean's `one_real_slot_one_block`:
Two distinct blocks of a valid chain cannot both have their first-signing event at the same real slot $r$.

c. **Quantifiers, parameter ranges and definitions**: Exact match with the lemma's preconditions ($2 \le n$, `ValidChain n c`, `AvailableAt log G B R$, $1 \le k < k'$, first-signed at $r$).

d. **Convenience assumptions**: None; fully verified in `MoltPetit/Model/Timed.lean`.

e. **Do the Lean definitions mean what the prose says?** Yes. The prose accurately traces the formal proof steps of `one_real_slot_one_block`.

Verdict: FAITHFUL

---

### C48

a. **Hypotheses**: Fully disclosed in text and Appendix D:
- Timed execution: `TimedExecution n bad log G`.
- No back-dating: `NoBackdate bad log` (`∀ r B, B ∈ log r → ¬ bad B.slot → B.slot = r`).
- Signature oracle bridge (EUF-CMA): `∀ B, Signed B → ∃ r, B ∈ log r`.
The paper explicitly states that Assumption~ef{ass:sig}(c) is derived from EUF-CMA plus the *no-back-dating* residue, noting that `NoBackdate` is logically independent of `TimedExecution` alone (`noBackdate_independent`).

b. **Conclusion**: Matches Lean.
Lean proves `sigUnforgeableRecent_of_timed`:
`SigUnforgeableRecent n bad Signed (projectSigned n log) now Δ`.
As noted in the paper, this holds for any verifier clock `now` and recency bound `Δ` because `NoBackdate` pins every honest-stamp block directly.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Scrutiny of `NoBackdate`: `NoBackdate` requires that an honest-stamped block cannot be minted at any real slot other than its stamp. The paper explicitly identifies this as an essential, non-redundant cryptographic assumption and formally proves its independence from the other timed-model axioms in `noBackdate_independent`.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C49

a. **Hypotheses**: None (definitional).
The paper states:
*"The protocol's key-rotation machinery was defined with the protocol itself: the in-band version (\code{keyIndex}, Section~ef{sec:protocol}) and the monotone rule (\code{keyMonoOk}) are already part of the one chain validity."*

b. **Conclusion**: Matches Lean. Lean's block structure contains the field `keyIndex : Nat`, and `validChainK n c := validChain n c && keyMonoOk n c` combines core structural validity with `keyMonoOk`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C50

a. **Hypotheses**: Definitional.
The paper states:
*"The key-stealing corruption predicate (\code{badKeyrot}) counts a slot bad if it is rented \emph{or} some version at-or-above the one in force for its producer is stolen --- which builds \emph{healing} into the definition: a stolen key stops counting the moment its retirement takes force."*

b. **Conclusion**: Matches Lean.
Lean defines `badKeyrotOn`:
`badKeyrotOn n Δconf rented Stolen c₀ s := rented s ∨ ∃ j, inForce n Δconf c₀ (producerForSlot n s) s ≤ j ∧ Stolen (producerForSlot n s) j`.
A slot is corrupted if rented or if a stolen key version exists at or above the currently confirmed in-force index. Once a newer key version is confirmed at depth $\Delta_{\mathrm{conf}}$, $\mathit{inForce}$ advances past the stolen version, so the slot ceases to be corrupted (heals).

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: The corruption predicate is parameterized by a reference chain $c_0$ defining the in-force version, which later motivates the anchor requirement (`H-ANCHOR`) for light clients.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C51

a. **Hypotheses**: Definitional / scoping of cryptographic assumptions:
- Mode 1 chain-level rule scopes collision resistance to `KeyStealingSigned` (any registered key version).
- Modes 2--3 and certified mode 1 scope collision resistance to `SignedDeclared` (declared key version).
Fully disclosed in the paper.

b. **Conclusion**: Matches Lean.
Lean defines:
- `KeyStealingSigned n ops registry B := ∃ sig j, ops.verify (registry (producerForSlot n B.slot) j) B sig = true`.
- `SignedDeclared n ops registry B := ∃ sig, ops.verify (registry (producerForSlot n B.slot) B.keyIndex) B sig = true`.
The paper correctly notes that `SignedDeclared` is strictly narrower than `KeyStealingSigned` (`keyStealingSigned_of_declared`).

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C52

a. **Hypotheses**: Assumption~\ref{ass:rotation-honest} (No back-dating, honest custody --- per mode):
The paper explicitly discloses that this assumption is stated directly rather than derived from timed execution:
*"Unlike Assumption~\ref{ass:sig}(c) (Section~\ref{sec:timed}), this is stated directly rather than derived: Appendix~\ref{app:timed-uniq}'s derivation needs only one key's safety per real slot, while \code{KeyStealingEUFCMA}/\code{SchedCoreUnforgeable} are stated per individual key version, and one real slot can host several eligible key versions of which only one verifies --- so one key's safety does not certify the slot's, and the timed-model route does not generalize here without weakening an already-assumed primitive (machine-checked: \code{badSched_single_key_safe_not_enough}, \code{badKeyrot_single_key_safe_not_enough})."*

b. **Conclusion**: Matches Lean.
Lean proves:
- `badSched_single_key_safe_not_enough`: `∃ n schedule rented Stolen s j, ¬rented s ∧ ¬Stolen (producerForSlot n s) j ∧ badSched n schedule rented Stolen s`.
- `badKeyrotOn_single_key_safe_not_enough` (aliased in `Molt` as `badKeyrot_single_key_safe_not_enough`): `∃ n Δconf rented Stolen s j, ¬rented s ∧ ¬Stolen (producerForSlot n s) j ∧ badKeyrotOn n Δconf rented Stolen [] s`.
These counterexamples prove that a single key's safety does not imply slot safety.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: The paper explicitly treats this as a primitive assumption (Assumption 5) and machine-checks the obstruction demonstrating why it cannot be derived from single-key timed custody.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C53

a. **Hypotheses**: Fully disclosed in text:
- Mode 0 loss-only condition: `Stolen := fun _ _ => False` (no key stolen/exfiltrated).
The paper states: *"With nothing stolen the corruption the theorems count collapses to rent alone in every mode (\code{badKeyrot_lossOnly}, \code{badSched_lossOnly}; mode 3 inherits mode 2's count) --- no anchor, no cadence, any pin."*

b. **Conclusion**: Matches Lean.
Lean proves:
- `badKeyrotOn_lossOnly`: `badKeyrotOn n Δconf rented (fun _ _ => False) c₀ = rented`.
- `badSched_lossOnly`: `badSched n schedule rented (fun _ _ => False) = rented`.
Both corruption predicates collapse identically to `rented`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; exact reduction when no keys are stolen.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C54

a. **Hypotheses**: None (definitional).
The paper states:
*"seat $i$'s version \emph{in force} at slot $s$ (\code{inForce}) is the highest version $i$ has declared in the chain's \emph{confirmed prefix} --- blocks at least $n$ slots old --- and no block may declare less (\code{validSignedChainK$'$})."*

b. **Conclusion**: Matches Lean.
Lean defines:
- `inForce n Δconf c i s := keyFloor n (confirmedPrefix Δconf c s) i`.
- `validSignedChainK' n Δconf ops registry sc := sigsOk n ops registry sc && validChainK' n Δconf (stripSigs sc)`, where `validChainK'` enforces `keyFloor ≤ b.keyIndex` on all blocks.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The text fixes $\Delta_{\mathrm{conf}} = n$.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C55

a. **Hypotheses**: Fully disclosed in text and Theorem~\ref{thm:refresh}:
- Parameter range: $1 \le n$.
- Cryptographic assumptions: `KeyStealingEUFCMA n n ops registry rented Stolen honestSigned now Δ` and `SignedHashInjective (KeyStealingSigned n ops registry) G`.
- Previous sync verification: `validSignedChainK' n n` verified at clock time $t$ on recent tip (`t ≤ tipPrev.slot + n`), length $> n$.
- Anchor: block $A$ at depth $n$ below previous tip (`stripSigs scPrev (len - 1 - n)`).
- Cadence: client re-verifies within $n$ slots (`now ≤ t + n`).
- Anchor containment: $A \in \text{stripSigs } sc$ and $A \in \text{stripSigs } sc'$.
- Standing budget: on every $n$-slot window starting in trailing $5n$ slots (`now < u + 5n`), bad slots bounded by `faultBudget n`.
- Acceptance and recency: both chains accepted (`validSignedChainK' n n`), tips recent (`now ≤ sTip.slot + Δ`), lengths $> n$.

b. **Conclusion**: Matches Lean.
- At equal tip heights (`sTip.height = sTip'.height`), `sync_rule` proves equality of blocks $n$ deep below tips: $B = B'$.
- At unequal tip heights (`sTip.height ≤ sTip'.height`), `sync_rule_mem` proves the lower chain's $n$-deep block is in the taller chain at least $n$ deep: `∃ i', i' + n < len ∧ blockAt? sc' i' = some B`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Scrutiny of cadence, anchor, and trailing budget:
- Cadence `now ≤ t + n` and anchor $A$: essential operational premises explicitly specified by the client sync rule.
- Trailing budget `now < u + 5n`: explicitly derived in the text from tip recency ($n$), anchor depth ($2n$ slots), sync cadence ($n$), and window width ($n$).

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C56

a. **Hypotheses**: Stated in text:
- $1 \le n$.
- Valid chain: `ValidChain n c`.
- Blocks $A$ and $D$ at indices $m$ and $m + n$ in $c$.

b. **Conclusion**: Matches Lean.
Lean proves `deep_block_span`: `D.slot < A.slot + 2 * n`.
The text states: *"The anchor sits fewer than $2n$ \emph{slots} below that tip although it is $n$ \emph{blocks} deep --- density leaves no room for more (two full windows in the gap would demand $2\quorum > n$ blocks where only $n$ exist; Lean \code{deep_block_span})."*

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; direct density consequence of `ValidChain`.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C57

a. **Hypotheses**: Disclosed in text:
Taking anchor $A := \text{genesis}$ with $H := now$ in `client_refresh_rule` covers every window from genesis onwards.

b. **Conclusion**: Matches Lean.
In `client_refresh_rule`, anchor freshness is `now ≤ A.slot + H` and the budget guard is `now < u + n + H`. With $A := \text{genesis}$ ($A.\mathrm{slot} = 0$) and $H := now$, freshness is trivially $now \le 0 + now$ and the budget guard becomes $now < u + n + now \iff 0 < u + n$, covering all windows $u \ge 0$.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C58

a. **Hypotheses**: Fully disclosed in text:
- Mode 1 certificate grounding: `GroundedCertK` threads constant-size per-producer key floors alongside claims.
- Cryptographic assumptions: `KeyStealingEUFCMA` and collision resistance over `KeyStealingSigned` / `SignedDeclared`.
- Anchored presentations: both certificate-plus-suffix presentations contain client anchor $A$.
- Trailing budget: consulted only on windows ending after the anchor.

b. **Conclusion**: Matches Lean.
Lean proves:
- `keyrot_recent_certified_suffix_agreement`: two grounded certificates with validated recent suffixes agree $n$ deep.
- `keyrot_certified_suffix_agreement_anchored`: anchored agreement with trailing budget.
- Client rules at certificate presentation: `cert_sync_rule` and `cert_max_sync_period`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: The text explicitly notes that the certificate must authenticate claim and floor together: *"an unauthenticated floor readmits stolen retired keys (\code{keyrot_recent_certified_suffix_agreement}, over the strengthened grounding \code{GroundedCertK})"*.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C59

a. **Hypotheses**: Fully disclosed in text:
- Reaction delay $d$: `Reacts n Δconf d c₀ stolenAt` (within $d$ slots of theft, victim's floor in $c_0$ advances past stolen key).
- Per-window rent bound $R_{\mathrm{rent}}$: `(badSlotsIn rented u n).card ≤ Rrent`.
- Per-window recent theft count $T$: `(recentTheftProducersK n d stolenAt u).card ≤ T`.
- Overall window budget: $R_{\mathrm{rent}} + T \le \text{faultBudget } n$.

b. **Conclusion**: Matches Lean.
Lean proves:
- `budget_of_reaction`: the combined corruption predicate `badKeyrotOn` satisfies the window budget $\le \text{maxByzantine } n$.
- Composed client rules: `sync_rule_timed` and `max_sync_period_timed`.

c. **Quantifiers, parameter ranges and definitions**: Exact match ($1 \le n$, $n \le \Delta_{\mathrm{conf}}$).

d. **Convenience assumptions**: Scrutiny of `Reacts`: the paper explicitly discloses that *"The reaction delay is asserted, like not-before in mode 2, not derived."* It assumes the reference chain $c_0$ confirms the victim's rotation by slot $r + d$.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C60

a. **Hypotheses**: Fully disclosed in text:
- Sync cadence: client re-verifies within $F$ slots (`now ≤ t + F`).
- Anchor: block $A$ at depth $n$ below previous tip.
- Trailing budget: window budget holds on every window starting in trailing $F + 4n$ slots or later (`now < u + F + 4n`).
- Standard validity, tip recency, and length $> n$.

b. **Conclusion**: Matches Lean.
Lean proves `max_sync_period`: chains agreeing on anchor agree on block $n$ deep below tips ($B = B'$).

c. **Quantifiers, parameter ranges and definitions**: Exact match ($1 \le n$, $n \le \Delta_{\mathrm{conf}}$, arbitrary $F$).

d. **Convenience assumptions**: Cadence $F$ enters linearly into the reach $F + 4n$ of the trailing budget requirement.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C61

a. **Hypotheses**: Fully disclosed in text:
- Roster set $P$ of victim producers whose not-yet-retired-at-$u$ keys were stolen.
- Floor monotonicity: `inForce_mono` (`s ≤ s' → inForce n Δconf c i s ≤ inForce n Δconf c i s'`).
- Victim count exceeds fault budget: $\text{faultBudget } n < P.\mathrm{card}$.

b. **Conclusion**: Matches Lean.
Lean proves:
- `census_accumulates`: $P.\mathrm{card} \le (\text{badSlotsIn } (\text{badKeyrot } \dots) \; u \; n).\mathrm{card}$.
- `census_accumulates_later_thefts`: thefts occurring after window $u$ also charge window $u$ by `inForce_mono`.
- `no_budget_beyond`: if $P.\mathrm{card} > \text{faultBudget } n$, then the budget condition is strictly violated.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; formal impossibility / tightness result explaining why sync period $F$ cannot exceed $S - 4n$.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C62

a. **Hypotheses**: Fully disclosed in text:
- Operational hypothesis 1: reaction delay $ (`Reacts n Δconf d c₀ stolenAt`, $\forall i j r, \text{stolenAt } i j r \to \forall s, r + d \le s \to j < \text{inForce } n \Delta_{\mathrm{conf}} c_0 i s$).
- Operational hypothesis 2: no stolen-key backdating (`NoTheftBackdating n Δconf c₀ stolenAt`, $\forall i j r s, \text{stolenAt } i j r \to \text{inForce } n \Delta_{\mathrm{conf}} c_0 i s \le j \to r \le s$).

b. **Conclusion**: Matches Lean.
The text correctly introduces both as named operational hypotheses rather than theorems proved from cryptographic primitives, explicitly stating: *"Both hypotheses are asserted, like not-before; deriving no-back-dating from a signature primitive aware of mint times is future work..."*

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: The paper explicitly scrutinizes both hypotheses and highlights that neither is derived in the Lean formalization; both are unproved operational premises bounding the adversary's signing ability.

e. **Do the Lean definitions mean what the prose says?** Yes. Under `NoTheftBackdating`, exposing slot $ with stolen version $ requires  \ge r$. Under `Reacts`, exposure ends once  \ge r + d$.

Verdict: FAITHFUL

---

### C63

a. **Hypotheses**: Fully disclosed in text:
- `Reacts n Δconf d c₀ stolenAt`.
- `NoTheftBackdating n Δconf c₀ stolenAt`.
- Exposure premise: version $ stolen at $ (`stolenAt i j r`) and in force at slot $ (`inForce n Δconf c₀ i s ≤ j`).

b. **Conclusion**: Matches Lean.
Lean proves `theft_exposure_window`:  \le s \wedge s < r + d$, i.e.  \in [r, r + d)$.
The text accurately summarizes: *"a stolen key is charged from the moment it is stolen until the reaction fires, and to no earlier window."*

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: The conclusion follows as a direct logical consequence of the two operational hypotheses `Reacts` and `NoTheftBackdating`.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C64

a. **Hypotheses**: Fully disclosed in text:
- For `paced_tight_census_bound_all_F`: adversary spacing  + d \le P$, paced theft schedule `pacedStolenAt ι P`, arbitrary sync period $, and arbitrary window reach condition `now < u + F + 4n`.
- For `max_sync_period_tight`: standard mode-1 hypotheses (validity, tip recency $\le \Delta$, cadence $\le t + F$, anchor agreement, EUF-CMA, hash injectivity, `Reacts`, `NoTheftBackdating`, rent bound $\le R_{\mathrm{rent}}$, tight theft census $\le T$, and overall budget {\mathrm{rent}} + T \le \text{faultBudget } n$).

b. **Conclusion**: Matches Lean.
Lean proves:
- `paced_tight_census_bound_all_F`: `(recentTheftProducersTight n d (pacedStolenAt ι P) u).card ≤ 1` holds for all $.
- `max_sync_period_tight`: full mode-1 agreement under the tightened reaction budget.
The text scrupulously clarifies the scope: *"That is what 'a larger $' means here --- the census no longer constrains $; rent still has to be bounded over the same stretch."*

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Text explicitly discloses that `max_sync_period_tight` still requires the rent bound over the expanded trailing stretch  + 4n$, avoiding any overclaim that large $ is safe unconditionally.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C65

a. **Hypotheses**: Fully disclosed in text:
- For `client_refresh_rule`: anchor age $ (`now ≤ A.slot + H`), trailing budget over reach  + H$ (`now < u + n + H`), EUF-CMA, hash injectivity, tip recency $\le \Delta$, equal height.
- For `stay_recent_client_safe`: previous tip recency at sync (`t ≤ tipPrev.slot + n`), previous length $> n$, anchor $ at depth $, sync cadence  = n$ (`now ≤ t + n`), trailing budget over n$ slots (`now < u + 5n`).

b. **Conclusion**: Matches Lean.
`stay_recent_client_safe` formally derives the anchor age bound  := 4n - 1$ from `deep_block_span` and cadence  = n$, establishing safety under trailing budget span  = 5n$ ( + H = 5n - 1 < 5n$). Chains agree on the block $ below tips ( = B'$).

c. **Quantifiers, parameter ranges and definitions**: Exact match ( \le n \le \Delta_{\mathrm{conf}}$).

d. **Convenience assumptions**: The cadence  = n$ and recency at sync are explicit operational rules for the active client.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C66

a. **Hypotheses**: Fully disclosed in text:
- Standing mode-1 hypotheses:  \le n$, EUF-CMA, hash injectivity, previous sync validity/recency/length/anchor, cadence `now ≤ t + n`, anchor membership in both chains, trailing n$ budget on accepted chain, valid signed chains, tips recent (`now ≤ sTip.slot + Δ`), length $> n$.
- For equal heights (`sync_rule`): .\mathrm{height} = sTip'.\mathrm{height}$.
- For unequal heights (`sync_rule_mem`): .\mathrm{height} \le sTip'.\mathrm{height}$.
- Prefix extension (`same_block_same_prefix`): `IdInjective record`, `ChainInRecord`, `ParentLinked`.

b. **Conclusion**: Matches Lean.
Lean proves:
- `sync_rule`: blocks $ deep below tips are equal ( = B'$).
- `sync_rule_mem`: the hBcdeep block of the lower tip appears in the taller chain at depth $\ge n$ (`i' + n < (stripSigs sc').length`).
- `same_block_same_prefix`: matching block implies agreement on the entire prefix up to that height.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Standard active-client cadence ( = n$) and trailing budget (n$ slots) as described in the deployment paragraph.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C67

a. **Hypotheses**: Fully disclosed in text:
- Reference chain validity, recency (`now k ≤ (rTip k).slot + n`), length $> n$, and monotonic prefix growth (`stripSigs (R k) <+: stripSigs (R (k + 1))`).
- Reference chain height condition (`hRLe`): accepted tip height does not exceed reference tip height (`∀ k, (tip k).height ≤ (rTip k).height`).
- Base anchor membership: `a 0 ∈ stripSigs (R 0)`.
- Client step conditions: validity, recency, cadence, anchor preservation, and trailing n$ budget.

b. **Conclusion**: Matches Lean.
Lean proves `∀ k, a k ∈ stripSigs (R k)`: every sync's anchor lies on the reference chain at that sync.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Scrutinizing `hRLe`: the theorem requires `(tip k).height ≤ (rTip k).height` at every step. This hypothesis is explicitly highlighted in the text: *"provided that chain's tip is at least as tall as the accepted one at every sync, and recent. The height comparison is a stated hypothesis of the theorem, not a conclusion..."*

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C68

a. **Hypotheses**: Fully disclosed. The prose is an explicit meta-disclosure regarding the mathematical boundary of `sync_induction_full_chain`:
*"The height comparison is a stated hypothesis of the theorem, not a conclusion --- it is what the density remark argues for informally (a recent taller fork's hBcdeep block sits below its divergence), and that remark is not itself machine-checked."*

b. **Conclusion**: Matches Lean. Lean theorem `sync_induction_full_chain` explicitly takes `hRLe : ∀ k, (tip k).height ≤ (rTip k).height` as an input hypothesis.

c. **Quantifiers, parameter ranges and definitions**: N/A (prose disclaimer).

d. **Convenience assumptions**: The text explicitly concedes that `hRLe` is an operational assumption that relies on an unverified informal density argument.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C69

a. **Hypotheses**: Fully disclosed in text:
- Standing mode-1 hypotheses: $1 \le n$, $n \le \Delta_{\mathrm{conf}}$, EUF-CMA (`KeyStealingEUFCMA`), hash injectivity (`SignedHashInjective`), valid signed chains (`validSignedChainK'`), recent tips (`now ≤ sTip.slot + Δ`), length $> n$, equal tip heights.
- Fresh trust anchor: checkpoint block $A \in \operatorname{stripSigs}(sc) \cap \operatorname{stripSigs}(sc')$.
- Anchor age / freshness: $now \le A.\mathrm{slot} + H$ (prose instantiates to $H \approx 4n$).
- Trailing corruption budget: window budget on every window overlapping trailing $H + n$ slots (`now < u + n + H`).

b. **Conclusion**: Matches Lean.
Lean proves $B = B'$: the two accepted chains agree on the block $n$ deep below their tips.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The parameter $H$ is free in Lean (`{H : Nat}`) and bound operationally in text to $\approx 4n$.

d. **Convenience assumptions**: Standard mode-1 trailing corruption budget and presence of a fresh common anchor. The text explicitly frames this as "the op-model's fresh trust event".

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C70

a. **Hypotheses**: N/A (definition of validator).

b. **Conclusion**: Matches Lean.
`validSignedChainSched` requires `sigsOk n ops registry sc && validChainK n (stripSigs sc) && schedPin schedule (stripSigs sc)`. The `schedPin` predicate enforces $\forall b \in c,\, \operatorname{schedule}(b.\mathrm{slot}) \le b.\mathrm{keyIndex}$.

c. **Quantifiers, parameter ranges and definitions**: Exact match: $\mathit{gen}(\mathit{slot}) \le \mathit{keyIndex}$.

d. **Convenience assumptions**: None; definition.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C71

a. **Hypotheses**: Fully disclosed in text:
- Scheduled signed validator: `validSignedChainSched n schedule ops registry sc = true` (and for $sc'$).
- Unforgeability surface: `SchedUnforgeable n schedule ops registry rented Stolen honestSigned now Δ`.
- Hash injectivity over declared-version signatures: `SignedHashInjective (SignedDeclared n ops registry) G`.
- Chain-independent budget: `ByzantineBounded n (badSched n schedule rented Stolen)`.
- Shared genesis: `blockAt? (stripSigs sc) 0 = some G` and `blockAt? (stripSigs sc') 0 = some G`.
- Recent tips: `now ≤ sTip.slot + Δ` and `now ≤ sTip'.slot + Δ`.
- Chain length: $n < |sc|$ and $n < |sc'|$.
- For equal heights (`scheduled_client_safety` / `sched_recent_tip_ancestor_agreement`): $sTip.\mathrm{height} = sTip'.\mathrm{height}$.
- For unequal heights (`sched_recent_tip_ancestor_mem`): $sTip.\mathrm{height} \le sTip'.\mathrm{height}$.

b. **Conclusion**: Matches Lean:
- Equal heights: agreement on the block $n$ below tips ($B = B'$).
- Unequal heights: the lower chain's $n$-deep block appears in the taller chain at depth $\ge n$ (`∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B`).

c. **Quantifiers, parameter ranges and definitions**: Exact match. The text accurately emphasizes that no anchor, sync rule, or confirmation wait is needed.

d. **Convenience assumptions**: Chain-independent schedule corruption predicate `badSched` ($s$ is bad if rented or its producer has a stolen key with $j \ge \operatorname{schedule}(s)$).

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C72

a. **Hypotheses**: Fully disclosed. The text explicitly presents `NoPrematureTheft` and cold-root custody as:
*"named operational assumptions the cited theorems do not consume: not-before --- a generation's key cannot be stolen before it is derived; formalized separately as NoPrematureTheft in the timed theft layer --- and cold-root custody, which stays informal."*

b. **Conclusion**: Matches Lean. `NoPrematureTheft R stolenAt` is defined as $\forall i\, j\, r,\, \operatorname{stolenAt}(i, j, r) \to j \cdot R \le r$.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Candidly unbundled and disclosed as operational assumptions outside the core safety theorem.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C73

a. **Hypotheses**: Fully disclosed in text:
- Accepted chain under scheduled validator: `validSignedChainSched n schedule ops registry sc = true`.
- Stale era condition: $\forall s,\, \operatorname{schedule}(s) \le J \to s + \Delta < now$.
- Tip generation: tip $t$ declares $t.\mathrm{keyIndex} \le J$.

b. **Conclusion**: Matches Lean.
Lean proves `¬ now ≤ t.slot + Δ`: any fork whose tip declares a retired generation $J$ whose era ended more than $\Delta$ slots ago fails the recency check.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; direct consequence of scheduled pinning and recency check.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C74

a. **Hypotheses**: Fully disclosed in text:
- Certificate claim grounding under schedule: `GroundedCertSched n schedule (SignedDeclared n ops registry) G cl` (and for $cl'$).
- Scheduled core unforgeability: `SchedCoreUnforgeable`.
- Hash injectivity: `SignedHashInjective (SignedDeclared n ops registry) G`.
- Global scheduled budget: `ByzantineBounded n (badSched n schedule rented Stolen)`.
- Valid certified suffix extensions: links, density (`quorum n ≤ windowCount ...`), schedule pinned (`schedPinned`), declared signatures, recent tips, depth $\ge n$, equal heights.

b. **Conclusion**: Matches Lean.
Lean proves agreement on suffix blocks: $B = B'$ at equal relative heights.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The certificate state `CertClaim` carries no floor snapshot (`tipId`, `tipSlot`, `tipHeight`, `tail`), confirming that the certificate state remains the plain one.

d. **Convenience assumptions**: Global Byzantine budget across all windows (explicitly disclosed).

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C75

a. **Hypotheses**: Fully disclosed in text:
- Scheduled surface: `SchedUnforgeable`.
- Hash injectivity: `SignedHashInjective (SignedDeclared n ops registry) G`.
- Horizon-scoped budget: `ByzantineBoundedFrom H n (badSched n schedule rented Stolen)`.
- Valid chains under scheduled validator: `validSignedChainSched`.
- Recent tips: `now ≤ sTip.slot + Δ` and `now ≤ sTip'.slot + Δ`.
- Arithmetic horizon conditions: $H + n \le sTip.\mathrm{slot} + 1$ and $H + n \le sTip'.\mathrm{slot} + 1$.
- Equal tip heights: $sTip.\mathrm{height} = sTip'.\mathrm{height}$.
- Shared genesis is omitted from the hypotheses (`hHead` and `hHead'` are absent).

b. **Conclusion**: Matches Lean.
Lean proves agreement on block $n$ below tips ($B = B'$).

c. **Quantifiers, parameter ranges and definitions**: Exact match. The text explicitly notes that the budget is budgeted only on windows starting at $H$ (trailing $\approx 2n$ slots) and that genesis agreement is a consequence rather than a premise.

d. **Convenience assumptions**: Horizon-scoped Byzantine bound from $H$.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C76

a. **Hypotheses**: Fully disclosed in text:
- For `same_block_same_prefix`: `IdInjective record`, `ChainInRecord`, `ParentLinked`, and block equality at height $m$.
- For `sched_recent_tip_ancestor_mem_horizon`: horizon-scoped scheduled premises with unequal heights ($sTip.\mathrm{height} \le sTip'.\mathrm{height}$).

b. **Conclusion**: Matches Lean:
- Equal heights: agreement on block $n$ below tips implies agreement on the entire common prefix down to height 0 via `same_block_same_prefix`.
- Unequal heights: `∃ i', i' + n < (stripSigs sc').length ∧ blockAt? (stripSigs sc') i' = some B`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Standard horizon-scoping.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C77

a. **Hypotheses**: Fully disclosed. The text explicitly states the limitation:
*"Only the certificate form is proved under the global all-window budget, with the strengthened grounding GroundedCertSched (sched_recent_certified_suffix_agreement); carrying the horizon scoping to certificates is future work."*

b. **Conclusion**: Matches Lean. Lean theorem `sched_recent_certified_suffix_agreement` requires `ByzantineBounded n (badSched n schedule rented Stolen)` (the all-window global budget) rather than `ByzantineBoundedFrom`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Explicit meta-disclosure of the global budget requirement for the certificate presentation.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C78

a. **Hypotheses**: N/A (definitions of no-mixing discipline and lockstep validator).

b. **Conclusion**: Matches Lean:
- `lockstepOk` (`noMixing`): within each grid window ($b.\mathrm{slot}/n = b'.\mathrm{slot}/n \to b.\mathrm{keyIndex} = b'.\mathrm{keyIndex}$) and non-decreasing across windows ($b.\mathrm{keyIndex} \le b'.\mathrm{keyIndex}$).
- `validSignedChainLock`: conjunction of `sigsOk`, `validChainK`, and `lockstepOk`.

c. **Quantifiers, parameter ranges and definitions**: Exact match: slots $[Wn, Wn+n)$ form the grid windows $s / n = W$.

d. **Convenience assumptions**: None; validator definition.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

### C79

a. **Hypotheses**: Fully disclosed in text:
- Lockstep validator: `validSignedChainLock n ops registry sc = true` (and for $sc'$).
- `LockstepPackage`:
  - Monotone roster counter: `rosterGen w ≤ rosterGen w'`.
  - Honest declarations: `honestSigned i s = some B → B.keyIndex = rosterGen (s / n)`.
  - Initial genesis generation: `G.keyIndex = rosterGen (G.slot / n)`.
  - Hash injectivity: `SignedHashInjective (SignedDeclared n ops registry) G`.
  - Signature surface: `SchedCoreUnforgeable n (fun _ => 0) ...` (pin-free core signature surface).
  - Budget: `rentBound` ($R$), `exposedBound` ($T$ assessed at `lagSched n rosterGen`), and $R + T ≤ \fmax$.
- Shared genesis: `blockAt? sc 0 = some G` and `blockAt? sc' 0 = some G` (disclosed in text: client holds genesis and a clock).
- Recent tips: `now ≤ sTip.slot + Δ` and `now ≤ sTip'.slot + Δ`.
- Depth: $n < \mathrm{length}(sc)$.
- Equal tip heights for `lockstep_recent_tip_ancestor_agreement`, or $sTip.\mathrm{height} ≤ sTip'.\mathrm{height}$ for `lockstep_recent_tip_ancestor_mem`.

b. **Conclusion**: Matches Lean:
- Equal heights: agreement on block $n$ below tips ($B = B'$).
- Unequal heights: lower tip's confirmed ancestor at depth $n$ appears on the longer chain at depth $\ge n$.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Lockstep package assumes `exposedBound` at the lagged counter `lagSched n rosterGen` (mirroring Package A), fully disclosed in the text.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C80

a. **Hypotheses**: Fully disclosed in text:
- `LockstepPackage n rosterGen ...`.
- Accepted recent chain: `validSignedChainLock n ops registry sc = true` and `∃ t, getLast? sc = some t ∧ now ≤ t.slot + Δ`.
- Rooted at genesis: `blockAt? sc 0 = some G`.
- Matured window $W$: `∃ D ∈ sc, W * n + n ≤ D.slot + 1`.

b. **Conclusion**: Matches Lean.
Lean proves `B.keyIndex = rosterGen W` for any block $B ∈ sc$ with $B.\mathrm{slot}/n = W$. The prose states: "on any accepted recent chain, every matured grid window declares exactly the roster's counter".

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; pinning theorem derived from the Byzantine quorum threshold and validator discipline.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C81

a. **Hypotheses**: Fully disclosed in text:
- Lockstep validator: `validSignedChainLock`.
- `LockstepPackageGen`:
  - Honest declarations: `honestSigned i s = some B → B.keyIndex = rosterGen (s / n)`.
  - Hash injectivity: `SignedHashInjective (SignedDeclared n ops registry) G`.
  - Pin-free core signature surface: `SchedCoreUnforgeable n (fun _ => 0) ...`.
  - Rent budget: rent at most $R$ per window.
  - Per-generation theft budget: for every generation $j$, at most $T$ seats stolen (`genBound`).
  - Combined budget: $R + T ≤ \fmax$.
- Recent tips: `now ≤ sTip.slot + Δ` and `now ≤ sTip'.slot + Δ`.
- Depth: $2n < \mathrm{length}(sc)$.
- Shared genesis is omitted from the premises (`hHead` and `hHead'` are absent).

b. **Conclusion**: Matches Lean:
- Equal heights: agreement on block $2n$ below tips ($B = B'$).
- Genesis agreement: `lockstepGen_recent_genesis_agreement` proves $\exists P,\; \mathrm{blockAt?}\;sc\;0 = \mathrm{some}\;P \land \mathrm{blockAt?}\;sc'\;0 = \mathrm{some}\;P$.
- Prefix agreement down to height 0 follows through parent-id linkage.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The text explicitly points out that no shared genesis is assumed and confirmation depth is $2n$.

d. **Convenience assumptions**: None beyond the stated per-generation budget package.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C82

a. **Hypotheses**: Fully disclosed in text:
- `lockstep_window_declares_rosterGen`: `LockstepPackageGen`, accepted chain under `validSignedChainLock`, recent tip, and matured grid window $W$ witnessed by $D ∈ sc$ with $Wn + n ≤ D.\mathrm{slot} + 1$.
- `window_shared_prefix`: `HonestSlotsUniqueOn u n bad record`, `IdInjective record`, two valid chains extending through window $u$ ($u + n ≤ tip.\mathrm{slot} + 1$), and bad slots on window $u$ bounded by $\fmax$.

b. **Conclusion**: Matches Lean.
`lockstep_window_declares_rosterGen` proves all blocks in matured window $W$ carry $B.\mathrm{keyIndex} = \mathrm{rosterGen}(W)$. In `window_shared_prefix`, blocks prior to $u$ agree across chains.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Non-inductive single-window pinning.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C83

a. **Hypotheses**: Fully disclosed in text:
- `LockstepPackageGen`.
- Valid chains under lockstep validator with recent tips.
- Lower tip slot ordering: $sTip.\mathrm{slot} ≤ sTip'.\mathrm{slot}$.
- Depth condition: block index $k$ satisfies $k + n + (sTip.\mathrm{slot} + 1) \bmod n < \mathrm{length}(sc)$.

b. **Conclusion**: Matches Lean.
Lean proves agreement on the block at index $k$. The offset requirement is exactly $n + ((t+1) \bmod n)$ positions behind tip $t = sTip.\mathrm{slot}$, which is bounded by $2n$.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; sharp arithmetic bound on the unmatured tip window offset.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C84

a. **Hypotheses**: Fully disclosed in text:
- `LockstepPackage` (the cumulative package).
- Roster surjectivity: $\forall j,\; \exists W,\; \mathrm{rosterGen}(W) = j$ ("when the counter skips no generation").
- Non-zero committee: $0 < n$.

b. **Conclusion**: Matches Lean.
Lean constructs `LockstepPackageGen` from `LockstepPackage` under surjectivity.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Surjectivity condition matches the prose description "skips no generation".

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C85

a. **Hypotheses**: Fully disclosed in text:
- `ErasureTimedLock n rosterGen stolenAt`: $\forall i\; j\; r,\; stolenAt(i, j, r) \to \mathrm{rosterGen}(r / n) ≤ j$.
- Pre-retirement while-live theft bound: $\forall j,\; |\mathrm{preRetirementTheftProducers}(n, \mathrm{rosterGen}, stolenAt, j)| ≤ T$.
- `LockstepPackageTimed`: incorporates `ErasureTimedLock`, `NoPrematureTheftLock`, and the while-live census bound.

b. **Conclusion**: Matches Lean:
- `genBound_of_preRetirementBound`: deduces the timeless per-generation theft bound $\forall j,\; |\{i < n \mid \mathrm{stolenOf}(stolenAt, i, j)\}| ≤ T$.
- `lockstepTimed_recent_tip_ancestor_agreement`: proves agreement at depth $2n$ end-to-end under `LockstepPackageTimed`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Erasure hypothesis `ErasureTimedLock` explicitly formalized and proved to be the exact consumed premise enabling the while-live census reduction.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL


---

### C86

a. **Hypotheses**: Fully disclosed in text:
- Multi-party committee: $n \ge 2$ (`2 ≤ n`).
- Grounded lockstep certificate: `GroundedCertLock n Signed G cl g`.

b. **Conclusion**: Matches Lean:
- `groundedCertLock_gen_of_tail`: proves $\exists t \in cl.\mathrm{tail},\; t.\mathrm{slot} = cl.\mathrm{tipSlot} \land t.\mathrm{keyIndex} = g$.
- `groundedCertLock_gen_unique`: proves $\forall t \in cl.\mathrm{tail},\; t.\mathrm{slot} = cl.\mathrm{tipSlot} \to t.\mathrm{keyIndex} = g$.
Thus for $n \ge 2$, the generation $g$ is uniquely determined by the claim's own tail, requiring no external counter attestation.

c. **Quantifiers, parameter ranges and definitions**: Exact match ($n \ge 2$ for existence, $n \ge 1$ for uniqueness).

d. **Convenience assumptions**: None; structural combinatorial property of quorum-dense certificate tails.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C87

a. **Hypotheses**: Fully disclosed in text:
- `LockstepPackageTimed n rosterGen ops registry rented stolenAt honestSigned now Δ G R T`.
- Valid chains under lockstep validator: `validSignedChainLock n ops registry sc = true` and `sc'`.
- Tip recency: `now ≤ sTip.slot + Δ` and `now ≤ sTip'.slot + Δ`.
- Suffix depth condition: `2 * n < sc.length` and `2 * n < sc'.length`.
- Equal tip heights: `sTip.height = sTip'.height`.

b. **Conclusion**: Matches Lean.
Lean proves agreement on the block at index $\mathrm{length} - 1 - 2n$ for any two valid chains at equal heights with recent tips.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: All timed assumptions (`ErasureTimedLock`, `NoPrematureTheftLock`, bounded pre-retirement theft) are formalized in `LockstepPackageTimed` and explicitly disclosed.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C88

a. **Hypotheses**: Fully disclosed in text:
- `LockstepPackage` and its unforgeability/collision-resistance components.
- Certificate grounding and valid certified suffixes (`GroundedCertLock`, `lockstepFrom`).
- Tip recency bounds: `now ≤ sTip.slot + Δ`.
- Tip height relations ($sTip.\mathrm{height} = sTip'.\mathrm{height}$ or $sTip.\mathrm{height} \le sTip'.\mathrm{height}$).
- Chain parent-linking and record injectivity for prefix induction (`same_block_same_prefix`).

b. **Conclusion**: Matches Lean:
- Equal heights: agreement at depth $n$ (`lockstep_client_safety`).
- Unequal heights: confirmed block of lower chain is an ancestor of the taller chain (`lockstep_recent_tip_ancestor_mem`).
- Roster pinning: `lockstep_declares_rosterGen` pins block key indices to `rosterGen W` once the window matures.
- Certificate level: suffix agreement (`lockstep_recent_certified_suffix_agreement`) with certificate generation pinned (`lockstep_cert_gen_pinned`).
- Prefix agreement: `same_block_same_prefix` lifts single-block agreement to the entire confirmed prefix.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; accurately formalizes full lockstep safety across both raw and certified chain representations.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C89

a. **Hypotheses**: Fully disclosed in text:
- Reactive rotation: `Reacts n Δconf d c₀ stolenAt`.
- Operational no-theft-backdating: `NoTheftBackdating n Δconf c₀ stolenAt`.
- Paced theft schedule: `pacedStolenAt ι P` with spacing $n + d \le P$.
- Fault budget constraints: bounded rented slots $R_{\mathrm{rent}} + 1 \le \mathrm{faultBudget}(n)$.

b. **Conclusion**: Matches Lean:
- `theft_exposure_window`: confines exposure to $[r, r + d)$.
- `paced_tight_census_bound_all_F`: bounds recent theft producers to at most 1 in any window $u$ for all horizons $F$.
- `paced_budget_holds_under_timing`: proves the bad slots remain within `faultBudget(n)`.
The prose explicitly highlights that there is no execution-level separation between timed and untimed budgets, and that no-backdating is an operational hypothesis.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: The text explicitly discusses the convenience assumption `NoTheftBackdating`, noting it is asserted rather than derived from mint-timed primitives.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C90

a. **Hypotheses**: Fully disclosed in text:
- Mode 2 scheduled core unforgeability: `SchedCoreUnforgeable n schedule ops registry rented Stolen honestSigned now Δ`.
- Global fault budget: `ByzantineBounded n (badSched n schedule rented Stolen)`.
- Grounded certificates: `GroundedCertSched`.
- Tip recency: `now ≤ sTip.slot + Δ`.

b. **Conclusion**: Matches Lean.
`sched_recent_certified_suffix_agreement` proves certified suffix agreement under a global fault budget. The text explicitly acknowledges that carrying horizon scoping to mode-2 certificates remains future work.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: The global budget assumption is explicitly acknowledged as a limitation in the text.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C91

a. **Hypotheses**: Fully disclosed in text:
- Constructive counterexample witnesses for mode 2 (`badSched_single_key_safe_not_enough`) and mode 1 (`badKeyrotOn_single_key_safe_not_enough`).

b. **Conclusion**: Matches Lean.
Lean machine-checks counterexample executions where a slot is not rented and its producer's key at that slot is not stolen, yet the slot is classified as bad under the multi-key adversary definitions. The text faithfully uses these counterexamples to motivate why per-mode no-backdating is stated directly as an operational assumption.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; constructive negative existential witnesses.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C92

a. **Hypotheses**: Fully disclosed in text:
- Fault budget: `ByzantineBounded n bad`.
- Valid starting chain: `validChain n c = true`.
- Current slot belongs to honest producer: `producerForSlot n slot = me`.
- Delivery / cover assumption (Assumption~\ref{ass:delivery}): `HonestBlocksCover bad record (c ++ [nextBlock ...]) u n`.
- For global liveness: `genesisOk g`, strictly increasing slot sequence `IsChain (<) (g.slot :: ss)`, and window bounded bad slots `(badSlotsIn ...).card ≤ maxByzantine n`.

b. **Conclusion**: Matches Lean:
- Local liveness (`production_liveness`): `produceBlock?` succeeds and yields the valid next block extending $c$.
- Global liveness (`global_liveness`): `buildChain g ss` is valid (`validChain n = true`) with length `ss.length + 1`.
The prose explicitly notes that multi-chain fork-choice coalescence is not machine-checked.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Assumption~\ref{ass:delivery} (`HonestBlocksCover`) assumes synchronous arrival of honest blocks in every maturing window, which is explicitly disclosed in the text as liveness-only.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C93

a. **Hypotheses**: Fully disclosed in text:
- Parameters: $0 < n$, $0 \le \mathrm{baseline}$, $0 \le \mathrm{perBlock}$, $0 < \tau$.
- Sufficiency: $\mathrm{recommendedSlot}(n, \mathrm{baseline}, \mathrm{perBlock}) \le \tau$, initial backlog $u_0 \le n/2$.
- Necessity: $\mathrm{perBlock} < \tau < \mathrm{recommendedSlot}(n, \mathrm{baseline}, \mathrm{perBlock})$, steady state $\mathrm{nextBacklog}(u) = u$.

b. **Conclusion**: Matches Lean:
- `slot_time_sufficient`: proves $\forall j,\; \mathrm{backlog}(j) \le n/2 \land \mathrm{peakSuffix}(j) \le n$.
- `slot_time_necessary`: proves $n < \mathrm{peakSuffix}(u)$ at any steady-state backlog $u$.

c. **Quantifiers, parameter ranges and definitions**: Exact match over $\mathbb{Q}$.

d. **Convenience assumptions**: Prover throughput model assumes deterministic linear proving cost $\mathrm{baseline} + \mathrm{perBlock} \cdot b$.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C94

a. **Hypotheses**: Fully disclosed in text:
- Extracted Rust AST: `molt_petit.valid_chain n c = Result.ok true`.

b. **Conclusion**: Matches Lean.
`rust_valid_chain_sound` proves that if the extracted Rust validator accepts chain $c$, the semantic model predicate `MoltPetit.Model.ValidChain (↑n) (Rust.toModelChain c)` holds.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Relies on Charon + Aeneas translation pipeline to model Rust semantics.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C95

a. **Hypotheses**: Fully disclosed in text:
- Soundness bridge `rust_valid_chain_sound`.
- Underlying model hypotheses of Theorem~\ref{thm:lc} (Byzantine bound, unforgeability, hash injectivity, certificate grounding, tip recency, suffix overlap).

b. **Conclusion**: Matches Lean.
`rust_recent_tip_ancestor_mem` carries light-client safety to the extracted Rust validator. The prose accurately describes soundness as the direction carrying safety theorems to shipped code.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Assumes unverified frontend translations preserve Rust operational semantics.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C96

a. **Hypotheses**: Fully disclosed in text:
- $0 < \uparrow n$.
- Imported Rust validator: `molt_petit.valid_chain n c = Result.ok true` and `molt_petit.valid_chain_k n c = Result.ok true`.

b. **Conclusion**: Matches Lean:
- `rust_valid_chain_sound`: proves `ValidChain (↑n) (toModelChain c)`.
- `rust_valid_chain_k_sound`: proves `ValidChain (↑n) (toModelChain c) ∧ KeyIndexMonotone (↑n) (toModelChain c)`.
The prose explicitly notes that rotation pins remain checked at model level.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None beyond the Charon/Aeneas translation base.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C97

a. **Hypotheses**: Fully disclosed in text:
- Backend-generic validator instantiated over `Rust.UB` (`U64Backend`): `molt_petit.valid_chain_be Rust.UB () n q (Rust.toChainG c) = Result.ok true`.
- Quorum calculation: `molt_petit.quorum n = Result.ok q`.

b. **Conclusion**: Matches Lean.
`valid_chain_be_validChain` proves soundness of the generic validator under the native u64 backend. The prose explicitly and prominently discloses that per-gadget faithfulness of the circuit backend (Plonky2) is an external trust assumption, stated rather than proved.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: External trust assumption of circuit backend faithfulness is explicitly acknowledged.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C98

a. **Hypotheses**: Contextual engineering claim based on benchmark table (Table~\ref{tab:bench}) showing Plonky2 recursive circuit row counts and proving overhead.

b. **Conclusion**: Matches empirical findings reported in text; no Lean formalization claimed (`lean_decls: []`).

c. **Quantifiers, parameter ranges and definitions**: Informal engineering terminology.

d. **Convenience assumptions**: Relies on specific benchmark hardware and Plonky2 configuration.

e. **Do the Lean definitions mean what the prose says?** N/A (empirical benchmark evaluation).

Verdict: FAITHFUL

---

### C99

a. **Hypotheses**: Qualitative survey and comparison with Ouroboros literature (Praos, Genesis).

b. **Conclusion**: Accurately describes the distinction between Molt Petit's deterministic window-density rule with round-robin leader and Ouroboros's stake-weighted VRF-based probabilistic finality.

c. **Quantifiers, parameter ranges and definitions**: N/A (related work).

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** N/A (prose comparison).

Verdict: FAITHFUL

---

### C100

a. **Hypotheses**: Qualitative literature comparison with Plumo.

b. **Conclusion**: Accurately describes Plumo's SNARK-proved committee hand-offs with pen-and-paper committee-weighted analysis vs Molt Petit's deterministic machine-checked consensus.

c. **Quantifiers, parameter ranges and definitions**: N/A (related work).

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** N/A (prose comparison).

Verdict: FAITHFUL

---

### C101

a. **Hypotheses**: Qualitative literature comparison with verified consensus systems (Velisarios, Verdi, IronFleet).

b. **Conclusion**: Accurately contrasts Molt Petit's pipeline (importing deployed Rust and TypeScript code into Lean) with refinement/extraction pipelines from prover-internal models.

c. **Quantifiers, parameter ranges and definitions**: N/A (related work).

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** N/A (prose comparison).

Verdict: FAITHFUL

---

### C102

a. **Hypotheses**: Fully disclosed. The text provides a rigorous, exhaustive disclosure of the entire trusted computing base:
- Lean kernel.
- Pinned translation front-ends (Charon + Aeneas, Thales) and hand-audited emitter bug corrections.
- Circuit backend gadget faithfulness (external trust assumption; equivalence lemma `valid_chain_be_validChain` proved at native u64 instantiation).
- Operational assumptions of Section~\ref{sec:assumptions}.
- Key-stealing signature surface (assumed, not derived from timed model).
- Out-of-circuit trust anchor and unverified clock reading in node loop.

b. **Conclusion**: Matches Lean. Perfectly summarizes what is verified versus what is admitted as named hypotheses or trusted tools.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Explicitly catalogs all convenience and operational assumptions.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C103

a. **Hypotheses**: Fully disclosed in text:
- Timed log: `log : MoltPetit.Model.TimedLog`.
- Participant index and slot: $p = \mathrm{producerForSlot}(n, s)$.

b. **Conclusion**: Matches Lean.
`MoltPetit.Model.projectSigned` defines the stamped signing log by extracting the unique block stamped $s$ signed at real slot $s$ when $p = \mathrm{producerForSlot}(n, s)$.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Canonical choice at honest slots via `TimedExecution.honest_once`; arbitrary choice at bad slots which theorems never consult.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C104

a. **Hypotheses**: Fully disclosed in text:
- Byzantine slots: `bad : MoltPetit.Model.ByzantineSlots`.
- Real-time log: `log : MoltPetit.Model.TimedLog`.
- EUF-CMA bridge: verifying signatures were produced at some real slot.
- `NoBackdate bad log`: $\forall r\; B,\; B \in \mathrm{log}(r) \to \neg\mathrm{bad}(B.\mathrm{slot}) \to B.\mathrm{slot} = r$.

b. **Conclusion**: Matches Lean.
Defines the two operational bridge assumptions connecting the timed real-time log to the stamped unforgeability model.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Explicitly isolated as the essential operational assumption not provided by the bare timed execution model.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C105

a. **Hypotheses**: Fully disclosed in text:
- `TimedExecution n bad log G`.
- `NoBackdate bad log`.
- EUF-CMA bridge: $\forall B,\; \mathrm{Signed}(B) \to \exists r,\; B \in \mathrm{log}(r)$.

b. **Conclusion**: Matches Lean.
`sigUnforgeableRecent_of_timed` proves `SigUnforgeableRecent n bad Signed (projectSigned n log) now Δ` at every recency window $\Delta$. The proof never uses the recency parameter $\Delta$, exactly as claimed.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None beyond the stated and disclosed hypotheses.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C106

a. **Hypotheses**: Fully disclosed in text:
- Evaluated at $n = 2$.

b. **Conclusion**: Matches Lean.
`noBackdate_independent` constructively proves $\exists \mathrm{bad}\; \mathrm{log}\; G,\; \mathrm{TimedExecution}\; 2\; \mathrm{bad}\; \mathrm{log}\; G \land \neg\mathrm{NoBackdate}\; \mathrm{bad}\; \mathrm{log}$.

c. **Quantifiers, parameter ranges and definitions**: Exact match ($n = 2$).

d. **Convenience assumptions**: None; constructive witness exhibiting a bad real slot signing a block stamped for an honest slot.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C107

a. **Hypotheses**: Fully disclosed in text:
- Multi-key rotation schedules and intervals: `badSched` and `badKeyrotOn`.

b. **Conclusion**: Matches Lean.
`badSched_single_key_safe_not_enough` and `badKeyrotOn_single_key_safe_not_enough` prove that single-key safety does not imply slot safety in multi-key settings, justifying why Theorem~\ref{thm:timed-uniq} does not transport to the rotation modes and why per-mode no-backdating is stated directly as an operational assumption.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; constructive counterexamples.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

FAITHFULNESS: DONE
