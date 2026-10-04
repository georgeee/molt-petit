# Faithfulness Audit

Adversarial audit of formal and prose claims in `paper/molt.tex` against Lean 4 definitions and theorems (`verify-out/lean-statements.txt`, `verify-out/claims.json`, and source files in `Molt/`, `MoltPetit/`, and `Rust/`).

---

### C1

a. **Hypotheses**: High-level summary of formal verification scope. The paper explicitly qualifies: *"All safety claims are machine-checked in Lean~4 under the cryptographic and operational assumptions of Section~\ref{sec:assumptions} --- the core claims about the imported Rust validator source itself, proved sound against the model and re-used as the recursive-proof circuit (with circuit-backend faithfulness a stated trust assumption), and today's key-rotation results at model level."* The underlying formal theorems require cryptographic unforgeability (`SigUnforgeableRecent` / `hbridge`), hash collision resistance (`id_inj`), certificate grounding (`GroundedCert`), Byzantine quorum bounds (`ByzantineBounded n bad`), and clock tracking (`hRecent`). Section~\ref{sec:assumptions} discloses all of these, and the parenthetical explicitly acknowledges that Plonky2 circuit backend faithfulness is an external trust assumption rather than a Lean-verified equivalence.

b. **Conclusion**: Matches the Lean development. Rust validator source code is imported via Charon/Aeneas and proved sound against the model (`Rust/Soundness.lean`), and key-rotation results are proved at model level (`Molt/`).

c. **Quantifiers, parameter ranges and definitions**: Parameter bounds ($n \ge 1$, $f < n/3$) are referenced via Section~\ref{sec:assumptions}.

d. **Convenience assumptions**: Circuit backend arithmetic faithfulness is an external trust assumption (disclosed in text).

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C2

a. **Hypotheses**: High-level overview claim. In Lean, the forged-chain growth rate bound (`Molt.forged_time_bound` / `Molt.forged_chain_time_bound`) requires $2 \le n$, `TimedExecution n bad log G`, `FaultBounded n bad`, `ValidChain n c`, block availability at $rNow$, and genesis with no predecessor. Timed light-client safety (`timed_light_client_safety` / `rust_timed_certified_agreement`) requires $1 \le n$, `TimedExecution`, `ByzantineBounded`, signature validity/availability at verifier time $R$, `GroundedCert`, and tip recency $R \le \mathrm{sTip.slot} + n$. Section~\ref{sec:assumptions} and Section~\ref{sec:results} explicitly disclose these.

b. **Conclusion**: Lean's `forged_time_bound` bounds block index advancement on forged suffixes relative to elapsed real time by approximately half speed ($\approx \Delta r / 2$). Light-client safety is proved in the timed model, and three key rotation modes are formally developed.

c. **Quantifiers, parameter ranges and definitions**: Lean's `forged_time_bound` requires $2 \le n$ (disclosed in Theorem~\ref{thm:forge}). Basic light-client safety requires $1 \le n$.

d. **Convenience assumptions**: The adversary harvesting coerced signatures stamped for any slot is formalized in `TimedExecution`, where Byzantine slots can sign blocks stamped for any slot matching their producer residue class.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C3

a. **Hypotheses**: Lean's ground-truth theorem (`@Rust.rust_timed_certified_agreement`) requires:
1. `1 ≤ ↑n`
2. `MoltPetit.Model.TimedExecution (↑n) bad log G`
3. `MoltPetit.Model.ByzantineBounded (↑n) bad`
4. Causality / unforgeability: `∀ B, RustSigned I crypto n B → ∃ r ≤ R, B ∈ log r`
5. Signature monotonicity / crypto compatibility: `∀ b, RustSigned I crypto' n b → RustSigned I crypto n b`
6. Certificate grounding for both verifiers: `∀ cert, I.cert_verify crypto cert = ok true → ∃ cl, I.cert_claim crypto cert = ok cl ∧ GroundedCert ...`
7. Validation success for both certified chains: `validate_certified_chain` returns `ok true`
8. Non-empty stripped suffixes: `strip_sigs suffix = ok (.Cons sr1 srtl)` and for `suffix'`
9. Tip recency for both tips: `R ≤ sTip.slot + ↑n` and `R ≤ sTip'.slot + ↑n`
10. Grounded history witnesses: `GroundedHistory ... cl c` and `GroundedHistory ... cl' c'`
11. Depth bounds on **both** chains: `h + ↑n < (c ++ ...).length` AND `h + ↑n < (c' ++ ...).length`.
Hypotheses 1--10 are disclosed in Section~\ref{sec:assumptions}, but hypothesis 11 is not disclosed in the prose: the text states that the client *"may act on everything $n$ blocks deep"*, which claims safety based on inspecting a single certificate, without qualifying that competing chains must also extend to depth $h + n$.

b. **Conclusion**: Overclaim. The prose states *"the client may act on everything $n$ blocks deep"*, implying single-chain finality. Lean's theorem is a two-chain agreement theorem: it proves that if two certified chains both have recent tips and *both* reach height $h + n$, they agree at height $h$. It does not prove that every competing valid recent certified chain must reach height $h + n$, nor does it rule out a shorter competing chain without additional height bounds.

c. **Quantifiers, parameter ranges and definitions**: $n \ge 1$. Depth $n$ requires $h + n < \mathrm{length}$ on both presented chains.

d. **Convenience assumptions**: The theorem relies on `GroundedCert` and `GroundedHistory` connecting the recursive certificate claim to full chain semantics.

e. **Do the Lean definitions mean what the prose says?** Only partially: Lean proves mutual agreement between two sufficiently long recent chains, not unconditional single-chain finality against arbitrary shorter chains.

Severity: MAJOR
Fix: Clarify that the theorem guarantees agreement between any two certified recent chains that both reach height $h + n$ (as stated in Theorem~\ref{thm:lc}).

---

### C4

a. **Hypotheses**: Fully disclosed in text. Accurately details the Charon + Aeneas translation pipeline, notes that key rotation pins are checked at model level today, and explicitly discloses that circuit-backend arithmetic faithfulness is an external trust assumption rather than a Lean-verified equivalence.

b. **Conclusion**: Matches Lean formalization. Rust validator AST is proved sound against `MoltPetit.Model` in `Rust/Soundness.lean`; TypeScript validator is proved sound in `MoltPetit/Soundness.lean`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Circuit backend faithfulness is an external trust assumption, explicitly disclosed in the text.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C5

a. **Hypotheses**: Fully disclosed in text:
- Byzantine bound: `MoltPetit.Model.ByzantineBounded n bad`
- Valid chain: `MoltPetit.Model.validChainK n c = true`
- Tip slot strictly less than production slot: `tip.slot < slot`
- Producer allocation: `MoltPetit.Model.producerForSlot n slot = me`
- Valid slot records: `∀ s, ∀ B ∈ record s, B.slot = s`
- Continued density coverage: `∀ u, tip.slot + 1 < u + n → u + n ≤ slot + 1 → MoltPetit.Model.HonestBlocksCover bad record (...) u n`
- Key floor: `MoltPetit.Model.keyFloor n c me ≤ keyIndex`
The paper explicitly states the key condition *"under continued density coverage"*.

b. **Conclusion**: Equal to Lean. Lean proves `produceBlock?` outputs the extended block and `validChainK' n Δconf` remains true. The prose accurately restricts this to *"mode 1's local single-block production step"*.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: `HonestBlocksCover` assumes density coverage holds for the new block; this is standard for a local production step lemma.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C6

a. **Hypotheses**: Fully disclosed in text. Lean lemmas `badKeyrot_lossOnly`, `badSched_lossOnly`, and `exposedSched_lossOnly` set `stolen = fun _ _ => False`, which is the formal definition of zero permanent key theft.

b. **Conclusion**: Equal to Lean. When no keys are stolen, `badKeyrot` reduces to `rented`, `badSched` reduces to `rented`, and `exposedProducersSched` evaluates to empty set $\emptyset$.

c. **Quantifiers, parameter ranges and definitions**: Exact match across all parameters.

d. **Convenience assumptions**: The premise `fun _ _ => False` encodes the exact boundary where key theft is absent.

e. **Do the Lean definitions mean what the prose says?** Yes, these lemmas prove that generalized corruption sets collapse to the baseline per-slot corruption budget when permanent theft is absent.

Verdict: FAITHFUL

---

### C7

a. **Hypotheses**: Fully disclosed in text. Lean's `Molt.no_budget_beyond` assumes a window $u$ and a set of producers $P$ such that each $i \in P$ has a slot in $[u, u+n)$ where a stolen key version remains in force ($j \ge \mathrm{inForce}(n, \Delta_{\mathrm{conf}}, c_0, i, s) \land \mathrm{Stolen}(i, j)$), with $|P| > \mathrm{faultBudget}(n)$. The paper states this as: *"past the cadence the theorems' fault-budget assumption becomes one no deployment can stand behind --- quiet thefts accumulate until nothing satisfies it (\code{no\_budget\_beyond})"*.

b. **Conclusion**: Equal to Lean. Lean concludes that the corrupted slots in window $u$ strictly exceed $\mathrm{faultBudget}(n)$ ($
eg (\mathrm{badSlotsIn} \le \mathrm{faultBudget}(n))$). The prose characterizes this mathematically as making the budget assumption unsatisfiable, forcing clients to stop and re-join from a trusted checkpoint.

c. **Quantifiers, parameter ranges and definitions**: Exact match across all window and budget parameters.

d. **Convenience assumptions**: None; direct combinatorial consequence of cumulative corruptions.

e. **Do the Lean definitions mean what the prose says?** Yes. The text correctly identifies this as *"operational discipline the theorems force rather than state"*, accurately reflecting the boundary between the formal counting lemma and the operational protocol.

Verdict: FAITHFUL

---

### C8

a. **Hypotheses**: Disclosed in text with one minor qualification. Lean's `lockstep_recent_certified_suffix_agreement` assumes $1 \le n$, `LockstepPackage` (with cumulative budget $R + T \le \mathrm{maxByzantine}$), two grounded certificates rooted at a shared genesis $G$, and valid lockstep suffixes with recent tips. It requires that the queried blocks $B, B'$ be $n$ deep *within their presented suffixes* ($i + n < \mathrm{suffix.length}$ on both suffixes) at equal global heights. The paper states that *"Mode 3's guarantees hold at the certificate presentation as well as for full chains under the cumulative budget at depth $n$ (\code{lockstep\_recent\_certified\_suffix\_agreement}); lifting certificates to per-generation erasure credit at depth $2n$ remains future work."*

b. **Conclusion**: Equal to Lean. Lean concludes $B = B'$ for blocks $n$ deep in the suffix.

c. **Quantifiers, parameter ranges and definitions**: Parameter bounds ($n \ge 1$, cumulative budget) match.

d. **Convenience assumptions**: Operates under the cumulative budget package and shared genesis, as explicitly acknowledged in the text.

e. **Do the Lean definitions mean what the prose says?** Yes. The text accurately delineates certificate-level agreement under the cumulative budget from the per-generation erasure credit model.

Verdict: FAITHFUL

---

### C9

a. **Hypotheses**: Fully disclosed in text. Lean's `lockstep_client_safety_gen` and `lockstepGen_recent_tip_ancestor_mem` assume $1 \le n$, `LockstepPackageGen` (per-generation theft census $\le T$ for each generation $j$ separately, rented slots per window $\le R$, $R + T \le \mathrm{maxByzantine}$), valid lockstep chains with recent tips, and length $> 2n$. Crucially, no shared-genesis hypothesis is assumed. The paper explicitly lists every one of these conditions: *"under a per-generation census --- for each generation $j$ separately, at most $T$ seats whose generation-$j$ key is stolen --- the same agreement holds at confirmation depth $2n$ instead of $n$ (at equal tip heights, \code{lockstep\_client\_safety\_gen}; at unequal heights the lower chain's $2n$-deep block lies on the taller, \code{lockstepGen\_recent\_tip\_ancestor\_mem}), and with no shared-genesis hypothesis"*.

b. **Conclusion**: Equal to Lean. Proves exact block agreement at depth $2n$ for equal tip heights, and prefix membership at depth $2n$ for unequal heights.

c. **Quantifiers, parameter ranges and definitions**: Exact match ($2n$ confirmation depth, per-generation generation bound).

d. **Convenience assumptions**: The physical destruction / erasure premise is formalized as bounding key theft per generation $j$ rather than cumulatively across time.

e. **Do the Lean definitions mean what the prose says?** Yes. Lean's definitions match the prose description of per-generation erasure credit and genesis independence.

Verdict: FAITHFUL

---

### C10

a. **Hypotheses**: Fully disclosed in text. In Table~1 (Mode 0: no theft), the client trust profile is given as "genesis + clock", with no erasure and no anchor. Headline theorems cited are `timed_light_client_safety` and `Rust.rust_timed_certified_agreement`. The formal hypotheses (clock synchronization, signature availability before verification time $R$, Byzantine budget, grounded certificates) are developed in Section~\ref{sec:assumptions} and Theorem~\ref{thm:lc}.

b. **Conclusion**: Equal to Lean. Accurately classifies Mode 0 baseline safety.

c. **Quantifiers, parameter ranges and definitions**: Parameter ranges match ($n \ge 1$).

d. **Convenience assumptions**: Relies on circuit-backend arithmetic faithfulness as an external trust assumption (disclosed in text).

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C11

a. **Hypotheses**: Fully disclosed in text. Table~1 summarizes Mode 1 (reactive): pin computed from chain floor $n$ slots deep, client holds "genesis, clock, anchor, $n$-slot sync", no erasure, anchor required, headline theorem `sync_rule_timed` (Theorem~\ref{thm:refresh}). Lean theorem `sync_rule_timed` requires: client anchored at block $A$ $n$-deep below a verified tip from at most $n$ slots ago (`now ≤ t + n`), both competing chains contain $A$, victim reaction within delay $d$ (`Reacts`), and cumulative rent + theft budget $\le \mathrm{faultBudget}$ on trailing windows starting in the trailing $5n$ slots.

b. **Conclusion**: Equal to Lean. Cites headline agreement theorem for reactive key rotation.

c. **Quantifiers, parameter ranges and definitions**: Exact match across sync period $n$, trailing window $5n$, and confirmation depth $n$.

d. **Convenience assumptions**: The hypothesis `Reacts` requires victims to rotate within $d$ slots on the chain being validated; Section~\ref{sec:refresh} and Section~\ref{sec:limitations} explicitly disclose this as an open limitation of the current formalization.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C12

a. **Hypotheses**: Fully disclosed in text. Table~1 summarizes Mode 2 (scheduled): pin computed from slot arithmetic $\mathrm{gen}(s)$, client holds "genesis + clock + $\mathrm{gen}$", no erasure, no anchor, headline theorems `sched_recent_tip_ancestor_agreement_horizon` and `sched_recent_tip_ancestor_mem_horizon` (Theorem~\ref{thm:sched}). The formal theorems require $1 \le n$, `SchedUnforgeable`, `SignedHashInjective`, Byzantine budget starting from horizon $H$, horizon side conditions $H + n \le \mathrm{tip.slot} + 1$, and recent tips.

b. **Conclusion**: Equal to Lean. Accurately references both equal-height agreement and unequal-height prefix ancestor membership.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Just-in-time key derivation (`NoPrematureTheft`) is required operationally and scrutinized in Section~\ref{sec:opmodel} and Section~\ref{sec:scheduled}.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C13

a. **Hypotheses**: Fully disclosed in text. Table~1 summarizes Mode 3 (lockstep): pin computed from roster counter (no-mixing), client holds "genesis + clock", erasure credited (forward-referencing Theorem~\ref{thm:lock-gen}), anchor "no", headline theorem `lockstep_client_safety` (Theorem~\ref{thm:lock}). Lean theorem `lockstep_client_safety` assumes $1 \le n$, `LockstepPackage` (cumulative budget), valid lockstep chains rooted at common genesis $G$ (`blockAt? sc 0 = some G`), recent tips, length $> n$, and equal tip heights.

b. **Conclusion**: Equal to Lean. Proves block agreement at depth $n$.

c. **Quantifiers, parameter ranges and definitions**: Exact match ($n \ge 1$, depth $n$).

d. **Convenience assumptions**: Assumes lockstep roster progression and common genesis (the genesis assumption is relaxed in Theorem~\ref{thm:lock-gen}).

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C14

a. **Hypotheses**: Fully disclosed in text. Table~1 and accompanying paragraph cite Theorem~\ref{thm:lock-gen}: `lockstep_client_safety_gen` and `lockstepGen_recent_tip_ancestor_mem`. Formal hypotheses require $1 \le n$, `LockstepPackageGen` (per-generation budget $T$ per generation $j$, rent budget $R$, $R + T \le \mathrm{maxByzantine}$), valid lockstep chains with recent tips, and length $> 2n$. No shared genesis is required.

b. **Conclusion**: Equal to Lean. Proves agreement at depth $2n$ for equal tip heights and ancestor containment for unequal heights.

c. **Quantifiers, parameter ranges and definitions**: Exact match (depth $2n$).

d. **Convenience assumptions**: Physical destruction/erasure is modeled via per-generation budget isolation.

e. **Do the Lean definitions mean what the prose says?** Yes. The text correctly summarizes the trust model: *"mode 3 trusts roster coordination plus physical destruction"*.

Verdict: FAITHFUL

---

### C15

a. **Hypotheses**: Definitional statement. Defines slot-to-producer assignment. Lean definition `producer (n slot : Nat) : Nat := slot % n` in `Molt/Protocol.lean` (and `producerForSlot` in `MoltPetit.Model.Definitions.lean`). Fully disclosed in text.

b. **Conclusion**: Matches Lean definition ($s mod n$).

c. **Quantifiers, parameter ranges and definitions**: Exact match ($s, n \in \mathbb{N}$). Lean's modulo arithmetic matches the prose description.

d. **Convenience assumptions**: Static deterministic round-robin schedule without dynamic leader election.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C16

a. **Hypotheses**: Table~1 (Notation) summarizes parameters and relations ($n$, $\quorum$, $max$, $	au$, $\mathit{now}$, $H(\cdot)$, $\mathit{keyFor}(i,j)$, `keyIndex`, $
ho, T$, $R, \mathit{gen}(s)$). Fully disclosed in text.

b. **Conclusion**: Equal to Lean. Accurately summarizes definitions and relations used across the paper.

c. **Quantifiers, parameter ranges and definitions**: Exact match: $\quorum = \lceil 2n/3 
ceil$, $max = \lfloor (n-1)/3 
floor$, recency bound $b + \delta \le n$, and $\mathit{gen}(s) = \lfloor s/R 
floor$.

d. **Convenience assumptions**: None; accurately captures the parameter space.

e. **Do the Lean definitions mean what the prose says?** Yes; `keyIndex` is a `Nat` field on `Block` representing the key version.

Verdict: FAITHFUL

---

### C17

a. **Hypotheses**: Definitional prose for `Block.contentsHash`. Lean represents `contentsHash : Nat` on `MoltPetit.Model.Block`. Fully disclosed in text.

b. **Conclusion**: Equal to Lean. Lean's consensus rules (`genesisOk`, `childOk`, `linksOk`, `windowDense`, `denseSoFar`, `validChain`, `validChainK`) never inspect `contentsHash`.

c. **Quantifiers, parameter ranges and definitions**: Exact match (`contentsHash : Nat`).

d. **Convenience assumptions**: Payload transactions are abstracted to a single hash commitment.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C18

a. **Hypotheses**: Definitional prose for `Block.keyIndex`. Lean definition carries `keyIndex : Nat` in `MoltPetit.Model.Block`. Fully disclosed in text.

b. **Conclusion**: Equal to Lean. Key rotation is carried in-band via `keyIndex` and checked by `keyMonoOk` and per-mode pin rules.

c. **Quantifiers, parameter ranges and definitions**: Exact match (`keyIndex : Nat`).

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C19

a. **Hypotheses**: Fully disclosed in text. The paper specifies the preimage contract for block identifiers: $\mathit{id} = H(\mathit{slot}, \mathit{height}, \mathit{prev}, \mathit{parentSig}, \mathit{contentsHash}, \mathit{keyIndex})$, noting that the consensus rules treat ids as opaque and rely on collision resistance. In Lean, `Block.prev : Option Nat` and `Block.id : Nat`, with collision resistance captured via explicit hypothesis `SignedHashInjective`.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Treating cryptographic collision resistance as an abstract hypothesis (`SignedHashInjective`) on signed/genesis blocks is explicitly disclosed in the text.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C20

a. **Hypotheses**: Fully disclosed in text. Defines a valid chain structure: heights increase by one, slots strictly increase, each block links to parent id, rooted at genesis (`height = 0`, `prev = none`). Lean functions `genesisOk`, `childOk`, and `linksOk` formalize this verbatim.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match across height, slot, and parent id linkage.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C21

a. **Hypotheses**: Fully disclosed in text. Chain density requires that every matured window $[u, u+n)$ (where $u + n \le \mathit{tip.slot} + 1$) contains at least $\quorum$ blocks. Lean definitions `windowDense`, `denseSoFar`, and `validChain` implement this condition.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match: window size $n$, quorum threshold $\quorum = \lceil 2n/3 
ceil$, matured window condition $u + n \le \mathit{tip.slot} + 1$.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C22

a. **Hypotheses**: High-level overview claim. Informal explanation of the combinatorial pigeonhole argument: any two dense chains in an $n$-slot window collect $\quorum$ blocks each, overlapping in $2\quorum - n > max$ slots, forcing a shared honest slot. Lean formalizes this in `exists_honest_shared_slot` (using `quorum_overlap: maxByzantine n < 2 * quorum n - n`) in `MoltPetit/Model/Safety.lean`.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match ($1 \le n$).

d. **Convenience assumptions**: Requires that honest producers produce at most one block per slot (formalized in `SigningLogSingleSlot` / `TimedExecution`).

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C23

a. **Hypotheses**: Fully disclosed in text. Defines the monotonic key index condition: along a chain, a producer's declared key version never decreases. Lean definition `keyMonoOk` in `Molt/Rotation.lean` and `MoltPetit/Model/KeyIndex.lean` formalizes this and is proved equivalent to `KeyIndexMonotone` via `keyMonoOk_sound`.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match (compares pairs with equal producer residue modulo $n$).

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C24

a. **Hypotheses**: Fully disclosed in text. Defines `validChainK` as the conjunction of structural validity, window density, and key monotonicity. Lean definition `validChainK n c := validChain n c && keyMonoOk n c` in `Molt/Rotation.lean` (and `MoltPetit/Model/KeyIndex.lean`).

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C25

a. **Hypotheses**: Fully disclosed in text. Defines the cryptographic interfaces `SigOps` (`sign` and `verify`), `KeyRegistry` (`keyFor(i, j)` mapping seat and version to public key), and `CertOps` (`claim`, `verify`, and `generate`). Lean structures `SigOps`, `KeyRegistry`, and `CertOps` in `MoltPetit/Model/Definitions.lean` and `Molt/Verifier.lean` formalize these interfaces verbatim.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match across signature operations, versioned key directory lookup, and certificate inspection/extension.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C26

a. **Hypotheses**: Fully disclosed in text. States the light client acceptance rule: accept a certified chain if and only if (1) it validates under `validCertifiedChain` plus mode key checks, and (2) it satisfies the recency bound $now \le \mathit{tip.slot} + b$ with $R \le now + \delta$ and $b + \delta \le n$. The text explicitly notes that the clock comparison is implemented outside the Lean validator function. In the Lean development, validation is defined in `validCertifiedChain` while recency is an explicit hypothesis in the certified safety theorems.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match ($b + \delta \le n$, $R \le now + \delta$).

d. **Convenience assumptions**: Recency premise ($now \le \mathit{tip.slot} + \Delta$) is explicit in both prose and Lean theorem signatures.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C27

a. **Hypotheses**: Fully disclosed in text. Paragraph heading introducing the certified chain validator `validCertifiedChain`. Formalized in Lean as `validCertifiedChain n sigOps registry certOps cc`.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C28

a. **Hypotheses**: Fully disclosed in text. Defines the five validation checks: (1) certificate verification via `CertOps.verify`; (2) suffix signatures verified via `sigsOk` against `keyFor` at declared versions; (3) tip-to-suffix and internal suffix linkage (`height = tipHeight + 1`, `tipSlot < first.slot`, `first.prev = tipId`, and `linksOk`); (4) window density of newly matured windows over `tail ++ suffix` via `validSuffix`; and (5) key monotonicity (`keyMonoOk`) and mode rotation pins. The text explicitly notes that checks 1--4 are bundled into `validCertifiedChain` / `validSuffix`, while check 5 is enforced in the full-chain validator `validSignedChainK'` and the certified agreement theorems.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match between paper checks 1--4 and Lean's `validateSuffix` / `validCertifiedChain`, and check 5 with the full-chain / mode-specific definitions.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C29

a. **Hypotheses**: Fully disclosed in text. Parenthetical reference connecting the three certified validation modes to their corresponding Lean safety theorems: `keyrot_recent_certified_suffix_agreement` (Mode 1), `sched_recent_certified_suffix_agreement` (Mode 2), and `lockstep_recent_certified_suffix_agreement` (Mode 3).

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match with the corresponding Lean theorem names and statements.

d. **Convenience assumptions**: The theorems require their respective mode packages (`badKeyrotOn`, `badSched`, `LockstepPackage`, recency $now \le \mathit{sTip.slot} + \Delta$), which are disclosed in text and examined in their dedicated sections.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C30

a. **Hypotheses**: Fully disclosed in text. Describes the structural relationship between full genesis replay (`validChain`, checking `denseSoFar` over all windows up to the tip) and incremental checking (`validSuffix`, checking only windows that mature in $[lo, hi)$ over the boundary buffer `tail ++ suffix`). The inductive preservation lemmas in `MoltPetit/Model/Grounded.lean` formally verify this equivalence across chain extensions.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match: window maturity index range is $lo = \mathit{tipSlot} + 2 - n$ to $hi = \mathit{t.slot} + 2 - n$.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C31

a. **Hypotheses**: Fully disclosed in text. Defines honest block production `produceBlock?`: a node produces only in its assigned slot (`producer n slot = me`), links to the current tip, signs the block, and emits it only if the extended suffix passes `validSuffix`. Lean definition `produceBlock?` in `Molt/Verifier.lean` (and `produceBlockCert?` in `MoltPetit/Model/Definitions.lean`) formalizes this exact behavior.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C32

a. **Hypotheses**: Fully disclosed in text. Defines fork choice `selectChain`: adopt a candidate certified chain if and only if it validates under `validCertifiedChain` and has strictly greater tip height than the current chain (`tipHeight candidate > tipHeight current`). Lean definition `selectChain` in `Molt/Verifier.lean` (and `selectCertifiedChain` in `MoltPetit/Model/Definitions.lean`) formalizes this verbatim.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C33

a. **Hypotheses**: Fully disclosed in text. Explains compaction: jumping backwards to the latest available verified certificate whose claim matches the intermediate state, and requiring the resulting certified chain to pass `validCertifiedChain`. Lean implementations (e.g. in `MoltPetit/TS/Emitted.lean`) explicitly gate compaction on `validateCertifiedChain`.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None. Compaction is untrusted and validated.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C34

a. **Hypotheses**: Fully disclosed in text (Assumption 1, Fault budget). States that in any window of $n$ consecutive real-time slots, the adversary controls at most $\maxByz = \lfloor (n - 1) / 3 \rfloor$ slots. Formally defined in Lean as `ByzantineBounded n bad := \forall u, (badSlotsIn bad u n).card \le faultBudget n` where `faultBudget n = (n - 1) / 3`.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match across window length $n$, slot offset $u$, and bound $\lfloor (n - 1) / 3 \rfloor$.

d. **Convenience assumptions**: Dynamic windowed fault budget assumption, standard for sliding-window consensus protocols.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C35

a. **Hypotheses**: Fully disclosed in text (Assumption 2, Signatures). The text introduces `TimedExecution`, positing that signing occurs at discrete real slots. Formally, `TimedExecution n bad log G` packages five invariants over a physical-time log (`TimedLog := Nat → Finset Block`): `key_match`, `honest_stamp`, `honest_once`, `chain_order`, and `id_inj`.

b. **Conclusion**: Equal to Lean structure `TimedExecution`.

c. **Quantifiers, parameter ranges and definitions**: Exact match across slot count $n$, Byzantine slot set $bad$, physical log $log$, and genesis block $G$.

d. **Convenience assumptions**: The assumption models physical time where an honest slot signs only for itself and at most once, while Byzantine slots can sign arbitrarily for their assigned producer modulo $n$. Realistic abstraction of digital signature custody and scheduling.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C36

a. **Hypotheses**: Fully disclosed in text. The prose explicitly itemizes: (a) custody, (b) unforgeability, and (c) the timed signing discipline:
- `key_match`: at bad slots, arbitrary signatures with stamp in the producer's residue class modulo $n$ (`B ∈ log r → B.slot % n = r % n`);
- `honest_stamp`: honest slots sign only their current block (`¬bad r → B ∈ log r → B.slot = r`);
- `honest_once`: honest slots sign at most once (`¬bad r → B ∈ log r → B' ∈ log r → B = B'`);
- `hbridge`: signatures accepted at real slot $R$ were produced at some real slot $\le R$ (`Signed B → ∃ r ≤ R, B ∈ log r`).
All hypotheses and their identifiers match Lean definitions directly.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The text correctly identifies `hbridge` as an explicit theorem parameter combining causality and EUF-CMA security.

d. **Convenience assumptions**: `hbridge` requires that any signature accepted by a verifier by real time $R$ originated at some real time $r \le R$. This models physical causality and cryptographic unforgeability.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C37

a. **Hypotheses**: Fully disclosed in text. The prose asserts that the id-formation contract ensures a block is signed only once its parent is available (`chain_order`). In Lean, `TimedExecution.chain_order` states:
`∀ ⦃r : Nat⦄ ⦃B : Block⦄, B ∈ log r → ∀ ⦃i : Nat⦄, B.prev = some i → ∃ P : Block, P.id = i ∧ AvailableAt log G P r`, where `AvailableAt log G P r := P = G ∨ ∃ r' ≤ r, P ∈ log r'`.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match. Quantifies over all blocks in the log at real slot $r$ with parent pointer $i$, producing a block $P$ available at or before $r$.

d. **Convenience assumptions**: Justified by cryptographic hash binding in block ID formation ($id = H(slot, height, prev, ...)$); constructing a block pointing to parent ID $i$ requires knowledge of $i$, which by collision/preimage resistance implies the parent was already formed.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C38

a. **Hypotheses**: Fully disclosed in text (Lean citation marker for Assumption 2). References `TimedExecution` and `hbridge`.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None beyond those analyzed in C35–C37.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C39

a. **Hypotheses**: Fully disclosed in text (Assumption 3, Hash collision resistance). The prose states that collision resistance holds over occurring blocks: any two blocks occurring in the execution with equal IDs are equal (`TimedExecution.id_inj` over `SignedEver`). In Lean:
`id_inj : ∀ ⦃B B' : Block⦄, SignedEver log G B → SignedEver log G B' → B.id = B'.id → B = B'`, where `SignedEver log G B := B = G ∨ ∃ r, B ∈ log r`.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The text explicitly clarifies why injectivity is restricted to `SignedEver` rather than the entire universe of syntactically well-typed `Block`s.

d. **Convenience assumptions**: Scoping collision resistance to the domain of blocks actually signed or genesis is mathematically necessary to avoid trivial counterexamples from the pigeonhole principle on fixed-length digests, while faithfully capturing cryptographic collision resistance.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C40

a. **Hypotheses**: Fully disclosed in text. Explains the scoping of hash injectivity under key rotation:
- For chain-level sync-rule results (Theorem 4 / `thm:refresh`): scoped to `KeyStealingSigned` (blocks verifying under *some* registered version of their designated producer: `∃ sig j, ops.verify (registry (producerForSlot n B.slot) j) B sig = true`);
- For scheduled, lockstep, and certified results: scoped to `SignedDeclared` (blocks verifying under their *declared* version: `∃ sig, ops.verify (registry (producerForSlot n B.slot) B.keyIndex) B sig = true`).

b. **Conclusion**: Equal to Lean. The paper correctly observes that because `SignedDeclared B → KeyStealingSigned B`, the domain of declared-signed blocks is smaller, making hash injectivity on declared-signed blocks a strictly weaker assumption.

c. **Quantifiers, parameter ranges and definitions**: Exact match across `KeyStealingSigned`, `SignedDeclared`, and `Block.keyIndex`.

d. **Convenience assumptions**: Realistic domain restriction justified by the inclusion of `keyIndex` in the block header hash preimage.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C41

a. **Hypotheses**: Fully disclosed in text (Lean citation marker for Assumption 3). References `TimedExecution.id_inj` and `SignedHashInjective`.
Lean: `def SignedHashInjective (Signed : Block → Prop) (G : Block) : Prop := ∀ ⦃B B' : Block⦄, (B = G ∨ Signed B) → (B' = G ∨ Signed B') → B.id = B'.id → B = B'`.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None beyond those analyzed in C39–C40.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C42

a. **Hypotheses**: Fully disclosed in text (Assumption 4, Certificate grounding). The prose asserts that `GroundedCert` does not posit a valid chain behind the certificate as an axiom, but instead an inductive lemma reconstructs the prefix chain from the fold steps. In Lean, `groundedCert_history` (`MoltPetit/Model/Grounded.lean`) proves:
`theorem groundedCert_history (hn : 1 ≤ n) (h : GroundedCert n Signed G cl) : ∃ c : Chain, GroundedHistory n Signed G cl c`.

b. **Conclusion**: Equal to Lean (`groundedCert_history`).

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None. Prefix chain existence is constructively and inductively proved from the incremental fold checks, eliminating an ungrounded oracle axiom.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C43

a. **Hypotheses**: Fully disclosed in text (Lean citation marker for Assumption 4). References `GroundedCert`. In Lean, `GroundedCert n Signed G cl` is an inductive proposition with base case `genesis` and inductive step `fold`.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Standard inductive characterization of incremental certificate aggregation.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C44

a. **Hypotheses**: Fully disclosed in text (Assumption 5, Honest delivery — liveness only). Posits that for newly maturing windows $[u, u+n)$, honest producers were live and their blocks reached the current producer. Formally, `HonestBlocksCover bad record c u n := ∀ s, ¬bad s → u ≤ s → s < u + n → ∃ B : Block, B ∈ record s ∧ B ∈ c`.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match across window start $u$, window length $n$, honest slots $s$, and chain inclusion.

d. **Convenience assumptions**: Explicitly disclosed as a liveness-only assumption (combining node liveness and network synchrony). Safety theorems do not depend on it.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C45

a. **Hypotheses**: Fully disclosed in text (lines 664--666). Roadmap prose introducing Theorem~\ref{thm:lc} and pointing to the formal theorem `Molt.timed_light_client_safety`. The full operational hypotheses ($n \ge 1$, deployment genesis $G$, `TimedExecution n bad log G`, `ByzantineBounded n bad`, verification-time causality `hbridge`, two `GroundedCert` claims, validator predicates on suffixes, tip recency $R \le \mathrm{sTip.slot} + n$, and grounded histories) are detailed in Section~\ref{sec:assumptions} and Theorem~\ref{thm:lc}.

b. **Conclusion**: Equal to Lean. Accurately introduces the headline light-client safety theorem proved directly in the timed execution model.

c. **Quantifiers, parameter ranges and definitions**: Matches the formal development in `Molt.timed_light_client_safety`.

d. **Convenience assumptions**: None beyond the physical and cryptographic model assumptions analyzed under C48.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C46

a. **Hypotheses**: Meta-theoretical prose claim (line 679) asserting verification scope: *"Every result below is a Lean theorem, proved once against the model."* All subsequent formal results in Section~\ref{sec:results} (Theorems 1 and 2, rotation lemmas, and liveness) are formalized and verified in Lean 4 without custom axioms beyond standard Lean classical axioms (`Classical.choice`, `Quot.sound`, `propext`).

b. **Conclusion**: Equal to Lean. Every theorem stated in Section~\ref{sec:results} is verified by `lake build` and tracked in `Molt/Axioms.lean`.

c. **Quantifiers, parameter ranges and definitions**: N/A (prose statement).

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C47

a. **Hypotheses**: Fully disclosed in text (lines 679--685). Accurately defines the formal boundary: the light-client and timed theorems (Theorems~\ref{thm:lc} and~\ref{thm:forge}) are transported to implementations via the soundness bridge (Section~\ref{sec:impl}, `Rust/Soundness.lean`), whereas the key-rotation mode results (Section~\ref{sec:rotation}) and liveness (Section~\ref{sec:liveness}) are formally established at the model level.

b. **Conclusion**: Equal to Lean. Accurately delineates between model-level proofs and implementation-level Aeneas/Charon verified bridges.

c. **Quantifiers, parameter ranges and definitions**: Matches the architectural structure of the Lean formalization (`Molt/` and `MoltPetit/` vs `Rust/`).

d. **Convenience assumptions**: Transparently discloses that rotation-mode results and liveness do not yet possess an end-to-end Rust implementation bridge.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C48

a. **Hypotheses**: Fully disclosed in Theorem~\ref{thm:lc} (lines 693--719). Every Lean hypothesis of `@Molt.timed_light_client_safety` is explicitly stated in the paper text:
1. Parameters: $n \ge 1$ (`1 ≤ n`) and genesis block $G$;
2. `TimedExecution n bad log G` with its five constituent conditions explicitly stated: signing at real slots, bad slots signing residue class blocks (`key_match`), honest slots signing only their own current block (`honest_stamp`), honest single-signing (`honest_once`), parent availability before signing (`chain_order`), and collision resistance (`id_inj`);
3. Fault budget: `ByzantineBounded n bad`;
4. Verifier causality / unforgeability: verifier at real slot $R$, accepted signatures produced at $r \le R$ (`hbridge`);
5. Two presentations: grounded certificate claims `GroundedCert n Signed G cl` and `cl'`;
6. Suffix validator checks: linkage to certificate tip (`hLink`/`hLink'`), internal block linkage (`hLinks`/`hLinks'`), maturing window quorum density (`hDense`/`hDense'`), and valid signatures (`hSigned`/`hSigned'`);
7. Real-time tip recency: $R \le \mathrm{sTip.slot} + n$ and $R \le \mathrm{sTip'.slot} + n$;
8. Attested histories: `GroundedHistory n Signed G cl c` and `GroundedHistory n Signed G cl' c'`;
9. Depth bounds: $h + n < (c ++ s_1 :: srest).\mathrm{length}$ and $h + n < (c' ++ s_1' :: srest').\mathrm{length}$.

b. **Conclusion**: Equal to Lean. Lean proves `blockAt? (c ++ s₁ :: srest) h = blockAt? (c' ++ s₁' :: srest') h`. The paper correctly states that the two full chains agree at every height $h$ with $h + n$ below both full lengths, or equivalently at least $n$ blocks below the lower tip.

c. **Quantifiers, parameter ranges and definitions**: Exact match. Quantifiers across executions, presentation suffixes, and depth bounds match Lean.

d. **Convenience assumptions**: The theorem relies on `TimedExecution` (unifying `chain_order`, `key_match`, and honest slot discipline) and `hbridge` (bounding accepted signatures to real slots $\le R$). The text thoroughly justifies these as consequences of EUF-CMA signature unforgeability, hash collision resistance, and verifier physical arrival.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C49

a. **Hypotheses**: Fully disclosed in text (lines 725--729). Corresponds to `@MoltPetit.Model.late_tail_short`: $n \ge 1$, `TimedExecution n bad log G`, `ByzantineBounded n bad`, valid chain `ValidChain n c`, genesis at root (`blockAt? c 0 = some G`), block availability at verifier slot $R$, tip recency $R \le \mathrm{tip.slot} + n$, non-empty index $1 \le \ell < c.\mathrm{length}$, and late signature on block $L$ at index $\ell$ ($L.\mathrm{slot} < \min \{r \mid L \in \log r\}$).

b. **Conclusion**: Equal to Lean. Lean proves `c.length - ℓ ≤ maxByzantine n ∧ tip.slot + 1 < L.slot + n`. The prose captures both conjuncts: *"such blocks form a tail of at most $\fmax$ blocks inside one window"*.

c. **Quantifiers, parameter ranges and definitions**: Exact match across parameter bounds ($n \ge 1$, index $\ell$, fault budget $\fmax$).

d. **Convenience assumptions**: None; proved inductively from `TimedExecution` and cumulative window density.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C50

a. **Hypotheses**: Fully disclosed in prose comparison (lines 734--737). The paper explicitly distinguishes the untimed model theorem `Molt.light_client_safety` from the timed headline result: it requires the unreduced cryptographic premise `SigUnforgeableRecent n bad Signed signed now Δ` and `SignedHashInjective Signed G`, along with `FaultBounded n bad`, certificate groundings, and suffix validator checks.

b. **Conclusion**: Equal to Lean. The prose notes that this untimed theorem reaches the same agreement conclusion but *"keeps the exposure hypothesis"*. In Lean, the conclusion is equality $B = B'$ between suffix blocks at corresponding heights $i, i'$ appearing in the presented suffixes (`s₁ :: srest` and `s₁' :: srest'`).

c. **Quantifiers, parameter ranges and definitions**: Exact match across slot staleness $\Delta$ and clock $now$.

d. **Convenience assumptions**: The text explicitly acknowledges that `SigUnforgeableRecent` is an unreduced axiomatic residue in the untimed model, transparently explaining why the timed model is required.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C51

a. **Hypotheses**: Disclosed in text (lines 743--749). Describes the formal structure `Molt.TimedExecution` / `MoltPetit.Model.TimedExecution` over parameters $n$, `bad : ByzantineSlots`, `log : TimedLog`, and genesis $G$.

b. **Conclusion**: Equal to Lean. Accurately explains the semantics of fields `key_match`, `honest_stamp`, and `honest_once`: honest slots sign only their own current block at most once; bad slots sign arbitrarily many blocks under the producer key stamped with any slot in the residue class.

c. **Quantifiers, parameter ranges and definitions**: Exact match with Lean structure definition.

d. **Convenience assumptions**: The adversary model permits full equivocation and arbitrary past/future timestamps within the residue class at Byzantine slots.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C52

a. **Hypotheses**: Disclosed in text (lines 749--754) and Section~\ref{sec:protocol}. Corresponds to field `MoltPetit.Model.TimedExecution.chain_order`: for any $B \in \log r$ with parent pointer $B.\mathrm{prev} = \mathrm{some}\ i$, there exists parent block $P$ such that $P.\mathrm{id} = i$ and `AvailableAt log G P r`.

b. **Conclusion**: Equal to Lean. Formalizes that parent blocks must already have been available at or before real slot $r$.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Justified in text by reducing parent prediction to an EUF-CMA forgery on the parent's signature contained in the parent's ID preimage.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C53

a. **Hypotheses**: Fully disclosed in Theorem~\ref{thm:forge} (lines 758--779). Corresponds to `@Molt.forged_time_bound` and `@Molt.forged_chain_time_bound`:
- Timed execution: `TimedExecution n bad log G`;
- Fault budget: `FaultBounded n bad` / `ByzantineBounded n bad`;
- Valid chain: `ValidChain n c`, genesis `G.prev = none`;
- Real-time availability: `∀ B ∈ c, AvailableAt log G B rNow`;
- Suffix pivot $F$ at index $k_0 \ge 1$, first signed at real slot $r_0$;
- Coercion/forgery: all chain blocks past $F$'s slot signed only at bad real slots (`∀ B ∈ c, F.slot < B.slot → ∀ r, B ∈ log r → bad r`);
- Non-degeneracy conditions explicitly stated in text: $n \ge 2$, $F$ not the first block ($1 \le k_0$).

b. **Conclusion**: Equal to Lean. Theorem text gives the exact inequality $\quorum \cdot \lfloor \frac{\mathit{tip.slot} - F.\mathit{slot}}{n} \rfloor \le \fmax \cdot (\lfloor \frac{r_{\mathrm{now}} - r_0}{n} \rfloor + 1)$, and accurately cites the from-genesis corollary `forged_chain_time_bound`: $\quorum \cdot \lfloor \frac{\mathit{tip.slot} + 1}{n} \rfloor \le \fmax \cdot (\lfloor \frac{R}{n} \rfloor + 1) + 1$.

c. **Quantifiers, parameter ranges and definitions**: Exact match, including the floor division arithmetic and $+1$ discretization offsets.

d. **Convenience assumptions**: The text explicitly notes that a forged span under one window makes the bound trivially true, accurately stating the scope of the guarantee.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C54

a. **Hypotheses**: Disclosed in text (lines 782--788). Explains the proof mechanism of the rate-limiting lemma `one_real_slot_one_block` (`MoltPetit/Model/Timed.lean`): $2 \le n$, `TimedExecution`, `ValidChain`, block availability, and the hypothesis that two distinct chain blocks are first-signed at the same real slot $r$.

b. **Conclusion**: Equal to Lean. Lean proves `False` from the co-occurrence of two first-signings at real slot $r$. The prose accurately describes the proof: producer key matching implies slot stamps differ by at least $n$, matured window density forces an intervening block of a different seat, and `chain_order` pins that block's first signing to $r$, contradicting the single-seat key constraint.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; mechanically derived from `TimedExecution.chain_order` and window density.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C55

a. **Hypotheses**: High-level synthesis claim (lines 795--798). Connects the real-time rate bound of Theorem~\ref{thm:forge} to the light-client safety guarantee of Theorem~\ref{thm:lc}. Hypotheses are those of Theorem~\ref{thm:lc}.

b. **Conclusion**: Equal to Lean. Accurately summarizes that within staleness $n$, an adversary bound by Byzantine fault budget cannot forge an alternative valid chain reaching depth $n$ below the tip.

c. **Quantifiers, parameter ranges and definitions**: Matches the formal connection established between Theorem~\ref{thm:forge} and Theorem~\ref{thm:lc}.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---
### C56

a. **Hypotheses**: Descriptive prose (lines 807--810) introducing the protocol's key rotation components: the `Block.keyIndex : Nat` record field and the `keyMonoOk : Nat → Chain → Bool` monotonicity predicate (`validChainK n c := validChain n c && keyMonoOk n c`). Stated in Section~\ref{sec:protocol} and reaffirmed here.

b. **Conclusion**: Equal to Lean. Accurately describes that block version indexing (`keyIndex`) and non-decreasing versions per producer seat (`keyMonoOk`) are integral to full chain validity (`validChainK`, verified in `Rust/Bridge.lean` and `Molt/Rotation.lean`).

c. **Quantifiers, parameter ranges and definitions**: Exact match with Lean's `MoltPetit.Model.Block.keyIndex` and `Molt.keyMonoOk`.

d. **Convenience assumptions**: None; standard consensus-ordered version progression.

e. **Do the Lean definitions mean what the prose says?** Yes; scanning along a chain from genesis, an earlier block by producer $i$ cannot carry a strictly higher `keyIndex` than a later block by the same producer.

Verdict: FAITHFUL

---

### C57

a. **Hypotheses**: Definition/prose description of the key-stealing corruption predicate `badKeyrot` / `badKeyrotOn` (lines 834--838).

b. **Conclusion**: Equal to Lean. Lean defines `badKeyrot n Δconf rented Stolen c₀ s := rented s ∨ ∃ j, inForce n Δconf c₀ (producer n s) s ≤ j ∧ Stolen (producer n s) j`. The prose states that slot $s$ counts bad if rented or if some version at-or-above the one in force for its producer is stolen.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The existential quantification $\exists j \ge \mathrm{inForce}$ exactly mirrors the prose condition.

d. **Convenience assumptions**: None; accurately formalizes that once an emergency rotation reaches confirmed depth $\Delta_{\mathrm{conf}}$, `inForce` rises above the compromised version $j$, causing the disjunct to become false and the producer's slots to "heal".

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C58

a. **Hypotheses**: Prose specification of the scoping domains for hash injectivity (Assumption~\ref{ass:hash}) across rotation modes (lines 844--848).

b. **Conclusion**: Equal to Lean. Lean's `KeyStealingSigned n ops registry B` requires that $B$ verifies under its producer's registered key at *some* version $j$ (`∃ sig j, ops.verify ... j B sig = true`), while `SignedDeclared n ops registry B` requires verification under its *declared* version (`∃ sig, ops.verify ... B.keyIndex B sig = true`).

c. **Quantifiers, parameter ranges and definitions**: Exact match between paper prose and Lean formalizations (`KeyStealingSigned` for Mode 1 chain rule; `SignedDeclared` for Modes 2--3 and certified Mode 1).

d. **Convenience assumptions**: Restricting collision resistance to the domain of validly signed candidate blocks is standard and explicitly disclosed in Assumption~\ref{ass:hash}.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C59

a. **Hypotheses**: Context and motivation for Assumption~\ref{ass:rotation-honest} (lines 851--851). Accurately explains why unforgeability under key rotation (`KeyStealingEUFCMA` / `SchedCoreUnforgeable`) is stated directly per key version rather than derived from `TimedExecution`.

b. **Conclusion**: Equal to Lean. The prose cites two machine-checked theorems, `badSched_single_key_safe_not_enough` and `badKeyrot_single_key_safe_not_enough`, which prove that an unrented slot where a specific key version is unstolen can still be corrupted because another eligible version at that slot is compromised.

c. **Quantifiers, parameter ranges and definitions**: Exact match with the witness constructions in `MoltPetit/Model/KeyStealingTimedScope.lean` and `Molt/KeyStealingTimedScope.lean`.

d. **Convenience assumptions**: Unusually transparent disclosure: rather than sweeping the non-derivability under the rug, the authors proved explicit counterexample theorems in Lean to justify stating Assumption~\ref{ass:rotation-honest} directly.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C60

a. **Hypotheses**: Recovery of baseline security when no keys are stolen (`Stolen = fun _ _ => False`, lines 856--859).

b. **Conclusion**: Equal to Lean. Lean theorems `@Molt.badKeyrot_lossOnly` and `@Molt.badSched_lossOnly` prove that when the stolen key set is empty, `badKeyrot n Δconf rented (fun _ _ => False) c₀ = rented` and `badSched n schedule rented (fun _ _ => False) = rented`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; directly proves that lost (destroyed) keys that are not exfiltrated introduce zero additional corruption overhead.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C61

a. **Hypotheses**: Definition and mechanism of Mode 1 reactive pinning (lines 865--869). Discloses `inForce n Δconf c i s` as the floor over `confirmedPrefix Δconf c s`, and notes that while the Lean formalization accepts any $\Delta_{\mathrm{conf}} \ge n$, the protocol instantiates $\Delta_{\mathrm{conf}} = n$.

b. **Conclusion**: Equal to Lean. Accurately describes `validChainK'` checking `inForce n Δconf c (producer n b.slot) b.slot ≤ b.keyIndex` across all blocks $b$.

c. **Quantifiers, parameter ranges and definitions**: Exact match with `MoltPetit.Model.inForce` and `MoltPetit.Model.validSignedChainK'`.

d. **Convenience assumptions**: None; pure deterministic calculation over the validated chain's confirmed prefix.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C62

a. **Hypotheses**: Theorem~\ref{thm:refresh} (lines 894--911). Every hypothesis of `@Molt.sync_rule_timed` and `@Molt.sync_rule_mem_timed` is explicitly stated in the paper's itemized list:
- Parameter range: $n \ge 1$, deployment genesis $G$;
- Unforgeability (`hEUF`): `KeyStealingEUFCMA n n ops registry rented (stolenOf stolenAt) honestSigned now Δ`;
- Hash injectivity (`hHash`): `SignedHashInjective (KeyStealingSigned n ops registry) G`;
- Prior verified chain (`hVPrev`): `validSignedChainK' n n ops registry scPrev = true`;
- Prior tip recency: $t \le \mathit{tipPrev.slot} + n$;
- Anchor definition (`hAnchor`): block $A$ at index `length - 1 - n` in `scPrev` (requires `n < length`);
- Cadence (`hCadence`): $\mathit{now} \le t + n$;
- Anchor inclusion (`hA`, `hA'`): $A \in \mathit{sc}$ and $A \in \mathit{sc}'$;
- Rent bound (`hRent`): for every window $u$ with $\mathit{now} < u + 5n$, `(badSlotsIn rented u n).card ≤ Rrent`;
- Theft census (`hTheft`): for every window $u$ with $\mathit{now} < u + 5n$, `(recentTheftProducersK n d stolenAt u).card ≤ T`;
- Fault budget (`hRT`): $\mathit{Rrent} + T \le \mathrm{faultBudget}(n)$;
- Reaction delay (`hReacts`): `Reacts n n d (stripSigs sc) stolenAt`;
- Current validity (`hVal`, `hVal'`): `validSignedChainK' n n ops registry sc = true` and for $\mathit{sc}'$;
- Current tip recency (`hRecent`, `hRecent'`): $\mathit{now} \le \mathit{sTip.slot} + \Delta$, $\mathit{now} \le \mathit{sTip'.slot} + \Delta$;
- Current length (`hLong`): $n < \mathrm{length}(\mathit{sc})$ and $n < \mathrm{length}(\mathit{sc}')$;
- Height relation: $\mathit{sTip.height} = \mathit{sTip'.height}$ (for `sync_rule_timed`) or $\mathit{sTip.height} \le \mathit{sTip'.height}$ (for `sync_rule_mem_timed`).

b. **Conclusion**: Equal to Lean. Theorem text states both the equal-height agreement ($B = B'$) and the unequal-height membership form ($\exists i', i' + n < \mathrm{length}(\mathit{sc}') \wedge \mathrm{blockAt?}\ \mathit{sc}'\ i' = \mathrm{some}\ B$).

c. **Quantifiers, parameter ranges and definitions**: Exact match, including the trailing $5n$-slot scope ($\mathit{now} < u + 5n$) and the $n$-slot sync cadence ($\mathit{now} \le t + n$).

d. **Convenience assumptions**: The paper explicitly discloses that `Reacts` is evaluated on the chain being validated ($\mathit{sc}$), acknowledging in line 915 that a version quantified only over an honest chain remains an open problem.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C63

a. **Hypotheses**: Disclosed in text (lines 913--915). Cites `Molt.sync_rule`, `Molt.sync_rule_mem`, and `MoltPetit.Model.budget_of_reaction`.

b. **Conclusion**: Equal to Lean. `sync_rule` and `sync_rule_mem` consume an untimed windowed census budget over `badKeyrot` on the reference chain; `budget_of_reaction` formally derives that census budget from `Reacts`, the windowed rent bound, and `recentTheftProducersK`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: The prose explicitly notes the operational meaning of `Reacts` and that it is evaluated on the validated chain rather than an external honest chain.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C64

a. **Hypotheses**: Lean theorem `@Molt.deep_block_span` requires $1 \le n$, `ValidChain n c`, and two blocks $A, D$ at chain indices $m$ and $m+n$ respectively (lines 930--933).

b. **Conclusion**: Equal to Lean. Lean proves $D.\mathit{slot} < A.\mathit{slot} + 2n$. The paper accurately states that the anchor (at depth $n$ below the tip) sits strictly fewer than $2n$ slots below that tip.

c. **Quantifiers, parameter ranges and definitions**: Exact match; explains that two full windows in the gap would require $2\quorum > n$ blocks, which contradicts having only $n$ blocks between $m$ and $m+n$.

d. **Convenience assumptions**: None; combinatorial consequence of window density.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C65

a. **Hypotheses**: Specialization of anchor-based safety to the genesis anchor (lines 940--947), corresponding to `@Molt.client_refresh_rule`.

b. **Conclusion**: Equal to Lean. Lean's `client_refresh_rule` takes an anchor $A$ with $\mathit{now} \le A.\mathit{slot} + H$ and budget premise $orall u, \mathit{now} < u + n + H 	o \dots \le \mathrm{faultBudget}(n)$. When $A := G$ (genesis at slot 0) and $H := \mathit{now}$, the horizon condition holds trivially for all $u \ge 0$, recovering the lifetime budget from genesis.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL


---

### C66

a. **Hypotheses**: Disclosed in text (lines 980--994). The paper explicitly specifies that certificates must attest claim and floor together (`GroundedCertK`), the client holds an anchor block $A$ present in both suffixes, and the corruption budget is required over every history the certificate could attest (`AttestedHistoryK`) for windows ending after the anchor ($A.\mathit{slot} + 1 \le u + n$).

b. **Conclusion**: Equal to Lean. Lean concludes that blocks at matching chain heights $n$ deep behind suffix tips agree ($B = B'$); the prose states "agree $n$ deep".

c. **Quantifiers, parameter ranges and definitions**: Exact match ($1 \le n \le \Delta\mathrm{conf}$, heights match, both suffixes have length $> n$).

d. **Convenience assumptions**: The universal quantification over all candidate histories in `AttestedHistoryK` is the exact condition needed for certificate grounding without storing full chain history, and is explicitly stated in the text.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C67

a. **Hypotheses**: Disclosed in text (lines 996--1000). Requires $0 < n$ (or $1 \le n \le \Delta\mathrm{conf}$), `Reacts n Δconf d c₀ stolenAt`, rent bounded by $R_{\mathrm{rent}}$, recent theft producers bounded by $T$ via `recentTheftProducersK`, and $R_{\mathrm{rent}} + T \le \mathrm{faultBudget}(n)$.

b. **Conclusion**: Equal to Lean. Derives the trailing bad-slot bound for `badKeyrotOn` from the reaction delay and theft census, and proves suffix agreement under the timed client rules (`sync_rule_timed`, `max_sync_period_timed`).

c. **Quantifiers, parameter ranges and definitions**: Exact match. The text explicitly notes that the census is per-window with a reaction delay $d$, but under `recentTheftProducersK` (which only checks $u < r + d$) any theft at $r > u$ charges window $u$ as well.

d. **Convenience assumptions**: `Reacts` is an assumed operational hypothesis stating that the confirmed floor moves past the stolen key version within $d$ slots of theft; the text explicitly highlights that this is asserted rather than cryptographically derived ("asserted, like \emph{not-before} in mode~2, not derived").

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C68

a. **Hypotheses**: Disclosed in text (lines 1002--1011). Lean requires $1 \le n \le \Delta\mathrm{conf}$, standard EUF-CMA and hash injectivity, valid preceding signed chain, anchor $A$ at depth $n$ below previous tip, cadence condition $\mathit{now} \le t + F$, anchor $A$ in both current chains, and the trailing corruption budget $\forall u, \mathit{now} < u + F + 4n \to (\mathrm{badSlotsIn}\dots u\; n).\mathrm{card} \le \mathrm{faultBudget}(n)$.

b. **Conclusion**: Equal to Lean. Suffix blocks at depth $n$ below tips agree ($B = B'$).

c. **Quantifiers, parameter ranges and definitions**: Exact match. The window start condition $\mathit{now} < u + F + 4n$ corresponds directly to windows starting in the trailing $F + 4n$ slots or later.

d. **Convenience assumptions**: None; standard cadence and anchor setup.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C69

a. **Hypotheses**: Disclosed in text (lines 1012--1020). Lean states that if a set $P$ of producers each has an unretired stolen version at or after window $u$, then $|P| \le (\mathrm{badSlotsIn}\dots u\; n).\mathrm{card}$ (`census_accumulates`, `census_accumulates_later_thefts`), and if $|P| > \mathrm{faultBudget}(n)$, the precondition is violated (`no_budget_beyond`), using monotonicity of `inForce` (`inForce_mono`).

b. **Conclusion**: Equal to Lean. The prose is careful to describe this as a downward precondition barrier ("the safety theorem's precondition is not merely weaker --- nothing can meet it, so the theorem promises nothing") rather than claiming a formal end-to-end forged execution is certified in Lean, which lines 1030--1031 explicitly state is future work.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes.

Verdict: FAITHFUL

---

### C70

a. **Hypotheses**: Stated as operational definitions and hypotheses in prose (lines 1031--1035).

b. **Conclusion**: N/A (definitions of `Reacts` and `NoTheftBackdating`).

c. **Quantifiers, parameter ranges and definitions**: Flawed. Lean defines `NoTheftBackdating` as:
   `∀ i j r s, stolenAt i j r → inForce n Δconf c₀ i s ≤ j → r ≤ s`.

d. **Convenience assumptions**: Unrealistic and contradictory with chains starting at floor 0. `NoTheftBackdating` universally quantifies over all slots $s$. For any standard chain starting from genesis, `inForce n Δconf c₀ i 0 = 0 ≤ j` holds for any key version $j \ge 0$. Substituting $s = 0$ yields $r \le 0$. Consequently, `NoTheftBackdating` forces every theft of an initial active key to occur at slot $0$, making the hypothesis impossible to satisfy for thefts occurring after genesis ($r > 0$) unless keys were pre-retired before slot 0.

e. **Do the Lean definitions mean what the prose says?** No. The prose describes no-backdating as "a stolen version cannot be used to expose a slot that predates its theft", intending to restrict adversarial signatures/blocks from backdating slots. But the Lean predicate quantifies over all chain slots $s$ where key $j$ has not yet been retired by the confirmed floor (`inForce ... s ≤ j`), asserting that *every* such slot must be after the theft ($r \le s$). Because confirmed floors start at 0, this makes `NoTheftBackdating` jointly contradictory with `hFloor0` for non-zero theft times (as admitted in the codebase docstring for `paced_separation_witnessed`).

Severity: MAJOR
Fix: Redefine `NoTheftBackdating` to constrain only slots $s$ where an adversarial block signing under key $j$ is actually placed, avoiding universal quantification over unrotated historical slots.

---

### C71

a. **Hypotheses**: Disclosed in text (lines 1035--1038; requires `Reacts` and `NoTheftBackdating`).

b. **Conclusion**: Equal to Lean. Lean proves $r \le s \wedge s < r + d$ under `stolenAt i j r` and `inForce n Δconf c₀ i s ≤ j`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Inherits the convenience flaw of `NoTheftBackdating` from C70: because `inForce ... s ≤ j` holds at $s = 0$ for initial keys, any theft at $r > 0$ yields $r \le 0 \wedge 0 < r + d$, forcing $r = 0$. The exposure window $[r, r+d)$ only behaves as intended under chains that pre-rotate keys prior to slot 0.

e. **Do the Lean definitions mean what the prose says?** In isolation the theorem proves $s \in [r, r+d)$, but only by directly inheriting the defective definition of `NoTheftBackdating` where $r \le s$ is assumed for all unretired slots $s$.

Severity: MAJOR
Fix: Redefine `NoTheftBackdating` so `theft_exposure_window` applies to slots actually signed by the adversary rather than all historical slots with unadvanced floors.

---

### C72

a. **Hypotheses**: Disclosed in text (lines 1038--1042). `paced_tight_census_bound_all_F` requires $n + d \le P$, establishing that for paced thefts ($r = j \cdot P$) the tight census `recentTheftProducersTight` is $\le 1$ for all windows $u$ independent of $F$. `max_sync_period_tight` composes this into `max_sync_period`.

b. **Conclusion**: Equal to Lean. Lean proves the tight census is $\le 1$ for all windows satisfying $\mathit{now} < u + F + 4n$.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: `max_sync_period_tight` assumes `NoTheftBackdating` and `Reacts`. While `paced_tight_census_bound_all_F` itself does not assume `NoTheftBackdating`, the composition `max_sync_period_tight` requires both hypotheses on the chain `stripSigs sc`. As proved in `pacedStolenAt_safe_under_tight_unsafe_under_untimed` and `paced_budget_holds_under_timing`, these hypotheses cannot be jointly satisfied with initial zero floors `hFloor0` for non-zero theft slots.

e. **Do the Lean definitions mean what the prose says?** Yes for the combinatorial counting theorem `paced_tight_census_bound_all_F`; but the composed end-to-end guarantee `max_sync_period_tight` is bottlenecked by `NoTheftBackdating`.

Severity: MINOR
Fix: Note in the text that `paced_tight_census_bound_all_F` is an unconditioned combinatorial bound on the tight census filter, while the composed theorem `max_sync_period_tight` inherits the operational assumption `NoTheftBackdating`.
---
### C73

a. **Hypotheses**: Disclosed in text (lines 1047--1050; expanded in lines 1055--1090). For `client_refresh_rule`, takes freshness hypothesis `now ≤ A.slot + H` and corruption budget on windows satisfying `now < u + n + H`. `stay_recent_client_safe` derives $H = 4n - 1$ and trailing window bound $5n$ from previous chain validity (`hVPrev`), previous tip recency (`hRecPrev`: $t \le \mathit{tipPrev}.\mathit{slot} + n$), sync cadence (`hCadence`: $\mathit{now} \le t + n$), and slot spacing (`deep_block_span`).

b. **Conclusion**: Equal to Lean. Lean proves $B = B'$ (agreement on the block $n$ below each tip).

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: The derivation of the $4n-1$ age bound in `stay_recent_client_safe` relies on active sync cadence ($\mathit{now} \le t + n$) and bounded slot gaps between chain blocks (`deep_block_span`). These are realistic operational requirements for active clients and are explicitly disclosed.

e. **Do the Lean definitions mean what the prose says?** Yes. `client_refresh_rule` parameterizes the age bound by $H$, and `stay_recent_client_safe` formally derives the $4n-1$ age bound and $5n$ trailing budget window from the client's sync cadence.

Verdict: FAITHFUL

---

### C74

a. **Hypotheses**: Disclosed in text (lines 1076--1098). Lean hypotheses for `sync_rule_timed` and `sync_rule_mem_timed` require `KeyStealingEUFCMA`, `SignedHashInjective`, tip recency ($\mathit{now} \le \mathit{sTip}.\mathit{slot} + \Delta$), chain lengths $> n$, validity under `validSignedChainK'`, anchor containment ($A \in \mathit{stripSigs}(sc) \wedge A \in \mathit{stripSigs}(sc')$), previous sync recency and cadence ($\mathit{now} \le t + n$), rotation reaction (`Reacts n n d (stripSigs sc) stolenAt`), and budget condition $R_{\mathit{rent}} + T \le \mathit{faultBudget}(n)$ with bounded rented slots and bounded recent theft producers in trailing $5n$ windows.

b. **Conclusion**: Equal to Lean. `sync_rule_timed` proves equal-height agreement $B = B'$; `sync_rule_mem_timed` proves that the lower tip's $n$-deep block is an ancestor block in the taller chain at depth $\ge n$; and `same_block_same_prefix` proves that sharing this block forces identity on the entire confirmed prefix.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Unlike the tight-census formulations, `sync_rule_timed` uses `budget_of_reaction` via `recentTheftProducersK`, which does not assume `NoTheftBackdating`. The `Reacts` hypothesis requires honest producers to rotate keys within $d$ slots on suspicion of compromise, which is fully disclosed and justified as hardware-alarm-assisted rotation in the deployment scenario.

e. **Do the Lean definitions mean what the prose says?** Yes. Lean's `sync_rule_timed` and `sync_rule_mem_timed` provide the machine-checked safety guarantees, and `same_block_same_prefix` propagates agreement down the ancestor chain.

Verdict: FAITHFUL

---

### C75

a. **Hypotheses**: Disclosed in text (lines 1098--1106). In `sync_induction_full_chain`, hypotheses include the sequence of sync times with cadence $\mathit{now}(k+1) \le \mathit{now}(k) + n$, EUF-CMA, hash injectivity, valid accepted chains $c_k$ with anchors $a_k$ accepted on $c_{k+1}$, recency, trailing budget, and reference chain sequence $R_k$ satisfying validity, recency, length $> n$, prefix-growth (`stripSigs (R k) <+: stripSigs (R (k + 1))`), base case ($a_0 \in \mathit{stripSigs}(R_0)$), and height comparison `(tip k).height ≤ (rTip k).height` (`hRLe`).

b. **Conclusion**: Equal to Lean. Lean proves `∀ k, a k ∈ stripSigs (R k)`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: The premise `hRLe` (`∀ k, (tip k).height ≤ (rTip k).height`) is a strong external assumption encoding that the reference chain is never outgrown by an accepted chain. This assumption is necessary because `sync_rule_mem` requires `sTip.height ≤ sTip'.height` to guarantee ancestor containment. The paper explicitly admits that `hRLe` is an assumed hypothesis rather than a proved conclusion, and that the informal density argument justifying it is not machine-checked.

e. **Do the Lean definitions mean what the prose says?** Yes. The induction formally establishes that every client anchor belongs to the reference chain at every sync step under the stated hypotheses.

Verdict: FAITHFUL

---

### C76

a. **Hypotheses**: N/A (prose meta-commentary on formalization scope).

b. **Conclusion**: N/A.

c. **Quantifiers, parameter ranges and definitions**: N/A.

d. **Convenience assumptions**: None. The text explicitly disclaims machine checking for the density argument and transparently states that the height comparison `hRLe` is an assumed hypothesis of `sync_induction_full_chain` rather than a derived result.

e. **Do the Lean definitions mean what the prose says?** Yes. The paper's prose accurately reflects the formal structure of `sync_induction_full_chain` and its dependence on `hRLe`.

Verdict: FAITHFUL

---

### C77

a. **Hypotheses**: Disclosed in text (lines 1106--1109; referring to `client_refresh_rule`). The theorem requires an anchor $A$ common to both chains with freshness $\mathit{now} \le A.\mathit{slot} + H$ and corruption budget on trailing windows $\mathit{now} < u + n + H$, which at $H \approx 4n$ gives the $5n$-slot budget window.

b. **Conclusion**: Equal to Lean. Both chains agreeing on the join checkpoint $A$ within freshness horizon $H$ forces agreement on the $n$-deep block.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Assumes an initial trusted checkpoint $A \in sc \wedge A \in sc'$ no older than $\approx 4n$ slots. In `sync_induction_full_chain`, this base case (`hBase: a 0 ∈ stripSigs (R 0)`) is taken as raw data; the paper explicitly acknowledges this as the operational model's initial trust event outside the formal proof.

e. **Do the Lean definitions mean what the prose says?** Yes. `client_refresh_rule` directly consumes the anchor age bound $H$ and budget guard $u + n + H$.

Verdict: FAITHFUL

---

### C78

a. **Hypotheses**: N/A (definition of validator).

b. **Conclusion**: N/A.

c. **Quantifiers, parameter ranges and definitions**: Exact match. Lean defines `schedPin schedule c := c.all (fun b => decide (schedule b.slot ≤ b.keyIndex))`, which is checked alongside signatures and validity in `validSignedChainSched`.

d. **Convenience assumptions**: None; syntactic check enforcing that block key indices satisfy the slot schedule.

e. **Do the Lean definitions mean what the prose says?** Yes. Lean's `validSignedChainSched` exactly enforces $\mathit{gen}(\mathit{slot}) \le \mathit{keyIndex}$.

Verdict: FAITHFUL
---

### C79

a. **Hypotheses**: Fully disclosed in text (lines 1124--1147). Explicitly enumerates: `1 ≤ n`, `validSignedChainSched` on both chains, `SchedUnforgeable` (recency-scoped with $\mathit{now}, \Delta$), `SignedHashInjective (SignedDeclared n ops registry) G`, corruption budget `ByzantineBoundedFrom H n (badSched ...)`, horizon side conditions $H + n \le \mathit{tip}.\mathit{slot} + 1$ for both tips, recency $\mathit{now} \le \mathit{tip}.\mathit{slot} + \Delta$ for both tips, sufficient length $n < \mathit{length}$ (`hLong`), and the tip-height comparison (`hTipHeight` for equal heights, `hLe` for unequal heights).

b. **Conclusion**: Equal to Lean. Lean proves `B = B'` on the block $n$ below each tip for equal heights (`sched_recent_tip_ancestor_agreement_horizon`), and that the lower chain's $n$-deep block is an ancestor block at least $n$ deep in the taller chain (`sched_recent_tip_ancestor_mem_horizon`).

c. **Quantifiers, parameter ranges and definitions**: Exact match. The text also correctly notes that genesis agreement is a consequence (`sched_recent_genesis_agreement_horizon`) rather than an assumption, and that `scheduled_client_safety` follows as a corollary for any $H$.

d. **Convenience assumptions**: The corruption budget `ByzantineBoundedFrom H n` applies to windows starting at or after $H$ without constraining pre-$H$ corruption, reflecting the scheduled key retirement model. No hidden convenience assumptions.

e. **Do the Lean definitions mean what the prose says?** Yes. Scheduled validator validity and the unforgeability model precisely realize the offline-client safety theorem.

Verdict: FAITHFUL

---

### C80

a. **Hypotheses**: N/A (prose discussion of operational model assumptions not consumed by theorems).

b. **Conclusion**: N/A.

c. **Quantifiers, parameter ranges and definitions**: Exact match. Lean defines `NoPrematureTheft R stolenAt := ∀ i j r, stolenAt i j r → j * R ≤ r` (in `KeyStealingScheduleTimed.lean:96`), formalizing that key generation $j$ cannot be stolen before its derivation slot $j \cdot R$.

d. **Convenience assumptions**: None; the text explicitly emphasizes that `NoPrematureTheft` and cold-root custody are named operational duties that the core scheduled safety theorems do *not* consume.

e. **Do the Lean definitions mean what the prose says?** Yes. Lean's `NoPrematureTheft` precisely encodes the not-before derivation condition.

Verdict: FAITHFUL

---

### C81

a. **Hypotheses**: Disclosed in text (lines 1163--1167). Lean's `sched_oldkey_fork_stale` requires `validSignedChainSched n schedule ops registry sc = true`, `∀ s, schedule s ≤ J → s + Δ < now` (era ended more than $\Delta$ ago), tip block `(stripSigs sc).getLast? = some t`, and declared generation `t.keyIndex ≤ J`.

b. **Conclusion**: Equal to Lean. Lean proves `¬ now ≤ t.slot + Δ` (the tip fails the client recency check).

c. **Quantifiers, parameter ranges and definitions**: Exact match ($\Delta = n$ in standard operational parameters).

d. **Convenience assumptions**: None; the result follows purely by arithmetic from the validator's pin rule (`rotated_key_dead_sched`) without consuming corruption budget or honest-majority premises.

e. **Do the Lean definitions mean what the prose says?** Yes. An accepted tip declaring a retired generation cannot satisfy recency.

Verdict: FAITHFUL

---

### C82

a. **Hypotheses**: Disclosed in text (lines 1167--1172). Refers to the inductive certificate derivation `GroundedCertSched` and suffix agreement `sched_recent_certified_suffix_agreement`.

b. **Conclusion**: Equal to Lean. Confirms that certificate claims require no floor snapshot and that safety carries over by folding the pin check into the inductive certificate claim.

c. **Quantifiers, parameter ranges and definitions**: Exact match. `GroundedCertSched` maintains the standard `CertClaim` structure (`tipId`, `tipSlot`, `tipHeight`, `tail`) and verifies `schedule b.slot ≤ b.keyIndex` at each step.

d. **Convenience assumptions**: Standard certificate grounding assumptions matching the core certificate architecture.

e. **Do the Lean definitions mean what the prose says?** Yes. Pinning is verified per-block from each block's own slot without modifying the claim signature.

Verdict: FAITHFUL

---

### C83

a. **Hypotheses**: Disclosed in text (lines 1192--1195). Lean theorem `same_block_same_prefix` requires `IdInjective record`, `ChainInRecord record c`, `ChainInRecord record c'`, `ParentLinked c`, `ParentLinked c'`, and a shared block `blockAt? c m = some B` and `blockAt? c' m = some B`.

b. **Conclusion**: Equal to Lean. For all $k \le m$, there exists $P$ such that `blockAt? c k = some P` and `blockAt? c' k = some P`.

c. **Quantifiers, parameter ranges and definitions**: Exact match. Combined with Theorem 4's agreement at depth $n$, this yields agreement on the full confirmed prefix.

d. **Convenience assumptions**: Standard parent-hash chaining and hash injectivity.

e. **Do the Lean definitions mean what the prose says?** Yes. Agreement on a single block implies agreement on the entire prefix preceding it.

Verdict: FAITHFUL

---

### C84

a. **Hypotheses**: N/A (prose disclaimer on formalization boundaries).

b. **Conclusion**: N/A.

c. **Quantifiers, parameter ranges and definitions**: Exact match. Accurately states that `sched_recent_certified_suffix_agreement` is proved under `ByzantineBounded` (the global all-window budget) rather than `ByzantineBoundedFrom H n` (horizon scoping).

d. **Convenience assumptions**: None. The paper explicitly disclaims horizon scoping for certificates and notes it as future work.

e. **Do the Lean definitions mean what the prose says?** Yes. The formal theorem `sched_recent_certified_suffix_agreement` indeed consumes `ByzantineBounded n (badSched ...)`.

Verdict: FAITHFUL

---

### C85

a. **Hypotheses**: N/A (definition of lockstep rotation rules).

b. **Conclusion**: N/A.

c. **Quantifiers, parameter ranges and definitions**: Exact match. In Lean, `noMixing` (`MoltPetit.Model.lockstepOk`) checks `(b.slot / n = b'.slot / n → b.keyIndex = b'.keyIndex) ∧ b.keyIndex ≤ b'.keyIndex`, and `validSignedChainLock` checks `sigsOk`, `validChainK`, and `noMixing`.

d. **Convenience assumptions**: None; syntactic check on block chains enforcing intra-grid uniformity and inter-grid monotonicity of generation counters.

e. **Do the Lean definitions mean what the prose says?** Yes. Lean's `lockstepOk` exactly enforces grid-window uniformity and monotonicity.

Verdict: FAITHFUL

---

### C86

a. **Hypotheses**: Fully disclosed in text (lines 1211--1222). Lean theorems `lockstep_client_safety` (`lockstep_recent_tip_ancestor_agreement`) and `lockstep_recent_tip_ancestor_mem` require `1 ≤ n`, `LockstepPackage` (containing monotone roster counter, honest signatures declaring window generation, initial genesis counter, hash injectivity, and $\rho + T \le \fmax$ budget over the one-window lagged counter), `validSignedChainLock` on both chains, shared genesis `blockAt? (stripSigs sc) 0 = some G` on both chains, recency $\mathit{now} \le \mathit{tip}.\mathit{slot} + \Delta$, sufficient length $n < \mathit{length}$, and tip-height relation ($\mathit{height} = \mathit{height}'$ or $\mathit{height} \le \mathit{height}'$).

b. **Conclusion**: Equal to Lean. Proves exact block agreement at depth $n$ for equal heights, and ancestor block containment for unequal heights.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The text explicitly notes that the client holds only genesis and a clock (matching the `blockAt? sc 0 = some G` hypothesis).

d. **Convenience assumptions**: Mode 3 assumes shared genesis agreement and the `LockstepPackage` properties (which transport to `PackageA` at the lagged schedule via `LockstepPackage.toPackageA`). All of these are explicitly enumerated in the theorem statement.

e. **Do the Lean definitions mean what the prose says?** Yes. Proves consensus safety under uncoordinated, event-driven key rotation.

Verdict: FAITHFUL

---

### C87

a. **Hypotheses**: Disclosed in text (lines 1224--1229). Lean theorem `lockstep_declares_rosterGen` requires `1 ≤ n`, `LockstepPackage`, `validSignedChainLock sc = true`, shared genesis `blockAt? (stripSigs sc) 0 = some G`, recency `∃ t, getLast? sc = some t ∧ now ≤ t.slot + Δ`, grid window $W$, and maturation `∃ D ∈ stripSigs sc, W * n + n ≤ D.slot + 1`.

b. **Conclusion**: Equal to Lean. Lean proves `∀ B ∈ stripSigs sc, B.slot / n = W → B.keyIndex = rosterGen W`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Consumes the standard `LockstepPackage` and chain validity; the maturation premise correctly captures that the window has been closed and witnessed by later blocks.

e. **Do the Lean definitions mean what the prose says?** Yes. Lean formally establishes that every block in a matured grid window declares the exact roster generation counter for that window.

Verdict: FAITHFUL

---

### C88

a. **Hypotheses**: Disclosed in Theorem 6 (lines 1233--1250). Lean theorems `lockstep_client_safety_gen` (`lockstepGen_recent_tip_ancestor_agreement`) and `lockstepGen_recent_tip_ancestor_mem` require `1 ≤ n`, `LockstepPackageGen` (honest declared generation `keyIndex = rosterGen (s / n)`, hash injectivity, core signature unforgeability, per-window rent bound $, per-generation theft bound $, and  + T \le max$), `validSignedChainLock` on both chains, recency `now ≤ tip.slot + Δ` for both tips, and chain length n < \mathit{length}$ (`hLong`, for both chains at equal heights; for the lower chain at unequal heights). Notably, unlike Theorem 5, no shared genesis hypothesis is required.

b. **Conclusion**: Equal to Lean. Proves exact block agreement at depth n$ (`List.length - 1 - 2 * n`) for equal tip heights, and ancestor block containment in the taller chain at depth at least n$ for unequal tip heights. Lean also establishes common prefix agreement down to genesis (`lockstepGen_recent_genesis_agreement`).

c. **Quantifiers, parameter ranges and definitions**: Exact match. Parameter ranges ( \le n$, confirmation depth n$) match Lean precisely.

d. **Convenience assumptions**: None beyond the disclosed package structure. Theorem 6 dispenses with the shared genesis assumption of Theorem 5, proving genesis agreement as a consequence.

e. **Do the Lean definitions mean what the prose says?** Yes. The definitions formally prove consensus safety under event-driven uncoordinated key rotation with a per-generation Byzantine budget.

Verdict: FAITHFUL

---

### C89

a. **Hypotheses**: Disclosed in text (lines 1252). Lean theorem `lockstep_window_declares_rosterGen` requires `1 ≤ n`, `LockstepPackageGen`, chain validity `validSignedChainLock`, tip recency, and window maturation `∃ D ∈ stripSigs sc, W * n + n ≤ D.slot + 1`. `window_shared_prefix` requires honest slot uniqueness, id injectivity, valid chains in record, tip slots past  + n \le \mathit{tip.slot} + 1$, and Byzantine slots bounded by $max$ on window $.

b. **Conclusion**: Equal to Lean. `lockstep_window_declares_rosterGen` shows every block in the matured grid window declares `rosterGen W`, and `window_shared_prefix` proves agreement on prefix blocks with slot $< u$.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The prose description matches the Lean theorem mechanics without discrepancy.

d. **Convenience assumptions**: Window maturation is the exact operational requirement for closing a grid window before drawing quorum inferences.

e. **Do the Lean definitions mean what the prose says?** Yes. The Lean formalization pins the window's declared generation without needing induction or genesis anchors.

Verdict: FAITHFUL

---

### C90

a. **Hypotheses**: Fully disclosed in text (line 1252). Lean theorem `lockstepGen_shared_prefix_sharp` requires `1 ≤ n`, `LockstepPackageGen`, valid signed chains, tip recency, lower tip slot ordering `sTip.slot ≤ sTip'.slot`, and the sharp depth bound `k + n + (sTip.slot + 1) % n < (stripSigs sc).length`.

b. **Conclusion**: Equal to Lean. Proves common block agreement at position $ across both chains.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The prose specifies "exactly  + ((t{+}1) mod n)$ positions for lower tip slot $", which is an exact translation of Lean's `k + n + (sTip.slot + 1) % n < length`.

d. **Convenience assumptions**: Standard package and chain validity; the sharp depth calculation accounts precisely for the unmatured tip grid window.

e. **Do the Lean definitions mean what the prose says?** Yes. Accurately formalizes the exact prefix boundary for lockstep chains.

Verdict: FAITHFUL

---

### C91

a. **Hypotheses**: Disclosed in text (line 1252). Lean theorem `LockstepPackage.toGen` requires `0 < n`, `LockstepPackage`, and the condition `∀ j, ∃ W, rosterGen W = j` ("the counter skips no generation").

b. **Conclusion**: Equal to Lean. Yields `LockstepPackageGen`.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The phrase "the counter skips no generation" directly corresponds to surjectivity of `rosterGen`.

d. **Convenience assumptions**: Surjectivity of `rosterGen` is necessary to ensure every generation's key theft is accounted for under cumulative window exposure.

e. **Do the Lean definitions mean what the prose says?** Yes. Demonstrates how cumulative exposure bounds imply per-generation bounds when generations advance without gaps.

Verdict: FAITHFUL

---

### C92

a. **Hypotheses**: Fully disclosed in text (lines 1257). `ErasureTimedLock n rosterGen stolenAt` formalizes erasure as `∀ i j r, stolenAt i j r → rosterGen (r / n) ≤ j`. `genBound_of_preRetirementBound` assumes `ErasureTimedLock` and `∀ j, (preRetirementTheftProducers n rosterGen stolenAt j).card ≤ T`. `lockstep_client_safety_timed` (`lockstepTimed_recent_tip_ancestor_agreement`) consumes `LockstepPackageTimed`.

b. **Conclusion**: Equal to Lean. `genBound_of_preRetirementBound` derives the per-generation census bound `{i ∈ range n | stolenOf stolenAt i j}.card ≤ T`, and `lockstep_client_safety_timed` delivers safety at depth n$.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The mathematical definition of erasure and pre-retirement theft bounds matches the prose explanation.

d. **Convenience assumptions**: Erasure is modeled by requiring that if seat $'s generation $ key is compromised at slot $, the active generation at $ does not exceed $ (`rosterGen (r / n) ≤ j`), faithfully encoding hardware destruction upon generation rollover.

e. **Do the Lean definitions mean what the prose says?** Yes. Lean explicitly shows that erasure allows recycling the corruption budget across distinct generations.

Verdict: FAITHFUL

---

### C93

a. **Hypotheses**: Fully disclosed in text (lines 1269--1275). `groundedCertLock_gen_of_tail` requires  \le n$ and `GroundedCertLock n Signed G cl g`. `groundedCertLock_gen_unique` requires  \le n$, `GroundedCertLock n Signed G cl g`, and  \in cl.tail$ with .slot = cl.tipSlot$.

b. **Conclusion**: Equal to Lean. Proves that for  \ge 2$, the tip block  \in cl.tail$ witnessing `cl.tipSlot` has `t.keyIndex = g`, and that this generation is uniquely determined.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The text explicitly distinguishes the behavior for  \ge 2$ from  = 1$.

d. **Convenience assumptions**: Follows directly from certificate structure and tail filtering; no ad-hoc convenience hypotheses.

e. **Do the Lean definitions mean what the prose says?** Yes. Formally shows that for  \ge 2$, certificate claims need not separately authenticate generation counters because the tip generation is contained within the claim's verified tail.

Verdict: FAITHFUL


---

### C94

a. **Hypotheses**: Fully disclosed in text (lines 1275--1286). `Molt.lockstep_client_safety_timed` requires `1 ≤ n`, `LockstepPackageTimed n rosterGen ops registry rented stolenAt honestSigned now Δ G R T`, valid signed chains under `validSignedChainLock`, tip recency `now ≤ sTip.slot + Δ`, confirmation depth `2 * n < sc.length`, and equal tip height `sTip.height = sTip'.height`.

b. **Conclusion**: Equal to Lean. Proves block agreement at depth $2n$ (`length - 1 - 2 * n`) below the tips under the timed model with erasure.

c. **Quantifiers, parameter ranges and definitions**: Exact match. Confirmation depth $2n$, window length $n$, rent and pre-retirement theft bounds match the paper's specification for mode 3 under timed theft.

d. **Convenience assumptions**: `LockstepPackageTimed` assumes erasure (`ErasureTimedLock`) and pre-retirement theft bounds (`preRetirementTheftBound`), which derive the per-generation bound via `genBound_of_preRetirementBound`. The paper explicitly discusses and defends these operational assumptions.

e. **Do the Lean definitions mean what the prose says?** Yes. Formally connects the timed key-stealing and hardware erasure model to end-to-end client safety.

Verdict: FAITHFUL

---

### C95

a. **Hypotheses**: Fully disclosed in text (lines 1286--1298). Lean theorems `lockstep_client_safety` (equal tip heights) and `lockstep_recent_tip_ancestor_mem` (unequal tip heights) require `1 ≤ n`, `LockstepPackage`, valid chains, and tip recency. `lockstep_declares_rosterGen` requires window maturity. `lockstep_recent_certified_suffix_agreement` and `lockstep_cert_gen_pinned` require certificate validity and quorum on certified suffix windows. `same_block_same_prefix` requires parent linking and hash injectivity.

b. **Conclusion**: Equal to Lean. Covers equal-height tip agreement at depth $n$, inclusion of the lower confirmed block on taller chains at unequal heights, and entire confirmed prefix agreement via parent hashes.

c. **Quantifiers, parameter ranges and definitions**: Exact match across all six cited machine-checked theorems.

d. **Convenience assumptions**: Standard package and chain validity hypotheses without unphysical constraints.

e. **Do the Lean definitions mean what the prose says?** Yes. Faithfully establishes full safety, suffix agreement, and certified agreement for schedule-free lockstep mode.

Verdict: FAITHFUL

---

### C96

a. **Hypotheses**: Disclosed in text (lines 1303--1311). `theft_exposure_window` assumes `Reacts` and `NoTheftBackdating`. `paced_tight_census_bound_all_F` assumes pacing bound $n + d \le P$. `paced_budget_holds_under_timing` assumes `Reacts`, `NoTheftBackdating`, and slot rent bounds.

b. **Conclusion**: Equal to Lean. Accurately describes that timed theft confines exposure to $[r, r+d)$ and prevents retroactive census expansion, while explicitly disclaiming execution-level budget separation.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The text correctly identifies the interval $[r, r+d)$ and the pacing constraint $n+d \le P$.

d. **Convenience assumptions**: The text is remarkably candid: it highlights that `NoTheftBackdating` is an asserted operational hypothesis whose derivation from signature primitives remains future work.

e. **Do the Lean definitions mean what the prose says?** Yes. Accurately reflects both the theoretical guarantees and the formal boundaries of the timed theft model.

Verdict: FAITHFUL

---

### C97

a. **Hypotheses**: Fully disclosed in text (lines 1311--1318). Lean theorems `sched_recent_certified_suffix_agreement` and `lockstep_recent_certified_suffix_agreement` require depth $n$ suffix bounds (`i + n < length`) under cumulative fault budgets (`SchedCoreUnforgeable` + `ByzantineBounded`, and `LockstepPackage`).

b. **Conclusion**: Equal to Lean. The text explicitly limits the scope of what is claimed, noting that both certificate theorems operate at depth $n$ under cumulative budgets, and acknowledging that extending them to horizon scoping (mode 2) or depth $2n$ erasure credit (mode 3) remains future work.

c. **Quantifiers, parameter ranges and definitions**: Exact match. Depth $n$ and cumulative budget conditions match the Lean theorem statements.

d. **Convenience assumptions**: None; this paragraph serves as an explicit disclaimer of overclaiming.

e. **Do the Lean definitions mean what the prose says?** Yes. Accurately documents the exact scope and limitations of the certificate suffix agreement theorems.

Verdict: FAITHFUL

---

### C98

a. **Hypotheses**: Fully disclosed in text (lines 1318--1323). Lean theorems `badSched_single_key_safe_not_enough` and `badKeyrot_single_key_safe_not_enough` are constructive counterexamples showing that single-key unforgeability does not imply slot safety.

b. **Conclusion**: Equal to Lean. Correctly concludes that the per-mode signature surfaces cannot be derived solely from single-key security in the timed model, justifying the need for per-mode operational no-back-dating assumptions.

c. **Quantifiers, parameter ranges and definitions**: Exact match. The existential witnesses in Lean match the text's assertion.

d. **Convenience assumptions**: Counterexamples with explicit witnesses; no convenience premises.

e. **Do the Lean definitions mean what the prose says?** Yes. Faithfully explains why Assumption 3 must be stated as an operational assumption.

Verdict: FAITHFUL


---

---

### C99

a. **Hypotheses**: Fully disclosed in text (lines 1333--1344). Lean theorem `Molt.production_liveness` requires fault budget (`ByzantineBounded n bad`), valid accepted chain (`validChain n c = true`), slot order (`tip.slot < slot`), slot assignment (`producerForSlot n slot = me`), slot record consistency (`∀ s, ∀ B ∈ record s, B.slot = s`), and honest delivery via `HonestBlocksCover` on the extended chain for newly matured windows. Lean theorem `Molt.global_liveness` requires valid genesis (`genesisOk g = true`), strictly increasing scheduled slots (`List.IsChain (· < ·) (g.slot :: ss)`), and Byzantine budget over matured windows where the adversary is defined as non-scheduled slots (`(badSlotsIn (fun s => s ∉ g.slot :: ss) u n).card ≤ maxByzantine n`).

b. **Conclusion**: Equal to Lean. Local liveness concludes that extension block production succeeds and passes the validator (`produceBlock? ... = some (nextBlock ...)`). Global liveness concludes that the synchronized honest run validates and has length `ss.length + 1` (`validChain n (buildChain g ss) = true ∧ (buildChain g ss).length = ss.length + 1`), reaching arbitrary height so that every block eventually becomes $n$-deep.

c. **Quantifiers, parameter ranges and definitions**: Exact match across both theorems.

d. **Convenience assumptions**: `production_liveness` assumes `HonestBlocksCover` directly on the extended chain `c ++ [nextBlock ...]`. `global_liveness` hard-codes a single synchronous line of blocks (`buildChain g ss`) where every block builds on its immediate predecessor, with the adversary defined tautologically as unscheduled slots. The paper explicitly qualifies: *"a synchronous honest run within the budget (over the run's span; each honest block reaches the next honest producer within its slot)"*.

e. **Do the Lean definitions mean what the prose says?** Yes. Accurately distinguishes local production on an accepted chain from synchronous global extension.

Verdict: FAITHFUL

---

### C100

a. **Hypotheses**: Fully disclosed in text (lines 1352--1357). Parameters $0 < n$, $0 \le \mathit{baseline}$, $0 \le \mathit{perBlock}$, $0 < \tau$. `Molt.slot_time_sufficient` assumes $\mathit{recommendedSlot} \le \tau$ and bounded initial backlog $0 \le u_0 \le n/2$. `Molt.slot_time_necessary` assumes $\mathit{perBlock} < \tau < \mathit{recommendedSlot}$ and a steady-state backlog $\mathit{nextBacklog}(u) = u$.

b. **Conclusion**: Equal to Lean. `slot_time_sufficient` proves that backlog remains $\le n/2$ and peak uncovered suffix remains $\le n$ for all iterations $j$. `slot_time_necessary` proves that at any steady state, peak uncovered suffix strictly exceeds $n$.

c. **Quantifiers, parameter ranges and definitions**: Exact match over the discrete proving backlog model.

d. **Convenience assumptions**: The timing pipeline model assumes proof generation time is affine in backlog ($baseline + u \cdot perBlock$), which the text explicitly acknowledges and instantiates in Section~\ref{sec:impl}.

e. **Do the Lean definitions mean what the prose says?** Yes. Accurately reflects the sufficiency and steady-state necessity of the recommended slot duration threshold.

Verdict: FAITHFUL

---

### C101

a. **Hypotheses**: Disclosed in text (lines 1364--1369). The extracted Rust validator accepts a chain: `molt_petit.valid_chain n c = Result.ok true`.

b. **Conclusion**: Equal to Lean. The projected chain is semantically valid in the model: `MoltPetit.Model.ValidChain (↑n) (Rust.toModelChain c)`.

c. **Quantifiers, parameter ranges and definitions**: Exact match between Aeneas-extracted `molt_petit.Chain` and `MoltPetit.Model.Chain`.

d. **Convenience assumptions**: None; directly connects the extracted Rust AST execution to the semantic specification.

e. **Do the Lean definitions mean what the prose says?** Yes. Establishes that if the extracted Rust validator accepts a chain, the semantic model predicate holds.

Verdict: FAITHFUL

---

### C102

a. **Hypotheses**: Fully disclosed in text (lines 1369--1374). Both Lean theorems (`Rust.rust_recent_tip_ancestor_mem` and `Rust.rust_timed_certified_agreement`) assume valid certified chain validation by the extracted Rust implementation (`validate_certified_chain ... = ok true`), Byzantine budget (`ByzantineBounded`), cryptographic interface assumptions (`RustSigned`, certificate verification to `GroundedCert`, and signature unforgeability or timed execution), and recency ($now \le slot + n$ or $R \le slot + n$).

b. **Conclusion**: Equal to Lean. Proves certified agreement / ancestor membership at depth $n$ for certified chains and suffixes accepted by the Rust validator.

c. **Quantifiers, parameter ranges and definitions**: Exact match across extracted Rust types and model representations.

d. **Convenience assumptions**: Standard cryptographic interface assumptions bridging concrete Rust crypto verification to model unforgeability.

e. **Do the Lean definitions mean what the prose says?** Yes. Accurately states that light-client safety and timed-growth theorems hold directly for chains accepted by the Rust validator.

Verdict: FAITHFUL

---

### C103

a. **Hypotheses**: Fully disclosed in text (lines 1374--1378). `valid_chain n c = Result.ok true` for the core validator; $0 < n$ and `valid_chain_k n c = Result.ok true` for the key-indexed validator.

b. **Conclusion**: Equal to Lean. Proves `ValidChain` and `KeyIndexMonotone` for the key-indexed validator, while the text explicitly notes that the three rotation pins of Section~\ref{sec:rotation} remain model-level today.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; the text is careful to disclaim implementation-level proofs of the rotation pins.

e. **Do the Lean definitions mean what the prose says?** Yes. Faithfully delimits what is proved about the Rust implementation versus what is proved at the model level.

Verdict: FAITHFUL

---

### C104

a. **Hypotheses**: Fully disclosed in text (lines 1378--1384). Quorum calculation succeeds (`quorum n = Result.ok q`) and the generic backend validator accepts: `valid_chain_be UB () n q (toChainG c) = Result.ok true`.

b. **Conclusion**: Equal to Lean. Yields `ValidChain (↑n) (toModelChain c)`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: The text explicitly notes that the equivalence theorem `valid_chain_be_validChain` is proven for the native `U64` backend (`UB`), leaving per-gadget faithfulness of the plonky2 circuit backend as a stated trust assumption rather than a verified equivalence.

e. **Do the Lean definitions mean what the prose says?** Yes. Accurately reports both the machine-checked backend-generic equivalence and the unverified circuit trust assumption.

Verdict: FAITHFUL

---

### C105

a. **Hypotheses**: N/A (prose empirical summary of proving performance).

b. **Conclusion**: N/A.

c. **Quantifiers, parameter ranges and definitions**: N/A.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** N/A (empirical evaluation claim).

Verdict: FAITHFUL

---

### C106

a. **Hypotheses**: N/A (related work comparison with Ouroboros line).

b. **Conclusion**: N/A.

c. **Quantifiers, parameter ranges and definitions**: N/A.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** N/A.

Verdict: FAITHFUL

---

### C107

a. **Hypotheses**: N/A (related work comparison with Plumo).

b. **Conclusion**: N/A.

c. **Quantifiers, parameter ranges and definitions**: N/A.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** N/A.

Verdict: FAITHFUL

---

### C108

a. **Hypotheses**: N/A (paragraph heading introducing machine-checked consensus related work).

b. **Conclusion**: N/A.

c. **Quantifiers, parameter ranges and definitions**: N/A.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** N/A.

Verdict: FAITHFUL

---

### C109

a. **Hypotheses**: Fully disclosed in text (lines 1535--1555). Comprehensive accounting of the trusted computing base (Lean kernel, pinned translation front-ends, circuit backend per-gadget faithfulness, native u64 equivalence `valid_chain_be_validChain`, operational assumptions, key-stealing signature surface, version independence under theft, roster commitment trust anchor, recency check in node loop, per-mode operational assumptions).

b. **Conclusion**: Equal to Lean. Transparently bounds the scope of verification.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; serves as an explicit disclaimer of unverified assumptions.

e. **Do the Lean definitions mean what the prose says?** Yes. Faithfully lists the formal boundary and trust base.

Verdict: FAITHFUL

---

### C110

a. **Hypotheses**: Fully disclosed in text (lines 1555--1560). Accurately notes that `Reacts` ($r + d \le s \implies j < \mathit{inForce}\; n\; \Delta\mathit{conf}\; c_0\; i\; s$) is formulated with respect to the version in force on the chain $c_0$ being validated.

b. **Conclusion**: Equal to Lean. The text explicitly identifies this as an open limitation (*"not yet in its final form... a form quantified only over the honest chain is open"*).

c. **Quantifiers, parameter ranges and definitions**: Exact match with definition of `MoltPetit.Model.Reacts`.

d. **Convenience assumptions**: The text is admirably candid about the limitation of the current formulation.

e. **Do the Lean definitions mean what the prose says?** Yes. Accurately explains the definition and its operational implications.

Verdict: FAITHFUL

---

### C111

a. **Hypotheses**: Fully disclosed in text (lines 1593--1594). Theorem~\ref{thm:lc} (`light_client_safety`) operates in the untimed model taking `SigUnforgeableRecent` as an input premise; it does not assume `NoBackdate`.

b. **Conclusion**: Equal to Lean. Theorem~\ref{thm:lc}'s type signature does not contain `NoBackdate`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. Accurately states that headline Theorem~\ref{thm:lc} does not use `NoBackdate`.

Verdict: FAITHFUL

---

### C112

a. **Hypotheses**: Fully disclosed in text (lines 1594--1596). Explains the purpose of Appendix~\ref{app:timed-uniq}: showing how `SigUnforgeableRecent` (the premise consumed by `light_client_safety`) is derived from EUF-CMA and `NoBackdate` in the timed model.

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None.

e. **Do the Lean definitions mean what the prose says?** Yes. Accurately frames the reduction proved in Theorem~\ref{thm:timed-uniq}.

Verdict: FAITHFUL

---

### C113

a. **Hypotheses**: Fully disclosed in text (lines 1608--1613). Definition of `projectSigned n log`: entry for $(p, s)$ is the block stamped $s$ that $p$ signed at real slot $s$.

b. **Conclusion**: Equal to Lean. Single-valued at honest slots where nodes sign at most once per slot (`honest_once`); at bad slots it chooses an arbitrary witness (`choose`) which downstream theorems never consult.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: Classical choice is used at bad slots, which is never consulted by downstream proofs.

e. **Do the Lean definitions mean what the prose says?** Yes. Prose matches the definition verbatim.

Verdict: FAITHFUL

---

### C114

a. **Hypotheses**: Fully disclosed in text (lines 1613--1620). Defines the EUF-CMA bridge (`Signed B → ∃ r, B ∈ log r`) and `NoBackdate` (`∀ r B, B ∈ log r → ¬ bad B.slot → B.slot = r`).

b. **Conclusion**: Equal to Lean.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: `NoBackdate` is explicitly acknowledged as an operational assumption closing the gap between EUF-CMA and slot uniqueness.

e. **Do the Lean definitions mean what the prose says?** Yes. Matches Lean definition exactly.

Verdict: FAITHFUL

---

### C115

a. **Hypotheses**: Fully disclosed in text (lines 1623--1628). `TimedExecution n bad log G`, `NoBackdate bad log`, and EUF-CMA bridge `∀ ⦃B⦄, Signed B → ∃ r, B ∈ log r`.

b. **Conclusion**: Equal to Lean. Concludes `SigUnforgeableRecent n bad Signed (projectSigned n log) now Δ`. The paper correctly notes that `now` and `Δ` are unused in the proof.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: No hidden premises; relies explicitly on `NoBackdate` and the bridge.

e. **Do the Lean definitions mean what the prose says?** Yes. Accurately reports the derivation of the untimed uniqueness residue.

Verdict: FAITHFUL

---

### C116

a. **Hypotheses**: Fully disclosed in text (lines 1643--1648). Constructive countermodel showing `NoBackdate` does not follow from `TimedExecution` alone.

b. **Conclusion**: Equal to Lean: $\exists \mathit{bad}\; \mathit{log}\; G,\; \mathit{TimedExecution}\; 2\; \mathit{bad}\; \mathit{log}\; G \wedge \neg \mathit{NoBackdate}\; \mathit{bad}\; \mathit{log}$.

c. **Quantifiers, parameter ranges and definitions**: Exact match ($n = 2$).

d. **Convenience assumptions**: None; constructive counterexample with concrete witnesses.

e. **Do the Lean definitions mean what the prose says?** Yes. Directly supports the claim that the bare timed model allows back-dating by bad slots onto honest stamps.

Verdict: FAITHFUL

---

### C117

a. **Hypotheses**: Fully disclosed in text (lines 1661--1667). Constructive countermodels for both mode 2 (`badSched`) and mode 1 (`badKeyrot`).

b. **Conclusion**: Equal to Lean. Shows there exist executions where a slot is not rented and an eligible key version $j$ is not stolen, yet the slot is corrupt under `badSched` or `badKeyrot`.

c. **Quantifiers, parameter ranges and definitions**: Exact match.

d. **Convenience assumptions**: None; constructive countermodels justifying why rotation security surfaces cannot be reduced to single-key unforgeability.

e. **Do the Lean definitions mean what the prose says?** Yes. Faithfully explains why Assumption~\ref{ass:rotation-honest} must be stated as an operational assumption.

Verdict: FAITHFUL

FAITHFULNESS: DONE
