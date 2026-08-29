import Molt.Protocol

/-!
# The rules a node runs (paper §4)

The three operations of a node's life — validate, produce, select — over
certified chains, plus the signature layer they sit on. Fresh presentation;
bridges to the `MoltPetit.Model` originals at the bottom.

The interface *types* (`SigOps`, `CertOps`, …) are re-exported, not
re-declared, for the same reason as `Block`: theorems transport only across
shared types.
-/

namespace Molt

/-! ## The signature layer -/

/-- Abstract signature operations over signature type `σ`, secret-key type
`sk`, and public-key type `pk`: `sign` and `verify`. -/
abbrev SigOps (σ sk pk : Type) := MoltPetit.Model.SigOps σ sk pk

/-- The versioned public-key directory: `registry i j` is seat `i`'s public
key at version `j`, written `dk(i, j)` in the paper. Deployments realize it
inside the signature bundle (paper §3), not as a service. -/
abbrev KeyRegistry (pk : Type) := MoltPetit.Model.KeyRegistry pk

/-- A block on the wire: content plus a detached signature. -/
abbrev SignedBlock (σ : Type) := MoltPetit.Model.SignedBlock σ

/-- A signed chain. -/
abbrev SignedChain (σ : Type) := MoltPetit.Model.SignedChain σ

/-- Forget the signatures. -/
def stripSigs {σ : Type} (sc : SignedChain σ) : Chain :=
  sc.map MoltPetit.Model.SignedBlock.block

/-- One block's signature verifies, under the key of its slot's producer at
the block's declared version. -/
def sigOk {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk)
    (registry : KeyRegistry pk) (sb : SignedBlock σ) : Bool :=
  ops.verify (registry (producer n sb.block.slot) sb.block.keyIndex)
    sb.block sb.sig

/-- Every block's signature verifies. -/
def sigsOk {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk)
    (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sc.all (sigOk n ops registry)

/-- A signed chain is valid: all signatures verify and the stripped chain
passes `validChain`. -/
def validSignedChain {σ sk pk : Type} (n : Nat) (ops : SigOps σ sk pk)
    (registry : KeyRegistry pk) (sc : SignedChain σ) : Bool :=
  sigsOk n ops registry sc && validChain n (stripSigs sc)

/-! ## Certified chains -/

/-- What a certificate claims: the tip it vouches for (id, slot, height)
plus a boundary buffer of near-tip stripped blocks, so window density can
be counted across the certificate/suffix seam. -/
abbrev CertClaim := MoltPetit.Model.CertClaim

/-- Abstract certificate operations: read the `claim`, `verify` the
certificate (e.g. verify a recursive ZK proof), `generate` an extension by
one validated block. -/
abbrev CertOps (α : Type) := MoltPetit.Model.CertOps α

/-- What a node holds: a certificate for the prefix plus a signed suffix. -/
abbrev CertifiedChain (α σ : Type) := MoltPetit.Model.CertifiedChain α σ

/-- Effective tip height: the suffix tip's if the suffix is nonempty, else
the claim's. -/
def tipHeight {α σ : Type} (ops : CertOps α) (cc : CertifiedChain α σ) : Nat :=
  cc.suffix.getLast?.map (·.block.height) |>.getD (ops.claim cc.cert).tipHeight

/-- Validate a signed suffix as a continuation of a certified prefix:
signatures; the structural link from claim tip to first suffix block; links
within the suffix; density of every window maturing inside the suffix,
counted over the boundary buffer plus the suffix. -/
def validSuffix {α σ sk pk : Type} (n : Nat)
    (sigOps : SigOps σ sk pk) (registry : KeyRegistry pk)
    (certOps : CertOps α) (cert : α)
    (suffix : SignedChain σ) : Bool :=
  let chain := stripSigs suffix
  sigsOk n sigOps registry suffix &&
  match chain with
  | [] => true
  | first :: rest =>
    let c := certOps.claim cert
    decide (first.height = c.tipHeight + 1 ∧
            c.tipSlot < first.slot ∧
            first.prev = some c.tipId) &&
    linksOk (first :: rest) &&
    (match (first :: rest).getLast? with
     | none   => true
     | some t =>
         let buf := c.tail ++ (first :: rest)
         let lo  := c.tipSlot + 2 - n
         let hi  := t.slot + 2 - n
         (List.range (hi - lo)).all fun d => windowDense n buf (lo + d))

/-- **Validate**: the certificate verifies and the suffix continues it. -/
def validCertifiedChain {α σ sk pk : Type} (n : Nat)
    (sigOps : SigOps σ sk pk) (registry : KeyRegistry pk)
    (certOps : CertOps α) (cc : CertifiedChain α σ) : Bool :=
  certOps.verify cc.cert &&
  validSuffix n sigOps registry certOps cc.cert cc.suffix

/-- **Produce**: only in the caller's own slot — build the next block on
the current tip, sign it, append it, and ship the result only if it passes
the same suffix validation every other node runs. -/
def produceBlock? {α σ sk pk : Type} (n me slot newId : Nat)
    (contentsHash keyIndex : Nat)
    (sigOps : SigOps σ sk pk) (registry : KeyRegistry pk) (myKey : sk)
    (certOps : CertOps α) (cc : CertifiedChain α σ) :
    Option (SignedBlock σ × CertifiedChain α σ) :=
  if producer n slot ≠ me then none
  else
    let c   := certOps.claim cc.cert
    let tip : Block :=
      cc.suffix.getLast?.map (·.block) |>.getD
        { slot := c.tipSlot, height := c.tipHeight, prev := none,
          id := c.tipId, contentsHash := 0, keyIndex := 0 }
    let b  : Block         :=
      { slot, height := tip.height + 1, prev := some tip.id, id := newId,
        contentsHash, keyIndex }
    let sb : SignedBlock σ := { block := b, sig := sigOps.sign myKey b }
    let newSuffix := cc.suffix ++ [sb]
    if validSuffix n sigOps registry certOps cc.cert newSuffix then
      some (sb, { cert := cc.cert, suffix := newSuffix })
    else none

/-- **Select**: adopt a candidate only if it validates and its tip is
strictly higher. Safety never depends on this rule (the theorems quantify
over arbitrary accepted chains); only liveness does. -/
def selectChain {α σ sk pk : Type} (n : Nat)
    (sigOps : SigOps σ sk pk) (registry : KeyRegistry pk)
    (certOps : CertOps α) (current candidate : CertifiedChain α σ) :
    CertifiedChain α σ :=
  if validCertifiedChain n sigOps registry certOps candidate &&
     tipHeight certOps candidate > tipHeight certOps current
  then candidate
  else current

/-! ## Bridge to the core development -/

theorem stripSigs_eq_core {σ : Type} :
    (stripSigs (σ := σ)) = MoltPetit.Model.stripSigs := rfl
theorem sigOk_eq_core {σ sk pk : Type} :
    (sigOk (σ := σ) (sk := sk) (pk := pk)) = MoltPetit.Model.sigOk := rfl
theorem sigsOk_eq_core {σ sk pk : Type} :
    (sigsOk (σ := σ) (sk := sk) (pk := pk)) = MoltPetit.Model.sigsOk := rfl

theorem validSignedChain_eq_core {σ sk pk : Type} :
    (validSignedChain (σ := σ) (sk := sk) (pk := pk))
      = MoltPetit.Model.validSignedChain := by
  funext n ops registry sc
  simp only [validSignedChain, MoltPetit.Model.validSignedChain,
    sigsOk_eq_core, validChain_eq_core, stripSigs_eq_core]

theorem tipHeight_eq_core {α σ : Type} :
    (tipHeight (α := α) (σ := σ)) = MoltPetit.Model.certTipHeight := rfl

theorem validSuffix_eq_core {α σ sk pk : Type} :
    (validSuffix (α := α) (σ := σ) (sk := sk) (pk := pk))
      = MoltPetit.Model.validateSuffix := by
  funext n sigOps registry certOps cert suffix
  simp only [validSuffix, MoltPetit.Model.validateSuffix,
    sigsOk_eq_core, stripSigs_eq_core]
  rcases hc : MoltPetit.Model.stripSigs suffix with _ | ⟨first, rest⟩
  · simp only [hc]
  · simp only [hc]
    rcases hg : (first :: rest).getLast? with _ | t
    · simp only [hg, linksOk_eq_core]
    · simp only [hg, linksOk_eq_core, windowDense_eq_core]

theorem validCertifiedChain_eq_core {α σ sk pk : Type} :
    (validCertifiedChain (α := α) (σ := σ) (sk := sk) (pk := pk))
      = MoltPetit.Model.validateCertifiedChain := by
  funext n sigOps registry certOps cc
  simp only [validCertifiedChain, MoltPetit.Model.validateCertifiedChain,
    validSuffix_eq_core]

theorem produceBlock?_eq_core {α σ sk pk : Type} :
    (produceBlock? (α := α) (σ := σ) (sk := sk) (pk := pk))
      = MoltPetit.Model.produceBlockCert? := by
  funext n me slot newId contentsHash keyIndex sigOps registry myKey certOps cc
  unfold produceBlock? MoltPetit.Model.produceBlockCert?
  simp only [producer_eq_core, validSuffix_eq_core]

theorem selectChain_eq_core {α σ sk pk : Type} :
    (selectChain (α := α) (σ := σ) (sk := sk) (pk := pk))
      = MoltPetit.Model.selectCertifiedChain := by
  funext n sigOps registry certOps current candidate
  simp only [selectChain, MoltPetit.Model.selectCertifiedChain,
    validCertifiedChain_eq_core, tipHeight_eq_core]
  rfl

end Molt
