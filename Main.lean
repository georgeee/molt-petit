import MoltPetit.Model.Definitions

/-!
Demo driver — certificate + signature simulation.

Two modes shown side-by-side:

* **Plain** — bare `validChain`-based chain (unsigned, baseline).
* **Cert** — `CertifiedChain` with trivial unit signatures and trivial cert.

Both use `n = 7`, `σ = Unit`, `pk = Unit` (trivial sig ops accept everything).
The cert rolls the suffix into the certificate every `n` blocks.
-/

open MoltPetit.Model

-- ---------------------------------------------------------------------------
-- Plain simulation (unchanged from before)
-- ---------------------------------------------------------------------------

def simulatePlain (n : Nat) (offline : List Nat) (slots : Nat) : Chain := Id.run do
  let mut chain : Chain := [genesisBlock 0]
  let mut nextId := 1
  for slot in [1:slots+1] do
    let producer := producerForSlot n slot
    unless offline.contains producer do
      match produceBlock? n producer slot nextId 0 0 chain with
      | some b => chain := chain ++ [b]; nextId := nextId + 1
      | none   => pure ()
  return chain

-- ---------------------------------------------------------------------------
-- Certificate + signature simulation
-- ---------------------------------------------------------------------------

def maybeRoll (n rollEvery : Nat) (certOps : CertOps TrivialCert)
    (cc : CertifiedChain TrivialCert Unit) : CertifiedChain TrivialCert Unit :=
  if cc.suffix.length >= rollEvery then
    let newCert := cc.suffix.foldl (fun c sb => certOps.generate c sb.block) cc.cert
    { cert := newCert, suffix := [] }
  else cc

def simulateCert (n rollEvery : Nat) (offline : List Nat) (slots : Nat)
    : CertifiedChain TrivialCert Unit := Id.run do
  let certOps := trivialCertOps n
  let sigOps  := trivialSigOps
  let reg     := trivialRegistry n
  let mut cc  : CertifiedChain TrivialCert Unit := trivialGenesisCertChain 0
  let mut nextId := 1
  for slot in [1:slots+1] do
    let producer := producerForSlot n slot
    unless offline.contains producer do
      match produceBlockCert? n producer slot nextId 0 0 sigOps reg () certOps cc with
      | some (_, cc') =>
        cc := maybeRoll n rollEvery certOps cc'
        nextId := nextId + 1
      | none => pure ()
  return cc

-- ---------------------------------------------------------------------------
-- Reporting
-- ---------------------------------------------------------------------------

def reportPlain (n : Nat) (label : String) (offline : List Nat) (slots : Nat) : IO Unit := do
  let chain := simulatePlain n offline slots
  let valid := validChain n chain
  let tip   := chain.getLast?.map (fun b => s!"slot={b.slot} h={b.height}") |>.getD "empty"
  IO.println s!"  [plain] {label}: {chain.length} blocks, valid={valid}, {tip}"

def reportCert (n rollEvery : Nat) (label : String) (offline : List Nat) (slots : Nat) : IO Unit := do
  let certOps := trivialCertOps n
  let sigOps  := trivialSigOps
  let reg     := trivialRegistry n
  let cc      := simulateCert n rollEvery offline slots
  let valid   := validateCertifiedChain n sigOps reg certOps cc
  let h       := certTipHeight certOps cc
  let cLen    := cc.cert.length
  let sLen    := cc.suffix.length
  IO.println s!"  [cert]  {label}: valid={valid}, h={h} (cert={cLen}blk suffix={sLen}blk signed)"

def main : IO Unit := do
  let n        := 7
  let rollEvery := n
  IO.println s!"Molt Petit (n={n}, quorum={quorum n}, maxByzantine={maxByzantine n})"
  IO.println ""
  for (label, offline) in [("0 offline", ([] : List Nat)),
                             ("2 offline (= maxByzantine)", [2, 5]),
                             ("3 offline (> maxByzantine)", [1, 2, 5])] do
    reportPlain n label offline 70
    reportCert  n rollEvery label offline 70
