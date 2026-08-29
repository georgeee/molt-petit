import Thales.TS.Runtime

open Thales.TS

set_option linter.unusedVariables false

namespace MoltPetit

abbrev RawSignature := Int

abbrev RawPublicKey := Int

abbrev RawSecretKey := Int

abbrev RawCertificate := Int

abbrev Hash := Int

inductive Chain where
  | nil
  | cons (slot : Int) (height : Int) (prev : (Option Hash)) (id : Hash) (contentsHash : Hash) (keyIndex : Int) (tail : Chain)
  deriving Repr

def quorum (n : Int) : Int :=
  (((2 * n) + 2) / 3)

def maxByzantine (n : Int) : Int :=
  ((n - 1) / 3)

def producerForSlot (n : Int) (slot : Int) : Int :=
  (slot - ((slot / n) * n))

def lengthOf (c : Chain) : Int :=
  match c with
    | .nil => 0
    | .cons slot height prev id contentsHash keyIndex tail => (1 + (lengthOf tail))

def appendChains (a : Chain) (b : Chain) : Chain :=
  match a with
    | .nil => b
    | .cons slot height prev id contentsHash keyIndex tail => let s := slot
    let h := height
    let p := prev
    let i := id
    let ct := contentsHash
    let ki := keyIndex
    let rest := (appendChains tail b)
    (.cons s h p i ct ki rest)

def tipSlotFrom (cur : Int) (t : Chain) : Int :=
  match t with
    | .nil => cur
    | .cons slot height prev id contentsHash keyIndex tail => (tipSlotFrom slot tail)

def tipHeightFrom (cur : Int) (t : Chain) : Int :=
  match t with
    | .nil => cur
    | .cons slot height prev id contentsHash keyIndex tail => (tipHeightFrom height tail)

def tipIdFrom (cur : Hash) (t : Chain) : Hash :=
  match t with
    | .nil => cur
    | .cons slot height prev id contentsHash keyIndex tail => (tipIdFrom id tail)

def windowCount (c : Chain) (u : Int) (n : Int) : Int :=
  match c with
    | .nil => 0
    | .cons slot height prev id contentsHash keyIndex tail => let inWin := if ((u <= slot) && (slot < (u + n))) then 1 else 0
    (inWin + (windowCount tail u n))

def windowDense (c : Chain) (u : Int) (n : Int) : Bool :=
  ((quorum n) <= (windowCount c u n))

def anchorsDense (all : Chain) (rest : Chain) (lo : Int) (t : Int) (n : Int) : Bool :=
  match rest with
    | .nil => true
    | .cons slot height prev id contentsHash keyIndex tail => let u := (slot + 1)
    let ok := if ((lo <= u) && ((u + n) <= (t + 1))) then (windowDense all u n) else true
    (ok && (anchorsDense all tail lo t n))

def maturedDense (c : Chain) (lo : Int) (t : Int) (n : Int) : Bool :=
  let base := if ((lo + n) <= (t + 1)) then (windowDense c lo n) else true
  (base && (anchorsDense c c lo t n))

def linksFrom (pSlot : Int) (pHeight : Int) (pId : Hash) (t : Chain) : Bool :=
  match t with
    | .nil => true
    | .cons slot height prev id contentsHash keyIndex tail => let link := (((height == (pHeight + 1)) && (pSlot < slot)) && (prev == pId))
    (link && (linksFrom slot height id tail))

def validChain (n : Int) (c : Chain) : Bool :=
  match c with
    | .nil => true
    | .cons slot height prev id contentsHash keyIndex tail => let genesis := ((height == 0) && prev.isNone)
    let links := (linksFrom slot height id tail)
    let tipSlot := (tipSlotFrom slot tail)
    ((genesis && links) && (maturedDense c 0 tipSlot n))

def monoAgainst (n : Int) (slot : Int) (ki : Int) (rest : Chain) : Bool :=
  match rest with
    | .nil => true
    | .cons slot height prev id contentsHash keyIndex tail => let ok := if ((producerForSlot n slot) == (producerForSlot n slot)) then (ki <= keyIndex) else true
    (ok && (monoAgainst n slot ki tail))

def keyMonoOk (n : Int) (c : Chain) : Bool :=
  match c with
    | .nil => true
    | .cons slot height prev id contentsHash keyIndex tail => ((monoAgainst n slot keyIndex tail) && (keyMonoOk n tail))

def validChainK (n : Int) (c : Chain) : Bool :=
  ((validChain n c) && (keyMonoOk n c))

def singletonBlock (slot : Int) (height : Int) (prev : Hash) (id : Hash) (contentsHash : Hash) (keyIndex : Int) : Chain :=
  (.cons slot height prev id contentsHash keyIndex .nil)

def produceBlock (n : Int) (me : Int) (atSlot : Int) (newId : Hash) (contentsHash : Hash) (keyIndex : Int) (c : Chain) : (Option Chain) :=
  if ((producerForSlot n atSlot) != me) then .none else match c with
    | .nil => .none
    | .cons slot height prev id contentsHash keyIndex tail => let tipHeight := (tipHeightFrom height tail)
    let tipId := (tipIdFrom id tail)
    let extended := (appendChains c ((singletonBlock atSlot ((tipHeight + 1)) tipId newId contentsHash keyIndex)))
    if (validChain n extended) then (.some extended) else .none

def selectChain (n : Int) (cur : Chain) (candidate : Chain) : Chain :=
  if ((validChain n candidate) && ((lengthOf cur) < (lengthOf candidate))) then candidate else cur

structure CertClaim where
  tipId : Hash
  tipSlot : Int
  tipHeight : Int
  tail : Chain
  deriving Repr, BEq

def validateSuffix (n : Int) (c : CertClaim) (suffix : Chain) : Bool :=
  match suffix with
    | .nil => true
    | .cons slot height prev id contentsHash keyIndex tail => let link := (((height == (c.tipHeight + 1)) && (c.tipSlot < slot)) && (prev == c.tipId))
    let links := (linksFrom slot height id tail)
    let buf := (appendChains c.tail suffix)
    let lo := ((c.tipSlot + 2) - n)
    let tipSlot := (tipSlotFrom slot tail)
    ((link && links) && (maturedDense buf lo tipSlot n))

inductive FloorList where
  | fnil
  | fcons (producer : Int) (floor : Int) (tail : FloorList)
  deriving Repr

def floorLookup (fl : FloorList) (i : Int) : Int :=
  match fl with
    | .fnil => 0
    | .fcons producer floor tail => if (producer == i) then floor else (floorLookup tail i)

def floorBump (fl : FloorList) (i : Int) (v : Int) : FloorList :=
  match fl with
    | .fnil => .fnil
    | .fcons producer floor tail => let f := if (producer == i) then if (floor < v) then v else floor else floor
    let rest := if (producer == i) then tail else (floorBump tail i v)
    (.fcons fl.producer f rest)

def floorsShapeFrom (i : Int) (n : Int) (fl : FloorList) : Bool :=
  match fl with
    | .fnil => (i == n)
    | .fcons producer floor tail => (((producer == i) && (0 <= floor)) && (floorsShapeFrom ((i + 1)) n tail))

def floorsShapeOk (n : Int) (fl : FloorList) : Bool :=
  (floorsShapeFrom 0 n fl)

def keyMonoFromTs (n : Int) (fl : FloorList) (c : Chain) : Bool :=
  match c with
    | .nil => true
    | .cons slot height prev id contentsHash keyIndex tail => let i := (producerForSlot n slot)
    let ok := ((floorLookup fl i) <= keyIndex)
    (ok && (keyMonoFromTs n ((floorBump fl i keyIndex)) tail))

def validateSuffixK (n : Int) (c : CertClaim) (fl : FloorList) (suffix : Chain) : Bool :=
  (((validateSuffix n c suffix) && (floorsShapeOk n fl)) && (keyMonoFromTs n fl suffix))

inductive SignedChain where
  | nil
  | cons (slot : Int) (height : Int) (prev : (Option Hash)) (id : Hash) (contentsHash : Hash) (keyIndex : Int) (sig : RawSignature) (tail : SignedChain)
  deriving Repr

structure SigOps where
  sign : (RawSecretKey → (Int → (Int → (Hash → (Hash → RawSignature)))))
  verify : (RawPublicKey → (Int → (Int → ((Option Hash) → (Hash → (RawSignature → Bool))))))
  keyFor : (Int → (Int → RawPublicKey))
  deriving Repr, BEq

def lengthOfSigned (sc : SignedChain) : Int :=
  match sc with
    | .nil => 0
    | .cons slot height prev id contentsHash keyIndex sig tail => (1 + (lengthOfSigned tail))

def stripSigs (sc : SignedChain) : Chain :=
  match sc with
    | .nil => .nil
    | .cons slot height prev id contentsHash keyIndex sig tail => let s := slot
    let h := height
    let p := prev
    let i := id
    let ct := contentsHash
    let ki := keyIndex
    let rest := (stripSigs tail)
    (.cons s h p i ct ki rest)

def appendSigned (a : SignedChain) (b : SignedChain) : SignedChain :=
  match a with
    | .nil => b
    | .cons slot height prev id contentsHash keyIndex sig tail => let s := slot
    let h := height
    let p := prev
    let i := id
    let ct := contentsHash
    let ki := keyIndex
    let g := sig
    let rest := (appendSigned tail b)
    (.cons s h p i ct ki g rest)

def sigsOk (n : Int) (sigOps : SigOps) (sc : SignedChain) : Bool :=
  match sc with
    | .nil => true
    | .cons slot height prev id contentsHash keyIndex sig tail => let ok := (sigOps.verify ((sigOps.keyFor ((producerForSlot n slot)) keyIndex)) slot height prev id sig)
    (ok && (sigsOk n sigOps tail))

structure CertOps where
  verify : (RawCertificate → Bool)
  claim : (RawCertificate → CertClaim)
  certFor : (Hash → RawCertificate)
  deriving Repr, BEq

inductive CertifiedChain where
  | invalid
  | cc (cert : RawCertificate) (suffix : SignedChain)
  deriving Repr

def isNilChain (c : Chain) : Bool :=
  match c with
    | .nil => true
    | .cons slot height prev id contentsHash keyIndex tail => false

def headMatches (pslot : Int) (pheight : Int) (pprev : (Option Hash)) (pid : Hash) (c : Chain) : Bool :=
  match c with
    | .nil => false
    | .cons slot height prev id contentsHash keyIndex tail => ((((pslot == slot) && (pheight == height)) && (pprev == prev)) && (pid == id))

def tailOf (c : Chain) : Chain :=
  match c with
    | .nil => .nil
    | .cons slot height prev id contentsHash keyIndex tail => tail

def eqChain (a : Chain) (b : Chain) : Bool :=
  match a with
    | .nil => (isNilChain b)
    | .cons slot height prev id contentsHash keyIndex tail => let head := (headMatches slot height prev id b)
    (head && (eqChain tail ((tailOf b))))

def filterLow (c : Chain) (lo : Int) : Chain :=
  match c with
    | .nil => .nil
    | .cons slot height prev id contentsHash keyIndex tail => let s := slot
    let h := height
    let p := prev
    let i := id
    let ct := contentsHash
    let ki := keyIndex
    let rest := (filterLow tail lo)
    if (lo <= s) then (.cons s h p i ct ki rest) else rest

def validateCertifiedChain (n : Int) (sigOps : SigOps) (certOps : CertOps) (cc : CertifiedChain) : Bool :=
  match cc with
    | .invalid => false
    | .cc cert suffix => (((certOps.verify cert) && (sigsOk n sigOps suffix)) && (validateSuffix n ((certOps.claim cert)) ((stripSigs suffix))))

def ccIf (ok : Bool) (cert : RawCertificate) (suffix : SignedChain) : CertifiedChain :=
  if ok then (.cc cert suffix) else .invalid

def orFirst (a : CertifiedChain) (b : CertifiedChain) : CertifiedChain :=
  match a with
    | .invalid => b
    | .cc cert suffix => a

def tryCut (n : Int) (certOps : CertOps) (oldCl : CertClaim) (droppedAcc : Chain) (suffix : SignedChain) : CertifiedChain :=
  match suffix with
    | .nil => .invalid
    | .cons slot height prev id contentsHash keyIndex sig tail => if ((lengthOfSigned tail) < n) then .invalid else let ds := slot
    let dh := height
    let dp := prev
    let di := id
    let tail := tail
    let dct := contentsHash
    let dki := keyIndex
    let cutBlock : Chain := (.cons ds dh dp di dct dki .nil)
    let dropped := (appendChains droppedAcc cutBlock)
    let deeper := (tryCut n certOps oldCl dropped tail)
    let cand := (certOps.certFor di)
    let cl := (certOps.claim cand)
    let expectedTail := (filterLow ((appendChains oldCl.tail dropped)) (((ds + 2) - n)))
    let shapeOk := (((((certOps.verify cand) && (cl.tipId == di)) && (cl.tipSlot == ds)) && (cl.tipHeight == dh)) && (eqChain cl.tail expectedTail))
    let here := (ccIf shapeOk cand tail)
    (orFirst deeper here)

def orKeep (cut : CertifiedChain) (cert : RawCertificate) (suffix : SignedChain) : CertifiedChain :=
  match cut with
    | .invalid => (.cc cert suffix)
    | .cc cert suffix => cut

def compactChain (n : Int) (certOps : CertOps) (cert : RawCertificate) (suffix : SignedChain) : CertifiedChain :=
  let nilChain : Chain := .nil
  let cut := (tryCut n certOps ((certOps.claim cert)) nilChain suffix)
  (orKeep cut cert suffix)

def produceBlockCert (n : Int) (me : Int) (atSlot : Int) (newId : Hash) (contentsHash : Hash) (keyIndex : Int) (sk : RawSecretKey) (sigOps : SigOps) (certOps : CertOps) (cert : RawCertificate) (suffix : SignedChain) : CertifiedChain :=
  if ((producerForSlot n atSlot) != me) then .invalid else let cl := (certOps.claim cert)
  let stripped := (stripSigs suffix)
  let tipH := (tipHeightFrom cl.tipHeight stripped)
  let tipI := (tipIdFrom cl.tipId stripped)
  let sig := (sigOps.sign sk atSlot ((tipH + 1)) tipI newId)
  let sb : SignedChain := (.cons atSlot ((tipH + 1)) tipI newId contentsHash keyIndex sig .nil)
  let newSuffix := (appendSigned suffix sb)
  let compacted := (compactChain n certOps cert newSuffix)
  if (validateCertifiedChain n sigOps certOps compacted) then compacted else .invalid

def ccHeight (certOps : CertOps) (cc : CertifiedChain) : Int :=
  match cc with
    | .invalid => (0 - 1)
    | .cc cert suffix => (tipHeightFrom ((certOps.claim cert)).tipHeight ((stripSigs suffix)))

def selectCertifiedChain (n : Int) (sigOps : SigOps) (certOps : CertOps) (cur : CertifiedChain) (candidate : CertifiedChain) : CertifiedChain :=
  if ((validateCertifiedChain n sigOps certOps candidate) && ((ccHeight certOps cur) < (ccHeight certOps candidate))) then candidate else cur

end MoltPetit
