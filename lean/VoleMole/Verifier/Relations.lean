import VoleMole.Verifier.Verify
import VoleMole.Verifier.Keygen
import VoleMole.Spec.Moussaka
import VoleMole.Spec.PomFRIT
import VoleMole.Arith.Moussaka
import VoleMole.Arith.Ratatouille
import VoleMole.Arith.PomFRIT
import VoleMole.Verifier.UovEval

/-!
# The five relations as verifier statements

For each of vole-mole's relations, a `Statement` built from the instance: parameters, DST
(`src/dst.hpp`), the instance encoding (`hash_instance`), binders, and the constraint evaluator
(the sharing evaluators of `Arith/*`, instantiated at `F := GF128`, `β := beta`, `K := GF256`;
for the three UOV relations with the UOV term computed directly over arrays,
`Verifier/UovEval.lean`, proved equal).

* Moussaka issuance and redemption: `Spec.Moussaka.IssueInstance.encode`,
  `RedeemInstance.encode`; `Arith.Moussaka.issueValues`, `UovEval.moussakaRedeemValues`
  (`= Arith.Moussaka.redeemValues`).
* Ratatouille issuance and spend: `hash_instance` (`src/ratatouille/issue.hpp:151-155`,
  `spend.hpp:321-327`) is written out here (`Spec/Ratatouille.lean` has no encoding);
  `Arith.Ratatouille.issueValues`, `UovEval.ratatouilleSpendValues` (`= spendValues`).
* PomFRIT redemption: delayed instance binding, binders `refresher_com` and `refresher`
  (`src/pomfrit/pomfrit.cpp:219-237`), instance `(pk, h)` with
  `h = Spec.PomFRIT.hashToTarget dig(pk) chal1 sig msg`; `UovEval.pomfritRedeemValues`
  (`= System.values` of `Arith.PomFRIT.pomfritRedeemSystem`).
* `labelRows` (default `false`, `main`'s layout) selects the dedicated-label-row layout of branch
  `voleith-label-rows` (`Params.labelRows`), which all five relations use there.
* The UOV combinations: `l = H(chal2 ‖ COMBINE_DST)`, 45 field elements
  (`uov::detail::Combination`, `src/uov/circuit.hpp:56-69`).
* UOV public keys: `UovPk.ofCompressed` expands a compressed public key as pqov's `expand_pk`
  (`subprojects/pqov/src/ov_keypair.c:66-76`): `P1 ‖ P2` is AES-128-CTR under the 16-byte
  `pk_seed` (zero 12-byte nonce, 32-bit big-endian block counter from 0;
  `pqov/utils/utils_prng.c:287-320`), followed by `P3` from the compressed key; the digest is
  `SHAKE256(cpk)` (32 bytes, `src/uov/uov.cpp:73-86`). `UovPk.ofSecret` derives the compressed
  key from a compact secret key first (pqov's key generation, `Verifier/Keygen.lean`).
-/

namespace VoleMole.Verifier

open VoleMole.Arith VoleMole.Spec

def toBA (b : Bytes) : ByteArray := ⟨b.toArray⟩
def toL (b : ByteArray) : Bytes := b.toList
/-- A byte string as a function (zero beyond the end). -/
def fnOf (b : ByteArray) : ℕ → UInt8 := fun i => if h : i < b.size then b[i] else 0

/-- An expanded UOV public key. -/
structure UovPk where
  digest : ByteArray
  expanded : ByteArray

namespace UovPk

/-- Bytes of `P1 ‖ P2` for (n, m) = (119, 45): `m·v(v+1)/2 + m·v·m` with `v = 74`. -/
def p12Bytes : ℕ := 45 * (74 * 75 / 2) + 45 * 74 * 45

/-- pqov's `expand_pk` and the vole-mole digest. -/
def ofCompressed (cpk : ByteArray) : UovPk :=
  { digest := SHAKE.shake256 cpk 32
    expanded := Keygen.publicInputs (cpk.extract 0 16) p12Bytes ++ cpk.extract 16 cpk.size }

/-- The public key of a compact secret key (`SecretKey(bytes)`): pqov's key generation
(`Keygen.compressedPk`), then `expand_pk`. -/
def ofSecret (sk : ByteArray) : UovPk := ofCompressed (Keygen.compressedPk sk)

/-- The public map's coefficients (`ℕ → GF256`, zero beyond the end). -/
def map (pk : UovPk) : ℕ → GF256 := fun i =>
  if h : i < pk.expanded.size then ⟨pk.expanded[i]⟩ else 0

def toSpec (pk : UovPk) : UOVKey := ⟨toL pk.digest, pk.map⟩

end UovPk

/-- The coefficients of `Combination(chal2, dst)`. -/
def combinationArr (n : ℕ) (chal2 dst : ByteArray) : Array GF128 :=
  let b := H (chal2 ++ dst) (16 * n)
  (Array.range n).map fun k => gfOfBytes b (16 * k)

/-- `encode_credits`: 8 bytes little-endian. -/
def le64 (v : ℕ) : ByteArray := ⟨(Array.range 8).map fun i => (v / 2 ^ (8 * i)).toUInt8⟩

/-! ## Moussaka -/

def moussakaIssue (t ctxIss : ByteArray) (labelRows := false) : Statement where
  params := { witnessBytes := 256, qsDegree := 9, labelRows }
  dst := toBA (makeDst "mous" 0 'i' '0')
  instEnc := fun _ => toBA (Moussaka.IssueInstance.encode ⟨toL t, toL ctxIss⟩)
  values := fun _ _ w => Moussaka.issueValues (F := GF128) (fun k => fnOf t k.val) (fnOf ctxIss) w

def moussakaRedeem (anchors : List UovPk) (nf ctxIss ctxRed challengeDigest : ByteArray)
    (labelRows := false) : Statement where
  params := { witnessBytes := 343, qsDegree := 9, labelRows }
  dst := toBA (makeDst "mous" 0 'r' '0')
  instEnc := fun _ => toBA (Moussaka.RedeemInstance.encode
    ⟨anchors.map UovPk.toSpec, toL nf, toL ctxIss, toL ctxRed, toL challengeDigest⟩)
  values := fun _ c2 w =>
    UovEval.moussakaRedeemValues (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss) (fnOf ctxRed)
      (combinationArr Moussaka.M c2 (toBA (makeDst "mous" 0 'l' '0'))) w

/-! ## Ratatouille -/

def ratatouilleIssue (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray) (labelRows := false) :
    Statement where
  params := { witnessBytes := 240, qsDegree := 9, labelRows }
  dst := toBA (makeDst "rata" 0 'i' '0')
  instEnc := fun _ => c ++ le64 tInit ++ ctxIss
  values := fun _ _ w => Ratatouille.issueValues (fnOf c) tInit (fnOf ctxIss) w

def ratatouilleSpend (pk : UovPk) (nf : ByteArray) (d : ℕ) (cNext ctxIss : ByteArray)
    (labelRows := false) : Statement where
  params := { witnessBytes := 847, qsDegree := 9, labelRows }
  dst := toBA (makeDst "rata" 0 'p' '0')
  instEnc := fun _ => pk.digest ++ nf ++ le64 d ++ cNext ++ ctxIss
  values := fun _ c2 w =>
    UovEval.ratatouilleSpendValues pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss)
      (combinationArr Ratatouille.uovM c2 (toBA (makeDst "rata" 0 'l' '0'))) w

/-! ## PomFRIT -/

def pomfritParams (labelRows := false) : Params := { witnessBytes := 164, qsDegree := 2, labelRows }

/-- `hash_to_target(pk, sig, chal1, msg)` with the proof layout of `p`: `Spec.PomFRIT.hashToTarget`,
whose field offsets are `main`'s, reads `ũ` and `d[0..M)` at the offsets of `p` instead. -/
def pomfritTarget (p : Params) (dig chal1 sig msg : ByteArray) : ByteArray :=
  let pf : Proof := { params := p, bytes := sig.extract 0 p.proofBytes }
  toBA (shake128B (PomFRIT.targetInput (toL dig) (toL chal1) (toL pf.voleCheck)
    (toL (pf.correction.extract 0 uovM)) (toL msg)) uovM)

-- `main`'s layout is the one `Spec.PomFRIT` hard-codes.
#guard (pomfritParams).proofBytes == PomFRIT.proofBytes &&
  (pomfritParams).field? "vole_check" == some (PomFRIT.offVoleCheck, PomFRIT.voleCheckBytes) &&
  ((pomfritParams).field? "correction").map (·.1) == some PomFRIT.offCorrection

/-- A PomFRIT blind signature `sig = proof ‖ refresher_com ‖ refresher` on `msg`. The proof is
`sig[0 .. proofBytes)` (5323 bytes, or 5579 with dedicated label rows). -/
def pomfritRedeem (pk : UovPk) (sig msg : ByteArray) (labelRows := false) : Statement :=
  let p := pomfritParams labelRows
  let n := p.proofBytes
  let h : ByteArray → ByteArray := fun c1 => pomfritTarget p pk.digest c1 sig msg
  { params := p
    dst := toBA (makeDst "pomf" 0 'p' '0')
    delayed := true
    binder1 := sig.extract n (n + 32)
    binder2 := sig.extract (n + 32) (n + 64)
    instEnc := fun c1 => pk.digest ++ h c1
    values := fun c1 c2 w =>
      let hb := h c1
      UovEval.pomfritRedeemValues 119 45 pk.map (fun k => ⟨fnOf hb k.val⟩)
        (combinationArr 45 c2 (toBA (makeDst "pomf" 0 'l' '0'))) w }

/-- PomFRIT's `verify` (`pomfrit.cpp:219-237`): the refresher commitment, then the proof. -/
def pomfritVerify (T : CrtTables) (pk : UovPk) (sig msg : ByteArray) (labelRows := false) :
    Transcript :=
  let n := (pomfritParams labelRows).proofBytes
  let refresher := sig.extract (n + 32) (n + 64)
  let com := sig.extract n (n + 32)
  if toBA (PomFRIT.commitRefresher (toL refresher)) != com then { error := "refresher_com" }
  else verify T (pomfritRedeem pk sig msg labelRows) (sig.extract 0 n)

end VoleMole.Verifier
