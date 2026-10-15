import VoleMole.Verifier.Verify
import VoleMole.Verifier.CrtGen

/-!
# The VOLEitH prover (executable)

`voleith_vole_gen` followed by `voleith_prove_commit` (`src/voleith.hpp:146-322`), for a
`Statement` of `Verify.lean`, with the C++'s seed derivation, so that the output is the C++'s proof
byte for byte (checked on all KAT proofs by `lake exe prover_vectors`, `ProverKats.lean`). `fao/` is
`subprojects/faest-arch-opt/`. Every hash goes through `Hs : Hashes`.

## Step 1 (`voleGen`)

* `(seed, iv_pre) = H₃(w_prefix ‖ mu₁ ‖ rho ‖ 3)` (32 bytes), `iv = H₄(iv_pre ‖ mu₁ ‖ 4)`.
* BAVC commit (`BAVC.commit`): the GGM tree from `seed`, leaf keys and commitments in spec order,
  `vole_commit_check`.
* ConvertToVOLE, sender side (`vole_commit_impl`, `fao/small_vole.inc`). With `R_j` the PRG output
  of leaf `j` of small VOLE `i` (`prgWords`), the prover's input is `u^{(i)} = Σ_j R_j` (all rows,
  `smallVoleUWords`) and its tags are `v_{p_i + b} = Σ_j j_b R_j`. The latter is exactly the
  verifier's key column at `Δ = 0` (`convertToVoleAt` with all bits `false`: the hidden leaf is leaf
  0, which contributes nothing), so `senderColumns` is that call. The corrections are
  `c_i = u^{(0)} ⊕ u^{(i)}` on the first `VOLE_CORRECTION_ROWS` rows; `u = u^{(0)}`.
* CRT VOLE, sender side (`crt_vole_commit`, `fao/vole_commit.inc:584-612`):
  - gate labels `L0_e = G[e] · v` on the label rows (as the verifier's `gateInputs` at `Δ = 0`) and
    `L1_e = L0_e ⊕ u[o..o+128)` (`lift_and_hash_vq`, `u_prefix`, at the label-row offset `o`);
    `h⁰_e`, `h¹_e` their `H₅` hashes;
  - `v` rows (CRT-lifted on the first `ℓ'` rows), `ṽ_mask[m] = W_TREE·r̃(v)_m ⊕ W_GATE·h⁰_m`: the
    verifier's `crtReconstructWith` at `Δ = 0` with the hashes `h⁰` (`γ = 0`);
  - `u_mask[m] = W_CRT·u_low[m] ⊕ M_tree·u_hi[m]` (`compute_u_mask`), where bit `p_i + t` of
    `u_low[m]` is row `ℓ' + 8m + t` of `u^{(i)}` (`extract_u_low`), and `u_hi[m]` is byte `m` of
    `PRG(seed, iv, 2³¹ − 1)` (`gen_u_hi`, a carry-less product of degree `< 128`);
  - `c_mult[m]` bit `e` = bit `m` of `h⁰_e ⊕ h¹_e`, plus `⟨F[e], u_mask[m]⟩` (`compute_v_gate`).
* `chal1` as the verifier (`chal1` of `Proof.lean`, on the proof written so far).
* VOLE check, sender side (`kos_vole_check_sender`): the VOLEHash of `u` (its bits on the `ℓ'`
  corrected rows as field elements `0`/`1`, and `u_mask`) is `ũ`, of `v` (the lifted rows and
  `v_mask`) is `h_V`. Both are the verifier's `voleHashReceiver` at `Δ' = 0`, which is linear in
  its rows and masks there.
* `d = u ⊕ w` on the witness prefix (dedicated label rows get no `d`).

## Step 2 (`proveCommit`)

* `d` on the rest of the witness, `chal2` (the verifier's `chal2` on the proof written so far).
* QuickSilver. The verifier's check value is `V(Δ') = G(Δ') + Σ_{i=1}^{d−1} ã_{i−1} Δ'^i`, where `G`
  is its check value (`qsCheck`) with `ã = 0` and its keys `q_j = v_j + w_j Δ'`,
  `q_mask[m] = ṽ_mask[m] + u_mask[m] Δ'`. For a satisfying witness `G` is a polynomial of degree
  `< d` in `Δ'` (the constraint values `Δ'^d f_k(q/Δ')` have degree `≤ d` and leading coefficient
  `f_k(w) = 0`). The prover makes `V` constant: `ã_{i−1} = G_i` and `qs_check = G_0`. The C++
  computes these coefficients with its own degree-tracking arithmetic (`quicksilver_state<S, false,
  d>`); since an accepted proof needs `V(Δ') = qs_check` for the `Δ` that `chal3` picks later, they
  are determined uniquely, and here they are obtained by evaluating `G` with the verifier's own
  functions (`qsAt`) at the `d + 1` points `Δ' = 1, …, d + 1` (`samplePt`, the bit patterns of
  the integers) and interpolating (`interpolate`, Newton's divided differences). The prover
  rejects a witness whose top coefficient `G_d` is nonzero (the constraints are not satisfied),
  and checks that the samples lie on the interpolated polynomial.
* Grinding (`grind_and_open`, `fao/vector_com.inc:981-1066`): for `ctr = 0, 1, …` (`findFirst`,
  `grindStep`), `Δ = H₂³(chal2 ‖ qs_check ‖ ã ‖ ctr ‖ 11)` (`ctr` 32-bit little-endian); the first
  `ctr` whose `Δ` has its 8 top bits zero and whose BAVC opening needs at most `T_OPEN = 105`
  seeds wins.
* Opening (`one_tree_bavc::open`, `fao/vector_com.inc:784-854`, `BAVC.openAt`): the 17 hidden
  leaves' commitments, then, walking `n = L − 2, …, 0`, the non-hidden child of every node with
  exactly one hidden child; zero padding.

The proof's fields are assembled in the order of `Params.fieldSizes` (`assemble`).

`Verifier/Bridge/Prover.lean` proves that the verifier accepts what this prover outputs
(`verify_proveCommit`, per relation `*_complete`), assuming the BAVC opening and the CRT masks
are correct (both checked on every proof by `lake exe prover_vectors`).
-/

namespace VoleMole.Verifier

open VoleMole.Arith

namespace BAVC

/-- The hidden nodes for `Δ` (the 17 hidden leaves and their ancestors), and the seeds the
opening reveals, in the order `verify` reads them (walking `n = L − 2, …, 0`, the other child of
every node with exactly one hidden child). -/
def openSeeds (t : Array ByteArray) (delta : ByteArray) : Array ByteArray := Id.run do
  let mut hidden : Array Bool := Array.replicate numNodes false
  for i in [0:tau] do
    hidden := hidden.set! (treePos i (deltaIndex delta i)) true
  let mut seeds : Array ByteArray := #[]
  for m in [0:numLeaves - 1] do
    let n := numLeaves - 2 - m
    let l := hidden[2 * n + 1]!
    let r := hidden[2 * n + 2]!
    hidden := hidden.set! n (l || r)
    if l != r then seeds := seeds.push t[if l then 2 * n + 2 else 2 * n + 1]!
  return seeds

/-- `one_tree_bavc::open`: the opening of the tree `t` (with leaf commitments `coms`, spec order)
at `Δ`, or `none` if it needs more than `T_OPEN = 105` seeds. -/
def openAt (t : Array ByteArray) (coms delta : ByteArray) : Option ByteArray :=
  let seeds := openSeeds t delta
  if seeds.size > 105 then none
  else
    let hidden := (List.range tau).foldl (fun acc i =>
      let j := leafOffset i + deltaIndex delta i
      acc ++ coms.extract (hashLen * j) (hashLen * j + hashLen)) ByteArray.empty
    let body := seeds.foldl (· ++ ·) hidden
    some (body ++ ⟨Array.replicate (openSize - body.size) 0⟩)

end BAVC

namespace Prover

/-! ## Small helpers -/

/-- `n` zero bytes. -/
def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- Parity of a 64-bit word. -/
@[inline] def parity64 (x : UInt64) : Bool := Id.run do
  let mut v := x
  for s in [32, 16, 8, 4, 2, 1] do
    v := v ^^^ (v >>> s.toUInt64)
  return v &&& 1 == 1

/-- `⟨a, b⟩` over `F₂`. -/
@[inline] def dot (a b : W128) : Bool := parity64 ((a.lo &&& b.lo) ^^^ (a.hi &&& b.hi))

/-- Bit `j` of a byte string (bit `j % 8` of byte `j / 8`). -/
@[inline] def bitOf (b : ByteArray) (j : Nat) : Bool :=
  (b.get! (j / 8) >>> (j % 8).toUInt8) &&& 1 == 1

@[inline] def W128.ofGF (a : GF128) : W128 := ⟨a.lo, a.hi⟩

/-- Field elements as bytes (16 each, little-endian, as `gfToBytes`). -/
def gfsToBytes (xs : Array GF128) : ByteArray :=
  bytesOfWords (xs.toList.flatMap fun x => [x.lo, x.hi]).toArray

/-- The first `f c ≠ none` for `c = c₀, c₀ + 1, …` (at most `fuel` tries). -/
def findFirst {α : Type} (f : Nat → Option α) : Nat → Nat → Option α
  | 0, _ => none
  | fuel + 1, c => match f c with
    | some a => some a
    | none => findFirst f fuel (c + 1)

/-- `F` (312 rows over `u ∈ F₂¹²⁸`) and `M_tree = Π M_i` (degree 120), from `CrtData`. -/
def fRows : Array W128 := CrtGen.F.map CrtGen.w128OfNat
def mTree : Nat := CrtGen.hexNat CrtData.mTreeHex

/-! ## ConvertToVOLE and the CRT VOLE, sender side -/

/-- The prover's input `u^{(i)} = Σ_j R_j` of small VOLE `i` (all leaves, all rows). -/
def smallVoleUWords (p : Params) (iv : ByteArray) (i : Nat) (key : Nat → ByteArray) :
    Array UInt64 :=
  (List.range (2 ^ BAVC.kOf i)).foldl (fun acc j => xorWords acc (prgWords p iv i (key j)))
    (zeroCol p)

/-- The prover's tag columns `v_{p_i + b} = Σ_j j_b R_j`: the verifier's columns at `Δ = 0`. -/
def senderColumns (p : Params) (iv : ByteArray) (key : Nat → Nat → ByteArray) :
    Array (Array UInt64) :=
  convertToVoleAt p (fun _ => false) (fun _ => ByteArray.empty) iv key

/-- The correction `c_i = u^{(0)} ⊕ u^{(i)}` on the first `VOLE_CORRECTION_ROWS` rows. -/
def correctionOf (p : Params) (u0 ui : Array UInt64) : ByteArray :=
  (bytesOfWords (xorWords u0 ui)).extract 0 p.correctionBytes

/-- The inputs `iv ‖ e ‖ (L0_e ⊕ off) ‖ 5` of the gate hashes (`off = 0`: the verifier's
`gateInputs`; `off = u` on the label rows: the other label). -/
def gateInputsOff (p : Params) (T : CrtTables) (iv : ByteArray) (cols : Array (Array UInt64))
    (off : W128) : List ByteArray :=
  let o := p.labelRowOffset
  let tops : Array W128 :=
    (Array.range 120).map fun c => ⟨wordAt cols[c]! o, wordAt cols[c]! (o + 64)⟩
  (List.range p.nMult).map fun e =>
    (AES.pushLE32 iv e.toUInt32 ++
      ((W128.rowMul (fun c => wbit T.g[c]! e) 120 tops).xor off).toBytes).push 5

/-- `u_mask[m] = W_CRT · u_low[m] ⊕ M_tree · u_hi[m]` (`compute_u_mask`), from the prover's inputs
`us i = u^{(i)}` and the root seed. -/
def uMaskOf (p : Params) (T : CrtTables) (seed iv : ByteArray) (us : Array (Array UInt64)) :
    Array W128 :=
  let ell := p.correctionRows
  let hi := AES.prg seed iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128)
  (Array.range p.nMask).map fun m =>
    let low : Nat → Bool := fun c =>
      let i := BAVC.treeOf c
      wbit us[i]! (ell + 8 * m + (c - BAVC.bitOffset i))
    (W128.rowMul low 120 T.wCrt).xor (CrtGen.w128OfNat (CrtGen.pmul (hi.get! m).toNat mTree))

/-- `c_mult` (`compute_v_gate`): bit `e` of row `m` is bit `m` of `h⁰_e ⊕ h¹_e`, plus
`⟨F[e], u_mask[m]⟩`; `N_MULT_BYTES = 39` bytes per row. -/
def cMultOf (p : Params) (h0 h1 : Array UInt32) (uMask : Array W128) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (p.nMask * p.nMultBytes)
  for m in [0:p.nMask] do
    for k in [0:p.nMultBytes] do
      let mut byte : UInt8 := 0
      for b in [0:8] do
        let e := 8 * k + b
        let bit := (((h0[e]! ^^^ h1[e]!) >>> m.toUInt32) &&& 1 == 1) ^^ dot fRows[e]! uMask[m]!
        if bit then byte := byte ||| ((1 : UInt8) <<< b.toUInt8)
      out := out.push byte
  return out

/-! ## Proof assembly -/

/-- The proof fields, in the order of `Params.fieldSizes`. -/
structure Fields where
  corrections : ByteArray
  cmult : ByteArray
  voleCheck : ByteArray
  correction : ByteArray
  qsProof : ByteArray
  opening : ByteArray
  delta : ByteArray
  ivPre : ByteArray
  ctr : ByteArray

/-- `b`, zero-padded or truncated to `n` bytes. -/
def fit (b : ByteArray) (n : Nat) : ByteArray := (b ++ zeros (n - b.size)).extract 0 n

/-- The fields, each fitted to its size (`Params.fieldSizes`). -/
def fieldList (p : Params) (f : Fields) : List ByteArray :=
  [fit f.corrections (16 * p.correctionBytes), fit f.cmult (p.nMask * p.nMultBytes),
   fit f.voleCheck 64, fit f.correction p.witnessBytes, fit f.qsProof ((p.qsDegree - 1) * 16),
   fit f.opening BAVC.openSize, fit f.delta 16, fit f.ivPre 16, fit f.ctr 4]

/-- The proof bytes: the fields, each zero-padded or truncated to its size, in order. -/
def assemble (p : Params) (f : Fields) : ByteArray := (fieldList p f).foldl (· ++ ·) ByteArray.empty

/-! ## Interpolation over `GF(2¹²⁸)` -/

/-- Coefficients (constant term first) of `a(X) · (X + c)`. -/
def mulLinear (a : Array GF128) (c : GF128) : Array GF128 :=
  (Array.range (a.size + 1)).map fun i =>
    (if i < a.size then a[i]! * c else 0) + (if 0 < i then a[i - 1]! else 0)

/-- The polynomial of degree `< n` through `(xs[k], ys[k])`, `k < n` (Newton's divided
differences; the `xs` distinct). Coefficients, constant term first. -/
def interpolate (xs ys : Array GF128) : Array GF128 := Id.run do
  let n := xs.size
  let mut dd := ys
  for j in [1:n] do
    for s in [0:n - j] do
      let i := n - 1 - s
      dd := dd.set! i ((dd[i]! + dd[i - 1]!) * gfInv (xs[i]! + xs[i - j]!))
  let mut poly : Array GF128 := #[dd[n - 1]!]
  for s in [1:n] do
    let i := n - 1 - s
    poly := mulLinear poly xs[i]!
    poly := poly.set! 0 (poly[0]! + dd[i]!)
  return poly

/-- `Σ_i a_i x^i`. -/
def evalPoly (a : Array GF128) (x : GF128) : GF128 := a.foldr (fun c acc => acc * x + c) 0

/-! ## The two steps -/

/-- The prover's state between the steps (`PendingProof`), and the proof bytes written so far. -/
structure Pending where
  params : Params
  seed : ByteArray
  iv : ByteArray
  ivPre : ByteArray
  /-- The GGM tree and the leaves (keys and commitments, spec order). -/
  tree : Array ByteArray
  leaves : BAVC.Leaves
  /-- `u = u^{(0)}`, as a column. -/
  u : Array UInt64
  /-- The tags of the first `ℓ'` rows, CRT-lifted, and `ṽ_mask`, `u_mask`. -/
  vRows : Array W128
  vMask : Array W128
  uMask : Array W128
  chal1 : ByteArray
  hV : Array GF128
  /-- The witness prefix. -/
  wPrefix : ByteArray
  /-- The fields written by step 1. -/
  fields : Fields

/-- **Step 1** (`voleith_vole_gen`): commit to the VOLE, `chal1`, the VOLE check, and `d` on the
witness prefix `wPrefix`. `mu1` is `Statement.mu1` (`H₂⁰(inst ‖ DST ‖ 8)`, or `H₂⁴(DST ‖ 12)` for
delayed instance binding), `rho` the prover's 16-byte randomness, `binder1` the `chal1` binder. -/
def voleGen (Hs : Hashes) (T : CrtTables) (p : Params) (mu1 wPrefix rho binder1 : ByteArray) :
    Pending :=
  let h3 := Hs.hash .h3 ((wPrefix ++ mu1 ++ rho).push 3)
  let seed := h3.extract 0 16
  let ivPre := h3.extract 16 32
  let iv := Hs.hash .h4 ((ivPre ++ mu1).push 4)
  let tl := BAVC.commit seed iv
  let tree := tl.1
  let leaves := tl.2
  let check := BAVC.check (Hs.hash .h1) leaves.coms
  let key := leafKey leaves
  -- ConvertToVOLE.
  let us : Array (Array UInt64) :=
    (Array.range BAVC.tau).map fun i => smallVoleUWords p iv i (key i)
  let u := us[0]!
  let cols := senderColumns p iv key
  let corrections := (List.range (BAVC.tau - 1)).foldl
    (fun acc i => acc ++ correctionOf p u us[i + 1]!) ByteArray.empty
  -- CRT VOLE.
  let uPre : W128 := ⟨wordAt u p.labelRowOffset, wordAt u (p.labelRowOffset + 64)⟩
  let h0 := gateWords ((Prover.gateInputsOff p T iv cols W128.zero).map (Hs.hash .h5))
  let h1 := gateWords ((Prover.gateInputsOff p T iv cols uPre).map (Hs.hash .h5))
  let vOut := crtReconstructWith h0 p (fun _ => false) ByteArray.empty T cols
  let uMask := uMaskOf p T seed iv us
  let cmult := cMultOf p h0 h1 uMask
  -- chal1.
  let f0 : Fields :=
    { corrections := corrections, cmult := cmult, voleCheck := .empty, correction := .empty,
      qsProof := .empty, opening := .empty, delta := .empty, ivPre := ivPre, ctr := .empty }
  let c1 := chal1 Hs { params := p, bytes := assemble p f0 } mu1 check binder1
  -- VOLE check.
  let uRows : Array W128 := (Array.range p.correctionRows).map fun r =>
    if wbit u r then ⟨1, 0⟩ else W128.zero
  let uTilde := voleHashReceiver p c1 uRows uMask 0 (zeros 64)
  let hV := voleHashReceiver p c1 vOut.rows vOut.qMask 0 (zeros 64)
  let voleCheck := gfsToBytes uTilde
  -- d on the prefix.
  let ub := bytesOfWords u
  let correction : ByteArray :=
    ⟨(Array.range wPrefix.size).map fun k => ub.get! k ^^^ wPrefix.get! k⟩
  { params := p, seed := seed, iv := iv, ivPre := ivPre, tree := tree, leaves := leaves, u := u,
    vRows := vOut.rows, vMask := vOut.qMask, uMask := uMask, chal1 := c1, hV := hV,
    wPrefix := wPrefix, fields := { f0 with voleCheck := voleCheck, correction := correction } }

/-- The proof bytes written by step 1 (`ũ`, `d` on the prefix, and the VOLE commitment; the rest
zero). PomFRIT's `hash_to_target` reads `ũ` and `d[0..M)` from them. -/
def Pending.proof (s : Pending) : ByteArray := assemble s.params s.fields

/-- The verifier's witness keys `q_j = v_j + w_j x` at `Δ' = x`, `j < ℓ`. -/
def qsKeys (p : Params) (vRows : Array W128) (w : ByteArray) (x : GF128) : Array GF128 :=
  (Array.range p.witnessBits).map fun j => vRows[j]!.toGF + (if bitOf w j then x else 0)

/-- The verifier's masks `q_mask[m] = ṽ_mask[m] + u_mask[m] x` at `Δ' = x`. -/
def qsMasks (p : Params) (vMask uMask : Array W128) (x : GF128) : Array W128 :=
  (Array.range p.nMask).map fun m => W128.ofGF (vMask[m]!.toGF + uMask[m]!.toGF * x)

/-- `G(x)`: the verifier's QuickSilver check value at `Δ' = x`, with the `ã` of `pf0`. -/
def qsAt (pf0 : Proof) (chal2 : ByteArray) (values : (Nat → GF128) → List GF128)
    (vRows vMask uMask : Array W128) (w : ByteArray) (x : GF128) : GF128 :=
  let p := pf0.params
  qsCheck pf0 chal2 (constraintKeys p (qsKeys p vRows w x) x values) (qsMasks p vMask uMask x) x

/-- The sample point `k + 1` (as a field element, the bit pattern of the integer). -/
def samplePt (k : Nat) : GF128 := ⟨(k + 1).toUInt64, 0⟩

/-- The QuickSilver coefficients: `(qs_check, ã)`, or an error if the witness does not satisfy
the constraints. `pf0` is the proof with `ã = 0`. -/
def qsProve (pf0 : Proof) (chal2 : ByteArray) (values : (Nat → GF128) → List GF128)
    (vRows vMask uMask : Array W128) (w : ByteArray) : Except String (GF128 × Array GF128) := do
  let d := pf0.params.qsDegree
  let xs := (Array.range (d + 1)).map samplePt
  let ys := xs.map (qsAt pf0 chal2 values vRows vMask uMask w)
  let g := interpolate xs ys
  if g.size != d + 1 then throw "QuickSilver: interpolation failed"
  if g[d]! != 0 then throw "QuickSilver: the witness does not satisfy the constraints"
  if !(List.range (d + 1)).all fun k => evalPoly g xs[k]! == ys[k]! then
    throw "QuickSilver: interpolation failed"
  return (g[0]!, (Array.range (d - 1)).map fun i => g[i + 1]!)

/-- One grinding attempt: `Δ = H₂³(pre ‖ ctr ‖ 11)`, accepted if its 8 top bits are zero and the
opening at `Δ` fits. -/
def grindStep (Hs : Hashes) (s : Pending) (pre : ByteArray) (ctr : Nat) :
    Option (Nat × ByteArray × ByteArray) :=
  let delta := Hs.hash .h23 ((AES.pushLE32 pre ctr.toUInt32).push 11)
  if delta.get! 15 == 0 then (BAVC.openAt s.tree s.leaves.coms delta).map fun o => (ctr, delta, o)
  else none

/-- **Step 2** (`voleith_prove_commit`): `d` on the witness suffix `wSuffix`, `chal2`, QuickSilver,
grinding and the opening, for the statement `st` (whose `params`, binders, `values` and, for
delayed instance binding, instance are used; `mu1` was fixed in step 1). -/
def proveCommit (Hs : Hashes) (st : Statement) (wSuffix : ByteArray) (s : Pending) :
    Except String ByteArray := do
  let p := s.params
  let w := s.wPrefix ++ wSuffix
  if w.size != p.witnessBytes then throw "witness: wrong length"
  let ub := bytesOfWords s.u
  let correction : ByteArray := ⟨(Array.range p.witnessBytes).map fun k => ub.get! k ^^^ w.get! k⟩
  let f1 := { s.fields with correction := correction }
  let pf1 : Proof := { params := p, bytes := assemble p f1 }
  let c2 := chal2 Hs pf1 s.chal1 s.hV (st.muDelayed Hs s.chal1) st.binder2
  let values := st.values s.chal1 (st.combBytes Hs c2)
  let (check, aT) ← qsProve pf1 c2 values s.vRows s.vMask s.uMask w
  let qsProof := gfsToBytes aT
  -- Grinding.
  let pre := c2 ++ gfToBytes check ++ qsProof
  let some (ctr, delta, opening) := findFirst (grindStep Hs s pre) (2 ^ 32) 0
    | throw "grinding failed"
  return assemble p
    { f1 with qsProof := qsProof, opening := opening, delta := delta,
              ctr := AES.pushLE32 ByteArray.empty ctr.toUInt32 }

/-- **The prover** for a statement without delayed instance binding: step 1 with the first
`prefixBytes` bytes of the witness `w` (`WITNESS_PREFIX_BYTES`), then step 2. -/
def prove (Hs : Hashes) (T : CrtTables) (st : Statement) (w rho : ByteArray)
    (prefixBytes : Nat := st.params.witnessBytes) : Except String ByteArray :=
  proveCommit Hs st (w.extract prefixBytes w.size)
    (voleGen Hs T st.params (st.mu1 Hs) (w.extract 0 prefixBytes) rho st.binder1)

end Prover

end VoleMole.Verifier
