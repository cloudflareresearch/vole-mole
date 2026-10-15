import VoleMole.Verifier.Proof

/-!
# ConvertToVOLE and the CRT VOLE reconstruction (executable)

The verifier's VOLE keys, from the BAVC leaves (`BAVC.reconstruct`, spec order) to the rows `q`
and masks `q_mask` that the VOLE check and QuickSilver consume (`crt_vole_reconstruct`,
`fao/vole_commit.inc:614-651`; `fao/` is `subprojects/faest-arch-opt/`).

## ConvertToVOLE (`vole_reconstruct_impl`, `fao/vole_commit.inc:137-191`; `fao/small_vole.inc`)

Small VOLE `i` (`k = k_i` bits of `Δ`, starting at bit `p_i`) has leaf keys `r_j`, `j < 2^k`, the
hidden one `j = Δ_i` unknown. With `R_j = PRG(r_j, iv, tweak 2³¹ + i)` (`VOLE_COL_BLOCKS` blocks,
counter 0), column `p_i + b` (`b < k`) of the verifier's key matrix is

  `q_{p_i + b} = Δ_{i,b} · c_i + Σ_{j ≠ Δ_i} (j ⊕ Δ_i)_b · R_j`,

where `c_i` (`i ≥ 1`; `c_0 = 0`) is the correction from the proof on the first `ℓ'` rows
(`ℓ' = VOLE_CORRECTION_ROWS`: `ℓ`, or `ℓ + 128` with dedicated label rows), zero below.
Columns `120 … 127` (the zero bits of `Δ`) are zero. faest-arch-opt computes the same sum over its
permuted leaf order with Gray-code accumulation (`xor_reduce`, `process_prg_output`); here it is
written out directly (`treeColumns`, one fold per column over the `R_j`, each computed once). A
column is a bit vector over rows (row `r` = bit `r % 8` of byte `r / 8`).

The steps take `Δ` as its bits (`BAVC.deltaBit`, `c < 120`) and the commitments as separate
arguments (`convertToVoleAt`, `crtReconstructAt`; `convertToVole`, `crtReconstruct` read them off a
proof), so that `Bridge/Columns.lean` can treat them as functions of the challenge with the
commitments fixed.

## The CRT step

* Gate labels and hashes (`lift_and_hash_vq`, `vole_commit.inc:339-432`): `L_e = Σ_{c < 120}
  G[c][e] · q_c[o..o+128)` for `e < N_MULT` (the 128 label rows of each column, as a block; `o` is
  `Params.labelRowOffset`: `0` on `main`, `ℓ` with dedicated label rows, patch 0005's
  `crt_labels`), and `h_e` = the first 4 bytes of `H₅(iv ‖ e (u32 LE) ‖ L_e ‖ 5)`.
* Rows: row `r` of the key matrix is the 128-bit vector whose bit `c` is bit `r` of column `c`. The
  first `ℓ'` rows are CRT-lifted, `q_r = row_r · W_CRT` (`crt_lift_q`; a row vector times a
  120 × 128 matrix over GF(2)); the mask rows `ℓ' + 8m + t` are used unlifted.
* `r̃_m` (`compute_r_tilde`, `vole_commit.inc:284-335`): for small VOLE `i`,
  `Σ_{t < k_i} x_{m,t,i} · X^t mod M_i`, where `x_{m,t,i}` is bits `p_i … p_i + k_i − 1` of mask row
  `ℓ' + 8m + t` as a polynomial, written back to bits `p_i …` of `r̃_m`.
* `q_mask[m] = r̃_m · W_TREE + (H_m ⊕ (γ ∧ c_mult[m])) · W_GATE`, where bit `e` of `H_m` is bit `m` of
  `h_e` and `γ = Δ · G` (`compute_q_mask`, `compute_q_gate`, `vole_commit.inc:500-549`).
* `crt_lift_delta(Δ) = Δ · W_CRT`.

The matrices `G`, `W_CRT`, `W_TREE`, `W_GATE` and the moduli `M_i` are faest-arch-opt's generated
tables for `(s128, τ = 17, 120)` (`fao/tools/gen_crt_tables.py`), from `CrtData.lean`.
-/

namespace VoleMole.Verifier

/-- A 128-bit block: `lo` = bits 0-63, `hi` = bits 64-127 (bytes little-endian). -/
structure W128 where
  lo : UInt64
  hi : UInt64
  deriving BEq, Inhabited, Repr

namespace W128

def zero : W128 := ⟨0, 0⟩

@[inline] def xor (a b : W128) : W128 := ⟨a.lo ^^^ b.lo, a.hi ^^^ b.hi⟩

@[inline] def and (a b : W128) : W128 := ⟨a.lo &&& b.lo, a.hi &&& b.hi⟩

/-- Bit `i` (`< 128`). -/
@[inline] def bit (a : W128) (i : Nat) : Bool :=
  if i < 64 then (a.lo >>> i.toUInt64) &&& 1 == 1 else (a.hi >>> (i - 64).toUInt64) &&& 1 == 1

/-- Little-endian word of 8 bytes at `off`. -/
@[inline] def word (b : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut w : UInt64 := 0
  for j in [0:8] do
    w := w ||| ((b.get! (off + j)).toUInt64 <<< (8 * j).toUInt64)
  return w

def ofBytes (b : ByteArray) (off : Nat := 0) : W128 := ⟨word b off, word b (off + 8)⟩

def pushWord (out : ByteArray) (w : UInt64) : ByteArray := Id.run do
  let mut o := out
  for j in [0:8] do
    o := o.push (w >>> (8 * j).toUInt64).toUInt8
  return o

def toBytes (a : W128) : ByteArray := pushWord (pushWord ByteArray.empty a.lo) a.hi

/-- `Σ_{i < n, bit i of x} M[i]`: the row vector `x` times the matrix with rows `M`. -/
def rowMul (x : Nat → Bool) (n : Nat) (M : Array W128) : W128 := Id.run do
  let mut acc := zero
  for i in [0:n] do
    if x i then acc := acc.xor M[i]!
  return acc

end W128

/-- The generated CRT tables. -/
structure CrtTables where
  /-- `M_i`, `i < 17` (bit `j` = coefficient of `X^j`). -/
  mI : Array UInt64
  /-- `W_CRT`: 120 rows. -/
  wCrt : Array W128
  /-- `W_TREE`: 120 rows. -/
  wTree : Array W128
  /-- `W_GATE`: `N_MULT` rows. -/
  wGate : Array W128
  /-- `G`: 120 rows of `N_MULT` bits (5 words each). -/
  g : Array (Array UInt64)

/-- Bit `r` of a bit vector stored as words. -/
@[inline] def wbit (w : Array UInt64) (r : Nat) : Bool := (w[r / 64]! >>> (r % 64).toUInt64) &&& 1 == 1

/-- Bits `o … o + 63` of a bit vector stored as words (zero beyond the end). -/
@[inline] def wordAt (w : Array UInt64) (o : Nat) : UInt64 :=
  let s := o % 64
  if s == 0 then w.getD (o / 64) 0
  else (w.getD (o / 64) 0 >>> s.toUInt64) ||| (w.getD (o / 64 + 1) 0 <<< (64 - s).toUInt64)

/-- A byte string as little-endian words (length a multiple of 8). -/
def wordsOf (b : ByteArray) : Array UInt64 :=
  (Array.range (b.size / 8)).map fun i => W128.word b (8 * i)

def bytesOfWords (w : Array UInt64) : ByteArray := w.foldl W128.pushWord ByteArray.empty

/-- `a ⊕ b` on word arrays (the length of `a`; `b` read as zero beyond its end). -/
@[inline] def xorWords (a b : Array UInt64) : Array UInt64 := a.mapIdx fun i x => x ^^^ b[i]!

/-- A zero column (`colBytes / 8` words). -/
def zeroCol (p : Params) : Array UInt64 := Array.replicate (p.colBytes / 8) 0

/-- The correction `c_i` of small VOLE `i` as a column (zero for `i = 0`, zero-padded below). -/
def corrWords (p : Params) (i : Nat) (corr : ByteArray) : Array UInt64 :=
  if i == 0 then zeroCol p else wordsOf (corr ++ ⟨Array.replicate (p.colBytes - corr.size) 0⟩)

/-- `R = PRG(key, iv, 2³¹ + i)`, `VOLE_COL_BLOCKS` blocks, as a column. -/
def prgWords (p : Params) (iv : ByteArray) (i : Nat) (key : ByteArray) : Array UInt64 :=
  wordsOf (AES.prg key iv (((1 : UInt32) <<< 31) + i.toUInt32) 0 p.voleColBlocks)

/-- `R_j` for the leaves `j < 2^{k_i}` of small VOLE `i`, except the hidden one `dI` (zero). -/
def prgOuts (p : Params) (iv : ByteArray) (i dI : Nat) (key : Nat → ByteArray) :
    Array (Array UInt64) :=
  (Array.range (2 ^ BAVC.kOf i)).map fun j => if j == dI then zeroCol p else prgWords p iv i (key j)

/-- The `k_i` key columns of small VOLE `i` (`q_{p_i + b}`, `b < k_i`), from its hidden index
`dI`, its correction `corr` (`c_i`, bytes) and its leaf keys `key j`:
`q_{p_i + b} = dI_b · c_i + Σ_{j ≠ dI} (j ⊕ dI)_b · R_j`. The PRG outputs `R_j` are computed once
per leaf; the hidden leaf's key is never read. -/
def treeColumns (p : Params) (iv : ByteArray) (i dI : Nat) (corr : ByteArray)
    (key : Nat → ByteArray) : Array (Array UInt64) :=
  let prgOut := prgOuts p iv i dI key
  (Array.range (BAVC.kOf i)).map fun b =>
    (List.range (2 ^ BAVC.kOf i)).foldl
      (fun acc j => if j != dI && (j ^^^ dI).testBit b then xorWords acc prgOut[j]! else acc)
      (if dI.testBit b then corrWords p i corr else zeroCol p)

/-- The verifier's 128 key columns (`colBytes / 8` words each) before the CRT lift, from the bits
`dbit c` of `Δ`, the corrections `corr i` and the leaf keys `key i j` (leaf `j` of vector `i`). -/
def convertToVoleAt (p : Params) (dbit : Nat → Bool) (corr : Nat → ByteArray) (iv : ByteArray)
    (key : Nat → Nat → ByteArray) : Array (Array UInt64) :=
  let trees : Array (Array (Array UInt64)) := (Array.range BAVC.tau).map fun i =>
    treeColumns p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i)
  (Array.range 128).map fun c =>
    if c < 120 then trees[BAVC.treeOf c]![c - BAVC.bitOffset (BAVC.treeOf c)]! else zeroCol p

/-- Leaf `j` of vector `i` (16 bytes). -/
def leafKey (leaves : BAVC.Leaves) (i j : Nat) : ByteArray :=
  leaves.keys.extract (16 * (BAVC.leafOffset i + j)) (16 * (BAVC.leafOffset i + j) + 16)

/-- The verifier's 128 key columns (`colBytes / 8` words each) before the CRT lift. -/
def convertToVole (pf : Proof) (iv : ByteArray) (leaves : BAVC.Leaves) : Array (Array UInt64) :=
  convertToVoleAt pf.params (BAVC.deltaBit pf.delta) pf.correctionOf iv (leafKey leaves)

/-- The columns as bytes, concatenated (the dump's `q_columns`). -/
def columnsBytes (cols : Array (Array UInt64)) : ByteArray :=
  cols.foldl (fun acc c => acc ++ bytesOfWords c) ByteArray.empty

/-- Row `r` of the key matrix. -/
def rowOf (cols : Array (Array UInt64)) (r : Nat) : W128 := Id.run do
  let mut lo : UInt64 := 0
  let mut hi : UInt64 := 0
  for c in [0:64] do
    if wbit cols[c]! r then lo := lo ||| ((1 : UInt64) <<< c.toUInt64)
    if wbit cols[c + 64]! r then hi := hi ||| ((1 : UInt64) <<< c.toUInt64)
  return ⟨lo, hi⟩

/-- `M_i`-reduction of a GF(2) polynomial (both as words). -/
def polyMod (x m : UInt64) : UInt64 := Id.run do
  let deg := m.toNat.log2
  let mut x := x
  for s in [0:64] do
    let b := 63 - s
    if b ≥ deg && (x >>> b.toUInt64) &&& 1 == 1 then x := x ^^^ (m <<< (b - deg).toUInt64)
  return x

/-- The inputs `iv ‖ e (u32 LE) ‖ L_e ‖ 5` of the gate hashes, `e < N_MULT`. -/
def gateInputs (p : Params) (T : CrtTables) (iv : ByteArray) (cols : Array (Array UInt64)) :
    List ByteArray :=
  -- The 128 label rows of each column, as a block.
  let o := p.labelRowOffset
  let tops : Array W128 := (Array.range 120).map fun c => ⟨wordAt cols[c]! o, wordAt cols[c]! (o + 64)⟩
  (List.range p.nMult).map fun e =>
    (AES.pushLE32 iv e.toUInt32 ++ (W128.rowMul (fun c => wbit T.g[c]! e) 120 tops).toBytes).push 5

/-- The gate hashes `h_e` (as 32-bit words), from the `H₅` answers to `gateInputs`. -/
def gateWords (hs : List ByteArray) : Array UInt32 := (hs.map fun h => AES.getLE32 h 0).toArray

/-- The gate hashes `h_e` (as 32-bit words), with `h5` = `H₅`. -/
def gateHashes (h5 : ByteArray → ByteArray) (p : Params) (T : CrtTables) (iv : ByteArray)
    (cols : Array (Array UInt64)) : Array UInt32 :=
  gateWords ((gateInputs p T iv cols).map h5)

/-- Output of the CRT reconstruction. -/
structure CrtOut where
  hashes : Array UInt32
  rTilde : Array W128
  /-- The first `ℓ'` (`VOLE_CORRECTION_ROWS`) rows, CRT-lifted (before the correction `d`). -/
  rows : Array W128
  qMask : Array W128
  deltaLifted : W128

/-- `γ = Δ · G`, from the bits `dbit c` (`c < 120`) of `Δ`. -/
def gammaOf (T : CrtTables) (dbit : Nat → Bool) : Array UInt64 :=
  (List.range 120).foldl (fun acc c => if dbit c then xorWords acc T.g[c]! else acc)
    (Array.replicate 5 0)

/-- `r̃_m` from the 8 mask rows `src` of mask `m`. -/
def rTildeOf (T : CrtTables) (src : Array W128) : W128 := Id.run do
  let mut rt := W128.zero
  for i in [0:BAVC.tau] do
    let k := BAVC.kOf i
    let o := BAVC.bitOffset i
    let mut x : UInt64 := 0
    for t in [0:k] do
      let mut bits : UInt64 := 0
      for b in [0:k] do
        if src[t]!.bit (o + b) then bits := bits ||| ((1 : UInt64) <<< b.toUInt64)
      x := x ^^^ (bits <<< t.toUInt64)
    let red := polyMod x T.mI[i]!
    for b in [0:k] do
      if (red >>> b.toUInt64) &&& 1 == 1 then
        let pos := o + b
        rt := if pos < 64 then { rt with lo := rt.lo ||| ((1 : UInt64) <<< pos.toUInt64) }
          else { rt with hi := rt.hi ||| ((1 : UInt64) <<< (pos - 64).toUInt64) }
  return rt

/-- `crt_vole_reconstruct` after the plain reconstruction and the gate hashes, and
`crt_lift_delta`, from the gate hashes `hashes`, the bits `dbit c` (`c < 120`) of `Δ` and `c_mult`.
Lifted row `r` is `Σ_{c < 120} q_c[r] · W_CRT[c]`. -/
def crtReconstructWith (hashes : Array UInt32) (p : Params) (dbit : Nat → Bool)
    (cmult : ByteArray) (T : CrtTables) (cols : Array (Array UInt64)) : CrtOut :=
  let ell := p.correctionRows
  let rows : Array W128 := (Array.range ell).map fun r =>
    W128.rowMul (fun c => wbit cols[c]! r) 120 T.wCrt
  let gamma := gammaOf T dbit
  let rTilde : Array W128 := (Array.range p.nMask).map fun m =>
    rTildeOf T ((Array.range 8).map fun t => rowOf cols (ell + 8 * m + t))
  let qMask : Array W128 := (Array.range p.nMask).map fun m =>
    let cm := cmult.extract (m * p.nMultBytes) ((m + 1) * p.nMultBytes)
    let gateRow : Nat → Bool := fun e =>
      ((hashes[e]! >>> m.toUInt32) &&& 1 == 1) ^^
        (wbit gamma e && (cm.get! (e / 8) >>> (e % 8).toUInt8) &&& 1 == 1)
    (W128.rowMul rTilde[m]!.bit 120 T.wTree).xor (W128.rowMul gateRow p.nMult T.wGate)
  { hashes, rTilde, rows, qMask, deltaLifted := W128.rowMul dbit 120 T.wCrt }

/-- `crt_vole_reconstruct` after the plain reconstruction, and `crt_lift_delta`, from the bits
`dbit c` (`c < 120`) of `Δ` and `c_mult`, with `h5` = `H₅` for the gate hashes. -/
def crtReconstructAt (h5 : ByteArray → ByteArray) (p : Params) (dbit : Nat → Bool)
    (cmult : ByteArray) (T : CrtTables) (iv : ByteArray) (cols : Array (Array UInt64)) : CrtOut :=
  crtReconstructWith (gateHashes h5 p T iv cols) p dbit cmult T cols

/-- `crt_vole_reconstruct` after the plain reconstruction, and `crt_lift_delta`. -/
def crtReconstruct (Hs : Hashes) (pf : Proof) (T : CrtTables) (iv : ByteArray)
    (cols : Array (Array UInt64)) : CrtOut :=
  crtReconstructAt (Hs.hash .h5) pf.params (BAVC.deltaBit pf.delta) pf.cmult T iv cols

end VoleMole.Verifier
