import VoleMole.Verifier.AES
import VoleMole.Spec.SHAKE

/-!
# pqov key generation (uov-Ip-pkc), executable

vole-mole's `SecretKey` (`src/uov/uov.cpp:52-60`) derives its compressed public key from the
32-byte secret seed with pqov's `generate_keypair_pkc` (`subprojects/pqov/src/ov_keypair.c`,
built with `-D_OV256_119_45 -D_OV_PKC`, so `n = 119`, `m = o = 45`, `v = 74`, GF(256)):

* `pk_seed ‖ O = SHAKE256(sk_seed)`, 16 + 74·45 bytes (`hash_init`/`hash_update`/
  `hash_final_digest`, `utils/utils_hash.c`, SHAKE256 by default). `O` is the secret 74×45 matrix,
  stored column by column: `O[k][j]` is byte `74 j + k` (the `B` argument of
  `batch_trimat_madd_gf256` with `size_Bcolvec = 74`).
* `P1 ‖ P2` is the first `m·v(v+1)/2 + m·v·m` bytes of `prng_gen_publicinputs` under `pk_seed`
  (`publicInputs`; two consecutive calls read one AES-128-CTR stream, `utils/utils_prng.c:287-320`).
  `P1` is the upper-triangular `v×v` matrix of 45-byte vectors, entry `(i, k)` (`i ≤ k`) at
  `idx_of_trimat(i, k, v)` (`parallel_matrix_op.h:39-41`); `P2` is the `v×o` matrix of 45-byte
  vectors in row-major order.
* `calculate_F2_P3` (`ov_keypair_computation.c:61-80`): `S = P1·O + P2`
  (`batch_trimat_madd_gf256`, `parallel_matrix_op.c:337-350`), `M = Oᵀ·S` and
  `P3 = UT(M + Mᵀ)`, i.e. entry `(i, j)`, `i ≤ j`, of the upper-triangular `o×o` matrix `P3` is
  `M[i][j] + M[j][i]` for `i < j` and `M[i][i]` on the diagonal
  (`batch_upper_matTr_x_mat_gf256`, `parallel_matrix_op.c:407-422`). The third step
  (`batch_trimatTr_madd`) only updates the secret `S`.
* The compressed public key (`cpk_t`) is `pk_seed ‖ P3`, 16 + 45·45·46/2 bytes.

GF(256) is the AES field (pqov's `gf256_mul`, modulus `x⁸ + x⁴ + x³ + x + 1`), so products are
looked up in a 64 KiB table built from `AES.gmul`. The loops work in place on `ByteArray`s: about
1.2·10⁷ multiply-adds per key. Checked byte for byte against the C++ by `lake exe verifier_vectors`
and `lake exe spec_kats` (`lean/vectors/verifier_keys.txt`, `uov_keys.txt`, when present).
-/

namespace VoleMole.Verifier.Keygen

/-- pqov's `_V`, `_O` (= `_PUB_M`) for uov-Ip. -/
abbrev v : Nat := 74
abbrev o : Nat := 45

/-- `LEN_PKSEED`, `LEN_SKSEED`. -/
abbrev pkSeedBytes : Nat := 16
abbrev skSeedBytes : Nat := 32

/-- `_PK_P1_BYTE`, `_PK_P2_BYTE`, `_PK_P3_BYTE`. -/
abbrev p1Bytes : Nat := o * (v * (v + 1) / 2)
abbrev p2Bytes : Nat := o * v * o
abbrev p3Bytes : Nat := o * (o * (o + 1) / 2)

/-- `OV_PK_COMPRESSED_BYTES`. -/
abbrev cpkBytes : Nat := pkSeedBytes + p3Bytes

/-- `idx_of_trimat(i, j, dim)`: the position of entry `(i, j)`, `i ≤ j`, of an upper-triangular
`dim×dim` matrix stored row by row. -/
@[inline] def idxTri (i j dim : Nat) : Nat := (2 * dim - i + 1) * i / 2 + j - i

#guard idxTri 0 0 v == 0 && idxTri 0 (v - 1) v == v - 1 && idxTri 1 1 v == v &&
  idxTri (v - 1) (v - 1) v + 1 == v * (v + 1) / 2

/-- `prng_gen_publicinputs` from a fresh `prng_set_publicinputs(pk_seed)`: AES-128-CTR under the
16-byte `pk_seed`, zero 12-byte nonce, 32-bit big-endian block counter from 0; the first `n`
bytes. -/
def publicInputs (pkSeed : ByteArray) (n : Nat) : ByteArray := Id.run do
  let rk := AES.expandKey (pkSeed.extract 0 16)
  let nBlocks := (n + 15) / 16
  let mut out := ByteArray.emptyWithCapacity (nBlocks * 16)
  for j in [0:nBlocks] do
    let ctr := j.toUInt32
    let blk : ByteArray := ⟨(Array.replicate 12 (0 : UInt8)) ++
      #[(ctr >>> 24).toUInt8, (ctr >>> 16).toUInt8, (ctr >>> 8).toUInt8, ctr.toUInt8]⟩
    out := out ++ AES.encrypt rk blk
  return out.extract 0 n

/-- GF(256) products: entry `256 a + b` is `a·b`. -/
def mulTab : ByteArray := Id.run do
  let mut t := ByteArray.emptyWithCapacity 65536
  for a in [0:256] do
    for b in [0:256] do
      t := t.push (AES.gmul a.toUInt8 b.toUInt8)
  return t

-- pqov's `gf256_mul` test values (`0x53 · 0xca = 1` in the AES field).
#guard mulTab.get! (256 * 0x53 + 0xca) == 1 && mulTab.get! (256 * 0x57 + 0x83) == 0xc1

/-- `dst[d .. d + 45) += a · src[s .. s + 45)` (`gf256v_madd`). -/
@[inline] def madd (dst src : ByteArray) (d s : Nat) (a : UInt8) : ByteArray := Id.run do
  let mut dst := dst
  let row := 256 * a.toNat
  for c in [0:o] do
    dst := dst.set! (d + c) (dst.get! (d + c) ^^^ mulTab.get! (row + (src.get! (s + c)).toNat))
  return dst

/-- `calculate_F2_P3`'s `P3` from `P1 ‖ P2` (`p12`) and `O`. -/
def computeP3 (p12 O : ByteArray) : ByteArray := Id.run do
  -- S = P1·O + P2, a v×o matrix of 45-byte vectors (row-major).
  let mut S := p12.extract p1Bytes (p1Bytes + p2Bytes)
  for i in [0:v] do
    for k in [i:v] do
      let a := 45 * idxTri i k v
      for j in [0:o] do
        let x := O.get! (v * j + k)
        if x != 0 then S := madd S p12 (o * (o * i + j)) a x
  -- M = Oᵀ·S, an o×o matrix of 45-byte vectors (row-major).
  let mut M := ByteArray.mk (Array.replicate (o * o * o) 0)
  for i in [0:o] do
    for k in [0:v] do
      let x := O.get! (v * i + k)
      if x != 0 then
        for j in [0:o] do
          M := madd M S (o * (o * i + j)) (o * (o * k + j)) x
  -- P3 = UT(M + Mᵀ).
  let mut P3 := ByteArray.emptyWithCapacity p3Bytes
  for i in [0:o] do
    for j in [i:o] do
      for c in [0:o] do
        let x := M.get! (o * (o * i + j) + c)
        P3 := P3.push (if i == j then x else x ^^^ M.get! (o * (o * j + i) + c))
  return P3

/-- `generate_keypair_pkc`: the compressed public key `pk_seed ‖ P3` of a 32-byte secret seed. -/
def compressedPk (skSeed : ByteArray) : ByteArray :=
  let buf := Spec.SHAKE.shake256 skSeed (pkSeedBytes + v * o)
  let pkSeed := buf.extract 0 pkSeedBytes
  let O := buf.extract pkSeedBytes (pkSeedBytes + v * o)
  pkSeed ++ computeP3 (publicInputs pkSeed (p1Bytes + p2Bytes)) O

end VoleMole.Verifier.Keygen
