/-!
# AES-128 and faest-arch-opt's AES-CTR PRG (executable)

* `sbox`: the AES S-box, computed (not tabulated) as the affine map of FIPS 197 §5.1.1 applied to
  the inverse in GF(2⁸) modulo `x⁸ + x⁴ + x³ + x + 1`.
* `expandKey key` (FIPS 197 §5.2) gives the 11 round keys of AES-128 as 176 bytes; `encrypt rk pt`
  (§5.1) encrypts one 16-byte block. Bytes are in FIPS order: state byte `r + 4c` is row `r`,
  column `c`, which is the memory order of the C++ `block128` (AES-NI, `aes.hpp`).
* `prg key iv tweak counter n` is faest-arch-opt's `aes_ctr_prg<secpar::s128>` (`prgs.hpp:153-230`):
  block `j` of the output is `E_key(iv ⊞ (counter + j, 0, 0, tweak))`, where `⊞` is lane-wise
  addition of four little-endian 32-bit words modulo 2³² (`build_ecb_input`, `prgs.hpp:197-206`:
  `iv.add32(block_t::set_low_high32(cnt, twk))`; `set_low_high32(x, y) = _mm_setr_epi32(x, 0, 0,
  y)` and `add32 = _mm_add_epi32`, `avx2/block_impl.hpp:34-42`). Every call site in the verifier
  starts at `counter = 0` (`expand_chunk`, `vector_com.inc:39-77`; `gen_u_hi`,
  `vole_commit.inc:242`; `vole_sender/receiver`, `small_vole.inc`).

Executable data structures only (`ByteArray`, `Array UInt8`). Checked by the `#guard`s below
(FIPS 197 Appendices B and C.1, and PRG blocks recomputed from `encrypt`) and, at run time, by
`lake exe verifier_vectors` against values dumped from faest-arch-opt
(`tests/voleith/dump_verifier_vectors.cpp`, `lean/vectors/verifier_prims.txt`).
-/

namespace VoleMole.Verifier.AES

/-- Multiplication by `x` in GF(2⁸) modulo `x⁸ + x⁴ + x³ + x + 1`. -/
@[inline] def xtime (a : UInt8) : UInt8 :=
  (a <<< 1) ^^^ (if a &&& 0x80 != 0 then 0x1b else 0)

/-- Multiplication in GF(2⁸) (shift-and-add). -/
def gmul (a b : UInt8) : UInt8 := Id.run do
  let mut r : UInt8 := 0
  let mut x := a
  let mut y := b
  for _ in [0:8] do
    if y &&& 1 != 0 then r := r ^^^ x
    x := xtime x
    y := y >>> 1
  return r

/-- `a²⁵⁴`, the inverse of `a` in GF(2⁸) (and `0 ↦ 0`). -/
def ginv (a : UInt8) : UInt8 := Id.run do
  let mut r : UInt8 := 1
  for _ in [0:254] do
    r := gmul r a
  return r

@[inline] def rotl8 (a : UInt8) (n : UInt8) : UInt8 := (a <<< n) ||| (a >>> (8 - n))

/-- The S-box: `b ⊕ rotl(b,1) ⊕ rotl(b,2) ⊕ rotl(b,3) ⊕ rotl(b,4) ⊕ 0x63` with `b = a⁻¹`. -/
def sboxEntry (a : UInt8) : UInt8 :=
  let b := ginv a
  b ^^^ rotl8 b 1 ^^^ rotl8 b 2 ^^^ rotl8 b 3 ^^^ rotl8 b 4 ^^^ 0x63

def sbox : Array UInt8 := (Array.range 256).map fun i => sboxEntry i.toUInt8

#guard sbox[0x00]! == 0x63 && sbox[0x01]! == 0x7c && sbox[0x53]! == 0xed && sbox[0xff]! == 0x16

@[inline] def sub (a : UInt8) : UInt8 := sbox[a.toNat]!

/-- The AES-128 key schedule: 11 round keys, 176 bytes (`key` must have 16 bytes). -/
def expandKey (key : ByteArray) : ByteArray := Id.run do
  let mut w := key
  let mut rcon : UInt8 := 1
  for i in [4:44] do
    let mut t0 := w.get! (4 * i - 4)
    let mut t1 := w.get! (4 * i - 3)
    let mut t2 := w.get! (4 * i - 2)
    let mut t3 := w.get! (4 * i - 1)
    if i % 4 == 0 then
      let (a, b, c, d) := (sub t1 ^^^ rcon, sub t2, sub t3, sub t0)
      t0 := a; t1 := b; t2 := c; t3 := d
      rcon := xtime rcon
    w := w.push (w.get! (4 * i - 16) ^^^ t0)
    w := w.push (w.get! (4 * i - 15) ^^^ t1)
    w := w.push (w.get! (4 * i - 14) ^^^ t2)
    w := w.push (w.get! (4 * i - 13) ^^^ t3)
  return w

/-- Encrypt one block (`pt` 16 bytes) with expanded round keys `rk` (176 bytes). -/
def encrypt (rk : ByteArray) (pt : ByteArray) : ByteArray := Id.run do
  let mut s : Array UInt8 := (Array.range 16).map fun i => pt.get! i ^^^ rk.get! i
  for r in [1:11] do
    -- SubBytes and ShiftRows: new byte (row i, column c) is old (row i, column c + i).
    let t : Array UInt8 := (Array.range 16).map fun j =>
      let row := j % 4
      let col := j / 4
      sub s[row + 4 * ((col + row) % 4)]!
    -- MixColumns (skipped in the last round), then AddRoundKey.
    let mut u := t
    if r != 10 then
      for c in [0:4] do
        let a0 := t[4 * c]!
        let a1 := t[4 * c + 1]!
        let a2 := t[4 * c + 2]!
        let a3 := t[4 * c + 3]!
        u := u.set! (4 * c) (xtime a0 ^^^ (xtime a1 ^^^ a1) ^^^ a2 ^^^ a3)
        u := u.set! (4 * c + 1) (a0 ^^^ xtime a1 ^^^ (xtime a2 ^^^ a2) ^^^ a3)
        u := u.set! (4 * c + 2) (a0 ^^^ a1 ^^^ xtime a2 ^^^ (xtime a3 ^^^ a3))
        u := u.set! (4 * c + 3) ((xtime a0 ^^^ a0) ^^^ a1 ^^^ a2 ^^^ xtime a3)
    s := (Array.range 16).map fun j => u[j]! ^^^ rk.get! (16 * r + j)
  return ⟨s⟩

/-- Little-endian 32-bit word at byte offset `o`. -/
@[inline] def getLE32 (b : ByteArray) (o : Nat) : UInt32 :=
  (b.get! o).toUInt32 ||| ((b.get! (o + 1)).toUInt32 <<< 8) |||
    ((b.get! (o + 2)).toUInt32 <<< 16) ||| ((b.get! (o + 3)).toUInt32 <<< 24)

/-- Append the little-endian encoding of `x`. -/
@[inline] def pushLE32 (b : ByteArray) (x : UInt32) : ByteArray :=
  b.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8

/-- `iv.add32(set_low_high32(cnt, twk))`: the CTR input block. -/
def ctrBlock (iv : ByteArray) (cnt tweak : UInt32) : ByteArray :=
  let b := pushLE32 ByteArray.empty (getLE32 iv 0 + cnt)
  let b := pushLE32 b (getLE32 iv 4)
  let b := pushLE32 b (getLE32 iv 8)
  pushLE32 b (getLE32 iv 12 + tweak)

/-- `aes_ctr_prg<s128>` with an already expanded key: `n` blocks (16 n bytes) starting at
counter `counter`. -/
def prgExpanded (rk : ByteArray) (iv : ByteArray) (tweak counter : UInt32) (n : Nat) :
    ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (16 * n)
  for j in [0:n] do
    out := out ++ encrypt rk (ctrBlock iv (counter + j.toUInt32) tweak)
  return out

/-- `aes_ctr_prg<s128>::init/gen` for one key: `n` blocks starting at counter `counter`. -/
def prg (key : ByteArray) (iv : ByteArray) (tweak counter : UInt32) (n : Nat) : ByteArray :=
  prgExpanded (expandKey key) iv tweak counter n

/-! ## Known answers -/

/-- Lowercase hex. -/
def hex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let h := Nat.toDigits 16 x.toNat
    String.ofList (if h.length = 1 then '0' :: h else h))

/-- Bytes from a list of naturals. -/
def bytes (l : List Nat) : ByteArray := ⟨(l.map Nat.toUInt8).toArray⟩

-- FIPS 197 Appendix A.1: the last round key of the key 2b7e1516 28aed2a6 abf71588 09cf4f3c.
#guard hex ((expandKey (bytes [0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15,
    0x88, 0x09, 0xcf, 0x4f, 0x3c])).extract 160 176) == "d014f9a8c9ee2589e13f0cc8b6630ca6"

-- FIPS 197 Appendix B.
#guard hex (encrypt (expandKey (bytes [0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7,
    0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c]))
  (bytes [0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d, 0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07,
    0x34])) == "3925841d02dc09fbdc118597196a0b32"

-- FIPS 197 Appendix C.1.
#guard hex (encrypt (expandKey (bytes (List.range 16)))
  (bytes ((List.range 16).map (· * 0x11)))) == "69c4e0d86a7b0430d8cdb78070b4c55a"

-- CTR input arithmetic: lane 0 gets the counter, lane 3 the tweak, each with 32-bit wrap-around
-- and no carry into the neighbouring lane.
#guard hex (ctrBlock (bytes [0xff, 0xff, 0xff, 0xff, 1, 0, 0, 0, 0, 0, 0, 0, 0xfe, 0xff, 0xff, 0xff])
  2 3) == "01000000010000000000000001000000"

end VoleMole.Verifier.AES
