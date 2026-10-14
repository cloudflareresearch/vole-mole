/-!
# Concrete GF(2¹²⁸) and GF(256)

Computable models of the two fields of the C++ code, for running the constraint generators of
`VoleMole/Arith/*` on concrete values and comparing with the C++ (`lake exe arith_vectors`).
This file imports only Lean core.

* `GF128` is `faest-arch-opt`'s `poly128` modulo `X¹²⁸ + X⁷ + X² + X + 1` (`reduce_to<128>`,
  `polynomials_constants.hpp`). `lo` holds the coefficients of `X⁰ … X⁶³` (bit `i` of `lo` is the
  coefficient of `Xⁱ`), `hi` those of `X⁶⁴ … X¹²⁷`. This is `poly128::load` / `store` on a
  little-endian machine: byte `i` of the 16-byte encoding holds the coefficients of
  `X^(8i) … X^(8i+7)`, least significant bit first. The hex encoding (`GF128.toHex`, `ofHex?`) is
  those 16 bytes in order, as `tests/arith/dump_arith_vectors.cpp` writes them.
* `GF256` is pqov's GF(2)[x]/(x⁸ + x⁴ + x³ + x + 1) (`pqov/src/gf16.h`, `gf256_mul`, the 0x11b
  modulus), a byte `a = Σ_b a_b 2^b` standing for `Σ_b a_b x^b`.
* `beta b` is `β_b`: `β_0 = 1` and `β_b = gf8_in_gf128[b-1]` (`faest-arch-opt/
  polynomials_constants.cpp`), and `iota a = Σ_b a_b β_b` is `poly128::from_8_byte(a)`.

There is deliberately no `Field GF128` instance: only `+`, `*`, `0`, `1`, which is all the
generators need.

## What is checked about `ι`

`ι` is GF(2)-linear by definition. Kernel-checked here (`decide +kernel`, no `native_decide`):
* `iota_one`: `ι 1 = 1`;
* `iota_mul_basis`: `ι(xⁱ · xʲ) = ι(xⁱ) · ι(xʲ)` for all `i, j < 8` (the 64 products of basis
  elements; with bilinearity of both multiplications this is multiplicativity);
* `iota_eq_zero_iff`: `ι a = 0 ↔ a = 0` for all 256 bytes (with additivity, injectivity);
* `iota_add_basis`: `ι(a + xʲ) = ι a + ι(xʲ)` for all bytes `a` and `j < 8`.

The bilinearity of the multiplications is not proved, so the full statements (`ι` is an injective
ring homomorphism) are checked exhaustively at run time instead: `lake exe arith_vectors` checks all
65536 sums and products (`VoleMole/Arith/Vectors.lean`, `checkIotaHom`).
-/

namespace VoleMole.Arith

/-! ## GF(2¹²⁸) -/

/-- An element of GF(2¹²⁸): `lo` = coefficients of `X⁰ … X⁶³`, `hi` = those of `X⁶⁴ … X¹²⁷`. -/
structure GF128 where
  lo : UInt64
  hi : UInt64
  deriving DecidableEq, Inhabited, Hashable, Repr

namespace GF128

def zero : GF128 := ⟨0, 0⟩
def one : GF128 := ⟨1, 0⟩

/-- Addition is XOR. -/
def add (a b : GF128) : GF128 := ⟨a.lo ^^^ b.lo, a.hi ^^^ b.hi⟩

/-- Multiplication by `X`, reducing with `X¹²⁸ = X⁷ + X² + X + 1` (0x87). -/
def mulX (a : GF128) : GF128 :=
  ⟨(a.lo <<< 1) ^^^ ((a.hi >>> 63) * 0x87), (a.hi <<< 1) ^^^ (a.lo >>> 63)⟩

/-- Shift-and-add over the `n` low bits of the word `w`: returns `(acc + Σ_{i<n} w_i · p Xⁱ, p Xⁿ)`. -/
def mulWord : Nat → UInt64 → GF128 → GF128 → GF128 × GF128
  | 0, _, acc, p => (acc, p)
  | n + 1, w, acc, p => mulWord n (w >>> 1) (if w &&& 1 = 1 then add acc p else acc) (mulX p)

/-- The product in GF(2¹²⁸): `Σ_i a_i · b Xⁱ`. -/
def mul (a b : GF128) : GF128 :=
  let r := mulWord 64 a.lo zero b
  (mulWord 64 a.hi r.1 r.2).1

instance : Zero GF128 := ⟨zero⟩
instance : One GF128 := ⟨one⟩
instance : Add GF128 := ⟨add⟩
instance : Mul GF128 := ⟨mul⟩

/-- The 16 bytes of `poly128::store`. -/
def toBytes (a : GF128) : List UInt8 :=
  (List.range 8).map (fun i => (a.lo >>> (8 * i).toUInt64).toUInt8) ++
    (List.range 8).map (fun i => (a.hi >>> (8 * i).toUInt64).toUInt8)

/-- A little-endian word from (up to) 8 bytes. -/
def wordOfBytes (bs : List UInt8) : UInt64 :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.toUInt64) 0

/-- `poly128::load` of 16 bytes (missing bytes are zero). -/
def ofBytes (bs : List UInt8) : GF128 := ⟨wordOfBytes (bs.take 8), wordOfBytes ((bs.drop 8).take 8)⟩

end GF128

/-! ## Hex -/

namespace Hex

def digit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

def byteToHex (b : UInt8) : String := String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)]

def bytesToHex (bs : List UInt8) : String := String.join (bs.map byteToHex)

def nibble? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decode a list of hex digits (even length). -/
def decodeChars : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | a :: b :: rest => do
    let hi ← nibble? a
    let lo ← nibble? b
    let tl ← decodeChars rest
    pure ((hi * 16 + lo).toUInt8 :: tl)

/-- Decode a hex string into bytes; `-` is the empty string. -/
def decode? (s : String) : Option (List UInt8) :=
  if s = "-" then some [] else decodeChars s.toList

/-- Decode a hex string into a `ByteArray` (fast path for long strings such as UOV keys). -/
def decodeByteArray? (s : String) : Option ByteArray := Id.run do
  if s = "-" then return some ByteArray.empty
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then return none
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    match nibble? cs[2 * i]!, nibble? cs[2 * i + 1]! with
    | some h, some l => out := out.push (h * 16 + l).toUInt8
    | _, _ => return none
  return some out

end Hex

namespace GF128

/-- 32 hex digits: the 16 bytes of `poly128::store`. -/
def toHex (a : GF128) : String := Hex.bytesToHex a.toBytes

instance : ToString GF128 := ⟨toHex⟩

def ofHex? (s : String) : Option GF128 := do
  let bs ← Hex.decode? s
  if bs.length = 16 then some (ofBytes bs) else none

/-- A concatenation of 32-digit encodings (`-` if empty). -/
def listOfHex? (s : String) : Option (Array GF128) := do
  let bs ← Hex.decodeByteArray? s
  if bs.size % 16 != 0 then none
  else
    let n := bs.size / 16
    some <| (Array.range n).map fun i =>
      ofBytes ((List.range 16).map fun j => bs.get! (16 * i + j))

end GF128

/-! ## GF(256) -/

/-- An element of pqov's GF(256): the byte `val`. -/
structure GF256 where
  val : UInt8
  deriving DecidableEq, Inhabited, Hashable, Repr

namespace GF256

def add (a b : GF256) : GF256 := ⟨a.val ^^^ b.val⟩

/-- `xtime`: `a ↦ x·a`, `(a << 1) ^ ((a >> 7) * 0x1b)`. -/
def xtime (a : UInt8) : UInt8 := (a <<< 1) ^^^ ((a >>> 7) * 0x1b)

/-- pqov's `gf256_mul` (`gf16.h`), step by step. -/
def mulAux : Nat → UInt8 → UInt8 → UInt8 → UInt8
  | 0, _, _, r => r
  | n + 1, a, b, r => mulAux n (xtime a) (b >>> 1) (r ^^^ (a * (b &&& 1)))

def mul (a b : GF256) : GF256 := ⟨mulAux 8 a.val b.val 0⟩

instance : Zero GF256 := ⟨⟨0⟩⟩
instance : One GF256 := ⟨⟨1⟩⟩
instance : Add GF256 := ⟨add⟩
instance : Mul GF256 := ⟨mul⟩

/-- Bit `b` of the byte (the coefficient of `x^b`). -/
def toBits (a : GF256) (b : Fin 8) : Bool := (a.val >>> b.val.toUInt8) &&& 1 = 1

/-- The byte with bits `v` (LSB first). -/
def ofBits (v : Fin 8 → Bool) : GF256 :=
  ⟨(List.finRange 8).foldl (fun acc b => if v b then acc ||| ((1 : UInt8) <<< b.val.toUInt8) else acc)
    0⟩

/-- All 256 elements. -/
def all : List GF256 := (List.range 256).map fun n => ⟨n.toUInt8⟩

/-- `x^i`. -/
def basis (i : Fin 8) : GF256 := ⟨(1 : UInt8) <<< i.val.toUInt8⟩

end GF256

/-! ## The embedding -/

/-- `gf8_in_gf128` (`faest-arch-opt/polynomials_constants.cpp`), as stored. -/
def gf8InGf128 : List (List UInt8) :=
  [[0x0d, 0xce, 0x60, 0x55, 0xac, 0xe8, 0x3f, 0xa1, 0x1c, 0x9a, 0x97, 0xa9, 0x55, 0x85, 0x3d, 0x05],
   [0xe1, 0xae, 0x88, 0x34, 0xca, 0x59, 0x77, 0xec, 0x84, 0xbb, 0xbf, 0x9c, 0x43, 0xb7, 0xf4, 0x4c],
   [0xa8, 0x46, 0x39, 0x36, 0xae, 0x02, 0xcf, 0xbf, 0xc6, 0xd2, 0x51, 0x7d, 0x4f, 0x60, 0xad, 0x35],
   [0x49, 0x98, 0x2e, 0x3c, 0x48, 0x30, 0x83, 0x6b, 0xfe, 0x22, 0xa2, 0x40, 0x46, 0x36, 0xcb, 0x0d],
   [0xb4, 0x82, 0x1b, 0x7b, 0x27, 0x49, 0x2b, 0x25, 0xa5, 0xde, 0x88, 0x1a, 0xe1, 0x10, 0x98, 0x54],
   [0x22, 0xff, 0x21, 0x25, 0xef, 0xf2, 0x2b, 0xc7, 0x75, 0x1f, 0x0c, 0x6c, 0x68, 0xa5, 0x81, 0xd6],
   [0xbc, 0xf9, 0x36, 0xe1, 0x94, 0x8e, 0x7a, 0x7a, 0xe0, 0x8f, 0xb7, 0x4f, 0x1a, 0x31, 0x50, 0x09]]

/-- `β_0 = 1`, `β_b = gf8_in_gf128[b-1]`: `β_b = poly128::from_8_byte(1 << b)`. -/
def beta (b : Fin 8) : GF128 :=
  if b.val = 0 then 1 else GF128.ofBytes (gf8InGf128.getD (b.val - 1) [])

/-- `ι(a) = Σ_b a_b β_b` (`poly128::from_8_byte`, `uov::detail::embed`), summed for `b = 0 … 7`. -/
def iota (a : GF256) : GF128 :=
  (List.finRange 8).foldl (fun acc b => if a.toBits b then acc + beta b else acc) 0

/-! ## Kernel-checked facts about `ι` -/

theorem iota_one : iota 1 = 1 := by decide +kernel

theorem iota_mul_basis :
    ∀ i j : Fin 8, iota (GF256.basis i * GF256.basis j) = iota (GF256.basis i) * iota (GF256.basis j) := by
  decide +kernel

theorem iota_eq_zero_iff : ∀ a : Fin 256, iota ⟨a.val.toUInt8⟩ = 0 ↔ (⟨a.val.toUInt8⟩ : GF256) = 0 := by
  decide +kernel

theorem iota_add_basis :
    ∀ (a : Fin 256) (j : Fin 8),
      iota (⟨a.val.toUInt8⟩ + GF256.basis j) = iota ⟨a.val.toUInt8⟩ + iota (GF256.basis j) := by
  decide +kernel

end VoleMole.Arith
