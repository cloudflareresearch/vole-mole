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

## `ι` is an injective ring homomorphism (kernel-checked)

`iota_zero`, `iota_one`, `iota_add`, `iota_mul`, `iota_injective` are proved without
`native_decide`. The proof combines two kinds of facts:
* small finite checks evaluated by the kernel (`decide +kernel`): the 64 products of basis
  elements `ι(xⁱ · xʲ) = ι(xⁱ) · ι(xʲ)` (`iota_mul_basis`), `ι a = 0 ↔ a = 0` on all 256 bytes
  (`iota_eq_zero_iff`), `ι 1 = 1`, and the decomposition of each byte into its bits
  (`GF256.decomp`);
* symbolic proofs that both multiplications are bilinear (`GF128.add_mul`, `GF128.mul_add`,
  `GF256.add_mul`, `GF256.mul_add`) and that `ι` is additive. To make these easy, the reduction
  steps `mulX` and `xtime` multiply the overflow bit by the modulus with shifts and XORs rather than
  with an integer product, and bits are read with `BitVec.getLsbD`.
`lake exe arith_vectors` additionally checks all 65536 sums and products at run time, and checks
`GF128` and `GF256` multiplication, `β` and `ι` against the C++ (`lean/vectors/field.txt`).
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

instance : Zero GF128 := ⟨zero⟩
instance : One GF128 := ⟨one⟩
instance : Add GF128 := ⟨add⟩

/-- Multiplication by `X`, reducing with `X¹²⁸ = X⁷ + X² + X + 1` (0x87). -/
def mulX (a : GF128) : GF128 :=
  let c := a.hi >>> 63 -- the coefficient of X¹²⁷, times X⁷ + X² + X + 1:
  ⟨(a.lo <<< 1) ^^^ c ^^^ (c <<< 1) ^^^ (c <<< 2) ^^^ (c <<< 7), (a.hi <<< 1) ^^^ (a.lo >>> 63)⟩

/-- Shift-and-add over the `n` low bits of the word `w`: returns `(acc + Σ_{i<n} w_i · p Xⁱ, p Xⁿ)`. -/
def mulWord : Nat → UInt64 → GF128 → GF128 → GF128 × GF128
  | 0, _, acc, p => (acc, p)
  | n + 1, w, acc, p =>
    mulWord n (w >>> 1) (if w.toBitVec.getLsbD 0 then acc + p else acc) (mulX p)

/-- The product in GF(2¹²⁸): `Σ_i a_i · b Xⁱ`. -/
def mul (a b : GF128) : GF128 :=
  let r := mulWord 64 a.lo 0 b
  (mulWord 64 a.hi r.1 r.2).1

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
def xtime (a : UInt8) : UInt8 :=
  let c := a >>> 7 -- the coefficient of x⁷, times x⁴ + x³ + x + 1:
  (a <<< 1) ^^^ c ^^^ (c <<< 1) ^^^ (c <<< 3) ^^^ (c <<< 4)

/-- pqov's `gf256_mul` (`gf16.h`), step by step. -/
def mulAux : Nat → UInt8 → UInt8 → UInt8 → UInt8
  | 0, _, _, r => r
  | n + 1, a, b, r => mulAux n (xtime a) (b >>> 1) (if b.toBitVec.getLsbD 0 then r ^^^ a else r)

def mul (a b : GF256) : GF256 := ⟨mulAux 8 a.val b.val 0⟩

instance : Zero GF256 := ⟨⟨0⟩⟩
instance : One GF256 := ⟨⟨1⟩⟩
instance : Add GF256 := ⟨add⟩
instance : Mul GF256 := ⟨mul⟩

/-- Bit `b` of the byte (the coefficient of `x^b`). -/
def toBits (a : GF256) (b : Fin 8) : Bool := a.val.toBitVec.getLsbD b.val

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

/-- `Σ_{b < 8, c b} v b`, summed for `b = 0 … 7`. -/
def foldSel {α : Type} [Add α] [Zero α] (c : Fin 8 → Bool) (v : Fin 8 → α) : α :=
  (List.finRange 8).foldl (fun acc b => if c b then acc + v b else acc) 0

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
def iota (a : GF256) : GF128 := foldSel a.toBits beta

/-! ## Kernel-checked facts about `ι` -/

theorem iota_one : iota 1 = 1 := by decide +kernel

theorem iota_mul_basis :
    ∀ i j : Fin 8, iota (GF256.basis i * GF256.basis j) = iota (GF256.basis i) * iota (GF256.basis j) := by
  decide +kernel

theorem iota_eq_zero_iff : ∀ a : Fin 256, iota ⟨a.val.toUInt8⟩ = 0 ↔ (⟨a.val.toUInt8⟩ : GF256) = 0 := by
  decide +kernel


/-! ## Proof that `ι` is an injective ring homomorphism -/

/-- `+` is XOR: an abelian group in which every element is its own negative. -/
class XorGroup (α : Type) [Add α] [Zero α] : Prop where
  add_comm : ∀ a b : α, a + b = b + a
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  add_zero : ∀ a : α, a + 0 = a
  add_self : ∀ a : α, a + a = 0

namespace XorGroup

theorem zero_add {α : Type} [Add α] [Zero α] [XorGroup α] (a : α) : 0 + a = a := by
  rw [add_comm, add_zero]

theorem add_self_left {α : Type} [Add α] [Zero α] [XorGroup α] (a b : α) : a + (a + b) = b := by
  rw [← add_assoc, add_self, zero_add]

theorem add_left_comm {α : Type} [Add α] [Zero α] [XorGroup α] (a b c : α) :
    a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

/-- An additive map sends `0` to `0`. -/
theorem map_zero_of_add {α β : Type} [Add α] [Zero α] [XorGroup α] [Add β] [Zero β] [XorGroup β]
    (g : α → β) (hg : ∀ x y, g (x + y) = g x + g y) : g 0 = 0 := by
  have h := hg 0 0
  rw [add_zero] at h
  have := congrArg (· + g 0) h
  simp only [add_self] at this
  rw [zero_add] at this
  exact this.symm

theorem foldl_sel_map {α β : Type} [Add α] [Add β] (g : α → β)
    (hg : ∀ x y, g (x + y) = g x + g y) (c : Fin 8 → Bool) (v : Fin 8 → α) (L : List (Fin 8))
    (acc : α) :
    g (L.foldl (fun acc b => if c b then acc + v b else acc) acc) =
      L.foldl (fun acc b => if c b then acc + g (v b) else acc) (g acc) := by
  induction L generalizing acc with
  | nil => rfl
  | cons b L ih =>
    simp only [List.foldl_cons]
    rw [ih]
    cases c b <;> simp [hg]

/-- An additive map commutes with `foldSel`. -/
theorem foldSel_map {α β : Type} [Add α] [Zero α] [XorGroup α] [Add β] [Zero β] [XorGroup β]
    (g : α → β) (hg : ∀ x y, g (x + y) = g x + g y) (c : Fin 8 → Bool) (v : Fin 8 → α) :
    g (foldSel c v) = foldSel c (fun b => g (v b)) := by
  rw [foldSel, foldl_sel_map g hg, map_zero_of_add g hg]; rfl

theorem foldl_sel_xor {α : Type} [Add α] [Zero α] [XorGroup α] (c d : Fin 8 → Bool)
    (v : Fin 8 → α) (L : List (Fin 8)) (a b : α) :
    L.foldl (fun acc i => if (c i ^^ d i) then acc + v i else acc) (a + b) =
      L.foldl (fun acc i => if c i then acc + v i else acc) a +
        L.foldl (fun acc i => if d i then acc + v i else acc) b := by
  induction L generalizing a b with
  | nil => rfl
  | cons i L ih =>
    simp only [List.foldl_cons]
    cases hc : c i <;> cases hd : d i <;> simp only [Bool.xor_false, Bool.xor_true, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    · exact ih a b
    · rw [add_assoc, ih]
    · rw [add_assoc, add_comm b, ← add_assoc, ih]
    · rw [← ih]; congr 1
      rw [add_assoc, add_left_comm (v i), add_self, add_zero]

/-- `foldSel` is additive in the selector, for XOR of selectors. -/
theorem foldSel_xor {α : Type} [Add α] [Zero α] [XorGroup α] (c d : Fin 8 → Bool)
    (v : Fin 8 → α) : foldSel (fun i => c i ^^ d i) v = foldSel c v + foldSel d v := by
  rw [foldSel, ← add_zero (0 : α), foldl_sel_xor]; rfl

end XorGroup

open XorGroup

/-- Normalize sums in an `XorGroup`, cancelling equal summands that end up adjacent. -/
macro "xor_norm" : tactic =>
  `(tactic| simp only [XorGroup.zero_add, XorGroup.add_zero, XorGroup.add_assoc,
    XorGroup.add_comm, XorGroup.add_left_comm, XorGroup.add_self, XorGroup.add_self_left])

namespace GF128

theorem ext' {a b : GF128} (h1 : a.lo = b.lo) (h2 : a.hi = b.hi) : a = b := by
  cases a; cases b; simp_all

theorem add_lo (a b : GF128) : (a + b).lo = a.lo ^^^ b.lo := rfl
theorem add_hi (a b : GF128) : (a + b).hi = a.hi ^^^ b.hi := rfl

instance : XorGroup GF128 where
  add_comm _ _ := ext' (UInt64.xor_comm _ _) (UInt64.xor_comm _ _)
  add_assoc _ _ _ := ext' (UInt64.xor_assoc _ _ _) (UInt64.xor_assoc _ _ _)
  add_zero _ := ext' UInt64.xor_zero UInt64.xor_zero
  add_self _ := ext' UInt64.xor_self UInt64.xor_self

theorem mulX_add (a b : GF128) : mulX (a + b) = mulX a + mulX b := by
  apply ext' <;> simp only [mulX, add_lo, add_hi, UInt64.shiftLeft_xor, UInt64.shiftRight_xor] <;>
    ac_rfl

theorem mulWord_acc (n : Nat) (w : UInt64) (acc p : GF128) :
    (mulWord n w acc p).1 = acc + (mulWord n w 0 p).1 := by
  induction n generalizing w acc p with
  | zero => exact (add_zero acc).symm
  | succ n ih =>
    simp only [mulWord]
    cases w.toBitVec.getLsbD 0 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ih ..
    · rw [ih _ (acc + p), ih _ (0 + p), zero_add, add_assoc]

theorem mulWord_w (n : Nat) (w1 w2 : UInt64) (p : GF128) :
    (mulWord n (w1 ^^^ w2) 0 p).1 = (mulWord n w1 0 p).1 + (mulWord n w2 0 p).1 := by
  induction n generalizing w1 w2 p with
  | zero => exact (add_zero 0).symm
  | succ n ih =>
    simp only [mulWord, UInt64.shiftRight_xor, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    cases w1.toBitVec.getLsbD 0 <;> cases w2.toBitVec.getLsbD 0 <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, mulWord_acc n _ (0 + p), ih] <;> xor_norm

/-- `p Xⁿ`. -/
def xpow : Nat → GF128 → GF128
  | 0, p => p
  | n + 1, p => xpow n (mulX p)

theorem mulWord_snd_eq (n : Nat) (w : UInt64) (acc p : GF128) : (mulWord n w acc p).2 = xpow n p := by
  induction n generalizing w acc p with
  | zero => rfl
  | succ n ih => exact ih ..

theorem xpow_add (n : Nat) (p1 p2 : GF128) : xpow n (p1 + p2) = xpow n p1 + xpow n p2 := by
  induction n generalizing p1 p2 with
  | zero => rfl
  | succ n ih => simp only [xpow, mulX_add, ih]

theorem mulWord_p (n : Nat) (w : UInt64) (p1 p2 : GF128) :
    (mulWord n w 0 (p1 + p2)).1 = (mulWord n w 0 p1).1 + (mulWord n w 0 p2).1 := by
  induction n generalizing w p1 p2 with
  | zero => exact (add_zero 0).symm
  | succ n ih =>
    simp only [mulWord]
    cases w.toBitVec.getLsbD 0 <;>
      simp only [Bool.false_eq_true, ↓reduceIte, mulX_add, mulWord_acc n _ (0 + (p1 + p2)),
        mulWord_acc n _ (0 + p1), mulWord_acc n _ (0 + p2), ih] <;> xor_norm

/-- `mul a b` as the sum of the contributions of `a.lo` and `a.hi`. -/
theorem mul_eq (a b : GF128) :
    a * b = (mulWord 64 a.lo 0 b).1 + (mulWord 64 a.hi 0 (xpow 64 b)).1 := by
  show (mulWord 64 a.hi _ _).1 = _
  rw [mulWord_acc, mulWord_snd_eq]

theorem add_mul (a b c : GF128) : (a + b) * c = a * c + b * c := by
  rw [mul_eq, mul_eq, mul_eq, add_lo, add_hi, mulWord_w, mulWord_w]
  xor_norm

theorem mul_add (a b c : GF128) : a * (b + c) = a * b + a * c := by
  rw [mul_eq, mul_eq, mul_eq, mulWord_p, xpow_add, mulWord_p]
  xor_norm

theorem mulWord_zero_word (n : Nat) (acc p : GF128) : (mulWord n 0 acc p).1 = acc := by
  induction n generalizing acc p with
  | zero => rfl
  | succ n ih =>
    have h1 : (0 : UInt64) >>> 1 = 0 := by decide
    have h2 : (0 : UInt64).toBitVec.getLsbD 0 = false := by decide
    simp only [mulWord, h1, h2, Bool.false_eq_true, ↓reduceIte]
    exact ih ..

theorem one_mul (b : GF128) : 1 * b = b := by
  have h1 : (1 : UInt64) >>> 1 = 0 := by decide
  have h2 : (1 : UInt64).toBitVec.getLsbD 0 = true := by decide
  rw [mul_eq]
  show (mulWord (63 + 1) 1 0 b).1 + (mulWord 64 0 0 _).1 = b
  rw [mulWord.eq_2, h1, h2, mulWord_zero_word, mulWord_zero_word]
  simp only [↓reduceIte, zero_add, add_zero]

theorem zero_mul (b : GF128) : 0 * b = 0 := map_zero_of_add (· * b) fun x y => add_mul x y b

end GF128

namespace GF256

theorem ext' {a b : GF256} (h : a.val = b.val) : a = b := by cases a; cases b; simp_all

theorem add_val (a b : GF256) : (a + b).val = a.val ^^^ b.val := rfl

instance : XorGroup GF256 where
  add_comm _ _ := ext' (UInt8.xor_comm _ _)
  add_assoc _ _ _ := ext' (UInt8.xor_assoc _ _ _)
  add_zero _ := ext' UInt8.xor_zero
  add_self _ := ext' UInt8.xor_self

theorem xtime_xor (a b : UInt8) : xtime (a ^^^ b) = xtime a ^^^ xtime b := by
  simp only [xtime, UInt8.shiftLeft_xor, UInt8.shiftRight_xor]; ac_rfl

/-- `mulAux` on bytes, as a map into the `XorGroup` `GF256`. -/
theorem mulAux_r (n : Nat) (a b r : UInt8) :
    (⟨mulAux n a b r⟩ : GF256) = ⟨r⟩ + ⟨mulAux n a b 0⟩ := by
  induction n generalizing a b r with
  | zero => exact ext' UInt8.xor_zero.symm
  | succ n ih =>
    simp only [mulAux]
    cases b.toBitVec.getLsbD 0 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ih ..
    · rw [ih _ _ (r ^^^ a), ih _ _ (0 ^^^ a)]
      exact ext' (by simp only [add_val, UInt8.zero_xor, UInt8.xor_assoc])

theorem mulAux_a (n : Nat) (a1 a2 b : UInt8) :
    (⟨mulAux n (a1 ^^^ a2) b 0⟩ : GF256) = ⟨mulAux n a1 b 0⟩ + ⟨mulAux n a2 b 0⟩ := by
  induction n generalizing a1 a2 b with
  | zero => exact (add_self _).symm
  | succ n ih =>
    simp only [mulAux, xtime_xor]
    cases b.toBitVec.getLsbD 0 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ih ..
    · rw [mulAux_r n _ _ (0 ^^^ (a1 ^^^ a2)), mulAux_r n _ _ (0 ^^^ a1),
        mulAux_r n _ _ (0 ^^^ a2), ih]
      have : (⟨0 ^^^ (a1 ^^^ a2)⟩ : GF256) = ⟨0 ^^^ a1⟩ + ⟨0 ^^^ a2⟩ :=
        ext' (by simp only [add_val, UInt8.zero_xor])
      rw [this]; xor_norm

theorem mulAux_b (n : Nat) (a b1 b2 : UInt8) :
    (⟨mulAux n a (b1 ^^^ b2) 0⟩ : GF256) = ⟨mulAux n a b1 0⟩ + ⟨mulAux n a b2 0⟩ := by
  induction n generalizing a b1 b2 with
  | zero => exact (add_self _).symm
  | succ n ih =>
    simp only [mulAux, UInt8.shiftRight_xor, UInt8.toBitVec_xor, BitVec.getLsbD_xor]
    cases b1.toBitVec.getLsbD 0 <;> cases b2.toBitVec.getLsbD 0 <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, mulAux_r n _ _ (0 ^^^ a), ih] <;> xor_norm

theorem add_mul (a b c : GF256) : (a + b) * c = a * c + b * c := mulAux_a ..

theorem mul_add (a b c : GF256) : a * (b + c) = a * b + a * c := mulAux_b ..

/-- Every byte is the sum of its bits times the basis. -/
theorem decomp (a : GF256) : a = foldSel a.toBits basis := by
  have h : ∀ n : Fin 256,
      (⟨n.val.toUInt8⟩ : GF256) = foldSel (GF256.toBits ⟨n.val.toUInt8⟩) basis := by
    decide +kernel
  have e : (⟨a.val.toNat.toUInt8⟩ : GF256) = a := ext' UInt8.ofNat_toNat
  have := h ⟨a.val.toNat, a.val.toNat_lt⟩
  rwa [e] at this

theorem toBits_add (a b : GF256) (i : Fin 8) : (a + b).toBits i = (a.toBits i ^^ b.toBits i) := by
  simp [toBits, add_val, UInt8.toBitVec_xor]

end GF256

theorem iota_add (a b : GF256) : iota (a + b) = iota a + iota b := by
  simp only [iota]
  rw [show (a + b).toBits = fun i => a.toBits i ^^ b.toBits i from funext (GF256.toBits_add a b),
    foldSel_xor]

theorem iota_zero : iota 0 = 0 := map_zero_of_add iota iota_add

/-- `ι` is multiplicative: from the 64 kernel-checked products of basis elements
(`iota_mul_basis`) and the bilinearity of both multiplications. -/
theorem iota_mul (a b : GF256) : iota (a * b) = iota a * iota b := by
  have hb : iota b = foldSel b.toBits fun j => iota (GF256.basis j) := by
    conv => lhs; rw [GF256.decomp b]
    exact foldSel_map iota iota_add _ _
  have ha : iota a = foldSel a.toBits fun j => iota (GF256.basis j) := by
    conv => lhs; rw [GF256.decomp a]
    exact foldSel_map iota iota_add _ _
  conv => lhs; rw [GF256.decomp a, GF256.decomp b]
  rw [foldSel_map (· * _) (fun x y => GF256.add_mul x y _), foldSel_map iota iota_add]
  simp only [foldSel_map (fun y => GF256.basis _ * y) (fun x y => GF256.mul_add _ x y),
    foldSel_map iota iota_add, iota_mul_basis]
  rw [ha, hb, foldSel_map (· * _) (fun x y => GF128.add_mul x y _)]
  simp only [foldSel_map (fun y => iota (GF256.basis _) * y) (fun x y => GF128.mul_add _ x y)]

theorem iota_injective (a b : GF256) (h : iota a = iota b) : a = b := by
  have h0 : iota (a + b) = 0 := by rw [iota_add, h, add_self]
  have := iota_eq_zero_iff ⟨(a + b).val.toNat, (a + b).val.toNat_lt⟩
  have e : (⟨(a + b).val.toNat.toUInt8⟩ : GF256) = a + b := GF256.ext' UInt8.ofNat_toNat
  rw [e] at this
  have hab : a + b = 0 := this.mp h0
  calc a = a + (b + b) := by rw [add_self, add_zero]
    _ = b := by rw [← add_assoc, hab, zero_add]

end VoleMole.Arith
