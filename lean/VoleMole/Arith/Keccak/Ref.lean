import VoleMole.Arith.Keccak.Circuit

/-!
# Reference Keccak-p[800, 12] on lanes (`src/keccak/keccak.cpp`, `src/keccak/tables.hpp`)

* `round800`: one round on 25 lanes `a[x + 5y] : BitVec 32`, transcribing `round800`
  (`keccak.cpp:17-50`).
* `keccakRounds first num`: rounds `first, …, first + num - 1`; `keccakP800Rounds` and `keccakP800`
  on the 100-byte state, with lanes packed little-endian (`keccak_p800_rounds`,
  `keccak.cpp:54-74`, `include/vole_mole/keccak.hpp:22-28`).
* The tables of `Keccak/Circuit.lean` are checked against their generating code
  (`rhoTable_eq`, `rcTable_eq`, `thetaInvQ_eq`), and `keccakP800` against `tests/keccak/kat.txt`
  (`#guard`, evaluated by the interpreter at elaboration time).
-/

set_option linter.unusedSectionVars false

namespace VoleMole.Arith.Keccak

/-! ## The tables, from their generating code -/

/-- `keccak_rc_bit(t)` (FIPS 202, Algorithm 5; `tables.hpp:20-32`). -/
def rcBit (t : ℕ) : ℕ :=
  if t % 255 = 0 then 1 else
  (List.range (t % 255)).foldl (fun r _ =>
    let r := r <<< 1
    let r8 := (r >>> 8) &&& 1
    (r ^^^ (r8 ||| (r8 <<< 4) ||| (r8 <<< 5) ||| (r8 <<< 6))) &&& 0xff) 1 &&& 1

/-- `keccak_round_constant(ir)` truncated to 32 bits (`tables.hpp:35-41`). -/
def roundConstant (ir : ℕ) : ℕ :=
  (List.range 6).foldl (fun rc j => rc ||| (rcBit (j + 7 * ir) <<< (2 ^ j - 1))) 0

theorem rcTable_eq : rcTable = (List.range 12).map fun i => BitVec.ofNat 32 (roundConstant (10 + i)) := by
  decide +kernel

/-- `KECCAK_RHO` by its generating loop (`tables.hpp:54-64`): `(x, y, offset)` triples. -/
def rhoGen : List (ℕ × ℕ × ℕ) :=
  ((List.range 24).foldl (fun (acc : List (ℕ × ℕ × ℕ) × ℕ × ℕ) t =>
    let (l, x, y) := acc
    ((x, y, (t + 1) * (t + 2) / 2 % 32) :: l, y, (2 * x + 3 * y) % 5)) ([], 1, 0)).1

theorem rhoTable_eq : ∀ e ∈ rhoGen, (rhoTable.getD e.1 []).getD e.2.1 0 = e.2.2 := by
  decide +kernel

theorem rho_zero_zero : (rhoTable.getD 0 []).getD 0 0 = 0 := rfl

/-- Multiplication in GF(2)[X] / (X⁵ + 1) (`tables.hpp:91-101`). -/
def polyMul5 (a b : ℕ) : ℕ :=
  (List.range 5).foldl (fun out i => (List.range 5).foldl (fun out j =>
    if a.testBit i && b.testBit j then out ^^^ (1 <<< ((i + j) % 5)) else out) out) 0

/-- `KECCAK_THETA_INV_Q`: the least `r` with `q r = 1`, `q = 1 + X^{(5 - 32 % 5) % 5} + X^{32 % 5}`
(`tables.hpp:102-108`). -/
theorem thetaInvQ_eq :
    let q := 1 ^^^ (1 <<< ((5 - 32 % 5) % 5)) ^^^ (1 <<< (32 % 5))
    polyMul5 q thetaInvQ = 1 ∧ ∀ r < thetaInvQ, 0 < r → polyMul5 q r ≠ 1 := by
  decide +kernel

/-! ## The lane-based round -/

/-- 25 lanes `a[x + 5y]`. -/
abbrev Lanes := Vector (BitVec 32) 25

/-- Lane index `x + 5y`. -/
def lane (x y : Fin 5) : Fin 25 := ⟨x.1 + 5 * y.1, by omega⟩
/-- `x` of a lane index. -/
def lx (l : Fin 25) : Fin 5 := ⟨l.1 % 5, Nat.mod_lt _ (by norm_num)⟩
/-- `y` of a lane index. -/
def ly (l : Fin 25) : Fin 5 := ⟨l.1 / 5, by omega⟩

/-- `round800(a, rc)` (`keccak.cpp:17-50`). -/
def round800 (rcv : BitVec 32) (a : Lanes) : Lanes :=
  -- theta
  let cp : Vector (BitVec 32) 5 := Vector.ofFn fun x =>
    a[lane x 0] ^^^ a[lane x 1] ^^^ a[lane x 2] ^^^ a[lane x 3] ^^^ a[lane x 4]
  let d : Vector (BitVec 32) 5 := Vector.ofFn fun x => cp[x + 4] ^^^ cp[x + 1].rotateLeft 1
  let a₁ : Lanes := Vector.ofFn fun l => a[l] ^^^ d[lx l]
  -- rho and pi
  let b : Lanes := Vector.ofFn fun l =>
    let sx := lx l + 3 * ly l
    let sy := lx l
    a₁[lane sx sy].rotateLeft (rho sx sy).1
  -- chi
  let a₂ : Lanes := Vector.ofFn fun l =>
    b[l] ^^^ (~~~b[lane (lx l + 1) (ly l)] &&& b[lane (lx l + 2) (ly l)])
  -- iota (`a[0] ^= rc`)
  Vector.ofFn fun l => if l.1 = 0 then a₂[l] ^^^ rcv else a₂[l]

/-- Rounds `first, …, first + num - 1` (`keccak.cpp:62-64`). -/
def keccakRounds (first : ℕ) : ℕ → Lanes → Lanes
  | 0, a => a
  | num + 1, a => keccakRounds (first + 1) num (round800 (rc first) a)

/-! ## The byte-level permutation -/

/-- `Kp800State`: 100 bytes. -/
abbrev State := Vector UInt8 100

/-- Little-endian lane packing (`keccak.cpp:57-61`). -/
def toLanes (s : State) : Lanes :=
  Vector.ofFn fun l => s[4 * l.1 + 3].toBitVec ++ s[4 * l.1 + 2].toBitVec ++
    s[4 * l.1 + 1].toBitVec ++ s[4 * l.1].toBitVec

/-- Unpacking (`keccak.cpp:66-70`). -/
def fromLanes (a : Lanes) : State :=
  Vector.ofFn fun k => UInt8.ofBitVec (a[k.1 / 4].extractLsb' (8 * (k.1 % 4)) 8)

/-- `keccak_p800_rounds(state, first, num)`. -/
def keccakP800Rounds (first num : ℕ) (s : State) : State :=
  fromLanes (keccakRounds first num (toLanes s))

/-- `keccak_p800(state)`: Keccak-p[800, 12]. -/
def keccakP800 (s : State) : State := keccakP800Rounds 0 12 s

/-- Bit `i` of a state: bit `i % 8` of byte `⌊i / 8⌋`. -/
def stateBit (s : State) (i : ℕ) : Bool :=
  if h : i / 8 < 100 then s[i / 8].toBitVec.getLsbD (i % 8) else false

/-- The state as 800 bits. -/
def stateBits (s : State) : Vector Bool 800 := Vector.ofFn fun i => stateBit s i.1

/-! ## Known answers (`tests/keccak/kat.txt`) -/

/-- Parse a hex string into bytes (for the known answers). -/
def ofHex (s : String) : List UInt8 :=
  let d (c : Char) : ℕ := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List UInt8
    | a :: b :: t => UInt8.ofNat (16 * d a + d b) :: go t
    | _ => []
  go s.toList

/-- A 100-byte state from hex. -/
def stateOfHex (s : String) : State := Vector.ofFn fun k => (ofHex s).getD k.1 0

/-- Bytes to hex (for the known answers). -/
def toHex (s : State) : String :=
  String.join (s.toList.map fun b =>
    let h := Nat.toDigits 16 b.toNat
    String.ofList (if h.length = 1 then '0' :: h else h))

#guard toHex (keccakP800 (stateOfHex (String.ofList (List.replicate 200 '0')))) =
  "0b3e6e25cb9aebd24d7f25c1669636eda9cf4ef7c9ea4dd58c308e1793ea1968ad9f8d11c206fe0191e28d4492422ba45af67a62c6f049978fc1f2c59a3ab148c73381d02bb9f603e2a081eecae2b83814ba14e9b8f23d2d2e537a35ac9180493a826fdd"

#guard toHex (keccakP800 (Vector.ofFn fun k => UInt8.ofNat k.1)) =
  "3765d4757348c5173de2c85f54ab6137aed4488c50bc6c17fe679108ddd4726a1ccc9b98a38abf6630a1655ab06fd3777ef1d6d5aa131b590dfe9ec4dde3bfe995a545844d555a9b2ceccbe84bad748a1c772a80869080f06b4681a4780ae1f073888416"

end VoleMole.Arith.Keccak
