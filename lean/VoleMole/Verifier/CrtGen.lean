import VoleMole.Verifier.VOLE
import VoleMole.Verifier.CrtData

/-!
# The CRT VOLE tables: recomputed parts, the defining identity, and the row tables

From `CrtData` (faest-arch-opt's generated matrices for FAEST-EM-128f):

* `wCrtOk`, `mTreeOk`: `W_crt` and `M_tree` are recomputed from the tree moduli `M_0 … M_16`:
  column `p_i + b` of `W_crt` is the CRT basis polynomial `≡ x^b (mod M_i)`, `≡ 0 (mod M_j)` for
  `j ≠ i`, of degree `< 120` (`Q_i · (x^b Q_i⁻¹ mod M_i)` with `Q_i = M_tree / M_i`), and
  `M_tree = Π M_i`.
* `identityOk`: the bilinear identity that defines `F`, `G`, `W_tree`, `W_gate` (the JSON's
  `semantics.identity`): for all `u ∈ F₂¹²⁸`, `Δ' ∈ F₂¹²⁰` and `k < 128`, coefficient `k` of
  `u · D mod (x¹²⁸ + x⁷ + x² + x + 1)` with `D = W_crt Δ'` equals
  `⟨W_tree[k], r(u, Δ')⟩ ⊕ ⟨W_gate[k], g(u, Δ')⟩`, where `r` concatenates
  `(u mod M_i)(D mod M_i) mod M_i` and `g[e] = ⟨F[e], u⟩ ⟨G[e], Δ'⟩`. Both sides are bilinear, so
  checking the `128 · 120` basis pairs `(xⁱ, e_j)` proves it for all inputs (run time, in
  `lake exe verifier_vectors`).
* `tables`: the verifier's row tables (`CrtTables`), the bit-transposes of the matrices, as
  `tools/gen_crt_tables.py` writes them (`gen_lift_row_table`).

Polynomials over `F₂` are `Nat` bit vectors here (one-time computations, not on the verifier's hot
path).
-/

namespace VoleMole.Verifier.CrtGen

open CrtData

def hexDigit (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

def hexNat (s : String) : Nat := s.toList.foldl (fun acc c => 16 * acc + hexDigit c) 0

def moduli : Array Nat := treeModuliHex.map hexNat
def F : Array Nat := fHex.map hexNat
def G : Array Nat := gHex.map hexNat
def wTree : Array Nat := wTreeHex.map hexNat
def wGate : Array Nat := wGateHex.map hexNat
def wCrt : Array Nat := wCrtHex.map hexNat

/-- Carry-less product. -/
def pmul (a b : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:b.log2 + 1] do
    if b.testBit i then r := r ^^^ (a <<< i)
  return r

/-- Remainder modulo `m ≠ 0`. -/
def pmod (a m : Nat) : Nat := Id.run do
  let dm := m.log2
  let top := a.log2
  let mut a := a
  for s in [0:top + 1] do
    let i := top - s
    if i ≥ dm && a.testBit i then a := a ^^^ (m <<< (i - dm))
  return a

/-- Quotient modulo `m ≠ 0`. -/
def pdiv (a m : Nat) : Nat := Id.run do
  let dm := m.log2
  let mut a := a
  let mut q := 0
  let top := a.log2
  for s in [0:top + 1] do
    let i := top - s
    if i ≥ dm && a.testBit i then
      a := a ^^^ (m <<< (i - dm))
      q := q ||| (1 <<< (i - dm))
  return q

/-- Inverse modulo a small `m` (search). -/
def pinv (a m : Nat) : Nat :=
  ((List.range (2 ^ m.log2)).find? fun x => pmod (pmul a x) m == 1).getD 0

/-- Parity of `a AND b`. -/
def dot (a b : Nat) : Bool := Id.run do
  let mut x := a &&& b
  let mut p := false
  while x != 0 do
    p := !p
    x := x &&& (x - 1)
  return p

def degs : Array Nat := moduli.map (·.log2)
def offsets : Array Nat := Id.run do
  let mut o := #[]
  let mut acc := 0
  for d in degs do
    o := o.push acc
    acc := acc + d
  return o

def mTree : Nat := moduli.foldl pmul 1

def mTreeOk : Bool := mTree == hexNat mTreeHex

/-- The CRT basis polynomial for tree `i`, bit `b`. -/
def crtBasis (i b : Nat) : Nat :=
  let m := moduli[i]!
  let q := pdiv mTree m
  pmul q (pmod (pmul (1 <<< b) (pinv (pmod q m) m)) m)

/-- Column `j < 120` of `W_crt`, as a polynomial. -/
def wCrtCol (j : Nat) : Nat := wCrt.foldl (fun (acc, k) row =>
  (if row.testBit j then acc ||| (1 <<< k) else acc, k + 1)) (0, 0) |>.1

def wCrtOk : Bool := Id.run do
  for i in [0:degs.size] do
    for b in [0:degs[i]!] do
      if crtBasis i b != wCrtCol (offsets[i]! + b) then return false
  return wCrt.size == 128

/-- The defining identity on all basis pairs. -/
def identityOk : Bool := Id.run do
  let modulus := hexNat modulusHex
  let cols : Array Nat := (Array.range 120).map wCrtCol
  for i in [0:128] do
    let u := 1 <<< i
    let uRes : Array Nat := moduli.map (pmod u ·)
    let fu : Array Bool := F.map (dot · u)
    for j in [0:120] do
      let D := cols[j]!
      let lhs := pmod (pmul u D) modulus
      let mut r := 0
      for t in [0:moduli.size] do
        let m := moduli[t]!
        r := r ||| (pmod (pmul uRes[t]! (pmod D m)) m <<< offsets[t]!)
      let mut g := 0
      for e in [0:F.size] do
        if fu[e]! && G[e]!.testBit j then g := g ||| (1 <<< e)
      for k in [0:128] do
        if lhs.testBit k != (dot wTree[k]! r ^^ dot wGate[k]! g) then return false
  return true

/-- A row of `cols` bits as a `W128` (`cols ≤ 128`). -/
def w128OfNat (x : Nat) : W128 := ⟨(x % 2 ^ 64).toUInt64, (x / 2 ^ 64 % 2 ^ 64).toUInt64⟩

/-- Row `j` of the transpose: bit `k` is bit `j` of `M[k]`. -/
def transposeRow (M : Array Nat) (j : Nat) : Nat := M.foldl (fun (acc, k) row =>
  (if row.testBit j then acc ||| (1 <<< k) else acc, k + 1)) (0, 0) |>.1

/-- The verifier's row tables. -/
def tables : CrtTables where
  mI := moduli.map Nat.toUInt64
  wCrt := (Array.range 120).map fun j => w128OfNat (transposeRow wCrt j)
  wTree := (Array.range 120).map fun j => w128OfNat (transposeRow wTree j)
  wGate := (Array.range 312).map fun e => w128OfNat (transposeRow wGate e)
  g := (Array.range 120).map fun j =>
    let x := transposeRow G j
    (Array.range 5).map fun w => (x / 2 ^ (64 * w) % 2 ^ 64).toUInt64

end VoleMole.Verifier.CrtGen
