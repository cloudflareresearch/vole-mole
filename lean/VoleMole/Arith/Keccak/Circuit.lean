import VoleMole.Arith.Basic

/-!
# The bit-level Keccak-p[800] round, generic over the type of a state bit (`src/keccak/circuit.hpp`)

Like the C++ templates, every layer is written once over an abstract "bit algebra" `BitOps T`
(`+`, `*`, `1`), so that the same definition is

* the constraint generator (`T = Expr F`, `BitOps.expr`),
* the plain semantics (`T = Bool`, XOR / AND, `BitOps.bool`),
* a degree counter (`T = ℕ` with `max` / `+`, `BitOps.deg`), and
* a bit-sliced evaluator (`T = ℕ` with bitwise XOR / AND, `BitOps.nat`), used to check the linear
  layers on all 800 basis vectors at once in `Keccak/Inverse.lean`.

States are `Vector T 800`; bit `i` is bit `z` of lane `(x, y)` for `i = 32(5y + x) + z`
(`tables.hpp:67-69`, `idx`). Index arithmetic mod 5 and mod 32 is `Fin` arithmetic, which equals the
C++ `(a + 5 - b) % 5` etc. on these ranges. Each `Vector.ofFn` is one C++ `push_back` loop, in the
same order, with the same left-associated sums, so the `Expr F` instance builds the same
expressions as the C++ (`add_const(x) = x + poly1(1)` is `O.add x O.one`).

Every layer comes with a *relational* lemma (`*_rel`): if a relation `R : T → U → Prop` is
preserved by the operations (`BitOps.Rel`, or `BitOps.AddRel` for the linear layers), it is
preserved by the layer, entrywise. Instances: `R e b := e.eval (ofBits w) = bitF b` (Expr ↔ Bool,
soundness and completeness), `R e n := e.degree ≤ n` (Expr ↔ ℕ, degree bookkeeping), and
`R n b := parity of n on s = b` (bit-sliced ↔ Bool).
-/

set_option linter.unusedSectionVars false

namespace VoleMole.Arith.Keccak

/-! ## Bit algebras and relations between them -/

/-- The operations a state-bit type must provide: `+` (XOR), `*` (AND) and the constant `1`. -/
structure BitOps (T : Type*) where
  add : T → T → T
  mul : T → T → T
  one : T

/-- Plain bits. -/
def BitOps.bool : BitOps Bool := ⟨xor, and, true⟩

/-- Constraint expressions (`qs_bit` in the C++): `poly1(1)` is `Expr.const 1`. -/
def BitOps.expr {F : Type*} [One F] : BitOps (Expr F) := ⟨Expr.add, Expr.mul, Expr.const 1⟩

/-- Degree counting: `deg (a + b) = max`, `deg (a b) = deg a + deg b`, `deg 1 = 0`. -/
def BitOps.deg : BitOps ℕ := ⟨max, (· + ·), 0⟩

/-- Bit-sliced plain bits: bit `k` of each number is an independent evaluation. -/
def BitOps.nat : BitOps ℕ := ⟨(· ^^^ ·), (· &&& ·), 0⟩

variable {T U : Type*}

/-- `R` is preserved by `+`. -/
structure BitOps.AddRel (O : BitOps T) (P : BitOps U) (R : T → U → Prop) : Prop where
  add : ∀ {a a' b b'}, R a a' → R b b' → R (O.add a b) (P.add a' b')

/-- `R` is preserved by `+`, `*` and `1`. -/
structure BitOps.Rel (O : BitOps T) (P : BitOps U) (R : T → U → Prop) : Prop
    extends BitOps.AddRel O P R where
  mul : ∀ {a a' b b'}, R a a' → R b b' → R (O.mul a b) (P.mul a' b')
  one : R O.one P.one

/-- Entrywise relation of two vectors. -/
def VRel (R : T → U → Prop) {n : ℕ} (v : Vector T n) (v' : Vector U n) : Prop :=
  ∀ i (h : i < n), R v[i] v'[i]

theorem VRel.get {R : T → U → Prop} {n : ℕ} {v : Vector T n} {v' : Vector U n}
    (h : VRel R v v') (i : Fin n) : R v[i] v'[i] := h i.1 i.2

/-! ## Constants (`src/keccak/tables.hpp`) -/

/-- Rho offsets `KECCAK_RHO[x][y]` reduced mod 32 (`tables.hpp:54-64`; checked against the
generating loop in `Keccak/Ref.lean`). -/
def rhoTable : List (List ℕ) :=
  [[0, 4, 3, 9, 18], [1, 12, 10, 13, 2], [30, 6, 11, 15, 29], [28, 23, 25, 21, 24],
   [27, 20, 7, 8, 14]]

/-- `KECCAK_RHO[x][y]` as an element of `Fin 32`. -/
def rho (x y : Fin 5) : Fin 32 := Fin.ofNat 32 ((rhoTable.getD x.1 []).getD y.1 0)

/-- Round constants `KP800_RC` (`tables.hpp:45-51`; checked against FIPS 202 Algorithms 5-6 in
`Keccak/Ref.lean`). Rounds `≥ 12` get `0`. -/
def rcTable : List (BitVec 32) :=
  [0x80008009, 0x8000000A, 0x8000808B, 0x0000008B, 0x00008089, 0x00008003, 0x00008002,
   0x00000080, 0x0000800A, 0x8000000A, 0x80008081, 0x00008080]

/-- `KP800_RC[j]`. -/
def rc (j : ℕ) : BitVec 32 := rcTable.getD j 0

/-- `KECCAK_THETA_INV_Q = 0b10011` (`tables.hpp:90-110`; checked in `Keccak/Ref.lean`). -/
def thetaInvQ : ℕ := 0b10011

/-! ## Indices -/

/-- `keccak_bit_index(x, y, z) = 32(5y + x) + z`. -/
def idx (x y : Fin 5) (z : Fin 32) : Fin 800 := ⟨32 * (5 * y.1 + x.1) + z.1, by omega⟩

/-- `x = (i / w) % 5`. -/
def ix (i : Fin 800) : Fin 5 := ⟨i.1 / 32 % 5, Nat.mod_lt _ (by norm_num)⟩
/-- `y = (i / w) / 5`. -/
def iy (i : Fin 800) : Fin 5 := ⟨i.1 / 32 / 5, by omega⟩
/-- `z = i % w`. -/
def iz (i : Fin 800) : Fin 32 := ⟨i.1 % 32, Nat.mod_lt _ (by norm_num)⟩

/-- Index `w x + z` of a column. -/
def cidx (x : Fin 5) (z : Fin 32) : Fin 160 := ⟨32 * x.1 + z.1, by omega⟩
/-- `x` of column index `j`. -/
def cx (j : Fin 160) : Fin 5 := ⟨j.1 / 32, by omega⟩
/-- `z` of column index `j`. -/
def cz (j : Fin 160) : Fin 32 := ⟨j.1 % 32, Nat.mod_lt _ (by norm_num)⟩

@[simp] theorem ix_idx (x y : Fin 5) (z : Fin 32) : ix (idx x y z) = x := by
  ext; simp only [ix, idx]; omega
@[simp] theorem iy_idx (x y : Fin 5) (z : Fin 32) : iy (idx x y z) = y := by
  ext; simp only [iy, idx]; omega
@[simp] theorem iz_idx (x y : Fin 5) (z : Fin 32) : iz (idx x y z) = z := by
  ext; simp only [iz, idx]; omega
@[simp] theorem idx_decode (i : Fin 800) : idx (ix i) (iy i) (iz i) = i := by
  ext; simp only [idx, ix, iy, iz]; omega
@[simp] theorem cx_cidx (x : Fin 5) (z : Fin 32) : cx (cidx x z) = x := by
  ext; simp only [cx, cidx]; omega
@[simp] theorem cz_cidx (x : Fin 5) (z : Fin 32) : cz (cidx x z) = z := by
  ext; simp only [cz, cidx]; omega
@[simp] theorem cidx_decode (j : Fin 160) : cidx (cx j) (cz j) = j := by
  ext; simp only [cidx, cx, cz]; omega

theorem idx_lt_32 (x y : Fin 5) (z : Fin 32) : (idx x y z).1 < 32 ↔ x = 0 ∧ y = 0 := by
  simp only [idx, Fin.ext_iff, Fin.val_zero]; omega

/-! ## The layers -/

section Layers

variable (O : BitOps T)

/-- Column parities `C[x][z] = Σ_y A[x][y][z]` (`circuit.hpp:35-42`, `:110-117`). -/
def colParity (a : Vector T 800) : Vector T 160 :=
  Vector.ofFn fun j =>
    O.add (O.add (O.add (O.add a[idx (cx j) 0 (cz j)] a[idx (cx j) 1 (cz j)])
      a[idx (cx j) 2 (cz j)]) a[idx (cx j) 3 (cz j)]) a[idx (cx j) 4 (cz j)]

/-- `keccak_theta_rho_pi` (`circuit.hpp:29-60`): `L = π ∘ ρ ∘ θ`. -/
def thetaRhoPi (a : Vector T 800) : Vector T 800 :=
  let col := colParity O a
  let d : Vector T 160 := Vector.ofFn fun j =>
    O.add col[cidx (cx j + 4) (cz j)] col[cidx (cx j + 1) (cz j - 1)]
  Vector.ofFn fun i =>
    let sx := ix i + 3 * iy i
    let sy := ix i
    let sz := iz i - rho sx sy
    O.add a[idx sx sy sz] d[cidx sx sz]

/-- The χ lambda of `qs_keccak_round` (`segmented.hpp:133-136`): `a + (b + 1) c`. -/
def chi (a b c : T) : T := O.add a (O.mul (O.add b O.one) c)

/-- χ and ι of `keccak_round` (`circuit.hpp:73-90`) on `b = L(in)`, computing only the first `n`
output bits. -/
def chiIota (j n : ℕ) (hn : n ≤ 800) (b : Vector T 800) : Vector T n :=
  Vector.ofFn fun i =>
    let i' : Fin 800 := ⟨i.1, by omega⟩
    let v := chi O b[i'] b[idx (ix i' + 1) (iy i') (iz i')] b[idx (ix i' + 2) (iy i') (iz i')]
    if i.1 < 32 ∧ (rc j).getLsbD i.1 = true then O.add v O.one else v

/-- `qs_keccak_round(in, j, n)` (`segmented.hpp:130-139`, `circuit.hpp:78-91`). -/
def roundN (j n : ℕ) (hn : n ≤ 800) (a : Vector T 800) : Vector T n :=
  chiIota O j n hn (thetaRhoPi O a)

/-- A full round `R_j`. -/
def round (j : ℕ) (a : Vector T 800) : Vector T 800 := roundN O j 800 le_rfl a

/-- One step of the `p` loop of `keccak_theta_rho_pi_inverse` (`circuit.hpp:132-142`):
`p ↦ (1 + M^s) p`. -/
def thetaInvStep (p : Vector T 160) (s : ℕ) : Vector T 160 :=
  Vector.ofFn fun j =>
    O.add (O.add p[j] p[cidx (cx j - Fin.ofNat 5 s) (cz j)]) p[cidx (cx j + Fin.ofNat 5 s) (cz j - Fin.ofNat 32 s)]

/-- One step of the `d` accumulation (`circuit.hpp:147-155`). -/
def thetaInvAcc (p : Vector T 160) (j : Fin 160) (acc : T) (i : ℕ) : T :=
  if thetaInvQ.testBit i then O.add acc p[cidx (cx j + Fin.ofNat 5 i) (cz j)] else acc

/-- `keccak_theta_rho_pi_inverse` (`circuit.hpp:94-155`): `L⁻`. -/
def thetaRhoPiInv (b : Vector T 800) : Vector T 800 :=
  let a : Vector T 800 := Vector.ofFn fun i =>
    b[idx (iy i) (2 * (ix i - iy i)) (iz i + rho (ix i) (iy i))]
  let col := colParity O a
  let p := [1, 2, 4, 8, 16].foldl (thetaInvStep O) col
  let d : Vector T 160 := Vector.ofFn fun j => [0, 1, 2, 3, 4].foldl (thetaInvAcc O p j) col[j]
  Vector.ofFn fun i => O.add a[i] d[cidx (ix i) (iz i)]

/-- The χ⁻¹ lambda of `qs_keccak_iota_chi_inverse` (`segmented.hpp:159-166`):
`a + (b + 1)(c + (d + 1) e)`. -/
def chiInv (a b c d e : T) : T := O.add a (O.mul (O.add b O.one) (O.add c (O.mul (O.add d O.one) e)))

/-- ι of round `j` on a full state (`circuit.hpp:177-183`). -/
def iota (j : ℕ) (s : Vector T 800) : Vector T 800 :=
  Vector.ofFn fun i => if i.1 < 32 ∧ (rc j).getLsbD i.1 = true then O.add s[i] O.one else s[i]

/-- `keccak_iota_chi_inverse` (`circuit.hpp:161-187`): `N_j⁻ = χ⁻¹ ∘ ι_j`. The output is pushed in
`(y, x, z)` order, which is index order. -/
def iotaChiInv (j : ℕ) (s : Vector T 800) : Vector T 800 :=
  let a := iota O j s
  Vector.ofFn fun i =>
    chiInv O a[idx (ix i) (iy i) (iz i)] a[idx (ix i + 1) (iy i) (iz i)]
      a[idx (ix i + 2) (iy i) (iz i)] a[idx (ix i + 3) (iy i) (iz i)] a[idx (ix i + 4) (iy i) (iz i)]

end Layers

/-! ## Relational lemmas -/

section Rel

variable {O : BitOps T} {P : BitOps U} {R : T → U → Prop}

theorem colParity_rel (hR : BitOps.AddRel O P R) {a : Vector T 800} {a' : Vector U 800}
    (h : VRel R a a') : VRel R (colParity O a) (colParity P a') := by
  intro i hi
  simp only [colParity, Vector.getElem_ofFn]
  exact hR.add (hR.add (hR.add (hR.add (h.get _) (h.get _)) (h.get _)) (h.get _)) (h.get _)

theorem thetaRhoPi_rel (hR : BitOps.AddRel O P R) {a : Vector T 800} {a' : Vector U 800}
    (h : VRel R a a') : VRel R (thetaRhoPi O a) (thetaRhoPi P a') := by
  have hc := colParity_rel hR h
  intro i hi
  simp only [thetaRhoPi, Vector.getElem_ofFn, Fin.getElem_fin]
  exact hR.add (h _ _) (hR.add (hc _ _) (hc _ _))

theorem chi_rel (hR : BitOps.Rel O P R) {a a' b b' c c'} (ha : R a a') (hb : R b b')
    (hc : R c c') : R (chi O a b c) (chi P a' b' c') :=
  hR.add ha (hR.mul (hR.add hb hR.one) hc)

theorem chiInv_rel (hR : BitOps.Rel O P R) {a a' b b' c c' d d' e e'} (ha : R a a') (hb : R b b')
    (hc : R c c') (hd : R d d') (he : R e e') :
    R (chiInv O a b c d e) (chiInv P a' b' c' d' e') :=
  hR.add ha (hR.mul (hR.add hb hR.one) (hR.add hc (hR.mul (hR.add hd hR.one) he)))

theorem chiIota_rel (hR : BitOps.Rel O P R) (j n : ℕ) (hn : n ≤ 800) {a : Vector T 800}
    {a' : Vector U 800} (h : VRel R a a') : VRel R (chiIota O j n hn a) (chiIota P j n hn a') := by
  intro i hi
  simp only [chiIota, Vector.getElem_ofFn, Fin.getElem_fin]
  split_ifs
  · exact hR.add (chi_rel hR (h i (by omega)) (h.get _) (h.get _)) hR.one
  · exact chi_rel hR (h i (by omega)) (h.get _) (h.get _)

theorem roundN_rel (hR : BitOps.Rel O P R) (j n : ℕ) (hn : n ≤ 800) {a : Vector T 800}
    {a' : Vector U 800} (h : VRel R a a') : VRel R (roundN O j n hn a) (roundN P j n hn a') :=
  chiIota_rel hR j n hn (thetaRhoPi_rel hR.toAddRel h)

theorem round_rel (hR : BitOps.Rel O P R) (j : ℕ) {a : Vector T 800} {a' : Vector U 800}
    (h : VRel R a a') : VRel R (round O j a) (round P j a') :=
  roundN_rel hR j 800 le_rfl h

theorem thetaInvStep_rel (hR : BitOps.AddRel O P R) (s : ℕ) {p : Vector T 160}
    {p' : Vector U 160} (h : VRel R p p') : VRel R (thetaInvStep O p s) (thetaInvStep P p' s) := by
  intro i hi
  simp only [thetaInvStep, Vector.getElem_ofFn, Fin.getElem_fin]
  exact hR.add (hR.add (h _ _) (h _ _)) (h _ _)

theorem foldl_thetaInvStep_rel (hR : BitOps.AddRel O P R) (l : List ℕ) {p : Vector T 160}
    {p' : Vector U 160} (h : VRel R p p') :
    VRel R (l.foldl (thetaInvStep O) p) (l.foldl (thetaInvStep P) p') := by
  induction l generalizing p p' with
  | nil => exact h
  | cons s l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (thetaInvStep_rel hR s h)

theorem foldl_thetaInvAcc_rel (hR : BitOps.AddRel O P R) {p : Vector T 160} {p' : Vector U 160}
    (h : VRel R p p') (j : Fin 160) (l : List ℕ) {acc : T} {acc' : U} (hacc : R acc acc') :
    R (l.foldl (thetaInvAcc O p j) acc) (l.foldl (thetaInvAcc P p' j) acc') := by
  induction l generalizing acc acc' with
  | nil => exact hacc
  | cons i l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    simp only [thetaInvAcc]
    split_ifs
    · exact hR.add hacc (h.get _)
    · exact hacc

theorem thetaRhoPiInv_tail_rel (hR : BitOps.AddRel O P R) {a : Vector T 800} {a' : Vector U 800}
    (ha : VRel R a a') :
    VRel R (let col := colParity O a
      let p := [1, 2, 4, 8, 16].foldl (thetaInvStep O) col
      let d : Vector T 160 := Vector.ofFn fun j => [0, 1, 2, 3, 4].foldl (thetaInvAcc O p j) col[j]
      Vector.ofFn fun i => O.add a[i] d[cidx (ix i) (iz i)])
    (let col := colParity P a'
      let p := [1, 2, 4, 8, 16].foldl (thetaInvStep P) col
      let d : Vector U 160 := Vector.ofFn fun j => [0, 1, 2, 3, 4].foldl (thetaInvAcc P p j) col[j]
      Vector.ofFn fun i => P.add a'[i] d[cidx (ix i) (iz i)]) := by
  have hc := colParity_rel hR ha
  have hp := foldl_thetaInvStep_rel hR [1, 2, 4, 8, 16] hc
  have hd : VRel R
      (Vector.ofFn fun j => [0, 1, 2, 3, 4].foldl
        (thetaInvAcc O ([1, 2, 4, 8, 16].foldl (thetaInvStep O) (colParity O a)) j)
        (colParity O a)[j])
      (Vector.ofFn fun j => [0, 1, 2, 3, 4].foldl
        (thetaInvAcc P ([1, 2, 4, 8, 16].foldl (thetaInvStep P) (colParity P a')) j)
        (colParity P a')[j]) := by
    intro j hj
    rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
    exact foldl_thetaInvAcc_rel hR hp _ _ (hc.get _)
  intro i hi
  simp only
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  exact hR.add (ha _ _) (hd.get _)

theorem thetaRhoPiInv_rel (hR : BitOps.AddRel O P R) {b : Vector T 800} {b' : Vector U 800}
    (h : VRel R b b') : VRel R (thetaRhoPiInv O b) (thetaRhoPiInv P b') := by
  have ha : VRel R (Vector.ofFn fun i : Fin 800 =>
      b[idx (iy i) (2 * (ix i - iy i)) (iz i + rho (ix i) (iy i))])
      (Vector.ofFn fun i : Fin 800 =>
      b'[idx (iy i) (2 * (ix i - iy i)) (iz i + rho (ix i) (iy i))]) := by
    intro i hi; simp only [Vector.getElem_ofFn]; exact h.get _
  exact thetaRhoPiInv_tail_rel hR ha

theorem iota_rel (hR : BitOps.Rel O P R) (j : ℕ) {s : Vector T 800} {s' : Vector U 800}
    (h : VRel R s s') : VRel R (iota O j s) (iota P j s') := by
  intro i hi
  simp only [iota, Vector.getElem_ofFn]
  split_ifs
  · exact hR.add (h _ _) hR.one
  · exact h _ _

theorem iotaChiInv_rel (hR : BitOps.Rel O P R) (j : ℕ) {s : Vector T 800} {s' : Vector U 800}
    (h : VRel R s s') : VRel R (iotaChiInv O j s) (iotaChiInv P j s') := by
  have ha := iota_rel hR j h
  intro i hi
  simp only [iotaChiInv, Vector.getElem_ofFn]
  exact chiInv_rel hR (ha.get _) (ha.get _) (ha.get _) (ha.get _) (ha.get _)

end Rel

end VoleMole.Arith.Keccak
