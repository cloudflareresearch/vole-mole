import VoleMole.Arith.Keccak.Circuit

/-!
# The inverse layers invert the round (facts F1 and F2 of `L7-keccak.md` §2.3)

On plain bits (`BitOps.bool`):

* `thetaRhoPi_thetaRhoPiInv`, `thetaRhoPiInv_thetaRhoPi`: `L ∘ L⁻ = L⁻ ∘ L = id` (F1).
* `chiIota_iotaChiInv`, `iotaChiInv_chiIota`: `N_j ∘ N_j⁻ = N_j⁻ ∘ N_j = id` for every `j` (F2),
  with the χ and χ⁻¹ lambdas as used to generate constraints.

`L7-keccak.md` checks F1 on the 800 unit vectors by a test. Here F1 is proved: `L` splits as the
permutation `π ∘ ρ` after `θ` (`thetaRhoPi_eq`), `L⁻` as `θ⁻¹` after `(π ∘ ρ)⁻¹` (by definition),
the permutations are checked to be mutually inverse on all 800 indices (`decide`), and `θ ∘ θ⁻¹ = id`
reduces to an identity of translation-invariant linear maps on the 160 column parities. Such maps
are XORs of translates (`conv`), composition multiplies the lists of translations (`conv_mulL`),
and a list in which every translation occurs an even number of times gives the zero map
(`conv_eq_false`). The identity `(1 + M) Q⁻¹ (1 + M)(1 + M²)⋯(1 + M¹⁶) = 1` of
`tables.hpp:73-89` is then a parity count on a list of 1459 translations (`total_mask`,
`totalInv_mask`), checked by `decide` on a bit mask.
-/

set_option linter.unusedSectionVars false

namespace VoleMole.Arith.Keccak

/-! ## Translation-invariant maps on the column parities -/

/-- Column coordinates `(x, z)`. -/
abbrev Col := Fin 5 × Fin 32

/-- `v ↦ Σ_{t ∈ l} v(· - t)` on functions `Col → Bool`. -/
def conv (l : List Col) (v : Col → Bool) (g : Col) : Bool :=
  l.foldr (fun t b => xor (v (g - t)) b) false

/-- The product of two lists of translations. -/
def mulL (l₁ l₂ : List Col) : List Col := l₁.flatMap fun a => l₂.map (a + ·)

/-- An injective code of a translation. -/
def colCode (g : Col) : ℕ := 32 * g.1.1 + g.2.1

/-- Bit `colCode g` is the parity of the multiplicity of `g` in `l`. -/
def parityMask (l : List Col) : ℕ := l.foldr (fun g n => 2 ^ colCode g ^^^ n) 0

@[simp] theorem conv_nil (v : Col → Bool) (g : Col) : conv [] v g = false := rfl

@[simp] theorem conv_cons (t : Col) (l : List Col) (v : Col → Bool) (g : Col) :
    conv (t :: l) v g = xor (v (g - t)) (conv l v g) := rfl

theorem conv_append (l₁ l₂ : List Col) (v : Col → Bool) (g : Col) :
    conv (l₁ ++ l₂) v g = xor (conv l₁ v g) (conv l₂ v g) := by
  induction l₁ with
  | nil => simp
  | cons t l ih => simp [ih]

theorem conv_xor (l : List Col) (u v : Col → Bool) (g : Col) :
    conv l (fun h => xor (u h) (v h)) g = xor (conv l u g) (conv l v g) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [conv_cons, ih]
    cases u (g - t) <;> cases v (g - t) <;> simp

theorem conv_map_add (a : Col) (l : List Col) (v : Col → Bool) (g : Col) :
    conv (l.map (a + ·)) v g = conv l v (g - a) := by
  induction l with
  | nil => simp
  | cons t l ih => simp [ih, sub_add_eq_sub_sub]

theorem conv_mulL (l₁ l₂ : List Col) (v : Col → Bool) (g : Col) :
    conv (mulL l₁ l₂) v g = conv l₁ (conv l₂ v) g := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    simp only [mulL, List.flatMap_cons] at ih ⊢
    rw [conv_append, conv_map_add, ih, conv_cons]

theorem conv_mulL' (l₁ l₂ : List Col) (v : Col → Bool) :
    conv (mulL l₁ l₂) v = conv l₁ (conv l₂ v) := funext (conv_mulL l₁ l₂ v)

theorem colCode_inj {g h : Col} (e : colCode g = colCode h) : g = h := by
  obtain ⟨⟨x, hx⟩, ⟨z, hz⟩⟩ := g
  obtain ⟨⟨x', hx'⟩, ⟨z', hz'⟩⟩ := h
  simp only [colCode] at e
  have : x = x' := by omega
  have : z = z' := by omega
  subst_vars; rfl

theorem parityMask_perm {l l' : List Col} (p : l.Perm l') : parityMask l = parityMask l' := by
  unfold parityMask
  apply p.foldr_eq'
  intro x _ y _ z
  rw [← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_comm (2 ^ colCode y)]

theorem conv_perm {l l' : List Col} (p : l.Perm l') (v : Col → Bool) (g : Col) :
    conv l v g = conv l' v g := by
  unfold conv
  apply p.foldr_eq'
  intro x _ y _ z
  rw [← Bool.xor_assoc, ← Bool.xor_assoc, Bool.xor_comm (v (g - y))]

theorem mem_of_testBit_parityMask {l : List Col} {k : ℕ} (h : (parityMask l).testBit k = true) :
    ∃ g ∈ l, colCode g = k := by
  induction l with
  | nil => simp [parityMask] at h
  | cons t l ih =>
    simp only [parityMask, List.foldr_cons, Nat.testBit_xor, Nat.testBit_two_pow] at h
    by_cases e : colCode t = k
    · exact ⟨t, List.mem_cons_self, e⟩
    · simp only [e, decide_false, Bool.false_xor] at h
      obtain ⟨g, hg, hc⟩ := ih h
      exact ⟨g, List.mem_cons_of_mem _ hg, hc⟩

theorem parityMask_cons (t : Col) (l : List Col) :
    parityMask (t :: l) = 2 ^ colCode t ^^^ parityMask l := rfl

theorem nat_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  have := congrArg (a ^^^ ·) h
  simpa [← Nat.xor_assoc] using this.symm

/-- A list in which every translation occurs an even number of times gives the zero map. -/
theorem conv_eq_false : ∀ (n : ℕ) (l : List Col), l.length = n → parityMask l = 0 →
    ∀ v g, conv l v g = false := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hl hm v g
    match l, hl, hm with
    | [], _, _ => rfl
    | t :: l, hl, hm =>
      rw [parityMask_cons] at hm
      have hl' := (nat_xor_eq_zero hm).symm
      have hbit : (parityMask l).testBit (colCode t) = true := by simp [hl']
      obtain ⟨t', ht', hc⟩ := mem_of_testBit_parityMask hbit
      have := colCode_inj hc; subst this
      have hp := List.perm_cons_erase ht'
      have hm' : parityMask (l.erase t') = 0 := by
        have := parityMask_perm hp
        rw [parityMask_cons, hl'] at this
        have := congrArg (2 ^ colCode t' ^^^ ·) this
        simpa [← Nat.xor_assoc] using this.symm
      have hlen : (l.erase t').length < n := by
        rw [List.length_erase_of_mem ht']; simp at hl; omega
      rw [conv_cons, conv_perm hp, conv_cons, ih _ hlen _ rfl hm' v g]
      simp

theorem conv_eq_false' {l : List Col} (hm : parityMask l = 0) (v : Col → Bool) (g : Col) :
    conv l v g = false := conv_eq_false _ l rfl hm v g

/-! ## The column operators of θ and θ⁻¹ -/

/-- `M`: `D[x][z] = C[x-1][z] + C[x+1][z-1]` (`circuit.hpp:44-48`, written `x + 4`). -/
def ML : List Col := [(-4, 0), (-1, 1)]

/-- One factor `1 + M^s` of the `p` loop (`circuit.hpp:132-142`). -/
def stepL (s : ℕ) : List Col := [(0, 0), (Fin.ofNat 5 s, 0), (-Fin.ofNat 5 s, Fin.ofNat 32 s)]

/-- `(1 + M^16) ⋯ (1 + M^2)(1 + M)`. -/
def PL : List Col := mulL (stepL 16) (mulL (stepL 8) (mulL (stepL 4) (mulL (stepL 2) (stepL 1))))

/-- `Q⁻¹ = 1 + X + X⁴` (`KECCAK_THETA_INV_Q = 0b10011`), as translations by `-i` in `x`. -/
def QL : List Col := [(-Fin.ofNat 5 0, 0), (-Fin.ofNat 5 1, 0), (-Fin.ofNat 5 4, 0)]

/-- `1 + (1 + M) Q⁻¹ P`, which must vanish (for `θ ∘ θ⁻¹ = id`). -/
def totalL : List Col := mulL ((0, 0) :: ML) (mulL QL PL) ++ [(0, 0)]

/-- `1 + Q⁻¹ P + Q⁻¹ P M`, which must vanish (for `θ⁻¹ ∘ θ = id`). -/
def totalInvL : List Col := (0, 0) :: (mulL QL PL ++ mulL (mulL QL PL) ML)

theorem total_mask : parityMask totalL = 0 := by decide +kernel
theorem totalInv_mask : parityMask totalInvL = 0 := by decide +kernel

/-- Column parities as a function of `(x, z)`. -/
def toCol (v : Vector Bool 160) : Col → Bool := fun g => v[cidx g.1 g.2]

theorem toCol_thetaInvStep (p : Vector Bool 160) (s : ℕ) :
    toCol (thetaInvStep BitOps.bool p s) = conv (stepL s) (toCol p) := by
  funext g
  simp [toCol, thetaInvStep, stepL, BitOps.bool]

theorem toCol_foldl_thetaInvStep (v : Vector Bool 160) :
    toCol ([1, 2, 4, 8, 16].foldl (thetaInvStep BitOps.bool) v) = conv PL (toCol v) := by
  funext g
  simp only [List.foldl_cons, List.foldl_nil, toCol_thetaInvStep, PL, conv_mulL']

/-! ## θ and θ⁻¹ -/

section Theta

variable {T : Type*} (O : BitOps T)

/-- θ alone: `A[x][y][z] + D[x][z]` with `D` as in `keccak_theta_rho_pi`. -/
def theta (a : Vector T 800) : Vector T 800 :=
  let col := colParity O a
  let d : Vector T 160 := Vector.ofFn fun j =>
    O.add col[cidx (cx j + 4) (cz j)] col[cidx (cx j + 1) (cz j - 1)]
  Vector.ofFn fun i => O.add a[i] d[cidx (ix i) (iz i)]

/-- θ⁻¹: the second half of `keccak_theta_rho_pi_inverse` (`circuit.hpp:120-162`). -/
def thetaInv (a : Vector T 800) : Vector T 800 :=
  let col := colParity O a
  let p := [1, 2, 4, 8, 16].foldl (thetaInvStep O) col
  let d : Vector T 160 := Vector.ofFn fun j => [0, 1, 2, 3, 4].foldl (thetaInvAcc O p j) col[j]
  Vector.ofFn fun i => O.add a[i] d[cidx (ix i) (iz i)]

/-- The source index of `π ∘ ρ` (`circuit.hpp:64-69`). -/
def piSrc (i : Fin 800) : Fin 800 :=
  idx (ix i + 3 * iy i) (ix i) (iz i - rho (ix i + 3 * iy i) (ix i))

/-- The source index of `(π ∘ ρ)⁻¹` (`circuit.hpp:101-108`). -/
def piSrcInv (i : Fin 800) : Fin 800 := idx (iy i) (2 * (ix i - iy i)) (iz i + rho (ix i) (iy i))

/-- `π ∘ ρ`. -/
def piRho (v : Vector T 800) : Vector T 800 := Vector.ofFn fun i => v[piSrc i]
/-- `(π ∘ ρ)⁻¹`. -/
def piRhoInv (v : Vector T 800) : Vector T 800 := Vector.ofFn fun i => v[piSrcInv i]

theorem thetaRhoPi_eq (a : Vector T 800) : thetaRhoPi O a = piRho (theta O a) := by
  ext i hi
  simp [thetaRhoPi, piRho, theta, piSrc]

theorem thetaRhoPiInv_eq (b : Vector T 800) : thetaRhoPiInv O b = thetaInv O (piRhoInv b) := rfl

theorem piSrcInv_piSrc : ∀ i, piSrcInv (piSrc i) = i := by decide +kernel
theorem piSrc_piSrcInv : ∀ i, piSrc (piSrcInv i) = i := by decide +kernel

theorem piRho_piRhoInv (v : Vector T 800) : piRho (piRhoInv v) = v := by
  ext i hi
  simp only [piRho, piRhoInv, Vector.getElem_ofFn, Fin.getElem_fin, Fin.eta, piSrcInv_piSrc]

theorem piRhoInv_piRho (v : Vector T 800) : piRhoInv (piRho v) = v := by
  ext i hi
  simp only [piRho, piRhoInv, Vector.getElem_ofFn, Fin.getElem_fin, Fin.eta, piSrc_piSrcInv]

end Theta

/-! ## `θ ∘ θ⁻¹ = θ⁻¹ ∘ θ = id` on plain bits -/

/-- Add a column function to every bit: `A[x][y][z] + f(x, z)`. -/
def addCol (a : Vector Bool 800) (f : Col → Bool) : Vector Bool 800 :=
  Vector.ofFn fun i => xor a[i] (f (ix i, iz i))

/-- The column parities `C` of a plain state. -/
def colOf (a : Vector Bool 800) : Col → Bool := toCol (colParity BitOps.bool a)

theorem theta_bool (a : Vector Bool 800) : theta BitOps.bool a = addCol a (conv ML (colOf a)) := by
  ext i hi
  simp [theta, addCol, colOf, toCol, ML, BitOps.bool]

theorem foldl_thetaInvAcc_bool (col p : Vector Bool 160) (j : Fin 160) :
    [0, 1, 2, 3, 4].foldl (thetaInvAcc BitOps.bool p j) col[j.1] =
      xor col[j.1] (conv QL (toCol p) (cx j, cz j)) := by
  have h0 : Nat.testBit 19 0 = true := by decide
  have h1 : Nat.testBit 19 1 = true := by decide
  have h2 : Nat.testBit 19 2 = false := by decide
  have h3 : Nat.testBit 19 3 = false := by decide
  have h4 : Nat.testBit 19 4 = true := by decide
  simp only [List.foldl_cons, List.foldl_nil, thetaInvAcc, thetaInvQ, h0, h1, h2, h3, h4,
    ite_true, Bool.false_eq_true, ite_false]
  simp [QL, toCol, BitOps.bool]

theorem thetaInv_bool (a : Vector Bool 800) :
    thetaInv BitOps.bool a = addCol a (fun g => xor (colOf a g) (conv QL (conv PL (colOf a)) g)) := by
  ext i hi
  have hp := toCol_foldl_thetaInvStep (colParity BitOps.bool a)
  simp only [thetaInv, addCol, Vector.getElem_ofFn, Fin.getElem_fin, Fin.eta]
  rw [foldl_thetaInvAcc_bool, hp]
  simp [colOf, toCol, BitOps.bool]

theorem xor5 (b₀ b₁ b₂ b₃ b₄ c : Bool) :
    xor (xor (xor (xor (xor b₀ c) (xor b₁ c)) (xor b₂ c)) (xor b₃ c)) (xor b₄ c) =
      xor (xor (xor (xor (xor b₀ b₁) b₂) b₃) b₄) c := by
  revert b₀ b₁ b₂ b₃ b₄ c; decide

theorem colOf_addCol (a : Vector Bool 800) (f : Col → Bool) :
    colOf (addCol a f) = fun g => xor (colOf a g) (f g) := by
  funext g
  simp only [colOf, toCol, colParity, addCol, BitOps.bool, Vector.getElem_ofFn, Fin.getElem_fin,
    Fin.eta, ix_idx, iz_idx, cx_cidx, cz_cidx]
  exact xor5 _ _ _ _ _ _

theorem addCol_addCol (a : Vector Bool 800) (f f' : Col → Bool) :
    addCol (addCol a f) f' = addCol a (fun g => xor (f g) (f' g)) := by
  ext i hi
  simp [addCol]

theorem addCol_eq_self (a : Vector Bool 800) {f : Col → Bool} (h : ∀ g, f g = false) :
    addCol a f = a := by
  ext i hi
  simp [addCol, h]

theorem col_sub_zero (g : Col) : g - (0, 0) = g := by simp [Prod.ext_iff]

theorem conv_xor' (l : List Col) (u v : Col → Bool) :
    conv l (fun h => xor (u h) (v h)) = fun g => xor (conv l u g) (conv l v g) :=
  funext (conv_xor l u v)

theorem theta_thetaInv (a : Vector Bool 800) : theta BitOps.bool (thetaInv BitOps.bool a) = a := by
  rw [thetaInv_bool, theta_bool, addCol_addCol, colOf_addCol]
  apply addCol_eq_self
  intro g
  have h := conv_eq_false' total_mask (colOf a) g
  simp only [totalL, conv_append, conv_mulL', conv_cons, conv_nil, col_sub_zero] at h
  have e : (fun g => xor (colOf a g) (xor (colOf a g) (conv QL (conv PL (colOf a)) g))) =
      conv QL (conv PL (colOf a)) := by funext g; simp
  rw [e]
  generalize conv ML (conv QL (conv PL (colOf a))) g = m at h ⊢
  generalize conv QL (conv PL (colOf a)) g = x at h ⊢
  generalize colOf a g = c at h ⊢
  revert h; revert m x c; decide

theorem thetaInv_theta (a : Vector Bool 800) : thetaInv BitOps.bool (theta BitOps.bool a) = a := by
  rw [theta_bool, thetaInv_bool, addCol_addCol, colOf_addCol]
  apply addCol_eq_self
  intro g
  have h := conv_eq_false' totalInv_mask (colOf a) g
  simp only [totalInvL, conv_append, conv_mulL', conv_cons, col_sub_zero] at h
  simp only [conv_xor']
  generalize conv QL (conv PL (conv ML (colOf a))) g = m at h ⊢
  generalize conv QL (conv PL (colOf a)) g = x at h ⊢
  generalize conv ML (colOf a) g = y at h ⊢
  generalize colOf a g = c at h ⊢
  revert h; revert m x y c; decide

/-- **F1**: `L ∘ L⁻ = id`. -/
theorem thetaRhoPi_thetaRhoPiInv (b : Vector Bool 800) :
    thetaRhoPi BitOps.bool (thetaRhoPiInv BitOps.bool b) = b := by
  rw [thetaRhoPi_eq, thetaRhoPiInv_eq, theta_thetaInv, piRho_piRhoInv]

/-- **F1**: `L⁻ ∘ L = id`. -/
theorem thetaRhoPiInv_thetaRhoPi (a : Vector Bool 800) :
    thetaRhoPiInv BitOps.bool (thetaRhoPi BitOps.bool a) = a := by
  rw [thetaRhoPi_eq, thetaRhoPiInv_eq, piRhoInv_piRho, thetaInv_theta]

/-! ## `N_j ∘ N_j⁻ = N_j⁻ ∘ N_j = id` on plain bits (F2)

Both act on the 160 rows `(y, z)` independently (S3, S4). Each output bit is unfolded to an
expression in the five bits of its row and the ι bit `c = (y = 0 ∧ RC_j[z])`, and the row identities
are checked by `decide` over all `2 · 32` row values and the 5 positions. -/

/-- ι on a row: flip bit `0` if `c`. -/
def rowIota (c : Bool) (r : Fin 5 → Bool) (k : Fin 5) : Bool :=
  if k = 0 ∧ c = true then BitOps.bool.add (r k) BitOps.bool.one else r k

/-- `N⁻` on a row. -/
def rowChiInv (c : Bool) (r : Fin 5 → Bool) (x : Fin 5) : Bool :=
  chiInv BitOps.bool (rowIota c r x) (rowIota c r (x + 1)) (rowIota c r (x + 2))
    (rowIota c r (x + 3)) (rowIota c r (x + 4))

/-- `N` on a row. -/
def rowChi (c : Bool) (r : Fin 5 → Bool) (x : Fin 5) : Bool :=
  rowIota c (fun k => chi BitOps.bool (r k) (r (k + 1)) (r (k + 2))) x

theorem rowChi_rowChiInv : ∀ c r x, rowChi c (rowChiInv c r) x = r x := by decide
theorem rowChiInv_rowChi : ∀ c r x, rowChiInv c (rowChi c r) x = r x := by decide

theorem chiIota_iotaChiInv (j : ℕ) (s : Vector Bool 800) :
    chiIota BitOps.bool j 800 le_rfl (iotaChiInv BitOps.bool j s) = s := by
  ext i hi
  obtain ⟨x, y, z, rfl⟩ := exists_idx i hi
  simp only [chiIota, iotaChiInv, iota, Vector.getElem_ofFn, Fin.getElem_fin, Fin.eta,
    ix_idx, iy_idx, iz_idx, iota_cond]
  have := rowChi_rowChiInv (decide (y = 0 ∧ (rc j).getLsbD z.1 = true)) (fun k => s[idx k y z]) x
  simp only [rowChi, rowChiInv, rowIota, decide_eq_true_eq, Fin.getElem_fin] at this
  exact this

theorem iotaChiInv_chiIota (j : ℕ) (b : Vector Bool 800) :
    iotaChiInv BitOps.bool j (chiIota BitOps.bool j 800 le_rfl b) = b := by
  ext i hi
  obtain ⟨x, y, z, rfl⟩ := exists_idx i hi
  simp only [chiIota, iotaChiInv, iota, Vector.getElem_ofFn, Fin.getElem_fin, Fin.eta,
    ix_idx, iy_idx, iz_idx, iota_cond]
  have := rowChiInv_rowChi (decide (y = 0 ∧ (rc j).getLsbD z.1 = true)) (fun k => b[idx k y z]) x
  simp only [rowChi, rowChiInv, rowIota, decide_eq_true_eq, Fin.getElem_fin] at this
  exact this

end VoleMole.Arith.Keccak
