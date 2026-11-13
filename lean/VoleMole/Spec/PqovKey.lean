import VoleMole.Spec.PqovSigner
import VoleMole.Spec.PqovSignerExec

/-!
# pqov's keys: the oil space and the system coefficients, from the key layout

`Spec/PqovSigner.lean` models pqov's `ov_preimage_core` with its linear system computed from the
public map's polar form (`sysMat`, `sysCoef`), and proves it correct for every key whose map
vanishes on the oil space (`OilSpace`). This file connects both to the layout of pqov's keys.

## The layout

The expanded key (`UOVKey.map`, `for_each_monomial`'s layout, `Arith.UOV.forEachMonomial 119 45`)
holds three blocks of 45-byte vectors (component `k` at `+ k`):

* `P1`, the upper-triangular `74 × 74` block, entry `(i, l)`, `i ≤ l < 74`, at `off1 i l`
  (pqov's `idx_of_trimat(i, l, 74)`, times 45): coefficient `c1 pk i l k` of `x_i x_l`;
* `P2`, the `74 × 45` block, row-major, entry `(i, j)` at `off2 i j`: coefficient `c2 pk i j k` of
  `x_i x_{74+j}`;
* `P3`, the upper-triangular `45 × 45` block, entry `(a, b)`, `a ≤ b`, at `off3 a b`: coefficient
  `c3 pk a b k` of `x_{74+a} x_{74+b}`.

`sum_forEachMonomial` splits any sum over the monomials into these three blocks, and
`qmap_eq_blocks` writes `P(σ)` in them.

## pqov's computation (`calculate_F2_P3`, `ov_keypair_computation.c:61-80`)

With `O` the oil matrix (`O j l = O[l][j]`, column `j` is the oil vector's vinegar part):

* `pqovS1 = P1·O + P2` (`batch_trimat_madd`, `P1` upper triangular);
* `pqovM = Oᵀ·pqovS1`, and `P3 = UT(M + Mᵀ)` (`batch_upper_matTr_x_mat`): `pqovP3 a b` is
  `M[a][b] + M[b][a]` for `a < b` and `M[a][a]` on the diagonal; this is `Verifier.Keygen.computeP3`
  (checked byte for byte against the C++ by `verifier_vectors` and `spec_kats`);
* `pqovS = (P1 + P1ᵀ)·O + P2` (`batch_trimatTr_madd` adds `P1ᵀ·O`): the secret `S` of `sk_t`,
  from which `ov_calc_l1_mat` builds `L_v = vᵀ S` (`l1_mat_from_s`; the `_OV_PKC_SKC` variant
  `l1_mat_from_p2` computes the same `vᵀ P2 + vᵀ(P1 + P1ᵀ)·O` without storing `S`).

`P3Pqov pk O` says that the `P3` block of `pk` is `pqovP3` of its own `P1`, `P2` blocks and `O`.

## Results

* **`oilSpace_of_P3Pqov`**: `P3Pqov pk O → OilSpace pk O`, for every `O` and all `P1`, `P2`: the
  standard UOV identity (on `ō(y) = (O y, y)`, `P(ō(y)) = Q₁ + Q₂ + Q₃` with
  `Q₃ = yᵀ M y = Q₁ + Q₂`, so `P(ō(y)) = 2(Q₁ + Q₂) = 0` in characteristic 2).
* **`sysCoef_eq_pqovS`** (for every key, no hypothesis on `P3`): the system coefficients the signer
  model computes from the polar form, `S k i j = B(e_i, ō_j)_k`, are pqov's stored
  `S = (P1 + P1ᵀ)·O + P2` read from the key layout. (The diagonal of `P1 + P1ᵀ` is `2·P1(i, i) = 0`.)
  So the model's `L_v = vᵀ S` (`sysMat_eq_sum`) is pqov's `ov_calc_l1_mat`.
* `qmap_vinVec_eq_P1`: `P(v, 0)` is `P₁(v) = Σ_{i ≤ l} P1(i, l) v_i v_l` (`batch_quad_trimat_eval`),
  the constant of pqov's system.
* `sysCoef_congr`, `pqovP3_congr`: `S` and pqov's `P3` depend on the key only through its `P1` and
  `P2` blocks.
-/

open Finset

namespace VoleMole.Spec.Pqov

open VoleMole.Arith VoleMole.Arith.UOV

/-! ## Triangle numbers -/

lemma triangle_succ (n : ℕ) : triangle (n + 1) = triangle n + (n + 1) := by
  unfold triangle
  rw [show (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) by ring,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

lemma triangle_mono {m n : ℕ} (h : m ≤ n) : triangle m ≤ triangle n :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

lemma le_triangle (n : ℕ) : n ≤ triangle n := by
  unfold triangle
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  rcases n with _ | m
  · simp
  · exact Nat.mul_le_mul_left _ (by omega)

lemma triangle_74' : triangle 74 = 2775 := by decide
lemma triangle_45 : triangle 45 = 1035 := by decide

/-! ## The block layout of the expanded key -/

/-- The offset of `P1` entry `(i, l)`, `i ≤ l < 74` (`45·idx_of_trimat(i, l, 74)`). -/
def off1 (i l : ℕ) : ℕ := 45 * (triangle 74 - triangle (74 - i)) + (l - i) * 45

/-- The offset of `P2` entry `(i, j)`, `i < 74`, `j < 45` (row-major, after `P1`). -/
def off2 (i j : ℕ) : ℕ := 45 * triangle 74 + i * (45 * 45) + j * 45

/-- The offset of `P3` entry `(a, b)`, `a ≤ b < 45` (`45·idx_of_trimat(a, b, 45)`, after `P2`). -/
def off3 (a b : ℕ) : ℕ :=
  45 * triangle 74 + 45 * 74 * 45 + 45 * (triangle 45 - triangle (45 - a)) + (b - a) * 45

/-- The `P1` coefficient of `x_i x_l` (`i ≤ l`) in component `k`. -/
def c1 (pk : UOVKey) (i l : Fin 74) (k : Fin 45) : GF256 := pk.map (off1 i l + k)

/-- The `P2` coefficient of `x_i x_{74+j}` in component `k`. -/
def c2 (pk : UOVKey) (i : Fin 74) (j : Fin 45) (k : Fin 45) : GF256 := pk.map (off2 i j + k)

/-- The `P3` coefficient of `x_{74+a} x_{74+b}` (`a ≤ b`) in component `k`. -/
def c3 (pk : UOVKey) (a b : Fin 45) (k : Fin 45) : GF256 := pk.map (off3 a b + k)

lemma list_sum_range' {β : Type*} [AddCommMonoid β] (n : ℕ) (g : ℕ → β) :
    ((List.range n).map g).sum = ∑ t ∈ range n, g t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

lemma list_sum_flatMap' {α β : Type*} [AddCommMonoid β] (f : ℕ → List α) (g : α → β)
    (L : List ℕ) : ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

lemma sum_row {β : Type*} [AddCommMonoid β] (g : Monomial → β) (i j0 n p : ℕ) :
    ((row 45 i j0 n p).map g).sum = ∑ t ∈ range (n - j0), g ⟨i, j0 + t, p + t * 45⟩ := by
  unfold row
  rw [List.map_map, list_sum_range']
  rfl

/-- A row of a triangular block as a masked sum over the full row. -/
lemma sum_tri_row {β : Type*} [AddCommMonoid β] (n i p : ℕ) (f : ℕ → ℕ → β) :
    ∑ t ∈ range (n - i), f (i + t) (p + t * 45) =
      ∑ l ∈ range n, if i ≤ l then f l (p + (l - i) * 45) else 0 := by
  rw [← Finset.sum_filter, show (range n).filter (fun l => i ≤ l) = Ico i n by
    ext l; simp only [mem_filter, mem_range, mem_Ico]; omega, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.add_sub_cancel_left]

/-- **Any sum over the monomials, by block**: `P1` (`i ≤ l < 74`), `P2` (`i < 74`, `74 + j`),
`P3` (`74 + a ≤ 74 + b`). -/
theorem sum_forEachMonomial {β : Type*} [AddCommMonoid β] (g : Monomial → β) :
    ((forEachMonomial 119 45).map g).sum =
      (∑ i : Fin 74, ∑ l : Fin 74, if (i : ℕ) ≤ l then g ⟨i, l, off1 i l⟩ else 0) +
      (∑ i : Fin 74, ∑ j : Fin 45, g ⟨i, 74 + j, off2 i j⟩) +
      (∑ a : Fin 45, ∑ b : Fin 45, if (a : ℕ) ≤ b then g ⟨74 + a, 74 + b, off3 a b⟩ else 0) := by
  unfold forEachMonomial
  simp only [Nat.reduceSub, List.map_append, List.sum_append, list_sum_flatMap', sum_row,
    List.sum_map_add]
  congr 1
  · congr 1
    · rw [list_sum_range', ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sum_tri_row 74 i _ (fun l o => g ⟨i, l, o⟩), ← Fin.sum_univ_eq_sum_range]
      rfl
  · rw [List.range'_eq_map_range, List.map_map, list_sum_range', ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.isLt
    simp only [Function.comp, show 119 - (74 + (a : ℕ)) = 45 - a by omega]
    refine (Finset.sum_congr rfl fun t _ => ?_).trans ((sum_tri_row 45 a
      (45 * triangle 74 + 45 * 74 * 45 + 45 * (triangle 45 - triangle (45 - a)))
      (fun l o => g ⟨74 + a, 74 + l, o⟩)).trans ?_)
    · exact congrArg g (by congr 1; omega)
    · rw [← Fin.sum_univ_eq_sum_range]
      rfl

/-- `P(σ)` by block. -/
theorem qmap_eq_blocks (pk : UOVKey) (σ : ℕ → GF256) (k : Fin 45) :
    qmap pk σ k =
      (∑ i : Fin 74, ∑ l : Fin 74, if (i : ℕ) ≤ l then c1 pk i l k * σ i * σ l else 0) +
      (∑ i : Fin 74, ∑ j : Fin 45, c2 pk i j k * σ i * σ (74 + j)) +
      (∑ a : Fin 45, ∑ b : Fin 45,
        if (a : ℕ) ≤ b then c3 pk a b k * σ (74 + a) * σ (74 + b) else 0) := by
  unfold qmap publicMap
  rw [sum_forEachMonomial]
  rfl

/-- The polar form by block. -/
theorem polar_eq_blocks (pk : UOVKey) (x y : ℕ → GF256) (k : Fin 45) :
    polar pk x y k =
      (∑ i : Fin 74, ∑ l : Fin 74,
        if (i : ℕ) ≤ l then c1 pk i l k * (x i * y l + y i * x l) else 0) +
      (∑ i : Fin 74, ∑ j : Fin 45, c2 pk i j k * (x i * y (74 + j) + y i * x (74 + j))) +
      (∑ a : Fin 45, ∑ b : Fin 45, if (a : ℕ) ≤ b then
        c3 pk a b k * (x (74 + a) * y (74 + b) + y (74 + a) * x (74 + b)) else 0) := by
  unfold polar
  rw [sum_forEachMonomial]
  rfl

/-! ## pqov's key computation -/

/-- `P1·O + P2` (`batch_trimat_madd`, `P1` upper triangular), component `k`, entry `(i, j)`. -/
noncomputable def pqovS1 (pk : UOVKey) (O : OilMat) (k : Fin 45) (i : Fin 74) (j : Fin 45) : GF256 :=
  (∑ l : Fin 74, (if (i : ℕ) ≤ l then c1 pk i l k else 0) * O j l) + c2 pk i j k

/-- `M = Oᵀ·(P1·O + P2)` (`batch_upper_matTr_x_mat`, before `UT`). -/
noncomputable def pqovM (pk : UOVKey) (O : OilMat) (k : Fin 45) (a b : Fin 45) : GF256 :=
  ∑ i : Fin 74, O a i * pqovS1 pk O k i b

/-- pqov's `P3 = UT(M + Mᵀ)`, entry `(a, b)`, `a ≤ b` (`calculate_F2_P3`, `Keygen.computeP3`). -/
noncomputable def pqovP3 (pk : UOVKey) (O : OilMat) (k : Fin 45) (a b : Fin 45) : GF256 :=
  if a = b then pqovM pk O k a a else pqovM pk O k a b + pqovM pk O k b a

/-- **The `P3` block of `pk` is pqov's**, computed from its own `P1`, `P2` blocks and `O`. -/
def P3Pqov (pk : UOVKey) (O : OilMat) : Prop :=
  ∀ a b : Fin 45, (a : ℕ) ≤ b → ∀ k, c3 pk a b k = pqovP3 pk O k a b

/-- pqov's stored `S = (P1 + P1ᵀ)·O + P2` (`calculate_F2_P3` / `calculate_F2`). -/
noncomputable def pqovS (pk : UOVKey) (O : OilMat) (k : Fin 45) (i : Fin 74) (j : Fin 45) : GF256 :=
  (∑ l : Fin 74, ((if (i : ℕ) ≤ l then c1 pk i l k else 0) +
    (if (l : ℕ) ≤ i then c1 pk l i k else 0)) * O j l) + c2 pk i j k

/-! ## The coordinates of `x₀` and `ō_j` -/

lemma vinVec_unit_fin (i l : Fin 74) : vinVec (unitVin i) l = if l = i then 1 else 0 := by
  simp only [vinVec, l.isLt, ↓reduceDIte, Fin.eta, unitVin]
  by_cases h : l = i
  · subst h; simp
  · simp [h]

lemma vinVec_oil (v : Vin) (x : ℕ) : vinVec v (74 + x) = 0 := by
  simp [vinVec]

lemma oilVec_fin (O : OilMat) (j : Fin 45) (l : Fin 74) : oilVec O j l = O j l := by
  simp [oilVec]

lemma oilVec_oil (O : OilMat) (j j' : Fin 45) : oilVec O j (74 + j') = if j' = j then 1 else 0 := by
  simp only [oilVec, show ¬ 74 + (j' : ℕ) < 74 by omega, ↓reduceDIte, Nat.add_left_cancel_iff]
  by_cases h : j' = j
  · simp [h]
  · simp [h, Fin.val_ne_of_ne h]

/-! ## The UOV identities -/

/-- **The system coefficients are pqov's `S = (P1 + P1ᵀ)·O + P2`**: `B(e_i, ō_j)_k`, which the
signer model computes from the polar form, is entry `(i, j)` of component `k` of pqov's stored `S`
read from the key layout. Every key, no hypothesis on its `P3` block. -/
theorem sysCoef_eq_pqovS (pk : UOVKey) (O : OilMat) (k : Fin 45) (i : Fin 74) (j : Fin 45) :
    sysCoef pk O k i j = pqovS pk O k i j := by
  unfold sysCoef
  rw [polar_eq_blocks]
  simp only [vinVec_unit_fin, vinVec_oil, oilVec_fin, oilVec_oil, mul_zero, zero_mul, add_zero,
    ite_self, Finset.sum_const_zero, ite_mul, one_mul]
  have e1 : ∀ x l : Fin 74, (if (x : ℕ) ≤ l then c1 pk x l k *
      ((if x = i then O j l else 0) + O j x * if l = i then 1 else 0) else 0) =
      (if x = i then (if (x : ℕ) ≤ l then c1 pk x l k * O j l else 0) else 0) +
      (if l = i then (if (x : ℕ) ≤ l then c1 pk x l k * O j x else 0) else 0) := by
    intro x l
    by_cases h1 : (x : ℕ) ≤ l <;> by_cases h2 : x = i <;> by_cases h3 : l = i <;>
      simp_all [mul_add]
  simp only [e1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x l => if x = i then _ else 0)]
  simp only [Finset.sum_ite_eq', mem_univ, ↓reduceIte, pqovS, add_mul, ite_mul, zero_mul]
  have e2 : (∑ x : Fin 74, ∑ x_1 : Fin 45, c2 pk x x_1 k *
      if x = i then (if x_1 = j then 1 else 0) else 0) = c2 pk i j k := by
    rw [Fintype.sum_eq_single i (fun x hx => by simp [hx])]
    simp
  rw [e2, Finset.sum_add_distrib]

/-- `Σ_{a ≤ b} UT(M + Mᵀ)_{ab} y_a y_b = yᵀ M y`, in any commutative ring. -/
lemma sum_ut {n : ℕ} {R : Type*} [CommRing R] (M : Fin n → Fin n → R) (y : Fin n → R) :
    (∑ a : Fin n, ∑ b : Fin n, if (a : ℕ) ≤ b then (if a = b then M a a else M a b + M b a) * y a * y b else 0) =
      ∑ a : Fin n, ∑ b : Fin n, M a b * y a * y b := by
  have e : ∀ a b : Fin n, (if (a : ℕ) ≤ b then
      (if a = b then M a a else M a b + M b a) * y a * y b else 0) =
      (if (a : ℕ) ≤ b then M a b * y a * y b else 0) +
      (if (a : ℕ) < b then M b a * y a * y b else 0) := by
    intro a b
    by_cases h1 : a = b
    · subst h1; simp
    · have h1' : (a : ℕ) ≠ b := Fin.val_ne_of_ne h1
      by_cases h2 : (a : ℕ) ≤ b
      · simp only [h1, h2, ↓reduceIte, show (a : ℕ) < b by omega]
        ring
      · simp [h2, show ¬ (a : ℕ) < b by omega]
  have e' : ∀ a b : Fin n, M a b * y a * y b =
      (if (a : ℕ) ≤ b then M a b * y a * y b else 0) +
      (if (b : ℕ) < a then M a b * y a * y b else 0) := by
    intro a b
    by_cases h : (a : ℕ) ≤ b
    · simp [h, show ¬ (b : ℕ) < a by omega]
    · simp [h, show (b : ℕ) < a by omega]
  calc _ = (∑ a : Fin n, ∑ b : Fin n, if (a : ℕ) ≤ b then M a b * y a * y b else 0) +
        ∑ a : Fin n, ∑ b : Fin n, (if (a : ℕ) < b then M b a * y a * y b else 0) := by
          simp only [e, Finset.sum_add_distrib]
    _ = (∑ a : Fin n, ∑ b : Fin n, if (a : ℕ) ≤ b then M a b * y a * y b else 0) +
        ∑ a : Fin n, ∑ b : Fin n, (if (b : ℕ) < a then M a b * y a * y b else 0) := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          split_ifs <;> ring
    _ = _ := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun b _ => (e' a b).symm

open Matrix in
lemma oilComb_fin (O : OilMat) (y : Fin 45 → GF256) (l : Fin 74) :
    (∑ j, y j • oilVec O j) l = (y ᵥ* Matrix.of O) l := by
  simp only [Finset.sum_apply, Pi.smul_apply, oilVec_fin, smul_eq_mul, Matrix.vecMul, dotProduct,
    Matrix.of_apply]

lemma oilComb_oil (O : OilMat) (y : Fin 45 → GF256) (a : Fin 45) :
    (∑ j, y j • oilVec O j) (74 + a) = y a := by
  simp only [Finset.sum_apply, Pi.smul_apply, oilVec_oil, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, mem_univ, ↓reduceIte]

open Matrix in
/-- **The public map on the oil space, for every key**: on `ō(y) = (u, y)`, `u = Oy`,
`P(ō(y)) = Q₁ + Q₂ + Q₃` with `Q₁ = uᵀ P1 u`, `Q₂ = uᵀ P2 y`, `Q₃ = Σ_{a ≤ b} P3_{ab} y_a y_b`, and
`Q₁ + Q₂ = yᵀ Oᵀ(P1·O + P2) y = yᵀ M y = Σ_{a ≤ b} UT(M + Mᵀ)_{ab} y_a y_b`, so in characteristic 2
`P(ō(y)) = Σ_{a ≤ b} (P3 − pqovP3)_{ab} y_a y_b`. -/
theorem qmap_oil_eq (pk : UOVKey) (O : OilMat) (y : Fin 45 → GF256) (k : Fin 45) :
    qmap pk (∑ j, y j • oilVec O j) k = ∑ a : Fin 45, ∑ b : Fin 45,
      if (a : ℕ) ≤ b then (c3 pk a b k - pqovP3 pk O k a b) * y a * y b else 0 := by
  rw [qmap_eq_blocks]
  simp only [oilComb_fin, oilComb_oil]
  set Om : Matrix (Fin 45) (Fin 74) GF256 := Matrix.of O
  set u := y ᵥ* Om
  set T1 : Matrix (Fin 74) (Fin 74) GF256 :=
    Matrix.of fun i l => if (i : ℕ) ≤ l then c1 pk i l k else 0
  set C2 : Matrix (Fin 74) (Fin 45) GF256 := Matrix.of fun i j => c2 pk i j k
  have h1 : (∑ i : Fin 74, ∑ l : Fin 74, if (i : ℕ) ≤ l then c1 pk i l k * u i * u l else 0) =
      u ⬝ᵥ (T1 *ᵥ u) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [T1, Matrix.of_apply]
    split_ifs <;> ring
  have h2 : (∑ i : Fin 74, ∑ j : Fin 45, c2 pk i j k * u i * y j) = u ⬝ᵥ (C2 *ᵥ y) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [C2, Matrix.of_apply]
    ring
  have hM : ∀ a b, pqovM pk O k a b = (Om * (T1 * Omᵀ + C2)) a b := by
    intro a b
    simp only [pqovM, pqovS1, Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply, Om, T1,
      C2, Matrix.of_apply]
  have h3 : (∑ a : Fin 45, ∑ b : Fin 45,
      if (a : ℕ) ≤ b then pqovP3 pk O k a b * y a * y b else 0) =
      y ⬝ᵥ ((Om * (T1 * Omᵀ + C2)) *ᵥ y) := by
    simp only [pqovP3]
    rw [sum_ut]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, hM]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hQ : y ⬝ᵥ ((Om * (T1 * Omᵀ + C2)) *ᵥ y) = u ⬝ᵥ (T1 *ᵥ u) + u ⬝ᵥ (C2 *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_transpose, dotProduct_add]
  have hD : (∑ a : Fin 45, ∑ b : Fin 45,
      if (a : ℕ) ≤ b then (c3 pk a b k - pqovP3 pk O k a b) * y a * y b else 0) =
      (∑ a : Fin 45, ∑ b : Fin 45, if (a : ℕ) ≤ b then c3 pk a b k * y a * y b else 0) -
      ∑ a : Fin 45, ∑ b : Fin 45, if (a : ℕ) ≤ b then pqovP3 pk O k a b * y a * y b else 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [hD, h1, h2, h3, hQ, CharTwo.sub_eq_add]
  ring

/-- **The UOV identity**: the public map of a key whose `P3` block is pqov's (`P3Pqov`) vanishes on
the oil space, for every oil matrix `O` and all `P1`, `P2` blocks (`qmap_oil_eq`). -/
theorem oilSpace_of_P3Pqov (pk : UOVKey) (O : OilMat) (h : P3Pqov pk O) : OilSpace pk O := by
  intro y
  funext k
  rw [qmap_oil_eq, Pi.zero_apply]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with hab
  · rw [h a b hab k, sub_self, zero_mul, zero_mul]
  · rfl

/-- A quadratic form `Σ_{a ≤ b} D_{ab} y_a y_b` that vanishes everywhere has `D = 0`. -/
lemma quad_coeff_zero {n : ℕ} {R : Type*} [CommRing R] (D : Fin n → Fin n → R)
    (h : ∀ y : Fin n → R, (∑ a : Fin n, ∑ b : Fin n,
      if (a : ℕ) ≤ b then D a b * y a * y b else 0) = 0) (a b : Fin n) (hab : (a : ℕ) ≤ b) :
    D a b = 0 := by
  have hd : ∀ c : Fin n, D c c = 0 := by
    intro c
    have := h (Pi.single c 1)
    rw [Fintype.sum_eq_single c (fun x hx => Finset.sum_eq_zero fun z _ => by
      simp [Pi.single_apply, hx])] at this
    rw [Fintype.sum_eq_single c (fun z hz => by simp [hz])] at this
    simpa using this
  by_cases e : a = b
  · subst e; exact hd a
  · have hlt : (a : ℕ) < b := lt_of_le_of_ne hab (Fin.val_ne_of_ne e)
    set y : Fin n → R := Pi.single a 1 + Pi.single b 1
    have ya : y a = 1 := by simp [y, e]
    have yb : y b = 1 := by simp [y, Ne.symm e]
    have y0 : ∀ x, x ≠ a ∧ x ≠ b → y x = 0 := fun x hx => by
      simp [y, hx.1, hx.2]
    have := h y
    rw [Fintype.sum_eq_add a b e (fun x hx => Finset.sum_eq_zero fun z _ => by
      simp [y0 x hx])] at this
    rw [Fintype.sum_eq_add a b e (fun z hz => by simp [y0 z hz]),
      Fintype.sum_eq_add a b e (fun z hz => by simp [y0 z hz])] at this
    simpa [ya, yb, hd, hab, show ¬ (b : ℕ) ≤ a by omega] using this

/-- **The oil-space condition characterizes pqov's `P3`**: `P` vanishes on the oil space of `O` iff
the `P3` block is pqov's `UT(M + Mᵀ)`, `M = Oᵀ(P1·O + P2)`; so pqov's key generation is the only
completion of `(P1, P2, O)` to a key with oil space `O`. -/
theorem oilSpace_iff_P3Pqov (pk : UOVKey) (O : OilMat) : OilSpace pk O ↔ P3Pqov pk O := by
  refine ⟨fun h a b hab k => ?_, oilSpace_of_P3Pqov pk O⟩
  have := quad_coeff_zero (fun a b => c3 pk a b k - pqovP3 pk O k a b) (fun y => by
    rw [← qmap_oil_eq, h y, Pi.zero_apply]) a b hab
  exact sub_eq_zero.1 this

/-! ## The constant of the system, and what `S`, `P3` depend on -/

lemma vinVec_fin (v : Vin) (l : Fin 74) : vinVec v l = v l := by
  simp [vinVec]

/-- **`P(v, 0) = P₁(v)`** (`batch_quad_trimat_eval(P1, v)`, the constant of pqov's system). -/
theorem qmap_vinVec_eq (pk : UOVKey) (v : Vin) (k : Fin 45) :
    qmap pk (vinVec v) k =
      ∑ i : Fin 74, ∑ l : Fin 74, if (i : ℕ) ≤ l then c1 pk i l k * v i * v l else 0 := by
  rw [qmap_eq_blocks]
  simp only [vinVec_fin, vinVec_oil, mul_zero, Finset.sum_const_zero, add_zero, ite_self]

/-- `S` depends on the key only through its `P1` and `P2` blocks. -/
theorem sysCoef_congr {pk pk' : UOVKey} (O : OilMat) (h1 : ∀ i l k, c1 pk i l k = c1 pk' i l k)
    (h2 : ∀ i j k, c2 pk i j k = c2 pk' i j k) : sysCoef pk O = sysCoef pk' O := by
  funext k i j
  simp only [sysCoef_eq_pqovS, pqovS, h1, h2]

/-- pqov's `P3` depends on the key only through its `P1` and `P2` blocks. -/
theorem pqovP3_congr {pk pk' : UOVKey} (O : OilMat) (h1 : ∀ i l k, c1 pk i l k = c1 pk' i l k)
    (h2 : ∀ i j k, c2 pk i j k = c2 pk' i j k) (k a b : Fin 45) :
    pqovP3 pk O k a b = pqovP3 pk' O k a b := by
  simp only [pqovP3, pqovM, pqovS1, h1, h2]

/-! ## pqov's expanded public key from `(O, P1, P2)` -/

/-- The `P1`, `P2` blocks of an expanded key and nothing else: the `P1` part `P1` (offsets
`< 124875`), the `P2` part `P2` (`P2 i j k` at `124875 + 2025 i + 45 j + k`), `0` from `274725`
(the same map as `Privacy.Moussaka.keyO0`). -/
def keyP12 (P1 : ℕ → GF256) (P2 : Fin 74 → Fin 45 → Fin 45 → GF256) : UOVKey :=
  ⟨[], fun n => if n < 124875 then P1 n else
    if h : n < 274725 then P2 ⟨(n - 124875) / 2025, by omega⟩ ⟨(n - 124875) / 45 % 45, by omega⟩
      ⟨(n - 124875) % 45, by omega⟩ else 0⟩

lemma off3_ge (a b : ℕ) : 274725 ≤ off3 a b := by
  simp only [off3, triangle_74']
  omega

lemma off1_lt (i l : Fin 74) (k : Fin 45) : off1 i l + k < 124875 := by
  have h1 := le_triangle (74 - i)
  have h2 := triangle_mono (show 74 - (i : ℕ) ≤ 74 by omega)
  have hi := i.isLt
  have hl := l.isLt
  have hk := k.isLt
  simp only [off1, triangle_74'] at h2 ⊢
  have : (l : ℕ) - i < triangle (74 - i) := by omega
  have : 45 * (2775 - triangle (74 - i)) + (l - i) * 45 + k < 45 * 2775 := by omega
  omega

/-- The row starts of the `P3` block grow by the row lengths. -/
lemma off3_row_lt {a a' b : ℕ} (h : a < a') (hb : b < 45) (ha' : a' ≤ 45) :
    (triangle 45 - triangle (45 - a)) + (b - a) < triangle 45 - triangle (45 - a') := by
  have e := triangle_succ (44 - a)
  rw [show 44 - a + 1 = 45 - a by omega] at e
  have m1 := triangle_mono (show 45 - a' ≤ 44 - a by omega)
  have m2 := triangle_mono (show 45 - a ≤ 45 by omega)
  omega

lemma off3_inj {a b k a' b' k' : Fin 45} (hab : (a : ℕ) ≤ b) (hab' : (a' : ℕ) ≤ b')
    (h : off3 a b + k = off3 a' b' + k') : a = a' ∧ b = b' ∧ k = k' := by
  have hk := k.isLt
  have hk' := k'.isLt
  have hb := b.isLt
  have hb' := b'.isLt
  unfold off3 at h
  have e : (triangle 45 - triangle (45 - a)) + (b - a) =
      (triangle 45 - triangle (45 - a')) + (b' - a') ∧ (k : ℕ) = k' := by omega
  rcases lt_trichotomy (a : ℕ) a' with hlt | heq | hgt
  · have := off3_row_lt hlt hb (by omega)
    omega
  · have hb2 : (b : ℕ) = b' := by rw [heq] at e; omega
    exact ⟨Fin.ext heq, Fin.ext hb2, Fin.ext e.2⟩
  · have := off3_row_lt hgt hb' (by omega)
    omega

/-- The `P3` block holding `F a b k` at `off3 a b + k` (`a ≤ b`), `0` elsewhere. -/
noncomputable def p3Region (F : Fin 45 → Fin 45 → Fin 45 → GF256) (n : ℕ) : GF256 :=
  ∑ x : Fin 45 × Fin 45 × Fin 45,
    if (x.1 : ℕ) ≤ x.2.1 ∧ n = off3 x.1 x.2.1 + x.2.2 then F x.1 x.2.1 x.2.2 else 0

lemma p3Region_off (F : Fin 45 → Fin 45 → Fin 45 → GF256) (a b k : Fin 45) (hab : (a : ℕ) ≤ b) :
    p3Region F (off3 a b + k) = F a b k := by
  unfold p3Region
  rw [Fintype.sum_eq_single (a, b, k) fun x hx => ?_]
  · simp [hab]
  · rw [ite_eq_right_iff]
    rintro ⟨h1, h2⟩
    obtain ⟨e1, e2, e3⟩ := off3_inj hab h1 h2
    exact absurd (by rw [e1, e2, e3]) hx

/-- **pqov's expanded public key** for the oil matrix `O` and the `P1`, `P2` parts `P1`, `P2`
(`generate_keypair_pkc` then `expand_pk`): the `P1`, `P2` blocks of `keyP12 P1 P2` and the `P3`
block computed from them and `O` as `calculate_F2_P3` does (`pqovP3`, `Keygen.computeP3`). -/
noncomputable def pqovKey (O : OilMat) (P1 : ℕ → GF256)
    (P2 : Fin 74 → Fin 45 → Fin 45 → GF256) : UOVKey :=
  ⟨[], fun n => if n < 274725 then (keyP12 P1 P2).map n else
    p3Region (fun a b k => pqovP3 (keyP12 P1 P2) O k a b) n⟩

section Key

variable (O : OilMat) (P1 : ℕ → GF256) (P2 : Fin 74 → Fin 45 → Fin 45 → GF256)

lemma c1_keyP12 (i l : Fin 74) (k : Fin 45) : c1 (keyP12 P1 P2) i l k = P1 (off1 i l + k) := by
  simp only [c1, keyP12, off1_lt i l k, ↓reduceIte]

lemma c2_keyP12 (i : Fin 74) (j k : Fin 45) : c2 (keyP12 P1 P2) i j k = P2 i j k := by
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  have e : off2 i j + k = 124875 + i.val * 2025 + j.val * 45 + k.val := by
    simp only [off2, triangle_74']
  have h1 : ¬ 124875 + i.val * 2025 + j.val * 45 + k.val < 124875 := by omega
  have h2 : 124875 + i.val * 2025 + j.val * 45 + k.val < 274725 := by omega
  have key : ∀ (a' : Fin 74) (t' k' : Fin 45), a'.val = i.val → t'.val = j.val →
      k'.val = k.val → P2 a' t' k' = P2 i j k := by
    intro a' t' k' e1 e2 e3
    rw [Fin.ext e1, Fin.ext e2, Fin.ext e3]
  rw [c2, e]
  unfold keyP12
  dsimp only
  simp only [h1, h2, ↓reduceIte, ↓reduceDIte]
  exact key _ _ _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)

lemma c1_pqovKey (i l : Fin 74) (k : Fin 45) :
    c1 (pqovKey O P1 P2) i l k = c1 (keyP12 P1 P2) i l k := by
  simp only [c1, pqovKey, show off1 i l + k < 274725 by have := off1_lt i l k; omega, ↓reduceIte]

lemma c2_pqovKey (i : Fin 74) (j k : Fin 45) :
    c2 (pqovKey O P1 P2) i j k = c2 (keyP12 P1 P2) i j k := by
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  have : off2 i j + k < 274725 := by simp only [off2, triangle_74']; omega
  simp only [c2, pqovKey, this, ↓reduceIte]

lemma c3_pqovKey (a b k : Fin 45) (hab : (a : ℕ) ≤ b) :
    c3 (pqovKey O P1 P2) a b k = pqovP3 (keyP12 P1 P2) O k a b := by
  simp only [c3, pqovKey, show ¬ off3 a b + k < 274725 by have := off3_ge a b; omega, ↓reduceIte]
  exact p3Region_off _ a b k hab

/-- `pqovKey` has pqov's `P3` block. -/
theorem P3Pqov_pqovKey : P3Pqov (pqovKey O P1 P2) O := fun a b hab k => by
  rw [c3_pqovKey O P1 P2 a b k hab]
  exact (pqovP3_congr O (fun i l k => (c1_pqovKey O P1 P2 i l k).symm)
    (fun i j k => (c2_pqovKey O P1 P2 i j k).symm) k a b)

/-- **`P` vanishes on the oil space of pqov's keys**, for every oil matrix `O` and all `P1`, `P2`
parts: pqov's signer model is correct for them (`signer_correct`, `deriveRef_correct`). -/
theorem oilSpace_pqovKey : OilSpace (pqovKey O P1 P2) O :=
  oilSpace_of_P3Pqov _ O (P3Pqov_pqovKey O P1 P2)

/-- pqov's `S = (P1 + P1ᵀ)·O` for the `P1` part, without `P2`. -/
noncomputable def sP1 (k : Fin 45) (i : Fin 74) (j : Fin 45) : GF256 :=
  ∑ l : Fin 74, ((if (i : ℕ) ≤ l then P1 (off1 i l + k) else 0) +
    (if (l : ℕ) ≤ i then P1 (off1 l i + k) else 0)) * O j l

/-- **The system coefficients of pqov's keys**: `S = (P1 + P1ᵀ)·O + P2`, the `P2` part entering
additively (`sysCoef_keyO0` is the case `O = 0`). -/
theorem sysCoef_pqovKey (k : Fin 45) (i : Fin 74) (j : Fin 45) :
    sysCoef (pqovKey O P1 P2) O k i j = sP1 O P1 k i j + P2 i j k := by
  rw [sysCoef_eq_pqovS]
  simp only [pqovS, c1_pqovKey, c2_pqovKey, c1_keyP12, c2_keyP12, sP1]

end Key

/-! ## The executable twin of the signer (`Spec/PqovSignerExec.lean`) is the model -/

lemma sum45_eq (f : Fin 45 → GF256) : sum45 f = ∑ j, f j := by
  rw [Fin.sum_univ_def, sum45, List.sum, List.foldr_map]

/-- A solution of the attempt's system is the model's oil part when `L_v` is invertible. -/
theorem attempt_eq_of_sol (pk : UOVKey) (O : OilMat) (t : Bytes) (v : Vin) (x : Fin 45 → GF256)
    (hd : (sysMat pk O v).det ≠ 0)
    (hx : (sysMat pk O v).mulVec x = target t - qmap pk (vinVec v)) :
    attempt pk O t v = some (toBytes (vinVec v + ∑ j, x j • oilVec O j)) := by
  have hu : IsUnit (sysMat pk O v).det := isUnit_iff_ne_zero.2 hd
  have hs : oilSol pk O v t = x := by
    rw [oilSol, ← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  simp only [attempt, ne_eq, hd, not_false_eq_true, ↓reduceIte, preimageVec, hs]

lemma preimageExec_eq (O : OilMat) (v : Vin) (x : Fin 45 → GF256) :
    preimageExec O v x = toBytes (vinVec v + ∑ j, x j • oilVec O j) := by
  unfold preimageExec toBytes
  simp only [sum45_eq, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- **An accepted executable attempt is the model's attempt** when `L_v` is invertible. -/
theorem attemptExec_sound (pk : UOVKey) (O : OilMat) (t : Bytes) (v : Vin) (s : Bytes)
    (h : attemptExec pk O t v = some s) (hd : (sysMat pk O v).det ≠ 0) :
    attempt pk O t v = some s := by
  unfold attemptExec at h
  dsimp only at h
  split at h
  · cases h
  · rename_i x _
    split_ifs at h with hc
    cases h
    rw [preimageExec_eq]
    refine attempt_eq_of_sol pk O t v x hd (funext fun k => ?_)
    have := List.all_eq_true.1 hc k (List.mem_finRange k)
    rw [decide_eq_true_iff, sum45_eq] at this
    simpa [Matrix.mulVec, dotProduct, CharTwo.sub_eq_add] using this

end VoleMole.Spec.Pqov
