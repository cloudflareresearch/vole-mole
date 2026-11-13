import VoleMole.Privacy.PqovKeys
import VoleMole.Spec.PqovSymmetry

/-!
# Theorem T3: no affine symmetry of a UOV key translates targets, with the count

`lean/docs/security/ompr-shift-algebra.md` §3.1 (T2, T2′) and §8.4 (Lemma N, the scalar case
of (G) and (L)), over pqov's keys `pqovKey O P1 P2` (`Spec/PqovKey.lean`) with any oil matrix `O`,
any `P1` part and a uniform `P2` part, the model of `Privacy/PqovKeys.lean` (there `S` is uniform:
`sEquiv`, `sysMat_pqovKey`).

**Lemma N, first part** (`pr_not_radTriv`): the radical of `B` is `0` on `F^{119}` (`RadTriv`)
except with probability `≤ 256^{−1951} + 256^{−3285}`. A radical vector `a = (v, 0) + Σ x_j ō_j`
has `L_v = 0` (so `v ↦ L_v` is not injective unless `v = 0`), and for `v = 0`, `x ≠ 0` and
`Σ_j x_j S_k[i][j] = 0` for all `k, i` (`rad_coords`, `not_radTriv_imp`). Both are kernels of
surjective additive maps of the uniform `S` (`lin`, `colM`), hit with probability
`256^{−2025}` and `256^{−3330}`; a union over `v` and `x` gives the bound.

**No affine symmetry translates targets** (`no_translation`; `pr_translation_le`): for a key with
`RadTriv`, a pair `φ(s) = A s + a`, `Θ(y) = T y + c` with `A`, `T` homogeneous, `A` onto and
`P ∘ φ = Θ ∘ P` has `c = 0` and `a = 0` on `F^{119}` (with `affine_symmetry`). So over pqov's keys
such a pair with `c ≠ 0` exists with probability `≤ 256^{−1951} + 256^{−3285}`.

**Lemma N, second part** (`pr_not_spanTriv`): the values of `B` span `F^{45}` (`SpanTriv`) except
with probability `≤ 256^{−3285}`. Then **the target map of a symmetry is determined by `A`**
(`target_unique`): a scaling `A = λ·I` forces `T = λ²·I` (`scaling_target`), and a scalar
infinitesimal pair `X = λ·I` forces `Y = 0` (`scaling_infinitesimal_target`).

**Not mechanized** (§8 of the note): that `A` (or `X`) must be scalar, for linear `A` (G) and
infinitesimal `X` (L), with the bound `≤ 1.01·256^{−977}` (Lemma C on `F[x]`-modules, the rank
Lemmas E and F, the count of matrices by rank); (S) for semilinear maps; Lemma I; Proposition A
for additive maps. The bounds here are weaker than the note's Lemma N (`256^{−3211}`,
`256^{−5987}`) because only `P2` is random: they hold for every `P1`.

No `sorry`, no `axiom`.
-/

open Finset

namespace VoleMole.Assumptions.SymmetryCount

open VoleMole.Spec VoleMole.Spec.Pqov VoleMole.Arith VoleMole.Arith.UOV VoleMole.Privacy
  VoleMole.Privacy.Moussaka

/-! ## The radical of `B` -/

/-- **The radical of `B` is `0`** on `F^{119}`: a vector `a` with `B(a, ·) = 0` vanishes on the
coordinates that `P` reads. -/
def RadTriv (pk : UOVKey) : Prop :=
  ∀ a : ℕ → GF256, (∀ u, polar pk a u = 0) → ∀ i < 119, a i = 0

/-- `B` reads only the first `119` coordinates. -/
theorem polar_congr_left (pk : UOVKey) {a a' : ℕ → GF256} (h : ∀ i < 119, a i = a' i)
    (u : ℕ → GF256) : polar pk a u = polar pk a' u := by
  funext k
  simp only [polar]
  congr 1
  refine List.map_congr_left fun m hm => ?_
  obtain ⟨hij, hj⟩ := mem_forEachMonomial hm
  rw [h m.i (by omega), h m.j hj]

/-- The oil vector with coordinates `x`: `Σ_j x_j·ō_j`. -/
noncomputable def oilComb (O : OilMat) (x : Fin 45 → GF256) : ℕ → GF256 := ∑ j, x j • oilVec O j

/-- **`B` vanishes on the oil space.** -/
theorem polar_oilComb (pk : UOVKey) (O : OilMat) (hO : OilSpace pk O) (x y : Fin 45 → GF256) :
    polar pk (oilComb O x) (oilComb O y) = 0 := by
  have e : oilComb O x + oilComb O y = oilComb O (x + y) := by
    simp only [oilComb, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have h := qmap_add pk (oilComb O x) (oilComb O y)
  rw [e, oilComb, oilComb, oilComb, hO, hO, hO, zero_add, zero_add] at h
  exact h.symm

lemma oilComb_single (O : OilMat) (j : Fin 45) : oilComb O (Pi.single j 1) = oilVec O j := by
  unfold oilComb
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- `S_k[i][j] = B(e_i, ō_j)_k` is the `(k, j)` entry of `L_{e_i}`. -/
lemma sysCoef_eq_sysMat (pk : UOVKey) (O : OilMat) (k : Fin 45) (i : Fin 74) (j : Fin 45) :
    sysCoef pk O k i j = sysMat pk O (unitVin i) k j := by
  rfl

/-- **The radical, in the coordinates of the oil space** (T2′ of the note). A vector `a` with
`B(a, ·) = 0`, written `a = (v, 0) + Σ_j x_j·ō_j` on `F^{119}`, has `L_v = 0`; if `v = 0`, then
`Σ_j x_j·S_k[i][j] = 0` for all `k`, `i`. -/
theorem rad_coords (pk : UOVKey) (O : OilMat) (hO : OilSpace pk O) (a : ℕ → GF256)
    (ha : ∀ u, polar pk a u = 0) :
    let x : Fin 45 → GF256 := fun j => a (74 + j)
    let v : Vin := fun i => a i - ∑ j, x j * O j i
    (∀ i < 119, a i = (vinVec v + oilComb O x) i) ∧ sysMat pk O v = 0 ∧
      (v = 0 → ∀ k i, ∑ j, x j * sysCoef pk O k i j = 0) := by
  intro x v
  have hco : ∀ i < 119, a i = (vinVec v + oilComb O x) i := by
    intro i hi
    simp only [Pi.add_apply, oilComb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vinVec, v,
      oilVec]
    by_cases h74 : i < 74
    · simp only [h74, ↓reduceDIte]
      ring
    · simp only [h74, ↓reduceDIte, zero_add]
      rw [Finset.sum_eq_single ⟨i - 74, by omega⟩ (fun b _ hb => by
        have : i ≠ 74 + b.val := fun e => hb (Fin.ext (by simp; omega))
        simp [this]) (by simp)]
      simp only [x]
      have : 74 + (i - 74) = i := by omega
      simp [this]
  have hpa : ∀ u, polar pk (vinVec v + oilComb O x) u = 0 := fun u => by
    rw [← polar_congr_left pk hco u, ha u]
  have hL : sysMat pk O v = 0 := by
    ext k j
    have h := congrFun (hpa (oilVec O j)) k
    rw [polar_add_left, ← oilComb_single O j, polar_oilComb pk O hO, add_zero] at h
    simpa [sysMat, oilComb_single] using h
  refine ⟨hco, hL, fun hv k i => ?_⟩
  have hv0 : vinVec v = 0 := by funext n; simp [vinVec, hv]
  have h := congrFun (hpa (vinVec (unitVin i))) k
  rw [hv0, zero_add, oilComb, polar_sum_left] at h
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
  rw [sysCoef, polar_comm]

/-! ## Counting over pqov's keys -/

/-- `S ↦ (Σ_j x_j·S_k[i][j])_{k,i}`: the system coefficients applied to the oil coordinates. -/
noncomputable def colM (x : Fin 45 → GF256) : Coef →+ (Fin 45 → Fin 74 → GF256) where
  toFun S k i := ∑ j, x j * S k i j
  map_zero' := by ext k i; simp
  map_add' S S' := by
    ext k i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma colM_surjective {x : Fin 45 → GF256} (hx : x ≠ 0) : Function.Surjective (colM x) := by
  classical
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hx
  intro Y
  refine ⟨fun k i j => if j = j₀ then (x j₀)⁻¹ * Y k i else 0, ?_⟩
  ext k i
  simp only [colM, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' univ j₀]
  simp only [mem_univ, ↓reduceIte]
  rw [← mul_assoc, mul_inv_cancel₀ hj₀, one_mul]

/-- The kernel of a surjective additive map is hit with probability `1/|H|`. -/
lemma pr_ker {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) : pr G (fun g => f g = 0) = 1 / Fintype.card H := by
  classical
  rw [pr_comp_addHom f hf (fun h => h = 0), pr_def]
  congr 1
  rw [Finset.filter_eq' univ (0 : H)]
  simp

lemma lin_unit (S : Coef) (i : Fin 74) (k j : Fin 45) : lin (unitVin i) S k j = S k i j := by
  simp only [lin, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply, unitVin]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
  simp

variable (O : OilMat) (P1 : ℕ → GF256)

/-- **A nontrivial radical forces one of two linear events on `S`**: `L_v = 0` for some `v ≠ 0`
(the map `v ↦ L_v` is not injective), or `Σ_j x_j·S_k[i][j] = 0` for all `k, i` for some
`x ≠ 0`. -/
theorem not_radTriv_imp (P2 : P2Part) (h : ¬ RadTriv (pqovKey O P1 P2)) :
    (∃ v : Vin, v ≠ 0 ∧ lin v (sEquiv O P1 P2) = 0) ∨
      ∃ x : Fin 45 → GF256, x ≠ 0 ∧ colM x (sEquiv O P1 P2) = 0 := by
  simp only [RadTriv, not_forall] at h
  obtain ⟨a, ha, i₀, hi₀, hne⟩ := h
  obtain ⟨hco, hL, h0⟩ := rad_coords (pqovKey O P1 P2) O (oilSpace_pqovKey O P1 P2) a ha
  set x : Fin 45 → GF256 := fun j => a (74 + j)
  set v : Vin := fun i => a i - ∑ j, x j * O j i
  by_cases hv : v = 0
  · refine Or.inr ⟨x, fun hx => hne ?_, ?_⟩
    · rw [hco i₀ hi₀, hv, hx]
      simp [vinVec, oilComb]
    · ext k i
      have := h0 hv k i
      simp only [colM, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sysCoef_eq_sysMat, sysMat_pqovKey, lin_unit]
  · exact Or.inl ⟨v, hv, by rw [← sysMat_pqovKey]; exact hL⟩

/-- **Lemma N, first part, over pqov's keys**: for every oil matrix `O` and `P1` part, over a
uniform `P2` part, the radical of `B` is nontrivial with probability at most
`256^{74−2025} + 256^{45−3330} = 256^{−1951} + 256^{−3285}`. -/
theorem pr_not_radTriv :
    pr P2Part (fun P2 => ¬ RadTriv (pqovKey O P1 P2)) ≤ 1 / 256 ^ 1951 + 1 / 256 ^ 3285 := by
  have hF : pr Coef (fun _ => False) = 0 := by
    classical
    rw [pr_def, Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_div]
  refine (pr_mono fun P2 h => not_radTriv_imp O P1 P2 h).trans ?_
  rw [pr_equiv (sEquiv O P1) (fun S => (∃ v : Vin, v ≠ 0 ∧ lin v S = 0) ∨
    ∃ x : Fin 45 → GF256, x ≠ 0 ∧ colM x S = 0)]
  refine (pr_or_le _ _).trans (add_le_add ?_ ?_)
  · refine (pr_exists_le_sum (fun (v : Vin) S => v ≠ 0 ∧ lin v S = 0)).trans ?_
    have hterm : ∀ v : Vin, pr Coef (fun S => v ≠ 0 ∧ lin v S = 0) ≤ 1 / 256 ^ (45 * 45) := by
      intro v
      by_cases hv : v = 0
      · refine (pr_mono (Q := fun _ => False) fun S h => h.1 hv).trans ?_
        rw [hF]; positivity
      · refine (pr_mono fun S h => h.2).trans (le_of_eq ?_)
        rw [pr_ker (lin v) (lin_surjective hv), card_mat45, GF256.card_eq]
        simp only [Nat.cast_ofNat]
    refine (Finset.sum_le_sum fun v _ => hterm v).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_vin,
      show 45 * 45 = 74 + 1951 from rfl, pow_add, one_div, one_div, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (by positivity), one_mul]
  · refine (pr_exists_le_sum (fun (x : Fin 45 → GF256) S => x ≠ 0 ∧ colM x S = 0)).trans ?_
    have hterm : ∀ x : Fin 45 → GF256, pr Coef (fun S => x ≠ 0 ∧ colM x S = 0) ≤
        1 / ((256 : ℝ) ^ 74) ^ 45 := by
      intro x
      by_cases hx : x = 0
      · refine (pr_mono (Q := fun _ => False) fun S h => h.1 hx).trans ?_
        rw [hF]; positivity
      · refine (pr_mono fun S h => h.2).trans (le_of_eq ?_)
        rw [pr_ker (colM x) (colM_surjective hx)]
        simp only [Fintype.card_fun, Fintype.card_fin, GF256.card_eq, Nat.cast_pow,
          Nat.cast_ofNat]
    refine (Finset.sum_le_sum fun x _ => hterm x).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [Fintype.card_fun, Fintype.card_fin, GF256.card_eq, Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul, show 74 * 45 = 45 + 3285 from rfl, pow_add, one_div, one_div, mul_inv,
      ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-! ## No affine symmetry translates targets -/

lemma exists_ne_zero_one : ∃ l : GF256, l ≠ 0 ∧ l ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset GF256) ⊆ {0, 1} := fun μ _ => by
    by_cases h0 : μ = 0
    · simp [h0]
    · simp [h μ h0]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, GF256.card_eq] at this
  exact absurd (this.trans Finset.card_le_two) (by norm_num)

/-- **No affine symmetry translates targets** (T2 and T2′ of the note, §3.1). If the radical of
`B` is trivial, every pair `φ(s) = A s + a`, `Θ(y) = T y + c` with `A`, `T` homogeneous, `A` onto
and `P ∘ φ = Θ ∘ P` has `c = 0` (and `a = 0` on `F^{119}`). In particular `Θ` is never a
translation `y ↦ y + Δ` with `Δ ≠ 0`. -/
theorem no_translation (pk : UOVKey) (hR : RadTriv pk) (A : (ℕ → GF256) → ℕ → GF256)
    (a : ℕ → GF256) (T : (Fin 45 → GF256) → Fin 45 → GF256) (c : Fin 45 → GF256)
    (hA : ∀ (l : GF256) (s : ℕ → GF256), A (l • s) = l • A s)
    (hT : ∀ (l : GF256) (y : Fin 45 → GF256), T (l • y) = l • T y)
    (hon : Function.Surjective A) (h : ∀ s, qmap pk (A s + a) = T (qmap pk s) + c) :
    c = 0 ∧ ∀ i < 119, a i = 0 := by
  obtain ⟨l, h0, h1⟩ := exists_ne_zero_one
  obtain ⟨hc, hrad, -⟩ := affine_symmetry pk A a T c hA hT h h0 h1
  have ha : ∀ i < 119, a i = 0 := hR a fun u => by
    obtain ⟨s, rfl⟩ := hon u
    rw [polar_comm]
    exact hrad s
  refine ⟨?_, ha⟩
  rw [hc, qmap_congr pk (τ := 0) ha]
  simpa using qmap_smul pk 0 0

/-- **T3, translation part, with the count**: for every oil matrix `O` and `P1` part, over a
uniform `P2` part, the key has an affine symmetry pair with `A` homogeneous and onto that moves
targets by a nonzero translation `c` with probability at most `256^{−1951} + 256^{−3285}`. -/
theorem pr_translation_le :
    pr P2Part (fun P2 => ∃ (A : (ℕ → GF256) → ℕ → GF256) (a : ℕ → GF256)
      (T : (Fin 45 → GF256) → Fin 45 → GF256) (c : Fin 45 → GF256),
      (∀ (l : GF256) (s : ℕ → GF256), A (l • s) = l • A s) ∧
      (∀ (l : GF256) (y : Fin 45 → GF256), T (l • y) = l • T y) ∧ Function.Surjective A ∧
      (∀ s, qmap (pqovKey O P1 P2) (A s + a) = T (qmap (pqovKey O P1 P2) s) + c) ∧ c ≠ 0) ≤
      1 / 256 ^ 1951 + 1 / 256 ^ 3285 := by
  refine (pr_mono fun P2 hP hR => ?_).trans (pr_not_radTriv O P1)
  obtain ⟨A, a, T, c, hA, hT, hon, h, hc⟩ := hP
  exact hc (no_translation _ hR A a T c hA hT hon h).1

/-- Non-vacuity: for every `O` and `P1` some `P2` gives a key with a trivial radical. -/
theorem exists_radTriv : ∃ P2 : P2Part, RadTriv (pqovKey O P1 P2) := by
  by_contra h
  push Not at h
  have h1 : pr P2Part (fun P2 => ¬ RadTriv (pqovKey O P1 P2)) = 1 := by
    rw [pr_congr (Q := fun _ => True) fun P2 => ⟨fun _ => trivial, fun _ => h P2⟩,
      pr_const]
    simp
  have h2 := pr_not_radTriv O P1
  rw [h1] at h2
  have : (1 : ℝ) / 256 ^ 1951 + 1 / 256 ^ 3285 < 1 := by
    have a1 : (1 : ℝ) / 256 ^ 1951 ≤ 1 / 256 := by
      gcongr
      exact le_self_pow₀ (by norm_num) (by norm_num)
    have a2 : (1 : ℝ) / 256 ^ 3285 ≤ 1 / 256 := by
      gcongr
      exact le_self_pow₀ (by norm_num) (by norm_num)
    calc (1 : ℝ) / 256 ^ 1951 + 1 / 256 ^ 3285 ≤ 1 / 256 + 1 / 256 := add_le_add a1 a2
      _ < 1 := by norm_num
  exact absurd h2 (not_le.mpr this)

/-! ## The values of `B` span `F^45`, and the target map is determined -/

/-- **The values of `B` span `F^{45}`**: no nonzero functional `h` vanishes on all of them. -/
def SpanTriv (pk : UOVKey) : Prop :=
  ∀ h : Fin 45 → GF256, (∀ s u, ∑ k, h k * polar pk s u k = 0) → h = 0

/-- `S ↦ (Σ_k h_k·S_k[i][j])_{i,j}`. -/
noncomputable def rowM (h : Fin 45 → GF256) : Coef →+ (Fin 74 → Fin 45 → GF256) where
  toFun S i j := ∑ k, h k * S k i j
  map_zero' := by ext i j; simp
  map_add' S S' := by
    ext i j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma rowM_surjective {h : Fin 45 → GF256} (hh : h ≠ 0) : Function.Surjective (rowM h) := by
  classical
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 hh
  intro Y
  refine ⟨fun k i j => if k = k₀ then (h k₀)⁻¹ * Y i j else 0, ?_⟩
  ext i j
  simp only [rowM, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' univ k₀]
  simp only [mem_univ, ↓reduceIte]
  rw [← mul_assoc, mul_inv_cancel₀ hk₀, one_mul]

/-- **Lemma N, second part, over pqov's keys**: the values of `B` fail to span `F^{45}` with
probability at most `256^{45−3330} = 256^{−3285}`. -/
theorem pr_not_spanTriv :
    pr P2Part (fun P2 => ¬ SpanTriv (pqovKey O P1 P2)) ≤ 1 / 256 ^ 3285 := by
  have hF : pr Coef (fun _ => False) = 0 := by
    classical
    rw [pr_def, Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_div]
  refine (pr_mono (Q := fun P2 => ∃ h : Fin 45 → GF256, h ≠ 0 ∧
      rowM h (sEquiv O P1 P2) = 0) fun P2 hP => ?_).trans ?_
  · simp only [SpanTriv, not_forall] at hP
    obtain ⟨h, hh, hne⟩ := hP
    refine ⟨h, hne, ?_⟩
    ext i j
    have := hh (vinVec (unitVin i)) (oilVec O j)
    simp only [rowM, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    refine (lin_unit _ i k j).symm.trans ?_
    rw [← sysMat_pqovKey]
    rfl
  rw [pr_equiv (sEquiv O P1) (fun S => ∃ h : Fin 45 → GF256, h ≠ 0 ∧ rowM h S = 0)]
  refine (pr_exists_le_sum (fun (h : Fin 45 → GF256) S => h ≠ 0 ∧ rowM h S = 0)).trans ?_
  have hterm : ∀ h : Fin 45 → GF256, pr Coef (fun S => h ≠ 0 ∧ rowM h S = 0) ≤
      1 / ((256 : ℝ) ^ 45) ^ 74 := by
    intro h
    by_cases hh : h = 0
    · refine (pr_mono (Q := fun _ => False) fun S hS => hS.1 hh).trans ?_
      rw [hF]; positivity
    · refine (pr_mono fun S hS => hS.2).trans (le_of_eq ?_)
      rw [pr_ker (rowM h) (rowM_surjective hh)]
      simp only [Fintype.card_fun, Fintype.card_fin, GF256.card_eq, Nat.cast_pow, Nat.cast_ofNat]
  refine (Finset.sum_le_sum fun h _ => hterm h).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_fin, GF256.card_eq, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, show 45 * 74 = 45 + 3285 from rfl, pow_add, one_div, one_div, mul_inv,
    ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- **The values of `B` span `F^{45}`** as a submodule, when `SpanTriv` holds. -/
theorem span_polar_eq_top (pk : UOVKey) (hS : SpanTriv pk) :
    Submodule.span GF256 (Set.range fun p : (ℕ → GF256) × (ℕ → GF256) => polar pk p.1 p.2) =
      ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  refine hf0 ?_
  have hh := hS (fun k => f (Pi.single k 1)) fun s u => by
    have : f (polar pk s u) = 0 :=
      hle (Submodule.subset_span ⟨(s, u), rfl⟩)
    rw [← this]
    conv_rhs => rw [show polar pk s u = ∑ k, polar pk s u k • Pi.single k 1 by
      ext i; simp [Finset.sum_apply, Pi.single_apply]]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  refine LinearMap.ext fun y => ?_
  rw [show y = ∑ k, y k • Pi.single k 1 by ext i; simp [Finset.sum_apply, Pi.single_apply]]
  have hk : ∀ k, f (Pi.single k 1) = 0 := fun k => congrFun hh k
  simp [map_sum, hk]

/-- **The target map of a symmetry is determined by `A`** (§8.4, last step of (G) and (L)). If
the values of `B` span, two linear maps `T`, `T'` that agree on the values of `P` are equal. -/
theorem target_unique (pk : UOVKey) (hS : SpanTriv pk)
    (T T' : (Fin 45 → GF256) →ₗ[GF256] (Fin 45 → GF256)) (h : ∀ s, T (qmap pk s) = T' (qmap pk s)) :
    T = T' := by
  have hpol : ∀ s u, T (polar pk s u) = T' (polar pk s u) := fun s u => by
    have e : polar pk s u = qmap pk (s + u) - qmap pk s - qmap pk u := by
      rw [qmap_add]; abel
    rw [e, map_sub, map_sub, map_sub, map_sub, h, h, h]
  refine LinearMap.ext_on_range (span_polar_eq_top pk hS) fun p => hpol p.1 p.2

/-- **A scaling pair has the scaling target map**: if `P(λs) = T(P(s))` for all `s`, with `T`
linear, then `T = λ²·I` (outside the event of `pr_not_spanTriv`). -/
theorem scaling_target (pk : UOVKey) (hS : SpanTriv pk) (l : GF256)
    (T : (Fin 45 → GF256) →ₗ[GF256] (Fin 45 → GF256)) (h : ∀ s, qmap pk (l • s) = T (qmap pk s)) :
    T = l ^ 2 • LinearMap.id :=
  target_unique pk hS T _ fun s => by rw [← h, qmap_smul]; rfl

/-- **A scalar infinitesimal pair has `Y = 0`**: if `B(s, λs) = Y(P(s))` for all `s`, with `Y`
linear, then `Y = 0` (outside the event of `pr_not_spanTriv`). -/
theorem scaling_infinitesimal_target (pk : UOVKey) (hS : SpanTriv pk) (l : GF256)
    (Y : (Fin 45 → GF256) →ₗ[GF256] (Fin 45 → GF256))
    (h : ∀ s, polar pk s (l • s) = Y (qmap pk s)) : Y = 0 :=
  target_unique pk hS Y 0 fun s => by rw [← h, scaling_infinitesimal]; rfl

end VoleMole.Assumptions.SymmetryCount
