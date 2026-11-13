import Mathlib

/-!
# L5: a block Schur test for sums of orthogonal projectors

For orthogonal projectors `P_1, …, P_m`,
`‖(1/m) Σ_i P_i‖ ≤ max_i (1/m) Σ_j ‖P_i P_j‖`.

The sketch proves this with the block row operator `X = [P_1 ⋯ P_m]` and `‖XX*‖ = ‖X*X‖`. The
proof here is the same Schur test written on vectors, with no block operator. Put `x_i := P_i v`.
Then

* `‖Σ_i x_i‖² = Σ_{i,j} ⟨x_i, P_i P_j x_j⟩ ≤ Σ_{i,j} c_{ij} ‖x_i‖ ‖x_j‖ ≤ K Σ_i ‖x_i‖²`, by
  AM–GM and the symmetry of `c`; and
* `Σ_i ‖x_i‖² = ⟨v, Σ_i x_i⟩ ≤ ‖v‖ ‖Σ_i x_i‖`.

Together these give `‖Σ_i x_i‖ ≤ K ‖v‖`, not merely its square root.
-/

open Finset
open scoped InnerProductSpace

namespace VoleMole.Extraction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {ι : Type*} [Fintype ι]

/-- **L5**, with explicit bounds `c i j` on the products `P_i P_j`. The projectors need not be
linear; only self-adjointness and idempotence are used. -/
theorem schur_projections (P : ι → H → H) (c : ι → ι → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hsa : ∀ i x y, ⟪P i x, y⟫_ℝ = ⟪x, P i y⟫_ℝ) (hid : ∀ i x, P i (P i x) = P i x)
    (hc : ∀ i j x, ‖P i (P j x)‖ ≤ c i j * ‖x‖) (hc0 : ∀ i j, 0 ≤ c i j)
    (hsym : ∀ i j, c i j = c j i) (hrow : ∀ i, ∑ j, c i j ≤ K) (v : H) :
    ‖∑ i, P i v‖ ≤ K * ‖v‖ ∧ ∑ i, ⟪v, P i v⟫_ℝ ≤ K * ‖v‖ ^ 2 := by
  set a : ι → ℝ := fun i => ‖P i v‖
  set s := ∑ i, a i ^ 2
  set N := ‖∑ i, P i v‖
  have hxi : ∀ i, ⟪v, P i v⟫_ℝ = a i ^ 2 := by
    intro i
    have : ⟪P i v, P i v⟫_ℝ = ⟪v, P i v⟫_ℝ := by rw [hsa, hid]
    rw [← this, real_inner_self_eq_norm_sq]
  have hs1 : ∑ i, ⟪v, P i v⟫_ℝ = s := Finset.sum_congr rfl fun i _ => hxi i
  have hs3 : s ≤ ‖v‖ * N := by
    rw [← hs1, ← inner_sum]
    exact real_inner_le_norm _ _
  have hcross : ∀ i j, ⟪P i v, P j v⟫_ℝ ≤ c i j * (a i * a j) := by
    intro i j
    calc ⟪P i v, P j v⟫_ℝ = ⟪P i (P i v), P j (P j v)⟫_ℝ := by rw [hid, hid]
      _ = ⟪P i v, P i (P j (P j v))⟫_ℝ := hsa _ _ _
      _ ≤ a i * ‖P i (P j (P j v))‖ := real_inner_le_norm _ _
      _ ≤ a i * (c i j * a j) := mul_le_mul_of_nonneg_left (hc _ _ _) (norm_nonneg _)
      _ = c i j * (a i * a j) := by ring
  have hamgm : ∑ i, ∑ j, c i j * (a i * a j) ≤ K * s := by
    calc ∑ i, ∑ j, c i j * (a i * a j)
        ≤ ∑ i, ∑ j, (c i j * a i ^ 2 / 2 + c j i * a j ^ 2 / 2) := by
          gcongr with i _ j _
          rw [← hsym i j]
          nlinarith [hc0 i j, mul_nonneg (hc0 i j) (sq_nonneg (a i - a j))]
      _ = ∑ i, ∑ j, c i j * a i ^ 2 / 2 + ∑ i, ∑ j, c i j * a i ^ 2 / 2 := by
          simp only [Finset.sum_add_distrib]
          rw [Finset.sum_comm (f := fun i j => c j i * a j ^ 2 / 2)]
      _ = ∑ i, a i ^ 2 * ∑ j, c i j := by
          rw [← two_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ ∑ i, a i ^ 2 * K := by
          gcongr with i
          exact hrow i
      _ = K * s := by rw [← Finset.sum_mul, mul_comm]
  have hN : N ^ 2 ≤ K * s := by
    calc N ^ 2 = ∑ i, ∑ j, ⟪P i v, P j v⟫_ℝ := by
          rw [← real_inner_self_eq_norm_sq, sum_inner]
          simp only [inner_sum]
      _ ≤ ∑ i, ∑ j, c i j * (a i * a j) := by gcongr with i _ j _; exact hcross i j
      _ ≤ K * s := hamgm
  have hN0 : 0 ≤ N := norm_nonneg _
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
  have hNle : N ≤ K * ‖v‖ := by
    have : N ^ 2 ≤ K * ‖v‖ * N := hN.trans (by nlinarith [hs3])
    nlinarith [mul_nonneg hK hv0]
  refine ⟨hNle, ?_⟩
  rw [hs1]
  calc s ≤ ‖v‖ * N := hs3
    _ ≤ ‖v‖ * (K * ‖v‖) := mul_le_mul_of_nonneg_left hNle hv0
    _ = K * ‖v‖ ^ 2 := by ring

variable [CompleteSpace H]

lemma norm_mul_comm_of_isSelfAdjoint {A B : H →L[ℝ] H} (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B) : ‖A * B‖ = ‖B * A‖ := by
  rw [← ContinuousLinearMap.adjoint.norm_map (A * B)]
  change ‖ContinuousLinearMap.adjoint (A ∘L B)‖ = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.isSelfAdjoint_iff'.1 hA,
    ContinuousLinearMap.isSelfAdjoint_iff'.1 hB]
  rfl

lemma inner_map_of_isSelfAdjoint {A : H →L[ℝ] H} (hA : IsSelfAdjoint A) (x y : H) :
    ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ := by
  conv_lhs => rw [← ContinuousLinearMap.isSelfAdjoint_iff'.1 hA]
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- **L5** for orthogonal projectors: if every row sum `Σ_j ‖P_i P_j‖` is at most `K`, then
`‖Σ_i P_i‖ ≤ K`. -/
theorem norm_sum_projections_le (P : ι → H →L[ℝ] H) (hid : ∀ i, IsIdempotentElem (P i))
    (hsa : ∀ i, IsSelfAdjoint (P i)) {K : ℝ} (hK : 0 ≤ K) (hrow : ∀ i, ∑ j, ‖P i * P j‖ ≤ K) :
    ‖∑ i, P i‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun v => ?_
  rw [_root_.sum_apply]
  refine (schur_projections (fun i => P i) (fun i j => ‖P i * P j‖) hK
    (fun i => inner_map_of_isSelfAdjoint (hsa i))
    (fun i x => congrArg (· x) (hid i).eq)
    (fun i j x => (P i * P j).le_opNorm x) (fun _ _ => norm_nonneg _)
    (fun i j => norm_mul_comm_of_isSelfAdjoint (hsa i) (hsa j)) hrow v).1

/-- **L5**, as stated in the sketch:
`‖(1/m) Σ_i P_i‖ ≤ max_i (1/m) Σ_j ‖P_i P_j‖` with `m = |ι|`. -/
theorem norm_avg_projections_le (P : ι → H →L[ℝ] H) (hid : ∀ i, IsIdempotentElem (P i))
    (hsa : ∀ i, IsSelfAdjoint (P i)) :
    ‖(Fintype.card ι : ℝ)⁻¹ • ∑ i, P i‖ ≤ ⨆ i, (Fintype.card ι : ℝ)⁻¹ * ∑ j, ‖P i * P j‖ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  set R := ⨆ i, (Fintype.card ι : ℝ)⁻¹ * ∑ j, ‖P i * P j‖
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hle : ∀ i, (Fintype.card ι : ℝ)⁻¹ * ∑ j, ‖P i * P j‖ ≤ R :=
    fun i => le_ciSup (f := fun i => (Fintype.card ι : ℝ)⁻¹ * ∑ j, ‖P i * P j‖)
      (Set.finite_range _).bddAbove i
  have hR : 0 ≤ R := by
    obtain ⟨i⟩ := hι
    exact (mul_nonneg (inv_nonneg.2 hm.le) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).trans
      (hle i)
  have hrow : ∀ i, ∑ j, ‖P i * P j‖ ≤ Fintype.card ι * R := by
    intro i
    have := hle i
    rwa [inv_mul_le_iff₀ hm] at this
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hm, inv_mul_le_iff₀ hm]
  exact norm_sum_projections_le P hid hsa (mul_nonneg hm.le hR) hrow

end VoleMole.Extraction
