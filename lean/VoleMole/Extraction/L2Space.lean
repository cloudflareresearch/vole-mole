import Mathlib

/-!
# Real functions on a finite type as the Hilbert space `ℓ²(Ω)`

The proofs manipulate plain functions `Ω → ℝ` with explicit sums; operator norms are taken on
`EuclideanSpace ℝ Ω`, the same functions with the `ℓ²` inner product. This file is the bridge.
-/

open scoped InnerProductSpace

namespace VoleMole.Extraction

variable {Ω : Type*} [Fintype Ω]

lemma norm_sq_toLp (f : Ω → ℝ) :
    ‖(WithLp.toLp 2 f : EuclideanSpace ℝ Ω)‖ ^ 2 = ∑ H, f H ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

lemma inner_toLp (f g : Ω → ℝ) :
    ⟪(WithLp.toLp 2 f : EuclideanSpace ℝ Ω), WithLp.toLp 2 g⟫_ℝ = ∑ H, f H * g H := by
  rw [PiLp.inner_apply]
  simp [mul_comm]

/-- A linear map on `Ω → ℝ`, as a continuous linear map on `ℓ²(Ω)`. -/
noncomputable def lift (A : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) :
    EuclideanSpace ℝ Ω →L[ℝ] EuclideanSpace ℝ Ω :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Ω → ℝ)).symm.toLinearMap ∘ₗ A ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Ω → ℝ)).toLinearMap)

lemma lift_apply (A : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) (x : EuclideanSpace ℝ Ω) :
    lift A x = WithLp.toLp 2 (A x.ofLp) := rfl

/-- An operator norm bound from a bound on squared norms of plain functions. -/
lemma norm_le_of_sum_sq_le (B : EuclideanSpace ℝ Ω →L[ℝ] EuclideanSpace ℝ Ω) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : EuclideanSpace ℝ Ω, ‖B x‖ ^ 2 ≤ c ^ 2 * ‖x‖ ^ 2) : ‖B‖ ≤ c := by
  refine B.opNorm_le_bound hc fun x => ?_
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) two_ne_zero, mul_pow]
  exact h x

end VoleMole.Extraction
