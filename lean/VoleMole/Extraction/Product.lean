import VoleMole.Extraction.Model
import VoleMole.Extraction.L2Space

/-!
# L4: the product of two bad projectors

`‖P_Θ P_Θ'‖ ≤ |Im_{U(Θ,Θ')}|⁻¹`.

The proof differs from the sketch's: instead of splitting `L` into four blocks and using
`‖X ⊗ Y‖ = ‖X‖‖Y‖`, it applies Cauchy–Schwarz pointwise and uses the sibling-average bound
`Model.avg_check_le` twice, once for each challenge. With `k := Π_{S_Θ'} f`,

* `(P_Θ P_Θ' f)(H)² ≤ c_Θ(H) · ι · (Π_{S_Θ} k²)(H)` by Cauchy–Schwarz and `Π_{S_Θ} c_Θ' ≤ ι`;
* `Σ_H c_Θ · Π_{S_Θ} k² = Σ_H Π_{S_Θ'} c_Θ · Π_{S_Θ} k² ≤ ι Σ_H k² ≤ ι Σ_H f²`, because
  `Π_{S_Θ} k²` does not depend on the `S_Θ'`-coordinates and `Π_{S_Θ'}` is self-adjoint;

where `ι = |Im_{U(Θ,Θ')}|⁻¹`. Like the sketch's proof, this needs no case split on validity.
-/

open Finset
open scoped InnerProductSpace

set_option linter.unusedSectionVars false

namespace VoleMole.Extraction

namespace Model

variable {𝔼 V T Ch : Type*} [Fintype 𝔼] [DecidableEq 𝔼] [AddCommGroup V] [Fintype V]
  [DecidableEq V] [AddCommGroup T] [Fintype T] [DecidableEq T] [Fintype Ch] [DecidableEq Ch]
variable (m : Model 𝔼 V T Ch)

/-- **L4**, on plain functions: `‖P_Θ P_Θ' f‖² ≤ |Im_{U(Θ,Θ')}|⁻² ‖f‖²`. -/
theorem sum_bad_bad_sq_le (Θ Θ' : Ch) (f : (𝔼 × Bool → V) → ℝ) :
    ∑ H, m.bad Θ (m.bad Θ' f) H ^ 2 ≤ m.hit Θ Θ' ^ 2 * ∑ H, f H ^ 2 := by
  set S := m.sib Θ
  set S' := m.sib Θ'
  set c := m.check Θ
  set c' := m.check Θ'
  set ι := m.hit Θ Θ'
  set k := avg S' f
  set X := avg S (fun H => k H ^ 2)
  have hc := m.isCheck Θ
  have hc' := m.isCheck Θ'
  have hι : 0 ≤ ι := m.hit_nonneg _ _
  have hX : ∀ H, 0 ≤ X H := avg_nonneg fun _ => sq_nonneg _
  -- Pointwise Cauchy–Schwarz.
  have hpt : ∀ H, m.bad Θ (m.bad Θ' f) H ^ 2 ≤ ι * (c H * X H) := by
    intro H
    have e : m.bad Θ (m.bad Θ' f) H = c H * avg S (fun H => c' H * k H) H := rfl
    have hA := avg_mul_sq_le (S := S) hc'.idem k H
    have h1 : avg S c' H ≤ ι := m.avg_check_le Θ Θ' H
    have h2 : avg S (fun H => c' H * k H ^ 2) H ≤ X H :=
      avg_mono (fun H => mul_le_of_le_one_left (sq_nonneg _) (hc'.le_one H)) H
    have h3 : 0 ≤ avg S (fun H => c' H * k H ^ 2) H :=
      avg_nonneg (fun H => mul_nonneg (hc'.nonneg H) (sq_nonneg _)) H
    have hA' : avg S (fun H => c' H * k H) H ^ 2 ≤ ι * X H :=
      hA.trans (mul_le_mul h1 h2 h3 hι)
    rw [e, mul_pow, sq, hc.idem]
    calc c H * avg S (fun H => c' H * k H) H ^ 2 ≤ c H * (ι * X H) :=
          mul_le_mul_of_nonneg_left hA' (hc.nonneg H)
      _ = ι * (c H * X H) := by ring
  -- `X` does not depend on the `S'`-coordinates.
  have hXinv : InvOn S' X := by
    refine invOn_avg ?_
    intro H H' h
    simp only [k, invOn_avg_self S' f H H' h]
  have hsum : ∑ H, c H * X H ≤ ι * ∑ H, f H ^ 2 := by
    calc ∑ H, c H * X H = ∑ H, c H * avg S' X H := by rw [avg_of_invOn hXinv]
      _ = ∑ H, avg S' c H * X H := sum_mul_avg S' c X
      _ ≤ ∑ H, ι * X H := by
          gcongr with H
          · exact hX H
          · rw [show ι = m.hit Θ' Θ from m.hit_comm Θ Θ']; exact m.avg_check_le Θ' Θ H
      _ = ι * ∑ H, k H ^ 2 := by rw [← Finset.mul_sum, sum_avg]
      _ ≤ ι * ∑ H, avg S' (fun H => f H ^ 2) H := by
          gcongr with H; exact avg_sq_le S' f H
      _ = ι * ∑ H, f H ^ 2 := by rw [sum_avg]
  calc ∑ H, m.bad Θ (m.bad Θ' f) H ^ 2 ≤ ∑ H, ι * (c H * X H) := Finset.sum_le_sum fun H _ => hpt H
    _ = ι * ∑ H, c H * X H := by rw [Finset.mul_sum]
    _ ≤ ι * (ι * ∑ H, f H ^ 2) := mul_le_mul_of_nonneg_left hsum hι
    _ = ι ^ 2 * ∑ H, f H ^ 2 := by ring

/-- **L4**, trivial case: if either challenge is invalid then `P_Θ P_Θ' = 0`. -/
theorem bad_bad_of_not_valid {Θ Θ' : Ch} (h : Θ ∉ m.Valid ∨ Θ' ∉ m.Valid)
    (f : (𝔼 × Bool → V) → ℝ) : m.bad Θ (m.bad Θ' f) = 0 := by
  rcases h with h | h
  · exact m.bad_of_not_valid h _
  · rw [m.bad_of_not_valid h f]
    funext H; simp [bad, dproj, avg]

/-- The bad projector `P_Θ` as an operator on `ℓ²(Ω)`. -/
noncomputable def badOp (Θ : Ch) :
    EuclideanSpace ℝ (𝔼 × Bool → V) →L[ℝ] EuclideanSpace ℝ (𝔼 × Bool → V) :=
  lift (dprojₗ (m.check Θ) (m.sib Θ))

lemma badOp_apply (Θ : Ch) (x : EuclideanSpace ℝ (𝔼 × Bool → V)) :
    m.badOp Θ x = WithLp.toLp 2 (m.bad Θ x.ofLp) := rfl

/-- **L4**: `‖P_Θ P_Θ'‖ ≤ |Im_{U(Θ,Θ')}|⁻¹`. -/
theorem norm_badOp_comp_le (Θ Θ' : Ch) : ‖m.badOp Θ ∘L m.badOp Θ'‖ ≤ m.hit Θ Θ' := by
  refine norm_le_of_sum_sq_le _ (m.hit_nonneg _ _) fun x => ?_
  have hx : x = WithLp.toLp 2 x.ofLp := rfl
  rw [ContinuousLinearMap.comp_apply, badOp_apply, badOp_apply, norm_sq_toLp, hx, norm_sq_toLp]
  exact m.sum_bad_bad_sq_le Θ Θ' _

/-- **L3.4**: `P_Θ` is an orthogonal projector. -/
theorem isIdempotentElem_badOp (Θ : Ch) : IsIdempotentElem (m.badOp Θ) := by
  ext1 x
  change m.badOp Θ (m.badOp Θ x) = m.badOp Θ x
  rw [badOp_apply, badOp_apply]
  exact congrArg _ (dproj_dproj (m.isCheck Θ) _)

theorem inner_badOp (Θ : Ch) (x y : EuclideanSpace ℝ (𝔼 × Bool → V)) :
    ⟪m.badOp Θ x, y⟫_ℝ = ⟪x, m.badOp Θ y⟫_ℝ := by
  have hx : x = WithLp.toLp 2 x.ofLp := rfl
  have hy : y = WithLp.toLp 2 y.ofLp := rfl
  rw [badOp_apply, badOp_apply, hx, hy, inner_toLp, inner_toLp]
  exact (sum_mul_dproj (m.isCheck Θ) _ _).symm

end Model

end VoleMole.Extraction
