import VoleMole.Extraction.Product
import VoleMole.Extraction.Schur

/-!
# L6, L7 and the Core Theorem

States are functions `ψ : Ω → E` into the prover's register space `E`, with
`‖ψ‖² = Σ_H ‖ψ(H)‖²`. The norm profile of `ψ` is the real function `a_ψ(H) = ‖ψ(H)‖`.

A block-diagonal evolution is a family `W : Ω → E → E`, applied as `H ↦ W H (ψ H)`. The only
property used is that every block preserves norms. Unitary blocks (standard-oracle queries,
unitaries on `E` alone, and their compositions) have this property. Linearity of the blocks is
never used, so the theorems hold for arbitrary norm-preserving blocks.

`E` is any real normed space. A complex inner product space is one via
`InnerProductSpace.complexToReal`, with the same norm.
-/

open Finset
open scoped InnerProductSpace

set_option linter.unusedSectionVars false

namespace VoleMole.Extraction

section StateLemma

variable {L V : Type*} [DecidableEq L] [Fintype L] [Fintype V] [DecidableEq V] [Nonempty V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The norm profile `a_ψ(H) = ‖ψ(H)‖`. -/
def profile (ψ : (L → V) → E) : (L → V) → ℝ := fun H => ‖ψ H‖

/-- `‖ψ‖²` for `ψ ∈ ℓ²(Ω; E)`. -/
def nsq (ψ : (L → V) → E) : ℝ := ∑ H, ‖ψ H‖ ^ 2

lemma nsq_eq_profile (ψ : (L → V) → E) : nsq ψ = ∑ H, profile ψ H ^ 2 := rfl

/-- Apply a block-diagonal map. -/
def applyBlocks (W : (L → V) → E → E) (ψ : (L → V) → E) : (L → V) → E := fun H => W H (ψ H)

/-- Norm-preserving blocks preserve the norm profile. -/
lemma profile_applyBlocks {W : (L → V) → E → E} (hW : ∀ H v, ‖W H v‖ = ‖v‖)
    (ψ : (L → V) → E) : profile (applyBlocks W ψ) = profile ψ := by
  funext H; exact hW H (ψ H)

/-- **L6** (state lemma): for `d` `{0,1}`-valued and independent of the `S`-coordinates,
`‖D Π_S ψ‖² ≤ ⟨a_ψ, D Π_S a_ψ⟩`. -/
theorem state_lemma {d : (L → V) → ℝ} {S : Finset L} (hd : IsCheck d S) (ψ : (L → V) → E) :
    nsq (dproj d S ψ) ≤ ∑ H, profile ψ H * dproj d S (profile ψ) H := by
  rw [← sum_dproj_sq hd]
  refine Finset.sum_le_sum fun H _ => ?_
  have h : ‖dproj d S ψ H‖ ≤ dproj d S (profile ψ) H := by
    simp only [dproj, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hd.nonneg H), smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (norm_avg_le S ψ H) (hd.nonneg H)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end StateLemma

namespace Model

variable {𝔼 V T Ch : Type*} [Fintype 𝔼] [DecidableEq 𝔼] [AddCommGroup V] [Fintype V]
  [DecidableEq V] [AddCommGroup T] [Fintype T] [DecidableEq T] [Fintype Ch] [DecidableEq Ch]
variable (m : Model 𝔼 V T Ch)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The averaged operator `M = E_{Θ ∈ Ch} P_Θ` on `ℓ²(Ω)`. -/
noncomputable def M : EuclideanSpace ℝ (𝔼 × Bool → V) →L[ℝ] EuclideanSpace ℝ (𝔼 × Bool → V) :=
  (Fintype.card Ch : ℝ)⁻¹ • ∑ Θ, m.badOp Θ

lemma isSelfAdjoint_badOp (Θ : Ch) : IsSelfAdjoint (m.badOp Θ) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 (m.inner_badOp Θ)

lemma badOp_of_not_valid {Θ : Ch} (h : Θ ∉ m.Valid) : m.badOp Θ = 0 := by
  ext1 x
  rw [badOp_apply, m.bad_of_not_valid h]
  rfl

/-- `‖M‖ ≤ ε`: L5 applied to the family `(P_Θ)`, with L4 bounding each product. -/
theorem norm_M_le_eps : ‖m.M‖ ≤ m.eps := by
  rcases isEmpty_or_nonempty Ch with hCh | hCh
  · simpa [M] using m.eps_nonneg
  refine (norm_avg_projections_le m.badOp m.isIdempotentElem_badOp m.isSelfAdjoint_badOp).trans ?_
  refine ciSup_le fun Θ => ?_
  by_cases hΘ : Θ ∈ m.Valid
  · refine le_trans ?_ (m.epsTerm_le_eps Θ)
    simp only [epsTerm, hΘ, ↓reduceIte]
    gcongr with Θ'
    split_ifs with hΘ'
    · exact m.norm_badOp_comp_le Θ Θ'
    · simp [m.badOp_of_not_valid hΘ']
  · simpa [m.badOp_of_not_valid hΘ] using m.eps_nonneg

/-- `⟨a, M a⟩ = E_Θ ⟨a, P_Θ a⟩` for a real function `a`. -/
lemma inner_M_toLp (a : (𝔼 × Bool → V) → ℝ) :
    ⟪(WithLp.toLp 2 a : EuclideanSpace ℝ _), m.M (WithLp.toLp 2 a)⟫_ℝ =
      (Fintype.card Ch : ℝ)⁻¹ * ∑ Θ, ∑ H, a H * m.bad Θ a H := by
  simp only [M, smul_apply, _root_.sum_apply, inner_smul_right, inner_sum, badOp_apply, inner_toLp]

/-- **L7** (one game step): for norm-preserving block-diagonal `W_Θ`,
`E_Θ ‖P_Θ W_Θ ψ‖² ≤ ⟨a_ψ, M a_ψ⟩ ≤ ‖M‖ ‖ψ‖²`. -/
theorem game_step (W : Ch → (𝔼 × Bool → V) → E → E) (hW : ∀ Θ H v, ‖W Θ H v‖ = ‖v‖)
    (ψ : (𝔼 × Bool → V) → E) :
    (Fintype.card Ch : ℝ)⁻¹ * ∑ Θ, nsq (m.bad Θ (applyBlocks (W Θ) ψ)) ≤
        ⟪(WithLp.toLp 2 (profile ψ) : EuclideanSpace ℝ _), m.M (WithLp.toLp 2 (profile ψ))⟫_ℝ ∧
      ⟪(WithLp.toLp 2 (profile ψ) : EuclideanSpace ℝ _), m.M (WithLp.toLp 2 (profile ψ))⟫_ℝ ≤
        ‖m.M‖ * nsq ψ := by
  refine ⟨?_, ?_⟩
  · rw [inner_M_toLp]
    gcongr with Θ
    have h := state_lemma (m.isCheck Θ) (applyBlocks (W Θ) ψ)
    rwa [profile_applyBlocks (hW Θ)] at h
  · set x : EuclideanSpace ℝ (𝔼 × Bool → V) := WithLp.toLp 2 (profile ψ)
    have hx : ‖x‖ ^ 2 = nsq ψ := by rw [norm_sq_toLp]; rfl
    calc ⟪x, m.M x⟫_ℝ ≤ ‖x‖ * ‖m.M x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖m.M‖ * ‖x‖) := mul_le_mul_of_nonneg_left (m.M.le_opNorm x) (norm_nonneg _)
      _ = ‖m.M‖ * nsq ψ := by rw [← hx]; ring

/-- **Core Theorem.** For a finite family of states `ψ_x` and norm-preserving block-diagonal
evolutions `W_{x,Θ}`,
`Σ_x E_Θ ‖P_Θ W_{x,Θ} ψ_x‖² ≤ ‖M‖ · Σ_x ‖ψ_x‖²` and `‖M‖ ≤ ε`. -/
theorem core {X : Type*} [Fintype X] (ψ : X → (𝔼 × Bool → V) → E)
    (W : X → Ch → (𝔼 × Bool → V) → E → E) (hW : ∀ x Θ H v, ‖W x Θ H v‖ = ‖v‖) :
    ∑ x, (Fintype.card Ch : ℝ)⁻¹ * ∑ Θ, nsq (m.bad Θ (applyBlocks (W x Θ) (ψ x))) ≤
        ‖m.M‖ * ∑ x, nsq (ψ x) ∧
      ‖m.M‖ ≤ m.eps := by
  refine ⟨?_, m.norm_M_le_eps⟩
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ =>
    let h := m.game_step (W x) (hW x) (ψ x)
    h.1.trans h.2

/-- **Core Theorem**, normalised: if `Σ_x ‖ψ_x‖² = 1` then
`Σ_x E_Θ ‖P_Θ W_{x,Θ} ψ_x‖² ≤ ‖M‖ ≤ ε`. -/
theorem core_normalized {X : Type*} [Fintype X] (ψ : X → (𝔼 × Bool → V) → E)
    (hψ : ∑ x, nsq (ψ x) = 1)
    (W : X → Ch → (𝔼 × Bool → V) → E → E) (hW : ∀ x Θ H v, ‖W x Θ H v‖ = ‖v‖) :
    ∑ x, (Fintype.card Ch : ℝ)⁻¹ * ∑ Θ, nsq (m.bad Θ (applyBlocks (W x Θ) (ψ x))) ≤ ‖m.M‖ ∧
      ‖m.M‖ ≤ m.eps := by
  have h := m.core ψ W hW
  rw [hψ, mul_one] at h
  exact h

end Model

end VoleMole.Extraction
