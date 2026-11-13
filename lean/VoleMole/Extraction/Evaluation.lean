import VoleMole.Extraction.Model

/-!
# Evaluation of `ε` for linear forced-label maps (sketch §5)

In FAEST, the H₂³ output `Θ` decodes to `Δ' = δ(Θ) ∈ F₂^{n_Δ}` (its first `n_Δ` bits). A valid `Θ`
has its last `w_grind` bits zero, so `δ` is injective on `Valid`. The forced label of gate `e` is
`γ_e(Θ) = G[e]·Δ'`. Then `U(Θ, Θ') = supp(G(Δ' ⊕ Δ''))`, and

`ε ≤ |Ch|⁻¹ · Σ_{c ∈ F₂^{n_Δ}} |Im_{supp(Gc)}|⁻¹ = 2^{-w_grind} · E_c |Im_{supp(Gc)}|⁻¹`

(with `|Ch| = 2^λ` and `n_Δ = λ - w_grind`). The FAEST lower bound `|Im_U| ≥ 2^{4ρ(U)}`, which
turns the right-hand side into `2^{-w_grind} · ε_gate`, is left as a numeric input.

Here `F₂^{n_Δ}` is any finite abelian group `D`, and `G[e]·_` is any homomorphism `D →+ ZMod 2`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Extraction

namespace Model

variable {𝔼 V T Ch : Type*} [Fintype 𝔼] [DecidableEq 𝔼] [AddCommGroup V] [Fintype V]
  [DecidableEq V] [AddCommGroup T] [Fintype T] [DecidableEq T] [Fintype Ch] [DecidableEq Ch]
variable (m : Model 𝔼 V T Ch)

/-- `supp(Gc) = {e | G[e]·c ≠ 0}`. -/
def suppG {D : Type*} [AddCommGroup D] (g : 𝔼 → D →+ ZMod 2) (c : D) : Finset 𝔼 :=
  {e | g e c ≠ 0}

lemma zmod2_ne_iff (a b : ZMod 2) : (¬((a = 1) ↔ (b = 1))) ↔ b - a ≠ 0 := by
  revert a b; decide

theorem disagree_eq_suppG {D : Type*} [AddCommGroup D] (δ : Ch → D) (g : 𝔼 → D →+ ZMod 2)
    (hγ : ∀ e, ∀ Θ ∈ m.Valid, (m.γ e Θ = true ↔ g e (δ Θ) = 1)) {Θ Θ' : Ch}
    (hΘ : Θ ∈ m.Valid) (hΘ' : Θ' ∈ m.Valid) : m.disagree Θ Θ' = suppG g (δ Θ' - δ Θ) := by
  ext e
  simp only [disagree, suppG, Finset.mem_filter, Finset.mem_univ, true_and, map_sub]
  rw [← zmod2_ne_iff, ← hγ e Θ hΘ, ← hγ e Θ' hΘ', Bool.eq_iff_iff.symm.not]

/-- **Evaluation of `ε`.** If `γ_e(Θ) = G[e]·δ(Θ)` on valid challenges and `δ` is injective on
them, then `ε ≤ |Ch|⁻¹ · Σ_c |Im_{supp(Gc)}|⁻¹`. -/
theorem eps_le_of_linear_gamma {D : Type*} [AddCommGroup D] [Fintype D] [DecidableEq D]
    (δ : Ch → D) (g : 𝔼 → D →+ ZMod 2) (hinj : Set.InjOn δ m.Valid)
    (hγ : ∀ e, ∀ Θ ∈ m.Valid, (m.γ e Θ = true ↔ g e (δ Θ) = 1)) :
    m.eps ≤ (Fintype.card Ch : ℝ)⁻¹ * ∑ c : D, (Nat.card (ImU m.φ (suppG g c)) : ℝ)⁻¹ := by
  set F : D → ℝ := fun c => (Nat.card (ImU m.φ (suppG g c)) : ℝ)⁻¹
  have hF : ∀ c, 0 ≤ F c := fun c => by simp [F]
  have hR : 0 ≤ (Fintype.card Ch : ℝ)⁻¹ * ∑ c, F c :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun c _ => hF c)
  refine Real.iSup_le (fun Θ => ?_) hR
  by_cases hΘ : Θ ∈ m.Valid
  · simp only [epsTerm, hΘ, ↓reduceIte]
    gcongr
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    calc ∑ Θ' ∈ m.Valid, m.hit Θ Θ' = ∑ Θ' ∈ m.Valid, F (δ Θ' - δ Θ) :=
          Finset.sum_congr rfl fun Θ' hΘ' => by
            simp only [hit, F, m.disagree_eq_suppG δ g hγ hΘ hΘ']
      _ = ∑ c ∈ m.Valid.image (fun Θ' => δ Θ' - δ Θ), F c := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          exact hinj ha hb (sub_left_injective hab)
      _ ≤ ∑ c, F c := Finset.sum_le_univ_sum_of_nonneg hF
  · simpa [epsTerm, hΘ] using hR

end Model

end VoleMole.Extraction
