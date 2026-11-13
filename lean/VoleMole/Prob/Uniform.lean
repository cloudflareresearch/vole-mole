import Mathlib.Probability.Distributions.Uniform

/-!
# Probabilities under the uniform distribution on a finite type

Phase A of `docs/probabilistic-plan.md` (M1): every single-sample statement of `Prob/` is a
probability under Mathlib's `PMF.uniformOfFintype`, which is what VCVio's `$ᵗ` is specified
against (`𝒟[$ᵗ β] = uniformOn univ`), so the statements transfer unchanged to a later oracle model.

* `prU α P`: the probability of `P` under the uniform distribution on `α`.
* `prU_eq_card`, `prU_eq_ofReal`, `prU_le_of_card_le`: the probability is `#{x | P x} / |α|`, so a
  count is a bound.
* `prU_mono`, `prU_or_le`: monotonicity and the union bound.
* `prU_map_equiv`: the pushforward of the uniform distribution along an equivalence is uniform
  (decoding uniform bytes into field elements and challenges, `Prob/Bytes.lean`).
* `prU_prod_le_left`, `prU_prod_le_right`: averaging over a product. If `P` has probability
  `≤ ε` in one coordinate for every value of the other, it has probability `≤ ε` on the product
  (a challenge drawn independently of data fixed before it).
-/

open Finset ENNReal

namespace VoleMole.Prob

/-- **The probability of `P` under the uniform distribution on the finite type `α`.** -/
noncomputable def prU (α : Type*) [Fintype α] [Nonempty α] (P : α → Prop) : ℝ≥0∞ :=
  (PMF.uniformOfFintype α).toOuterMeasure {x | P x}

variable {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]

theorem prU_eq_card (P : α → Prop) [DecidablePred P] :
    prU α P = (#{x | P x} : ℝ≥0∞) / Fintype.card α := by
  rw [prU, PMF.toOuterMeasure_uniformOfFintype_apply]
  congr 2
  rw [Fintype.card_ofFinset]
  rfl

/-- The probability as a real ratio (for bounds stated in `ℝ`, e.g. `Seed.epsQS`). -/
theorem prU_eq_ofReal (P : α → Prop) [DecidablePred P] :
    prU α P = ENNReal.ofReal ((#{x | P x} : ℝ) / Fintype.card α) := by
  rw [prU_eq_card, ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

/-- **A count bounds the probability.** -/
theorem prU_le_of_card_le (P : α → Prop) [DecidablePred P] {N : ℕ} (h : #{x | P x} ≤ N) :
    prU α P ≤ (N : ℝ≥0∞) / Fintype.card α := by
  rw [prU_eq_card]
  gcongr

theorem prU_mono {P R : α → Prop} (h : ∀ x, P x → R x) : prU α P ≤ prU α R :=
  (PMF.uniformOfFintype α).toOuterMeasure.mono fun x hx => h x hx

theorem prU_congr {P R : α → Prop} (h : ∀ x, P x ↔ R x) : prU α P = prU α R :=
  le_antisymm (prU_mono fun x => (h x).1) (prU_mono fun x => (h x).2)

/-- **The union bound.** -/
theorem prU_or_le (P R : α → Prop) : prU α (fun x => P x ∨ R x) ≤ prU α P + prU α R :=
  MeasureTheory.measure_union_le (μ := (PMF.uniformOfFintype α).toOuterMeasure) _ _

theorem prU_false : prU α (fun _ => False) = 0 := by
  classical
  rw [prU_eq_card]; simp

theorem prU_le_one (P : α → Prop) : prU α P ≤ 1 := by
  classical
  rw [prU_eq_card]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_univ (α := α)).le

/-- **The uniform distribution pushed along an equivalence is uniform.** -/
theorem prU_map_equiv (e : α ≃ β) (P : β → Prop) : prU β P = prU α (P ∘ e) := by
  classical
  rw [prU_eq_card, prU_eq_card, Fintype.card_congr e]
  congr 2
  exact_mod_cast (Finset.card_equiv e (by simp)).symm

omit [Nonempty α] [Nonempty β] in
lemma card_filter_prod (P : α × β → Prop) [DecidablePred P] :
    #{x : α × β | P x} = ∑ b : β, #{a : α | P (a, b)} := by
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  exact Finset.sum_congr rfl fun b _ => (Finset.card_filter _ _).symm

/-- **Averaging over the second coordinate**: a bound `ε` on the probability over `a` for every
fixed `b` bounds the probability over `(a, b)`. -/
theorem prU_prod_le_left (P : α × β → Prop) {ε : ℝ≥0∞}
    (h : ∀ b, prU α (fun a => P (a, b)) ≤ ε) : prU (α × β) P ≤ ε := by
  classical
  have hα : (Fintype.card α : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [prU_eq_card, card_filter_prod, Fintype.card_prod, Nat.cast_sum, Nat.cast_mul,
    ENNReal.sum_div]
  calc ∑ b, (#{a | P (a, b)} : ℝ≥0∞) / (Fintype.card α * Fintype.card β)
      = ∑ b, prU α (fun a => P (a, b)) / Fintype.card β := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [prU_eq_card, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl hα) (Or.inl (by simp)), mul_comm (Fintype.card α : ℝ≥0∞)⁻¹,
          mul_assoc]
    _ ≤ ∑ _b : β, ε / Fintype.card β := Finset.sum_le_sum fun b _ => by gcongr; exact h b
    _ = ε := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.mul_div_cancel hβ (by simp)]

/-- **Averaging over the first coordinate.** -/
theorem prU_prod_le_right (P : α × β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, prU β (fun b => P (a, b)) ≤ ε) : prU (α × β) P ≤ ε := by
  rw [prU_map_equiv (Equiv.prodComm β α)]
  exact prU_prod_le_left _ h

/-- An event about the first coordinate has its marginal probability. -/
theorem prU_fst_le (P : α → Prop) {ε : ℝ≥0∞} (h : prU α P ≤ ε) :
    prU (α × β) (fun x => P x.1) ≤ ε :=
  prU_prod_le_left _ fun _ => h

/-- An event about the second coordinate has its marginal probability. -/
theorem prU_snd_le (P : β → Prop) {ε : ℝ≥0∞} (h : prU β P ≤ ε) :
    prU (α × β) (fun x => P x.2) ≤ ε :=
  prU_prod_le_right _ fun _ => h

end VoleMole.Prob
