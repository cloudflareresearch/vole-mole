import VoleMole.Extraction.Ops

/-!
# The finite data of the abstract model (sketch §3)

Gates `𝔼`, labels `L = 𝔼 × Bool`, label values `V`, check targets `T`, challenges `Ch`. The forced
label of gate `e` under `Θ` is `(e, γ e Θ)` and the sibling is `(e, !γ e Θ)`, so forced and sibling
labels partition `L` by construction; this is (A2).
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Extraction

/-- The finite data of §3. -/
structure Model (𝔼 V T Ch : Type*) [AddCommGroup V] [AddCommGroup T] where
  /-- `φ e : V → T`, the contribution of gate `e`'s hash value to the check. -/
  φ : 𝔼 → V →+ T
  /-- `γ e Θ`: which label of gate `e` the verifier queries under challenge `Θ`. -/
  γ : 𝔼 → Ch → Bool
  /-- The check target. -/
  τ : Ch → T
  /-- Challenges that are not rejected outright (grinding, opening size). -/
  Valid : Finset Ch

namespace Model

variable {𝔼 V T Ch : Type*} [Fintype 𝔼] [DecidableEq 𝔼] [AddCommGroup V] [Fintype V]
  [DecidableEq V] [AddCommGroup T] [Fintype T] [DecidableEq T] [Fintype Ch] [DecidableEq Ch]
variable (m : Model 𝔼 V T Ch)

/-- The sibling labels `S_Θ`. -/
def sib (Θ : Ch) : Finset (𝔼 × Bool) := {l | l.2 ≠ m.γ l.1 Θ}

lemma mem_sib {Θ : Ch} {l : 𝔼 × Bool} : l ∈ m.sib Θ ↔ l.2 ≠ m.γ l.1 Θ := by simp [sib]

lemma forced_not_mem_sib (Θ : Ch) (e : 𝔼) : (e, m.γ e Θ) ∉ m.sib Θ := by simp [sib]

/-- The diagonal check `c_Θ(H) = [Θ ∈ Valid] · [Σ_e φ_e(H(e, γ_e(Θ))) = τ(Θ)]`. -/
noncomputable def check (Θ : Ch) (H : 𝔼 × Bool → V) : ℝ :=
  if Θ ∈ m.Valid ∧ ∑ e, m.φ e (H (e, m.γ e Θ)) = m.τ Θ then 1 else 0

/-- The bad projector `P_Θ = C_Θ Π_{S_Θ}`. -/
noncomputable def bad (Θ : Ch) {X : Type*} [AddCommGroup X] [Module ℝ X]
    (ψ : (𝔼 × Bool → V) → X) : (𝔼 × Bool → V) → X :=
  dproj (m.check Θ) (m.sib Θ) ψ

/-- The disagreement set `U(Θ, Θ') = {e | γ_e(Θ) ≠ γ_e(Θ')}`. -/
def disagree (Θ Θ' : Ch) : Finset 𝔼 := {e | m.γ e Θ ≠ m.γ e Θ'}

lemma disagree_comm (Θ Θ' : Ch) : m.disagree Θ Θ' = m.disagree Θ' Θ := by
  simp [disagree, ne_comm]

/-- `|Im_{U(Θ,Θ')}|⁻¹`. -/
noncomputable def hit (Θ Θ' : Ch) : ℝ := (Nat.card (ImU m.φ (m.disagree Θ Θ')) : ℝ)⁻¹

lemma hit_comm (Θ Θ' : Ch) : m.hit Θ Θ' = m.hit Θ' Θ := by simp [hit, disagree_comm]

lemma hit_nonneg (Θ Θ' : Ch) : 0 ≤ m.hit Θ Θ' := by simp [hit]

/-- The per-challenge term of `ε`: `E_{Θ'} [Θ' ∈ Valid] · |Im_{U(Θ,Θ')}|⁻¹` for valid `Θ`, else 0. -/
noncomputable def epsTerm (Θ : Ch) : ℝ :=
  if Θ ∈ m.Valid then
    (Fintype.card Ch : ℝ)⁻¹ * ∑ Θ', if Θ' ∈ m.Valid then m.hit Θ Θ' else 0
  else 0

/-- `ε := max_{Θ ∈ Valid} E_{Θ' ∈ Ch} [Θ' ∈ Valid] · |Im_{U(Θ,Θ')}|⁻¹`, and `0` if `Valid = ∅`. -/
noncomputable def eps : ℝ := ⨆ Θ : Ch, m.epsTerm Θ

lemma epsTerm_nonneg (Θ : Ch) : 0 ≤ m.epsTerm Θ := by
  unfold epsTerm
  split_ifs
  · refine mul_nonneg (by positivity) (Finset.sum_nonneg fun Θ' _ => ?_)
    split_ifs
    · exact m.hit_nonneg _ _
    · exact le_rfl
  · exact le_rfl

lemma epsTerm_le_eps (Θ : Ch) : m.epsTerm Θ ≤ m.eps :=
  le_ciSup (Set.finite_range _).bddAbove Θ

lemma eps_nonneg : 0 ≤ m.eps := by
  rcases isEmpty_or_nonempty Ch with h | ⟨⟨Θ⟩⟩
  · simp [eps]
  · exact (m.epsTerm_nonneg Θ).trans (m.epsTerm_le_eps Θ)

/-! ### Basic properties of the check -/

lemma check_invOn (Θ : Ch) : InvOn (m.sib Θ) (m.check Θ) := by
  intro H H' h
  have : ∀ e, H (e, m.γ e Θ) = H' (e, m.γ e Θ) := fun e => h _ (m.forced_not_mem_sib Θ e)
  simp [check, this]

lemma isCheck (Θ : Ch) : IsCheck (m.check Θ) (m.sib Θ) where
  idem H := by unfold check; split_ifs <;> simp
  inv := m.check_invOn Θ

lemma check_of_not_valid {Θ : Ch} (h : Θ ∉ m.Valid) (H : 𝔼 × Bool → V) : m.check Θ H = 0 := by
  simp [check, h]

lemma bad_of_not_valid {Θ : Ch} (h : Θ ∉ m.Valid) {X : Type*} [AddCommGroup X] [Module ℝ X]
    (ψ : (𝔼 × Bool → V) → X) : m.bad Θ ψ = 0 := by
  funext H; simp [bad, dproj, m.check_of_not_valid h]

/-! ### The sibling average of a check (the use of L1/L2 inside L4) -/

/-- The part of the check sum of `Θ'` that reads the siblings of `Θ`, as a homomorphism of `Ω`. -/
def sibHom (Θ Θ' : Ch) : (𝔼 × Bool → V) →+ T where
  toFun G := ∑ e, m.φ e (mix (m.sib Θ) G 0 (e, m.γ e Θ'))
  map_zero' := by simp [mix]
  map_add' G G' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← map_add]
    congr 1
    simp only [mix, Pi.add_apply, Pi.zero_apply]
    split_ifs <;> simp

lemma ImU_le_range_sibHom (Θ Θ' : Ch) : ImU m.φ (m.disagree Θ Θ') ≤ (m.sibHom Θ Θ').range := by
  refine iSup₂_le fun e he => ?_
  rintro _ ⟨v, rfl⟩
  refine ⟨Pi.single (e, m.γ e Θ') v, ?_⟩
  have hsib : (e, m.γ e Θ') ∈ m.sib Θ := by
    simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and] at he
    simpa [mem_sib] using Ne.symm he
  simp only [sibHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single e]
  · simp [mix, hsib]
  · intro e' _ hne
    have : ((e', m.γ e' Θ') : 𝔼 × Bool) ≠ (e, m.γ e Θ') := fun h => hne (congrArg Prod.fst h)
    simp only [mix]
    split_ifs <;> simp [this]
  · simp

/-- Averaging the check of `Θ'` over the siblings of `Θ` gives at most `|Im_{U(Θ,Θ')}|⁻¹`: for
fixed values outside `S_Θ`, the check of `Θ'` constrains `Σ_{e ∈ U} φ_e` of the values at
`S_Θ ∩ F_{Θ'}` to a single target. -/
lemma avg_check_le (Θ Θ' : Ch) (H : 𝔼 × Bool → V) :
    avg (m.sib Θ) (m.check Θ') H ≤ m.hit Θ Θ' := by
  by_cases hv : Θ' ∈ m.Valid
  · have hsplit : ∀ G, ∑ e, m.φ e (mix (m.sib Θ) G H (e, m.γ e Θ')) =
        m.sibHom Θ Θ' G + ∑ e, m.φ e (mix (m.sib Θ) 0 H (e, m.γ e Θ')) := by
      intro G
      simp only [sibHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ← Finset.sum_add_distrib, ← map_add]
      refine Finset.sum_congr rfl fun e _ => ?_
      congr 1
      simp only [mix, Pi.zero_apply]
      split_ifs <;> simp
    obtain ⟨t, ht⟩ : ∃ t, t = m.τ Θ' - ∑ e, m.φ e (mix (m.sib Θ) 0 H (e, m.γ e Θ')) := ⟨_, rfl⟩
    have hc : ∀ G, m.check Θ' (mix (m.sib Θ) G H) = if m.sibHom Θ Θ' G = t then 1 else 0 := by
      intro G
      unfold check
      rw [hsplit G, ht]
      simp only [hv, true_and, eq_sub_iff_add_eq]
    simp only [avg, smul_eq_mul, hc, Finset.sum_boole]
    exact fiber_prob_le_of_le_range _ (m.ImU_le_range_sibHom Θ Θ') t
  · simp [avg, m.check_of_not_valid hv, m.hit_nonneg]

end Model

end VoleMole.Extraction
