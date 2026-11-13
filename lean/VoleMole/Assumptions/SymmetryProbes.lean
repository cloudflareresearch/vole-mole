import VoleMole.Privacy.PqovDelta

/-!
# Probes
-/

open Finset

namespace VoleMole.Assumptions.SymmetryProbes

open VoleMole.Privacy VoleMole.Privacy.Moussaka Module

variable {F : Type*} [Field F]

/-! ## Evaluation of an array of slices at a vector -/

/-- `Σ_i a_i • L_i`: the slice of the array `L` at the vector `a`. -/
def ev {ι S : Type*} [Fintype ι] [AddCommGroup S] [Module F S] (L : ι → S) (a : ι → F) : S :=
  ∑ i, a i • L i

section Ev

variable {ι S : Type*} [Fintype ι] [AddCommGroup S] [Module F S]

lemma ev_add (L : ι → S) (a b : ι → F) : ev L (a + b) = ev L a + ev L b := by
  simp only [ev, Pi.add_apply, add_smul, Finset.sum_add_distrib]

lemma ev_smul (L : ι → S) (c : F) (a : ι → F) : ev L (c • a) = c • ev L a := by
  simp only [ev, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

lemma ev_zero (L : ι → S) : ev L (0 : ι → F) = 0 := by
  simp [ev]

lemma ev_sub (L : ι → S) (a b : ι → F) : ev L (a - b) = ev L a - ev L b := by
  simp only [ev, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- The slices of `L` at the vectors of a family, as an additive map of `L`. -/
def evHom {α : Type*} (u : α → ι → F) : (ι → S) →+ (α → S) where
  toFun L a := ev L (u a)
  map_zero' := by funext a; simp [ev]
  map_add' L L' := by
    funext a
    simp only [ev, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- A linearly independent family has a dual family. -/
lemma exists_dual {α : Type*} [Fintype α] [DecidableEq α] {u : α → ι → F}
    (hu : LinearIndependent F u) :
    ∃ d : α → ι → F, ∀ a b, ∑ i, d a i * u b i = if a = b then 1 else 0 := by
  classical
  have hinj := linearIndependent_iff_injective_fintypeLinearCombination.1 hu
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    (Fintype.linearCombination F u) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨fun a i => g (fun j => if i = j then 1 else 0) a, fun a b => ?_⟩
  have h1 : g (u b) a = ∑ i, g (fun j => if i = j then 1 else 0) a * u b i := by
    rw [LinearMap.pi_apply_eq_sum_univ g (u b)]
    simp [Finset.sum_apply, mul_comm]
  have h2 : g (u b) = Pi.single b 1 := by
    have := congrArg (fun f => f (Pi.single b 1)) hg
    simpa [Fintype.linearCombination_apply] using this
  rw [← h1, h2]
  simp [Pi.single_apply]

/-- **Interpolation**: the slices of a uniform array at linearly independent vectors can be
prescribed, so they are uniform and independent. -/
theorem evHom_surjective {α : Type*} [Fintype α] {u : α → ι → F} (hu : LinearIndependent F u) :
    Function.Surjective (evHom (S := S) u) := by
  classical
  obtain ⟨d, hd⟩ := exists_dual hu
  intro τ
  refine ⟨fun i => ∑ a, d a i • τ a, ?_⟩
  funext b
  simp only [evHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ev, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [Finset.sum_eq_single b (fun a _ hab => by
    rw [show ∑ i, u b i * d a i = 0 by
      simp only [mul_comm (u b _), hd a b, hab, ↓reduceIte], zero_smul]) (by simp)]
  rw [show ∑ i, u b i * d b i = 1 by simp only [mul_comm (u b _), hd b b, ↓reduceIte], one_smul]

end Ev

/-! ## Probabilities -/

/-- A surjective additive map takes each value with probability `1/|H|`. -/
lemma pr_fiber {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (c : H) :
    pr G (fun g => f g = c) = 1 / Fintype.card H := by
  classical
  rw [pr_comp_addHom f hf (fun h => h = c), pr_def]
  congr 1
  rw [Finset.filter_eq' univ c]
  simp

/-- **Free probes.** Let `t_j`, `a_j` (`j < ρ`) be `2ρ` linearly independent vectors and let each
`Rel j` determine its second argument from the first. Then for a uniform array `L` the slices at
`a_j` are in relation with the slices at `t_j` with probability at most `|S|^{−ρ}`. -/
theorem pr_free {ι S : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup S] [Module F S]
    [Fintype S] {ρ : ℕ} (t a : Fin ρ → ι → F) (h : LinearIndependent F (Sum.elim t a))
    (Rel : Fin ρ → S → S → Prop) (hRel : ∀ j X Y Y', Rel j X Y → Rel j X Y' → Y = Y') :
    pr (ι → S) (fun L => ∀ j, Rel j (ev L (t j)) (ev L (a j))) ≤
      1 / (Fintype.card S : ℝ) ^ ρ := by
  classical
  have e := pr_comp_addHom (evHom (S := S) (Sum.elim t a)) (evHom_surjective h)
    (fun f => ∀ j, Rel j (f (Sum.inl j)) (f (Sum.inr j)))
  have e' : pr (ι → S) (fun L => ∀ j, Rel j (ev L (t j)) (ev L (a j))) =
      pr (Fin ρ ⊕ Fin ρ → S) (fun f => ∀ j, Rel j (f (Sum.inl j)) (f (Sum.inr j))) := by
    rw [← e]; rfl
  rw [e', pr_def]
  have hc : #{f : Fin ρ ⊕ Fin ρ → S | ∀ j, Rel j (f (Sum.inl j)) (f (Sum.inr j))} ≤
      Fintype.card (Fin ρ → S) := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun f j => f (Sum.inl j)) (fun _ _ => mem_univ _) ?_
    intro f hf g hg hfg
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf hg
    funext x
    rcases x with j | j
    · exact congrFun hfg j
    · have := congrFun hfg j
      dsimp only at this
      exact hRel j _ _ _ (hf j) (this ▸ hg j)
  have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have : (Fintype.card (Fin ρ ⊕ Fin ρ → S) : ℝ) =
      (Fintype.card S : ℝ) ^ ρ * (Fintype.card S : ℝ) ^ ρ := by
    simp [Fintype.card_sum, pow_add]
  rw [this]
  have hc' : (#{f : Fin ρ ⊕ Fin ρ → S | ∀ j, Rel j (f (Sum.inl j)) (f (Sum.inr j))} : ℝ) ≤
      (Fintype.card S : ℝ) ^ ρ := by
    have : (Fintype.card (Fin ρ → S) : ℝ) = (Fintype.card S : ℝ) ^ ρ := by simp
    rw [← this]; exact_mod_cast hc
  exact mul_le_mul_of_nonneg_right hc' (by positivity)

/-! ## Kernels of a few functionals -/

/-- The common kernel of `c` functionals on `F^κ` contains `|κ| − c` independent vectors. -/
lemma exists_indep_ker {κ : Type*} [Fintype κ] [DecidableEq κ] (c : ℕ) (Φ : Fin c → κ → F) :
    ∃ y : Fin (Fintype.card κ - c) → κ → F, LinearIndependent F y ∧ ∀ b a, Φ a ⬝ᵥ y b = 0 := by
  classical
  let f : (κ → F) →ₗ[F] (Fin c → F) := Matrix.mulVecLin (Matrix.of Φ)
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : finrank F (LinearMap.range f) ≤ c := by
    have := Submodule.finrank_le (LinearMap.range f)
    simpa using this
  have h3 : finrank F (κ → F) = Fintype.card κ := by simp
  have h4 : Fintype.card κ - c ≤ finrank F (LinearMap.ker f) := by omega
  obtain ⟨y, hy⟩ := exists_linearIndependent_of_le_finrank h4
  refine ⟨fun b => (y b : κ → F), hy.map' (LinearMap.ker f).subtype (Submodule.ker_subtype _),
    fun b a => ?_⟩
  have := (y b).2
  rw [LinearMap.mem_ker] at this
  exact congrFun this a

/-! ## Arrays with three indices -/

section Tri

variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]

/-- The trilinear form of an array: `Σ a_i b_j c_k L_{ijk}`. -/
def tri (L : ι₁ → ι₂ → ι₃ → F) (a : ι₁ → F) (b : ι₂ → F) (c : ι₃ → F) : F :=
  ev (ev (ev L a) b) c

variable [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃] [Fintype F]

/-- **Vanishing on a box.** For `w ≠ 0` and `c₂`, `c₃` functionals on the other two legs, a
uniform array vanishes on `w × ker Φ × ker Ψ` with probability at most
`|F|^{−(n₂ − c₂)(n₃ − c₃)}`. -/
theorem pr_vanish_fixed {w : ι₁ → F} (hw : w ≠ 0) {c₂ c₃ : ℕ} (Φ : Fin c₂ → ι₂ → F)
    (Ψ : Fin c₃ → ι₃ → F) :
    pr (ι₁ → ι₂ → ι₃ → F) (fun L => ∀ b c, (∀ a, Φ a ⬝ᵥ b = 0) → (∀ a, Ψ a ⬝ᵥ c = 0) →
      tri L w b c = 0) ≤
      1 / (Fintype.card F : ℝ) ^ ((Fintype.card ι₃ - c₃) * (Fintype.card ι₂ - c₂)) := by
  classical
  obtain ⟨y, hy, hyΦ⟩ := exists_indep_ker c₂ Φ
  obtain ⟨z, hz, hzΨ⟩ := exists_indep_ker c₃ Ψ
  have hw' : LinearIndependent F (fun _ : Unit => w) := LinearIndependent.of_subsingleton () hw
  let G₁ : (ι₁ → ι₂ → ι₃ → F) →+ (Unit → ι₂ → ι₃ → F) := evHom (fun _ : Unit => w)
  let G₂ : (ι₂ → ι₃ → F) →+ (Fin (Fintype.card ι₂ - c₂) → ι₃ → F) := evHom y
  let G₃ : (ι₃ → F) →+ (Fin (Fintype.card ι₃ - c₃) → F) := evHom z
  let G : (ι₁ → ι₂ → ι₃ → F) →+
      (Fin (Fintype.card ι₂ - c₂) → Fin (Fintype.card ι₃ - c₃) → F) :=
    (AddMonoidHom.compLeft G₃ _).comp (G₂.comp ((Pi.evalAddMonoidHom _ ()).comp G₁))
  have hG : Function.Surjective G := by
    have h1 : Function.Surjective (Pi.evalAddMonoidHom (fun _ : Unit => ι₂ → ι₃ → F) ()) :=
      fun x => ⟨fun _ => x, rfl⟩
    have h3 : Function.Surjective (AddMonoidHom.compLeft G₃ (Fin (Fintype.card ι₂ - c₂))) :=
      Function.Surjective.comp_left (evHom_surjective hz)
    simp only [G, AddMonoidHom.coe_comp]
    exact h3.comp ((evHom_surjective hy).comp (h1.comp (evHom_surjective hw')))
  refine (pr_mono (Q := fun L => G L = 0) fun L hL => ?_).trans (le_of_eq ?_)
  · funext a b
    exact hL (y a) (z b) (fun a' => hyΦ a a') (fun a' => hzΨ b a')
  · rw [pr_fiber G hG]
    simp [← pow_mul]

/-- The bilinear map of an array with the target index first:
`L(v, x)_k = Σ v_i x_j L_{kij}`. -/
def bil (L : ι₁ → ι₂ → ι₃ → F) (v : ι₂ → F) (x : ι₃ → F) : ι₁ → F :=
  fun k => ev (ev (L k) v) x

/-- **Paired probes.** For `2n` independent vectors `v_i`, `v'_j` and `2n` independent vectors
`o_i`, `o'_j`, a uniform array has `L(v_i, o'_j) + L(v'_j, o_i) = 0` for all `i`, `j` with
probability `|F|^{−n₁ n²}`. -/
theorem pr_paired {n : ℕ} (v v' : Fin n → ι₂ → F) (o o' : Fin n → ι₃ → F)
    (hv : LinearIndependent F (Sum.elim v v')) (ho : LinearIndependent F (Sum.elim o o')) :
    pr (ι₁ → ι₂ → ι₃ → F) (fun L => ∀ i j, bil L (v i) (o' j) + bil L (v' j) (o i) = 0) ≤
      1 / (Fintype.card F : ℝ) ^ (n * n * Fintype.card ι₁) := by
  classical
  let H₂ : (ι₂ → ι₃ → F) →+ (Fin n ⊕ Fin n → Fin n ⊕ Fin n → F) :=
    (AddMonoidHom.compLeft (evHom (Sum.elim o o')) _).comp (evHom (Sum.elim v v'))
  have hH₂ : Function.Surjective H₂ := by
    have h3 : Function.Surjective
        (AddMonoidHom.compLeft (evHom (S := F) (Sum.elim o o')) (Fin n ⊕ Fin n)) :=
      Function.Surjective.comp_left (evHom_surjective ho)
    simp only [H₂, AddMonoidHom.coe_comp]
    exact h3.comp (evHom_surjective hv)
  let Γ : (Fin n ⊕ Fin n → Fin n ⊕ Fin n → F) →+ (Fin n → Fin n → F) :=
    { toFun := fun m i j => m (Sum.inl i) (Sum.inr j) + m (Sum.inr j) (Sum.inl i)
      map_zero' := by funext i j; simp
      map_add' := fun m m' => by funext i j; simp only [Pi.add_apply]; ring }
  have hΓ : Function.Surjective Γ := by
    intro τ
    refine ⟨fun s s' => Sum.elim (fun i => Sum.elim (fun _ => 0) (fun j => τ i j) s')
      (fun _ => 0) s, ?_⟩
    funext i j
    simp [Γ]
  let G : (ι₁ → ι₂ → ι₃ → F) →+ (ι₁ → Fin n → Fin n → F) :=
    AddMonoidHom.compLeft (Γ.comp H₂) ι₁
  have hG : Function.Surjective G := by
    have : Function.Surjective (Γ.comp H₂) := by
      rw [AddMonoidHom.coe_comp]; exact hΓ.comp hH₂
    exact Function.Surjective.comp_left this
  refine (pr_mono (Q := fun L => G L = 0) fun L hL => ?_).trans (le_of_eq ?_)
  · funext k i j
    exact congrFun (hL i j) k
  · rw [pr_fiber G hG]
    simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.cast_pow, ← pow_mul]

end Tri

end VoleMole.Assumptions.SymmetryProbes
