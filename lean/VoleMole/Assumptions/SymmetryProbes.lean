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

/-! ## Maps that are close to a scalar -/

section Det

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- A **free family** of size `m` for `g`: vectors `t_j` with `t_j`, `g t_j` (`2m` vectors)
linearly independent. -/
def FreeFam (g : V → V) (m : ℕ) : Prop :=
  ∃ t : Fin m → V, finrank F (Submodule.span F (Set.range t ∪ Set.range (g ∘ t))) = 2 * m

lemma freeFam_indep [FiniteDimensional F V] {g : V → V} {m : ℕ} {t : Fin m → V}
    (h : finrank F (Submodule.span F (Set.range t ∪ Set.range (g ∘ t))) = 2 * m) :
    LinearIndependent F (Sum.elim t (g ∘ t)) := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, Set.Sum.elim_range, h]
  simp [two_mul]

lemma finrank_sup_singleton [FiniteDimensional F V] (W : Submodule F V) {x : V} (hx : x ∉ W) :
    finrank F (W ⊔ F ∙ x : Submodule F V) = finrank F W + 1 := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ W.zero_mem)
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (F ∙ x)
  rw [((Submodule.disjoint_span_singleton' hx0).2 hx).eq_bot, finrank_bot,
    finrank_span_singleton hx0] at h
  omega

lemma finrank_span_singleton_le' (x : V) : finrank F (F ∙ x : Submodule F V) ≤ 1 := by
  by_cases hx : x = 0
  · rw [hx, Submodule.span_zero_singleton, finrank_bot]
    exact zero_le_one
  · rw [finrank_span_singleton hx]

lemma freeFam_succ [FiniteDimensional F V] {g : V → V} {m : ℕ} {t : Fin m → V}
    (h : finrank F (Submodule.span F (Set.range t ∪ Set.range (g ∘ t))) = 2 * m) {u : V}
    (hu : u ∉ Submodule.span F (Set.range t ∪ Set.range (g ∘ t)))
    (hgu : g u ∉ Submodule.span F (Set.range t ∪ Set.range (g ∘ t)) ⊔ F ∙ u) :
    FreeFam (F := F) g (m + 1) := by
  refine ⟨Fin.cons u t, ?_⟩
  have e : Submodule.span F (Set.range (Fin.cons u t : Fin (m + 1) → V) ∪
      Set.range (g ∘ (Fin.cons u t : Fin (m + 1) → V))) =
      (Submodule.span F (Set.range t ∪ Set.range (g ∘ t)) ⊔ F ∙ u) ⊔ F ∙ g u := by
    rw [Fin.comp_cons, Fin.range_cons, Fin.range_cons, Submodule.span_union,
      Submodule.span_insert, Submodule.span_insert, Submodule.span_union]
    ac_rfl
  rw [e, finrank_sup_singleton _ hgu, finrank_sup_singleton _ hu, h]
  ring

/-- **A map without `ρ` free vectors is a scalar up to a small subspace.** Let `g` be additive
and `σ`-semilinear on a space of dimension `> 2ρ`, with no free family of size `ρ`. Then there
are `c` and a subspace `Z` of dimension `≤ 2(ρ − 1)` with `g u − c u ∈ Z` for all `u`; and `c = 0`
or `σ` is the identity. -/
theorem near_scalar [FiniteDimensional F V] (σ : F →+* F) (g : V → V)
    (hadd : ∀ u w, g (u + w) = g u + g w) (hsm : ∀ (c : F) u, g (c • u) = σ c • g u) {ρ : ℕ}
    (hρ : 2 * ρ + 1 ≤ finrank F V) (hfree : ¬ FreeFam (F := F) g ρ) :
    ∃ (c : F) (Z : Submodule F V), finrank F Z ≤ 2 * (ρ - 1) ∧ (∀ u, g u - c • u ∈ Z) ∧
      (c = 0 ∨ ∀ x, σ x = x) := by
  classical
  have h0 : FreeFam (F := F) g 0 := ⟨Fin.elim0, by simp⟩
  set m := Nat.findGreatest (FreeFam (F := F) g) ρ with hm
  have hmP : FreeFam (F := F) g m := Nat.findGreatest_spec (Nat.zero_le ρ) h0
  have hmle : m ≤ ρ := Nat.findGreatest_le ρ
  have hmlt : m < ρ := lt_of_le_of_ne hmle fun e => hfree (e ▸ hmP)
  have hmax : ¬ FreeFam (F := F) g (m + 1) :=
    Nat.findGreatest_is_greatest (Nat.lt_succ_self m) hmlt
  obtain ⟨t, ht⟩ := hmP
  set Z := Submodule.span F (Set.range t ∪ Set.range (g ∘ t)) with hZ
  have hZle : finrank F Z ≤ 2 * (ρ - 1) := by omega
  -- every vector outside `Z` is an eigenvector modulo `Z`
  have ex : ∀ u, u ∉ Z → ∃ c : F, g u - c • u ∈ Z := by
    intro u hu
    by_contra hc
    refine hmax (freeFam_succ ht hu fun hmem => hc ?_)
    obtain ⟨z, hz, y, hy, e⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    exact ⟨c, by rw [← e, add_sub_cancel_right]; exact hz⟩
  have g0 : g 0 = 0 := by simpa using hsm 0 0
  have gneg : ∀ u, g (-u) = -g u := fun u => by
    have := hadd u (-u)
    rw [add_neg_cancel, g0] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have gsub : ∀ u w, g (u - w) = g u - g w := fun u w => by
    rw [sub_eq_add_neg, hadd, gneg, ← sub_eq_add_neg]
  have key : ∀ u w, u ∉ Z → w ∉ Z ⊔ F ∙ u → ∀ cu cw : F, g u - cu • u ∈ Z → g w - cw • w ∈ Z →
      cu = cw := by
    intro u w hu hw cu cw hcu hcw
    have huw : u + w ∉ Z := fun h => hw (by
      have : w = (u + w) + (-1 : F) • u := by simp
      rw [this]
      exact Submodule.add_mem_sup h (Submodule.mem_span_singleton.2 ⟨-1, rfl⟩))
    obtain ⟨c', hc'⟩ := ex _ huw
    have e1 : (c' - cw) • w = ((g u - cu • u) + (g w - cw • w) - (g (u + w) - c' • (u + w))) +
        (cu - c') • u := by
      rw [hadd]; simp only [smul_add, sub_smul]; abel
    have h1 : (c' - cw) • w ∈ Z ⊔ F ∙ u := by
      rw [e1]
      exact Submodule.add_mem_sup (Z.sub_mem (Z.add_mem hcu hcw) hc')
        (Submodule.mem_span_singleton.2 ⟨_, rfl⟩)
    have h2 : c' = cw := by
      by_contra hne
      have hne' : c' - cw ≠ 0 := sub_ne_zero.2 hne
      refine hw ?_
      have := (Z ⊔ F ∙ u).smul_mem (c' - cw)⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at this
    have e2 : (c' - cu) • u = (g u - cu • u) + (g w - cw • w) - (g (u + w) - c' • (u + w)) := by
      rw [hadd, h2]; simp only [smul_add, sub_smul]; abel
    have h3 : (c' - cu) • u ∈ Z := by
      rw [e2]; exact Z.sub_mem (Z.add_mem hcu hcw) hc'
    have h4 : c' = cu := by
      by_contra hne
      have hne' : c' - cu ≠ 0 := sub_ne_zero.2 hne
      refine hu ?_
      have := Z.smul_mem (c' - cu)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at this
    rw [← h4, h2]
  have hZtop : Z ≠ ⊤ := fun h => by
    have := congrArg (fun W : Submodule F V => finrank F W) h
    simp only [finrank_top] at this
    omega
  obtain ⟨u0, hu0⟩ : ∃ u0, u0 ∉ Z := by
    by_contra h
    push Not at h
    exact hZtop (eq_top_iff.2 fun x _ => h x)
  obtain ⟨c0, hc0⟩ := ex u0 hu0
  have hall' : ∀ u, u ∉ Z → g u - c0 • u ∈ Z := by
    intro u hu
    obtain ⟨cu, hcu⟩ := ex u hu
    have hfin : finrank F ((Z ⊔ F ∙ u0) ⊔ F ∙ u : Submodule F V) < finrank F V := by
      have h1 := Submodule.finrank_add_le_finrank_add_finrank (Z ⊔ F ∙ u0) (F ∙ u)
      have h2 := Submodule.finrank_add_le_finrank_add_finrank Z (F ∙ u0)
      have h3 := finrank_span_singleton_le' (F := F) u0
      have h4 := finrank_span_singleton_le' (F := F) u
      omega
    obtain ⟨y, hy⟩ : ∃ y, y ∉ (Z ⊔ F ∙ u0) ⊔ F ∙ u := by
      by_contra h
      push Not at h
      have : ((Z ⊔ F ∙ u0) ⊔ F ∙ u : Submodule F V) = ⊤ := eq_top_iff.2 fun x _ => h x
      rw [this, finrank_top] at hfin
      exact lt_irrefl _ hfin
    have hy0 : y ∉ Z ⊔ F ∙ u0 := fun h => hy (Submodule.mem_sup_left h)
    have hyu : y ∉ Z ⊔ F ∙ u := fun h => hy (by
      have : Z ⊔ F ∙ u ≤ (Z ⊔ F ∙ u0) ⊔ F ∙ u :=
        sup_le (le_sup_of_le_left le_sup_left) le_sup_right
      exact this h)
    have hyZ : y ∉ Z := fun h => hy0 (Submodule.mem_sup_left h)
    obtain ⟨cy, hcy⟩ := ex y hyZ
    rw [key u0 y hu0 hy0 c0 cy hc0 hcy, ← key u y hu hyu cu cy hcu hcy]
    exact hcu
  have hall : ∀ u, g u - c0 • u ∈ Z := by
    intro u
    by_cases hu : u ∈ Z
    · have h1 : u + u0 ∉ Z := fun h => hu0 (by
        have := Z.sub_mem h hu
        rwa [add_sub_cancel_left] at this)
      have h2 := Z.sub_mem (hall' _ h1) hc0
      have e : g (u + u0) - c0 • (u + u0) - (g u0 - c0 • u0) = g u - c0 • u := by
        rw [hadd, smul_add]; abel
      rwa [e] at h2
    · exact hall' u hu
  refine ⟨c0, Z, hZle, hall, ?_⟩
  by_cases hc : c0 = 0
  · exact Or.inl hc
  · refine Or.inr fun x => ?_
    by_cases hx : x = 0
    · rw [hx, map_zero]
    · have h1 := hall (x • u0)
      rw [hsm] at h1
      have h2 := Z.smul_mem (σ x) hc0
      have h3 := Z.sub_mem h1 h2
      have e : σ x • g u0 - c0 • x • u0 - σ x • (g u0 - c0 • u0) = (σ x * c0 - c0 * x) • u0 := by
        simp only [smul_sub, sub_smul, mul_smul]; abel
      rw [e] at h3
      by_contra hne
      have hne' : σ x * c0 - c0 * x ≠ 0 := fun h => hne (by
        have : σ x * c0 = x * c0 := by rw [sub_eq_zero.1 h, mul_comm]
        exact mul_right_cancel₀ hc this)
      refine hu0 ?_
      have := Z.smul_mem (σ x * c0 - c0 * x)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at this

end Det

/-! ## A subspace of small codimension is the kernel of a few functionals -/

/-- A linear map of rank `≤ d` on `F^κ` vanishes on the common kernel of `d` functionals. -/
lemma exists_functionals {κ W : Type*} [Fintype κ] [DecidableEq κ] [AddCommGroup W] [Module F W]
    (R : (κ → F) →ₗ[F] W) {d : ℕ} (h : finrank F (LinearMap.range R) ≤ d) :
    ∃ Φ : Fin d → κ → F, ∀ u, (∀ a, Φ a ⬝ᵥ u = 0) → R u = 0 := by
  classical
  let b := Module.finBasis F (LinearMap.range R)
  let E : (Fin (finrank F (LinearMap.range R)) → F) →ₗ[F] (Fin d → F) :=
    Function.ExtendByZero.linearMap F (Fin.castLE h)
  let j : (κ → F) →ₗ[F] (Fin d → F) := E.comp (b.equivFun.toLinearMap.comp R.rangeRestrict)
  have hE : Function.Injective E := by
    intro x y hxy
    funext i
    have := congrFun hxy (Fin.castLE h i)
    change Function.extend (Fin.castLE h) x 0 _ = Function.extend (Fin.castLE h) y 0 _ at this
    rwa [(Fin.castLE_injective h).extend_apply, (Fin.castLE_injective h).extend_apply] at this
  refine ⟨fun a i => j (fun i' => if i = i' then 1 else 0) a, fun u hu => ?_⟩
  have hj : j u = 0 := by
    funext a
    have := hu a
    rw [LinearMap.pi_apply_eq_sum_univ j u]
    simp only [dotProduct] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    refine Eq.trans ?_ this
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h1 : b.equivFun (R.rangeRestrict u) = 0 := hE (by simpa [j] using hj)
  have h2 : R.rangeRestrict u = 0 := by simpa using h1
  simpa using congrArg Subtype.val h2

/-- A subspace of `F^κ` of codimension `≤ d` contains the common kernel of `d` functionals. -/
lemma exists_functionals_of_finrank {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : Submodule F (κ → F)) {d : ℕ} (h : Fintype.card κ ≤ finrank F K + d) :
    ∃ Φ : Fin d → κ → F, ∀ u, (∀ a, Φ a ⬝ᵥ u = 0) → u ∈ K := by
  have h1 := Submodule.finrank_quotient_add_finrank K
  have h2 : finrank F (κ → F) = Fintype.card κ := by simp
  have h3 : finrank F (LinearMap.range K.mkQ) ≤ d := by
    rw [Submodule.range_mkQ, finrank_top]; omega
  obtain ⟨Φ, hΦ⟩ := exists_functionals K.mkQ h3
  exact ⟨Φ, fun u hu => by simpa using hΦ u hu⟩

end VoleMole.Assumptions.SymmetryProbes
