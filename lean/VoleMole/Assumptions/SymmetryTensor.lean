import VoleMole.Assumptions.SymmetryProbes

/-!
# Theorem T3: the symmetries of the vinegar-oil tensor

WIP header.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Assumptions.SymmetryTensor

open VoleMole.Spec VoleMole.Spec.Pqov VoleMole.Arith VoleMole.Privacy VoleMole.Privacy.Moussaka
  VoleMole.Assumptions.SymmetryProbes Module Matrix

/-- Oil coordinates. -/
abbrev Oil := Fin 45 → GF256

/-- Targets. -/
abbrev Tgt := Fin 45 → GF256

/-! ## The bad events -/

/-- `L(w, ·)` vanishes on a subspace of codimension `≤ 17` of the oil coordinates, in a subspace
of codimension `≤ 4` of the functionals on targets, for some vinegar `w ≠ 0`. -/
def BoxV (S : Coef) : Prop :=
  ∃ w : Vin, w ≠ 0 ∧ ∃ (Φ : Fin 17 → Oil) (Ψ : Fin 4 → Tgt), ∀ x h,
    (∀ i, Φ i ⬝ᵥ x = 0) → (∀ i, Ψ i ⬝ᵥ h = 0) → tri S h w x = 0

/-- The same for an oil vector `w ≠ 0` and a subspace of codimension `≤ 17` of the vinegars. -/
def BoxO (S : Coef) : Prop :=
  ∃ w : Oil, w ≠ 0 ∧ ∃ (Φ : Fin 17 → Vin) (Ψ : Fin 4 → Tgt), ∀ v h,
    (∀ i, Φ i ⬝ᵥ v = 0) → (∀ i, Ψ i ⬝ᵥ h = 0) → tri S h v w = 0

/-- The same for a functional `w ≠ 0` on targets and subspaces of codimension `≤ 4`. -/
def BoxH (S : Coef) : Prop :=
  ∃ w : Tgt, w ≠ 0 ∧ ∃ (Φ : Fin 4 → Vin) (Ψ : Fin 4 → Oil), ∀ v x,
    (∀ i, Φ i ⬝ᵥ v = 0) → (∀ i, Ψ i ⬝ᵥ x = 0) → tri S w v x = 0

/-- Free probes on the vinegar leg, group case, `σ`-semilinear maps. -/
def FreeV (S : Coef) : Prop :=
  ∃ (σ : GF256 → GF256) (t a : Fin 3 → Vin) (G₂ T : Fin 45 → Fin 45 → GF256),
    LinearIndependent GF256 (Sum.elim t a) ∧
    Function.Surjective (fun x : Oil => Matrix.of G₂ *ᵥ fun i => σ (x i)) ∧
    ∀ j x, bil S (a j) (Matrix.of G₂ *ᵥ fun i => σ (x i)) =
      Matrix.of T *ᵥ fun k => σ (bil S (t j) x k)

/-- Free probes on the oil leg, group case. -/
def FreeO (S : Coef) : Prop :=
  ∃ (t a : Fin 3 → Oil) (G₁ : Fin 74 → Fin 74 → GF256) (T : Fin 45 → Fin 45 → GF256),
    LinearIndependent GF256 (Sum.elim t a) ∧
    Function.Surjective (fun v : Vin => Matrix.of G₁ *ᵥ v) ∧
    ∀ j v, bil S (Matrix.of G₁ *ᵥ v) (a j) = Matrix.of T *ᵥ bil S v (t j)

/-- Free probes on the target leg, group case. -/
def FreeH (S : Coef) : Prop :=
  ∃ (t a : Fin 3 → Tgt) (G₁ : Fin 74 → Fin 74 → GF256) (G₂ : Fin 45 → Fin 45 → GF256),
    LinearIndependent GF256 (Sum.elim t a) ∧
    ∀ j v x, tri S (a j) v x = tri S (t j) (Matrix.of G₁ *ᵥ v) (Matrix.of G₂ *ᵥ x)

/-- Free probes on the vinegar leg, infinitesimal case. -/
def FreeLV (S : Coef) : Prop :=
  ∃ (t a : Fin 3 → Vin) (G₂ Y : Fin 45 → Fin 45 → GF256),
    LinearIndependent GF256 (Sum.elim t a) ∧
    ∀ j x, bil S (a j) x = Matrix.of Y *ᵥ bil S (t j) x - bil S (t j) (Matrix.of G₂ *ᵥ x)

/-- Free probes on the oil leg, infinitesimal case. -/
def FreeLO (S : Coef) : Prop :=
  ∃ (t a : Fin 3 → Oil) (G₁ : Fin 74 → Fin 74 → GF256) (Y : Fin 45 → Fin 45 → GF256),
    LinearIndependent GF256 (Sum.elim t a) ∧
    ∀ j v, bil S v (a j) = Matrix.of Y *ᵥ bil S v (t j) - bil S (Matrix.of G₁ *ᵥ v) (t j)

/-- Free probes on the target leg, infinitesimal case. -/
def FreeLH (S : Coef) : Prop :=
  ∃ (t a : Fin 3 → Tgt) (G₁ : Fin 74 → Fin 74 → GF256) (G₂ : Fin 45 → Fin 45 → GF256),
    LinearIndependent GF256 (Sum.elim t a) ∧
    ∀ j v x, tri S (a j) v x =
      tri S (t j) (Matrix.of G₁ *ᵥ v) x + tri S (t j) v (Matrix.of G₂ *ᵥ x)

/-- `L(v, C v) = 0` for all `v`, for a matrix `C` of rank `≥ 18`. -/
def PairVO (S : Coef) : Prop :=
  ∃ C : Fin 45 → Fin 74 → GF256,
    (∃ v : Fin 9 ⊕ Fin 9 → Vin, LinearIndependent GF256 fun s => Matrix.of C *ᵥ v s) ∧
    ∀ v, bil S v (Matrix.of C *ᵥ v) = 0

/-- `L(C x, x) = 0` for all `x`, for a matrix `C` of rank `≥ 18`. -/
def PairOV (S : Coef) : Prop :=
  ∃ C : Fin 74 → Fin 45 → GF256,
    (∃ x : Fin 9 ⊕ Fin 9 → Oil, LinearIndependent GF256 fun s => Matrix.of C *ᵥ x s) ∧
    ∀ x, bil S (Matrix.of C *ᵥ x) x = 0

/-- **The good tensors**: none of the eleven events. -/
structure GoodS (S : Coef) : Prop where
  boxV : ¬ BoxV S
  boxO : ¬ BoxO S
  boxH : ¬ BoxH S
  freeV : ¬ FreeV S
  freeO : ¬ FreeO S
  freeH : ¬ FreeH S
  freeLV : ¬ FreeLV S
  freeLO : ¬ FreeLO S
  freeLH : ¬ FreeLH S
  pairVO : ¬ PairVO S
  pairOV : ¬ PairOV S

/-! ## Their probabilities -/

lemma card_gf : (Fintype.card GF256 : ℝ) = 256 := by rw [GF256.card_eq]; norm_num

theorem pr_boxH : pr Coef BoxH ≤ 1 / 256 ^ 2349 := by
  have h := pr_vanish (F := GF256) (ι₁ := Fin 45) (ι₂ := Fin 74) (ι₃ := Fin 45) 4 4 521 2349
    (by simp) (by simp)
  rw [card_gf] at h
  exact h

theorem pr_boxV : pr Coef BoxV ≤ 1 / 256 ^ 129 := by
  have h := pr_vanish (F := GF256) (ι₁ := Fin 74) (ι₂ := Fin 45) (ι₃ := Fin 45) 17 4 1019 129
    (by simp) (by simp)
  rw [card_gf, ← pr_equiv (rotEquiv (ι₁ := Fin 45) (ι₂ := Fin 74) (ι₃ := Fin 45))] at h
  refine (pr_mono fun S hS => ?_).trans h
  obtain ⟨w, hw, Φ, Ψ, hΦ⟩ := hS
  exact ⟨w, hw, Φ, Ψ, fun x y hx hy => by
    rw [show rotEquiv S = rot S from rfl, tri_rot]; exact hΦ x y hx hy⟩

theorem pr_boxO : pr Coef BoxO ≤ 1 / 256 ^ 854 := by
  have h := pr_vanish (F := GF256) (ι₁ := Fin 45) (ι₂ := Fin 74) (ι₃ := Fin 45) 17 4 1483 854
    (by simp) (by simp)
  rw [card_gf, ← pr_equiv (rotEquiv (ι₁ := Fin 45) (ι₂ := Fin 45) (ι₃ := Fin 74)),
    ← pr_equiv (swEquiv (ι₁ := Fin 45) (ι₂ := Fin 74) (ι₃ := Fin 45))] at h
  refine (pr_mono fun S hS => ?_).trans h
  obtain ⟨w, hw, Φ, Ψ, hΦ⟩ := hS
  exact ⟨w, hw, Φ, Ψ, fun x y hx hy => by
    rw [show rotEquiv (swEquiv S) = rot (sw S) from rfl, tri_rot, tri_sw]; exact hΦ x y hx hy⟩

lemma card_slice45 : (Fintype.card (Fin 45 → Fin 45 → GF256) : ℝ) =
    (Fintype.card GF256 : ℝ) ^ 2025 := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [← pow_mul]

lemma card_slice74 : (Fintype.card (Fin 74 → Fin 45 → GF256) : ℝ) =
    (Fintype.card GF256 : ℝ) ^ 3330 := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  push_cast
  rw [← pow_mul]

/-- Closes `Fintype.card W ≤ |GF256| ^ a` for a product of function types into `GF256`. -/
macro "card_le" : tactic => `(tactic|
  (simp only [Fintype.card_prod, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, ← pow_add]
   exact pow_le_pow_right₀ Fintype.card_pos
     (by first | (simp only [GF256.card_eq]; norm_num) | norm_num)))

theorem pr_freeV : pr Coef FreeV ≤ 1 / 256 ^ 1325 := by
  classical
  refine (pr_mono (Q := fun S => ∃ w : (GF256 → GF256) × (Fin 3 → Vin) × (Fin 3 → Vin) ×
      (Fin 45 → Fin 45 → GF256) × (Fin 45 → Fin 45 → GF256),
      (LinearIndependent GF256 (Sum.elim w.2.1 w.2.2.1) ∧
        Function.Surjective (fun x : Oil => Matrix.of w.2.2.2.1 *ᵥ fun i => w.1 (x i))) ∧
      ∀ j x, bil S (w.2.2.1 j) (Matrix.of w.2.2.2.1 *ᵥ fun i => w.1 (x i)) =
        Matrix.of w.2.2.2.2 *ᵥ fun k => w.1 (bil S (w.2.1 j) x k))
    fun S ⟨σ, t, a, G₂, T, h1, h2, h3⟩ => ⟨(σ, t, a, G₂, T), ⟨h1, h2⟩, h3⟩).trans ?_
  rw [← card_gf]
  refine pr_union Fintype.card_pos _ 4750 1325 (by card_le) fun w => ?_
  obtain ⟨σ, t, a, G₂, T⟩ := w
  by_cases hw : LinearIndependent GF256 (Sum.elim t a) ∧
      Function.Surjective (fun x : Oil => Matrix.of G₂ *ᵥ fun i => σ (x i))
  · let Rel : Fin 3 → (Fin 45 → Fin 45 → GF256) → (Fin 45 → Fin 45 → GF256) → Prop :=
      fun _ X Y => ∀ x : Oil, app Y (Matrix.of G₂ *ᵥ fun i => σ (x i)) =
        Matrix.of T *ᵥ fun k => σ (app X x k)
    have hRel : ∀ j X Y Y', Rel j X Y → Rel j X Y' → Y = Y' := by
      intro j X Y Y' h1 h2
      refine app_injective fun y => ?_
      obtain ⟨x, rfl⟩ := hw.2 y
      rw [h1 x, h2 x]
    have h := pr_free t a hw.1 Rel hRel
    rw [← pr_equiv (rotEquiv (ι₁ := Fin 45) (ι₂ := Fin 74) (ι₃ := Fin 45)), card_slice45,
      ← pow_mul] at h
    refine (pr_mono fun S hS j x => ?_).trans (h.trans (le_of_eq (by norm_num)))
    have := hS.2 j x
    rw [bil_eq_app_rot, bil_eq_app_rot] at this
    exact this
  · rw [pr_congr (Q := fun _ => False) fun S => ⟨fun h => hw h.1, False.elim⟩, pr_false]
    positivity

theorem pr_freeO : pr Coef FreeO ≤ 1 / 256 ^ 2219 := by
  classical
  refine (pr_mono (Q := fun S => ∃ w : (Fin 3 → Oil) × (Fin 3 → Oil) ×
      (Fin 74 → Fin 74 → GF256) × (Fin 45 → Fin 45 → GF256),
      (LinearIndependent GF256 (Sum.elim w.1 w.2.1) ∧
        Function.Surjective (fun v : Vin => Matrix.of w.2.2.1 *ᵥ v)) ∧
      ∀ j v, bil S (Matrix.of w.2.2.1 *ᵥ v) (w.2.1 j) = Matrix.of w.2.2.2 *ᵥ bil S v (w.1 j))
    fun S ⟨t, a, G₁, T, h1, h2, h3⟩ => ⟨(t, a, G₁, T), ⟨h1, h2⟩, h3⟩).trans ?_
  rw [← card_gf]
  refine pr_union Fintype.card_pos _ 7771 2219 (by card_le) fun w => ?_
  obtain ⟨t, a, G₁, T⟩ := w
  by_cases hw : LinearIndependent GF256 (Sum.elim t a) ∧
      Function.Surjective (fun v : Vin => Matrix.of G₁ *ᵥ v)
  · let Rel : Fin 3 → (Fin 74 → Fin 45 → GF256) → (Fin 74 → Fin 45 → GF256) → Prop :=
      fun _ X Y => ∀ v : Vin, app Y (Matrix.of G₁ *ᵥ v) = Matrix.of T *ᵥ app X v
    have hRel : ∀ j X Y Y', Rel j X Y → Rel j X Y' → Y = Y' := by
      intro j X Y Y' h1 h2
      refine app_injective fun y => ?_
      obtain ⟨x, rfl⟩ := hw.2 y
      rw [h1 x, h2 x]
    have h := pr_free t a hw.1 Rel hRel
    rw [← pr_equiv (rotEquiv (ι₁ := Fin 45) (ι₂ := Fin 45) (ι₃ := Fin 74)),
      ← pr_equiv (swEquiv (ι₁ := Fin 45) (ι₂ := Fin 74) (ι₃ := Fin 45)), card_slice74,
      ← pow_mul] at h
    refine (pr_mono fun S hS j v => ?_).trans (h.trans (le_of_eq (by norm_num)))
    have := hS.2 j v
    rw [bil_eq_app_rot_sw, bil_eq_app_rot_sw] at this
    exact this
  · rw [pr_congr (Q := fun _ => False) fun S => ⟨fun h => hw h.1, False.elim⟩, pr_false]
    positivity

theorem pr_freeH : pr Coef FreeH ≤ 1 / 256 ^ 2219 := by
  classical
  refine (pr_mono (Q := fun S => ∃ w : (Fin 3 → Tgt) × (Fin 3 → Tgt) ×
      (Fin 74 → Fin 74 → GF256) × (Fin 45 → Fin 45 → GF256),
      LinearIndependent GF256 (Sum.elim w.1 w.2.1) ∧
      ∀ j v x, tri S (w.2.1 j) v x =
        tri S (w.1 j) (Matrix.of w.2.2.1 *ᵥ v) (Matrix.of w.2.2.2 *ᵥ x))
    fun S ⟨t, a, G₁, G₂, h1, h3⟩ => ⟨(t, a, G₁, G₂), h1, h3⟩).trans ?_
  rw [← card_gf]
  refine pr_union Fintype.card_pos _ 7771 2219 (by card_le) fun w => ?_
  obtain ⟨t, a, G₁, G₂⟩ := w
  by_cases hw : LinearIndependent GF256 (Sum.elim t a)
  · let Rel : Fin 3 → (Fin 74 → Fin 45 → GF256) → (Fin 74 → Fin 45 → GF256) → Prop :=
      fun _ X Y => ∀ (v : Vin) (x : Oil), app₂ Y v x =
        app₂ X (Matrix.of G₁ *ᵥ v) (Matrix.of G₂ *ᵥ x)
    have hRel : ∀ j X Y Y', Rel j X Y → Rel j X Y' → Y = Y' := by
      intro j X Y Y' h1 h2
      exact app₂_injective fun v x => by rw [h1 v x, h2 v x]
    have h := pr_free t a hw Rel hRel
    rw [card_slice74, ← pow_mul] at h
    exact (pr_mono fun S hS j v x => hS.2 j v x).trans (h.trans (le_of_eq (by norm_num)))
  · rw [pr_congr (Q := fun _ => False) fun S => ⟨fun h => hw h.1, False.elim⟩, pr_false]
    positivity

theorem pr_freeLV : pr Coef FreeLV ≤ 1 / 256 ^ 1581 := by
  classical
  refine (pr_mono (Q := fun S => ∃ w : (Fin 3 → Vin) × (Fin 3 → Vin) ×
      (Fin 45 → Fin 45 → GF256) × (Fin 45 → Fin 45 → GF256),
      LinearIndependent GF256 (Sum.elim w.1 w.2.1) ∧
      ∀ j x, bil S (w.2.1 j) x = Matrix.of w.2.2.2 *ᵥ bil S (w.1 j) x -
        bil S (w.1 j) (Matrix.of w.2.2.1 *ᵥ x))
    fun S ⟨t, a, G₂, Y, h1, h3⟩ => ⟨(t, a, G₂, Y), h1, h3⟩).trans ?_
  rw [← card_gf]
  refine pr_union Fintype.card_pos _ 4494 1581 (by card_le) fun w => ?_
  obtain ⟨t, a, G₂, Y⟩ := w
  by_cases hw : LinearIndependent GF256 (Sum.elim t a)
  · let Rel : Fin 3 → (Fin 45 → Fin 45 → GF256) → (Fin 45 → Fin 45 → GF256) → Prop :=
      fun _ X Z => ∀ x : Oil, app Z x = Matrix.of Y *ᵥ app X x - app X (Matrix.of G₂ *ᵥ x)
    have hRel : ∀ j X Z Z', Rel j X Z → Rel j X Z' → Z = Z' := by
      intro j X Z Z' h1 h2
      exact app_injective fun x => by rw [h1 x, h2 x]
    have h := pr_free t a hw Rel hRel
    rw [← pr_equiv (rotEquiv (ι₁ := Fin 45) (ι₂ := Fin 74) (ι₃ := Fin 45)), card_slice45,
      ← pow_mul] at h
    refine (pr_mono fun S hS j x => ?_).trans (h.trans (le_of_eq (by norm_num)))
    have := hS.2 j x
    rw [bil_eq_app_rot, bil_eq_app_rot, bil_eq_app_rot] at this
    exact this
  · rw [pr_congr (Q := fun _ => False) fun S => ⟨fun h => hw h.1, False.elim⟩, pr_false]
    positivity

theorem pr_freeLO : pr Coef FreeLO ≤ 1 / 256 ^ 2219 := by
  classical
  refine (pr_mono (Q := fun S => ∃ w : (Fin 3 → Oil) × (Fin 3 → Oil) ×
      (Fin 74 → Fin 74 → GF256) × (Fin 45 → Fin 45 → GF256),
      LinearIndependent GF256 (Sum.elim w.1 w.2.1) ∧
      ∀ j v, bil S v (w.2.1 j) = Matrix.of w.2.2.2 *ᵥ bil S v (w.1 j) -
        bil S (Matrix.of w.2.2.1 *ᵥ v) (w.1 j))
    fun S ⟨t, a, G₁, Y, h1, h3⟩ => ⟨(t, a, G₁, Y), h1, h3⟩).trans ?_
  rw [← card_gf]
  refine pr_union Fintype.card_pos _ 7771 2219 (by card_le) fun w => ?_
  obtain ⟨t, a, G₁, Y⟩ := w
  by_cases hw : LinearIndependent GF256 (Sum.elim t a)
  · let Rel : Fin 3 → (Fin 74 → Fin 45 → GF256) → (Fin 74 → Fin 45 → GF256) → Prop :=
      fun _ X Z => ∀ v : Vin, app Z v = Matrix.of Y *ᵥ app X v - app X (Matrix.of G₁ *ᵥ v)
    have hRel : ∀ j X Z Z', Rel j X Z → Rel j X Z' → Z = Z' := by
      intro j X Z Z' h1 h2
      exact app_injective fun x => by rw [h1 x, h2 x]
    have h := pr_free t a hw Rel hRel
    rw [← pr_equiv (rotEquiv (ι₁ := Fin 45) (ι₂ := Fin 45) (ι₃ := Fin 74)),
      ← pr_equiv (swEquiv (ι₁ := Fin 45) (ι₂ := Fin 74) (ι₃ := Fin 45)), card_slice74,
      ← pow_mul] at h
    refine (pr_mono fun S hS j v => ?_).trans (h.trans (le_of_eq (by norm_num)))
    have := hS.2 j v
    rw [bil_eq_app_rot_sw, bil_eq_app_rot_sw, bil_eq_app_rot_sw] at this
    exact this
  · rw [pr_congr (Q := fun _ => False) fun S => ⟨fun h => hw h.1, False.elim⟩, pr_false]
    positivity

theorem pr_freeLH : pr Coef FreeLH ≤ 1 / 256 ^ 2219 := by
  classical
  refine (pr_mono (Q := fun S => ∃ w : (Fin 3 → Tgt) × (Fin 3 → Tgt) ×
      (Fin 74 → Fin 74 → GF256) × (Fin 45 → Fin 45 → GF256),
      LinearIndependent GF256 (Sum.elim w.1 w.2.1) ∧
      ∀ j v x, tri S (w.2.1 j) v x =
        tri S (w.1 j) (Matrix.of w.2.2.1 *ᵥ v) x + tri S (w.1 j) v (Matrix.of w.2.2.2 *ᵥ x))
    fun S ⟨t, a, G₁, G₂, h1, h3⟩ => ⟨(t, a, G₁, G₂), h1, h3⟩).trans ?_
  rw [← card_gf]
  refine pr_union Fintype.card_pos _ 7771 2219 (by card_le) fun w => ?_
  obtain ⟨t, a, G₁, G₂⟩ := w
  by_cases hw : LinearIndependent GF256 (Sum.elim t a)
  · let Rel : Fin 3 → (Fin 74 → Fin 45 → GF256) → (Fin 74 → Fin 45 → GF256) → Prop :=
      fun _ X Y => ∀ (v : Vin) (x : Oil), app₂ Y v x =
        app₂ X (Matrix.of G₁ *ᵥ v) x + app₂ X v (Matrix.of G₂ *ᵥ x)
    have hRel : ∀ j X Y Y', Rel j X Y → Rel j X Y' → Y = Y' := by
      intro j X Y Y' h1 h2
      exact app₂_injective fun v x => by rw [h1 v x, h2 v x]
    have h := pr_free t a hw Rel hRel
    rw [card_slice74, ← pow_mul] at h
    exact (pr_mono fun S hS j v x => hS.2 j v x).trans (h.trans (le_of_eq (by norm_num)))
  · rw [pr_congr (Q := fun _ => False) fun S => ⟨fun h => hw h.1, False.elim⟩, pr_false]
    positivity

theorem pr_pairVO : pr Coef PairVO ≤ 1 / 256 ^ 315 := by
  classical
  rw [← card_gf]
  refine pr_union Fintype.card_pos _ 3330 315 (by card_le) fun C => ?_
  by_cases hw : ∃ v : Fin 9 ⊕ Fin 9 → Vin, LinearIndependent GF256 fun s => Matrix.of C *ᵥ v s
  · obtain ⟨V, hV⟩ := hw
    have hV' : LinearIndependent GF256 V :=
      LinearIndependent.of_comp (Matrix.mulVecLin (Matrix.of C)) hV
    have h := pr_paired (F := GF256) (ι₁ := Fin 45) (V ∘ Sum.inl) (V ∘ Sum.inr)
      (fun i => Matrix.of C *ᵥ V (Sum.inl i)) (fun j => Matrix.of C *ᵥ V (Sum.inr j))
      (by rw [Sum.elim_comp_inl_inr]; exact hV')
      (by
        have : Sum.elim (fun i => Matrix.of C *ᵥ V (Sum.inl i))
            (fun j => Matrix.of C *ᵥ V (Sum.inr j)) = fun s => Matrix.of C *ᵥ V s := by
          funext s; cases s <;> rfl
        rw [this]; exact hV)
    simp only [Fintype.card_fin] at h
    refine (pr_mono fun S hS i j => ?_).trans (h.trans (le_of_eq (by norm_num)))
    have h1 := hS.2 (V (Sum.inl i) + V (Sum.inr j))
    rw [Matrix.mulVec_add, bil_add_left, bil_add_right, bil_add_right, hS.2, hS.2, zero_add,
      add_zero] at h1
    exact h1
  · rw [pr_congr (Q := fun _ => False) fun S => ⟨fun h => hw h.1, False.elim⟩, pr_false]
    positivity

theorem pr_pairOV : pr Coef PairOV ≤ 1 / 256 ^ 315 := by
  classical
  rw [← card_gf]
  refine pr_union Fintype.card_pos _ 3330 315 (by card_le) fun C => ?_
  by_cases hw : ∃ x : Fin 9 ⊕ Fin 9 → Oil, LinearIndependent GF256 fun s => Matrix.of C *ᵥ x s
  · obtain ⟨X, hX⟩ := hw
    have hX' : LinearIndependent GF256 X :=
      LinearIndependent.of_comp (Matrix.mulVecLin (Matrix.of C)) hX
    have h := pr_paired (F := GF256) (ι₁ := Fin 45)
      (fun i => Matrix.of C *ᵥ X (Sum.inl i)) (fun j => Matrix.of C *ᵥ X (Sum.inr j))
      (X ∘ Sum.inl) (X ∘ Sum.inr)
      (by
        have : Sum.elim (fun i => Matrix.of C *ᵥ X (Sum.inl i))
            (fun j => Matrix.of C *ᵥ X (Sum.inr j)) = fun s => Matrix.of C *ᵥ X s := by
          funext s; cases s <;> rfl
        rw [this]; exact hX)
      (by rw [Sum.elim_comp_inl_inr]; exact hX')
    simp only [Fintype.card_fin] at h
    refine (pr_mono fun S hS i j => ?_).trans (h.trans (le_of_eq (by norm_num)))
    have h1 := hS.2 (X (Sum.inl i) + X (Sum.inr j))
    rw [Matrix.mulVec_add, bil_add_left, bil_add_right, bil_add_right, hS.2, hS.2, zero_add,
      add_zero] at h1
    exact h1
  · rw [pr_congr (Q := fun _ => False) fun S => ⟨fun h => hw h.1, False.elim⟩, pr_false]
    positivity

lemma le_129 {b : ℕ} (hb : 129 ≤ b) {x : ℝ} (h : x ≤ 1 / 256 ^ b) : x ≤ 1 / 256 ^ 129 :=
  h.trans (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hb))

/-- **A uniform tensor is good** except with probability `11·256^{−129}`. -/
theorem pr_not_goodS : pr Coef (fun S => ¬ GoodS S) ≤ 11 / 256 ^ 129 := by
  refine (pr_mono (Q := fun S => BoxV S ∨ BoxO S ∨ BoxH S ∨ FreeV S ∨ FreeO S ∨ FreeH S ∨
      FreeLV S ∨ FreeLO S ∨ FreeLH S ∨ PairVO S ∨ PairOV S) fun S hS => ?_).trans ?_
  · by_contra hc
    simp only [not_or] at hc
    exact hS ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.2.2.2.2⟩
  · have h1 := le_129 (by norm_num) pr_boxV
    have h2 := le_129 (by norm_num) pr_boxO
    have h3 := le_129 (by norm_num) pr_boxH
    have h4 := le_129 (by norm_num) pr_freeV
    have h5 := le_129 (by norm_num) pr_freeO
    have h6 := le_129 (by norm_num) pr_freeH
    have h7 := le_129 (by norm_num) pr_freeLV
    have h8 := le_129 (by norm_num) pr_freeLO
    have h9 := le_129 (by norm_num) pr_freeLH
    have h10 := le_129 (by norm_num) pr_pairVO
    have h11 := le_129 (by norm_num) pr_pairOV
    refine (pr_or_le _ _).trans ?_
    refine (add_le_add h1 ((pr_or_le _ _).trans (add_le_add h2 ((pr_or_le _ _).trans
      (add_le_add h3 ((pr_or_le _ _).trans (add_le_add h4 ((pr_or_le _ _).trans
      (add_le_add h5 ((pr_or_le _ _).trans (add_le_add h6 ((pr_or_le _ _).trans
      (add_le_add h7 ((pr_or_le _ _).trans (add_le_add h8 ((pr_or_le _ _).trans
      (add_le_add h9 ((pr_or_le _ _).trans (add_le_add h10 h11))))))))))))))))))).trans ?_
    rw [show (11 : ℝ) / 256 ^ 129 = 11 * (1 / 256 ^ 129) by ring]
    generalize (1 : ℝ) / 256 ^ 129 = e
    exact le_of_eq (by ring)

/-! ## The symmetries of a good tensor -/

/-- A map that is additive and homogeneous, as a linear map. -/
def linOf {κ κ' : Type*} (g : (κ → GF256) → κ' → GF256) (ha : ∀ u w, g (u + w) = g u + g w)
    (hs : ∀ (c : GF256) u, g (c • u) = c • g u) : (κ → GF256) →ₗ[GF256] (κ' → GF256) where
  toFun := g
  map_add' := ha
  map_smul' c u := by simpa using hs c u

lemma toMatrix'_mulVec' {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    (G : (κ → GF256) →ₗ[GF256] (κ' → GF256)) (v : κ → GF256) :
    Matrix.of (fun i j => LinearMap.toMatrix' G i j) *ᵥ v = G v := by
  have : Matrix.of (fun i j => LinearMap.toMatrix' G i j) = LinearMap.toMatrix' G := rfl
  rw [this, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

/-- A `σ`-semilinear map is a matrix applied after `σ` on the coordinates. -/
lemma exists_matrix_semilin {κ κ' : Type*} [Fintype κ] [DecidableEq κ] (σ : GF256 →+* GF256)
    (g : (κ → GF256) → κ' → GF256) (hadd : ∀ u w, g (u + w) = g u + g w)
    (hsm : ∀ (c : GF256) u, g (c • u) = σ c • g u) :
    ∃ M : κ' → κ → GF256, ∀ x, g x = Matrix.of M *ᵥ fun i => σ (x i) := by
  have hbij : Function.Bijective σ := ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  let e := RingEquiv.ofBijective σ hbij
  have he : ∀ c, σ (e.symm c) = c := fun c => e.apply_symm_apply c
  let glin : (κ → GF256) →ₗ[GF256] (κ' → GF256) :=
    { toFun := fun y => g (fun i => e.symm (y i))
      map_add' := fun y z => by
        rw [← hadd]; congr 1; funext i; simp
      map_smul' := fun c y => by
        have : (fun i => e.symm ((c • y) i)) = e.symm c • fun i => e.symm (y i) := by
          funext i; simp
        rw [this, hsm, he]; rfl }
  refine ⟨fun i j => LinearMap.toMatrix' glin i j, fun x => ?_⟩
  rw [toMatrix'_mulVec']
  show g x = g (fun i => e.symm (σ (x i)))
  congr 1
  funext i
  exact (e.symm_apply_apply (x i)).symm

lemma finrank_vin : finrank GF256 Vin = 74 := by simp
lemma finrank_oil : finrank GF256 Oil = 45 := by simp

/-- A surjective linear map of `F^κ` that is `c` on the kernel of fewer than `|κ|` functionals
has `c ≠ 0`. -/
lemma scalar_ne_zero {κ : Type*} [Fintype κ] [DecidableEq κ] {g : (κ → GF256) → κ → GF256}
    (hg : Function.Surjective g) {c : GF256} {d : ℕ} (hd : d < Fintype.card κ)
    {Φ : Fin d → κ → GF256} (hΦ : ∀ u, (∀ a, Φ a ⬝ᵥ u = 0) → g u = c • u)
    (h0 : g 0 = 0) : c ≠ 0 := by
  rintro rfl
  obtain ⟨u, hu, hk⟩ := exists_ker_ne_zero Φ hd
  have hinj := Finite.injective_iff_surjective.2 hg
  exact hu (hinj (by rw [hΦ u hk, h0, zero_smul]))

/-- **The symmetries of a good tensor are scalar** (group case, with `σ`-semilinear maps). If
`L(g₁ v, g₂ x) = T(L(v, x))` with `g₁`, `g₂`, `T` additive and `σ`-semilinear and `g₁`, `g₂`
onto, then `σ` is the identity, `g₁ = α`, `g₂ = β` and `T = αβ`. -/
theorem tensor_group {S : Coef} (hS : GoodS S) (σ : GF256 →+* GF256) (g₁ : Vin → Vin)
    (g₂ : Oil → Oil) (T : Tgt → Tgt)
    (h1a : ∀ u w, g₁ (u + w) = g₁ u + g₁ w) (h1s : ∀ (c : GF256) u, g₁ (c • u) = σ c • g₁ u)
    (h2a : ∀ u w, g₂ (u + w) = g₂ u + g₂ w) (h2s : ∀ (c : GF256) u, g₂ (c • u) = σ c • g₂ u)
    (hTa : ∀ u w, T (u + w) = T u + T w) (hTs : ∀ (c : GF256) u, T (c • u) = σ c • T u)
    (h1b : Function.Surjective g₁) (h2b : Function.Surjective g₂)
    (h : ∀ v x, bil S (g₁ v) (g₂ x) = T (bil S v x)) :
    (∀ c, σ c = c) ∧ ∃ α β : GF256, α ≠ 0 ∧ β ≠ 0 ∧ (∀ v, g₁ v = α • v) ∧
      (∀ x, g₂ x = β • x) ∧ ∀ y, T y = (α * β) • y := by
  classical
  obtain ⟨M₂, hM₂⟩ := exists_matrix_semilin σ g₂ h2a h2s
  obtain ⟨MT, hMT⟩ := exists_matrix_semilin σ T hTa hTs
  have hf1 : ¬ FreeFam (F := GF256) g₁ 3 := by
    rintro ⟨t, ht⟩
    refine hS.freeV ⟨σ, t, g₁ ∘ t, M₂, MT, freeFam_indep ht, ?_, fun j x => ?_⟩
    · intro y
      obtain ⟨x, rfl⟩ := h2b y
      exact ⟨x, (hM₂ x).symm⟩
    · rw [← hM₂, ← hMT]
      exact h (t j) x
  obtain ⟨c₀, Z₁, hZ₁, hall₁, hc₀⟩ := near_scalar σ g₁ h1a h1s
    (by rw [finrank_vin]; norm_num) hf1
  have hσ : ∀ x, σ x = x := by
    rcases hc₀ with h0 | h0
    · exfalso
      have : Z₁ = ⊤ := eq_top_iff.2 fun y _ => by
        obtain ⟨u, rfl⟩ := h1b y
        simpa [h0] using hall₁ u
      have hfin : finrank GF256 Z₁ = 74 := by rw [this, finrank_top, finrank_vin]
      omega
    · exact h0
  let G₁ := linOf g₁ h1a fun c u => by rw [h1s, hσ]
  let G₂ := linOf g₂ h2a fun c u => by rw [h2s, hσ]
  let TL := linOf T hTa fun c u => by rw [hTs, hσ]
  let G₃ : Tgt →ₗ[GF256] Tgt := Matrix.mulVecLin (LinearMap.toMatrix' TL)ᵀ
  have hG₃ : ∀ (h : Tgt) (y : Tgt), G₃ h ⬝ᵥ y = h ⬝ᵥ T y := by
    intro h y
    show (LinearMap.toMatrix' TL)ᵀ *ᵥ h ⬝ᵥ y = h ⬝ᵥ TL y
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, ← Matrix.toLin'_apply,
      Matrix.toLin'_toMatrix']
  have key : ∀ (h : Tgt) (v : Vin) (x : Oil), tri S (G₃ h) v x = tri S h (g₁ v) (g₂ x) := by
    intro h' v x
    rw [tri_eq_dot, tri_eq_dot, hG₃, h v x]
  have hf2 : ¬ FreeFam (F := GF256) (⇑G₂) 3 := by
    rintro ⟨t, ht⟩
    refine hS.freeO ⟨t, g₂ ∘ t, fun i j => LinearMap.toMatrix' G₁ i j,
      fun i j => LinearMap.toMatrix' TL i j, freeFam_indep ht, ?_, fun j v => ?_⟩
    · intro y
      obtain ⟨x, rfl⟩ := h1b y
      exact ⟨x, toMatrix'_mulVec' G₁ x⟩
    · rw [toMatrix'_mulVec', toMatrix'_mulVec']
      exact h v (t j)
  have hf3 : ¬ FreeFam (F := GF256) (⇑G₃) 3 := by
    rintro ⟨t, ht⟩
    refine hS.freeH ⟨t, G₃ ∘ t, fun i j => LinearMap.toMatrix' G₁ i j,
      fun i j => LinearMap.toMatrix' G₂ i j, freeFam_indep ht, fun j v x => ?_⟩
    rw [toMatrix'_mulVec', toMatrix'_mulVec']
    exact key (t j) v x
  obtain ⟨c₁, hc₁⟩ := near_scalar_lin G₁ (by simp) hf1
  obtain ⟨c₂, hc₂⟩ := near_scalar_lin G₂ (by simp) hf2
  obtain ⟨c₃, hc₃⟩ := near_scalar_lin G₃ (by simp) hf3
  obtain ⟨Φ₁, hΦ₁⟩ := hc₁ 4 (by norm_num)
  obtain ⟨Φ₁', hΦ₁'⟩ := hc₁ 17 (by norm_num)
  obtain ⟨Φ₂, hΦ₂⟩ := hc₂ 4 (by norm_num)
  obtain ⟨Φ₂', hΦ₂'⟩ := hc₂ 17 (by norm_num)
  obtain ⟨Φ₃, hΦ₃⟩ := hc₃ 4 (by norm_num)
  have hc₁0 : c₁ ≠ 0 := scalar_ne_zero h1b (by simp) hΦ₁ (map_zero G₁)
  have hc₂0 : c₂ ≠ 0 := scalar_ne_zero h2b (by simp) hΦ₂ (map_zero G₂)
  -- the three scalars are related
  have hc : c₃ = c₁ * c₂ := by
    by_contra hne
    obtain ⟨h0, hh0, hk0⟩ := exists_ker_ne_zero Φ₃ (by simp)
    refine hS.boxH ⟨h0, hh0, Φ₁, Φ₂, fun v x hv hx => ?_⟩
    have e := key h0 v x
    rw [hΦ₃ h0 hk0, show g₁ v = c₁ • v from hΦ₁ v hv, show g₂ x = c₂ • x from hΦ₂ x hx,
      tri_smul₁, tri_smul₂, tri_smul₃] at e
    have e' : (c₃ - c₁ * c₂) * tri S h0 v x = 0 := by rw [sub_mul, e]; ring
    exact (mul_eq_zero.1 e').resolve_left (sub_ne_zero.2 hne)
  have h1 : ∀ v, g₁ v = c₁ • v := by
    intro u
    by_contra hne
    refine hS.boxV ⟨g₁ u - c₁ • u, sub_ne_zero.2 hne, Φ₂', Φ₃, fun x h' hx hh => ?_⟩
    have e := key h' u x
    rw [hΦ₃ h' hh, show g₂ x = c₂ • x from hΦ₂' x hx,
      show g₁ u = c₁ • u + (g₁ u - c₁ • u) by abel, tri_smul₁, tri_smul₃, tri_add₂, tri_smul₂,
      hc] at e
    have e' : c₂ * tri S h' (g₁ u - c₁ • u) x = 0 := by linear_combination -e
    exact (mul_eq_zero.1 e').resolve_left hc₂0
  have h2 : ∀ x, g₂ x = c₂ • x := by
    intro u
    by_contra hne
    refine hS.boxO ⟨g₂ u - c₂ • u, sub_ne_zero.2 hne, Φ₁', Φ₃, fun v h' hv hh => ?_⟩
    have e := key h' v u
    rw [hΦ₃ h' hh, show g₁ v = c₁ • v from hΦ₁' v hv,
      show g₂ u = c₂ • u + (g₂ u - c₂ • u) by abel, tri_smul₁, tri_smul₂, tri_add₃, tri_smul₃,
      hc] at e
    have e' : c₁ * tri S h' v (g₂ u - c₂ • u) = 0 := by linear_combination -e
    exact (mul_eq_zero.1 e').resolve_left hc₁0
  have h3 : ∀ h', G₃ h' = c₃ • h' := by
    intro u
    by_contra hne
    refine hS.boxH ⟨G₃ u - c₃ • u, sub_ne_zero.2 hne, Φ₁, Φ₂, fun v x hv hx => ?_⟩
    have e := key u v x
    rw [show g₁ v = c₁ • v from hΦ₁ v hv, show g₂ x = c₂ • x from hΦ₂ x hx,
      show G₃ u = c₃ • u + (G₃ u - c₃ • u) by abel, tri_add₁, tri_smul₁, tri_smul₂, tri_smul₃,
      hc] at e
    rw [hc]
    linear_combination e
  refine ⟨hσ, c₁, c₂, hc₁0, hc₂0, h1, h2, fun y => ?_⟩
  funext k
  have e := hG₃ (Pi.single k 1) y
  rw [h3, smul_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul, hc] at e
  rw [← e]
  rfl

/-- **The infinitesimal symmetries of a good tensor are scalar.** If
`L(X₁ v, x) + L(v, X₂ x) = Y(L(v, x))` with `X₁`, `X₂`, `Y` linear, then `X₁ = α`, `X₂ = β` and
`Y = α + β`. -/
theorem tensor_lie {S : Coef} (hS : GoodS S) (X₁ : Vin →ₗ[GF256] Vin) (X₂ : Oil →ₗ[GF256] Oil)
    (Y : Tgt →ₗ[GF256] Tgt) (h : ∀ v x, bil S (X₁ v) x + bil S v (X₂ x) = Y (bil S v x)) :
    ∃ α β : GF256, (∀ v, X₁ v = α • v) ∧ (∀ x, X₂ x = β • x) ∧ ∀ y, Y y = (α + β) • y := by
  classical
  let G₃ : Tgt →ₗ[GF256] Tgt := Matrix.mulVecLin (LinearMap.toMatrix' Y)ᵀ
  have hG₃ : ∀ (h : Tgt) (y : Tgt), G₃ h ⬝ᵥ y = h ⬝ᵥ Y y := by
    intro h y
    show (LinearMap.toMatrix' Y)ᵀ *ᵥ h ⬝ᵥ y = h ⬝ᵥ Y y
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, ← Matrix.toLin'_apply,
      Matrix.toLin'_toMatrix']
  have key : ∀ (h : Tgt) (v : Vin) (x : Oil),
      tri S (G₃ h) v x = tri S h (X₁ v) x + tri S h v (X₂ x) := by
    intro h' v x
    rw [tri_eq_dot, tri_eq_dot, tri_eq_dot, hG₃, ← h v x, dotProduct_add]
  have hf1 : ¬ FreeFam (F := GF256) (⇑X₁) 3 := by
    rintro ⟨t, ht⟩
    refine hS.freeLV ⟨t, X₁ ∘ t, fun i j => LinearMap.toMatrix' X₂ i j,
      fun i j => LinearMap.toMatrix' Y i j, freeFam_indep ht, fun j x => ?_⟩
    rw [toMatrix'_mulVec', toMatrix'_mulVec']
    exact eq_sub_of_add_eq (h (t j) x)
  have hf2 : ¬ FreeFam (F := GF256) (⇑X₂) 3 := by
    rintro ⟨t, ht⟩
    refine hS.freeLO ⟨t, X₂ ∘ t, fun i j => LinearMap.toMatrix' X₁ i j,
      fun i j => LinearMap.toMatrix' Y i j, freeFam_indep ht, fun j v => ?_⟩
    rw [toMatrix'_mulVec', toMatrix'_mulVec']
    exact eq_sub_of_add_eq' (h v (t j))
  have hf3 : ¬ FreeFam (F := GF256) (⇑G₃) 3 := by
    rintro ⟨t, ht⟩
    refine hS.freeLH ⟨t, G₃ ∘ t, fun i j => LinearMap.toMatrix' X₁ i j,
      fun i j => LinearMap.toMatrix' X₂ i j, freeFam_indep ht, fun j v x => ?_⟩
    rw [toMatrix'_mulVec', toMatrix'_mulVec']
    exact key (t j) v x
  obtain ⟨c₁, hc₁⟩ := near_scalar_lin X₁ (by simp) hf1
  obtain ⟨c₂, hc₂⟩ := near_scalar_lin X₂ (by simp) hf2
  obtain ⟨c₃, hc₃⟩ := near_scalar_lin G₃ (by simp) hf3
  obtain ⟨Φ₁, hΦ₁⟩ := hc₁ 4 (by norm_num)
  obtain ⟨Φ₁', hΦ₁'⟩ := hc₁ 17 (by norm_num)
  obtain ⟨Φ₂, hΦ₂⟩ := hc₂ 4 (by norm_num)
  obtain ⟨Φ₂', hΦ₂'⟩ := hc₂ 17 (by norm_num)
  obtain ⟨Φ₃, hΦ₃⟩ := hc₃ 4 (by norm_num)
  have hc : c₃ = c₁ + c₂ := by
    by_contra hne
    obtain ⟨h0, hh0, hk0⟩ := exists_ker_ne_zero Φ₃ (by simp)
    refine hS.boxH ⟨h0, hh0, Φ₁, Φ₂, fun v x hv hx => ?_⟩
    have e := key h0 v x
    rw [hΦ₃ h0 hk0, hΦ₁ v hv, hΦ₂ x hx, tri_smul₁, tri_smul₂, tri_smul₃] at e
    have e' : (c₃ - (c₁ + c₂)) * tri S h0 v x = 0 := by rw [sub_mul, e]; ring
    exact (mul_eq_zero.1 e').resolve_left (sub_ne_zero.2 hne)
  have h1 : ∀ v, X₁ v = c₁ • v := by
    intro u
    by_contra hne
    refine hS.boxV ⟨X₁ u - c₁ • u, sub_ne_zero.2 hne, Φ₂', Φ₃, fun x h' hx hh => ?_⟩
    have e := key h' u x
    rw [hΦ₃ h' hh, hΦ₂' x hx, show X₁ u = c₁ • u + (X₁ u - c₁ • u) by abel, tri_smul₁,
      tri_smul₃, tri_add₂, tri_smul₂, hc] at e
    linear_combination -e
  have h2 : ∀ x, X₂ x = c₂ • x := by
    intro u
    by_contra hne
    refine hS.boxO ⟨X₂ u - c₂ • u, sub_ne_zero.2 hne, Φ₁', Φ₃, fun v h' hv hh => ?_⟩
    have e := key h' v u
    rw [hΦ₃ h' hh, hΦ₁' v hv, show X₂ u = c₂ • u + (X₂ u - c₂ • u) by abel, tri_smul₁,
      tri_smul₂, tri_add₃, tri_smul₃, hc] at e
    linear_combination -e
  have h3 : ∀ h', G₃ h' = c₃ • h' := by
    intro u
    by_contra hne
    refine hS.boxH ⟨G₃ u - c₃ • u, sub_ne_zero.2 hne, Φ₁, Φ₂, fun v x hv hx => ?_⟩
    have e := key u v x
    rw [hΦ₁ v hv, hΦ₂ x hx, show G₃ u = c₃ • u + (G₃ u - c₃ • u) by abel, tri_add₁, tri_smul₁,
      tri_smul₂, tri_smul₃, hc] at e
    rw [hc]
    linear_combination e
  refine ⟨c₁, c₂, h1, h2, fun y => ?_⟩
  funext k
  have e := hG₃ (Pi.single k 1) y
  rw [h3, smul_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul, hc] at e
  rw [← e]
  rfl

end VoleMole.Assumptions.SymmetryTensor
