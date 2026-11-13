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

end VoleMole.Assumptions.SymmetryTensor
