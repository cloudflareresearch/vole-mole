import VoleMole.Extraction.Gates

/-!
# The abstract model and its operators (sketch §3, L3)

States are functions `Ω → X` on the truth tables `Ω = L → V`, where `X` is `ℝ` (for norm profiles)
or the prover's register space `E`. We never form tensor products.

The averaging projector `Π_S` is written as `avg S`:
`(avg S ψ)(H) = |Ω|⁻¹ Σ_{G ∈ Ω} ψ(mix S G H)`, where `mix S G H` takes the `S`-coordinates from `G`
and the others from `H`. This averages over the same fibre as the sketch's
`|V|^{-|S|} Σ_{H'|_{L∖S} = H|_{L∖S}} ψ(H')` (each `H'` of the fibre is hit `|V|^{|L∖S|}` times);
`avg_eq_fiber_sum` proves the two agree.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Extraction

section Coord

variable {L V : Type*} [DecidableEq L] [Fintype L] [Fintype V] [DecidableEq V] [Nonempty V]

/-- `mix S G H` takes the coordinates in `S` from `G` and the others from `H`. -/
def mix (S : Finset L) (G H : L → V) : L → V := fun l => if l ∈ S then G l else H l

/-- `H` and `H'` agree outside `S`. -/
def AgreeOff (S : Finset L) (H H' : L → V) : Prop := ∀ l, l ∉ S → H l = H' l

/-- `f` does not depend on the coordinates in `S`. -/
def InvOn {X : Type*} (S : Finset L) (f : (L → V) → X) : Prop :=
  ∀ H H', AgreeOff S H H' → f H = f H'

lemma agreeOff_mix (S : Finset L) (G H : L → V) : AgreeOff S (mix S G H) H :=
  fun l hl => by simp [mix, hl]

lemma mix_congr {S : Finset L} {H H' : L → V} (h : AgreeOff S H H') (G : L → V) :
    mix S G H = mix S G H' := by
  funext l; by_cases hl : l ∈ S <;> simp [mix, hl, h l]

/-- Exchanging the `S`-coordinates of a pair of truth tables. -/
def swapS (S : Finset L) (p : (L → V) × (L → V)) : (L → V) × (L → V) :=
  (mix S p.2 p.1, mix S p.1 p.2)

lemma swapS_involutive (S : Finset L) : Function.Involutive (swapS (V := V) S) := by
  rintro ⟨G, H⟩
  refine Prod.ext ?_ ?_ <;> funext l <;> by_cases hl : l ∈ S <;> simp [swapS, mix, hl]

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- The averaging operator `Π_S`. -/
noncomputable def avg (S : Finset L) (f : (L → V) → X) (H : L → V) : X :=
  (Fintype.card (L → V) : ℝ)⁻¹ • ∑ G, f (mix S G H)

lemma card_omega_pos : (0 : ℝ) < Fintype.card (L → V) := by exact_mod_cast Fintype.card_pos

lemma avg_congr {S : Finset L} (f : (L → V) → X) {H H' : L → V} (h : AgreeOff S H H') :
    avg S f H = avg S f H' := by
  simp [avg, mix_congr h]

/-- `Π_S ψ` is constant along the `S`-coordinates. -/
lemma invOn_avg_self (S : Finset L) (f : (L → V) → X) : InvOn S (avg S f) :=
  fun _ _ h => avg_congr f h

/-- `Π_S` fixes the functions that are constant along the `S`-coordinates. -/
lemma avg_of_invOn {S : Finset L} {f : (L → V) → X} (hf : InvOn S f) : avg S f = f := by
  funext H
  simp only [avg]
  rw [Finset.sum_congr rfl fun G _ => hf _ _ (agreeOff_mix S G H), Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ card_omega_pos.ne', one_smul]

/-- **L3.1** (idempotence). -/
lemma avg_avg (S : Finset L) (f : (L → V) → X) : avg S (avg S f) = avg S f :=
  avg_of_invOn (invOn_avg_self S f)

/-- `Π_S` preserves independence of any coordinate set. -/
lemma invOn_avg {S T : Finset L} {f : (L → V) → X} (hf : InvOn T f) : InvOn T (avg S f) := by
  intro H H' h
  simp only [avg]
  congr 1
  refine Finset.sum_congr rfl fun G _ => hf _ _ fun l hl => ?_
  by_cases hlS : l ∈ S <;> simp [mix, hlS, h l hl]

/-- **L3.2**: `Π_S` commutes with multiplication by a function independent of `S`. -/
lemma avg_smul_left {S : Finset L} {d : (L → V) → ℝ} (hd : InvOn S d) (f : (L → V) → X)
    (H : L → V) : avg S (fun H => d H • f H) H = d H • avg S f H := by
  simp only [avg]
  rw [Finset.sum_congr rfl fun G _ => by rw [hd _ _ (agreeOff_mix S G H)], ← Finset.smul_sum,
    smul_comm]

lemma avg_add (S : Finset L) (f g : (L → V) → X) :
    avg S (f + g) = avg S f + avg S g := by
  funext H; simp [avg, Finset.sum_add_distrib, smul_add]

lemma avg_smul (S : Finset L) (r : ℝ) (f : (L → V) → X) : avg S (r • f) = r • avg S f := by
  funext H; simp [avg, ← Finset.smul_sum, smul_comm r]

/-- `Π_S` as a linear map on real functions. -/
noncomputable def avgₗ (S : Finset L) : ((L → V) → ℝ) →ₗ[ℝ] ((L → V) → ℝ) where
  toFun := avg S
  map_add' := avg_add S
  map_smul' := avg_smul S

open Classical in
/-- `avg S` is the sketch's `Π_S`: `(Π_S ψ)(H) = |V|^{-|S|} Σ_{H' agreeing with H off S} ψ(H')`. -/
lemma avg_eq_fiber_sum (S : Finset L) (f : (L → V) → X) (H : L → V) :
    avg S f H = ((Fintype.card V : ℝ) ^ S.card)⁻¹ • ∑ H' ∈ {H' | AgreeOff S H' H}, f H' := by
  have hmaps : ∀ G ∈ (Finset.univ : Finset (L → V)), mix S G H ∈ ({H' | AgreeOff S H' H} :
      Finset (L → V)) := fun G _ => by simpa using agreeOff_mix S G H
  have hfib : ∀ H' ∈ ({H' | AgreeOff S H' H} : Finset (L → V)),
      #{G | mix S G H = H'} = Fintype.card V ^ (Fintype.card L - S.card) := by
    intro H' hH'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH'
    have : ({G | mix S G H = H'} : Finset (L → V)) =
        Fintype.piFinset fun l => if l ∈ S then {H' l} else Finset.univ := by
      ext G
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro rfl l
        by_cases hl : l ∈ S <;> simp [mix, hl]
      · intro h
        funext l
        by_cases hl : l ∈ S
        · simpa [mix, hl] using h l
        · simp [mix, hl, hH' l hl]
    rw [this, Fintype.card_piFinset]
    simp only [apply_ite Finset.card]
    rw [Finset.prod_ite]
    simp only [Finset.card_singleton, Finset.prod_const_one, one_mul, Finset.card_univ,
      Finset.prod_const]
    congr 1
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ]
    simp
  simp only [avg]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hS : S.card ≤ Fintype.card L := Finset.card_le_univ S
  have hpow : (Fintype.card (L → V) : ℝ) =
      (Fintype.card V : ℝ) ^ S.card * (Fintype.card V : ℝ) ^ (Fintype.card L - S.card) := by
    rw [← pow_add, Nat.add_sub_cancel' hS, Fintype.card_fun]; push_cast; rfl
  have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun H' hH' => ?_
  rw [Finset.sum_congr rfl fun G hG => by rw [(Finset.mem_filter.1 hG).2], Finset.sum_const,
    hfib H' hH', ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hpow]
  congr 1
  push_cast
  field_simp

/-! ### Real-valued functions: self-adjointness, positivity, Jensen -/

lemma sum_mix_swap (S : Finset L) (F : (L → V) → (L → V) → ℝ) :
    ∑ G, ∑ H, F H (mix S G H) = ∑ G, ∑ H, F (mix S G H) H := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Function.Involutive.toPerm _ (swapS_involutive S)) _ _ fun p => ?_
  obtain ⟨G, H⟩ := p
  simp only [Function.Involutive.coe_toPerm, swapS]
  congr 1
  funext l; by_cases hl : l ∈ S <;> simp [mix, hl]

/-- **L3.1** (self-adjointness): `⟨g, Π_S f⟩ = ⟨Π_S g, f⟩`. -/
lemma sum_mul_avg (S : Finset L) (g f : (L → V) → ℝ) :
    ∑ H, g H * avg S f H = ∑ H, avg S g H * f H := by
  have h := sum_mix_swap S fun H H' => g H * f H'
  have l : ∑ H, g H * avg S f H =
      ∑ G, ∑ H, (Fintype.card (L → V) : ℝ)⁻¹ * (g H * f (mix S G H)) := by
    simp only [avg, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have r : ∑ H, avg S g H * f H =
      ∑ G, ∑ H, (Fintype.card (L → V) : ℝ)⁻¹ * (g (mix S G H) * f H) := by
    simp only [avg, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [l, r]
  simp only [← Finset.mul_sum]
  rw [h]

/-- `Π_S` preserves the total sum. -/
lemma sum_avg (S : Finset L) (f : (L → V) → ℝ) : ∑ H, avg S f H = ∑ H, f H := by
  have h1 : avg S (fun _ : L → V => (1 : ℝ)) = fun _ => 1 := avg_of_invOn fun _ _ _ => rfl
  have h := sum_mul_avg S (fun _ : L → V => (1 : ℝ)) f
  rw [h1] at h
  simpa using h

lemma avg_mono {S : Finset L} {f g : (L → V) → ℝ} (h : ∀ H, f H ≤ g H) (H : L → V) :
    avg S f H ≤ avg S g H := by
  simp only [avg, smul_eq_mul]
  have := (inv_pos.2 (card_omega_pos (L := L) (V := V))).le
  gcongr with G
  exact h _

lemma avg_nonneg {S : Finset L} {f : (L → V) → ℝ} (h : ∀ H, 0 ≤ f H) (H : L → V) :
    0 ≤ avg S f H := by
  have h' := avg_mono (S := S) (f := fun _ : L → V => (0 : ℝ)) (g := f) h H
  simpa [avg] using h'

/-- Weighted Cauchy–Schwarz for a `{0,1}`-valued weight `w`. -/
lemma avg_mul_sq_le {S : Finset L} {w : (L → V) → ℝ} (hw : ∀ H, w H * w H = w H)
    (k : (L → V) → ℝ) (H : L → V) :
    avg S (fun H => w H * k H) H ^ 2 ≤ avg S w H * avg S (fun H => w H * k H ^ 2) H := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun G => w (mix S G H))
    (fun G => w (mix S G H) * k (mix S G H))
  simp only [avg, smul_eq_mul]
  have e1 : ∀ G, w (mix S G H) * (w (mix S G H) * k (mix S G H)) = w (mix S G H) * k (mix S G H) :=
    fun G => by rw [← mul_assoc, hw]
  have e2 : ∀ G, w (mix S G H) ^ 2 = w (mix S G H) := fun G => by rw [sq, hw]
  have e3 : ∀ G, (w (mix S G H) * k (mix S G H)) ^ 2 = w (mix S G H) * k (mix S G H) ^ 2 :=
    fun G => by rw [mul_pow, e2]
  simp only [e1, e2, e3] at hcs
  rw [mul_pow, mul_mul_mul_comm, ← sq]
  exact mul_le_mul_of_nonneg_left hcs (sq_nonneg _)

/-- Jensen: `(Π_S f)² ≤ Π_S (f²)` pointwise. -/
lemma avg_sq_le (S : Finset L) (f : (L → V) → ℝ) (H : L → V) :
    avg S f H ^ 2 ≤ avg S (fun H => f H ^ 2) H := by
  have h := avg_mul_sq_le (S := S) (w := fun _ => 1) (by simp) f H
  have h1 : avg S (fun _ => (1 : ℝ)) H = 1 := by
    rw [avg_of_invOn (f := fun _ => (1 : ℝ)) fun _ _ _ => rfl]
  simpa [h1] using h

/-- Triangle inequality: `‖(Π_S ψ)(H)‖ ≤ (Π_S ‖ψ‖)(H)`. -/
lemma norm_avg_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Finset L)
    (ψ : (L → V) → E) (H : L → V) : ‖avg S ψ H‖ ≤ avg S (fun H => ‖ψ H‖) H := by
  simp only [avg, norm_smul, smul_eq_mul, norm_inv, Real.norm_natCast]
  gcongr
  exact norm_sum_le _ _

/-! ### Diagonal-times-averaging: `D Π_S` -/

/-- The operator `D Π_S`, where `D` is multiplication by `d`. -/
noncomputable def dproj (d : (L → V) → ℝ) (S : Finset L) (f : (L → V) → X) : (L → V) → X :=
  fun H => d H • avg S f H

/-- `d` is `{0,1}`-valued and does not depend on the `S`-coordinates: the hypotheses under which
`D Π_S` is an orthogonal projector. -/
structure IsCheck (d : (L → V) → ℝ) (S : Finset L) : Prop where
  idem : ∀ H, d H * d H = d H
  inv : InvOn S d

lemma IsCheck.nonneg {d : (L → V) → ℝ} {S : Finset L} (hd : IsCheck d S) (H : L → V) :
    0 ≤ d H := by
  rw [← hd.idem H]; exact mul_self_nonneg _

lemma IsCheck.le_one {d : (L → V) → ℝ} {S : Finset L} (hd : IsCheck d S) (H : L → V) :
    d H ≤ 1 := by
  have h := hd.idem H
  nlinarith [hd.nonneg H]

/-- **L3.4** (idempotence of `D Π_S`). -/
lemma dproj_dproj {d : (L → V) → ℝ} {S : Finset L} (hd : IsCheck d S) (f : (L → V) → X) :
    dproj d S (dproj d S f) = dproj d S f := by
  funext H
  show d H • avg S (fun H => d H • avg S f H) H = d H • avg S f H
  rw [avg_smul_left hd.inv, avg_avg, smul_smul, hd.idem]

/-- **L3.4** (self-adjointness of `D Π_S`). -/
lemma sum_mul_dproj {d : (L → V) → ℝ} {S : Finset L} (hd : IsCheck d S) (g f : (L → V) → ℝ) :
    ∑ H, g H * dproj d S f H = ∑ H, dproj d S g H * f H := by
  have h := sum_mul_avg S (fun H => d H * g H) f
  simp only [dproj, smul_eq_mul]
  calc ∑ H, g H * (d H * avg S f H) = ∑ H, d H * g H * avg S f H :=
        Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ H, avg S (fun H => d H * g H) H * f H := h
    _ = ∑ H, d H * avg S g H * f H := by
        refine Finset.sum_congr rfl fun H _ => ?_
        rw [show (fun H => d H * g H) = fun H => d H • g H from rfl, avg_smul_left hd.inv]
        rfl

/-- `‖D Π_S f‖² = ⟨f, D Π_S f⟩`. -/
lemma sum_dproj_sq {d : (L → V) → ℝ} {S : Finset L} (hd : IsCheck d S) (f : (L → V) → ℝ) :
    ∑ H, dproj d S f H ^ 2 = ∑ H, f H * dproj d S f H := by
  have h := sum_mul_dproj hd (dproj d S f) f
  rw [dproj_dproj hd] at h
  simp only [sq]
  rw [h]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma dproj_add (d : (L → V) → ℝ) (S : Finset L) (f g : (L → V) → X) :
    dproj d S (f + g) = dproj d S f + dproj d S g := by
  funext H; simp [dproj, avg_add, smul_add]

lemma dproj_smul (d : (L → V) → ℝ) (S : Finset L) (r : ℝ) (f : (L → V) → X) :
    dproj d S (r • f) = r • dproj d S f := by
  funext H; simp [dproj, avg_smul, smul_comm r]

/-- `D Π_S` as a linear map on real functions. -/
noncomputable def dprojₗ (d : (L → V) → ℝ) (S : Finset L) :
    ((L → V) → ℝ) →ₗ[ℝ] ((L → V) → ℝ) where
  toFun := dproj d S
  map_add' := dproj_add d S
  map_smul' := dproj_smul d S

end Coord

end VoleMole.Extraction
