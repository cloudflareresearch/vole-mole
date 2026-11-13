import VoleMole.Assumptions.SymmetryTensor
import VoleMole.Assumptions.SymmetryCount

/-!
# Theorem T3: the symmetries of a UOV key are scalar

WIP header.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Assumptions.SymmetryScalar

open VoleMole.Spec VoleMole.Spec.Pqov VoleMole.Arith VoleMole.Arith.UOV VoleMole.Privacy
  VoleMole.Privacy.Moussaka VoleMole.Assumptions.SymmetryProbes VoleMole.Assumptions.SymmetryTensor Module Matrix

/-! ## Linear algebra -/

/-- A `σ`-semilinear map is a linear map applied after `σ` on the coordinates. -/
lemma exists_linear_semilin {κ W : Type*} [AddCommGroup W] [Module GF256 W]
    (σ : GF256 →+* GF256) (g : (κ → GF256) → W) (hadd : ∀ u w, g (u + w) = g u + g w)
    (hsm : ∀ (c : GF256) u, g (c • u) = σ c • g u) :
    ∃ Λ : (κ → GF256) →ₗ[GF256] W, ∀ x, g x = Λ fun i => σ (x i) := by
  have hbij : Function.Bijective σ := ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  let e := RingEquiv.ofBijective σ hbij
  have he : ∀ c, σ (e.symm c) = c := fun c => e.apply_symm_apply c
  refine ⟨{ toFun := fun y => g (fun i => e.symm (y i))
            map_add' := fun y z => by
              rw [← hadd]; congr 1; funext i; simp
            map_smul' := fun c y => by
              have : (fun i => e.symm ((c • y) i)) = e.symm c • fun i => e.symm (y i) := by
                funext i; simp
              rw [this, hsm, he]; rfl }, fun x => ?_⟩
  show g x = g (fun i => e.symm (σ (x i)))
  congr 1
  funext i
  exact (e.symm_apply_apply (x i)).symm

lemma exists_sigma_preimage {κ : Type*} (σ : GF256 →+* GF256) (z : κ → GF256) :
    ∃ x : κ → GF256, (fun i => σ (x i)) = z := by
  have hs := Finite.surjective_of_injective σ.injective
  choose x hx using hs
  exact ⟨fun i => x (z i), funext fun i => hx (z i)⟩

/-- A linear map has `18` independent values, or rank at most `17`. -/
lemma rank_dichotomy {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    (f : (κ → GF256) →ₗ[GF256] (κ' → GF256)) :
    (∃ x : Fin 9 ⊕ Fin 9 → κ → GF256, LinearIndependent GF256 fun s => f (x s)) ∨
      finrank GF256 (LinearMap.range f) ≤ 17 := by
  by_cases h : 9 + 9 ≤ finrank GF256 (LinearMap.range f)
  · left
    obtain ⟨y, hy⟩ := exists_linearIndependent_of_le_finrank h
    have hy' := (hy.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)).comp
      finSumFinEquiv finSumFinEquiv.injective
    choose x hx using fun i => (y i).2
    refine ⟨fun s => x (finSumFinEquiv s), ?_⟩
    convert hy' using 1
    funext s
    simp [hx]
  · right; omega

/-- `L(v, C v) = 0` for all `v` forces `C = 0`, for a good tensor. -/
lemma vo_eq_zero {S : Coef} (hS : GoodS S) (C : Vin →ₗ[GF256] Oil)
    (h : ∀ v, bil S v (C v) = 0) : C = 0 := by
  classical
  have hpol : ∀ v v', bil S v (C v') + bil S v' (C v) = 0 := by
    intro v v'
    have := h (v + v')
    rw [map_add, bil_add_left, bil_add_right, bil_add_right, h, h, zero_add, add_zero] at this
    exact this
  rcases rank_dichotomy C with ⟨x, hx⟩ | hr
  · refine absurd ⟨fun i j => LinearMap.toMatrix' C i j, ⟨x, ?_⟩, fun v => ?_⟩ hS.pairVO
    · have e : (fun s => Matrix.of (fun i j => LinearMap.toMatrix' C i j) *ᵥ x s) =
          fun s => C (x s) := funext fun s => toMatrix'_mulVec' C (x s)
      rw [e]; exact hx
    · rw [toMatrix'_mulVec']; exact h v
  · obtain ⟨Φ, hΦ⟩ := exists_functionals C hr
    refine LinearMap.ext fun u => ?_
    by_contra hne
    refine hS.boxO ⟨C u, hne, Φ, 0, fun v h' hv _ => ?_⟩
    have := hpol v u
    rw [hΦ v hv, bil_zero_right, add_zero] at this
    rw [tri_eq_dot, this, dotProduct_zero]

/-- `L(C x, x) = 0` for all `x` forces `C = 0`, for a good tensor. -/
lemma ov_eq_zero {S : Coef} (hS : GoodS S) (C : Oil →ₗ[GF256] Vin)
    (h : ∀ x, bil S (C x) x = 0) : C = 0 := by
  classical
  have hpol : ∀ x x', bil S (C x) x' + bil S (C x') x = 0 := by
    intro x x'
    have := h (x + x')
    rw [map_add, bil_add_left, bil_add_right, bil_add_right, h, h, zero_add, add_zero] at this
    exact this
  rcases rank_dichotomy C with ⟨x, hx⟩ | hr
  · refine absurd ⟨fun i j => LinearMap.toMatrix' C i j, ⟨x, ?_⟩, fun v => ?_⟩ hS.pairOV
    · have e : (fun s => Matrix.of (fun i j => LinearMap.toMatrix' C i j) *ᵥ x s) =
          fun s => C (x s) := funext fun s => toMatrix'_mulVec' C (x s)
      rw [e]; exact hx
    · rw [toMatrix'_mulVec']; exact h v
  · obtain ⟨Φ, hΦ⟩ := exists_functionals C hr
    refine LinearMap.ext fun u => ?_
    by_contra hne
    refine hS.boxV ⟨C u, hne, Φ, 0, fun x h' hx _ => ?_⟩
    have := hpol u x
    rw [hΦ x hx, bil_zero_left, add_zero] at this
    rw [tri_eq_dot, this, dotProduct_zero]

/-! ## A key in the coordinates of its oil space -/

/-- A quadratic map `Q` on the vinegars with polar form `BQ`. -/
structure QuadV (Q : Vin → Tgt) (BQ : Vin → Vin → Tgt) : Prop where
  add : ∀ v w, Q (v + w) = Q v + Q w + BQ v w
  smul : ∀ (c : GF256) v, Q (c • v) = c ^ 2 • Q v
  badd : ∀ v v' w, BQ (v + v') w = BQ v w + BQ v' w
  bsmul : ∀ (c : GF256) v w, BQ (c • v) w = c • BQ v w
  bcomm : ∀ v w, BQ v w = BQ w v
  bself : ∀ v, BQ v v = 0

/-- The key `P(v, x) = Q(v) + L(v, x)` in the coordinates of its oil space. -/
noncomputable def PA (Q : Vin → Tgt) (S : Coef) (s : Vin × Oil) : Tgt := Q s.1 + bil S s.1 s.2

/-- Its polar form. -/
noncomputable def BA (BQ : Vin → Vin → Tgt) (S : Coef) (s u : Vin × Oil) : Tgt :=
  BQ s.1 u.1 + bil S s.1 u.2 + bil S u.1 s.2

section Adapted

variable {Q : Vin → Tgt} {BQ : Vin → Vin → Tgt} {S : Coef}

lemma QuadV.zero (hQ : QuadV Q BQ) : Q 0 = 0 := by simpa using hQ.smul 0 0

lemma QuadV.bzero_left (hQ : QuadV Q BQ) (w : Vin) : BQ 0 w = 0 := by
  simpa using hQ.bsmul 0 0 w

lemma QuadV.bzero_right (hQ : QuadV Q BQ) (v : Vin) : BQ v 0 = 0 := by
  rw [hQ.bcomm, hQ.bzero_left]

lemma QuadV.badd_right (hQ : QuadV Q BQ) (v w w' : Vin) : BQ v (w + w') = BQ v w + BQ v w' := by
  rw [hQ.bcomm, hQ.badd, hQ.bcomm w, hQ.bcomm w']

lemma QuadV.bsmul_right (hQ : QuadV Q BQ) (c : GF256) (v w : Vin) :
    BQ v (c • w) = c • BQ v w := by
  rw [hQ.bcomm, hQ.bsmul, hQ.bcomm]

lemma PA_add (hQ : QuadV Q BQ) (s u : Vin × Oil) :
    PA Q S (s + u) = PA Q S s + PA Q S u + BA BQ S s u := by
  simp only [PA, BA, Prod.fst_add, Prod.snd_add, hQ.add, bil_add_left, bil_add_right]
  abel

lemma PA_smul (hQ : QuadV Q BQ) (c : GF256) (s : Vin × Oil) :
    PA Q S (c • s) = c ^ 2 • PA Q S s := by
  simp only [PA, Prod.smul_fst, Prod.smul_snd, hQ.smul, bil_smul_left, bil_smul_right, smul_add,
    smul_smul, sq]

lemma PA_zero (hQ : QuadV Q BQ) : PA Q S 0 = 0 := by
  simp [PA, hQ.zero, bil_zero_left]

lemma BA_comm (hQ : QuadV Q BQ) (s u : Vin × Oil) : BA BQ S s u = BA BQ S u s := by
  simp only [BA, hQ.bcomm s.1 u.1]; abel

lemma BA_add_left (hQ : QuadV Q BQ) (s s' u : Vin × Oil) :
    BA BQ S (s + s') u = BA BQ S s u + BA BQ S s' u := by
  simp only [BA, Prod.fst_add, Prod.snd_add, hQ.badd, bil_add_left, bil_add_right]
  abel

lemma BA_add_right (hQ : QuadV Q BQ) (s u u' : Vin × Oil) :
    BA BQ S s (u + u') = BA BQ S s u + BA BQ S s u' := by
  rw [BA_comm hQ, BA_add_left hQ, BA_comm hQ u, BA_comm hQ u']

lemma BA_smul_left (hQ : QuadV Q BQ) (c : GF256) (s u : Vin × Oil) :
    BA BQ S (c • s) u = c • BA BQ S s u := by
  simp only [BA, Prod.smul_fst, Prod.smul_snd, hQ.bsmul, bil_smul_left, bil_smul_right, smul_add]

lemma BA_zero_left (hQ : QuadV Q BQ) (u : Vin × Oil) : BA BQ S 0 u = 0 := by
  simpa using BA_smul_left (S := S) hQ 0 0 u

/-- **The radical of a good key is trivial.** -/
lemma rad_trivial (hQ : QuadV Q BQ) (hS : GoodS S) {z : Vin × Oil}
    (hz : ∀ u, BA BQ S z u = 0) : z = 0 := by
  have h1 : z.1 = 0 := by
    by_contra hne
    refine hS.boxV ⟨z.1, hne, 0, 0, fun x h' _ _ => ?_⟩
    have := hz (0, x)
    simp only [BA, hQ.bzero_right, bil_zero_left, zero_add, add_zero] at this
    rw [tri_eq_dot, this, dotProduct_zero]
  have h2 : z.2 = 0 := by
    by_contra hne
    refine hS.boxO ⟨z.2, hne, 0, 0, fun v h' _ _ => ?_⟩
    have := hz (v, 0)
    simp only [BA, h1, hQ.bzero_left, bil_zero_left, zero_add] at this
    rw [tri_eq_dot, this, dotProduct_zero]
  exact Prod.ext h1 h2

/-- The vinegar part is tied to the tensor by an identity `L(v, C v) = δ·Q(v)`: polar form. -/
lemma polar_of_diag (hQ : QuadV Q BQ) {C : Vin →ₗ[GF256] Oil} {δ : GF256}
    (h1 : ∀ v, bil S v (C v) = δ • Q v) (v v' : Vin) :
    δ • BQ v v' = bil S v (C v') + bil S v' (C v) := by
  have e := h1 (v + v')
  rw [map_add, bil_add_left, bil_add_right, bil_add_right, h1 v, h1 v', hQ.add, smul_add,
    smul_add] at e
  have e' : δ • Q v + δ • Q v' + (bil S v (C v') + bil S v' (C v)) =
      δ • Q v + δ • Q v' + δ • BQ v v' := by rw [← e]; abel
  exact (add_left_cancel e').symm

/-- **The bad events on the vinegar part** `Q`, given the tensor. -/
def IsoQ (BQ : Vin → Vin → Tgt) (S : Coef) : Prop :=
  ∃ (v v' : Fin 9 → Vin) (y y' : Fin 9 → Oil), LinearIndependent GF256 (Sum.elim v v') ∧
    ∀ i j, BQ (v i) (v' j) + bil S (v i) (y' j) + bil S (v' j) (y i) = 0

/-- The polar form of `Q` is determined by the tensor and a matrix `C`. -/
def DetQ (BQ : Vin → Vin → Tgt) (S : Coef) : Prop :=
  ∃ (δ : GF256) (C : Fin 45 → Fin 74 → GF256), δ ≠ 0 ∧
    ∀ v v', δ • BQ v v' = bil S v (Matrix.of C *ᵥ v') + bil S v' (Matrix.of C *ᵥ v)

/-- `L(v, C v) = δ·Q(v)` for all `v` forces `δ = 0` and `C = 0`, for a good key. -/
lemma diag_zero (hQ : QuadV Q BQ) (hS : GoodS S) (hD : ¬ DetQ BQ S) (C : Vin →ₗ[GF256] Oil)
    (δ : GF256) (h1 : ∀ v, bil S v (C v) = δ • Q v) : δ = 0 ∧ C = 0 := by
  have hδ : δ = 0 := by
    by_contra hne
    refine hD ⟨δ, fun i j => LinearMap.toMatrix' C i j, hne, fun v v' => ?_⟩
    rw [toMatrix'_mulVec', toMatrix'_mulVec']
    exact polar_of_diag hQ h1 v v'
  exact ⟨hδ, vo_eq_zero hS C fun v => by rw [h1, hδ, zero_smul]⟩

end Adapted

/-! ## The symmetries of a good key in adapted coordinates -/

section Main

variable {Q : Vin → Tgt} {BQ : Vin → Vin → Tgt} {S : Coef}

/-- **The symmetries of a good key are the scalings** (adapted coordinates, `σ`-semilinear
maps): if `P ∘ A = T ∘ P` with `A`, `T` additive and `σ`-semilinear and `A` bijective, then `σ`
is the identity, `A = λ` and `T = λ²`. -/
theorem adapted_group (hQ : QuadV Q BQ) (hS : GoodS S) (hI : ¬ IsoQ BQ S) (hD : ¬ DetQ BQ S)
    (σ : GF256 →+* GF256) (A : Vin × Oil → Vin × Oil) (T : Tgt → Tgt)
    (hAa : ∀ s u, A (s + u) = A s + A u) (hAs : ∀ (c : GF256) s, A (c • s) = σ c • A s)
    (hTa : ∀ y z, T (y + z) = T y + T z) (hTs : ∀ (c : GF256) y, T (c • y) = σ c • T y)
    (hAb : Function.Bijective A) (h : ∀ s, PA Q S (A s) = T (PA Q S s)) :
    (∀ c, σ c = c) ∧ ∃ l : GF256, l ≠ 0 ∧ (∀ s, A s = l • s) ∧ ∀ y, T y = l ^ 2 • y := by
  classical
  have hA0 : A 0 = 0 := by simpa using hAs 0 0
  have hT0 : T 0 = 0 := by simpa using hTs 0 0
  have hpol : ∀ s u, BA BQ S (A s) (A u) = T (BA BQ S s u) := by
    intro s u
    have e := h (s + u)
    rw [hAa, PA_add hQ, PA_add hQ, hTa, hTa, h s, h u] at e
    exact add_left_cancel e
  -- Step 1: `A` maps the oil space into itself
  have hiso : ∀ x x' : Oil, BA BQ S (A (0, x)) (A (0, x')) = 0 := by
    intro x x'
    rw [hpol]
    simp only [BA, hQ.bzero_left, bil_zero_left, add_zero, hT0]
  obtain ⟨Λ, hΛ⟩ := exists_linear_semilin σ (fun x : Oil => A (0, x))
    (fun u w => by rw [← hAa]; simp) (fun c u => by rw [← hAs]; simp)
  have hΛinj : Function.Injective Λ := by
    intro z z' hzz
    obtain ⟨x, rfl⟩ := exists_sigma_preimage σ z
    obtain ⟨x', rfl⟩ := exists_sigma_preimage σ z'
    rw [← hΛ, ← hΛ] at hzz
    have := hAb.1 hzz
    rw [(Prod.mk.inj this).2]
  let ā : Oil →ₗ[GF256] Vin := (LinearMap.fst GF256 Vin Oil).comp Λ
  have hā : ā = 0 := by
    rcases rank_dichotomy ā with ⟨z, hz⟩ | hr
    · exfalso
      choose x hx using fun s => exists_sigma_preimage σ (z s)
      refine hI ⟨fun i => ā (z (Sum.inl i)), fun j => ā (z (Sum.inr j)),
        fun i => (Λ (z (Sum.inl i))).2, fun j => (Λ (z (Sum.inr j))).2, ?_, fun i j => ?_⟩
      · have e : Sum.elim (fun i => ā (z (Sum.inl i))) (fun j => ā (z (Sum.inr j))) =
            fun s => ā (z s) := by funext s; cases s <;> rfl
        rw [e]; exact hz
      · have := hiso (x (Sum.inl i)) (x (Sum.inr j))
        rw [hΛ, hΛ, hx, hx] at this
        exact this
    · refine LinearMap.ext fun z0 => ?_
      by_contra hne
      let f : LinearMap.ker ā →ₗ[GF256] Oil :=
        ((LinearMap.snd GF256 Vin Oil).comp Λ).comp (LinearMap.ker ā).subtype
      have hf : Function.Injective f := by
        intro a b hab
        refine Subtype.ext (hΛinj (Prod.ext ?_ hab))
        exact (LinearMap.mem_ker.1 a.2).trans (LinearMap.mem_ker.1 b.2).symm
      have hK : Fintype.card (Fin 45) ≤ finrank GF256 (LinearMap.range f) + 17 := by
        rw [LinearMap.finrank_range_of_inj hf]
        have := LinearMap.finrank_range_add_finrank_ker ā
        rw [finrank_oil] at this
        simp only [Fintype.card_fin]
        exact this.symm.le.trans ((add_comm _ _).le.trans (Nat.add_le_add_left hr _))
      obtain ⟨Φ, hΦ⟩ := exists_functionals_of_finrank (LinearMap.range f) hK
      refine hS.boxV ⟨ā z0, hne, Φ, 0, fun x h' hx _ => ?_⟩
      obtain ⟨k, rfl⟩ := hΦ x hx
      obtain ⟨x0, hx0⟩ := exists_sigma_preimage σ z0
      obtain ⟨xk, hxk⟩ := exists_sigma_preimage σ (k : Oil)
      have e := hiso x0 xk
      rw [hΛ, hΛ, hx0, hxk] at e
      have hk0 : (Λ (k : Oil)).1 = 0 := LinearMap.mem_ker.1 k.2
      simp only [BA, hk0, hQ.bzero_right, bil_zero_left, zero_add, add_zero] at e
      rw [tri_eq_dot]
      show h' ⬝ᵥ bil S (Λ z0).1 (Λ (k : Oil)).2 = 0
      rw [e, dotProduct_zero]
  have h1 : ∀ x : Oil, (A (0, x)).1 = 0 := by
    intro x
    rw [hΛ]
    exact congrArg (fun g : Oil →ₗ[GF256] Vin => g fun i => σ (x i)) hā
  -- Step 2: the tensor
  let g₁ : Vin → Vin := fun v => (A (v, 0)).1
  let g₂ : Oil → Oil := fun x => (A (0, x)).2
  let cc : Vin → Oil := fun v => (A (v, 0)).2
  have hdec : ∀ v x, A (v, x) = (g₁ v, cc v + g₂ x) := by
    intro v x
    have : ((v, x) : Vin × Oil) = (v, 0) + (0, x) := by simp
    rw [this, hAa]
    refine Prod.ext ?_ rfl
    simp only [Prod.fst_add, h1 x, add_zero, g₁]
  have hv0 : ∀ u w : Vin, ((u + w, 0) : Vin × Oil) = (u, 0) + (w, 0) := fun u w => by simp
  have hvs : ∀ (c : GF256) (u : Vin), ((c • u, 0) : Vin × Oil) = c • (u, 0) := fun c u => by simp
  have hx0 : ∀ u w : Oil, ((0, u + w) : Vin × Oil) = (0, u) + (0, w) := fun u w => by simp
  have hxs : ∀ (c : GF256) (u : Oil), ((0, c • u) : Vin × Oil) = c • (0, u) := fun c u => by simp
  have h1b : Function.Surjective g₁ := by
    intro v'
    obtain ⟨⟨v, x⟩, hs⟩ := hAb.2 (v', 0)
    rw [hdec] at hs
    exact ⟨v, congrArg Prod.fst hs⟩
  have h1i : Function.Injective g₁ := Finite.injective_iff_surjective.2 h1b
  have hg₁0 : g₁ 0 = 0 := by
    show (A ((0 : Vin), (0 : Oil))).1 = 0
    rw [show (((0 : Vin), (0 : Oil)) : Vin × Oil) = 0 from rfl, hA0]; rfl
  have hcc0 : cc 0 = 0 := by
    show (A ((0 : Vin), (0 : Oil))).2 = 0
    rw [show (((0 : Vin), (0 : Oil)) : Vin × Oil) = 0 from rfl, hA0]; rfl
  have h2b : Function.Surjective g₂ := by
    intro x'
    obtain ⟨⟨v, x⟩, hs⟩ := hAb.2 (0, x')
    rw [hdec] at hs
    have hv : v = 0 := h1i ((congrArg Prod.fst hs).trans hg₁0.symm)
    have := congrArg Prod.snd hs
    simp only [hv, hcc0, zero_add] at this
    exact ⟨x, this⟩
  have hten : ∀ v x, bil S (g₁ v) (g₂ x) = T (bil S v x) := by
    intro v x
    have e := hpol (v, 0) (0, x)
    simp only [BA, h1 x, hQ.bzero_right, bil_zero_left, bil_zero_right, add_zero, zero_add] at e
    exact e
  obtain ⟨hσ, α, β, hα, hβ, hg₁, hg₂, hT⟩ := tensor_group hS σ g₁ g₂ T
    (fun u w => by simp only [g₁, hv0, hAa, Prod.fst_add])
    (fun c u => by simp only [g₁, hvs, hAs, Prod.smul_fst])
    (fun u w => by simp only [g₂, hx0, hAa, Prod.snd_add])
    (fun c u => by simp only [g₂, hxs, hAs, Prod.smul_snd])
    hTa hTs h1b h2b hten
  -- Step 3: the vinegar part
  let C : Vin →ₗ[GF256] Oil := linOf cc (fun u w => by simp only [cc, hv0, hAa, Prod.snd_add])
    (fun c u => by simp only [cc, hvs, hAs, Prod.smul_snd, hσ])
  have hQ1 : ∀ v, bil S v (C v) = (β - α) • Q v := by
    intro v
    have e := h (v, 0)
    have e1 : A (v, 0) = (α • v, C v) := Prod.ext (hg₁ v) rfl
    rw [e1, hT] at e
    simp only [PA, hQ.smul, bil_smul_left, bil_zero_right, add_zero] at e
    funext k
    have ek := congrFun e k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ek ⊢
    exact mul_left_cancel₀ hα (by linear_combination ek)
  obtain ⟨hδ, hC⟩ := diag_zero hQ hS hD C (β - α) hQ1
  have hβα : β = α := sub_eq_zero.1 hδ
  refine ⟨hσ, α, hα, fun s => ?_, fun y => by rw [hT, hβα, sq]⟩
  obtain ⟨v, x⟩ := s
  rw [hdec, hg₁, hg₂, hβα]
  have : cc v = 0 := congrArg (fun g : Vin →ₗ[GF256] Oil => g v) hC
  rw [this, zero_add]
  rfl

/-- **The infinitesimal symmetries of a good key are `F·(I, 0)`** (adapted coordinates). -/
theorem adapted_lie (hQ : QuadV Q BQ) (hS : GoodS S) (hD : ¬ DetQ BQ S)
    (X : (Vin × Oil) →ₗ[GF256] (Vin × Oil)) (Y : Tgt →ₗ[GF256] Tgt)
    (h : ∀ s, BA BQ S s (X s) = Y (PA Q S s)) :
    ∃ l : GF256, (∀ s, X s = l • s) ∧ ∀ y, Y y = 0 := by
  classical
  let xb : Oil →ₗ[GF256] Vin :=
    (LinearMap.fst GF256 Vin Oil).comp (X.comp (LinearMap.inr GF256 Vin Oil))
  let X₁ : Vin →ₗ[GF256] Vin :=
    (LinearMap.fst GF256 Vin Oil).comp (X.comp (LinearMap.inl GF256 Vin Oil))
  let X₂ : Oil →ₗ[GF256] Oil :=
    (LinearMap.snd GF256 Vin Oil).comp (X.comp (LinearMap.inr GF256 Vin Oil))
  let C : Vin →ₗ[GF256] Oil :=
    (LinearMap.snd GF256 Vin Oil).comp (X.comp (LinearMap.inl GF256 Vin Oil))
  have hxb : xb = 0 := by
    refine ov_eq_zero hS xb fun x => ?_
    have e := h (0, x)
    simp only [BA, PA, hQ.bzero_left, hQ.zero, bil_zero_left, zero_add, map_zero] at e
    exact e
  have hxb' : ∀ x : Oil, (X (0, x)).1 = 0 := fun x =>
    congrArg (fun g : Oil →ₗ[GF256] Vin => g x) hxb
  have hpol : ∀ s u, BA BQ S s (X u) + BA BQ S u (X s) = Y (BA BQ S s u) := by
    intro s u
    have e := h (s + u)
    rw [map_add, BA_add_left hQ, BA_add_right hQ, BA_add_right hQ, PA_add hQ, map_add, map_add,
      h s, h u] at e
    have e' : Y (PA Q S s) + Y (PA Q S u) + (BA BQ S s (X u) + BA BQ S u (X s)) =
        Y (PA Q S s) + Y (PA Q S u) + Y (BA BQ S s u) := by rw [← e]; abel
    exact add_left_cancel e'
  have hten : ∀ v x, bil S (X₁ v) x + bil S v (X₂ x) = Y (bil S v x) := by
    intro v x
    have e := hpol (v, 0) (0, x)
    simp only [BA, hxb' x, hQ.bzero_left, hQ.bzero_right, bil_zero_left, bil_zero_right, add_zero,
      zero_add] at e
    rw [add_comm]
    exact e
  obtain ⟨α, β, hX₁, hX₂, hY⟩ := tensor_lie hS X₁ X₂ Y hten
  have hQ1 : ∀ v, bil S v (C v) = (α + β) • Q v := by
    intro v
    have e := h (v, 0)
    have e1 : X (v, 0) = (α • v, C v) := Prod.ext (hX₁ v) rfl
    rw [e1, hY] at e
    simp only [BA, PA, hQ.bsmul_right, hQ.bself, smul_zero, bil_zero_right, add_zero,
      zero_add] at e
    exact e
  obtain ⟨hδ, hC⟩ := diag_zero hQ hS hD C (α + β) hQ1
  have hβα : β = α := by
    have : -α = β := neg_eq_of_add_eq_zero_right hδ
    rw [← this]; rfl
  refine ⟨α, fun s => ?_, fun y => by rw [hY, hδ, zero_smul]⟩
  obtain ⟨v, x⟩ := s
  have e : ((v, x) : Vin × Oil) = (v, 0) + (0, x) := by simp
  have e2 : X (0, x) = (0, α • x) := Prod.ext (hxb' x) ((hX₂ x).trans (by rw [hβα]))
  have e3 : X (v, 0) = (α • v, 0) :=
    Prod.ext (hX₁ v) (congrArg (fun g : Vin →ₗ[GF256] Oil => g v) hC)
  rw [e, map_add, e2, e3]
  simp

/-- **Affine pairs, and pairs with `T` injective** (adapted coordinates): if
`P(A s + a) = T(P s) + c` with `A`, `T` additive and `σ`-semilinear, and `A` is bijective or `T`
injective, then `σ` is the identity, `a = 0`, `c = 0`, `A = λ` and `T = λ²`. -/
theorem adapted_affine (hQ : QuadV Q BQ) (hS : GoodS S) (hI : ¬ IsoQ BQ S) (hD : ¬ DetQ BQ S)
    (σ : GF256 →+* GF256) (A : Vin × Oil → Vin × Oil) (a : Vin × Oil) (T : Tgt → Tgt) (c : Tgt)
    (hAa : ∀ s u, A (s + u) = A s + A u) (hAs : ∀ (c : GF256) s, A (c • s) = σ c • A s)
    (hTa : ∀ y z, T (y + z) = T y + T z) (hTs : ∀ (c : GF256) y, T (c • y) = σ c • T y)
    (hb : Function.Bijective A ∨ Function.Injective T)
    (h : ∀ s, PA Q S (A s + a) = T (PA Q S s) + c) :
    (∀ x, σ x = x) ∧ a = 0 ∧ c = 0 ∧
      ∃ l : GF256, l ≠ 0 ∧ (∀ s, A s = l • s) ∧ ∀ y, T y = l ^ 2 • y := by
  have hA0 : A 0 = 0 := by simpa using hAs 0 0
  have hT0 : T 0 = 0 := by simpa using hTs 0 0
  have hc : c = PA Q S a := by
    have := h 0
    rw [hA0, zero_add, PA_zero hQ, hT0, zero_add] at this
    exact this.symm
  have hE : ∀ s, PA Q S (A s) + BA BQ S (A s) a = T (PA Q S s) := by
    intro s
    have := h s
    rw [PA_add hQ, hc] at this
    have e : PA Q S (A s) + PA Q S a + BA BQ S (A s) a =
        PA Q S (A s) + BA BQ S (A s) a + PA Q S a := by abel
    rw [e] at this
    exact add_right_cancel this
  have hpol : ∀ s u, BA BQ S (A s) (A u) = T (BA BQ S s u) := by
    intro s u
    have e := hE (s + u)
    rw [hAa, PA_add hQ, BA_add_left hQ, PA_add hQ, hTa, hTa, ← hE s, ← hE u] at e
    have e' : PA Q S (A s) + BA BQ S (A s) a + (PA Q S (A u) + BA BQ S (A u) a) +
        BA BQ S (A s) (A u) = PA Q S (A s) + BA BQ S (A s) a +
        (PA Q S (A u) + BA BQ S (A u) a) + T (BA BQ S s u) := by rw [← e]; abel
    exact add_left_cancel e'
  have hbij : Function.Bijective A := by
    rcases hb with hb | hb
    · exact hb
    · refine Finite.injective_iff_bijective.1 ?_
      refine (injective_iff_map_eq_zero (AddMonoidHom.mk' A hAa)).2 fun z hz => ?_
      refine rad_trivial hQ hS fun u => hb ?_
      rw [← hpol, show A z = 0 from hz, BA_zero_left hQ, hT0]
  have ha : a = 0 := by
    refine rad_trivial hQ hS fun u => ?_
    obtain ⟨s, rfl⟩ := hbij.2 u
    rw [BA_comm hQ]
    obtain ⟨l, h0, h1⟩ := SymmetryCount.exists_ne_zero_one
    have hl0 : σ l ≠ 0 := fun e => h0 (σ.injective (e.trans (map_zero σ).symm))
    have hl1 : σ l ≠ 1 := fun e => h1 (σ.injective (e.trans (map_one σ).symm))
    have e1 := hE (l • s)
    rw [hAs, PA_smul hQ, PA_smul hQ, BA_smul_left hQ, hTs, map_pow, ← hE s, smul_add] at e1
    have e2 : (σ l - σ l ^ 2) • BA BQ S (A s) a = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact add_left_cancel e1
    rcases smul_eq_zero.mp e2 with e3 | e3
    · exfalso
      have : σ l * (1 - σ l) = 0 := by rw [← e3]; ring
      rcases mul_eq_zero.mp this with e4 | e4
      · exact hl0 e4
      · exact hl1 (sub_eq_zero.mp e4).symm
    · exact e3
  have hc0 : c = 0 := by rw [hc, ha, PA_zero hQ]
  obtain ⟨hσ, l, hl, hA, hT⟩ := adapted_group hQ hS hI hD σ A T hAa hAs hTa hTs hbij fun s => by
    have := h s
    rwa [ha, hc0, add_zero, add_zero] at this
  exact ⟨hσ, ha, hc0, l, hl, hA, hT⟩

end Main

/-! ## The vinegar part of pqov's keys -/

/-- The bytes of the `P1` part: the first `45·2775 = 124875` bytes of the expanded key. -/
abbrev P1Part := Fin 124875 → GF256

/-- The `P1` part as a function of the offset. -/
def p1 (p : P1Part) : ℕ → GF256 := fun n => if h : n < 124875 then p ⟨n, h⟩ else 0

/-- The polar form of the vinegar part `P₁`, from the bytes of `P1`. -/
noncomputable def bq (p : P1Part) (v w : Vin) : Tgt := fun k =>
  ∑ i : Fin 74, ∑ l : Fin 74, if (i : ℕ) < l then
    p ⟨off1 i l + k, off1_lt i l k⟩ * (v i * w l + w i * v l) else 0

private lemma gf_add_self (a : GF256) : a + a = 0 := by
  have h : -a = a := rfl
  calc a + a = a + -a := by rw [h]
    _ = 0 := add_neg_cancel a

/-- The polar form of pqov's key on two vinegar vectors is `bq`. -/
lemma polar_vinVec (O : OilMat) (p : P1Part) (P2 : P2Part) (v w : Vin) :
    polar (pqovKey O (p1 p) P2) (vinVec v) (vinVec w) = bq p v w := by
  funext k
  rw [polar_eq_blocks]
  simp only [vinVec_fin, vinVec_oil, mul_zero, add_zero, Finset.sum_const_zero,
    ite_self, c1_pqovKey, c1_keyP12, bq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases hil : (i : ℕ) < l
  · simp only [hil, hil.le, ↓reduceIte, p1, off1_lt i l k, ↓reduceDIte]
  · by_cases hil' : (i : ℕ) ≤ l
    · have : i = l := Fin.ext (by omega)
      subst this
      simp only [le_refl, ↓reduceIte, lt_irrefl, mul_comm (w i) (v i), gf_add_self, mul_zero]
    · simp only [hil, hil', ↓reduceIte]

lemma off1_row_lt {a a' b : ℕ} (h : a < a') (hb : b < 74) (ha' : a' ≤ 74) :
    (triangle 74 - triangle (74 - a)) + (b - a) < triangle 74 - triangle (74 - a') := by
  have e := triangle_succ (73 - a)
  rw [show 73 - a + 1 = 74 - a by omega] at e
  have m1 := triangle_mono (show 74 - a' ≤ 73 - a by omega)
  have m2 := triangle_mono (show 74 - a ≤ 74 by omega)
  omega

lemma off1_inj {i l i' l' : Fin 74} {k k' : Fin 45} (hil : (i : ℕ) ≤ l) (hil' : (i' : ℕ) ≤ l')
    (h : off1 i l + k = off1 i' l' + k') : i = i' ∧ l = l' ∧ k = k' := by
  have hk := k.isLt
  have hk' := k'.isLt
  have hl := l.isLt
  have hl' := l'.isLt
  unfold off1 at h
  have e : (triangle 74 - triangle (74 - i)) + (l - i) =
      (triangle 74 - triangle (74 - i')) + (l' - i') ∧ (k : ℕ) = k' := by omega
  rcases lt_trichotomy (i : ℕ) i' with hlt | heq | hgt
  · have := off1_row_lt hlt hl (by omega)
    omega
  · have hb2 : (l : ℕ) = l' := by rw [heq] at e; omega
    exact ⟨Fin.ext heq, Fin.ext hb2, Fin.ext e.2⟩
  · have := off1_row_lt hgt hl' (by omega)
    omega

/-- The `P1` bytes holding `F i l k` at `off1 i l + k` (`i < l`), `0` elsewhere. -/
noncomputable def p1Region (F : Fin 74 → Fin 74 → Fin 45 → GF256) : P1Part := fun n =>
  ∑ x : Fin 74 × Fin 74 × Fin 45,
    if (x.1 : ℕ) < x.2.1 ∧ (n : ℕ) = off1 x.1 x.2.1 + x.2.2 then F x.1 x.2.1 x.2.2 else 0

lemma p1Region_off (F : Fin 74 → Fin 74 → Fin 45 → GF256) (i l : Fin 74) (k : Fin 45)
    (hil : (i : ℕ) < l) : p1Region F ⟨off1 i l + k, off1_lt i l k⟩ = F i l k := by
  unfold p1Region
  rw [Fintype.sum_eq_single (i, l, k) fun x hx => ?_]
  · simp [hil]
  · rw [ite_eq_right_iff]
    rintro ⟨h1, h2⟩
    obtain ⟨e1, e2, e3⟩ := off1_inj hil.le h1.le h2
    exact absurd (by rw [e1, e2, e3]) hx

/-- `Σ_{i<l} (M_{il} + M_{li}) s_{il} = Σ_{i,l} M_{il} s_{il}` for `s` symmetric with zero
diagonal. -/
lemma sum_tri_sym {n : ℕ} (M s : Fin n → Fin n → GF256) (hs : ∀ i l, s i l = s l i)
    (h0 : ∀ i, s i i = 0) :
    (∑ i : Fin n, ∑ l : Fin n, if (i : ℕ) < l then (M i l + M l i) * s i l else 0) =
      ∑ i : Fin n, ∑ l : Fin n, M i l * s i l := by
  have e : ∀ i l : Fin n, (if (i : ℕ) < l then (M i l + M l i) * s i l else 0) =
      (if (i : ℕ) < l then M i l * s i l else 0) + (if (i : ℕ) < l then M l i * s l i else 0) := by
    intro i l
    by_cases h : (i : ℕ) < l
    · simp only [h, ↓reduceIte, hs l i]; ring
    · simp [h]
  have e' : ∀ i l : Fin n, M i l * s i l =
      (if (i : ℕ) < l then M i l * s i l else 0) + (if (l : ℕ) < i then M i l * s i l else 0) := by
    intro i l
    rcases lt_trichotomy (i : ℕ) l with h | h | h
    · simp [h, show ¬ (l : ℕ) < i by omega]
    · have : i = l := Fin.ext h
      subst this
      simp [h0]
    · simp [h, show ¬ (i : ℕ) < l by omega]
  calc _ = (∑ i : Fin n, ∑ l : Fin n, if (i : ℕ) < l then M i l * s i l else 0) +
        ∑ i : Fin n, ∑ l : Fin n, (if (i : ℕ) < l then M l i * s l i else 0) := by
          simp only [e, Finset.sum_add_distrib]
    _ = (∑ i : Fin n, ∑ l : Fin n, if (i : ℕ) < l then M i l * s i l else 0) +
        ∑ i : Fin n, ∑ l : Fin n, (if (l : ℕ) < i then M i l * s i l else 0) := by
          congr 1
          rw [Finset.sum_comm]
    _ = _ := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun l _ => (e' i l).symm

/-- The values of the polar form of `P₁` on two families, as an additive map of the bytes. -/
noncomputable def bqHom (v v' : Fin 9 → Vin) : P1Part →+ (Fin 9 → Fin 9 → Tgt) where
  toFun p i j := bq p (v i) (v' j)
  map_zero' := by funext i j k; simp [bq]
  map_add' p p' := by
    funext i j k
    simp only [bq, Pi.add_apply, add_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp

/-- **Interpolation for the vinegar part**: the values `B₁(v_i, v'_j)` of the polar form of a
uniform `P1` on `18` independent vectors are uniform and independent. -/
theorem bqHom_surjective {v v' : Fin 9 → Vin} (h : LinearIndependent GF256 (Sum.elim v v')) :
    Function.Surjective (bqHom v v') := by
  classical
  intro τ
  let H : (Fin 74 → Fin 74 → Tgt) →+ (Fin 9 ⊕ Fin 9 → Fin 9 ⊕ Fin 9 → Tgt) :=
    (AddMonoidHom.compLeft (evHom (S := Tgt) (Sum.elim v v')) _).comp (evHom (Sum.elim v v'))
  have hH : Function.Surjective H := by
    have h3 : Function.Surjective
        (AddMonoidHom.compLeft (evHom (S := Tgt) (Sum.elim v v')) (Fin 9 ⊕ Fin 9)) :=
      Function.Surjective.comp_left (evHom_surjective h)
    simp only [H, AddMonoidHom.coe_comp]
    exact h3.comp (evHom_surjective h)
  obtain ⟨U, hU⟩ := hH fun s s' => Sum.elim (fun i => Sum.elim (fun _ => 0) (fun j => τ i j) s')
    (fun _ => 0) s
  have hUb : ∀ (x y : Vin) (k : Fin 45), ev (ev U x) y k =
      ∑ i : Fin 74, ∑ l : Fin 74, U i l k * (x i * y l) := by
    intro x y k
    simp only [ev, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  refine ⟨p1Region fun i l k => U i l k + U l i k, ?_⟩
  funext i j k
  have h1 : bq (p1Region fun i l k => U i l k + U l i k) (v i) (v' j) k =
      ev (ev U (v i)) (v' j) k + ev (ev U (v' j)) (v i) k := by
    rw [hUb, hUb, ← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib, ← mul_add]
    rw [← sum_tri_sym (fun a b => U a b k) (fun a b => v i a * v' j b + v' j a * v i b)
      (fun a b => by ring) (fun a => by rw [mul_comm (v' j a)]; exact gf_add_self _)]
    simp only [bq]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : (a : ℕ) < b
    · simp only [hab, ↓reduceIte, p1Region_off _ a b k hab]
    · simp only [hab, ↓reduceIte]
  have h2 := congrFun (congrFun (congrFun hU (Sum.inl i)) (Sum.inr j)) k
  have h3 := congrFun (congrFun (congrFun hU (Sum.inr j)) (Sum.inl i)) k
  show bq _ (v i) (v' j) k = τ i j k
  rw [h1]
  have h2' : ev (ev U (v i)) (v' j) k = τ i j k := h2
  have h3' : ev (ev U (v' j)) (v i) k = 0 := h3
  rw [h2', h3', add_zero]

end VoleMole.Assumptions.SymmetryScalar
