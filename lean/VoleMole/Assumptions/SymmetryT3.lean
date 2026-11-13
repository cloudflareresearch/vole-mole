import VoleMole.Assumptions.SymmetryScalar

/-!
# Theorem T3 over pqov's keys

WIP header.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Assumptions.SymmetryT3

open VoleMole.Spec VoleMole.Spec.Pqov VoleMole.Arith VoleMole.Arith.UOV VoleMole.Privacy
  VoleMole.Privacy.Moussaka VoleMole.Assumptions.SymmetryProbes
  VoleMole.Assumptions.SymmetryTensor VoleMole.Assumptions.SymmetryScalar
  VoleMole.Assumptions.SymmetryCount Module Matrix

/-- The domain `F^{119}` of the public map. -/
abbrev F119 := Fin 119 → GF256

/-- A vector of `F^{119}` as a sequence (zero from `119`). -/
def ext119 (s : F119) : ℕ → GF256 := fun n => if h : n < 119 then s ⟨n, h⟩ else 0

/-- **The public map** on `F^{119}`. -/
def P119 (pk : UOVKey) (s : F119) : Tgt := qmap pk (ext119 s)

/-- **Its polar form** on `F^{119}`. -/
def B119 (pk : UOVKey) (s u : F119) : Tgt := polar pk (ext119 s) (ext119 u)

/-- The vector with vinegar part `v` and oil coordinates `x`: `(v, 0) + Σ_j x_j ō_j`. -/
noncomputable def emb (O : OilMat) (z : Vin × Oil) : ℕ → GF256 := vinVec z.1 + oilComb O z.2

/-- **The coordinates of the oil space**: `s = (v, 0) + Σ_j x_j ō_j ↔ (v, x)`, a linear
bijection of `F^{119}`. -/
noncomputable def adEquiv (O : OilMat) : F119 ≃ₗ[GF256] (Vin × Oil) where
  toFun s := (fun i => s ⟨i, by omega⟩ - ∑ j : Fin 45, s ⟨74 + j, by omega⟩ * O j i,
    fun j => s ⟨74 + j, by omega⟩)
  map_add' s u := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => rfl)
    simp only [Pi.add_apply, Prod.fst_add, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c s := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => rfl)
    simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_fst, RingHom.id_apply, mul_sub,
      Finset.mul_sum, mul_assoc]
  invFun z := fun n => if h : (n : ℕ) < 74 then z.1 ⟨n, h⟩ + ∑ j : Fin 45, z.2 j * O j ⟨n, h⟩
    else z.2 ⟨n - 74, by omega⟩
  left_inv s := by
    funext n
    by_cases h : (n : ℕ) < 74
    · simp only [h, ↓reduceDIte, Fin.eta, sub_add_cancel]
    · simp only [h, ↓reduceDIte]
      congr 1
      exact Fin.ext (by simp only; omega)
  right_inv z := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · have hi : (i : ℕ) < 74 := i.isLt
      have hj : ∀ j : Fin 45, ¬ 74 + (j : ℕ) < 74 := fun j => by omega
      simp only [hi, ↓reduceDIte, Fin.eta, hj, Nat.add_sub_cancel_left, add_sub_cancel_right]
    · have hj : ¬ 74 + (j : ℕ) < 74 := by omega
      simp only [hj, ↓reduceDIte, Nat.add_sub_cancel_left, Fin.eta]

/-- On the first `119` coordinates, the inverse of `adEquiv` is `emb`. -/
lemma ext119_symm (O : OilMat) (z : Vin × Oil) {n : ℕ} (hn : n < 119) :
    ext119 ((adEquiv O).symm z) n = emb O z n := by
  simp only [ext119, hn, ↓reduceDIte, emb, Pi.add_apply, oilComb, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, vinVec, oilVec]
  show (if h : n < 74 then z.1 ⟨n, h⟩ + ∑ j : Fin 45, z.2 j * O j ⟨n, h⟩
    else z.2 ⟨n - 74, by omega⟩) = _
  by_cases h : n < 74
  · simp only [h, ↓reduceDIte]
  · simp only [h, ↓reduceDIte, zero_add]
    rw [Finset.sum_eq_single ⟨n - 74, by omega⟩ (fun b _ hb => by
      have : n ≠ 74 + b.val := fun e => hb (Fin.ext (by simp; omega))
      simp [this]) (by simp)]
    have : n = 74 + (n - 74) := by omega
    simp [← this]

section Key

variable (O : OilMat) (p : P1Part) (P2 : P2Part)

/-- `B((v, 0), Σ_j x_j ō_j) = L(v, x)` with the tensor `S` of the key. -/
lemma polar_vin_oil (v : Vin) (x : Oil) :
    polar (pqovKey O (p1 p) P2) (vinVec v) (oilComb O x) = bil (sEquiv O (p1 p) P2) v x := by
  funext k
  rw [oilComb, polar_sum_right, bil_eq_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : polar (pqovKey O (p1 p) P2) (vinVec v) (oilVec O j) k =
      sysMat (pqovKey O (p1 p) P2) O v k j := rfl
  rw [e, sysMat_pqovKey]
  simp only [lin, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma vinVec_add (v w : Vin) : vinVec (v + w) = vinVec v + vinVec w := by
  funext n; simp only [vinVec, Pi.add_apply]; split_ifs <;> simp

lemma vinVec_smul (c : GF256) (v : Vin) : vinVec (c • v) = c • vinVec v := by
  funext n; simp only [vinVec, Pi.smul_apply]; split_ifs <;> simp

/-- The vinegar part of pqov's key is a quadratic map with polar form `bq p`. -/
lemma quadV : QuadV (fun v => qmap (pqovKey O (p1 p) P2) (vinVec v)) (bq p) := by
  refine ⟨fun v w => ?_, fun c v => ?_, fun v v' w => ?_, fun c v w => ?_, fun v w => ?_,
    fun v => ?_⟩
  · rw [vinVec_add, qmap_add, polar_vinVec]
  · rw [vinVec_smul, qmap_smul]
  · rw [← polar_vinVec O p P2, ← polar_vinVec O p P2, ← polar_vinVec O p P2, vinVec_add,
      polar_add_left]
  · rw [← polar_vinVec O p P2, ← polar_vinVec O p P2, vinVec_smul, polar_smul_left]
  · rw [← polar_vinVec O p P2, ← polar_vinVec O p P2, polar_comm]
  · rw [← polar_vinVec O p P2, polar_self]

/-- **The key in the coordinates of its oil space**: `P(v, x) = P₁(v) + L(v, x)`. -/
lemma qmap_emb (z : Vin × Oil) :
    qmap (pqovKey O (p1 p) P2) (emb O z) =
      PA (fun v => qmap (pqovKey O (p1 p) P2) (vinVec v)) (sEquiv O (p1 p) P2) z := by
  rw [emb, qmap_add, show qmap (pqovKey O (p1 p) P2) (oilComb O z.2) = 0 from
    oilSpace_pqovKey O (p1 p) P2 z.2, add_zero, polar_vin_oil]
  rfl

/-- The polar form in the coordinates of the oil space. -/
lemma polar_emb (z z' : Vin × Oil) :
    polar (pqovKey O (p1 p) P2) (emb O z) (emb O z') =
      BA (bq p) (sEquiv O (p1 p) P2) z z' := by
  rw [emb, emb, polar_add_left, polar_add_right, polar_add_right, polar_vinVec, polar_vin_oil,
    polar_oilComb _ O (oilSpace_pqovKey O (p1 p) P2), add_zero,
    polar_comm _ (oilComb O z.2), polar_vin_oil]
  rfl

lemma P119_symm (z : Vin × Oil) :
    P119 (pqovKey O (p1 p) P2) ((adEquiv O).symm z) =
      PA (fun v => qmap (pqovKey O (p1 p) P2) (vinVec v)) (sEquiv O (p1 p) P2) z := by
  rw [P119, qmap_congr _ (τ := emb O z) fun i hi => ext119_symm O z hi, qmap_emb]

lemma B119_symm (z z' : Vin × Oil) :
    B119 (pqovKey O (p1 p) P2) ((adEquiv O).symm z) ((adEquiv O).symm z') =
      BA (bq p) (sEquiv O (p1 p) P2) z z' := by
  rw [B119, polar_congr_left _ (a' := emb O z) fun i hi => ext119_symm O z hi, polar_comm,
    polar_congr_left _ (a' := emb O z') fun i hi => ext119_symm O z' hi, polar_comm, polar_emb]

end Key

/-! ## Theorem T3 -/

/-- **The conclusion of Theorem T3** for a key `pk`, on `F^{119}`.

* `group`: every pair `φ(s) = A s + a`, `Θ(y) = T y + c` with `P ∘ φ = Θ ∘ P`, where `A` and `T`
  are additive and `σ`-semilinear for a ring endomorphism `σ` of `GF(256)` (the identity: linear
  maps; a power of the Frobenius: semilinear maps) and `A` is bijective or `T` injective, is a
  scaling: `σ` is the identity, `a = 0`, `c = 0`, `A = λ·I` and `T = λ²·I` with `λ ≠ 0`.
* `inf`: every infinitesimal pair `B(s, X s) = Y(P s)` with `X`, `Y` linear is `(λ·I, 0)`. -/
structure T3Good (pk : UOVKey) : Prop where
  group : ∀ (σ : GF256 →+* GF256) (A : F119 → F119) (a : F119) (T : Tgt → Tgt) (c : Tgt),
    (∀ s u, A (s + u) = A s + A u) → (∀ (l : GF256) s, A (l • s) = σ l • A s) →
    (∀ y z, T (y + z) = T y + T z) → (∀ (l : GF256) y, T (l • y) = σ l • T y) →
    (Function.Bijective A ∨ Function.Injective T) →
    (∀ s, P119 pk (A s + a) = T (P119 pk s) + c) →
    (∀ x, σ x = x) ∧ a = 0 ∧ c = 0 ∧
      ∃ l : GF256, l ≠ 0 ∧ (∀ s, A s = l • s) ∧ ∀ y, T y = l ^ 2 • y
  inf : ∀ (X : F119 →ₗ[GF256] F119) (Y : Tgt →ₗ[GF256] Tgt),
    (∀ s, B119 pk s (X s) = Y (P119 pk s)) → ∃ l : GF256, X = l • LinearMap.id ∧ Y = 0

/-- **The bad keys**: the tensor `S` of the key is not good, or one of the two events on its
vinegar part `P₁` holds. -/
def BadKey (z : P1Part × Coef) : Prop := ¬ GoodS z.2 ∨ IsoQ (bq z.1) z.2 ∨ DetQ (bq z.1) z.2

/-- **Theorem T3, deterministic part**: a key of pqov that is not bad has only the scalings as
symmetries and only `F·(I, 0)` as infinitesimal symmetries. -/
theorem t3Good_of_not_bad (O : OilMat) (p : P1Part) (P2 : P2Part)
    (h : ¬ BadKey (p, sEquiv O (p1 p) P2)) : T3Good (pqovKey O (p1 p) P2) := by
  simp only [BadKey, not_or, not_not] at h
  obtain ⟨hS, hI, hD⟩ := h
  have hQ := quadV O p P2
  refine ⟨fun σ A a T c hAa hAs hTa hTs hb hsym => ?_, fun X Y hinf => ?_⟩
  · obtain ⟨hσ, ha, hc, l, hl, hA, hT⟩ := adapted_affine hQ hS hI hD σ
      (fun z => adEquiv O (A ((adEquiv O).symm z))) (adEquiv O a) T c
      (fun s u => by simp only [map_add, hAa])
      (fun l s => by simp only [map_smul, hAs])
      hTa hTs
      (hb.imp (fun hA => (adEquiv O).bijective.comp (hA.comp (adEquiv O).symm.bijective)) id)
      (fun z => by
        rw [← map_add, ← P119_symm, ← P119_symm, LinearEquiv.symm_apply_apply]
        exact hsym _)
    refine ⟨hσ, (adEquiv O).map_eq_zero_iff.1 ha, hc, l, hl, fun s => ?_, hT⟩
    have := hA (adEquiv O s)
    rw [LinearEquiv.symm_apply_apply, ← map_smul] at this
    exact (adEquiv O).injective this
  · obtain ⟨l, hX, hY⟩ := adapted_lie hQ hS hD
      ((adEquiv O).toLinearMap ∘ₗ X ∘ₗ (adEquiv O).symm.toLinearMap) Y (fun z => by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [← B119_symm, ← P119_symm, LinearEquiv.symm_apply_apply]
        exact hinf _)
    refine ⟨l, LinearMap.ext fun s => ?_, LinearMap.ext hY⟩
    have := hX (adEquiv O s)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
    rw [← map_smul] at this
    exact (adEquiv O).injective this

/-- **The bad keys are rare**: over a uniform `P1` part and a uniform tensor `S`. -/
theorem pr_badKey : pr (P1Part × Coef) BadKey ≤ 1 / 256 ^ 128 := by
  have h1 : pr (P1Part × Coef) (fun z => ¬ GoodS z.2) ≤ 11 / 256 ^ 129 := by
    rw [pr_prod_snd (fun S => ¬ GoodS S)]
    exact pr_not_goodS
  have h2 : pr (P1Part × Coef) (fun z => IsoQ (bq z.1) z.2) ≤ 1 / 256 ^ 129 := by
    rw [← pr_equiv (Equiv.prodComm Coef P1Part) (fun z => IsoQ (bq z.1) z.2)]
    exact le_129 (by norm_num) (pr_prod_le _ fun S => pr_isoQ S)
  have h3 : pr (P1Part × Coef) (fun z => DetQ (bq z.1) z.2) ≤ 1 / 256 ^ 129 := by
    rw [← pr_equiv (Equiv.prodComm Coef P1Part) (fun z => DetQ (bq z.1) z.2)]
    exact le_129 (by norm_num) (pr_prod_le _ fun S => pr_detQ S)
  refine ((pr_or_le _ _).trans (add_le_add h1 ((pr_or_le _ _).trans (add_le_add h2 h3)))).trans ?_
  rw [show (256 : ℝ) ^ 129 = 256 * 256 ^ 128 by rw [← pow_succ']]
  have hpos : (0 : ℝ) < 256 ^ 128 := by positivity
  generalize (256 : ℝ) ^ 128 = X at hpos ⊢
  have e : 11 / (256 * X) + (1 / (256 * X) + 1 / (256 * X)) = 13 / 256 * (1 / X) := by
    field_simp
    norm_num
  rw [e]
  have hX : 0 ≤ 1 / X := by positivity
  nlinarith

/-- **Theorem T3** (`lean/docs/security/ompr-shift-algebra.md` §8) over pqov's keys
`pqovKey O P1 P2`, for every oil matrix `O`, with the `P1` and `P2` parts uniform: except with
probability `≤ 256^{−128} = 2^{−1024}`, the only pairs `φ(s) = A s + a`, `Θ(y) = T y + c` with
`P ∘ φ = Θ ∘ P`, `A`, `T` additive and linear or Frobenius-semilinear, and `A` bijective or `T`
injective, are the scalings `(λ·I, λ²·I)`; and the only infinitesimal pairs are `F·(I, 0)`. -/
theorem t3 (O : OilMat) :
    pr (P1Part × P2Part) (fun κ => ¬ T3Good (pqovKey O (p1 κ.1) κ.2)) ≤ 1 / 256 ^ 128 := by
  refine (pr_mono (Q := fun κ : P1Part × P2Part =>
    BadKey (Equiv.prodShear (Equiv.refl P1Part) (fun p => sEquiv O (p1 p)) κ))
    fun κ h => ?_).trans ?_
  · by_contra hb
    exact h (t3Good_of_not_bad O κ.1 κ.2 hb)
  · rw [pr_equiv (Equiv.prodShear (Equiv.refl P1Part) (fun p => sEquiv O (p1 p))) BadKey]
    exact pr_badKey

end VoleMole.Assumptions.SymmetryT3
