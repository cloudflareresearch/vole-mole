import VoleMole.Assumptions.SymmetryT3

/-!
# Audit of Theorem T3 (`Assumptions/SymmetryT3.lean`)

`lean/docs/security/ompr-shift-algebra.md` §8.

* **Good keys exist for every oil matrix** (`exists_t3Good`): some `(P1, P2)` gives a key whose
  only symmetries are the scalings. So `T3Good` is satisfiable by pqov's keys and `t3` is not
  vacuous.
* **The classes of pairs are inhabited** (`scaling_group_hyps`, `scaling_inf_hyps`): the scaling
  `(λ·I, λ²·I)`, `λ ≠ 0`, satisfies every hypothesis of `T3Good.group`, and `(λ·I, 0)` that of
  `T3Good.inf`. So the conclusions of `T3Good` cannot be strengthened.
* **`P1` must be random** (`not_t3Good_p1_zero`): for the `P1` part `0`, every oil matrix `O` and
  every `P2`, the key has the non-scalar symmetry `(v, x) ↦ (v, β x)` (in the coordinates of the
  oil space) with `T = β·I`: `P(v, x) = L(v, x)` is bilinear. So Theorem T3 is false in the model
  of `Assumptions/SymmetryCount.lean` (`O`, `P1` arbitrary, `P2` uniform), and `t3` takes `P1`
  uniform as well, as the note does.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.SymmetryT3

open VoleMole.Spec VoleMole.Spec.Pqov VoleMole.Arith VoleMole.Arith.UOV VoleMole.Privacy
  VoleMole.Privacy.Moussaka VoleMole.Assumptions.SymmetryProbes
  VoleMole.Assumptions.SymmetryTensor VoleMole.Assumptions.SymmetryScalar
  VoleMole.Assumptions.SymmetryCount VoleMole.Assumptions.SymmetryT3

/-- **Some key of pqov has only the scalings as symmetries**, for every oil matrix. -/
theorem exists_t3Good (O : OilMat) : ∃ (p : P1Part) (P2 : P2Part), T3Good (pqovKey O (p1 p) P2) := by
  by_contra h
  push Not at h
  have h1 : pr (P1Part × P2Part) (fun κ => ¬ T3Good (pqovKey O (p1 κ.1) κ.2)) = 1 := by
    rw [pr_congr (Q := fun _ => True) fun κ => ⟨fun _ => trivial, fun _ => h κ.1 κ.2⟩, pr_const]
    simp
  have h2 := t3 O
  rw [h1] at h2
  have : (1 : ℝ) / 256 ^ 128 < 1 := by
    rw [div_lt_one (by positivity)]
    exact one_lt_pow₀ (by norm_num) (by norm_num)
  exact absurd h2 (not_le.mpr this)

lemma ext119_smul (l : GF256) (s : F119) : ext119 (l • s) = l • ext119 s := by
  funext n
  simp only [ext119, Pi.smul_apply]
  split_ifs <;> simp

/-- `P(λ s) = λ² P(s)` on `F^{119}`. -/
lemma P119_smul (pk : UOVKey) (l : GF256) (s : F119) : P119 pk (l • s) = l ^ 2 • P119 pk s := by
  rw [P119, ext119_smul, qmap_smul]
  rfl

/-- **The scalings satisfy the hypotheses of `T3Good.group`** (with `σ` the identity, `a = 0`,
`c = 0`). -/
theorem scaling_group_hyps (pk : UOVKey) {l : GF256} (hl : l ≠ 0) :
    (∀ s u : F119, l • (s + u) = l • s + l • u) ∧
      (∀ (μ : GF256) (s : F119), l • (μ • s) = RingHom.id GF256 μ • (l • s)) ∧
      (∀ y z : Tgt, l ^ 2 • (y + z) = l ^ 2 • y + l ^ 2 • z) ∧
      (∀ (μ : GF256) (y : Tgt), l ^ 2 • (μ • y) = RingHom.id GF256 μ • (l ^ 2 • y)) ∧
      Function.Bijective (fun s : F119 => l • s) ∧
      ∀ s, P119 pk (l • s + 0) = l ^ 2 • P119 pk s + 0 := by
  refine ⟨fun s u => smul_add l s u, fun μ s => smul_comm l μ s, fun y z => smul_add _ y z,
    fun μ y => smul_comm _ μ y, ⟨fun s u h => ?_, fun u => ⟨l⁻¹ • u, ?_⟩⟩,
    fun s => by rw [add_zero, add_zero, P119_smul]⟩
  · have := congrArg (fun w : F119 => l⁻¹ • w) h
    simpa [smul_smul, inv_mul_cancel₀ hl] using this
  · show l • (l⁻¹ • u) = u
    rw [smul_smul, mul_inv_cancel₀ hl, one_smul]

/-- `T3Good.group` applies to the scalings, and returns them. -/
example (pk : UOVKey) (hG : T3Good pk) {l : GF256} (hl : l ≠ 0) :=
  let h := scaling_group_hyps pk hl
  hG.group (RingHom.id GF256) (fun s => l • s) 0 (fun y => l ^ 2 • y) 0 h.1 h.2.1 h.2.2.1
    h.2.2.2.1 (Or.inl h.2.2.2.2.1) h.2.2.2.2.2

/-- **`(λ·I, 0)` satisfies the hypothesis of `T3Good.inf`**: `B(s, λ s) = 0`. -/
theorem scaling_inf_hyps (pk : UOVKey) (l : GF256) (s : F119) :
    B119 pk s ((l • LinearMap.id : F119 →ₗ[GF256] F119) s) =
      (0 : Tgt →ₗ[GF256] Tgt) (P119 pk s) := by
  show polar pk (ext119 s) (ext119 (l • s)) = 0
  rw [ext119_smul, scaling_infinitesimal]

/-- **`P1` must be random.** For the `P1` part `0`, every oil matrix and every `P2` part, the key
has a symmetry that is not a scaling: Theorem T3 fails for it. -/
theorem not_t3Good_p1_zero (O : OilMat) (P2 : P2Part) : ¬ T3Good (pqovKey O (p1 0) P2) := by
  intro hG
  obtain ⟨β, hβ0, hβ1⟩ := exists_ne_zero_one
  let e := adEquiv O
  let D : Vin × Oil → Vin × Oil := fun z => (z.1, β • z.2)
  have hQ0 : ∀ v : Vin, qmap (pqovKey O (p1 0) P2) (vinVec v) = 0 := by
    intro v
    funext k
    rw [qmap_vinVec_eq]
    simp [c1_pqovKey, c1_keyP12, p1]
  have hP : ∀ z : Vin × Oil, P119 (pqovKey O (p1 0) P2) (e.symm (D z)) =
      β • P119 (pqovKey O (p1 0) P2) (e.symm z) := by
    intro z
    rw [P119_symm, P119_symm]
    simp only [VoleMole.Assumptions.SymmetryScalar.PA, hQ0, zero_add, D, bil_smul_right]
  have hDb : Function.Bijective D := by
    refine ⟨fun z z' h => ?_, fun z => ⟨(z.1, β⁻¹ • z.2), ?_⟩⟩
    · have h1 := congrArg Prod.fst h
      have h2 := congrArg (fun w : Vin × Oil => β⁻¹ • w.2) h
      simp only [D, smul_smul, inv_mul_cancel₀ hβ0, one_smul] at h1 h2
      exact Prod.ext h1 h2
    · simp only [D, smul_smul, mul_inv_cancel₀ hβ0, one_smul]
  obtain ⟨-, -, -, l, -, hA, -⟩ := hG.group (RingHom.id GF256) (fun s => e.symm (D (e s))) 0
    (fun y => β • y) 0
    (fun s u => by simp only [D, map_add, Prod.fst_add, Prod.snd_add, smul_add, ← Prod.mk_add_mk])
    (fun μ s => by
      simp only [D, map_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_comm β μ,
        ← Prod.smul_mk])
    (fun y z => smul_add β y z) (fun μ y => smul_comm β μ y)
    (Or.inl (e.symm.bijective.comp (hDb.comp e.bijective)))
    (fun s => by
      rw [add_zero, add_zero, hP, LinearEquiv.symm_apply_apply])
  have hD : ∀ z : Vin × Oil, D z = l • z := by
    intro z
    have := hA (e.symm z)
    simp only [LinearEquiv.apply_symm_apply] at this
    rw [← map_smul] at this
    exact e.symm.injective this
  have h1 := congrArg (fun w : Vin × Oil => w.1 0) (hD (Pi.single 0 1, 0))
  have h2 := congrArg (fun w : Vin × Oil => w.2 0) (hD (0, Pi.single 0 1))
  simp only [D, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
    mul_one] at h1 h2
  exact hβ1 (h2.trans h1.symm)

end VoleMole.Audit.SymmetryT3
