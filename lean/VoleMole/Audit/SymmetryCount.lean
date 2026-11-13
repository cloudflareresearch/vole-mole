import VoleMole.Assumptions.SymmetryCount

/-!
# Non-vacuity of the symmetry count (Theorem T3, translation part)

`Assumptions/SymmetryCount.lean` (`lean/docs/security/ompr-shift-algebra.md` §3.1, §8.4).

* **Good keys exist for every oil matrix and `P1` part**: some `P2` gives a key with both a trivial
  radical and spanning values of `B` (`exists_good_key`, from the two counts).
* **The class of pairs in `no_translation` is inhabited**: the scaling `(λ·I, λ²·I)`, `λ ≠ 0`, with
  `a = 0`, `c = 0` satisfies all its hypotheses (`scaling_pair_hyps`); `no_translation` then says
  nothing new about it, as it must.
* **`scaling_target` is not vacuous**: its hypothesis holds for `T = λ²·I`, which it returns.
-/

open Finset

namespace VoleMole.Audit.SymmetryCount

open VoleMole.Spec VoleMole.Spec.Pqov VoleMole.Arith VoleMole.Privacy VoleMole.Privacy.Moussaka
  VoleMole.Assumptions.SymmetryCount

variable (O : OilMat) (P1 : ℕ → GF256)

/-- **Some `P2` gives a key with a trivial radical and spanning values of `B`.** -/
theorem exists_good_key :
    ∃ P2 : P2Part, RadTriv (pqovKey O P1 P2) ∧ SpanTriv (pqovKey O P1 P2) := by
  by_contra h
  push Not at h
  have h1 : pr P2Part (fun P2 => ¬ RadTriv (pqovKey O P1 P2) ∨ ¬ SpanTriv (pqovKey O P1 P2)) = 1 := by
    rw [pr_congr (Q := fun _ => True) fun P2 => ⟨fun _ => trivial, fun _ => by
      by_cases hR : RadTriv (pqovKey O P1 P2)
      · exact Or.inr (h P2 hR)
      · exact Or.inl hR⟩, pr_const]
    simp
  have h2 := (pr_or_le _ _).trans (add_le_add (pr_not_radTriv O P1) (pr_not_spanTriv O P1))
  rw [h1] at h2
  have a1 : (1 : ℝ) / 256 ^ 1951 ≤ 1 / 256 := by
    gcongr; exact le_self_pow₀ (by norm_num) (by norm_num)
  have a2 : (1 : ℝ) / 256 ^ 3285 ≤ 1 / 256 := by
    gcongr; exact le_self_pow₀ (by norm_num) (by norm_num)
  have : (1 : ℝ) / 256 ^ 1951 + 1 / 256 ^ 3285 + 1 / 256 ^ 3285 < 1 :=
    calc (1 : ℝ) / 256 ^ 1951 + 1 / 256 ^ 3285 + 1 / 256 ^ 3285 ≤ 1 / 256 + 1 / 256 + 1 / 256 :=
          add_le_add (add_le_add a1 a2) a2
      _ < 1 := by norm_num
  exact absurd h2 (not_le.mpr this)

/-- **The scaling pairs satisfy the hypotheses of `no_translation`.** -/
theorem scaling_pair_hyps (pk : UOVKey) {l : GF256} (hl : l ≠ 0) :
    (∀ (μ : GF256) (s : ℕ → GF256), l • (μ • s) = μ • (l • s)) ∧
      (∀ (μ : GF256) (y : Fin 45 → GF256), l ^ 2 • (μ • y) = μ • (l ^ 2 • y)) ∧
      Function.Surjective (fun s : ℕ → GF256 => l • s) ∧
      ∀ s, qmap pk (l • s + 0) = l ^ 2 • qmap pk s + 0 := by
  refine ⟨fun μ s => smul_comm l μ s, fun μ y => smul_comm _ μ y, fun u => ⟨l⁻¹ • u, ?_⟩,
    fun s => by rw [add_zero, add_zero, qmap_smul]⟩
  show l • (l⁻¹ • u) = u
  rw [smul_smul, mul_inv_cancel₀ hl, one_smul]

/-- `no_translation` applies to the scaling pairs (and gives `c = 0`, as it must). -/
example (pk : UOVKey) (hR : RadTriv pk) {l : GF256} (hl : l ≠ 0) :=
  let h := scaling_pair_hyps pk hl
  no_translation pk hR (fun s => l • s) 0 (fun y => l ^ 2 • y) 0 h.1 h.2.1 h.2.2.1 h.2.2.2

/-- `scaling_target` applies to `T = λ²·I`. -/
example (pk : UOVKey) (hS : SpanTriv pk) (l : GF256) :=
  scaling_target pk hS l (l ^ 2 • LinearMap.id) fun s => by
    rw [qmap_smul]; rfl

end VoleMole.Audit.SymmetryCount
