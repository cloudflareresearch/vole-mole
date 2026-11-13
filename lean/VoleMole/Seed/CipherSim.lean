import Mathlib

/-!
# Q4: combinatorial and arithmetic cores of the efficient ideal-cipher simulator

This file supports `lean/docs/extraction/Q4-efficient-cipher-simulation.md`.

The simulator there is `E_k = A_{F(k)} ∘ ρ_k`, where
- `F` is a compressed random oracle into the affine group `AGL(1, GF(2^128))`;
- `ρ_k` is a sometimes-recurse / swap-or-not permutation (Morris–Rogaway 2014) keyed by `k`.

Two facts used there are checked here.

1. **Exact fibre density (§3 of the note).** The affine group of a field is sharply 2-transitive.
   For `z₀ ≠ z₁` and `c₀ ≠ c₁` there is exactly one `(a, b)` with `a ≠ 0` mapping `z₀ ↦ c₀` and
   `z₁ ↦ c₁`; for `c₀ = c₁` there is none (`affine_two_point_existsUnique`,
   `affine_two_point_none`). Hence for every fixed `ρ_k` the commitment
   `A_y(ρ_k(x₀)) ‖ A_y(ρ_k(x₁))` hits each admissible target for exactly one of the
   `(|F| - 1)·|F|` group elements `y` (`affine_two_point_card`). That is the density
   `p = 1/(N(N-1))` of Q1, exactly, whatever `ρ` is.

2. **Round counts (§2 of the note).** The swap-or-not bound of Hoang–Morris–Rogaway (as restated
   in Morris–Rogaway 2014, eq. (1)) is
   `Δ_SN(M, M/2, r) ≤ (2 M^{3/2}/(r+2)) · (3/4)^{r/2+1}`.
   With `r = 2354` rounds per stage, this is at most `2^{-300}/127` for every stage size
   `M = 2^j`, `j ≤ 128` (`sn_stage_bound`). Summing over the 127 nontrivial stages
   (Morris–Rogaway 2014, Thm. 3) gives total-variation distance `≤ 2^{-300}` from a uniform
   permutation of `{0,1}^128`. The check is done in `ℕ` after squaring, to avoid `M^{3/2}`.
-/

namespace VoleMole.Seed.CipherSim

section Affine

variable {F : Type*} [Field F]

/-- Sharp 2-transitivity of the affine group: existence and uniqueness of the affine map
`z ↦ a*z + b` (`a ≠ 0`) sending `z₀ ↦ c₀`, `z₁ ↦ c₁`, for `z₀ ≠ z₁` and `c₀ ≠ c₁`. -/
theorem affine_two_point_existsUnique (z₀ z₁ c₀ c₁ : F) (hz : z₀ ≠ z₁) (hc : c₀ ≠ c₁) :
    ∃! ab : F × F, ab.1 ≠ 0 ∧ ab.1 * z₀ + ab.2 = c₀ ∧ ab.1 * z₁ + ab.2 = c₁ := by
  have hz' : z₀ - z₁ ≠ 0 := sub_ne_zero.mpr hz
  have hc' : c₀ - c₁ ≠ 0 := sub_ne_zero.mpr hc
  refine ⟨((c₀ - c₁) / (z₀ - z₁), c₀ - (c₀ - c₁) / (z₀ - z₁) * z₀), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact div_ne_zero hc' hz'
  · ring
  · field_simp
    ring
  · rintro ⟨a, b⟩ ⟨-, h₀, h₁⟩
    have ha : a = (c₀ - c₁) / (z₀ - z₁) := by
      rw [eq_div_iff hz']
      linear_combination h₀ - h₁
    have hb : b = c₀ - (c₀ - c₁) / (z₀ - z₁) * z₀ := by
      rw [← ha]
      linear_combination h₀
    simp [ha, hb]

/-- If the two targets coincide, no affine bijection reaches them from distinct points. -/
theorem affine_two_point_none (z₀ z₁ c : F) (hz : z₀ ≠ z₁) (a b : F) (ha : a ≠ 0) :
    ¬ (a * z₀ + b = c ∧ a * z₁ + b = c) := by
  rintro ⟨h₀, h₁⟩
  have : a * (z₀ - z₁) = 0 := by linear_combination h₀ - h₁
  rcases mul_eq_zero.mp this with h | h
  · exact ha h
  · exact hz (sub_eq_zero.mp h)

/-- Counting form: among all `(a, b)` with `a ≠ 0` (there are `(|F|-1)·|F|` of them), exactly one
maps `(z₀, z₁) ↦ (c₀, c₁)` when both pairs are distinct. -/
theorem affine_two_point_card [Fintype F] [DecidableEq F] (z₀ z₁ c₀ c₁ : F) (hz : z₀ ≠ z₁)
    (hc : c₀ ≠ c₁) :
    (Finset.univ.filter
        (fun ab : F × F => ab.1 ≠ 0 ∧ ab.1 * z₀ + ab.2 = c₀ ∧ ab.1 * z₁ + ab.2 = c₁)).card = 1 := by
  obtain ⟨ab, hab, huniq⟩ := affine_two_point_existsUnique z₀ z₁ c₀ c₁ hz hc
  rw [Finset.card_eq_one]
  refine ⟨ab, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun hx => huniq x hx, fun hx => hx ▸ hab⟩

/-- The number of affine bijections is `(|F| - 1)·|F|`. -/
theorem affine_group_card [Fintype F] [DecidableEq F] :
    (Finset.univ.filter (fun ab : F × F => ab.1 ≠ 0)).card =
      (Fintype.card F - 1) * Fintype.card F := by
  have : (Finset.univ.filter (fun ab : F × F => ab.1 ≠ 0)) =
      (Finset.univ.filter (fun a : F => a ≠ 0)) ×ˢ (Finset.univ : Finset F) := by
    ext ⟨a, b⟩
    simp
  rw [this, Finset.card_product, Finset.card_univ]
  congr 1
  rw [Finset.filter_ne' Finset.univ (0 : F), Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]

end Affine

section Rounds

set_option exponentiation.threshold 5000

/-- Squared, cross-multiplied form of
`(2 M^{3/2}/(r+2)) · (3/4)^{r/2+1} ≤ 2^{-300}/127` for `M = 2^128`, `r = 2354`
(so `r/2 + 1 = 1178`):
`(2 · 127 · 2^300)² · M³ · 3^{2·1178} ≤ (r+2)² · 4^{2·1178}`. -/
theorem sn_top_stage_bound :
    (2 * 127 * 2 ^ 300) ^ 2 * (2 ^ 128) ^ 3 * 3 ^ (2 * 1178) ≤ (2354 + 2) ^ 2 * 4 ^ (2 * 1178) := by
  norm_num

/-- The same bound for every stage size `M = 2^j` with `j ≤ 128` (the bound is monotone in `M`). -/
theorem sn_stage_bound (j : ℕ) (hj : j ≤ 128) :
    (2 * 127 * 2 ^ 300) ^ 2 * (2 ^ j) ^ 3 * 3 ^ (2 * 1178) ≤ (2354 + 2) ^ 2 * 4 ^ (2 * 1178) := by
  refine le_trans ?_ sn_top_stage_bound
  gcongr

/-- `2354` is the least even round count that works for the top stage. -/
theorem sn_top_stage_tight :
    ¬ ((2 * 127 * 2 ^ 300) ^ 2 * (2 ^ 128) ^ 3 * 3 ^ (2 * 1177) ≤ (2352 + 2) ^ 2 * 4 ^ (2 * 1177)) := by
  norm_num

/-- Worst-case round count of the simulator's SR permutation: 127 nontrivial stages of `2354`
rounds (constant-round strategy), plus one round for the 2-card stage. -/
theorem sr_worst_case_rounds : 127 * 2354 + 1 = 298959 := by norm_num

/-- Product over all `2^128` keys: total-variation distance `≤ 2^128 · 2^{-300} = 2^{-172}`. -/
theorem keyed_tv_bound : (2 : ℚ) ^ 128 * (1 / 2 ^ 300) = 1 / 2 ^ 172 := by
  rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
  norm_num

end Rounds

end VoleMole.Seed.CipherSim
