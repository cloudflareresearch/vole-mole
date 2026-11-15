import VoleMole.Theft.NumLin

/-!
# What the joint step gives with the overlap factor

`jointNum_le` (`Theft/NumLin.lean`) evaluates the joint bound `(Σ c + J)/(1 − N·B) + r` with the
budget charge `J` at most **one** hop's `zkB`. The overlap count of the `iv`s
(`ZK.Sim.exP_sum_inY_le`, `ZK.Sim.exP_sum_qkeys_tab_le`) charges the budget once **times**
`1 + N²·2⁻⁶⁴` (two `iv`s with equal middle bytes share every read at their common CTR blocks),
up to `5/4` at `N = 2³¹`. The target `2⁻⁵⁴` is still reached:

* **`overlap_le`**: `1 + N²·2⁻⁶⁴ ≤ 5/4` for `N ≤ 2³¹`;
* **`jointNumK_le`**: with `J ≤ (1 + N²·2⁻⁶⁴)·zkB(2⁶⁵, 2⁶⁵ + 2⁴¹, 2⁶⁵ + 2⁵⁰)` (and the other terms as in
  `jointNum_le`), `N·B < 1` and `(a + J)/(1 − N·B) + r ≤ 2⁻⁵⁴`. Numerically the left side is about
  `(5/4·223 + 13)·2⁻⁶³ ≈ 2⁻⁵⁴·⁸`.
-/

namespace VoleMole.Theft

open VoleMole.Privacy

set_option exponentiation.threshold 1100 in
/-- **The overlap factor at `N ≤ 2³¹`** is at most `5/4`. -/
lemma overlap_le {N : ℕ} (hN : N ≤ 2 ^ 31) : 1 + (N : ℝ) ^ 2 / 2 ^ 64 ≤ 5 / 4 := by
  have hN' : (N : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hN
  have : (N : ℝ) ^ 2 ≤ (2 ^ 31) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN' 2
  have : (N : ℝ) ^ 2 / 2 ^ 64 ≤ (2 ^ 31) ^ 2 / 2 ^ 64 := div_le_div_of_nonneg_right this (by positivity)
  norm_num at this ⊢
  linarith

set_option exponentiation.threshold 1100 in
/-- **The joint step with the overlap factor, numerically.** With `N ≤ 2³¹` proofs, the per-proof
terms summing to at most `N·2⁻¹⁰⁰`, the budget charge `J` at most `1 + N²·2⁻⁶⁴` times one hop's
`zkB` at the hops' budgets, the largest per-hop charge `B` at most one hop's `zkB`, and `ROM/`'s
error `r ≤ 13·2⁻⁶³`: `N·B < 1` and `(a + J)/(1 − N·B) + r ≤ 2⁻⁵⁴`. -/
lemma jointNumK_le {N : ℕ} (hN : N ≤ 2 ^ 31) {a J B r : ℝ}
    (ha : a ≤ N / 2 ^ 100)
    (hJ : J ≤ (1 + (N : ℝ) ^ 2 / 2 ^ 64) * zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50))
    (hB0 : 0 ≤ B) (hB : B ≤ zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50))
    (hr : r ≤ 13 / 2 ^ 63) :
    N * B < 1 ∧ (a + J) / (1 - N * B) + r ≤ 1 / 2 ^ 54 := by
  set Z := zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50)
  have hZ0 : 0 ≤ Z := zkB_nonneg _ _ _
  have hN' : (N : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hN
  have hz : (2 : ℝ) ^ 31 * Z ≤ 1 / 2 ^ 24 := by simp only [Z]; norm_num [zkB]
  have hNB : (N : ℝ) * B ≤ 1 / 2 ^ 24 :=
    (mul_le_mul hN' hB hB0 (by positivity)).trans hz
  have hden : (1 : ℝ) - 1 / 2 ^ 24 ≤ 1 - N * B := by linarith
  have hden0 : (0 : ℝ) < 1 - 1 / 2 ^ 24 := by norm_num
  have hK := overlap_le hN
  have hJ' : J ≤ 5 / 4 * Z := hJ.trans (mul_le_mul_of_nonneg_right hK hZ0)
  have hnum : a + J ≤ 2 ^ 31 / 2 ^ 100 + 5 / 4 * Z := by
    have : (N : ℝ) / 2 ^ 100 ≤ 2 ^ 31 / 2 ^ 100 := div_le_div_of_nonneg_right hN' (by positivity)
    linarith
  have hfin : (2 ^ 31 / 2 ^ 100 + 5 / 4 * Z) / (1 - 1 / 2 ^ 24) + 13 / 2 ^ 63 ≤ (1 : ℝ) / 2 ^ 54 := by
    simp only [Z]; norm_num [zkB]
  refine ⟨by linarith, ?_⟩
  have h1 : (a + J) / (1 - N * B) ≤ (2 ^ 31 / 2 ^ 100 + 5 / 4 * Z) / (1 - N * B) :=
    div_le_div_of_nonneg_right hnum (by linarith)
  have h2 : (2 ^ 31 / 2 ^ 100 + 5 / 4 * Z) / (1 - N * B) ≤
      (2 ^ 31 / 2 ^ 100 + 5 / 4 * Z) / (1 - 1 / 2 ^ 24) :=
    div_le_div_of_nonneg_left (by positivity) hden0 hden
  linarith

end VoleMole.Theft
