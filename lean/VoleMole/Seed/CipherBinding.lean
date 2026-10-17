import Mathlib

/-!
# Q6: binding of the `aes_ctr` leaf commitment (the `ε_multi` event)

Paper proof: `lean/docs/extraction/Q6-cipher-binding.md`. Nothing here is quantum-specific. The file checks
the real-number and counting cores that the paper's operator arguments reduce to.

## Results

* `mixed_combine` (paper §4, Lemma 4.3): a potential `A` that grows additively at quantum steps
  (`A' ≤ A + a`) and in squares at classical insertions (`A'² ≤ A² + b`) satisfies
  `A_T ≤ Σ a + √(Σ b)`. This is how classical queries become probability-additive.
* `sqrt_add_sub_sq_le` (paper §2, Lemma 2.2): `(√(i+n) − √i)² ≤ n`, used to bound the commutator of
  `Ẑ^{1/2}` with a cipher query by the first moment of the new-agreement count.
* `pivotal_subset` / `pivotal_card_le_two` (paper §4, Lemma 4.4): an agreement point is pivotal for
  at most two keys, so `Σ_k n̂_k ≤ 2 Ẑ`.
* `cross_terms_le` (paper §4): the insertion cross terms aggregate by Cauchy–Schwarz,
  `Σ 2√(g_i h_i) ≤ 2 √(Σ g) √(Σ h)`.
* Numbers (paper §5): Theorem 1 at `q = 2^{30}`, `2^{40}`, `2^{50}` for one proof, and Theorem 2
  (mixed bound, Lemma K counts) for strong and weak SE at `Q_S = q = 2^{30}`.
-/

open Finset

namespace VoleMole.Seed.CipherBinding

/-! ## The mixed telescoping lemma -/

/-- One step of the combination: if `A ≤ x + √y` then a classical step `A'² ≤ A² + b` keeps
`A' ≤ x + √(y + b)`. -/
theorem classical_step {A A' x y b : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hb : 0 ≤ b) (hle : A ≤ x + Real.sqrt y) (hstep : A' ^ 2 ≤ A ^ 2 + b) :
    A' ≤ x + Real.sqrt (y + b) := by
  have h1 : A ^ 2 ≤ (x + Real.sqrt y) ^ 2 := pow_le_pow_left₀ hA hle 2
  have hsy : Real.sqrt y ≤ Real.sqrt (y + b) := Real.sqrt_le_sqrt (by linarith)
  have hs1 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hs2 : Real.sqrt (y + b) ^ 2 = y + b := Real.sq_sqrt (by linarith)
  have h2 : (x + Real.sqrt y) ^ 2 + b ≤ (x + Real.sqrt (y + b)) ^ 2 := by
    nlinarith [Real.sqrt_nonneg y, Real.sqrt_nonneg (y + b)]
  have h3 : A' ^ 2 ≤ (x + Real.sqrt (y + b)) ^ 2 := by linarith
  have hr : 0 ≤ x + Real.sqrt (y + b) := by positivity
  exact (pow_le_pow_iff_left₀ hA' hr two_ne_zero).1 h3

/-- **Lemma 4.3 (mixed telescoping).** Steps are quantum (`quantum s`, then
`A (s+1) ≤ A s + a s`) or classical (`A (s+1)² ≤ A s² + b s`). Starting from `A 0 = 0`,
`A T ≤ Σ_{quantum} a + √(Σ_{classical} b)`. -/
theorem mixed_combine (A a b : ℕ → ℝ) (quantum : ℕ → Prop) [DecidablePred quantum]
    (hA : ∀ s, 0 ≤ A s) (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (h0 : A 0 = 0)
    (hq : ∀ s, quantum s → A (s + 1) ≤ A s + a s)
    (hc : ∀ s, ¬ quantum s → A (s + 1) ^ 2 ≤ A s ^ 2 + b s) :
    ∀ T, A T ≤ (∑ s ∈ (range T).filter quantum, a s)
      + Real.sqrt (∑ s ∈ (range T).filter (fun s => ¬ quantum s), b s) := by
  intro T
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    have hx : 0 ≤ ∑ s ∈ (range T).filter quantum, a s := sum_nonneg (fun s _ => ha s)
    have hy : 0 ≤ ∑ s ∈ (range T).filter (fun s => ¬ quantum s), b s :=
      sum_nonneg (fun s _ => hb s)
    by_cases hT : quantum T
    · rw [range_add_one, filter_insert, ite_eq_left hT, filter_insert, ite_eq_right (not_not.2 hT),
        sum_insert (by simp)]
      have := hq T hT
      linarith
    · rw [range_add_one, filter_insert, ite_eq_right hT, filter_insert, ite_eq_left hT,
        sum_insert (by simp), add_comm (b T)]
      exact classical_step (hA T) (hA (T + 1)) hx hy (hb T) ih (hc T hT)

/-! ## Lemma 2.2: the square-root increment -/

/-- `(√(i+n) − √i)² ≤ n`: the commutator of `Ẑ^{1/2}` with a query is controlled by the first
moment of the number of new agreement points. -/
theorem sqrt_add_sub_sq_le {i n : ℝ} (hi : 0 ≤ i) (hn : 0 ≤ n) :
    (Real.sqrt (i + n) - Real.sqrt i) ^ 2 ≤ n := by
  have h1 : Real.sqrt i ≤ Real.sqrt (i + n) := Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt (i + n) ≤ Real.sqrt i + Real.sqrt n := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hi, Real.sq_sqrt hn, Real.sqrt_nonneg i, Real.sqrt_nonneg n]
  have h3 : 0 ≤ Real.sqrt (i + n) - Real.sqrt i := by linarith
  calc (Real.sqrt (i + n) - Real.sqrt i) ^ 2 ≤ Real.sqrt n ^ 2 :=
        pow_le_pow_left₀ h3 (by linarith) 2
    _ = n := Real.sq_sqrt hn

/-! ## Lemma 4.4: an agreement point is pivotal for at most two keys -/

/-- If `W` is a nonempty set of witness pairs for a point and `k` lies in every pair (`k` is
pivotal), then `k` is a coordinate of any fixed witness `w₀`. -/
theorem pivotal_subset {α : Type*} [DecidableEq α] (W : Finset (α × α)) (w₀ : α × α)
    (hw₀ : w₀ ∈ W) (P : Finset α) (hP : ∀ k ∈ P, ∀ w ∈ W, k = w.1 ∨ k = w.2) :
    P ⊆ {w₀.1, w₀.2} := by
  intro k hk
  rcases hP k hk w₀ hw₀ with h | h <;> simp [h]

theorem pivotal_card_le_two {α : Type*} [DecidableEq α] (W : Finset (α × α)) (hW : W.Nonempty)
    (P : Finset α) (hP : ∀ k ∈ P, ∀ w ∈ W, k = w.1 ∨ k = w.2) : P.card ≤ 2 := by
  obtain ⟨w₀, hw₀⟩ := hW
  calc P.card ≤ ({w₀.1, w₀.2} : Finset α).card := card_le_card (pivotal_subset W w₀ hw₀ P hP)
    _ ≤ 2 := card_le_two

/-! ## Aggregating the insertion cross terms -/

theorem cross_terms_le {ι : Type*} (s : Finset ι) (g h : ι → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hh : ∀ i, 0 ≤ h i) :
    ∑ i ∈ s, 2 * Real.sqrt (g i * h i)
      ≤ 2 * (Real.sqrt (∑ i ∈ s, g i) * Real.sqrt (∑ i ∈ s, h i)) := by
  rw [← mul_sum]
  gcongr
  calc ∑ i ∈ s, Real.sqrt (g i * h i) = ∑ i ∈ s, Real.sqrt (g i) * Real.sqrt (h i) := by
        refine sum_congr rfl (fun i _ => ?_)
        rw [Real.sqrt_mul (hg i)]
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le s hg hh

/-! ## Numbers

`N = 2^{128}`, `p = 1/(N(N−1))`, `|T| = 17` (leaf tweaks) or `2320` (all GGM tweaks).

Theorem 1 (one proof, all oracles at `q`, `q₄ = 3q + 1`, `Q_E = q`), amplitude regime:
`ε ≤ 2·8|T|·q₄²·E_Z/N + 2·8·Q_E³·q₄·|T|·p` with `E_Z ≤ (32/9)·Q_E³/(N−1)`. -/

/-- Theorem 1 at `q = 2^{30}`: `≤ 2^{−92}` (the paper's sharper `2^{−93.9}` keeps the cross
term exactly). -/
theorem thm1_at_2_30 :
    let N : ℚ := 2 ^ 128
    let q : ℚ := 2 ^ 30
    let q₄ : ℚ := 3 * q + 1
    let EZ : ℚ := 32 / 9 * q ^ 3 / (N - 1)
    2 * (8 * 17 * q₄ ^ 2 * EZ / N) + 2 * (8 * q ^ 3 * q₄ * 17 / (N * (N - 1))) ≤ 1 / 2 ^ 92 := by
  norm_num

/-- Theorem 1 at `q = 2^{40}`: `≤ 2^{−42}` (paper: `2^{−43.9}`). Q1's bounds are vacuous here. -/
theorem thm1_at_2_40 :
    let N : ℚ := 2 ^ 128
    let q : ℚ := 2 ^ 40
    let q₄ : ℚ := 3 * q + 1
    let EZ : ℚ := 32 / 9 * q ^ 3 / (N - 1)
    2 * (8 * 17 * q₄ ^ 2 * EZ / N) + 2 * (8 * q ^ 3 * q₄ * 17 / (N * (N - 1))) ≤ 1 / 2 ^ 42 := by
  norm_num

/-- Count regime at `q = 2^{50}`: from `a² ≤ (32/9)q³/(N−1)` we get `a ≤ 2^{12}`, and with
`E_Z ≤ 1.0005·a` the `H₄` term is `≤ 2^{−5}` (paper: `2^{−5.8}`). -/
theorem count_regime_a_at_2_50 (a : ℝ) (ha : 0 ≤ a)
    (ha2 : a ^ 2 ≤ 32 / 9 * ((2 : ℝ) ^ 50) ^ 3 / (2 ^ 128 - 1)) : a ≤ 2 ^ 12 := by
  have h : a ^ 2 ≤ ((2 : ℝ) ^ 12) ^ 2 := by
    refine ha2.trans ?_
    rw [div_le_iff₀ (by norm_num)]
    norm_num
  exact (pow_le_pow_iff_left₀ ha (by norm_num) two_ne_zero).1 h

theorem count_regime_at_2_50 (a : ℝ) (ha12 : a ≤ 2 ^ 12) :
    8 * 17 * (3 * (2 : ℝ) ^ 50 + 1) ^ 2 * (10005 / 10000 * a) / 2 ^ 128 ≤ 1 / 2 ^ 5 := by
  have : 8 * 17 * (3 * (2 : ℝ) ^ 50 + 1) ^ 2 * (10005 / 10000 * a) / 2 ^ 128
      ≤ 8 * 17 * (3 * (2 : ℝ) ^ 50 + 1) ^ 2 * (10005 / 10000 * 2 ^ 12) / 2 ^ 128 := by
    gcongr
  exact this.trans (by norm_num)

/-- Theorem 2 (mixed) for SE at `Q_S = q = 2^{30}` with Lemma K (`4607` fetches per simulated
proof and per verification), weak SE (`|T| = 17`). Rational relaxation of the paper's bound:
`E_Z ≤ 2a² + 2(G + X)` with `a² = 8 Q_A² S/(N−1)`, `G = Q_C S/(N−1)`, `X = 2^9 G`, and the square of
a three-term amplitude sum bounded by three times the sum of squares. Paper value: `2^{−77.7}`. -/
theorem thm2_SE_weak_at_2_30 :
    let N : ℚ := 2 ^ 128
    let QA : ℚ := 2 ^ 30 + 4607
    let QC : ℚ := 2 ^ 30 * 4607
    let S : ℚ := QA + QC
    let q₄ : ℚ := 2 ^ 30 + 2 * (2 ^ 31 + 1) + 3 * 2 ^ 30 + 2
    let G : ℚ := QC * S / (N - 1)
    let EZ : ℚ := 2 * (8 * QA ^ 2 * S / (N - 1)) + 2 * (G + 2 ^ 9 * G)
    let T : ℚ := 17
    3 * (8 * T * q₄ ^ 2 * EZ / N + 8 * QA ^ 2 * S * q₄ * T / (N * (N - 1))
      + QC * S * q₄ * T / (N * (N - 1)) * (1 + 2 ^ 9)) ≤ 1 / 2 ^ 74 := by
  norm_num

/-- The same for strong SE (`|T'| = 2320`). Paper value: `2^{−70.6}`. -/
theorem thm2_SE_strong_at_2_30 :
    let N : ℚ := 2 ^ 128
    let QA : ℚ := 2 ^ 30 + 4607
    let QC : ℚ := 2 ^ 30 * 4607
    let S : ℚ := QA + QC
    let q₄ : ℚ := 2 ^ 30 + 2 * (2 ^ 31 + 1) + 3 * 2 ^ 30 + 2
    let G : ℚ := QC * S / (N - 1)
    let EZ : ℚ := 2 * (8 * QA ^ 2 * S / (N - 1)) + 2 * (G + 2 ^ 9 * G)
    let T : ℚ := 2320
    3 * (8 * T * q₄ ^ 2 * EZ / N + 8 * QA ^ 2 * S * q₄ * T / (N * (N - 1))
      + QC * S * q₄ * T / (N * (N - 1)) * (1 + 2 ^ 9)) ≤ 1 / 2 ^ 67 := by
  norm_num

/-- For contrast: counting the simulator's `2^{42.2}` fetches as quantum queries (Theorem 1 with
Lemma K, no mixed bound) gives only about `2^{−47.6}` for strong SE, above the `2^{−60.4}` main
term. Here: the `H₄` part alone exceeds `2^{−50}`. -/
theorem thm1_SE_strong_without_mixed_exceeds :
    let N : ℚ := 2 ^ 128
    let Q : ℚ := 2 ^ 30 + 4607 + 2 ^ 30 * 4607
    let q₄ : ℚ := 2 ^ 30 + 2 * (2 ^ 31 + 1) + 3 * 2 ^ 30 + 2
    let EZ : ℚ := 32 / 9 * Q ^ 3 / (N - 1)
    1 / 2 ^ 50 ≤ 8 * 2320 * q₄ ^ 2 * EZ / N := by
  norm_num

end VoleMole.Seed.CipherBinding
