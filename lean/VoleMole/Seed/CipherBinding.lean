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
* Block representation (paper §11–§13, Theorems 4 and 5): `typical_telescope` (the potential
  argument with an atypical-database correction), `chernoff_tail_num` and `typical_union_num`
  (the tail of the exposure count at `δ = 3`, mean `≥ 128`), `nbar_ok`, and the numbers
  `block_multi_at_2_50` … `block_multi_at_2_60`, `q2_total_at_2_58`, `q2_total_at_2_60_lt_one`.
* Review of Theorems 4 and 5 (paper §14): `openers_le_one_add_pairs` and `transfer_solve` (the
  transfer between the database and the real world costs `O(√(|𝒯|/N))`, independent of the query
  count), `transfer_refined_const`, `transfer_refined_sq_at_L`, and the numbers for
  simulation-extractability and multi-proof extraction with every cipher evaluation counted
  (`block_SE_at_q45_QS30`, `block_SE_at_q50_QS30`, `block_multiM_at_q50_n20`).
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

/-! ## Block representation (paper §11–§13)

`B = 2^{98}` (block size), `n̄ = 1037` (typical bound on the exposure count), `μ_B = n̄/(B(B−1))`.
Theorem 5: the expected number of agreement triples is `≤ a²` with `a² = (32/9)·Q_E³·μ_B`, up to
an atypical-database correction. Theorem 4 transfers it to the key-level `multi` event with an
additive amplitude `c_R`. -/

/-- The potential argument with a typical/atypical split (paper §12, step 4): if the potential
grows by at most `c t` on the typical part and by at most `C · b t` on the atypical part, then
`A T ≤ Σ c + C · Σ b`. -/
theorem typical_telescope (A c b : ℕ → ℝ) (C : ℝ) (h0 : A 0 = 0)
    (hstep : ∀ t, A (t + 1) ≤ A t + c t + C * b t) (T : ℕ) :
    A T ≤ ∑ t ∈ range T, c t + C * ∑ t ∈ range T, b t := by
  induction T with
  | zero => simp [h0]
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, mul_add]
    linarith [hstep n]

/-- Chernoff tail at `δ = 3` for a sum of negatively associated indicators with mean bound
`μ̄ ≥ 128`: `(e^δ/(1+δ)^{1+δ})^{128} ≤ 2^{−460}` (written `(2^{115})^4`). -/
theorem chernoff_tail_num : (Real.exp 3 / 4 ^ 4) ^ 128 ≤ (1 : ℝ) / (2 ^ 115) ^ 4 := by
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he : Real.exp 3 ≤ 201 / 10 := by
    rw [h3]
    have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
    calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le h1 3
      _ ≤ 201 / 10 := by norm_num
  have h32 : ((201 / 10 : ℝ) / 4 ^ 4) ^ 32 ≤ 1 / 2 ^ 115 := by norm_num
  calc (Real.exp 3 / 4 ^ 4) ^ 128 ≤ ((201 / 10 : ℝ) / 4 ^ 4) ^ 128 := by
        gcongr
    _ = (((201 / 10 : ℝ) / 4 ^ 4) ^ 32) ^ 4 := by rw [← pow_mul]
    _ ≤ (1 / 2 ^ 115) ^ 4 := pow_le_pow_left₀ (by positivity) h32 4
    _ = 1 / (2 ^ 115) ^ 4 := by rw [one_div_pow]

/-- Union over the two parity classes and the `N · N/B = 2^{158}` fresh entries: the density of
atypical values is `ε_T ≤ 2^{158}·2·2^{−460} ≤ 2^{−301}` (`2^{460} = (2^{115})^4`,
`2^{301} = 2^{200}·2^{101}`; the exponents are split to stay below Lean's evaluation threshold). -/
theorem typical_union_num :
    (2 : ℚ) ^ 158 * 2 * (1 / (2 ^ 115) ^ 4) ≤ 1 / (2 ^ 200 * 2 ^ 101) := by
  norm_num

/-- `n̄ = 1037 ≥ 2·(1+δ)·μ̄` with `δ = 3` and `μ̄ = (1+2^{−8})³·B⁴/(2N³) = 128·(1+2^{−8})³`. -/
theorem nbar_ok : (2 : ℚ) * (1 + 3) * (128 * (1 + 1 / 2 ^ 8) ^ 3) ≤ 1037 := by
  norm_num

/-- Theorem 5 at `Q_E = 2^{50}`: `a² ≤ 2^{−34}` (Theorem 1 gives `2^{−5.8}` here). -/
theorem block_multi_at_2_50 :
    let B : ℚ := 2 ^ 98
    (32 : ℚ) / 9 * (2 ^ 50) ^ 3 * (1037 / (B * (B - 1))) ≤ 1 / 2 ^ 34 := by
  norm_num

/-- Theorem 5 at `Q_E = 2^{55}`: `a² ≤ 2^{−19}` (Theorem 1 is vacuous here). -/
theorem block_multi_at_2_55 :
    let B : ℚ := 2 ^ 98
    (32 : ℚ) / 9 * (2 ^ 55) ^ 3 * (1037 / (B * (B - 1))) ≤ 1 / 2 ^ 19 := by
  norm_num

/-- Theorem 5 at `Q_E = 2^{58}`: `a² ≤ 2^{−10}`. -/
theorem block_multi_at_2_58 :
    let B : ℚ := 2 ^ 98
    (32 : ℚ) / 9 * (2 ^ 58) ^ 3 * (1037 / (B * (B - 1))) ≤ 1 / 2 ^ 10 := by
  norm_num

/-- Theorem 5 at `Q_E = 2^{60}`: `a² ≤ 2^{−4}`. -/
theorem block_multi_at_2_60 :
    let B : ℚ := 2 ^ 98
    (32 : ℚ) / 9 * (2 ^ 60) ^ 3 * (1037 / (B * (B - 1))) ≤ 1 / 2 ^ 4 := by
  norm_num

/-- The transfer amplitude `c_R` of Theorems 4 and 5 (four terms, `τ = 17`, `c̄/(B(B−1)) ≤
2(1+2^{−8})/N`) satisfies `c_R² ≤ 2^{−58}` for `q ≤ 2^{60}` (shown at `q = 2^{60}`; every term is
monotone in `q`). Uses `(x₁+x₂+x₃+x₄)² ≤ 4·Σ xᵢ²`. -/
theorem transfer_sq_at_2_60 :
    let N : ℚ := 2 ^ 128
    let q : ℚ := 2 ^ 60
    let cb : ℚ := 2 * (1 + 1 / 2 ^ 8) / N
    4 * ((2 * 17 * q + 2) / (N - 1) + 17 * q / (N - 1) + cb * (2 * 17 * q + 2) + cb * (17 * q))
      ≤ 1 / 2 ^ 58 := by
  norm_num

/-- Q2 with Theorems 4 and 5 at `q = 2^{58}`: main term `200q²/N` plus
`ε_multi ≤ (a + c_R)² ≤ 2a² + 2c_R²` is `≤ 2^{−4}` (paper: `2^{−4.3}`). -/
theorem q2_total_at_2_58 :
    let N : ℚ := 2 ^ 128
    let B : ℚ := 2 ^ 98
    let q : ℚ := 2 ^ 58
    200 * q ^ 2 / N + 2 * ((32 : ℚ) / 9 * q ^ 3 * (1037 / (B * (B - 1)))) + 2 * (1 / 2 ^ 58)
      ≤ 1 / 2 ^ 4 := by
  norm_num

/-- Q2 with Theorems 4 and 5 at `q = 2^{60}`: still below 1. The main term alone is `≈ 0.78`:
the bound is now limited by the Grover-inherent term, not by `ε_multi`. -/
theorem q2_total_at_2_60_lt_one :
    let N : ℚ := 2 ^ 128
    let B : ℚ := 2 ^ 98
    let q : ℚ := 2 ^ 60
    200 * q ^ 2 / N + 2 * ((32 : ℚ) / 9 * q ^ 3 * (1037 / (B * (B - 1)))) + 2 * (1 / 2 ^ 58)
      < 1 := by
  norm_num

/-! ## Review of Theorems 4 and 5 (paper §14) -/

/-- A target with `m` opening keys has at most `1 + C(m,2)` of them: the number of
(target, opening key) incidences is at most the number of targets plus the number of
(target, opening key pair) incidences. -/
theorem openers_le_one_add_pairs (m : ℕ) : m ≤ 1 + m.choose 2 := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    rcases n with _ | n
    · simp
    · omega

/-- The refined transfer step (paper §14.3). `x` and `A` are the square roots of the two pair
counts (real world and database, in either order), `r = √|𝒯|`, and `s = √ε` with `ε` the total
opening density of a uniform register. The three-term split and `openers_le_one_add_pairs` give
the hypothesis; the conclusion has no query count in it. -/
theorem transfer_solve {x A r s : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hr : 0 ≤ r) (hs0 : 0 ≤ s)
    (hs1 : s < 1)
    (h : x ≤ A + s * Real.sqrt (r ^ 2 + x ^ 2) + s * Real.sqrt (r ^ 2 + A ^ 2)) :
    x ≤ ((1 + s) * A + 2 * s * r) / (1 - s) := by
  have hsq : ∀ {u v : ℝ}, 0 ≤ u → 0 ≤ v → Real.sqrt (u ^ 2 + v ^ 2) ≤ u + v := by
    intro u v hu hv
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have h1 := hsq hr hx
  have h2 := hsq hr hA
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hs0, mul_le_mul_of_nonneg_left h2 hs0]

/-- The constant of the refined transfer: with `√ε ≤ (1001/1000)/√N` at key level
(`ε = 1/(N−1)`) and `√ε' ≤ (1418/1000)/√N` at block level (`ε' = 2(1+2^{−8})/N`), the two
`2√(ε|𝒯|)` terms, each inflated by `1001/1000` for the factors `(1±√ε)^{±1}`, add up to at most
`5·√(|𝒯|/N)`. -/
theorem transfer_refined_const :
    (2 : ℚ) * (1 + 1 / 2 ^ 8) ≤ (1418 / 1000) ^ 2 ∧
    (2 : ℚ) ^ 128 / (2 ^ 128 - 1) ≤ (1001 / 1000) ^ 2 ∧
    (2 : ℚ) * (1418 / 1000) * (1001 / 1000) + 2 * (1001 / 1000) * (1001 / 1000) ≤ 5 := by
  norm_num

/-- The refined transfer term for one proof (`|𝒯| ≤ L = 2304`): `c_R'² = 25·L/N ≤ 2^{−112}`,
for every query count. (The original `c_R²` was `≈ 2^{−58.7}` at `q = 2^{60}`.) -/
theorem transfer_refined_sq_at_L : (25 : ℚ) * 2304 / 2 ^ 128 ≤ 1 / 2 ^ 112 := by
  norm_num

/-- Simulation-extractability with Theorem 5, every cipher evaluation counted
(`2^{18}` per simulated proof and per verification): at `q = 2^{45}`, `Q_S = 2^{30}`,
`a² ≤ 2^{−39}`, below the main term `2^{−30.4}`. (Theorem 2 gives only `2^{−22.6}` here.) -/
theorem block_SE_at_q45_QS30 :
    let B : ℚ := 2 ^ 98
    let QE : ℚ := 2 ^ 45 + (2 ^ 30 + 1) * 2 ^ 18
    (32 : ℚ) / 9 * QE ^ 3 * (1037 / (B * (B - 1))) ≤ 1 / 2 ^ 39 := by
  norm_num

/-- The same at `q = 2^{50}`, `Q_S = 2^{30}`: `a² ≤ 2^{−33}` (main term `2^{−20.4}`; Theorems 1
and 2 are vacuous or nearly so). -/
theorem block_SE_at_q50_QS30 :
    let B : ℚ := 2 ^ 98
    let QE : ℚ := 2 ^ 50 + (2 ^ 30 + 1) * 2 ^ 18
    (32 : ℚ) / 9 * QE ^ 3 * (1037 / (B * (B - 1))) ≤ 1 / 2 ^ 33 := by
  norm_num

/-- Multi-proof extraction (Q7 Theorem M) with Theorem 5 at `q = 2^{50}`, `n = 2^{20}` outputs:
`a² ≤ 2^{−34}`, and the refined transfer term `25·nL/N ≤ 2^{−92}`. -/
theorem block_multiM_at_q50_n20 :
    let B : ℚ := 2 ^ 98
    let QE : ℚ := 2 ^ 50 + 2 ^ 20 * 2 ^ 18
    (32 : ℚ) / 9 * QE ^ 3 * (1037 / (B * (B - 1))) ≤ 1 / 2 ^ 34 ∧
    (25 : ℚ) * (2 ^ 20 * 2304) / 2 ^ 128 ≤ 1 / 2 ^ 92 := by
  norm_num

end VoleMole.Seed.CipherBinding
