import Mathlib

/-!
# Zero knowledge in the QROM: bound arithmetic (`lean/docs/zk-qrom.md`)

This file checks the scalar parts of `lean/docs/zk-qrom.md`. The operator-level steps are on paper.

* **Lemma R (hidden-set reprogramming), §3.2.** The proof tracks two norms per query: `Γ i`, the
  part of the purified state that has left the uniform superposition of the hidden variable `Θ`,
  and `e i`, the distance between the remaining part and the unprogrammed run. Each query obeys
  `Γ (i+1) ≤ Γ i + β` and `e (i+1) ≤ e i + a + β · Γ i`, with `a = 2b` and `β = 2√b`, where `b`
  bounds the probability over `Θ` that a fixed query input lies in the programmed set. The trace
  distance is at most `e q + (Γ q)² / 2`. `lemmaR_td` shows that this is at most `4 q² b`.
* **Numbers, §9.** The error terms at `λ = 128`, `Q_P = 2³⁰` and `q ∈ {2³⁰, 2⁵⁰, 2⁶⁴}`.

There is no `sorry` and no `axiom`.
-/

namespace VoleMole.ZK.QROM

/-! ## Lemma R: the scalar recurrence -/

/-- The escaped part grows by at most `β` per query. -/
theorem gamma_le (β : ℝ) (Γ : ℕ → ℝ) (h0 : Γ 0 = 0) (hstep : ∀ i, Γ (i + 1) ≤ Γ i + β) :
    ∀ n : ℕ, Γ n ≤ n * β := by
  intro n
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have := hstep n
    push_cast
    linarith

/-- The error of the remaining part: `e n ≤ n·a + β²·n(n-1)/2`. -/
theorem err_le (a β : ℝ) (hβ : 0 ≤ β) (Γ e : ℕ → ℝ) (hΓ0 : Γ 0 = 0) (he0 : e 0 = 0)
    (hΓ : ∀ i, Γ (i + 1) ≤ Γ i + β) (he : ∀ i, e (i + 1) ≤ e i + a + β * Γ i) :
    ∀ n : ℕ, e n ≤ n * a + β ^ 2 * ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
  intro n
  induction n with
  | zero => simp [he0]
  | succ n ih =>
    have hg : Γ n ≤ n * β := gamma_le β Γ hΓ0 hΓ n
    have h1 : β * Γ n ≤ β * (n * β) := mul_le_mul_of_nonneg_left hg hβ
    have := he n
    push_cast
    nlinarith

/-- **Lemma R, scalar core.** With `a = 2b` and `β = 2√b`, the trace-distance bound
`e q + (Γ q)²/2` is at most `4 q² b`. -/
theorem lemmaR_td (b : ℝ) (hb : 0 ≤ b) (Γ e : ℕ → ℝ) (hΓnn : ∀ i, 0 ≤ Γ i) (hΓ0 : Γ 0 = 0)
    (he0 : e 0 = 0) (hΓ : ∀ i, Γ (i + 1) ≤ Γ i + 2 * Real.sqrt b)
    (he : ∀ i, e (i + 1) ≤ e i + 2 * b + 2 * Real.sqrt b * Γ i) (q : ℕ) :
    e q + (Γ q) ^ 2 / 2 ≤ 4 * (q : ℝ) ^ 2 * b := by
  have hs : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hss : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hβ : (0 : ℝ) ≤ 2 * Real.sqrt b := by positivity
  have h1 := err_le (2 * b) (2 * Real.sqrt b) hβ Γ e hΓ0 he0 hΓ he q
  have h2 := gamma_le (2 * Real.sqrt b) Γ hΓ0 hΓ q
  have h3 : (Γ q) ^ 2 ≤ ((q : ℝ) * (2 * Real.sqrt b)) ^ 2 :=
    pow_le_pow_left₀ (hΓnn q) h2 2
  have h4 : ((q : ℝ) * (2 * Real.sqrt b)) ^ 2 = 4 * (q : ℝ) ^ 2 * b := by
    rw [mul_pow, mul_pow, hss]; ring
  have h5 : (2 * Real.sqrt b) ^ 2 = 4 * b := by rw [mul_pow, hss]; ring
  rw [h5] at h1
  rw [h4] at h3
  nlinarith

/-! ## The set version of the reprogramming bound (§3.1)

If the reprogrammed set `T` is sampled independently of the state, `E ε_T ≤ q · P_T`, and the
trace distance is at most `√(E ε_T) + E ε_T / 2`. Monotonicity in `E ε_T`: -/

theorem ghhm_set_mono (x y : ℝ) (hxy : x ≤ y) :
    Real.sqrt x + x / 2 ≤ Real.sqrt y + y / 2 := by
  have := Real.sqrt_le_sqrt hxy
  linarith

/-! ## Numbers (§9): `λ = 128`, `Q_P = 2³⁰`, every per-oracle query count `= q`

Each term is stated exactly or as an upper bound in powers of two. -/

/-- `ε_lab = 4·q²·K·2⁻¹²⁸` with `K = 2`, i.e. `q²·2⁻¹²⁵`. -/
theorem lab_eq (q : ℝ) : 4 * q ^ 2 * 2 / 2 ^ 128 = q ^ 2 / 2 ^ 125 := by ring

theorem lab_at_2_30 : ((2 : ℝ) ^ 30) ^ 2 / 2 ^ 125 = 1 / 2 ^ 65 := by norm_num
theorem lab_at_2_50 : ((2 : ℝ) ^ 50) ^ 2 / 2 ^ 125 = 1 / 2 ^ 25 := by norm_num
theorem lab_at_2_64 : ((2 : ℝ) ^ 64) ^ 2 / 2 ^ 125 = 8 := by norm_num

/-- `ε_rho = 4·q²·Q_P·2⁻¹²⁸ = q²·2⁻⁹⁶` at `Q_P = 2³⁰`. -/
theorem rho_eq (q : ℝ) : 4 * q ^ 2 * 2 ^ 30 / 2 ^ 128 = q ^ 2 / 2 ^ 96 := by ring

theorem rho_at_2_30 : ((2 : ℝ) ^ 30) ^ 2 / 2 ^ 96 = 1 / 2 ^ 36 := by norm_num
theorem rho_at_2_50 : ((2 : ℝ) ^ 50) ^ 2 / 2 ^ 96 = 16 := by norm_num

/-- With `rho` widened to 256 bits (recommendation R1), `ε_rho = q²·2⁻²²⁴`. -/
theorem rho256_at_2_64 : 4 * ((2 : ℝ) ^ 64) ^ 2 * 2 ^ 30 / 2 ^ 256 = 1 / 2 ^ 96 := by norm_num

/-- The main reprogramming term `ε_RP ≈ Q_P·√(q·2⁻¹²⁸)`. We state `(ε_RP / Q_P)² = q·2⁻¹²⁸`
and evaluate the square root at the three query counts. -/
theorem rp_sqrt_at_2_30 : Real.sqrt ((2 : ℝ) ^ 30 / 2 ^ 128) = 1 / 2 ^ 49 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
  norm_num

theorem rp_sqrt_at_2_50 : Real.sqrt ((2 : ℝ) ^ 50 / 2 ^ 128) = 1 / 2 ^ 39 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
  norm_num

theorem rp_sqrt_at_2_64 : Real.sqrt ((2 : ℝ) ^ 64 / 2 ^ 128) = 1 / 2 ^ 32 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
  norm_num

theorem rp_at_2_30 : (2 : ℝ) ^ 30 * Real.sqrt ((2 : ℝ) ^ 30 / 2 ^ 128) = 1 / 2 ^ 19 := by
  rw [rp_sqrt_at_2_30]; norm_num

theorem rp_at_2_50 : (2 : ℝ) ^ 30 * Real.sqrt ((2 : ℝ) ^ 50 / 2 ^ 128) = 1 / 2 ^ 9 := by
  rw [rp_sqrt_at_2_50]; norm_num

theorem rp_at_2_64 : (2 : ℝ) ^ 30 * Real.sqrt ((2 : ℝ) ^ 64 / 2 ^ 128) = 1 / 4 := by
  rw [rp_sqrt_at_2_64]; norm_num

/-- The linear part of the reprogramming term, `Q_P·q·2⁻¹²⁹`, is negligible next to the square
root part for `q ≤ 2⁶⁴`. -/
theorem rp_linear_at_2_64 : (2 : ℝ) ^ 30 * 2 ^ 64 / 2 ^ 129 = 1 / 2 ^ 35 := by norm_num

/-- AES hiding under the union bound: `2·N_inst·Q_P·t²·2⁻¹²⁸` with `N_inst ≤ 2⁸` PRG instances
per proof (`1 + τ⌈log L − 1⌉ + τ = 205`) and the Grover heuristic `Adv(t) = t²·2⁻¹²⁸`. -/
theorem hide_union_at_2_30 : 2 * 2 ^ 8 * 2 ^ 30 * ((2 : ℝ) ^ 30) ^ 2 / 2 ^ 128 = 1 / 2 ^ 29 := by
  norm_num

theorem hide_union_at_2_50 :
    1 ≤ 2 * 2 ^ 8 * 2 ^ 30 * ((2 : ℝ) ^ 50) ^ 2 / 2 ^ 128 := by norm_num

/-- AES hiding under the multi-user heuristic (no union loss): `2·t²·2⁻¹²⁸`. -/
theorem hide_mu_at_2_30 : 2 * ((2 : ℝ) ^ 30) ^ 2 / 2 ^ 128 = 1 / 2 ^ 67 := by norm_num
theorem hide_mu_at_2_50 : 2 * ((2 : ℝ) ^ 50) ^ 2 / 2 ^ 128 = 1 / 2 ^ 27 := by norm_num

/-- The H₅ pre-proof reprogramming term `Q_P·√(q·λ·2⁻²⁵⁶)` at `q = 2⁶⁴` (`λ = 2⁷`): its square
divided by `Q_P²` is `2⁻¹⁸⁵`, so the term is below `2^30 · 2⁻⁹²`. -/
theorem h5_pre_sq_at_2_64 : (2 : ℝ) ^ 64 * 2 ^ 7 / 2 ^ 256 = 1 / 2 ^ 185 := by norm_num

/-- The iv-multiplicity event: `C(Q_P, 3)·λ²·2⁻²⁵⁶ ≤ Q_P³·λ²·2⁻²⁵⁶ = 2⁻¹⁵²`. -/
theorem iv_triple : ((2 : ℝ) ^ 30) ^ 3 * (2 ^ 7) ^ 2 / 2 ^ 256 = 1 / 2 ^ 152 := by norm_num

/-- The Grover attack on the labels (§7.3) succeeds with probability about
`(q / n_mult)² · 2⁻¹²⁸`. With `n_mult ≤ 2⁹`, at `q = 2⁶⁴` this is at least `2⁻¹⁸`, so `ε_lab`
is within a factor `2²¹` of tight there. -/
theorem lab_attack_at_2_64 : 1 / 2 ^ 18 ≤ ((2 : ℝ) ^ 64 / 2 ^ 9) ^ 2 / 2 ^ 128 := by norm_num

end VoleMole.ZK.QROM
