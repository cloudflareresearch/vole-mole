import VoleMole.Seed.QROM

/-!
# Q7: bookkeeping for multi-proof QROM extraction and database-controlled programming

Paper proof: `lean/docs/extraction/Q7-qrom-multi-extraction.md`. As in `Seed/QROM.lean`, states are vectors
in a normed space and oracle steps are linear maps; nothing here is quantum-specific.

## Results

* `hybrid_le` (Lemma S, step 2): two runs that differ only in their oracle steps `A s` (contractions)
  versus `B s` drift apart by at most `Σ_s ‖(A s − B s) ψ_s‖`, evaluated on the *real* run `ψ`.
* `conj_run` (Lemma S, step 1): if every step of a run is conjugated by an invertible `V`, the
  final state is `V` applied to the unconjugated run's final state. This is how the programmed
  world `S` (target queries `V cO V⁻¹`) is identified with `V ψ_R̃`.
* `conj_defect_norm` (Lemma S, step 2): `‖(U − V⁻¹ U V) ψ‖ = ‖(V U − U V) ψ‖` for an isometry `V`.
* `comm_offdiag`, `swap_comm` (Lemma S, step 3): for an idempotent `P`, `[P, Z]` is the difference
  of its two off-diagonal blocks; for `F = 1 − 2P`, `[F, W] = −2[P, W − 1]`.
* `offdiag_norm_le` (Lemma S, step 3): the difference of two orthogonal vectors with norms
  `≤ c·a`, `≤ c·b`, `a² + b² = ‖v‖²`, has norm `≤ c‖v‖`. This is why the commutator costs the
  larger of the two blocks, not their sum.
* `density_swap_le` (Lemma S, step 4): the weighted count `Σ_v w_v Σ_{β : v ∈ NN β} a_β` is at most
  `ρ · Σ_β a_β` when every `NN β` has `w`-mass `≤ ρ`.
* `main_term_multi_eq`, `main_term_multi_at_2_30_n_2_20`, `main_term_multi_at_n_eq_q`
  (Theorem M): `8(5q + 7n)²·2^{−128}`, its expansion, and values.
* `shift_term_at_2_30`, `shift_term_at_2_20` (Theorem U1-Q): the Lemma-P-Q term
  `8·Q₂₃²·2^{57−128}`.
* `fetch_keys`, `multi_free_fetch_at_n_2_20`, `multi_free_blocks_at_n_2_20` (Lemma K): the verifier's
  `≤ 2L − 1 = 4607` key fetches per proof, and the effect on the free-iv `multi` bound.
* `stab_cipher_at_2_50` (§3.4): the squared cipher part of `δ_stab` at `q = 2^{50}`.

No `sorry`, no `axiom`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Seed.QMulti

section Hybrid

variable {𝕜 E : Type*} [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]

/-- **Hybrid over oracle steps.** `φ` runs with oracle steps `A s` (contractions), `ψ` with `B s`;
both use the same adversary isometries `U s`. Then the final distance is at most the sum of the
one-step defects `‖A s (ψ s) − B s (ψ s)‖`, evaluated on the run `ψ`. -/
theorem hybrid_le (A B U : ℕ → E →ₗ[𝕜] E) (φ ψ : ℕ → E)
    (hφ : ∀ s, φ (s + 1) = U s (A s (φ s))) (hψ : ∀ s, ψ (s + 1) = U s (B s (ψ s)))
    (hU : ∀ s v, ‖U s v‖ = ‖v‖) (hA : ∀ s v, ‖A s v‖ ≤ ‖v‖) (h0 : φ 0 = ψ 0) :
    ∀ T, ‖φ T - ψ T‖ ≤ ∑ s ∈ range T, ‖A s (ψ s) - B s (ψ s)‖ := by
  intro T
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    rw [hφ, hψ, ← map_sub, hU, Finset.sum_range_succ]
    have hsplit : A T (φ T) - B T (ψ T) = A T (φ T - ψ T) + (A T (ψ T) - B T (ψ T)) := by
      rw [map_sub]; abel
    rw [hsplit]
    calc ‖A T (φ T - ψ T) + (A T (ψ T) - B T (ψ T))‖
        ≤ ‖A T (φ T - ψ T)‖ + ‖A T (ψ T) - B T (ψ T)‖ := norm_add_le _ _
      _ ≤ ‖φ T - ψ T‖ + ‖A T (ψ T) - B T (ψ T)‖ := by gcongr; exact hA T _
      _ ≤ _ := by linarith

/-- **Conjugated runs.** If each step of `ψS` is `V ∘ K s ∘ W` with `W ∘ V = id`, and `ψS 0 = V (φ 0)`
where `φ` runs with the steps `K s`, then `ψS T = V (φ T)` for all `T`. -/
theorem conj_run (V W : E →ₗ[𝕜] E) (K : ℕ → E →ₗ[𝕜] E) (φ ψS : ℕ → E)
    (hWV : ∀ v, W (V v) = v) (hφ : ∀ s, φ (s + 1) = K s (φ s))
    (hS : ∀ s, ψS (s + 1) = V (K s (W (ψS s)))) (h0 : ψS 0 = V (φ 0)) :
    ∀ T, ψS T = V (φ T) := by
  intro T
  induction T with
  | zero => exact h0
  | succ T ih => rw [hS, ih, hWV, hφ]

/-- **The one-step defect is a commutator.** For an isometry `V` with right inverse `W`,
`‖U ψ − W (U (V ψ))‖ = ‖V (U ψ) − U (V ψ)‖`. -/
theorem conj_defect_norm (V W U : E →ₗ[𝕜] E) (hVW : ∀ v, V (W v) = v)
    (hV : ∀ v, ‖V v‖ = ‖v‖) (ψ : E) :
    ‖U ψ - W (U (V ψ))‖ = ‖V (U ψ) - U (V ψ)‖ := by
  rw [← hV (U ψ - W (U (V ψ))), map_sub, hVW]

end Hybrid

section Algebra

variable {R : Type*} [Ring R]

/-- `P Z − Z P = P Z (1 − P) − (1 − P) Z P` (a ring identity). For an idempotent `P` the two terms
are the off-diagonal blocks of `Z`, so the commutator consists of them. -/
theorem comm_offdiag (P Z : R) :
    P * Z - Z * P = P * Z * (1 - P) - (1 - P) * Z * P := by
  have h1 : P * Z * P - P * Z * P = 0 := sub_self _
  calc P * Z - Z * P = P * Z * (1 - P) - (1 - P) * Z * P + (P * Z * P - P * Z * P) := by
        noncomm_ring
    _ = P * Z * (1 - P) - (1 - P) * Z * P := by rw [h1, add_zero]

/-- With `F = 1 − 2P` (DFMS's swap of `⊥` and the uniform vector, `P = |w⟩⟨w|`),
`F W − W F = −2 (P (W − 1) − (W − 1) P)`. -/
theorem swap_comm (P W : R) : (1 - 2 * P) * W - W * (1 - 2 * P) = -2 * (P * (W - 1) - (W - 1) * P) := by
  noncomm_ring

end Algebra

section Offdiag

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Off-diagonal blocks cost their maximum.** If `x ⟂ y`, `‖x‖ ≤ c·a`, `‖y‖ ≤ c·b` and
`a² + b² = ‖v‖²` (the two components of `v`), then `‖x − y‖ ≤ c‖v‖`. Applied with
`x = P Z (1−P) v`, `y = (1−P) Z P v`. -/
theorem offdiag_norm_le (x y v : E) (a b c : ℝ) (hxy : inner 𝕜 x y = 0) (hc : 0 ≤ c)
    (hx : ‖x‖ ≤ c * a) (hy : ‖y‖ ≤ c * b) (hv : a ^ 2 + b ^ 2 = ‖v‖ ^ 2) :
    ‖x - y‖ ≤ c * ‖v‖ := by
  have hsq : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    rw [@norm_sub_sq 𝕜, hxy]; simp
  have hx2 : ‖x‖ ^ 2 ≤ (c * a) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hy2 : ‖y‖ ^ 2 ≤ (c * b) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  have h : ‖x - y‖ ^ 2 ≤ (c * ‖v‖) ^ 2 := by
    rw [hsq, mul_pow, ← hv]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

end Offdiag

section Density

/-- **Density swap.** Values `v` carry weights `w v ≥ 0` (`|u_v|²` of the uniform vector), database
states `β` carry weights `a β ≥ 0` (`|φ_β|²`). If every `β`'s non-neutral set `NN β` has `w`-mass at
most `ρ`, then `Σ_v w_v · Σ_{β : v ∈ NN β} a_β ≤ ρ·Σ_β a_β`. With the factor `4 = 2²` from
`‖Γ − 1‖ ≤ 2` this is `‖Z(u ⊗ φ)‖² ≤ 4ρ‖φ‖²`. -/
theorem density_swap_le {Val St : Type*} [DecidableEq Val] (Vs : Finset Val) (Bs : Finset St)
    (w : Val → ℝ) (a : St → ℝ) (NN : St → Finset Val) (ρ : ℝ)
    (ha : ∀ β, 0 ≤ a β) (hNN : ∀ β ∈ Bs, ∑ v ∈ Vs.filter (· ∈ NN β), w v ≤ ρ) :
    ∑ v ∈ Vs, w v * ∑ β ∈ Bs.filter (fun β => v ∈ NN β), a β ≤ ρ * ∑ β ∈ Bs, a β := by
  calc ∑ v ∈ Vs, w v * ∑ β ∈ Bs.filter (fun β => v ∈ NN β), a β
      = ∑ v ∈ Vs, ∑ β ∈ Bs, (if v ∈ NN β then w v * a β else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum, Finset.sum_filter]
    _ = ∑ β ∈ Bs, ∑ v ∈ Vs, (if v ∈ NN β then w v * a β else 0) := Finset.sum_comm
    _ = ∑ β ∈ Bs, a β * ∑ v ∈ Vs.filter (· ∈ NN β), w v := by
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> ring
    _ ≤ ∑ β ∈ Bs, a β * ρ := by
        refine Finset.sum_le_sum fun β hβ => ?_
        exact mul_le_mul_of_nonneg_left (hNN β hβ) (ha β)
    _ = ρ * ∑ β ∈ Bs, a β := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

end Density

section Numbers

/-- Theorem M's dominant term with `n` outputs: the verifier adds, per output, one H₂³ query
(weight `√9 + 2 = 5`), one H₂² query and one H_comb query (weight 1 each). So
`8·(5q + 7n)²·2^{−128} = (200q² + 560qn + 392n²)·2^{−128}`: the `q²` part is not multiplied by `n`. -/
theorem main_term_multi_eq (q n : ℝ) :
    8 * ((5 * q + 7 * n) / 2 ^ 64) ^ 2 = (200 * q ^ 2 + 560 * q * n + 392 * n ^ 2) / 2 ^ 128 := by
  ring

/-- `q = 2^{30}`, `n = 2^{20}` outputs: still below `2^{−60}`. -/
theorem main_term_multi_at_2_30_n_2_20 :
    8 * ((5 * (2 : ℝ) ^ 30 + 7 * 2 ^ 20) / 2 ^ 64) ^ 2 ≤ 1 / 2 ^ 60 := by
  norm_num

/-- `n = q = 2^{30}`: below `2^{−57}`. -/
theorem main_term_multi_at_n_eq_q :
    8 * ((5 * (2 : ℝ) ^ 30 + 7 * 2 ^ 30) / 2 ^ 64) ^ 2 ≤ 1 / 2 ^ 57 := by
  norm_num

/-- Lemma P-Q in the QROM: H₂³ density `2^{57}/2^{128}`, squared Lemma-T term
`8·Q₂₃²·2^{−71}`. At `Q₂₃ = 2^{30}` it is `2^{−8}`. -/
theorem shift_term_at_2_30 : 8 * ((2 : ℝ) ^ 30) ^ 2 * (2 ^ 57 / 2 ^ 128) = 1 / 2 ^ 8 := by
  norm_num

/-- At `Q₂₃ = 2^{20}` it is `2^{−28}`. -/
theorem shift_term_at_2_20 : 8 * ((2 : ℝ) ^ 20) ^ 2 * (2 ^ 57 / 2 ^ 128) = 1 / 2 ^ 28 := by
  norm_num

/-- Lemma K: a verifier touches at most `2L − 1` keys (GGM nodes and leaves), `L = 2304`. -/
theorem fetch_keys : 2 * 2304 - 1 = 4607 := by norm_num

/-- Free-iv `multi` with `q_E = 2^{30}` and `n = 2^{20}` verifications at `4607` fetches each:
below `2^{−28}`. -/
theorem multi_free_fetch_at_n_2_20 :
    32 / 9 * ((2 : ℝ) ^ 30 + 2 ^ 20 * 4607) ^ 3 / (2 ^ 128 - 1) ≤ 1 / 2 ^ 28 := by
  norm_num

/-- Without fetching (`2^{17}` block queries per verification) the same bound exceeds `2^{−16}`. -/
theorem multi_free_blocks_at_n_2_20 :
    1 / 2 ^ 16 ≤ 32 / 9 * ((2 : ℝ) ^ 30 + 2 ^ 20 * 2 ^ 17) ^ 3 / (2 ^ 128 - 1) := by
  norm_num

/-- §3.4: the cipher part of `δ_stab` is `4·K_E·√(2·Q₂₁·L·p)`; its square `32·Q³·L·p` at
`Q = 2^{50}` is below `2^{−89}`. -/
theorem stab_cipher_at_2_50 :
    32 * ((2 : ℝ) ^ 50) ^ 3 * 2304 * (1 / (2 ^ 128 * (2 ^ 128 - 1))) ≤ 1 / 2 ^ 89 := by
  norm_num

end Numbers

end VoleMole.Seed.QMulti
