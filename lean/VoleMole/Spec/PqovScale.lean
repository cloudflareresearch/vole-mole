import VoleMole.Spec.PqovSigner

/-!
# The scaling symmetry of the UOV public map, and CT-UF

pqov's public map `P` (`qmap`) is a homogeneous quadratic map over `GF(256)`, and squaring is a
bijection of `GF(256)`. So a preimage of `μ • t` (`μ ≠ 0`) gives a preimage of `t`: scale it by
`(μ⁻¹)^128`, the square root of `μ⁻¹`.

Consequence (`lean/docs/security/uov-open-reductions.md` §2): chosen-target unforgeability with a
signing oracle on **arbitrary** targets (CT-UF, `moussaka.md` §3.3), whose freshness condition is
"`Com(x*)` was never queried", is broken by one query, on `μ • Com(x*)` with `μ ∉ {0, 1}`
(`ctuf_scaling_attack`). The repaired notions ask for freshness up to nonzero scalars.

* `qmap_smul`: `P(c • σ) = c² • P(σ)`.
* `sq_pow_128`: `(μ^128)² = μ` in `GF(256)`.
* `scaled_preimage`: `P(s) = μ • t`, `μ ≠ 0` ⟹ `P((μ⁻¹)^128 • s) = t`.
* `scaled_target_ne`: `μ ≠ 1`, `t ≠ 0` ⟹ `μ • t ≠ t`.
* `ctuf_scaling_attack`: for every oracle `D` that returns preimages, the query `μ • t` differs from
  `t` and its answer, rescaled, is a preimage of `t`.
-/

namespace VoleMole.Spec.Pqov

open VoleMole.Arith VoleMole.Arith.UOV

/-- Homogeneity of the generic public map, for any sizes. -/
theorem publicMap_scale {K : Type*} [CommSemiring K] (N M : ℕ) (pk σ : ℕ → K) (c : K)
    (k : Fin M) :
    publicMap N M pk (fun i => c * σ i) k = c ^ 2 * publicMap N M pk σ k := by
  unfold publicMap
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  ring

/-- **`P` is homogeneous of degree 2**: `P(c • σ) = c² • P(σ)`. -/
theorem qmap_smul (pk : UOVKey) (c : GF256) (σ : ℕ → GF256) :
    qmap pk (c • σ) = c ^ 2 • qmap pk σ := by
  funext k
  exact publicMap_scale 119 45 pk.map σ c k

/-- **Square roots in `GF(256)`**: `μ^128` is the square root of `μ`. -/
theorem sq_pow_128 (μ : GF256) : (μ ^ 128) ^ 2 = μ := by
  have h := FiniteField.pow_card μ
  rw [GF256.card_eq] at h
  rw [← pow_mul]
  exact h

/-- **A preimage of `μ • t` gives a preimage of `t`.** -/
theorem scaled_preimage (pk : UOVKey) {μ : GF256} (hμ : μ ≠ 0) {s : ℕ → GF256}
    {t : Fin 45 → GF256} (h : qmap pk s = μ • t) : qmap pk ((μ⁻¹) ^ 128 • s) = t := by
  rw [qmap_smul, sq_pow_128, h, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- A nonzero target differs from its multiples by `μ ≠ 1`. -/
theorem scaled_target_ne {μ : GF256} (hμ : μ ≠ 1) {t : Fin 45 → GF256} (ht : t ≠ 0) :
    μ • t ≠ t := by
  intro h
  have h0 : (μ - 1) • t = 0 := by rw [sub_smul, one_smul, h, sub_self]
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact hμ (sub_eq_zero.mp h1)
  · exact ht h1

/-- **The one-query attack on CT-UF with an arbitrary-target oracle.** Let `D` return preimages
(`P(D y) = y`, as `derive_preimage` does when it does not fail). For a target `t ≠ 0` and any
`μ ∉ {0, 1}`: the query `μ • t` is not `t`, and `(μ⁻¹)^128 • D(μ • t)` is a preimage of `t`. -/
theorem ctuf_scaling_attack (pk : UOVKey) (D : (Fin 45 → GF256) → ℕ → GF256)
    (hD : ∀ y, qmap pk (D y) = y) {μ : GF256} (h0 : μ ≠ 0) (h1 : μ ≠ 1) {t : Fin 45 → GF256}
    (ht : t ≠ 0) :
    μ • t ≠ t ∧ qmap pk ((μ⁻¹) ^ 128 • D (μ • t)) = t :=
  ⟨scaled_target_ne h1 ht, scaled_preimage pk h0 (hD _)⟩

end VoleMole.Spec.Pqov
