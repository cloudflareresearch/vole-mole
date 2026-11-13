import VoleMole.Spec.PqovScale

/-!
# Translations of preimages of the UOV public map

Algebraic identities behind `lean/docs/security/ompr-shift-algebra.md` (OMPR versus the τ-shift
variant OMPR⊕τ). `P = qmap pk` is pqov's public map, `B = polar pk` its polar form
(`qmap_add`: `P(a + b) = P(a) + P(b) + B(a, b)`).

* `polar_smul_right`, `polar_smul_left`: `B` is homogeneous in each argument.
* `qmap_add_of_polar_eq_zero`: for `u` in the kernel of `B(s, ·)`, `P(s + u) = P(s) + P(u)`.
* `preimage_line`: for a singular vector `z` (`P(z) = 0`; an oil vector, or the answer to the
  query `0`), `P(s + c • z) = P(s) + c • B(s, z)`.
* `preimage_plane`: `P(α • s + β • s') = α² • P(s) + β² • P(s') + (α β) • B(s, s')`.
* `affine_symmetry`: if `P(A s + a) = T(P s) + c` for all `s`, with `A` and `T` homogeneous, then
  `c = P(a)`, `B(A s, a) = 0` for all `s`, and `P ∘ A = T ∘ P`. So an affine symmetry of `P`
  shifts targets only by `P(a)` with `a` orthogonal to the image of `A`: by nothing when `A` is
  onto and `B` is nondegenerate.
-/

namespace VoleMole.Spec.Pqov

open VoleMole.Arith VoleMole.Arith.UOV

/-- `B(a, c • b) = c • B(a, b)`. -/
theorem polar_smul_right (pk : UOVKey) (a b : ℕ → GF256) (c : GF256) :
    polar pk a (c • b) = c • polar pk a b := by
  funext k
  simp only [polar, Pi.smul_apply, smul_eq_mul]
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  ring

/-- `B(c • a, b) = c • B(a, b)`. -/
theorem polar_smul_left (pk : UOVKey) (a b : ℕ → GF256) (c : GF256) :
    polar pk (c • a) b = c • polar pk a b := by
  funext k
  simp only [polar, Pi.smul_apply, smul_eq_mul]
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  ring

/-- **Kernel translation**: if `B(s, u) = 0` then `P(s + u) = P(s) + P(u)`. -/
theorem qmap_add_of_polar_eq_zero (pk : UOVKey) {s u : ℕ → GF256} (h : polar pk s u = 0) :
    qmap pk (s + u) = qmap pk s + qmap pk u := by
  rw [qmap_add, h, add_zero]

/-- **The preimage line through a singular vector**: if `P(z) = 0` then
`P(s + c • z) = P(s) + c • B(s, z)`. -/
theorem preimage_line (pk : UOVKey) {z : ℕ → GF256} (hz : qmap pk z = 0) (s : ℕ → GF256)
    (c : GF256) : qmap pk (s + c • z) = qmap pk s + c • polar pk s z := by
  rw [qmap_add, qmap_smul, hz, smul_zero, add_zero, polar_smul_right]

/-- **`P` on the span of two vectors.** -/
theorem preimage_plane (pk : UOVKey) (s s' : ℕ → GF256) (α β : GF256) :
    qmap pk (α • s + β • s') =
      α ^ 2 • qmap pk s + β ^ 2 • qmap pk s' + (α * β) • polar pk s s' := by
  rw [qmap_add, qmap_smul, qmap_smul, polar_smul_right, polar_smul_left, smul_smul, mul_comm β α]

/-- **Affine symmetries do not translate targets.** Let `A` and `T` be homogeneous of degree 1
and `P(A s + a) = T(P s) + c` for all `s`. Then `c = P(a)`, `a` is `B`-orthogonal to the image of
`A`, and `P ∘ A = T ∘ P`. -/
theorem affine_symmetry (pk : UOVKey) (A : (ℕ → GF256) → ℕ → GF256) (a : ℕ → GF256)
    (T : (Fin 45 → GF256) → Fin 45 → GF256) (c : Fin 45 → GF256)
    (hA : ∀ (l : GF256) (s : ℕ → GF256), A (l • s) = l • A s)
    (hT : ∀ (l : GF256) (y : Fin 45 → GF256), T (l • y) = l • T y)
    (h : ∀ s, qmap pk (A s + a) = T (qmap pk s) + c) {l : GF256} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    c = qmap pk a ∧ (∀ s, polar pk (A s) a = 0) ∧ ∀ s, qmap pk (A s) = T (qmap pk s) := by
  have hA0 : A 0 = 0 := by simpa using hA 0 0
  have hT0 : T 0 = 0 := by simpa using hT 0 0
  have hP0 : qmap pk 0 = 0 := by simpa using qmap_smul pk 0 0
  have hc : c = qmap pk a := by
    have := h 0
    rw [hA0, zero_add, hP0, hT0, zero_add] at this
    exact this.symm
  have hE : ∀ s, qmap pk (A s) + polar pk (A s) a = T (qmap pk s) := by
    intro s
    have := h s
    rw [qmap_add, hc] at this
    have e : qmap pk (A s) + qmap pk a + polar pk (A s) a =
        qmap pk (A s) + polar pk (A s) a + qmap pk a := by abel
    rw [e] at this
    exact add_right_cancel this
  have hB : ∀ s, polar pk (A s) a = 0 := by
    intro s
    have e1 := hE (l • s)
    rw [hA, qmap_smul, qmap_smul, polar_smul_left, hT, ← hE s, smul_add] at e1
    have e2 : (l - l ^ 2) • polar pk (A s) a = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact add_left_cancel e1
    rcases smul_eq_zero.mp e2 with e3 | e3
    · exfalso
      have : l * (1 - l) = 0 := by rw [← e3]; ring
      rcases mul_eq_zero.mp this with e4 | e4
      · exact h0 e4
      · exact h1 (sub_eq_zero.mp e4).symm
    · exact e3
  exact ⟨hc, hB, fun s => by rw [← hE s, hB s, add_zero]⟩

end VoleMole.Spec.Pqov
