import VoleMole.Spec.PqovShift

/-!
# Symmetries of the UOV public map: the algebraic identities

Identities behind `lean/docs/security/ompr-shift-algebra.md` §8 (Theorem T3: for all but a
negligible fraction of keys, the only symmetries of `P` are the scalings). `P = qmap pk`,
`B = polar pk`. A *symmetry pair* is `(A, T)` with `P(A s) = T(P s)` for all `s`; an
*infinitesimal pair* is `(X, Y)` with `B(s, X s) = Y(P s)` for all `s`. Maps are only assumed
additive, so the statements cover linear and Frobenius-semilinear maps.

* `polar_comm`, `polar_self`: `B` is symmetric, and alternating (characteristic 2).
* `polar_add_left`, `polar_add_right`: `B` is additive in each argument.
* `scaling_symmetry`, `scaling_infinitesimal`: the known pairs `(λ, λ²)` and `(λ, 0)`.
* `symmetry_polar`: a symmetry pair satisfies `B(A s, A u) = T(B(s, u))`.
* `symmetry_eigen`: on an eigenvector `A k = μ • k`, `μ • B(k, A u) = T(B(k, u))`. This is the
  identity that the eigen-probe lemma (§8.3, Lemma E) feeds into the counting.
* `symmetry_kernel_radical`: if `T` is injective, the kernel of `A` lies in the radical of `B`.
  So for a key with `rad B = 0` a pair with `T` injective has `A` injective.
* `infinitesimal_polar`: an infinitesimal pair satisfies `B(s, X u) + B(u, X s) = Y(B(s, u))`.
* `infinitesimal_eigen`: on an eigenvector `X k = μ • k`, `B(k, X u + μ • u) = Y(B(k, u))`.
* `infinitesimal_add_scalar`: `(X, Y)` is an infinitesimal pair iff `(X + c, Y)` is one: the
  solution space contains `F·(I, 0)`, the tangent line of the scalings (`2λ = 0`).
* `infinitesimal_iff_first_order`: `(X, Y)` is an infinitesimal pair iff `(1 + cX, 1 + cY)` is
  a symmetry pair up to the term `c² P(X s)`, for all `c` (over the dual numbers: exactly). This
  is the formal link between the two statements; neither implies the other over a finite field
  (§8.1).
-/

namespace VoleMole.Spec.Pqov

open VoleMole.Arith VoleMole.Arith.UOV

private lemma gf_add_self (a : GF256) : a + a = 0 := by
  have h : -a = a := rfl
  calc a + a = a + -a := by rw [h]
    _ = 0 := add_neg_cancel a

/-- `B` is symmetric. -/
theorem polar_comm (pk : UOVKey) (a b : ℕ → GF256) : polar pk a b = polar pk b a := by
  funext k
  simp only [polar]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  ring

/-- `B` is additive in its second argument. -/
theorem polar_add_right (pk : UOVKey) (a b c : ℕ → GF256) :
    polar pk a (b + c) = polar pk a b + polar pk a c := by
  funext k
  simp only [polar, Pi.add_apply, ← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  ring

/-- `B` is additive in its first argument. -/
theorem polar_add_left (pk : UOVKey) (a b c : ℕ → GF256) :
    polar pk (a + b) c = polar pk a c + polar pk b c := by
  rw [polar_comm, polar_add_right, polar_comm pk c a, polar_comm pk c b]

/-- **`B` is alternating**: `B(s, s) = 0` (characteristic 2). -/
theorem polar_self (pk : UOVKey) (s : ℕ → GF256) : polar pk s s = 0 := by
  funext k
  simp only [polar, Pi.zero_apply]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx
  rw [gf_add_self, mul_zero]

/-- The scalings are symmetry pairs: `P(λ s) = λ² P(s)`. -/
theorem scaling_symmetry (pk : UOVKey) (l : GF256) (s : ℕ → GF256) :
    qmap pk (l • s) = l ^ 2 • qmap pk s := qmap_smul pk l s

/-- Their tangent direction is `(I, 0)`: `B(s, λ s) = 0`. -/
theorem scaling_infinitesimal (pk : UOVKey) (l : GF256) (s : ℕ → GF256) :
    polar pk s (l • s) = 0 := by
  rw [polar_smul_right, polar_self, smul_zero]

/-- **The polar identity of a symmetry pair**: `B(A s, A u) = T(B(s, u))`. -/
theorem symmetry_polar (pk : UOVKey) (A : (ℕ → GF256) → ℕ → GF256)
    (T : (Fin 45 → GF256) → Fin 45 → GF256)
    (hA : ∀ s u, A (s + u) = A s + A u) (hT : ∀ y z, T (y + z) = T y + T z)
    (h : ∀ s, qmap pk (A s) = T (qmap pk s)) (s u : ℕ → GF256) :
    polar pk (A s) (A u) = T (polar pk s u) := by
  have e := h (s + u)
  rw [hA, qmap_add, qmap_add, hT, hT, h s, h u] at e
  exact add_left_cancel e

/-- **The eigen-probe identity**: if `A k = μ • k` then `μ • B(k, A u) = T(B(k, u))`. -/
theorem symmetry_eigen (pk : UOVKey) (A : (ℕ → GF256) → ℕ → GF256)
    (T : (Fin 45 → GF256) → Fin 45 → GF256)
    (hA : ∀ s u, A (s + u) = A s + A u) (hT : ∀ y z, T (y + z) = T y + T z)
    (h : ∀ s, qmap pk (A s) = T (qmap pk s)) {k : ℕ → GF256} {μ : GF256} (hk : A k = μ • k)
    (u : ℕ → GF256) : μ • polar pk k (A u) = T (polar pk k u) := by
  rw [← symmetry_polar pk A T hA hT h k u, hk, polar_smul_left]

/-- **The kernel of `A` lies in the radical of `B`** when `T` is injective. -/
theorem symmetry_kernel_radical (pk : UOVKey) (A : (ℕ → GF256) → ℕ → GF256)
    (T : (Fin 45 → GF256) → Fin 45 → GF256)
    (hA : ∀ s u, A (s + u) = A s + A u) (hT : ∀ y z, T (y + z) = T y + T z)
    (hTinj : ∀ y, T y = 0 → y = 0)
    (h : ∀ s, qmap pk (A s) = T (qmap pk s)) {z : ℕ → GF256} (hz : A z = 0) (u : ℕ → GF256) :
    polar pk z u = 0 := by
  refine hTinj _ ?_
  rw [← symmetry_polar pk A T hA hT h z u, hz]
  have h0 : polar pk 0 (A u) = 0 := by
    simpa using polar_smul_left pk 0 (A u) 0
  exact h0

/-- **The polar identity of an infinitesimal pair**: `B(s, X u) + B(u, X s) = Y(B(s, u))`. -/
theorem infinitesimal_polar (pk : UOVKey) (X : (ℕ → GF256) → ℕ → GF256)
    (Y : (Fin 45 → GF256) → Fin 45 → GF256)
    (hX : ∀ s u, X (s + u) = X s + X u) (hY : ∀ y z, Y (y + z) = Y y + Y z)
    (h : ∀ s, polar pk s (X s) = Y (qmap pk s)) (s u : ℕ → GF256) :
    polar pk s (X u) + polar pk u (X s) = Y (polar pk s u) := by
  have e := h (s + u)
  rw [hX, polar_add_left, polar_add_right, polar_add_right, qmap_add, hY, hY, h s, h u] at e
  have e' : Y (qmap pk s) + Y (qmap pk u) + (polar pk s (X u) + polar pk u (X s)) =
      Y (qmap pk s) + Y (qmap pk u) + Y (polar pk s u) := by
    rw [← e]; abel
  exact add_left_cancel e'

/-- **The eigen-probe identity, infinitesimal form**: if `X k = μ • k` then
`B(k, X u + μ • u) = Y(B(k, u))`. -/
theorem infinitesimal_eigen (pk : UOVKey) (X : (ℕ → GF256) → ℕ → GF256)
    (Y : (Fin 45 → GF256) → Fin 45 → GF256)
    (hX : ∀ s u, X (s + u) = X s + X u) (hY : ∀ y z, Y (y + z) = Y y + Y z)
    (h : ∀ s, polar pk s (X s) = Y (qmap pk s)) {k : ℕ → GF256} {μ : GF256} (hk : X k = μ • k)
    (u : ℕ → GF256) : polar pk k (X u + μ • u) = Y (polar pk k u) := by
  rw [← infinitesimal_polar pk X Y hX hY h k u, hk, polar_add_right, polar_smul_right,
    polar_smul_right, polar_comm pk u k]

/-- **The solution space contains `F·(I, 0)`**: `(X, Y)` is an infinitesimal pair iff
`(X + c, Y)` is one. -/
theorem infinitesimal_add_scalar (pk : UOVKey) (X : (ℕ → GF256) → ℕ → GF256)
    (Y : (Fin 45 → GF256) → Fin 45 → GF256) (c : GF256) :
    (∀ s, polar pk s (X s + c • s) = Y (qmap pk s)) ↔ ∀ s, polar pk s (X s) = Y (qmap pk s) := by
  have e : ∀ s, polar pk s (X s + c • s) = polar pk s (X s) := fun s => by
    rw [polar_add_right, scaling_infinitesimal, add_zero]
  exact forall_congr' fun s => by rw [e s]

/-- **The infinitesimal equation is the first-order part of the symmetry equation.** For the
pair `(1 + c X, 1 + c Y)`, `P(s + c X s) = P(s) + c B(s, X s) + c² P(X s)` and
`(1 + c Y)(P s) = P(s) + c Y(P s)`. So `B(s, X s) = Y(P s)` for all `s` iff the pair is a symmetry
up to the term `c² P(X s)`, for all `c`: over the dual numbers `F[ε]/(ε²)` that is
`P ∘ (1 + ε X) = (1 + ε Y) ∘ P`. Neither the group statement nor the infinitesimal statement
implies the other over a finite field (§8.1). -/
theorem infinitesimal_iff_first_order (pk : UOVKey) (X : (ℕ → GF256) → ℕ → GF256)
    (Y : (Fin 45 → GF256) → Fin 45 → GF256) :
    (∀ s, polar pk s (X s) = Y (qmap pk s)) ↔
      ∀ (c : GF256) (s : ℕ → GF256),
        qmap pk (s + c • X s) = qmap pk s + c • Y (qmap pk s) + c ^ 2 • qmap pk (X s) := by
  constructor
  · intro h c s
    rw [qmap_add, qmap_smul, polar_smul_right, h s]
    abel
  · intro h s
    have e := h 1 s
    rw [qmap_add, one_smul, one_smul, one_pow, one_smul] at e
    have e' : qmap pk s + qmap pk (X s) + polar pk s (X s) =
        qmap pk s + qmap pk (X s) + Y (qmap pk s) := by
      rw [e]; abel
    exact add_left_cancel e'

end VoleMole.Spec.Pqov
