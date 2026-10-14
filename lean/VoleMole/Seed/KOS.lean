import VoleMole.SeedExtraction

/-!
# KOS consistency (Lemma L3, the sketch's Claim 2)

Paper proof: `lean/docs/extraction/L3-kos.md`. This file formalizes the whole argument except the
random-oracle step "the response functions are fixed before `chall₁`, which is uniform".

## Model

* `X` is the challenge space (decoded blocks `Δ'`), `e : X → F` the CRT lift, injective on `S`.
* `S` is the set of challenges on which the committed data defines the verifier's responses (every
  dead leaf hidden). `Q : X → Fin L → F` are the `L = ℓ + λ + d − 1` hashed rows (the uncorrected
  witness rows, then the λ dedicated gate-label rows of `CRT_DEDICATED_LABEL_ROWS`, then the first
  `d − 1` masks; `L = ℓ + d − 1` without the flag) and `D : X → Fin 4 → F` the four direct masks. No
  structure is assumed: the mask rows contain H₅ gate terms that are not affine in `Δ'`.
* A challenge `c = (r, s, t) ∈ F⁴ × F⁴ × T` is `chall₁` parsed as in `kos_vole_check.hpp`
  (`matrix`, `keys`, `key_4`; `T` is the set of field elements of degree `< 64`). VOLEHash is
  `h_j = r_j·P_x(s₀) + y_{j+1} + D_j` with `y = (P_x(s₁), P_x(s₂), P_x(s₃), P_x(t))` and
  `P_x = Σ_k x_k X^{L−1−k}` (`uhasher_gfsecpar`, `uhasher_gfsecpar_64`, `combine_hashes`).
* The verifier passes the KOS check at `Δ` iff `VOLEHash(Q(Δ)) + D(Δ) + e(Δ)·ũ = h_V`
  (`kosValue`), where `ũ, h_V` are chosen by the prover after seeing `chall₁`.

## Results

* `affine_of_good`: generic deterministic core (spec Lemma 10.26's extractor). If no triple in `S`
  has a nonzero collinearity defect `cross` killed by the hash, the accepted responses lie on one
  line `v* + e(Δ)·u*`, whatever `(ũ, h_V)`.
* `card_voleHashP_eq_le`: VOLEHash is `(|F|⁻⁴ + n⁵/(|F|⁴|T|))`-almost uniform on nonzero inputs of
  degree `≤ n` (spec Lemma 4.6, without its length restriction).
* `card_not_kosGood_le`: **KOS consistency, counting form.** At most
  `|S|³·(|F|⁴|T| + (L−1)⁵|F|⁴)` of the `|F|⁸|T|` values of `chall₁` are bad.
* `consistent_of_kosGood`, `claim4Hyp_of_kosGood`: on a good `chall₁`, the KOS check yields
  `Claim4Hyp.consistent` for the witness rows, so it chains with `free_tree_holds_witness`.
-/

open Finset Polynomial

set_option linter.unusedSectionVars false

namespace VoleMole.Seed

section Affine

variable {X F R M : Type*} [Field F] [AddCommGroup R] [Module F R] [AddCommGroup M] [Module F M]

/-- The collinearity defect of three responses: zero iff `(e Δᵢ, r Δᵢ)` are collinear (for
distinct lifts). -/
def cross (e : X → F) (r : X → R) (Δ₀ Δ₁ Δ₂ : X) : R :=
  (e Δ₂ - e Δ₀) • (r Δ₁ - r Δ₀) - (e Δ₁ - e Δ₀) • (r Δ₂ - r Δ₀)

lemma map_cross_eq_zero (K : R →ₗ[F] M) (e : X → F) (r : X → R) (u h : M) {Δ₀ Δ₁ Δ₂ : X}
    (h₀ : K (r Δ₀) + e Δ₀ • u = h) (h₁ : K (r Δ₁) + e Δ₁ • u = h)
    (h₂ : K (r Δ₂) + e Δ₂ • u = h) : K (cross e r Δ₀ Δ₁ Δ₂) = 0 := by
  have k₁ : K (r Δ₁ - r Δ₀) = -((e Δ₁ - e Δ₀) • u) := by
    rw [map_sub, sub_smul]; linear_combination (norm := module) h₁ - h₀
  have k₂ : K (r Δ₂ - r Δ₀) = -((e Δ₂ - e Δ₀) • u) := by
    rw [map_sub, sub_smul]; linear_combination (norm := module) h₂ - h₀
  simp only [cross, map_sub, map_smul, k₁, k₂, smul_neg, smul_smul, mul_comm]
  abel

/-- **Deterministic core of the KOS lemma.** Let `K` be the (linear) check hash and suppose every
triple of challenges in `S` with `Δ₀ ≠ Δ₁, Δ₂` whose collinearity defect `K` kills has zero
defect. Then for every `(u, h)` the responses on any `A ⊆ S` passing `K(r Δ) + e(Δ)·u = h` lie on
one line. -/
theorem affine_of_good (K : R →ₗ[F] M) (e : X → F) {S : Set X} (he : Set.InjOn e S) (r : X → R)
    (hgood : ∀ Δ₀ ∈ S, ∀ Δ₁ ∈ S, ∀ Δ₂ ∈ S, Δ₀ ≠ Δ₁ → Δ₀ ≠ Δ₂ →
      K (cross e r Δ₀ Δ₁ Δ₂) = 0 → cross e r Δ₀ Δ₁ Δ₂ = 0)
    {A : Set X} (hA : A ⊆ S) (u h : M) (hacc : ∀ Δ ∈ A, K (r Δ) + e Δ • u = h) :
    ∃ uStar vStar : R, ∀ Δ ∈ A, r Δ = vStar + e Δ • uStar := by
  by_cases h2 : ∃ Δ₀ ∈ A, ∃ Δ₁ ∈ A, Δ₀ ≠ Δ₁
  · obtain ⟨Δ₀, h₀, Δ₁, h₁, hne⟩ := h2
    have hd : e Δ₁ - e Δ₀ ≠ 0 := sub_ne_zero.2 fun h => hne (he (hA h₀) (hA h₁) h.symm)
    refine ⟨(e Δ₁ - e Δ₀)⁻¹ • (r Δ₁ - r Δ₀),
      r Δ₀ - e Δ₀ • ((e Δ₁ - e Δ₀)⁻¹ • (r Δ₁ - r Δ₀)), fun Δ hΔ => ?_⟩
    by_cases hΔ₀ : Δ = Δ₀
    · subst hΔ₀; simp
    have hx := hgood Δ₀ (hA h₀) Δ₁ (hA h₁) Δ (hA hΔ) hne (Ne.symm hΔ₀)
      (map_cross_eq_zero K e r u h (hacc _ h₀) (hacc _ h₁) (hacc _ hΔ))
    simp only [cross] at hx
    have key : r Δ - r Δ₀ = (e Δ₁ - e Δ₀)⁻¹ • ((e Δ - e Δ₀) • (r Δ₁ - r Δ₀)) := by
      rw [sub_eq_zero] at hx
      rw [hx, smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [smul_smul, smul_smul] at *
    linear_combination (norm := module) key
  · push Not at h2
    rcases A.eq_empty_or_nonempty with rfl | ⟨Δ₀, h₀⟩
    · exact ⟨0, 0, fun _ h => h.elim⟩
    · exact ⟨0, r Δ₀, fun Δ hΔ => by rw [h2 Δ hΔ Δ₀ h₀]; simp⟩

end Affine

section Hash

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The polynomial `P_x = Σ_k x_k X^{L-1-k}` that all five polynomial hashes evaluate. -/
noncomputable def hornerPoly {L : ℕ} (x : Fin L → F) : F[X] :=
  ∑ k : Fin L, C (x k) * X ^ (L - 1 - (k : ℕ))

lemma eval_hornerPoly {L : ℕ} (x : Fin L → F) (s : F) :
    (hornerPoly x).eval s = ∑ k : Fin L, x k * s ^ (L - 1 - (k : ℕ)) := by
  simp [hornerPoly, eval_finsetSum]

lemma natDegree_hornerPoly_le {L : ℕ} (x : Fin L → F) : (hornerPoly x).natDegree ≤ L - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun _ _ => (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)

lemma hornerPoly_ne_zero {L : ℕ} {x : Fin L → F} (hx : x ≠ 0) : hornerPoly x ≠ 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hx
  intro h
  have := congrArg (fun p => p.coeff (L - 1 - (k : ℕ))) h
  simp only [hornerPoly, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single k] at this
  · simp at this; exact hk this
  · intro k' _ hk'
    rw [ite_eq_right_iff]
    intro heq
    exfalso
    apply hk'
    have := k.isLt; have := k'.isLt
    ext; omega
  · simp

/-- A VOLEHash challenge `(r, s, t)`: the matrix column `r ∈ F⁴`, the four full keys `s ∈ F⁴`, and
the short key `t ∈ T` (the field elements of degree `< 64`). -/
abbrev Ch (F : Type*) (T : Finset F) := (Fin 4 → F) × (Fin 4 → F) × T

/-- `(y₁, y₂, y₃, y₄) = (P(s₁), P(s₂), P(s₃), P(t))`. -/
def ys (P : F[X]) (s : Fin 4 → F) (t : F) : Fin 4 → F :=
  ![P.eval (s 1), P.eval (s 2), P.eval (s 3), P.eval t]

/-- VOLEHash without the direct masks, as a function of the input polynomial:
`h_j = r_j · P(s₀) + y_{j+1}`. -/
def voleHashP {T : Finset F} (P : F[X]) (c : Ch F T) : Fin 4 → F :=
  fun j => c.1 j * P.eval (c.2.1 0) + ys P c.2.1 c.2.2 j

/-- VOLEHash of `x ∈ F^L` (`kos_vole_check.hpp`, `combine_hashes`), without the direct masks. -/
noncomputable def voleHash {T : Finset F} {L : ℕ} (c : Ch F T) (x : Fin L → F) : Fin 4 → F :=
  voleHashP (hornerPoly x) c

lemma hornerPoly_add {L : ℕ} (x y : Fin L → F) :
    hornerPoly (x + y) = hornerPoly x + hornerPoly y := by
  simp [hornerPoly, add_mul, Finset.sum_add_distrib]

lemma hornerPoly_smul {L : ℕ} (a : F) (x : Fin L → F) :
    hornerPoly (a • x) = C a * hornerPoly x := by
  simp [hornerPoly, Finset.mul_sum, mul_assoc]

/-- VOLEHash is `F`-linear in its input. -/
noncomputable def voleHashL {T : Finset F} {L : ℕ} (c : Ch F T) : (Fin L → F) →ₗ[F] (Fin 4 → F) where
  toFun := voleHash c
  map_add' x y := by
    funext j
    fin_cases j <;> simp [voleHash, voleHashP, ys, hornerPoly_add] <;> ring
  map_smul' a x := by
    funext j
    fin_cases j <;> simp [voleHash, voleHashP, ys, hornerPoly_smul] <;> ring

lemma card_eval_eq_le {P : F[X]} (hP : 0 < P.natDegree) (c : F) :
    #{a : F | P.eval a = c} ≤ P.natDegree := by
  have hQ : P - C c ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [natDegree_sub_C] at this
    simp at this
    omega
  calc #{a : F | P.eval a = c} ≤ (P - C c).roots.toFinset.card :=
        Finset.card_le_card fun a ha => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
          simp [Multiset.mem_toFinset, mem_roots hQ, ha]
    _ ≤ Multiset.card (P - C c).roots := Multiset.toFinset_card_le _
    _ ≤ (P - C c).natDegree := card_roots' _
    _ = P.natDegree := natDegree_sub_C

lemma card_eval_eq_le_subtype (T : Finset F) {P : F[X]} (hP : 0 < P.natDegree) (c : F) :
    #{t : T | P.eval (t : F) = c} ≤ P.natDegree := by
  refine le_trans ?_ (card_eval_eq_le hP c)
  refine Finset.card_le_card_of_injOn Subtype.val (fun t ht => ?_) Subtype.val_injective.injOn
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
  exact ht

/-- **Almost-universality of VOLEHash** (spec Lemma 4.6, for any input length): for a nonzero input
polynomial of degree `≤ n` and any target `v`, at most `|F|⁴·|T| + n⁵·|F|⁴` of the `|F|⁸·|T|`
challenges give `voleHashP P c = v`. -/
theorem card_voleHashP_eq_le (T : Finset F) {P : F[X]} (hP : P ≠ 0) {n : ℕ} (hn : P.natDegree ≤ n)
    (v : Fin 4 → F) :
    #{c : Ch F T | voleHashP P c = v} ≤
      Fintype.card F ^ 4 * #T + n ^ 5 * Fintype.card F ^ 4 := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (fun c : Ch F T => P.eval (c.2.1 0) = 0)]
  simp only [Finset.filter_filter]
  rw [add_comm]
  refine add_le_add ?_ ?_
  · -- `y₀ ≠ 0`: the matrix column `r` is determined by `(s, t)`.
    calc #{c : Ch F T | voleHashP P c = v ∧ ¬P.eval (c.2.1 0) = 0}
        ≤ #(Finset.univ : Finset ((Fin 4 → F) × T)) := by
          refine Finset.card_le_card_of_injOn (fun c => c.2) (fun _ _ => Finset.mem_coe.2
            (Finset.mem_univ _)) ?_
          rintro ⟨r, s, t⟩ hc ⟨r', s', t'⟩ hc' (heq : (s, t) = (s', t'))
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc hc'
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 heq
          have hr : r = r' := funext fun j => by
            have h1 := congrFun hc.1 j
            have h2 := congrFun hc'.1 j
            simp only [voleHashP] at h1 h2
            exact mul_right_cancel₀ hc.2 (add_right_cancel (h1.trans h2.symm))
          rw [hr]
      _ = Fintype.card F ^ 4 * #T := by simp [Fintype.card_prod]
  · -- `y₀ = 0`: `s₀` is a root of `P`, and `s₁, s₂, s₃, t` solve `P(·) = v_j`.
    by_cases hdeg : P.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hdeg] at hP ⊢
      have ha : P.coeff 0 ≠ 0 := fun h => hP (by rw [h, map_zero])
      simp [ha]
    have hpos : 0 < P.natDegree := Nat.pos_of_ne_zero hdeg
    set w : Fin 4 → F := ![0, v 0, v 1, v 2]
    calc #{c : Ch F T | voleHashP P c = v ∧ P.eval (c.2.1 0) = 0}
        ≤ #((Finset.univ : Finset (Fin 4 → F)) ×ˢ
            (Fintype.piFinset (fun k => ({a : F | P.eval a = w k} : Finset F)) ×ˢ
              ({t : T | P.eval (t : F) = v 3} : Finset T))) := by
          refine Finset.card_le_card fun c hc => ?_
          obtain ⟨r, s, t⟩ := c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          obtain ⟨hv, h0⟩ := hc
          have hy : ∀ j, ys P s t j = v j := fun j => by
            have := congrFun hv j
            simpa [voleHashP, h0] using this
          simp only [Finset.mem_product, Finset.mem_univ, Fintype.mem_piFinset,
            Finset.mem_filter, true_and]
          refine ⟨fun k => ?_, by simpa [ys] using hy 3⟩
          fin_cases k
          · simpa [w] using h0
          · simpa [w, ys] using hy 0
          · simpa [w, ys] using hy 1
          · simpa [w, ys] using hy 2
      _ ≤ Fintype.card F ^ 4 * (n ^ 4 * n) := by
          rw [Finset.card_product, Finset.card_product, Fintype.card_piFinset, Finset.card_univ,
            Fintype.card_fun, Fintype.card_fin]
          refine Nat.mul_le_mul_left _ (Nat.mul_le_mul ?_ ?_)
          · calc ∏ k, #({a : F | P.eval a = w k} : Finset F) ≤ n ^ (Finset.univ : Finset (Fin 4)).card :=
                  Finset.prod_le_pow_card _ _ _ fun k _ => (card_eval_eq_le hpos _).trans hn
              _ = n ^ 4 := by simp
          · exact (card_eval_eq_le_subtype T hpos _).trans hn
      _ = n ^ 5 * Fintype.card F ^ 4 := by ring

end Hash

section KOS

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {X : Type*}

/-- The verifier's KOS check value for challenge `Δ`: `VOLEHash(Q(Δ)) + D(Δ) + e(Δ)·ũ`, where `Q` are
the `L = ℓ + λ + d − 1` hashed rows (`ℓ + d − 1` without dedicated label rows) and `D` the four
direct masks. The check passes iff it equals `h_V`. -/
noncomputable def kosValue {T : Finset F} {L : ℕ} (c : Ch F T) (e : X → F) (Q : X → Fin L → F)
    (D : X → Fin 4 → F) (u : Fin 4 → F) (Δ : X) : Fin 4 → F :=
  voleHash c (Q Δ) + D Δ + e Δ • u

/-- `chall₁ = c` is *good* for the response functions `(Q, D)` on `S`: whatever `(ũ, h_V)` the
prover sends after seeing `c`, the responses on every set `A ⊆ S` of challenges passing the KOS
check lie on one line `v* + e(Δ)·u*`, in all hashed rows and all four direct masks. -/
def KOSGood {T : Finset F} {L : ℕ} (c : Ch F T) (S : Set X) (e : X → F) (Q : X → Fin L → F)
    (D : X → Fin 4 → F) : Prop :=
  ∀ (u h : Fin 4 → F) (A : Set X), A ⊆ S → (∀ Δ ∈ A, kosValue c e Q D u Δ = h) →
    ∃ uQ vQ : Fin L → F, ∃ uD vD : Fin 4 → F,
      ∀ Δ ∈ A, Q Δ = vQ + e Δ • uQ ∧ D Δ = vD + e Δ • uD

/-- The full VOLEHash including the direct masks, as a linear map on `(Q, D)`. -/
noncomputable def kosHashL {T : Finset F} {L : ℕ} (c : Ch F T) :
    ((Fin L → F) × (Fin 4 → F)) →ₗ[F] (Fin 4 → F) :=
  (voleHashL c).coprod LinearMap.id

/-- Deterministic core: if no triple of distinct challenges in `S` has a nonzero collinearity
defect in the hashed rows that VOLEHash maps to minus the defect in the direct masks, `c` is
good. -/
theorem kosGood_of_no_bad_triple {T : Finset F} {L : ℕ} (c : Ch F T) {S : Set X} {e : X → F}
    (he : Set.InjOn e S) (Q : X → Fin L → F) (D : X → Fin 4 → F)
    (hno : ∀ Δ₀ ∈ S, ∀ Δ₁ ∈ S, ∀ Δ₂ ∈ S, cross e Q Δ₀ Δ₁ Δ₂ ≠ 0 →
      voleHash c (cross e Q Δ₀ Δ₁ Δ₂) ≠ -cross e D Δ₀ Δ₁ Δ₂) :
    KOSGood c S e Q D := by
  intro u h A hA hacc
  have hcross : ∀ Δ₀ Δ₁ Δ₂, cross e (fun Δ => (Q Δ, D Δ)) Δ₀ Δ₁ Δ₂ =
      (cross e Q Δ₀ Δ₁ Δ₂, cross e D Δ₀ Δ₁ Δ₂) := fun _ _ _ => rfl
  obtain ⟨uStar, vStar, hline⟩ := affine_of_good (kosHashL c) e he (fun Δ => (Q Δ, D Δ))
    (fun Δ₀ h₀ Δ₁ h₁ Δ₂ h₂ _ _ hK => by
      rw [hcross] at hK ⊢
      have hK' : voleHash c (cross e Q Δ₀ Δ₁ Δ₂) + cross e D Δ₀ Δ₁ Δ₂ = 0 := hK
      by_cases hQ : cross e Q Δ₀ Δ₁ Δ₂ = 0
      · have h0 : voleHash c (cross e Q Δ₀ Δ₁ Δ₂) = 0 := by
          rw [hQ]; exact (voleHashL c).map_zero
        rw [h0, zero_add] at hK'
        rw [hQ, hK']; rfl
      · exact absurd (eq_neg_of_add_eq_zero_left hK') (hno Δ₀ h₀ Δ₁ h₁ Δ₂ h₂ hQ))
    hA u h (fun Δ hΔ => hacc Δ hΔ)
  exact ⟨uStar.1, vStar.1, uStar.2, vStar.2, fun Δ hΔ =>
    ⟨congrArg Prod.fst (hline Δ hΔ), congrArg Prod.snd (hline Δ hΔ)⟩⟩

open Classical in
/-- **KOS consistency, counting form.** For response functions `(Q, D)` fixed before `chall₁` on a
finite set `S` of challenges with injective lift, the number of bad challenges is at most
`|S|³ · (|F|⁴·|T| + (L−1)⁵·|F|⁴)`. Dividing by `|Ch| = |F|⁸·|T|`, the probability over `chall₁` is
at most `|S|³·(|F|⁻⁴ + (L−1)⁵/(|F|⁴·|T|))`. -/
theorem card_not_kosGood_le (T : Finset F) {L : ℕ} (S : Finset X) {e : X → F}
    (he : Set.InjOn e S) (Q : X → Fin L → F) (D : X → Fin 4 → F) :
    #{c : Ch F T | ¬KOSGood c (S : Set X) e Q D} ≤
      #S ^ 3 * (Fintype.card F ^ 4 * #T + (L - 1) ^ 5 * Fintype.card F ^ 4) := by
  set B := Fintype.card F ^ 4 * #T + (L - 1) ^ 5 * Fintype.card F ^ 4
  let bad : X × X × X → Finset (Ch F T) := fun τ =>
    {c | cross e Q τ.1 τ.2.1 τ.2.2 ≠ 0 ∧
      voleHash c (cross e Q τ.1 τ.2.1 τ.2.2) = -cross e D τ.1 τ.2.1 τ.2.2}
  have hsub : ({c : Ch F T | ¬KOSGood c (S : Set X) e Q D} : Finset _) ⊆
      (S ×ˢ S ×ˢ S).biUnion bad := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    by_contra hnot
    refine hc (kosGood_of_no_bad_triple c he Q D fun Δ₀ h₀ Δ₁ h₁ Δ₂ h₂ hQ hV => hnot ?_)
    exact Finset.mem_biUnion.2 ⟨(Δ₀, Δ₁, Δ₂), by simp_all, by simp [bad, hQ, hV]⟩
  have hbad : ∀ τ ∈ S ×ˢ S ×ˢ S, #(bad τ) ≤ B := fun τ _ => by
    by_cases hQ : cross e Q τ.1 τ.2.1 τ.2.2 = 0
    · simp [bad, hQ]
    · refine le_trans (Finset.card_le_card fun c hc => ?_)
        (card_voleHashP_eq_le T (hornerPoly_ne_zero hQ) (natDegree_hornerPoly_le _)
          (-cross e D τ.1 τ.2.1 τ.2.2))
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact hc.2
  calc _ ≤ #((S ×ˢ S ×ˢ S).biUnion bad) := Finset.card_le_card hsub
    _ ≤ ∑ τ ∈ S ×ˢ S ×ˢ S, #(bad τ) := Finset.card_biUnion_le
    _ ≤ #(S ×ˢ S ×ˢ S) * B := Finset.sum_le_card_nsmul _ _ _ hbad
    _ = #S ^ 3 * B := by rw [Finset.card_product, Finset.card_product]; ring

/-- On a good `chall₁`, the KOS check gives exactly `Claim4Hyp.consistent` for the witness rows
`j < ℓ ≤ L`: `Q[j](Δ) = v_j + u*[j]·e(Δ)` on `A` with one `u* ∈ F^ℓ`. -/
theorem consistent_of_kosGood {T : Finset F} {L ℓ : ℕ} (hℓ : ℓ ≤ L) {c : Ch F T} {S : Set X}
    {e : X → F} {Q : X → Fin L → F} {D : X → Fin 4 → F} (hc : KOSGood c S e Q D)
    {A : Set X} (hA : A ⊆ S) (u h : Fin 4 → F) (hacc : ∀ Δ ∈ A, kosValue c e Q D u Δ = h) :
    ∃ uStar : Fin ℓ → F, ∀ j, ∃ v, ∀ Δ ∈ A, Q Δ (Fin.castLE hℓ j) = v + uStar j * e Δ := by
  obtain ⟨uQ, vQ, _, _, hline⟩ := hc u h A hA hacc
  refine ⟨fun j => uQ (Fin.castLE hℓ j), fun j => ⟨vQ (Fin.castLE hℓ j), fun Δ hΔ => ?_⟩⟩
  have := congrFun (hline Δ hΔ).1 (Fin.castLE hℓ j)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
  rw [this, mul_comm]

/-- **Chaining with Claim 4.** On a good `chall₁`, the KOS hypothesis of `Claim4Hyp` is discharged:
given the other three fields, there is `u*` with `Claim4Hyp e A known u Q' u*`, where
`Q'[j] = Q[j]` on the witness rows `j < ℓ`. -/
theorem claim4Hyp_of_kosGood {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*}
    [∀ i, AddCommGroup (B i)] {T : Finset F} {L ℓ : ℕ} (hℓ : ℓ ≤ L) {c : Ch F T}
    {e : (∀ i, B i) →+ F} {S A : Set (∀ i, B i)} {known : Finset ι} {u : ι → Fin ℓ → Bool}
    {Q : (∀ i, B i) → Fin L → F} {D : (∀ i, B i) → Fin 4 → F} (hc : KOSGood c S e Q D)
    (hA : A ⊆ S) (ũ h : Fin 4 → F) (hacc : ∀ Δ ∈ A, kosValue c e Q D ũ Δ = h)
    (lift_inj : Function.Injective e)
    (tree_form : ∀ j, ∃ c, ∀ Δ ∈ A, Q Δ (Fin.castLE hℓ j) =
      c + ∑ i ∈ known, SeedExtraction.bit (u i j) * SeedExtraction.blockLift e i (Δ i))
    (unknown_fixed : ∀ i ∉ known, SeedExtraction.IsFixed A i) :
    ∃ uStar : Fin ℓ → F,
      SeedExtraction.Claim4Hyp e A known u (fun j Δ => Q Δ (Fin.castLE hℓ j)) uStar := by
  obtain ⟨uStar, hcons⟩ := consistent_of_kosGood hℓ hc hA ũ h hacc
  exact ⟨uStar, lift_inj, tree_form, hcons, unknown_fixed⟩

end KOS

end VoleMole.Seed
