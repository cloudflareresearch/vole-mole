import Mathlib

/-!
# Zero knowledge: the one-time-pad core (`lean/docs/zk.md`, hybrids H5–H7)

The zero-knowledge argument for the VOLE-in-the-Head proof in `src/voleith.hpp` finishes with
perfect hybrids. Each replaces a masked value that the prover reveals with a uniform value. Every
such step has the same shape: the revealed value is a *bijective* image of uniform masks, for every
fixed value of everything else, including the witness. This file proves those bijections and the
counting fact behind "a bijective image of a uniform value is uniform and independent of the
witness".

Distributions are unnormalised: `fiberCard V o` counts the random tapes on which `V` outputs `o`.
Two experiments over the same tape space have the same output distribution iff their `fiberCard`s
agree.

* `fiberCard_equiv`, `fiberCard_shear`: a view made of public data and a masked part, where the mask
  enters through a bijection, has a distribution that does not depend on that bijection. In
  particular, it does not depend on the witness.
* `qsResponse_bijective`: the QuickSilver response for degree `d` (`n = d - 1` masks) is a bijection
  of the masks `u_mask[0..n)`, for any unmasked coefficients, any `q_mask` and any `Δ`
  (faest-arch-opt `quicksilver.hpp:597-611`).
* `kosQs_equiv`, `kosQs_fiberCard`: jointly, the KOS (VOLE check) response and the QuickSilver
  response are a bijection of all `n + 4` masks, even though the KOS hash takes the QuickSilver
  masks as input (`kos_vole_check.hpp:127-129`).
* `corrections_equiv`: the witness correction `d = u₀ + w` and the tree corrections
  `c_i = u₀ + u_i` are a bijection of the tree outputs `(u₀, u_i)` on the witness rows.
* `cmult_equiv`: one bit row of `c_mult = h⁰ ⊕ h¹ ⊕ F·ū` is a bijection of the hash value at the
  sibling label (`vole_commit.inc:497-509 on `voleith-label-rows``).
-/

open Finset

namespace VoleMole.ZK

section Fiber

variable {R R' O X P M : Type*}

/-- The number of random tapes `r` on which the view `V` outputs `o`. Under a uniform tape this is
the unnormalised distribution of `V`. -/
def fiberCard [Fintype R] [DecidableEq O] (V : R → O) (o : O) : ℕ :=
  #(univ.filter fun r => V r = o)

/-- A bijective view is uniform: every output has exactly one preimage. -/
theorem fiberCard_equiv [Fintype R] [DecidableEq O] (e : R ≃ O) (o : O) : fiberCard e o = 1 := by
  unfold fiberCard
  rw [Finset.card_eq_one]
  refine ⟨e.symm o, ?_⟩
  ext r
  simp [← Equiv.eq_symm_apply]

/-- Re-parametrising the tape by a bijection does not change the distribution. -/
theorem fiberCard_comp_equiv [Fintype R] [Fintype R'] [DecidableEq O] (V : R → O) (e : R' ≃ R)
    (o : O) : fiberCard (V ∘ e) o = fiberCard V o := by
  unfold fiberCard
  exact Finset.card_equiv e (by simp)

/-- **Shear lemma.** The tape is `(p, m)`. The view is a public part `π p`, plus a masked part
`φ p m` in which the mask `m` enters through a bijection `φ p` for every `p`. Then the view has the
distribution of `(π p, uniform)`, which does not depend on `φ`. In the zero-knowledge proof, `φ`
depends on the witness and `π` does not. -/
theorem fiberCard_shear [Fintype P] [Fintype M] [DecidableEq X] [DecidableEq O] (π : P → X)
    (φ : P → M ≃ O) (x : X) (o : O) :
    fiberCard (fun r : P × M => (π r.1, φ r.1 r.2)) (x, o) = fiberCard π x := by
  unfold fiberCard
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : π p = x
  · have h1 : (∑ m : M, if φ p m = o then 1 else 0) = 1 := by
      have := fiberCard_equiv (φ p) o
      unfold fiberCard at this
      rwa [Finset.card_filter] at this
    simpa [hp] using h1
  · simp [hp]

/-- Witness independence: two views that differ only in the bijection through which the mask
enters (for instance, real responses for two different witnesses) have the same distribution. -/
theorem fiberCard_shear_indep [Fintype P] [Fintype M] [DecidableEq X] [DecidableEq O]
    (π : P → X) (φ φ' : P → M ≃ O) (x : X) (o : O) :
    fiberCard (fun r : P × M => (π r.1, φ r.1 r.2)) (x, o) =
      fiberCard (fun r : P × M => (π r.1, φ' r.1 r.2)) (x, o) := by
  rw [fiberCard_shear, fiberCard_shear]

end Fiber

section QuickSilver

variable {F : Type*} [CommRing F] {n : ℕ}

/-- `x (k + 1)`, or `0` if `k` is the last index. -/
def nextVal (x : Fin n → F) (k : Fin n) : F :=
  if h : k.val + 1 < n then x ⟨k.val + 1, h⟩ else 0

/-- The QuickSilver response with CRT masks, as `quicksilver.hpp:597-611` computes it. There are
`n = d - 1` masks `u_mask[j]`, with `v_mask[j] = q_mask[j] - Δ·u_mask[j]` (the VOLE relation
`q = v + Δ·u`). The prover's mask polynomial has coefficients `c_0 = v_0`, `c_i = u_{i-1} + v_i` for
`1 ≤ i < n`, and `c_n = u_{n-1}`. Proof element `k ∈ [0, n)` is `c_{k+1}` plus the unmasked
coefficient `H k`, which depends on the witness and the constraints. `c_0` goes into `qs_check`,
which the verifier recomputes and the proof does not contain. -/
def qsResponse (H q : Fin n → F) (Δ : F) (u : Fin n → F) : Fin n → F :=
  fun k => H k + u k + nextVal (fun j => q j - Δ * u j) k

theorem qsResponse_injective (H q : Fin n → F) (Δ : F) :
    Function.Injective (qsResponse H q Δ) := by
  intro u u' h
  -- Downward induction on the index: the map is unit upper-bidiagonal.
  have key : ∀ m : ℕ, ∀ k : Fin n, n ≤ k.val + m → u k = u' k := by
    intro m
    induction m with
    | zero => intro k hk; exact absurd k.isLt (by omega)
    | succ m ih =>
      intro k hk
      have hk' := congrFun h k
      by_cases hlt : k.val + 1 < n
      · have hnext : u ⟨k.val + 1, hlt⟩ = u' ⟨k.val + 1, hlt⟩ := ih _ (by simp; omega)
        simpa [qsResponse, nextVal, hlt, hnext] using hk'
      · simpa [qsResponse, nextVal, hlt] using hk'
  funext k
  exact key n k (by omega)

theorem qsResponse_bijective [Finite F] (H q : Fin n → F) (Δ : F) :
    Function.Bijective (qsResponse H q Δ) :=
  Finite.injective_iff_bijective.mp (qsResponse_injective H q Δ)

/-- The QuickSilver response as a bijection of the masks. -/
noncomputable def qsEquiv [Finite F] (H q : Fin n → F) (Δ : F) : (Fin n → F) ≃ (Fin n → F) :=
  Equiv.ofBijective _ (qsResponse_bijective H q Δ)

/-- The KOS response (`kos_vole_check.hpp:51-65,127-138`): `h_i = mask_{n+i} + G_i`, where `G`
(the universal hash of the witness rows of `u` and of the QuickSilver masks `u_mask[0..n)`,
combined with `chal1`) may depend on anything except the four direct masks `mask_{n..n+4)`. -/
def kosResponse {ι : Type*} (G : (Fin n → F) → ι → F) (uq : Fin n → F) (uk : ι → F) : ι → F :=
  uk + G uq

/-- **KOS + QuickSilver masking.** The map from all `n + |ι|` masks to the two responses is a
bijection, for every witness, unmasked QuickSilver coefficients `H`, KOS hash `G`, `q_mask`, and
`Δ`. -/
noncomputable def kosQsEquiv [Finite F] {ι : Type*} (H q : Fin n → F) (Δ : F)
    (G : (Fin n → F) → ι → F) : (Fin n → F) × (ι → F) ≃ (Fin n → F) × (ι → F) :=
  Equiv.prodShear (qsEquiv H q Δ) fun uq => Equiv.addRight (G uq)

theorem kosQsEquiv_apply [Finite F] {ι : Type*} (H q : Fin n → F) (Δ : F)
    (G : (Fin n → F) → ι → F) (uq : Fin n → F) (uk : ι → F) :
    kosQsEquiv H q Δ G (uq, uk) = (qsResponse H q Δ uq, kosResponse G uq uk) := rfl

/-- With uniform masks, the pair (QuickSilver response, KOS response) is uniform for every witness:
each value has exactly one preimage. -/
theorem kosQs_fiberCard [Fintype F] [DecidableEq F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H q : Fin n → F) (Δ : F) (G : (Fin n → F) → ι → F) (o : (Fin n → F) × (ι → F)) :
    fiberCard (fun m : (Fin n → F) × (ι → F) => (qsResponse H q Δ m.1, kosResponse G m.1 m.2))
      o = 1 :=
  fiberCard_equiv (kosQsEquiv H q Δ G) o

/-- Witness independence of the responses: for two witnesses (unmasked coefficients `H, H'` and
KOS hashes `G, G'`), the response distributions coincide. -/
theorem kosQs_indep [Fintype F] [DecidableEq F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H H' q : Fin n → F) (Δ : F) (G G' : (Fin n → F) → ι → F) (o : (Fin n → F) × (ι → F)) :
    fiberCard (fun m : (Fin n → F) × (ι → F) => (qsResponse H q Δ m.1, kosResponse G m.1 m.2)) o =
      fiberCard
        (fun m : (Fin n → F) × (ι → F) => (qsResponse H' q Δ m.1, kosResponse G' m.1 m.2)) o := by
  rw [kosQs_fiberCard, kosQs_fiberCard]

end QuickSilver

section Corrections

variable {U : Type*} [AddCommGroup U] {τ : ℕ}

/-- The corrections on the witness rows (`voleith.hpp:246-250,293-299 on `voleith-label-rows``, `vole_commit.inc:103-122`):
`d = u₀ + w` and `c_i = u₀ + u_i` for trees `i ≥ 1`. Over `F₂` addition is XOR. -/
def corrections (w : U) (u : U × (Fin τ → U)) : U × (Fin τ → U) :=
  (u.1 + w, fun i => u.1 + u.2 i)

/-- The corrections are a bijection of the tree outputs, for every witness `w`. -/
def correctionsEquiv (w : U) : U × (Fin τ → U) ≃ U × (Fin τ → U) :=
  Equiv.prodShear (Equiv.addRight w) fun u0 => Equiv.addLeft (fun _ => u0)

theorem correctionsEquiv_apply (w : U) (u : U × (Fin τ → U)) :
    correctionsEquiv w u = corrections w u := rfl

/-- With uniform tree outputs, `(d, c_1, …, c_τ)` is uniform for every witness. -/
theorem corrections_fiberCard [Fintype U] [DecidableEq U] (w : U) (o : U × (Fin τ → U)) :
    fiberCard (corrections (τ := τ) w) o = 1 :=
  fiberCard_equiv (correctionsEquiv w) o

end Corrections

section CMult

variable {B : Type*} [AddCommGroup B]

/-- One gate column of `c_mult` (`vole_commit.inc:497-509 on `voleith-label-rows``): `c = h_forced + h_sib + f`, where
`f = (F[e]·ū_m)_m` and `h_forced = H₅(iv, e, L^{γ_e})` is the hash the verifier recomputes. As a
function of the sibling hash `h_sib = H₅(iv, e, L^{1-γ_e})` it is a bijection. So if `H₅` at the
sibling label is uniform and unqueried, `c` is uniform and independent of `f`, that is, of the
masks. -/
def cmultEquiv (hForced f : B) : B ≃ B :=
  (Equiv.addLeft hForced).trans (Equiv.addRight f)

theorem cmultEquiv_apply (hForced f hSib : B) : cmultEquiv hForced f hSib = hForced + hSib + f :=
  rfl

theorem cmult_fiberCard [Fintype B] [DecidableEq B] (hForced f c : B) :
    fiberCard (fun hSib => hForced + hSib + f) c = 1 :=
  fiberCard_equiv (cmultEquiv hForced f) c

end CMult

end VoleMole.ZK
