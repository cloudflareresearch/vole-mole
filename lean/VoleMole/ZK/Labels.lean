import VoleMole.ZK.Masking

/-!
# Zero knowledge: VOLE correlation, gate labels, and the sibling-label attack (`lean/docs/zk.md` §§3–4)

Two label layouts. FAEST's default (`main` before `64fd1a4`, and on `main` the relations that set
`REUSE_CRT_WITNESS`: Moussaka and Ratatouille) derives the CRT gate labels from the first λ witness rows. On branch
`voleith-label-rows` (patch 0005) the relations set `CRT_DEDICATED_LABEL_ROWS`, and the labels come
from λ dedicated rows `[ℓ, ℓ+λ)` after the witness, which carry corrections `c_i` but no `d`; that
layout is in `LabelRows.lean`. Line numbers marked "main" are `vole_commit.inc` with patches
0001–0004; with patch 0005 they shift by +34 after line 338.

**Both layouts:**
* `vole_v_unique`, `vole_u_uniform_given_q`: given `Δ` and the verifier's keys `q`, every value of
  the prover's `u` is consistent with exactly one `v`. So `q` (all that the opened seeds, the
  corrections and `d` determine) carries no information about `u`, and the prover's `v = q - Δ·u`
  is determined by `u` and public data (hybrid H5 in `lean/docs/zk.md`).
* `label_q_eq`: the verifier's gate label `Σ_j G[e][j]·q_j` equals the prover's
  `L⁰_e = Σ_j G[e][j]·v_j` plus `γ_e·u` with `γ_e = Σ_j G[e][j]·Δ_j`, where `u` is the prover's
  input on the label rows (main `vole_commit.inc:364-369`; patched `:398`, `:403`, `crt_labels`
  `:351-372`; `crt_vole_helpers.inc:607-613`).

**Unpatched layout only** (label rows = first λ witness rows, offset `u[0..λ) = d[0..λ) ⊕ w[0..λ)`):
* `sibling_eq` and `attack_recovers`: over `F₂` (`x + x = 0`), the label the verifier does *not*
  learn is `L^{γ} + d[0..λ) + w[0..λ)`, and a verifier who knows `w[0..λ)` recovers
  `F[e]·ū_m = c_mult[m, e] ⊕ H₅(L^γ) ⊕ H₅(L^γ ⊕ d ⊕ w)` exactly. This is the deterministic core of
  the attack in `lean/docs/zk.md` §4: the masks, and then the KOS and QuickSilver responses, are unmasked
  whenever `w[0..λ)` is predictable.
* `query_hits_sibling_iff`: one `H₅` query hits the sibling label for exactly one guess of
  `w[0..λ)`. This gives the `q_{H₅} · 2^{-H∞(w[0..λ))}` term of the unpatched bound.

The definitions `forced` and `sibling` are layout-independent: they take the offset as an argument.
-/

open Finset

namespace VoleMole.ZK

section VoleRelation

variable {K U : Type*} [CommRing K] [AddCommGroup U] [Module K U] {J : Type*}

/-- For fixed `Δ`, `q` and `u`, there is exactly one `v` with `v_j + Δ_j • u = q_j` for all `j`.
-/
theorem vole_v_unique (Δ : J → K) (q : J → U) (u : U) :
    ∃! v : J → U, ∀ j, v j + Δ j • u = q j :=
  ⟨fun j => q j - Δ j • u, fun _ => sub_add_cancel _ _, fun _ hv =>
    funext fun j => eq_sub_of_add_eq (hv j)⟩

/-- Counting form: among all pairs `(u, v)` consistent with the verifier's keys `q`, each `u0`
occurs exactly once. With uniform `(u, v)`, `u` is uniform and independent of `q`. -/
theorem vole_u_uniform_given_q [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]
    (Δ : J → K) (q : J → U) (u0 : U) :
    #(univ.filter fun uv : U × (J → U) => (∀ j, uv.2 j + Δ j • uv.1 = q j) ∧ uv.1 = u0) = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨(u0, fun j => q j - Δ j • u0), ?_⟩
  ext ⟨u, v⟩
  simp only [mem_filter, mem_univ, true_and, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hv, rfl⟩
    exact ⟨rfl, funext fun j => eq_sub_of_add_eq (hv j)⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨fun j => sub_add_cancel _ _, rfl⟩

/-- The gate labels. The prover's label is `L⁰_e = Σ_j G[e][j]·v_j` over the λ label rows of the
VOLE columns (the first λ rows unpatched, rows `[ℓ, ℓ+λ)` with dedicated label rows). The verifier's label `Σ_j G[e][j]·q_j` equals `L⁰_e + γ_e·u` with
`γ_e = Σ_j G[e][j]·Δ_j`. -/
theorem label_q_eq [Fintype J] (g Δ : J → K) (v : J → U) (u : U) :
    ∑ j, g j • (v j + Δ j • u) = ∑ j, g j • v j + (∑ j, g j * Δ j) • u := by
  simp only [smul_add, Finset.sum_add_distrib, Finset.sum_smul, mul_smul]

end VoleRelation

section Sibling

/-! Labels live in an `F₂`-vector space, modelled as an additive group with `x + x = 0`. -/

variable {L B : Type*} [AddCommGroup L] [AddCommGroup B]

/-- The label the verifier learns (`L^{γ}`), given the prover's `L⁰` and the offset `u` (the prover's
VOLE input on the label rows: `u[0..λ)` unpatched, `Θ = u[ℓ..ℓ+λ)` patched). -/
def forced (L0 u : L) (γ : Bool) : L := if γ then L0 + u else L0

/-- The label the verifier does not learn (`L^{1-γ}`). -/
def sibling (L0 u : L) (γ : Bool) : L := if γ then L0 else L0 + u

variable (h2L : ∀ x : L, x + x = 0)
include h2L

/-- **Unpatched layout.** The sibling is the forced label plus `u[0..λ)`, and
`u[0..λ) = d[0..λ) + w[0..λ)` because `d = u + w` is public. So the sibling label is public data plus
the first λ witness bits. With dedicated label rows, see `sibling_eq_labelRows` instead. -/
theorem sibling_eq (L0 u w : L) (γ : Bool) :
    sibling L0 u γ = forced L0 u γ + (u + w) + w := by
  have hw : (u + w) + w = u := by rw [add_assoc, h2L, add_zero]
  rw [add_assoc, hw]
  cases γ
  · simp [sibling, forced]
  · simp [sibling, forced, add_assoc, h2L]

/-- **Unpatched layout.** A single `H₅` query `forced + d + g` hits the sibling label iff the guess
`g` equals `w[0..λ)`. So each query tests one candidate for the first λ witness bits. With dedicated
label rows, see `query_hits_sibling_iff_labelRows`. -/
theorem query_hits_sibling_iff (L0 u w g : L) (γ : Bool) :
    forced L0 u γ + (u + w) + g = sibling L0 u γ ↔ g = w := by
  rw [sibling_eq h2L L0 u w γ]
  exact add_left_cancel_iff

variable (h2B : ∀ x : B, x + x = 0)
include h2B

/-- **The attack, deterministically (unpatched layout).** Let `c = H(L⁰) + H(L⁰ + u) + f` (main
`vole_commit.inc:463-475`, patched `:497-509`, with `f = (F[e]·ū_m)_m`). A verifier who knows the
forced label, `d = u + w` and `w` recovers `f`, for every hash function `H`. -/
theorem attack_recovers (H : L → B) (L0 u w : L) (f : B) (γ : Bool) :
    (H L0 + H (L0 + u) + f) + H (forced L0 u γ) + H (forced L0 u γ + (u + w) + w) = f := by
  have hsib := sibling_eq h2L L0 u w γ
  rw [← hsib]
  cases γ
  · simp only [forced, sibling, Bool.false_eq_true, ↓reduceIte]
    calc H L0 + H (L0 + u) + f + H L0 + H (L0 + u)
        = f + (H L0 + H L0) + (H (L0 + u) + H (L0 + u)) := by abel
      _ = f := by rw [h2B, h2B, add_zero, add_zero]
  · simp only [forced, sibling, ↓reduceIte]
    calc H L0 + H (L0 + u) + f + H (L0 + u) + H L0
        = f + (H L0 + H L0) + (H (L0 + u) + H (L0 + u)) := by abel
      _ = f := by rw [h2B, h2B, add_zero, add_zero]

end Sibling

end VoleMole.ZK
