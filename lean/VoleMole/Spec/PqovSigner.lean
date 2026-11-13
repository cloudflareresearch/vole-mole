import VoleMole.Spec.PqovSignerDefs
import VoleMole.Arith.GF256Field

/-!
# pqov's `ov_derive_preimage` as a `Signer`

`Spec.Signer` (`Spec/Common.lean`) is UOV preimage derivation kept abstract. This file gives a
model of pqov's `ov_derive_preimage` (`subprojects/pqov/src/ov.c`, `ov_preimage_core`, patch
`pqov-patches/0001`) over the field `GF256` (`Arith/GF256Field.lean`), for a public key
`pk : UOVKey` and an oil matrix `O` (`sk->O`, `74 × 45`), and proves it correct for `pk` whenever
`P = pk.eval` vanishes on the oil space (`OilSpace pk O`).

## The model

pqov's attempt `ctr` draws a vinegar vector `v ∈ GF(256)⁷⁴` (`SHAKE256(t ‖ sk_seed ‖
"pqov-derive-preimage" ‖ ctr)`), builds the `45 × 45` linear system `L_v x = t + P₁(v)` with
`L_v = vᵀ·S`, `S_k = (P1_k + P1_kᵀ)·O + P2_k` (`ov_calc_l1_mat`, `batch_quad_trimat_eval`), solves
it by Gaussian elimination if `L_v` is invertible (`gf256mat_gaussian_elim`), and returns
`w = (v + O·x, x)`; otherwise it tries the next `ctr`.

Here `P` is `UOVKey.eval`'s quadratic map `qmap pk` (`Arith.UOV.publicMap 119 45`) and `B` its
polar form (`polar pk`, `P(a + b) = P(a) + P(b) + B(a, b)`, `qmap_add`). With `x₀ = (v, 0)`
(`vinVec v`) and the oil vectors `ō_j = (O_j, e_j)` (`oilVec O j`), pqov's system is
`B(x₀, ō_j)_k = (vᵀ S_k)_j` and `P(x₀) = P₁(v)` (the standard UOV identities: `x₀` is zero on the
oil coordinates), so the model computes the system from the public map: `sysMat pk O v` with
entries `B(x₀, ō_j)_k`, right-hand side `t − P(x₀)` (`= t + P(x₀)` in characteristic 2), the
unique solution `x = L_v⁻¹ (t − P(x₀))` when `det L_v ≠ 0` (any correct elimination returns it),
and `w = x₀ + Σ_j x_j ō_j` (`preimageVec`). The byte-level routines (`gfmat_prod`, the triangular
evaluations, the elimination) are not modelled. The identities with pqov's key layout are theorems
of `Spec/PqovKey.lean`: `B(e_i, ō_j)` is pqov's stored `S = (P1 + P1ᵀ)·O + P2` for every key
(`sysCoef_eq_pqovS`), `P(x₀) = P₁(v)` (`qmap_vinVec_eq`), and `OilSpace` holds exactly when `P3`
is pqov's `UT(Oᵀ(P1·O + P2) + (…)ᵀ)` (`oilSpace_iff_P3Pqov`), so for every key of pqov's key
generation (`pqovKey`, `oilSpace_pqovKey`). The computable definitions are in
`Spec/PqovSignerDefs.lean`; `Spec/PqovSignerExec.lean` runs the model (`lake exe spec_kats`
compares it with the C++ `derive_preimage` on the test key: equal on every KAT target).

**Only 255 vinegars are used.** `ov_preimage_core` increments `n_attempt` *before* trying the
attempt, breaks on success, and then returns `-1` if `MAX_ATTEMPT_VINEGAR <= n_attempt`
(`ov.c:166`): a success at the last attempt (`ctr = 255`, `n_attempt = 256`) is discarded. So pqov
fails iff the vinegars `ctr = 0, …, 254` all give a singular system (whatever `ctr = 255` gives).
`signer pk O vin tries` takes the number of attempts as a parameter; `deriveRef` (pqov) uses
`tries = 255`, and `tries = 256` is the intended behaviour.

## Results

* `qmap_add`, `polar_sum_right`, `polar_sum_left`: `P` is a quadratic form, `B` bilinear.
* **`signer_correct`**: for every `vin` and `tries`, `(signer pk O vin tries).Correct pk` if
  `OilSpace pk O`.
* **`signer_fail`**: the signer fails at `t` only if every attempt `i < tries` gives a singular
  system: `det (sysMat pk O (vin t i)) = 0`.
* `sysMat_eq_sum`: `L_v = Σ_i v_i S_i` with `S = sysCoef pk O` (`S k i j = B(e_i, ō_j)_k`): `L_v`
  is linear in `v`, so for a fixed key it ranges over a subspace of dimension `≤ 74` of the
  `45 × 45` matrices; its law is not the uniform one (`Privacy/MoussakaPqov.lean` bounds the
  fraction of bad vinegars on average over `S`).
* `deriveRef`: the signer with pqov's vinegars (`vinShake`: SHAKE256 of `t ‖ sk_seed ‖ DST ‖ ctr`,
  74 bytes) and 255 attempts; `deriveRef_correct`.
-/

open Finset

namespace VoleMole.Spec.Pqov

open VoleMole.Arith VoleMole.Arith.UOV

/-! ## The public map as a quadratic form -/

lemma list_sum_map_finsum {α ι : Type*} [Fintype ι] (L : List α) (f : α → ι → GF256) :
    (L.map fun a => ∑ j, f a j).sum = ∑ j, (L.map fun a => f a j).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- **`P` is a quadratic form**: `P(a + b) = P(a) + P(b) + B(a, b)`. -/
theorem qmap_add (pk : UOVKey) (a b : ℕ → GF256) :
    qmap pk (a + b) = qmap pk a + qmap pk b + polar pk a b := by
  funext k
  simp only [qmap, publicMap, polar, Pi.add_apply, ← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  ring

/-- **`B` is linear in its second argument.** -/
theorem polar_sum_right {ι : Type*} [Fintype ι] (pk : UOVKey) (a : ℕ → GF256) (y : ι → GF256)
    (b : ι → ℕ → GF256) (k : Fin 45) :
    polar pk a (∑ j, y j • b j) k = ∑ j, y j * polar pk a (b j) k := by
  have e : ∀ m : Monomial, pk.map (m.off + k) * (a m.i * (∑ j, y j • b j) m.j +
      (∑ j, y j • b j) m.i * a m.j) =
      ∑ j, y j * (pk.map (m.off + k) * (a m.i * b j m.j + b j m.i * a m.j)) := by
    intro m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [polar, e]
  rw [list_sum_map_finsum]
  exact Finset.sum_congr rfl fun j _ => by rw [List.sum_map_mul_left]

/-- **`B` is linear in its first argument.** -/
theorem polar_sum_left {ι : Type*} [Fintype ι] (pk : UOVKey) (y : ι → GF256) (a : ι → ℕ → GF256)
    (b : ℕ → GF256) (k : Fin 45) :
    polar pk (∑ i, y i • a i) b k = ∑ i, y i * polar pk (a i) b k := by
  have e : ∀ m : Monomial, pk.map (m.off + k) * ((∑ i, y i • a i) m.i * b m.j +
      b m.i * (∑ i, y i • a i) m.j) =
      ∑ i, y i * (pk.map (m.off + k) * (a i m.i * b m.j + b m.i * a i m.j)) := by
    intro m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [polar, e]
  rw [list_sum_map_finsum]
  exact Finset.sum_congr rfl fun j _ => by rw [List.sum_map_mul_left]

/-- `P` reads only the first `119` coordinates. -/
theorem qmap_congr (pk : UOVKey) {σ τ : ℕ → GF256} (h : ∀ i < 119, σ i = τ i) :
    qmap pk σ = qmap pk τ := by
  funext k
  simp only [qmap, publicMap]
  congr 1
  refine List.map_congr_left fun m hm => ?_
  obtain ⟨hij, hj⟩ := mem_forEachMonomial hm
  rw [h m.i (by omega), h m.j hj]

/-! ## The linear system of one attempt -/

/-- **`P` vanishes on the oil space** `span(ō_j)` (pqov's keys: `P3 = UT(M + Mᵀ)`,
`M = Oᵀ(P1·O + P2)`; `Spec/PqovKey.lean`, `oilSpace_iff_P3Pqov`). -/
def OilSpace (pk : UOVKey) (O : OilMat) : Prop :=
  ∀ y : Fin 45 → GF256, qmap pk (∑ j, y j • oilVec O j) = 0

/-- The oil part: `x = L_v⁻¹ (t − P(x₀))`. -/
noncomputable def oilSol (pk : UOVKey) (O : OilMat) (v : Vin) (t : Bytes) : Fin 45 → GF256 :=
  Matrix.mulVec (sysMat pk O v)⁻¹ (target t - qmap pk (vinVec v))

/-- The preimage `w = x₀ + Σ_j x_j ō_j = (v + O x, x)`. -/
noncomputable def preimageVec (pk : UOVKey) (O : OilMat) (v : Vin) (t : Bytes) : ℕ → GF256 :=
  vinVec v + ∑ j, oilSol pk O v t j • oilVec O j

/-- **One attempt**: the preimage if `L_v` is invertible. -/
noncomputable def attempt (pk : UOVKey) (O : OilMat) (t : Bytes) (v : Vin) : Option Bytes :=
  if (sysMat pk O v).det ≠ 0 then some (toBytes (preimageVec pk O v t)) else none

/-- **pqov's `ov_preimage_core`**: the first successful attempt among `ctr < tries`, the vinegar of
attempt `ctr` at target `t` being `vin t ctr`. -/
noncomputable def signer (pk : UOVKey) (O : OilMat) (vin : Bytes → Fin 256 → Vin) (tries : ℕ) :
    Signer :=
  ⟨fun t => ((List.finRange 256).filter fun i => decide (i.val < tries)).findSome? fun i =>
    attempt pk O t (vin t i)⟩

/-! ## Correctness -/

section Correct

variable (pk : UOVKey) (O : OilMat)

lemma toBytes_length (σ : ℕ → GF256) : (toBytes σ).length = uovN := by
  unfold toBytes; exact List.length_ofFn

lemma getD_toBytes (σ : ℕ → GF256) {i : ℕ} (hi : i < 119) :
    (⟨(toBytes σ).toArray.getD i 0⟩ : GF256) = σ i := by
  have hl : i < (toBytes σ).length := by rw [toBytes_length]; exact hi
  have : (toBytes σ).toArray.getD i 0 = (σ i).val := by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hl,
      Option.getD_some]
    simp only [toBytes, List.getElem_ofFn]
  rw [this]

/-- `P(w) = t` for the attempt's `w`, when `L_v` is invertible and `P` vanishes on the oil space. -/
theorem qmap_preimageVec (hO : OilSpace pk O) (v : Vin) (t : Bytes)
    (hd : (sysMat pk O v).det ≠ 0) :
    qmap pk (preimageVec pk O v t) = target t := by
  have hu : IsUnit (sysMat pk O v).det := isUnit_iff_ne_zero.2 hd
  unfold preimageVec
  rw [qmap_add, hO]
  have hlin : polar pk (vinVec v) (∑ j, oilSol pk O v t j • oilVec O j) =
      Matrix.mulVec (sysMat pk O v) (oilSol pk O v t) := by
    funext k
    rw [polar_sum_right]
    simp only [Matrix.mulVec, dotProduct, sysMat, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hlin, oilSol, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  abel

/-- An attempt's output is a preimage. -/
theorem attempt_correct (hO : OilSpace pk O) (t : Bytes) (ht : t.length = uovM) (v : Vin)
    (s : Bytes) (h : attempt pk O t v = some s) : s.length = uovN ∧ pk.eval s = t := by
  unfold attempt at h
  split_ifs at h with hd
  cases h
  refine ⟨toBytes_length _, ?_⟩
  have hq : qmap pk (fun i => ⟨(toBytes (preimageVec pk O v t)).toArray.getD i 0⟩) = target t := by
    rw [← qmap_preimageVec pk O hO v t hd]
    exact qmap_congr pk fun i hi => getD_toBytes _ hi
  unfold UOVKey.eval
  refine List.ext_getElem (by simp [ht]) fun k h1 h2 => ?_
  have hk : k < 45 := by simpa using h1
  have hk' := congrFun hq ⟨k, hk⟩
  simp only [qmap, target] at hk'
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk]
  rw [hk']
  exact List.getD_eq_getElem _ _ h2

/-- **The model of pqov's `derive_preimage` is correct for `pk`** when `P` vanishes on the oil
space, for every vinegar source and number of attempts. -/
theorem signer_correct (hO : OilSpace pk O) (vin : Bytes → Fin 256 → Vin) (tries : ℕ) :
    (signer pk O vin tries).Correct pk := by
  intro t s ht h
  obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some h
  exact attempt_correct pk O hO t ht _ s hi

/-- **The signer fails only if every attempt `i < tries` gives a singular system.** -/
theorem signer_fail (vin : Bytes → Fin 256 → Vin) (tries : ℕ) (t : Bytes)
    (h : (signer pk O vin tries).derivePreimage t = none) (i : Fin 256) (hi : i.val < tries) :
    (sysMat pk O (vin t i)).det = 0 := by
  have := List.findSome?_eq_none_iff.1 h i (by simp [hi])
  unfold attempt at this
  by_contra hd
  simp [hd] at this

end Correct

/-! ## `L_v` is linear in `v` -/

/-- The unit vinegar `e_i`. -/
def unitVin (i : Fin 74) : Vin := Pi.single i 1

/-- **The coefficients of the system**: `S k i j = B(e_i, ō_j)_k` (pqov's `S_k[i][j]`). -/
def sysCoef (pk : UOVKey) (O : OilMat) : Fin 45 → Fin 74 → Fin 45 → GF256 :=
  fun k i j => polar pk (vinVec (unitVin i)) (oilVec O j) k

lemma vinVec_eq_sum (v : Vin) : vinVec v = ∑ i, v i • vinVec (unitVin i) := by
  funext n
  simp only [vinVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitVin]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩ (fun b _ hb => by simp [hb.symm])
      (by simp)]
    simp
  · simp

/-- **`L_v = Σ_i v_i S_i`.** -/
theorem sysMat_eq_sum (pk : UOVKey) (O : OilMat) (v : Vin) :
    sysMat pk O v = Matrix.of fun k j => ∑ i, v i * sysCoef pk O k i j := by
  ext k j
  simp only [sysMat, Matrix.of_apply, sysCoef]
  rw [vinVec_eq_sum v, polar_sum_left]

/-! ## The reference signer (pqov's vinegar derivation) -/

/-- **pqov's `ov_derive_preimage`** for the key `(pk, O, sk_seed)`: 255 usable attempts. -/
noncomputable def deriveRef (pk : UOVKey) (O : OilMat) (skSeed : Bytes) : Signer :=
  signer pk O (vinShake skSeed) 255

theorem deriveRef_correct (pk : UOVKey) (O : OilMat) (skSeed : Bytes) (hO : OilSpace pk O) :
    (deriveRef pk O skSeed).Correct pk :=
  signer_correct pk O hO _ _

end VoleMole.Spec.Pqov
