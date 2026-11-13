import VoleMole.Spec.PqovShift

/-!
# Vinegar reuse and the cone of good vinegars

Two algebraic facts used by `lean/docs/security/ompr-cryptanalysis.md` (attacks on one-more
preimage resistance that use the `derive_preimage` oracle).

* `vinegar_reuse`: two answers of the signer with the **same** vinegar `v` (and an invertible
  system `L_v`) on targets `t ≠ t'` differ by a nonzero vector of the oil space,
  `w - w' = Σ_j y_j • ō_j`, and `P(w - w') = 0`. This is attack K1 of the note. It is why the
  vinegar of `ov_derive_preimage` is a hash of the target: distinct targets get independent
  vinegars.
* `sysMat_smul`, `det_sysMat_smul`, `good_smul_iff`: `L_{c v} = c • L_v`, so the good vinegars
  (`det L_v ≠ 0`) form a cone. This is used by Lemma F of the note (the characters of the bad set).
-/

namespace VoleMole.Spec.Pqov

open VoleMole.Arith VoleMole.Arith.UOV

variable (pk : UOVKey) (O : OilMat)

/-- Two answers with the same vinegar differ by an element of the oil space. -/
theorem preimageVec_sub_same_vinegar (v : Vin) (t t' : Bytes) :
    preimageVec pk O v t - preimageVec pk O v t' =
      ∑ j, (oilSol pk O v t j - oilSol pk O v t' j) • oilVec O j := by
  unfold preimageVec
  simp only [sub_smul, Finset.sum_sub_distrib]
  abel

/-- **Vinegar reuse reveals an oil vector** (attack K1). If `L_v` is invertible and the targets
differ, the two answers `w`, `w'` computed with the vinegar `v` differ by a nonzero oil vector, on
which `P` vanishes. -/
theorem vinegar_reuse (hO : OilSpace pk O) (v : Vin) (t t' : Bytes)
    (hd : (sysMat pk O v).det ≠ 0) (ht : target t ≠ target t') :
    preimageVec pk O v t - preimageVec pk O v t' ≠ 0 ∧
      (∃ y : Fin 45 → GF256, preimageVec pk O v t - preimageVec pk O v t' = ∑ j, y j • oilVec O j) ∧
      qmap pk (preimageVec pk O v t - preimageVec pk O v t') = 0 := by
  refine ⟨fun h => ht ?_, ⟨_, preimageVec_sub_same_vinegar pk O v t t'⟩, ?_⟩
  · rw [← qmap_preimageVec pk O hO v t hd, ← qmap_preimageVec pk O hO v t' hd,
      sub_eq_zero.1 h]
  · rw [preimageVec_sub_same_vinegar]
    exact hO _

/-- `vinVec` is homogeneous. -/
lemma vinVec_smul (c : GF256) (v : Vin) : vinVec (c • v) = c • vinVec v := by
  funext i
  simp only [vinVec, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- `L_{c v} = c • L_v`. -/
theorem sysMat_smul (c : GF256) (v : Vin) : sysMat pk O (c • v) = c • sysMat pk O v := by
  ext k j
  simp only [sysMat, Matrix.of_apply, Matrix.smul_apply, vinVec_smul, smul_eq_mul]
  exact congrFun (polar_smul_left pk (vinVec v) (oilVec O j) c) k

/-- `det L_{c v} = c^45 · det L_v`. -/
theorem det_sysMat_smul (c : GF256) (v : Vin) :
    (sysMat pk O (c • v)).det = c ^ 45 * (sysMat pk O v).det := by
  rw [sysMat_smul, Matrix.det_smul, Fintype.card_fin]

/-- **The good vinegars form a cone**: for `c ≠ 0`, `c • v` is good iff `v` is. -/
theorem good_smul_iff {c : GF256} (hc : c ≠ 0) (v : Vin) :
    (sysMat pk O (c • v)).det ≠ 0 ↔ (sysMat pk O v).det ≠ 0 := by
  rw [det_sysMat_smul]
  simp [hc]

end VoleMole.Spec.Pqov
