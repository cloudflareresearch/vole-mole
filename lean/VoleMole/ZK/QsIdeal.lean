import VoleMole.Verifier.Bridge.Prover

/-!
# The prover's QuickSilver coefficients, explicitly (`lean/docs/zk.md` H7)

`Prover.qsProve` evaluates the verifier's check value `G(Δ')` at `d + 1` points and interpolates.
`G` is the check polynomial `P₀ = sysCheckPoly(keys, cs, d, χ, maskPoly d ṽ_mask u_mask 0 0)`
(`Bridge.qsAt_eq`), so the prover's `ã_k` is the coefficient `P₀[k + 1]`, and the masks enter it as
`maskPoly`'s coefficient `[k + 1 < d − 1] ṽ_mask[k + 1] + u_mask[k]` (`maskPoly_coeff`): the
QuickSilver response of `ZK/Masking.lean`, unit-bidiagonal in the masks.

* `InterpOk d`: Newton interpolation at the sample points `1, …, d + 1` returns the coefficients
  of every polynomial of degree `≤ d`. **This is a hypothesis** (a deterministic fact about
  `Prover.interpolate`; the prover itself checks its output on every proof, and
  `lake exe prover_vectors` runs it on all KAT proofs).
* `qsProve_eq`: for a witness that satisfies the system (`hsat`), `qsProve` succeeds with
  `(P₀[0], (P₀[k + 1])_{k < d − 1})`.
-/

open Finset Polynomial

namespace VoleMole.ZK

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.EndToEnd

/-- The `d + 1` sample points of `Prover.qsProve`. -/
def samplePts (d : ℕ) : Array GF128 := (Array.range (d + 1)).map Prover.samplePt

/-- **Interpolation is correct** at the sample points, for polynomials of degree `≤ d`. -/
def InterpOk (d : ℕ) : Prop :=
  ∀ P : GF128[X], P.natDegree ≤ d →
    Prover.interpolate (samplePts d) ((samplePts d).map P.eval) = (Array.range (d + 1)).map P.coeff

/-- The witness bits as field elements (the slopes of the witness MACs). -/
noncomputable def wSlope (p : Params) (w : ByteArray) (j : ℕ) : GF128 :=
  if j < p.witnessBits ∧ Prover.bitOf w j then 1 else 0

lemma polyOf_coeffs (P : GF128[X]) {d : ℕ} (hP : P.natDegree ≤ d) :
    polyOf ((Array.range (d + 1)).map P.coeff) = P := by
  rw [polyOf]
  conv_rhs => rw [P.as_sum_range' (d + 1) (by omega)]
  simp only [Array.size_map, Array.size_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← C_mul_X_pow_eq_monomial]
  congr 2
  rw [List.getD_eq_getElem?_getD]
  simp [Finset.mem_range.1 hi]

lemma sysCheckPoly_add (q : ℕ → GF128[X]) (cs : System GF128) (d : ℕ)
    (χ : Fin cs.length → GF128) (R : GF128[X]) :
    sysCheckPoly q cs d χ R = sysCheckPoly q cs d χ 0 + R := by
  simp [sysCheckPoly, Seed.checkPoly]

/-- The masks' coefficients in the check polynomial. -/
lemma maskPoly_coeff (d : ℕ) (a b : ℕ → GF128) {i : ℕ} (hi1 : 1 ≤ i) (hid : i ≤ d - 1) :
    (Seed.maskPoly d a b (fun _ => 0) 0).coeff i = (if i < d - 1 then a i else 0) + b (i - 1) := by
  simp only [Seed.maskPoly, map_zero, zero_mul, Finset.sum_const_zero, add_zero, finsetSum_coeff,
    add_mul, coeff_add, mul_assoc, ← pow_succ', coeff_C_mul_X_pow, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq (range (d - 1)) i a]
  have : ∀ j ∈ range (d - 1), (if i = j + 1 then b j else 0) = if i - 1 = j then b j else 0 :=
    fun j _ => by
      by_cases h : i - 1 = j
      · simp [show i = j + 1 by omega]
      · simp [h, show i ≠ j + 1 by omega]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq (range (d - 1)) (i - 1) b]
  simp only [Finset.mem_range, show i - 1 < d - 1 by omega, ↓reduceIte]

/-- The check polynomial of `Prover.qsProve` (`ã = 0`). -/
noncomputable def qsPoly (p : Params) (c2 : ByteArray) (cs : System GF128)
    (vRows vMask uMask : Array W128) (w : ByteArray) : GF128[X] :=
  sysCheckPoly (keyPoly p vRows w) cs p.qsDegree
    (Seed.zkCoeff cs.length (gfOfBytes c2 0) (gfOfBytes c2 16) (gfOfBytes c2 32)
      ⟨W128.word c2 48, 0⟩)
    (Seed.maskPoly p.qsDegree (fun i => vMask[i]!.toGF) (fun i => uMask[i]!.toGF) (fun _ => 0) 0)

/-- **The prover's QuickSilver output, explicitly.** For a witness satisfying the system, with
`ã = 0` in `pf0` and correct interpolation, `qsProve` returns the coefficients of `qsPoly`. -/
theorem qsProve_eq (pf0 : Proof) (c2 : ByteArray) (values : (ℕ → GF128) → List GF128)
    (vRows vMask uMask : Array W128) (w : ByteArray) (cs : System GF128)
    (hvals : ∀ x, values x = cs.values x) (hdeg : ∀ e ∈ cs, e.degree ≤ pf0.params.qsDegree)
    (hd : 1 ≤ pf0.params.qsDegree) (hd' : pf0.params.qsDegree + 1 < 2 ^ 64)
    (h0 : ∀ i, gfOfBytes pf0.qsProof (16 * i) = 0) (hI : InterpOk pf0.params.qsDegree)
    (hsat : cs.Holds (wSlope pf0.params w)) :
    Prover.qsProve pf0 c2 values vRows vMask uMask w =
      .ok ((qsPoly pf0.params c2 cs vRows vMask uMask w).coeff 0,
        (Array.range (pf0.params.qsDegree - 1)).map fun i =>
          (qsPoly pf0.params c2 cs vRows vMask uMask w).coeff (i + 1)) := by
  set d := pf0.params.qsDegree with hdd
  set P0 := qsPoly pf0.params c2 cs vRows vMask uMask w with hP0
  have hã : (fun i => gfOfBytes pf0.qsProof (16 * (i - 1))) = fun _ => (0 : GF128) :=
    funext fun i => h0 _
  have hG : ∀ y ≠ 0, Prover.qsAt pf0 c2 values vRows vMask uMask w y = P0.eval y := by
    intro y hy
    rw [qsAt_eq pf0 c2 values vRows vMask uMask w cs hvals hdeg hy, hã]
    rfl
  have hdegP : P0.natDegree ≤ d ∧ P0.coeff d = ∑ k, _ :=
    sysCheckPoly_natDegree_coeff hd cs hdeg (keyPoly pf0.params vRows w)
      (fun j => (keyPoly pf0.params vRows w j).coeff 1)
      (fun j => ⟨(keyPoly_deg _ _ _ j).1, rfl⟩) _ _ (Seed.maskPoly_natDegree_le _ _ _ _ _)
  have hslope : (fun j => (keyPoly pf0.params vRows w j).coeff 1) = wSlope pf0.params w :=
    funext fun j => (keyPoly_deg _ _ _ j).2
  have htop : P0.coeff d = 0 := by
    rw [hdegP.2, hslope, (holds_iff_valVec_eq_zero cs _).1 hsat]
    simp
  have hys : (samplePts d).map (Prover.qsAt pf0 c2 values vRows vMask uMask w) =
      (samplePts d).map P0.eval := by
    refine Array.map_congr_left fun x hx => hG x ?_
    obtain ⟨k, hk, rfl⟩ := Array.mem_map.1 hx
    exact samplePt_ne_zero (by have := Array.mem_range.1 hk; omega)
  have hg : Prover.interpolate (samplePts d) ((samplePts d).map
      (Prover.qsAt pf0 c2 values vRows vMask uMask w)) = (Array.range (d + 1)).map P0.coeff := by
    rw [hys]; exact hI P0 hdegP.1
  unfold Prover.qsProve
  simp only [← hdd]
  change (do
    let g := Prover.interpolate (samplePts d) ((samplePts d).map
      (Prover.qsAt pf0 c2 values vRows vMask uMask w))
    if g.size != d + 1 then throw "QuickSilver: interpolation failed"
    if g[d]! != 0 then throw "QuickSilver: the witness does not satisfy the constraints"
    if !(List.range (d + 1)).all fun k => Prover.evalPoly g (samplePts d)[k]! ==
        ((samplePts d).map (Prover.qsAt pf0 c2 values vRows vMask uMask w))[k]! then
      throw "QuickSilver: interpolation failed"
    return (g[0]!, (Array.range (d - 1)).map fun i => g[i + 1]!) :
      Except String (GF128 × Array GF128)) = _
  rw [hg]
  have hsz : ((Array.range (d + 1)).map P0.coeff).size = d + 1 := by simp
  have hget : ∀ i ≤ d, ((Array.range (d + 1)).map P0.coeff)[i]! = P0.coeff i := fun i hi =>
    getElem!_range_map _ _ (by omega)
  have hall : ((List.range (d + 1)).all fun k =>
      Prover.evalPoly ((Array.range (d + 1)).map P0.coeff) (samplePts d)[k]! ==
        ((samplePts d).map P0.eval)[k]!) = true := by
    rw [List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    rw [evalPoly_eq, polyOf_coeffs P0 hdegP.1, beq_iff_eq]
    simp [samplePts, getElem!_pos, hk']
  rw [← hys] at hall
  simp only [hsz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hget d le_rfl, htop, hall,
    Bool.not_true, hget 0 (Nat.zero_le _)]
  congr 2
  refine Array.map_congr_left fun i hi => hget _ (by have := Array.mem_range.1 hi; omega)

end VoleMole.ZK
