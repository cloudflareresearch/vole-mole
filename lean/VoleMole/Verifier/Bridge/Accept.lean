import VoleMole.Verifier.Verify
import VoleMole.Verifier.Bridge.QuickSilver

/-!
# Bridge: what an accepting run of the executable verifier gives the models

* `accept_iff`: `verify` accepts iff `check_format` passes, the BAVC opening reconstructs, the
  lifted `Δ` is nonzero and `chal3 = Δ`, with every intermediate value written out as the
  executable step functions (`ivOf`, `BAVC.reconstruct`, `chal1`, `convertToVole`,
  `crtReconstruct`, `voleHashReceiver`, `chal2`, `correctedKeys`, `constraintKeys`, `qsCheck`,
  `chal3`). This is the shape of the verifier in one statement, for the bridges below to refer to.
* `map_correctedKeys`: the witness MACs the executable QuickSilver step evaluates on are
  `EndToEnd.macs`' `q_j = Q_j + d_j·Δ` (zero beyond the `ℓ` witness rows: `EndToEnd.extW`),
  with `Q_j = φ(row_j)` the CRT-lifted corrected rows, `d` the proof's correction and `Δ` the lifted
  `Δ`, for any label-row layout (the label rows get no `d` and are not witness rows).
* `accept_hacc`: **acceptance gives the accepting equation of `EndToEnd`.** If `verify` accepts,
  then for any field embedding `φ` into a field of `2¹²⁸` elements and characteristic 2, and any
  constraint system `cs c1 c2` over `F` that the statement's evaluator transports (`hvals`) and
  whose constraints have degree `≤ d`: `φ Δ_lifted ≠ 0`, and
  `EndToEnd.qsCheck (cs c1 c2) d (zkCoeff …chal2…) m (φ Δ) + (maskPoly d a 0 ã z).eval (φ Δ) = 0`
  with `m = macs` as above, `a_i = φ q_mask[i]`, `ã` the proof's QuickSilver proof, and `z` the
  verifier's check value, which `chal3 = H(chal2 ‖ z ‖ ã ‖ ctr ‖ 11) = Δ` binds.

**What is not bridged** (still assumed by the end-to-end theorems, or argued only on paper):
* (`hvals` and the field embedding are no longer assumed: `Bridge/Concrete.lean` constructs the
  embedding and restates `accept_hacc` as `accept_hacc_K`; `Bridge/Relations.lean` takes `GF128`
  itself as the field and proves `hvals` for the five relations, `*_accept`.)
* (`accept_hacc` is pointwise in `Δ`, with `b = 0`. The per-tree affine form of the witness rows
  across `Δ`, the injective CRT lift, and the accepting equation on a whole chain with masks
  `a_i + b_i·Δ` from L3 are `Bridge/Lift.lean`, `Bridge/Columns.lean`, `Bridge/Chain.lean`.)
* that `chal1`, `chal2`, `chal3` are random-oracle outputs (the random-oracle steps of L1-L4).
-/

open Polynomial

namespace VoleMole.Verifier.Bridge

open VoleMole.Arith VoleMole.Verifier VoleMole.EndToEnd VoleMole.EndToEnd.QSExprMac

lemma byteArray_beq_iff (a b : ByteArray) : (a == b) = true ↔ a = b := by
  change (a.data == b.data) = true ↔ a = b
  rw [beq_iff_eq, ByteArray.ext_iff]

/-- **The executable verifier, unfolded.** -/
theorem accept_iff (T : CrtTables) (st : Statement) (proof : ByteArray) :
    (verify T st proof).accept = true ↔
      let pf : Proof := { params := st.params, bytes := proof }
      let muI : ByteArray → ByteArray := fun c1 => mu (some (st.instEnc c1)) st.dst
      let mu1 := if st.delayed then mu none st.dst else muI ByteArray.empty
      let iv := ivOf pf mu1
      pf.checkFormat = true ∧ ∃ leaves, BAVC.reconstruct iv pf.opening pf.delta = some leaves ∧
        let c1 := chal1 pf mu1 (BAVC.check leaves.coms) st.binder1
        let crt := crtReconstruct pf T iv (convertToVole pf iv leaves)
        let deltaL := crt.deltaLifted.toGF
        let hV := voleHashReceiver st.params c1 crt.rows crt.qMask deltaL pf.voleCheck
        let c2 := chal2 pf c1 hV (if st.delayed then muI c1 else ByteArray.empty) st.binder2
        let cs := constraintKeys st.params (correctedKeys pf crt.rows deltaL) deltaL
          (st.values c1 c2)
        deltaL ≠ 0 ∧ chal3 pf c2 (qsCheck pf c2 cs crt.qMask deltaL) = pf.delta := by
  simp only [verify, Id.run]
  split
  · simp_all
  · split <;> (try split_ifs) <;> simp_all [pure, byteArray_beq_iff]

variable {F : Type*} [Field F] (φ : GFEmbedding F)

/-- Bit `j` of the proof's correction `d`. -/
def corrBit (pf : Proof) (j : ℕ) : Bool :=
  (pf.correction.get! (j / 8) >>> (j % 8).toUInt8) &&& 1 == 1

/-- **The executable witness MACs are `EndToEnd.macs`.** -/
theorem map_correctedKeys (pf : Proof) (rows : Array W128) (deltaL : GF128) :
    (fun j => φ ((correctedKeys pf rows deltaL).getD j 0)) =
      extW fun j : Fin pf.params.witnessBits =>
        φ rows[(j : ℕ)]!.toGF + SeedExtraction.bit (corrBit pf j) * φ deltaL := by
  funext j
  by_cases hj : j < pf.params.witnessBits
  · simp only [correctedKeys, extW, hj, dite_true, Array.getD_eq_getD_getElem?,
      Array.getElem?_map, Array.getElem?_range, ite_true, Option.map_some, Option.getD_some]
    unfold corrBit SeedExtraction.bit
    split_ifs <;> simp_all
  · simp [correctedKeys, extW, hj, Array.getD_eq_getD_getElem?]

/-- **Acceptance gives `EndToEnd`'s accepting equation at this transcript.** -/
theorem accept_hacc [Fintype F] [CharP F 2] (hF : Fintype.card F = 2 ^ 128) (T : CrtTables)
    (st : Statement) (proof : ByteArray) (h : (verify T st proof).accept = true)
    (cs : ByteArray → ByteArray → System F)
    (hvals : ∀ c1 c2 x, (st.values c1 c2 x).map φ = (cs c1 c2).values (φ ∘ x))
    (hdeg : ∀ c1 c2, ∀ e ∈ cs c1 c2, e.degree ≤ st.params.qsDegree) :
    let pf : Proof := { params := st.params, bytes := proof }
    let muI : ByteArray → ByteArray := fun c1 => mu (some (st.instEnc c1)) st.dst
    let mu1 := if st.delayed then mu none st.dst else muI ByteArray.empty
    let iv := ivOf pf mu1
    ∃ leaves, BAVC.reconstruct iv pf.opening pf.delta = some leaves ∧
      let c1 := chal1 pf mu1 (BAVC.check leaves.coms) st.binder1
      let crt := crtReconstruct pf T iv (convertToVole pf iv leaves)
      let deltaL := crt.deltaLifted.toGF
      let hV := voleHashReceiver st.params c1 crt.rows crt.qMask deltaL pf.voleCheck
      let c2 := chal2 pf c1 hV (if st.delayed then muI c1 else ByteArray.empty) st.binder2
      let check := qsCheck pf c2 (constraintKeys st.params (correctedKeys pf crt.rows deltaL) deltaL
        (st.values c1 c2)) crt.qMask deltaL
      φ deltaL ≠ 0 ∧ chal3 pf c2 check = pf.delta ∧
      EndToEnd.qsCheck (cs c1 c2) st.params.qsDegree
          (Seed.zkCoeff (cs c1 c2).length (φ (gfOfBytes c2 0)) (φ (gfOfBytes c2 16))
            (φ (gfOfBytes c2 32)) (φ ⟨W128.word c2 48, 0⟩))
          (extW fun j : Fin st.params.witnessBits =>
            φ crt.rows[(j : ℕ)]!.toGF + SeedExtraction.bit (corrBit pf j) * φ deltaL)
          (φ deltaL) +
        (Seed.maskPoly st.params.qsDegree (fun i => φ crt.qMask[i]!.toGF) 0
          (fun i => φ (gfOfBytes pf.qsProof (16 * (i - 1)))) (φ check)).eval (φ deltaL) = 0 := by
  intro pf muI mu1 iv
  obtain ⟨-, leaves, hr, h0, h3⟩ := (accept_iff T st proof).1 h
  refine ⟨leaves, hr, ?_⟩
  intro c1 crt deltaL hV c2 check
  have hΔ : φ deltaL ≠ 0 := fun h => h0 ((φ.map_eq_zero_iff _).1 h)
  refine ⟨hΔ, h3, ?_⟩
  have hm := map_correctedKeys φ pf crt.rows deltaL
  rw [← hm]
  refine hacc_of_qsCheck φ pf c2 _ crt.qMask deltaL (cs c1 c2) _ ?_ _ 0
    (fun i _ => by simp)
  rw [map_constraintKeys φ hF _ _ _ _ _ (hvals c1 c2)]
  congr 1
  funext k
  rw [keyVals, sysQS, mac_constraintQS _ hΔ _ (hdeg c1 c2 _ (List.get_mem _ k))]

end VoleMole.Verifier.Bridge
