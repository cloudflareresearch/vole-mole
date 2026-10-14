import VoleMole.Arith.GFField
import VoleMole.Verifier.Bridge.KOS
import VoleMole.Verifier.Bridge.Accept

/-!
# Bridge: the field embedding exists

The bridge theorems take a `GFEmbedding F` into a field with `2¹²⁸` elements (`Bridge/Field.lean`).
`Arith/GFField.lean` proves, in the kernel, that `X¹²⁸ + X⁷ + X² + X + 1` is irreducible over GF(2)
and that `a ↦ a(root)` is a bijection from `GF128` onto `K = GF(2)[X]/(X¹²⁸ + X⁷ + X² + X + 1)`
preserving `1`, `+`, `*`. This file packages it as `gfK : GFEmbedding GF128.K` and restates the
theorems that assumed `|F| = 2¹²⁸` (and characteristic 2) at `F := K`, where these hypotheses are
proved (`GF128.card_K`, the `CharP K 2` instance):
* `map_gfInv_K`: `gfInv` is the inverse;
* `map_voleHashReceiver_K`: the executable VOLE check is `Seed.kosValue`, with the 64-bit key `t`
  ranging over all of `K` (`T = univ`);
* `map_constraintKeys_K`: the executable constraint values are the `c_k = Δ^d·f_k(m/Δ)`;
* `accept_hacc_K`: acceptance gives `EndToEnd`'s accepting equation at that transcript.
The theorems of `Bridge/*` without these hypotheses apply to `gfK` directly. `hvals` is proved per
relation in `Bridge/Relations.lean` (over `GF128` itself, or at `gfK` via `values_map`). What
remains assumed is listed in `Bridge/Accept.lean` and `Bridge/ChainRelations.lean` (the
random-oracle and probabilistic steps).
-/

namespace VoleMole.Verifier.Bridge

open VoleMole.Arith VoleMole.Verifier VoleMole.EndToEnd

/-- **The embedding of the executable `GF128` into the field `GF(2)[X]/(X¹²⁸ + X⁷ + X² + X + 1)`**
(onto, by `GF128.ringEquivK`). -/
noncomputable def gfK : GFEmbedding GF128.K where
  toFun := GF128.ringEquivK
  map_one := map_one _
  map_add := map_add _
  map_mul := map_mul _
  injective := GF128.ringEquivK.injective

theorem map_gfInv_K (a : GF128) : gfK (gfInv a) = (gfK a)⁻¹ := gfK.map_gfInv GF128.card_K a

open Classical in
/-- `map_voleHashReceiver` at `gfK`, with `T = univ`. -/
theorem map_voleHashReceiver_K (p : Params) (chal1 : ByteArray) (rows qMask : Array W128)
    (deltaL : GF128) (uTilde : ByteArray) (i : Fin 4) :
    gfK (voleHashReceiver p chal1 rows qMask deltaL uTilde)[(i : ℕ)]! =
      Seed.kosValue (chOf gfK (T := Finset.univ) (fun _ => Finset.mem_univ _) chal1)
        (fun _ : Unit => gfK deltaL)
        (fun _ (k : Fin (hashedRows p rows qMask).size) => gfK (hashedRows p rows qMask)[k])
        (fun _ j => gfK qMask[p.qsDegree - 1 + j]!.toGF) (fun j => gfK (gfOfBytes uTilde (16 * j)))
        () i :=
  map_voleHashReceiver gfK _ p chal1 rows qMask deltaL uTilde i

/-- `map_constraintKeys` at `gfK`. -/
theorem map_constraintKeys_K (p : Params) (keys : Array GF128) (deltaL : GF128)
    (values : (ℕ → GF128) → List GF128) (cs : System GF128.K)
    (hvals : ∀ x, (values x).map gfK = cs.values (gfK ∘ x)) :
    (constraintKeys p keys deltaL values).map gfK =
      List.ofFn (keyVals cs p.qsDegree (fun j => gfK (keys.getD j 0)) (gfK deltaL)) :=
  map_constraintKeys gfK GF128.card_K p keys deltaL values cs hvals

/-- **`accept_hacc` at `gfK`: acceptance gives `EndToEnd`'s accepting equation, over the field
GF(2¹²⁸), with no hypothesis on the field.** -/
theorem accept_hacc_K (T : CrtTables) (st : Statement) (proof : ByteArray)
    (h : (verify T st proof).accept = true)
    (cs : ByteArray → ByteArray → System GF128.K)
    (hvals : ∀ c1 c2 x, (st.values c1 c2 x).map gfK = (cs c1 c2).values (gfK ∘ x))
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
      gfK deltaL ≠ 0 ∧ chal3 pf c2 check = pf.delta ∧
      EndToEnd.qsCheck (cs c1 c2) st.params.qsDegree
          (Seed.zkCoeff (cs c1 c2).length (gfK (gfOfBytes c2 0)) (gfK (gfOfBytes c2 16))
            (gfK (gfOfBytes c2 32)) (gfK ⟨W128.word c2 48, 0⟩))
          (extW fun j : Fin st.params.witnessBits =>
            gfK crt.rows[(j : ℕ)]!.toGF + SeedExtraction.bit (corrBit pf j) * gfK deltaL)
          (gfK deltaL) +
        (Seed.maskPoly st.params.qsDegree (fun i => gfK crt.qMask[i]!.toGF) 0
          (fun i => gfK (gfOfBytes pf.qsProof (16 * (i - 1)))) (gfK check)).eval (gfK deltaL) = 0 :=
  accept_hacc gfK GF128.card_K T st proof h cs hvals hdeg

end VoleMole.Verifier.Bridge
