import VoleMole.ROM.VerifyIC
import VoleMole.ZK.VerifyPre

/-!
# The verifier's grinding prefix as an oracle computation over the hashes and the cipher

The Lean simulator programs `H₂³` at the grinding points of the prefix `chal2 ‖ qs_check ‖ ã` that
the verifier recomputes from the simulated proof (`ZK.Sim.vPre`, `ZK.Sim.progRO`). A reduction
that answers the programmed points itself (the programming step of L8, `Theft/PlainLog.lean`)
must compute that prefix by queries, as `ROM/VerifyIC.lean`'s `verifyIC` computes the verifier.

* `vPreQ T st proof`: `vPre` with every hash a query (`mu₁`, `iv`, the leaf hashes and `com`,
  `chal1`, the 312 gate hashes, PomFRIT's `mu`, `chal2`, the combination); no `H₂³` query.
  `evalWithAnswerFn_vPreQ`: against a complete table it is `vPre` with the table's hashes.
* **`vPreIC T st proof`**: `mu₁` and `iv`, the tree derivation with cipher queries, the needed
  cells (`needCells`), then `vPreQ` with the PRG of the queried cells.
  **`evalWithAnswerFn_vPreIC`**: per table it is `vPre` with the hashes of `g` and the
  ideal-cipher PRG of `E` (`vPre_congr_cells`: `vPre` reads the cipher only at those cells).
* Query bounds: `extractorQueries + vPreQueries` per hash kind (no `H₂³` query,
  `isKindQueryBoundIC_vPreIC`) and `verifyCellBound p` cipher queries
  (`isQueryBoundP_right_vPreIC`).
-/

open Finset OracleComp OracleSpec

namespace VoleMole.ROM

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim

section Q

variable [VoleMole.Verifier.HasPrg]

/-- **The verifier's grinding prefix with every hash a query** (`ZK.Sim.vPre`, query by query). -/
def vPreQ (T : CrtTables) (st : Statement) (proof : ByteArray) : OracleComp spec ByteArray := do
  let pf : Proof := { params := st.params, bytes := proof }
  let mu1 ← mu1Q st
  let iv ← hashQ .h4 ((pf.ivPre ++ mu1).push 4)
  match BAVC.reconstruct iv pf.opening pf.delta with
  | none => return ByteArray.empty
  | some leaves =>
    let lh ← (BAVC.leafHashInputs leaves.coms).mapM (hashQ .h1)
    let com ← hashQ .h1 (BAVC.comInput lh)
    let c1 ← hashQ .h21 (chal1Input pf mu1 com st.binder1)
    let cols := convertToVole pf iv leaves
    let gh ← (gateInputs st.params T iv cols).mapM (hashQ .h5)
    let crt := crtReconstructWith (gateWords gh) st.params (BAVC.deltaBit pf.delta) pf.cmult T cols
    let deltaL := crt.deltaLifted.toGF
    let hV := voleHashReceiver st.params c1 crt.rows crt.qMask deltaL pf.voleCheck
    let muD ← muDelayedQ st c1
    let c2 ← hashQ .h22 (chal2Input pf c1 hV muD st.binder2)
    let lb ← combBytesQ st c2
    let check := qsCheck pf c2 (constraintKeys st.params (correctedKeys pf crt.rows deltaL) deltaL
      (st.values c1 lb)) crt.qMask deltaL
    return c2 ++ gfToBytes check ++ pf.qsProof

/-- **Against a complete answer table, `vPreQ` is the verifier's prefix** with the table's
hashes. -/
theorem evalWithAnswerFn_vPreQ (g : Table) (T : CrtTables) (st : Statement) (proof : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn g) (vPreQ T st proof) = vPre (Hashes.ofTable g) T st proof := by
  unfold vPreQ vPre vPreP
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_mu1Q, evalWithAnswerFn_hashQ, ivOf]
  generalize BAVC.reconstruct _ _ _ = R
  cases R with
  | none => rfl
  | some leaves =>
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_mapM_hashQ, evalWithAnswerFn_hashQ,
      evalWithAnswerFn_muDelayedQ, evalWithAnswerFn_pure, evalWithAnswerFn_combBytesQ, vPreOf,
      chal1, chal2, crtReconstruct, crtReconstructAt, gateHashes, BAVC.check, ivOf]

/-- The prefix's queries per domain: the verifier's (`verifierQueries`) without `chal3`. -/
def vPreQueries : Kind → ℕ
  | .h1 => 18
  | .mu => 2
  | .muDelayed => 1
  | .h3 => 0
  | .h4 => 1
  | .h5 => 312
  | .h21 => 1
  | .h22 => 1
  | .h23 => 0
  | .comb _ => 1

/-- **The prefix's queries per domain** (`vPreQueries`; none to `H₂³`). -/
theorem isKindQueryBound_vPreQ (T : CrtTables) (st : Statement) (proof : ByteArray) :
    IsKindQueryBound (vPreQ T st proof) vPreQueries := by
  unfold vPreQ
  dsimp only
  have hmu : ∀ {f : ByteArray → OracleComp spec ByteArray} {q : Kind → ℕ}, 0 < q .mu →
      0 < q .muDelayed → (∀ u, IsKindQueryBound (f u) (Function.update q .mu (q .mu - 1))) →
      (∀ u, IsKindQueryBound (f u) (Function.update q .muDelayed (q .muDelayed - 1))) →
      IsKindQueryBound (mu1Q st >>= f) q := by
    intro f q h1 h2 hf1 hf2
    unfold mu1Q
    split
    · exact isKindQueryBound_hashQ_bind_iff.2 ⟨h2, fun u => hf2 _⟩
    · exact isKindQueryBound_hashQ_bind_iff.2 ⟨h1, fun u => hf1 _⟩
  refine hmu (by decide) (by decide) (fun mu1 => ?_) (fun mu1 => ?_)
  all_goals
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [vPreQueries], fun iv => ?_⟩
    split
    · trivial
    refine isKindQueryBound_mapM_hashQ_bind _ _
      (by simp [vPreQueries, length_leafHashInputs]) fun lh => ?_
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨by
      simp [vPreQueries, length_leafHashInputs], fun com => ?_⟩
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [vPreQueries],
      fun c1 => ?_⟩
    refine isKindQueryBound_mapM_hashQ_bind _ _
      (by simp [vPreQueries, length_gateInputs]) fun gh => ?_
    refine isKindQueryBound_muDelayedQ_bind _ _ (by simp [vPreQueries])
      fun muD => ?_
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [vPreQueries],
      fun c2 => ?_⟩
    refine isKindQueryBound_combBytesQ_bind _ _
      (fun M => by simp [vPreQueries]) (fun M lb => ?_) (fun lb => ?_)
    all_goals trivial

end Q

namespace IC

/-! ## The prefix reads the cipher only at the needed cells -/

section Congr

variable {E E' : Cipher}

/-- **`vPre` with the ideal-cipher PRG reads the table only at `cellsE`**: two tables that agree
at the cells of the verifier's PRG calls give the same prefix. -/
theorem vPre_congr_cells (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (h : ∀ x ∈ cellsE E st.params (ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs))
      (⟨st.params, proof⟩ : Proof).opening (⟨st.params, proof⟩ : Proof).delta,
      E x.1 x.2 = E' x.1 x.2) :
    @vPre (icPrg E) Hs T st proof = @vPre (icPrg E') Hs T st proof := by
  set pf : Proof := ⟨st.params, proof⟩ with hpf
  have hr := reconstruct_congr_cells h
  simp only [vPre, vPreP]
  rw [← hpf, ← hr]
  split
  · rfl
  · rename_i leaves hl
    have hc : @convertToVole (icPrg E) pf (ivOf Hs pf (st.mu1 Hs)) leaves =
        @convertToVole (icPrg E') pf (ivOf Hs pf (st.mu1 Hs)) leaves := by
      unfold convertToVole
      refine convertToVoleAt_congr_cells fun i hi j hj hjd => ?_
      rw [@leafKey_reconstruct (icPrg E) _ _ _ leaves hl i j hi hj hjd]
      exact icPrgF_congr_cells fun x hx => h x (mem_cellsE_leaf hi hj (Or.inr hx))
    simp only [vPreOf]
    rw [hc]

end Congr

/-- **The verifier's grinding prefix as an oracle computation over the hashes and the cipher**:
`mu₁`, `iv`; the tree derivation with cipher queries; the needed cells, queried; then `vPreQ`
(hash queries) with the ideal-cipher PRG of the queried cells. -/
def vPreIC (T : CrtTables) (st : Statement) (proof : ByteArray) : OracleComp specIC ByteArray := do
  let pf : Proof := ⟨st.params, proof⟩
  let iv ← liftIC (ivQ st proof)
  let A ← treeQ iv pf.opening pf.delta
  let M ← cellsQ st.params iv A
  liftIC (@vPreQ (icPrg (fillC M)) T st proof)

/-- **Per table, `vPreIC` is the verifier's prefix** with the hashes of `g` and the ideal-cipher
PRG of `E`. -/
theorem evalWithAnswerFn_vPreIC (g : Table) (E : CTable) (T : CrtTables) (st : Statement)
    (proof : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (vPreIC T st proof) =
      @vPre (icPrg E.cipher) (Hashes.ofTable g) T st proof := by
  simp only [vPreIC, evalWithAnswerFn_bind, evalWithAnswerFn_liftIC, evalWithAnswerFn_ivQ,
    evalWithAnswerFn_treeQ, evalWithAnswerFn_vPreQ]
  rw [evalWithAnswerFn_cellsQ]
  refine (vPre_congr_cells (Hashes.ofTable g) T st proof fun x hx => ?_).symm
  show E x = (_ : Option Blk).getD 0
  erw [lookup_map_self E hx]
  rfl

/-- **The prefix's hash queries**: `mu₁` and `iv`, then `vPreQueries` (none to `H₂³`). -/
theorem isKindQueryBoundIC_vPreIC (T : CrtTables) (st : Statement) (proof : ByteArray) :
    IsKindQueryBoundIC (vPreIC T st proof) (extractorQueries + vPreQueries) := by
  unfold vPreIC
  refine isKindQueryBoundIC_bind (isKindQueryBoundIC_liftIC (isKindQueryBound_ivQ st proof))
    fun iv => ?_
  refine (isKindQueryBoundIC_bind (q₁ := 0) (q₂ := vPreQueries)
    (isKindQueryBoundIC_treeQ _ _ _) fun A => ?_).mono (by simp only [zero_add, le_refl])
  refine (isKindQueryBoundIC_bind (q₁ := 0) (q₂ := vPreQueries)
    (isKindQueryBoundIC_cellsQ _ _ _) fun M => ?_).mono (by simp only [zero_add, le_refl])
  exact isKindQueryBoundIC_liftIC (@isKindQueryBound_vPreQ (icPrg (fillC M)) T st proof)

/-- **The prefix's cipher queries**: the derivation's and the needed cells'. -/
theorem isQueryBoundP_right_vPreIC (T : CrtTables) (st : Statement) (proof : ByteArray) :
    IsQueryBoundP (vPreIC T st proof) (fun t => t.isRight = true) (verifyCellBound st.params) := by
  unfold vPreIC
  refine (isQueryBoundP_bind (n := 0) (m := verifyCellBound st.params)
    (isQueryBoundP_right_liftIC (ivQ st proof)) fun iv _ => ?_).mono (by simp only [zero_add, le_refl])
  refine isQueryBoundP_bind (n := 2 * (BAVC.numLeaves - 1)) (isQueryBoundP_right_treeQ _ _ _)
    fun A _ => ?_
  exact (isQueryBoundP_bind (m := 0) (isQueryBoundP_right_cellsQ _ _ _) fun M _ =>
      isQueryBoundP_right_liftIC _).mono (by simp only [add_zero, le_refl])

end IC

end VoleMole.ROM
