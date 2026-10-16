import VoleMole.Verifier.Bridge.BAVCComplete
import VoleMole.Verifier.Bridge.CrtComplete

/-!
# Bridge: completeness of the executable verifier, with the correctness facts proved

`Bridge/Prover.lean` proves that `verify` accepts the executable prover's output for any CRT
tables, assuming BAVC opening correctness (`BAVCComplete`) and the CRT masks' VOLE correlation for
the prover's commitment (`CrtComplete`). Both are now theorems: `bavcComplete`
(`Bridge/BAVCComplete.lean`, every `Δ`) and `crtComplete` (`Bridge/CrtComplete.lean`, for
faest-arch-opt's tables `CrtGen.tables` and every statement whose label rows are corrected rows,
`hlab_of`: witnesses of at least 16 bytes). Here the completeness theorems are restated at
`CrtGen.tables` without them:

* `verify_proveCommit_tables`, `verify_prove_tables`: any statement whose evaluator is a system of
  degree `≤ d`; assumed only `HashesWF Hs` and `Δ' ≠ 0` for the ground `Δ` (`Δ' = 0` has
  probability `≤ 2⁻¹¹⁴` over the grinding answers, `ZK.Sim.pr_hitZero_le_114`, `≈ 2⁻¹¹⁸·⁷` in
  truth; discharged in the random-oracle model by `ZK/CompleteRO.lean`, `complete_rom`).
* `moussakaIssue_complete_tables`, `moussakaRedeem_complete_tables`,
  `ratatouilleIssue_complete_tables`, `ratatouilleSpend_complete_tables`,
  `pomfritRedeem_complete_tables`: the five relations, either layout (`ProveOkT`: the prover
  returned the proof and `Δ' ≠ 0`).
* `*_complete_shake`: the same with SHAKE (`hashesWF_shake`).
-/

namespace VoleMole.Verifier.Bridge

-- The statements hold for any CTR PRG (`HasPrg`, `Verifier/Prg.lean`), AES included.
variable [VoleMole.Verifier.HasPrg]
set_option linter.unusedSectionVars false

open VoleMole.Arith VoleMole.Verifier

/-- The label rows are corrected rows when the witness has at least 16 bytes (both layouts). -/
theorem hlab_of {p : Params} (h : 16 ≤ p.witnessBytes) :
    p.labelRowOffset + 128 ≤ p.correctionRows := by
  simp only [Params.labelRowOffset, Params.correctionRows, Params.witnessBits]
  split <;> omega

/-- **Completeness of the verifier on `Prover.proveCommit`'s output**, for faest-arch-opt's
tables. Assumed: `HashesWF Hs`, label rows that are corrected rows, `Δ' ≠ 0`. -/
theorem verify_proveCommit_tables (Hs : Hashes) (hHs : HashesWF Hs) (st : Statement)
    (mu1 wPrefix rho binder1 wSuffix proof : ByteArray)
    (hmu : st.mu1 Hs = mu1) (hb1 : st.binder1 = binder1)
    (h : Prover.proveCommit Hs st wSuffix
      (Prover.voleGen Hs CrtGen.tables st.params mu1 wPrefix rho binder1) = .ok proof)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (hΔ : (W128.rowMul (BAVC.deltaBit ({ params := st.params, bytes := proof } : Proof).delta) 120
      CrtGen.tables.wCrt).toGF ≠ 0)
    (cs : ByteArray → ByteArray → System GF128)
    (hvals : ∀ c1 lb x, st.values c1 lb x = (cs c1 lb).values x)
    (hdeg : ∀ c1 lb, ∀ e ∈ cs c1 lb, e.degree ≤ st.params.qsDegree)
    (hd : 1 ≤ st.params.qsDegree) (hd' : st.params.qsDegree + 1 < 2 ^ 64) :
    (verify Hs CrtGen.tables st proof).accept = true :=
  verify_proveCommit Hs hHs bavcComplete CrtGen.tables st mu1 wPrefix rho binder1 wSuffix proof
    hmu hb1 h (crtComplete Hs st.params mu1 wPrefix rho binder1 hlab) hΔ cs hvals hdeg hd hd'

/-- **Completeness for `Prover.prove`**, for faest-arch-opt's tables. -/
theorem verify_prove_tables (Hs : Hashes) (hHs : HashesWF Hs) (st : Statement)
    (w rho : ByteArray) (prefixBytes : ℕ) (proof : ByteArray)
    (h : Prover.prove Hs CrtGen.tables st w rho prefixBytes = .ok proof)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (hΔ : (W128.rowMul (BAVC.deltaBit ({ params := st.params, bytes := proof } : Proof).delta) 120
      CrtGen.tables.wCrt).toGF ≠ 0)
    (cs : ByteArray → ByteArray → System GF128)
    (hvals : ∀ c1 lb x, st.values c1 lb x = (cs c1 lb).values x)
    (hdeg : ∀ c1 lb, ∀ e ∈ cs c1 lb, e.degree ≤ st.params.qsDegree)
    (hd : 1 ≤ st.params.qsDegree) (hd' : st.params.qsDegree + 1 < 2 ^ 64) :
    (verify Hs CrtGen.tables st proof).accept = true :=
  verify_prove Hs hHs bavcComplete CrtGen.tables st w rho prefixBytes proof h
    (crtComplete Hs st.params _ _ rho _ hlab) hΔ cs hvals hdeg hd hd'

/-! ### Per relation -/

/-- The prover returned `proof` and `Δ' ≠ 0` (`ProveOk` without `CrtComplete`). -/
def ProveOkT (Hs : Hashes) (st : Statement) (w rho proof : ByteArray) : Prop :=
  Prover.prove Hs CrtGen.tables st w rho = .ok proof ∧
    (W128.rowMul (BAVC.deltaBit ({ params := st.params, bytes := proof } : Proof).delta) 120
      CrtGen.tables.wCrt).toGF ≠ 0

lemma ProveOkT.proveOk {Hs : Hashes} {st : Statement} {w rho proof : ByteArray}
    (h : ProveOkT Hs st w rho proof) (hw : 16 ≤ st.params.witnessBytes) :
    ProveOk Hs CrtGen.tables st w rho proof :=
  ⟨h.1, crtComplete Hs st.params _ _ rho _ (hlab_of hw), h.2⟩

theorem moussakaIssue_complete_tables (Hs : Hashes) (hHs : HashesWF Hs) (t ctxIss : ByteArray)
    (labelRows : Bool) (w rho proof : ByteArray)
    (h : ProveOkT Hs (moussakaIssue t ctxIss labelRows) w rho proof) :
    (verify Hs CrtGen.tables (moussakaIssue t ctxIss labelRows) proof).accept = true :=
  moussakaIssue_complete Hs hHs bavcComplete CrtGen.tables t ctxIss labelRows w rho proof
    (h.proveOk (show 16 ≤ 256 by decide))

theorem moussakaRedeem_complete_tables (Hs : Hashes) (hHs : HashesWF Hs) (anchors : List UovPk)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool) (w rho proof : ByteArray)
    (h : ProveOkT Hs (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) w rho
      proof) :
    (verify Hs CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      proof).accept = true :=
  moussakaRedeem_complete Hs hHs bavcComplete CrtGen.tables anchors nf ctxIss ctxRed
    challengeDigest labelRows w rho proof (h.proveOk (show 16 ≤ 343 by decide))

theorem ratatouilleIssue_complete_tables (Hs : Hashes) (hHs : HashesWF Hs) (c : ByteArray)
    (tInit : ℕ) (ctxIss : ByteArray) (labelRows : Bool) (w rho proof : ByteArray)
    (h : ProveOkT Hs (ratatouilleIssue c tInit ctxIss labelRows) w rho proof) :
    (verify Hs CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) proof).accept = true :=
  ratatouilleIssue_complete Hs hHs bavcComplete CrtGen.tables c tInit ctxIss labelRows w rho proof
    (h.proveOk (show 16 ≤ 240 by decide))

theorem ratatouilleSpend_complete_tables (Hs : Hashes) (hHs : HashesWF Hs) (pk : UovPk)
    (nf : ByteArray) (d : ℕ) (cNext ctxIss : ByteArray) (labelRows : Bool)
    (w rho proof : ByteArray)
    (h : ProveOkT Hs (ratatouilleSpend pk nf d cNext ctxIss labelRows) w rho proof) :
    (verify Hs CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) proof).accept =
      true :=
  ratatouilleSpend_complete Hs hHs bavcComplete CrtGen.tables pk nf d cNext ctxIss labelRows w rho
    proof (h.proveOk (show 16 ≤ 847 by decide))

/-- **PomFRIT redemption: completeness** of the two-step prover, for faest-arch-opt's tables. -/
theorem pomfritRedeem_complete_tables (Hs : Hashes) (hHs : HashesWF Hs) (pk : UovPk)
    (msg r rho com refresher wSuffix proof : ByteArray) (labelRows : Bool) (hcom : com.size = 32)
    (h : Prover.proveCommit Hs (pomfritRedeem pk
      ((pomfritPending Hs CrtGen.tables labelRows r rho com).proof ++ com ++ refresher) msg
        labelRows) wSuffix (pomfritPending Hs CrtGen.tables labelRows r rho com) = .ok proof)
    (hΔ : (W128.rowMul (BAVC.deltaBit
      ({ params := pomfritParams labelRows, bytes := proof } : Proof).delta) 120
        CrtGen.tables.wCrt).toGF ≠ 0) :
    (verify Hs CrtGen.tables (pomfritRedeem pk
      ((pomfritPending Hs CrtGen.tables labelRows r rho com).proof ++ com ++ refresher) msg
        labelRows) proof).accept = true :=
  pomfritRedeem_complete Hs hHs bavcComplete CrtGen.tables pk msg r rho com refresher wSuffix proof
    labelRows hcom h (crtComplete Hs _ _ r rho com (hlab_of (show 16 ≤ 164 by decide))) hΔ

/-! ### With SHAKE -/

theorem moussakaIssue_complete_shake (t ctxIss : ByteArray) (labelRows : Bool)
    (w rho proof : ByteArray) (h : ProveOkT Hashes.shake (moussakaIssue t ctxIss labelRows) w rho proof) :
    (verify Hashes.shake CrtGen.tables (moussakaIssue t ctxIss labelRows) proof).accept = true :=
  moussakaIssue_complete_tables _ hashesWF_shake t ctxIss labelRows w rho proof h

theorem moussakaRedeem_complete_shake (anchors : List UovPk)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool) (w rho proof : ByteArray)
    (h : ProveOkT Hashes.shake (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      w rho proof) :
    (verify Hashes.shake CrtGen.tables
      (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) proof).accept = true :=
  moussakaRedeem_complete_tables _ hashesWF_shake anchors nf ctxIss ctxRed challengeDigest
    labelRows w rho proof h

theorem ratatouilleIssue_complete_shake (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray)
    (labelRows : Bool) (w rho proof : ByteArray)
    (h : ProveOkT Hashes.shake (ratatouilleIssue c tInit ctxIss labelRows) w rho proof) :
    (verify Hashes.shake CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) proof).accept =
      true :=
  ratatouilleIssue_complete_tables _ hashesWF_shake c tInit ctxIss labelRows w rho proof h

theorem ratatouilleSpend_complete_shake (pk : UovPk) (nf : ByteArray) (d : ℕ)
    (cNext ctxIss : ByteArray) (labelRows : Bool) (w rho proof : ByteArray)
    (h : ProveOkT Hashes.shake (ratatouilleSpend pk nf d cNext ctxIss labelRows) w rho proof) :
    (verify Hashes.shake CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows)
      proof).accept = true :=
  ratatouilleSpend_complete_tables _ hashesWF_shake pk nf d cNext ctxIss labelRows w rho proof h

theorem pomfritRedeem_complete_shake (pk : UovPk) (msg r rho com refresher wSuffix proof : ByteArray)
    (labelRows : Bool) (hcom : com.size = 32)
    (h : Prover.proveCommit Hashes.shake (pomfritRedeem pk
      ((pomfritPending Hashes.shake CrtGen.tables labelRows r rho com).proof ++ com ++ refresher)
        msg labelRows) wSuffix (pomfritPending Hashes.shake CrtGen.tables labelRows r rho com) =
        .ok proof)
    (hΔ : (W128.rowMul (BAVC.deltaBit
      ({ params := pomfritParams labelRows, bytes := proof } : Proof).delta) 120
        CrtGen.tables.wCrt).toGF ≠ 0) :
    (verify Hashes.shake CrtGen.tables (pomfritRedeem pk
      ((pomfritPending Hashes.shake CrtGen.tables labelRows r rho com).proof ++ com ++ refresher)
        msg labelRows) proof).accept = true :=
  pomfritRedeem_complete_tables _ hashesWF_shake pk msg r rho com refresher wSuffix proof labelRows
    hcom h hΔ

end VoleMole.Verifier.Bridge
