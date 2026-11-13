import VoleMole.ROM.SimExtract
import VoleMole.ROM.SpecSound

/-!
# Simultaneous extraction for the spec relations

`ROM/SimExtract.lean`'s simultaneous bounds (`prEvent_sim_le`, `prEvent_sim_comb_le`) for the
relations the protocol theorems use, with the spec relation of the chosen instance as the
extraction target (as `ROM/SpecSound.lean`'s `*_accept_le_adaptive_spec`). A run `G` (at most
`q_E` cipher queries, `q k` hash queries of kind `k`, `n_G` in all) outputs proofs `j ∈ J`, the
`j`-th read off it by `proj j`; for `m = |J|` outputs:

    Pr[some output is accepted and its extraction fails]
      ≤ (q₂₁+m)·2⁻¹⁵⁰ + (q₂₂+m)·ε₂ + (q₂₃+m)·9·2⁻¹²⁸ + chainHitEpsSim q m + stmtBindEpsSim q m
        + m·failEps q q_E,

against `m` times the single-proof bound `(q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε₂ + (q₂₃+1)·9·2⁻¹²⁸ + … +
failEps q q_E` (`*_accept_le_adaptive_spec`). `ε₂ = ε_QS(4008)` (Moussaka issuance),
`ε_QS(4409) + 2⁻¹²⁸ + (n_G + 339)·2⁻⁴⁴⁸` (redemption), `ε_QS(3776)` (Ratatouille issuance),
`ε_QS(3816) + 2⁻¹²⁸ + (n_G + 339)·2⁻⁴⁴⁸` (spend).

* `moussakaIssue_sim_spec`, `moussakaRedeem_sim_spec`, `ratatouilleIssue_sim_spec`,
  `ratatouilleSpend_sim_spec`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

variable {ι' γ α ι β : Type}

/-- **Moussaka issuance, simultaneous extraction, spec relation.** For a family of instances
`(t, ctx_iss) = inst s` (`|t| = 45`, `|ctx_iss| = 16`, injective encodings), a run `G` and the
outputs `proj j <$> G` (`j ∈ J`), an event that implies at every table that some output's proof is
accepted at its instance and the decoded witness of no known tree is an issuance witness has
probability at most the simultaneous bound (module doc). -/
theorem moussakaIssue_sim_spec (inst : ι → ByteArray × ByteArray)
    (ht : ∀ s, (inst s).1.size = 45) (hci : ∀ s, (inst s).2.size = 16) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (moussakaIssue (inst s).1 (inst s).2 labelRows).instEnc ByteArray.empty)
    (G : OracleComp specIC γ) (proj : ι' → γ → ByteArray × (ι × β)) (qE : ℕ)
    (hqE : IsQueryBoundP G (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC G q) (nG : ℕ) (hnG : IsQueryBoundP G (fun t => t.isLeft = true) nG)
    (J : Finset ι') (j₀ : ι') (oa : CTable → OracleComp spec α) (event : CTable → α → Prop)
    (htr : ∀ E g, event E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
        (fun s => moussakaIssue (inst s).1 (inst s).2 labelRows) (proj j <$> G) E)
      r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
        (moussakaIssue (inst (stOut r)).1 (inst (stOut r)).2 labelRows)
        (fun _ w => Privacy.Moussaka.IssueRelW
          ⟨toL (inst (stOut r)).1, toL (inst (stOut r)).2⟩
          (SpecRel.issueWitOf (toL (inst (stOut r)).2) w)) r) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      (q .h21 + J.card) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + J.card) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        (q .h23 + J.card) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsSim q J.card +
        stmtBindEpsSim q J.card + J.card * failEps q qE := by
  classical
  set stF : ι → Statement := fun s => moussakaIssue (inst s).1 (inst s).2 labelRows
  set st₀ := moussakaIssue ByteArray.empty ByteArray.empty labelRows
  have hmu := muIn_injective (stF := stF) (dst := st₀.dst) (fun _ => rfl) hinj
  have h := prEvent_sim_le CrtGen.tables stF (decOf fun s => muIn (stF s))
    (fun s => moussakaIssueSys (inst s).1 (inst s).2) liftInvOk_tables st₀ (fun _ => rfl)
    (fun _ => rfl) none (fun _ => rfl) (fun s => decOf_apply hmu s)
    (fun s => Moussaka.issueSystem_length _ _) 9
    (fun s _ => moussakaIssueWit (fun k => fnOf (inst s).1 k.val) (fnOf (inst s).2))
    (fun s c1 lb w => moussakaIssue_values (inst s).1 (inst s).2 labelRows c1 lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        moussakaIssue_extract_chain (inst s).1 (inst s).2 labelRows ch hv hA hAS hkos hP.1 hQS
          admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    G proj qE hqE q hq nG hnG J j₀ oa event fun E g hev => by
      obtain ⟨j, hj, hacc, hnex⟩ := htr E g hev
      exact ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
        SpecRel.issueRelW_of_wit _ _ (ht _) (hci _) w hw) he)⟩
  refine h.trans ?_
  rw [sim_sum_eq]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, moussakaIssue]) (by norm_num [st₀, moussakaIssue])
  gcongr
  norm_num

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Moussaka redemption, simultaneous extraction, spec relation** (as
`moussakaIssue_sim_spec`; `|nf| = 24`, contexts of 16 bytes, at most 64 anchors). -/
theorem moussakaRedeem_sim_spec (anc : ι → List UovPk)
    (hn64 : ∀ s, (anc s).length ≤ 64) (nf ctxIss ctxRed cd : ι → ByteArray)
    (hnf : ∀ s, (nf s).size = 24) (hci : ∀ s, (ctxIss s).size = 16)
    (hcr : ∀ s, (ctxRed s).size = 16) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows).instEnc
        ByteArray.empty)
    (G : OracleComp specIC γ) (proj : ι' → γ → ByteArray × (ι × β)) (qE : ℕ)
    (hqE : IsQueryBoundP G (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC G q) (nG : ℕ) (hnG : IsQueryBoundP G (fun t => t.isLeft = true) nG)
    (J : Finset ι') (j₀ : ι') (oa : CTable → OracleComp spec α) (event : CTable → α → Prop)
    (htr : ∀ E g, event E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
        (fun s => moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows)
        (proj j <$> G) E)
      r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
        (moussakaRedeem (anc (stOut r)) (nf (stOut r)) (ctxIss (stOut r)) (ctxRed (stOut r))
          (cd (stOut r)) labelRows)
        (fun _ w => Privacy.Moussaka.RedeemRelW
          ⟨(anc (stOut r)).map UovPk.toSpec, toL (nf (stOut r)), toL (ctxIss (stOut r)),
            toL (ctxRed (stOut r)), toL (cd (stOut r))⟩
          (SpecRel.redeemWitOf (toL (nf (stOut r))) (toL (ctxIss (stOut r)))
            (toL (ctxRed (stOut r))) w)) r) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      (q .h21 + J.card) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + J.card) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + J.card) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsCombSim q Moussaka.M J.card +
        stmtBindEpsSim q J.card + J.card * failEps q qE := by
  classical
  set stF : ι → Statement := fun s =>
    moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows
  set st₀ := moussakaRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty ByteArray.empty
    labelRows
  have hmu := muIn_injective (stF := stF) (dst := st₀.dst) (fun _ => rfl) hinj
  have h := prEvent_sim_comb_le CrtGen.tables stF (decOf fun s => muIn (stF s))
    (fun s => moussakaRedeemSysL (anc s) (nf s) (ctxIss s) (ctxRed s))
    (fun s => moussakaRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    (toBA (VoleMole.Spec.makeDst "mous" 0 'l' '0')) liftInvOk_tables st₀ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun s => decOf_apply hmu s)
    (fun s _ => Moussaka.redeemSystem_length _ _ _ _ _ _ _)
    (fun s w => prU_comb_bad_le _ _ w fun hW =>
      moussaka_redeem_comb_bad_gf128 _ (by simpa using hn64 s) _ _ _ w hW) 9
    (fun s _ => moussakaRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    (fun s c1 v w => by
      rw [moussakaRedeem_values]; simp only [moussakaRedeemSys, ofArr_combinationOf_ba])
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc l hv A hA hAS hkos hQS hcb hP =>
        moussakaRedeem_extract_chain (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows ch l hv
          hA hAS hkos hP.1 hQS hcb admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    G proj qE hqE q hq nG hnG J j₀ oa event fun E g hev => by
      obtain ⟨j, hj, hacc, hnex⟩ := htr E g hev
      exact ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
        SpecRel.redeemRelW_of_wit _ (hn64 _) _ _ _ _ (hnf _) (hci _) (hcr _) w hw) he)⟩
  refine h.trans ?_
  rw [sim_comb_sum_eq]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, moussakaRedeem]) (by norm_num [st₀, moussakaRedeem])
  gcongr
  all_goals norm_num

end VoleMole.ROM.IC
