import VoleMole.ROM.SimExtract
import VoleMole.ROM.SpecSound

/-!
# Simultaneous extraction for the spec relations

`ROM/SimExtract.lean`'s simultaneous bounds (`prEvent_sim_le`, `prEvent_sim_comb_le`) for the
relations the protocol theorems use, with the spec relation of the chosen instance as the
extraction target (as `ROM/SpecSound.lean`'s `*_accept_le_adaptive_spec`). Provers `P j`
(`j ∈ J`, the proofs of one protocol run) whose runs are prefixes of a reference run `P₀`
(`PrefixRuns`), all within `q_E` cipher queries, `q k` hash queries of kind `k` and `n_G` in all;
for `m = |J|` outputs:

    Pr[some output is accepted and its extraction fails]
      ≤ (q₂₁+m)·2⁻¹⁵⁰ + (q₂₂+m)·ε₂ + (q₂₃+m)·9·2⁻¹²⁸ + chainHitEpsSim q m + stmtBindEpsSim q m
        + m·failEps q q_E,

against `m` times the single-proof bound `(q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε₂ + (q₂₃+1)·9·2⁻¹²⁸ + … +
failEps q q_E` (`*_accept_le_adaptive_spec`). `ε₂ = ε_QS(4008)` (Moussaka issuance),
`ε_QS(4409) + 2⁻¹²⁸ + (n_G + 339)·2⁻⁴⁴⁸` (redemption), `ε_QS(3776)` (Ratatouille issuance),
`ε_QS(12282) + 2⁻¹²⁸ + (n_G + 339)·2⁻⁴⁴⁸` (spend).

* `moussakaIssue_sim_spec`, `moussakaRedeem_sim_spec`, `ratatouilleIssue_sim_spec`,
  `ratatouilleSpend_sim_spec`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

variable {ι' α ι β : Type}

/-- **Moussaka issuance, simultaneous extraction, spec relation.** For a family of instances
`(t, ctx_iss) = inst s` (`|t| = 45`, `|ctx_iss| = 16`, injective encodings) and provers `P j`
(`j ∈ J`) whose runs are prefixes of `P₀`, an event that implies at every table that some output's proof is
accepted at its instance and the decoded witness of no known tree is an issuance witness has
probability at most the simultaneous bound (module doc). -/
theorem moussakaIssue_sim_spec (inst : ι → ByteArray × ByteArray)
    (ht : ∀ s, (inst s).1.size = 45) (hci : ∀ s, (inst s).2.size = 16) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (moussakaIssue (inst s).1 (inst s).2 labelRows).instEnc ByteArray.empty)
    (P₀ : OracleComp specIC (ByteArray × (ι × β))) (P : ι' → OracleComp specIC (ByteArray × (ι × β)))
    (qE : ℕ) (hqE : ∀ j, IsQueryBoundP (P j) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq₀ : IsKindQueryBoundIC P₀ q) (hq : ∀ j, IsKindQueryBoundIC (P j) q) (nG : ℕ)
    (hnG₀ : IsQueryBoundP P₀ (fun t => t.isLeft = true) nG)
    (hnG : ∀ j, IsQueryBoundP (P j) (fun t => t.isLeft = true) nG)
    (J : Finset ι') (hpre : ∀ E, PrefixRuns E P₀ P J) (oa : CTable → OracleComp spec α)
    (event : CTable → α → Prop)
    (htr : ∀ E g, event E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
        (fun s => moussakaIssue (inst s).1 (inst s).2 labelRows) (P j) E)
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
    P₀ P qE hqE q hq₀ hq nG hnG₀ hnG J hpre oa event fun E g hev => by
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
    (P₀ : OracleComp specIC (ByteArray × (ι × β))) (P : ι' → OracleComp specIC (ByteArray × (ι × β)))
    (qE : ℕ) (hqE : ∀ j, IsQueryBoundP (P j) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq₀ : IsKindQueryBoundIC P₀ q) (hq : ∀ j, IsKindQueryBoundIC (P j) q) (nG : ℕ)
    (hnG₀ : IsQueryBoundP P₀ (fun t => t.isLeft = true) nG)
    (hnG : ∀ j, IsQueryBoundP (P j) (fun t => t.isLeft = true) nG)
    (J : Finset ι') (hpre : ∀ E, PrefixRuns E P₀ P J) (oa : CTable → OracleComp spec α)
    (event : CTable → α → Prop)
    (htr : ∀ E g, event E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
        (fun s => moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows)
        (P j) E)
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
    P₀ P qE hqE q hq₀ hq nG hnG₀ hnG J hpre oa event fun E g hev => by
      obtain ⟨j, hj, hacc, hnex⟩ := htr E g hev
      exact ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
        SpecRel.redeemRelW_of_wit _ (hn64 _) _ _ _ _ (hnf _) (hci _) (hcr _) w hw) he)⟩
  refine h.trans ?_
  rw [sim_comb_sum_eq]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, moussakaRedeem]) (by norm_num [st₀, moussakaRedeem])
  gcongr
  all_goals norm_num

/-- **Ratatouille issuance, simultaneous extraction, spec relation** (as
`moussakaIssue_sim_spec`; `t_init < 2⁶⁴`, injective encodings). -/
theorem ratatouilleIssue_sim_spec (inst : ι → ByteArray × ℕ × ByteArray)
    (ht : ∀ s, (inst s).2.1 < 2 ^ 64) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows).instEnc ByteArray.empty)
    (P₀ : OracleComp specIC (ByteArray × (ι × β))) (P : ι' → OracleComp specIC (ByteArray × (ι × β)))
    (qE : ℕ) (hqE : ∀ j, IsQueryBoundP (P j) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq₀ : IsKindQueryBoundIC P₀ q) (hq : ∀ j, IsKindQueryBoundIC (P j) q) (nG : ℕ)
    (hnG₀ : IsQueryBoundP P₀ (fun t => t.isLeft = true) nG)
    (hnG : ∀ j, IsQueryBoundP (P j) (fun t => t.isLeft = true) nG)
    (J : Finset ι') (hpre : ∀ E, PrefixRuns E P₀ P J) (oa : CTable → OracleComp spec α)
    (event : CTable → α → Prop)
    (htr : ∀ E g, event E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
        (fun s => ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows) (P j) E)
      r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
        (ratatouilleIssue (inst (stOut r)).1 (inst (stOut r)).2.1 (inst (stOut r)).2.2 labelRows)
        (fun _ w => Spec.Ratatouille.IssueRel
          (SpecRel.issueInstOf (inst (stOut r)).1 (inst (stOut r)).2.1 (inst (stOut r)).2.2)
          (SpecRel.issueWitOfR w)) r) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      (q .h21 + J.card) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + J.card) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
        (q .h23 + J.card) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsSim q J.card +
        stmtBindEpsSim q J.card + J.card * failEps q qE := by
  classical
  set stF : ι → Statement := fun s =>
    ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows
  set st₀ := ratatouilleIssue ByteArray.empty 0 ByteArray.empty labelRows
  have hmu := muIn_injective (stF := stF) (dst := st₀.dst) (fun _ => rfl) hinj
  have h := prEvent_sim_le CrtGen.tables stF (decOf fun s => muIn (stF s))
    (fun s => ratatouilleIssueSys (inst s).1 (inst s).2.1 (inst s).2.2) liftInvOk_tables st₀
    (fun _ => rfl) (fun _ => rfl) none (fun _ => rfl) (fun s => decOf_apply hmu s)
    (fun s => Ratatouille.issueSystem_length _ _ _) 9
    (fun s _ => ratatouilleIssueWit (fnOf (inst s).1) (inst s).2.1 (fnOf (inst s).2.2))
    (fun s c1 lb w => ratatouilleIssue_values (inst s).1 (inst s).2.1 (inst s).2.2 labelRows c1
      lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        ratatouilleIssue_extract_chain (inst s).1 (inst s).2.1 (inst s).2.2 labelRows ch hv hA hAS
          hkos hP.1 hQS admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    P₀ P qE hqE q hq₀ hq nG hnG₀ hnG J hpre oa event fun E g hev => by
      obtain ⟨j, hj, hacc, hnex⟩ := htr E g hev
      exact ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
        SpecRel.issueRel_of_witB _ _ _ (ht _) w hw) he)⟩
  refine h.trans ?_
  rw [sim_sum_eq]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, ratatouilleIssue])
      (by norm_num [st₀, ratatouilleIssue])
  gcongr
  norm_num

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Ratatouille spend, simultaneous extraction, spec relation** (as `moussakaRedeem_sim_spec`;
`d < 2⁶⁴`, injective encodings). -/
theorem ratatouilleSpend_sim_spec (pk : ι → UovPk) (nf : ι → ByteArray) (d : ι → ℕ)
    (hd : ∀ s, d s < 2 ^ 64) (cNext ctxIss : ι → ByteArray) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows).instEnc
        ByteArray.empty)
    (P₀ : OracleComp specIC (ByteArray × (ι × β))) (P : ι' → OracleComp specIC (ByteArray × (ι × β)))
    (qE : ℕ) (hqE : ∀ j, IsQueryBoundP (P j) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq₀ : IsKindQueryBoundIC P₀ q) (hq : ∀ j, IsKindQueryBoundIC (P j) q) (nG : ℕ)
    (hnG₀ : IsQueryBoundP P₀ (fun t => t.isLeft = true) nG)
    (hnG : ∀ j, IsQueryBoundP (P j) (fun t => t.isLeft = true) nG)
    (J : Finset ι') (hpre : ∀ E, PrefixRuns E P₀ P J) (oa : CTable → OracleComp spec α)
    (event : CTable → α → Prop)
    (htr : ∀ E g, event E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
        (fun s => ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows) (P j) E)
      r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
        (ratatouilleSpend (pk (stOut r)) (nf (stOut r)) (d (stOut r)) (cNext (stOut r))
          (ctxIss (stOut r)) labelRows)
        (fun _ w => Spec.Ratatouille.SpendRel
          (SpecRel.spendInstOf (pk (stOut r)) (nf (stOut r)) (d (stOut r)) (cNext (stOut r))
            (ctxIss (stOut r)))
          (SpecRel.spendWitOf w)) r) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      (q .h21 + J.card) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + J.card) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + J.card) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q Ratatouille.uovM J.card + stmtBindEpsSim q J.card +
        J.card * failEps q qE := by
  classical
  set stF : ι → Statement := fun s =>
    ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows
  set st₀ := ratatouilleSpend ⟨ByteArray.empty, ByteArray.empty⟩ ByteArray.empty 0 ByteArray.empty
    ByteArray.empty labelRows
  have hmu := muIn_injective (stF := stF) (dst := st₀.dst) (fun _ => rfl) hinj
  have h := prEvent_sim_comb_le CrtGen.tables stF (decOf fun s => muIn (stF s))
    (fun s => ratatouilleSpendSysL (pk s) (nf s) (d s) (cNext s) (ctxIss s))
    (fun s => ratatouilleSpendWit GF256.ofBits (pk s).map (fnOf (nf s)) (d s) (fnOf (cNext s))
      (fnOf (ctxIss s)))
    (toBA (VoleMole.Spec.makeDst "rata" 0 'l' '0')) liftInvOk_tables st₀ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun s => decOf_apply hmu s)
    (fun s _ => Ratatouille.spendSystem_length _ _ _ _ _ _ _ _)
    (fun s w => prU_comb_bad_le _ _ w fun hW =>
      ratatouille_spend_comb_bad_gf128 _ _ (hd s) _ _ w hW) 9
    (fun s _ => ratatouilleSpendWit GF256.ofBits (pk s).map (fnOf (nf s)) (d s) (fnOf (cNext s))
      (fnOf (ctxIss s)))
    (fun s c1 v w => by
      rw [ratatouilleSpend_values]; simp only [ratatouilleSpendSys, ofArr_combinationOf_ba])
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc l hv A hA hAS hkos hQS hcb hP =>
        ratatouilleSpend_extract_chain (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows ch l hv
          hA hAS hkos hP.1 hQS hcb admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    P₀ P qE hqE q hq₀ hq nG hnG₀ hnG J hpre oa event fun E g hev => by
      obtain ⟨j, hj, hacc, hnex⟩ := htr E g hev
      exact ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
        SpecRel.spendRel_of_witB _ _ _ (hd _) _ _ w hw) he)⟩
  refine h.trans ?_
  rw [sim_comb_sum_eq]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, ratatouilleSpend])
      (by norm_num [st₀, ratatouilleSpend])
  gcongr
  all_goals norm_num

end VoleMole.ROM.IC
