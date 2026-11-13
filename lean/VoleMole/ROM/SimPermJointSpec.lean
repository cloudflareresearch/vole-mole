import VoleMole.ROM.SimPermJoint
import VoleMole.ROM.SimJointSpec

/-!
# Simultaneous extraction across the two relations of a protocol, permutation model, spec relations

`ROM/SimPermJoint.lean`'s `prEvent_sim_joint_leP` for the relation pairs of the protocol theorems
(as `ROM/SimJointSpec.lean` in the PRF view): Moussaka issuance and redemption, Ratatouille
issuance and spend. The provers make forward and inverse cipher queries; both relations' provers
go through the **joint normalization** `normJ p_I p_R π` (`ROM/PermJoint.lean`: inverse queries
recorded as forward ones, and before every `H₂¹` query the `H₄` queries of the `iv` at both
relations' parameters), so the two relations' reference runs have one hash log (`hsame`; for
projections of one run, `tableQueryLog_runE_normJ_map`). For `m_I` and `m_R` proofs,
`m = m_I + m_R`, `q_E` cipher queries (forward or inverse), `n_G` hash queries in all:

    Pr[some proof of either relation is accepted and its extraction fails]
      ≤ (q₂₁+m)·2⁻¹⁵⁰ + (q₂₂+m)·(ε_QS(n') + 2⁻¹²⁸ + (n_G + 2q₂₁ + 339)·2⁻⁴⁴⁸) + (q₂₃+m)·9·2⁻¹²⁸
        + chainHitEpsCombSim q M m + stmtBindEpsSim q m + m·failEpsP q q_E,

the PRF-view bound (`moussaka_sim_joint_spec`, `ratatouille_sim_joint_spec`) with the failure
terms of the permutation model (`failEpsP`: `2·q_E²·p² + 2·(openHashEps q + q₁·p'²)
+ q_E·4608·q₂₁·p²`, `p = 1/(2¹²⁸ − q_E)`, `p' = 1/(2¹²⁸ − q_E − 4607)`) and the two `H₄` queries
per `H₂¹` query in the total hash count (`n_G + 2q₂₁`, only in the `2⁻⁴⁴⁸` term).

* `mousPI`, `mousPR`, `rataPI`, `rataPS`: the relations' parameters.
* `chainHitEpsCombSim_addH4`, `stmtBindEpsSim_addH4`: the hit terms do not count `H₄` queries.
* **`moussaka_sim_joint_specP`**, **`ratatouille_sim_joint_specP`**.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-- Moussaka issuance's parameters. -/
abbrev mousPI (lr : Bool) : Params := (moussakaIssue ByteArray.empty ByteArray.empty lr).params

/-- Moussaka redemption's parameters. -/
abbrev mousPR (lr : Bool) : Params :=
  (moussakaRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty ByteArray.empty lr).params

/-- Ratatouille issuance's parameters. -/
abbrev rataPI (lr : Bool) : Params := (ratatouilleIssue ByteArray.empty 0 ByteArray.empty lr).params

/-- Ratatouille spend's parameters. -/
abbrev rataPS (lr : Bool) : Params :=
  (ratatouilleSpend ⟨ByteArray.empty, ByteArray.empty⟩ ByteArray.empty 0 ByteArray.empty
    ByteArray.empty lr).params

lemma chainHitEpsCombSim_addH4 (q : Kind → ℕ) (M m : ℕ) :
    chainHitEpsCombSim (addH4 q) M m = chainHitEpsCombSim q M m := by
  simp [chainHitEpsCombSim, chainHitEpsSim, addH4]

lemma stmtBindEpsSim_addH4 (q : Kind → ℕ) (m : ℕ) :
    stmtBindEpsSim (addH4 q) m = stmtBindEpsSim q m := by
  simp [stmtBindEpsSim, addH4]

/-! ## Moussaka -/

variable {ιI' ιR' α ιI βI ιR βR : Type}

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Moussaka issuance and redemption, simultaneous extraction across both relations, spec
relations, permutation model** (`moussaka_sim_joint_spec` for provers with forward and inverse
cipher queries, run through the joint normalization `normJ`, the two reference runs having one
hash log after it): each query of the run is charged once, at the redemption relation's charge;
the failure terms are the permutation model's `failEpsP`. -/
theorem moussaka_sim_joint_specP (inst : ιI → ByteArray × ByteArray)
    (ht : ∀ s, (inst s).1.size = 45) (hciI : ∀ s, (inst s).2.size = 16) (labelRows : Bool)
    (hinjI : Function.Injective fun s =>
      (moussakaIssue (inst s).1 (inst s).2 labelRows).instEnc ByteArray.empty)
    (anc : ιR → List UovPk)
    (hn64 : ∀ s, (anc s).length ≤ 64) (nf ctxIss ctxRed cd : ιR → ByteArray)
    (hnf : ∀ s, (nf s).size = 24) (hci : ∀ s, (ctxIss s).size = 16)
    (hcr : ∀ s, (ctxRed s).size = 16)
    (hinjR : Function.Injective fun s =>
      (moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows).instEnc
        ByteArray.empty)
    (PI₀ : OracleComp specP (ByteArray × (ιI × βI)))
    (PI : ιI' → OracleComp specP (ByteArray × (ιI × βI)))
    (PR₀ : OracleComp specP (ByteArray × (ιR × βR)))
    (PR : ιR' → OracleComp specP (ByteArray × (ιR × βR)))
    (JI : Finset ιI') (JR : Finset ιR') (qE : ℕ)
    (hqEI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isRight = true) qE)
    (hqER : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hqI : ∀ j ∈ JI, IsKindQueryBoundP (PI j) q) (hqR₀ : IsKindQueryBoundP PR₀ q)
    (hqR : ∀ j ∈ JR, IsKindQueryBoundP (PR j) q) (nG : ℕ)
    (hnGI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isLeft = true) nG)
    (hnGR₀ : IsQueryBoundP PR₀ (fun t => t.isLeft = true) nG)
    (hnGR : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isLeft = true) nG)
    (hpreI : ∀ π : PTable, PrefixRuns π.fwd (normJ (mousPI labelRows) (mousPR labelRows) π PI₀)
      (fun j => normJ (mousPI labelRows) (mousPR labelRows) π (PI j)) JI)
    (hpreR : ∀ π : PTable, PrefixRuns π.fwd (normJ (mousPI labelRows) (mousPR labelRows) π PR₀)
      (fun j => normJ (mousPI labelRows) (mousPR labelRows) π (PR j)) JR)
    (hsame : ∀ (π : PTable) g,
      tableQueryLog (runE π.fwd (normJ (mousPI labelRows) (mousPR labelRows) π PI₀)) g =
        tableQueryLog (runE π.fwd (normJ (mousPI labelRows) (mousPR labelRows) π PR₀)) g)
    (oa : PTable → OracleComp spec α) (event : PTable → α → Prop)
    (htr : ∀ π g, event π (evalWithAnswerFn (QueryImpl.ofFn g) (oa π)) →
      (∃ j ∈ JI, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s => moussakaIssue (inst s).1 (inst s).2 labelRows)
          (normJ (mousPI labelRows) (mousPR labelRows) π (PI j)) π.fwd)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (moussakaIssue (inst (stOut r)).1 (inst (stOut r)).2 labelRows)
          (fun _ w => Privacy.Moussaka.IssueRelW
            ⟨toL (inst (stOut r)).1, toL (inst (stOut r)).2⟩
            (SpecRel.issueWitOf (toL (inst (stOut r)).2) w)) r) ∨
      (∃ j ∈ JR, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s => moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows)
          (normJ (mousPI labelRows) (mousPR labelRows) π (PR j)) π.fwd)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (moussakaRedeem (anc (stOut r)) (nf (stOut r)) (ctxIss (stOut r)) (ctxRed (stOut r))
            (cd (stOut r)) labelRows)
          (fun _ w => Privacy.Moussaka.RedeemRelW
            ⟨(anc (stOut r)).map UovPk.toSpec, toL (nf (stOut r)), toL (ctxIss (stOut r)),
              toL (ctxRed (stOut r)), toL (cd (stOut r))⟩
            (SpecRel.redeemWitOf (toL (nf (stOut r))) (toL (ctxIss (stOut r)))
              (toL (ctxRed (stOut r))) w)) r)) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (oa π)).run' ∅}[event π r] ≤
      (q .h21 + (JI.card + JR.card)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + (JI.card + JR.card)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 * q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + (JI.card + JR.card)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q Moussaka.M (JI.card + JR.card) +
        stmtBindEpsSim q (JI.card + JR.card) + JI.card * failEpsP q qE +
        JR.card * failEpsP q qE := by
  classical
  set stI : ιI → Statement := fun s => moussakaIssue (inst s).1 (inst s).2 labelRows
  set stI₀ := moussakaIssue ByteArray.empty ByteArray.empty labelRows
  set stR : ιR → Statement := fun s =>
    moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows
  set stR₀ := moussakaRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty ByteArray.empty
    labelRows
  have hmuI := muIn_injective (stF := stI) (dst := stI₀.dst) (fun _ => rfl) hinjI
  have hmuR := muIn_injective (stF := stR) (dst := stR₀.dst) (fun _ => rfl) hinjR
  have hsep := decOf_sep (fun s => muIn (stI s)) (fun s => muIn (stR s)) fun s s' =>
    muIn_ne_of_dst (by simp only [stI, stR, moussakaIssue, moussakaRedeem]; rfl)
      (by
        simp only [stI, stR, moussakaIssue, moussakaRedeem]
        intro h
        have := congrArg toL h
        simp only [SpecRel.toL_toBA] at this
        revert this
        decide)
  have h := prEvent_sim_joint_leP CrtGen.tables liftInvOk_tables stI (decOf fun s => muIn (stI s))
    (fun s => moussakaIssueSys (inst s).1 (inst s).2) stI₀ (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun s => decOf_apply hmuI s) (fun s => Moussaka.issueSystem_length _ _)
    stR (decOf fun s => muIn (stR s))
    (fun s => moussakaRedeemSysL (anc s) (nf s) (ctxIss s) (ctxRed s))
    (fun s => moussakaRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    (toBA (VoleMole.Spec.makeDst "mous" 0 'l' '0')) stR₀ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun s => decOf_apply hmuR s)
    (fun s _ => Moussaka.redeemSystem_length _ _ _ _ _ _ _)
    (fun s w => prU_comb_bad_le _ _ w fun hW =>
      moussaka_redeem_comb_bad_gf128 _ (by simpa using hn64 s) _ _ _ w hW) hsep 9
    (fun s _ => moussakaIssueWit (fun k => fnOf (inst s).1 k.val) (fnOf (inst s).2))
    (fun s c1 lb w => moussakaIssue_values (inst s).1 (inst s).2 labelRows c1 lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        moussakaIssue_extract_chain (inst s).1 (inst s).2 labelRows ch hv hA hAS hkos hP.1 hQS
          admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    (fun s _ => moussakaRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    (fun s c1 v w => by
      rw [moussakaRedeem_values]; simp only [moussakaRedeemSys, ofArr_combinationOf_ba])
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc l hv A hA hAS hkos hQS hcb hP =>
        moussakaRedeem_extract_chain (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows ch l hv
          hA hAS hkos hP.1 hQS hcb admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    stI₀.params (addIV stR₀.params PI₀) (fun j => addIV stR₀.params (PI j))
    (addIV stR₀.params PR₀) (fun j => addIV stR₀.params (PR j))
    (fun j π g => ivBefore_normP stI₀.params π _ g)
    (fun j π g => ivBefore_normP_addIV stI₀.params stR₀.params π (PR j) g) JI JR qE
    (fun j hj => isQueryBoundP_right_addIV _ (hqEI j hj))
    (fun j hj => isQueryBoundP_right_addIV _ (hqER j hj)) (addH4 q)
    (fun j hj => isKindQueryBoundP_addIV _ (hqI j hj)) (isKindQueryBoundP_addIV _ hqR₀)
    (fun j hj => isKindQueryBoundP_addIV _ (hqR j hj)) (nG + q .h21)
    (fun j hj => isQueryBoundP_left_addIV _ (hnGI j hj) (hqI j hj))
    (isQueryBoundP_left_addIV _ hnGR₀ hqR₀)
    (fun j hj => isQueryBoundP_left_addIV _ (hnGR j hj) (hqR j hj)) hpreI hpreR hsame oa event
    fun π g hev => by
      rcases htr π g hev with ⟨j, hj, hacc, hnex⟩ | ⟨j, hj, hacc, hnex⟩
      · exact Or.inl ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
          SpecRel.issueRelW_of_wit _ _ (ht _) (hciI _) w hw) he)⟩
      · exact Or.inr ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
          SpecRel.redeemRelW_of_wit _ (hn64 _) _ _ _ _ (hnf _) (hci _) (hcr _) w hw) he)⟩
  rw [failEpsP_addH4] at h
  refine h.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  have hkosI : epsKOS #chal3Blocks (Chain.kosL stI₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stI₀, moussakaIssue]) (by norm_num [stI₀, moussakaIssue])
  have hkosR : epsKOS #chal3Blocks (Chain.kosL stR₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stR₀, moussakaRedeem])
      (by norm_num [stR₀, moussakaRedeem])
  refine (sim_joint_sum_le stI₀ stR₀ _ _ _ _ 9 _ (addH4 (addH4 q)) JI JR _
    (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) + (2 ^ 128 : ℝ≥0∞)⁻¹) hkosI hkosR
    ((ofReal_epsQS_mono (by norm_num) (by norm_num)).trans le_self_add) le_rfl).trans ?_
  simp only [addH4_of_ne _ (show Kind.h21 ≠ .h4 by decide),
    addH4_of_ne _ (show Kind.h22 ≠ .h4 by decide), addH4_of_ne _ (show Kind.h23 ≠ .h4 by decide),
    chainHitEpsCombSim_addH4, stmtBindEpsSim_addH4, two_mul, Nat.cast_ofNat, add_assoc, le_refl]

/-! ## Ratatouille -/

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Ratatouille issuance and spend, simultaneous extraction across both relations, spec
relations, permutation model** (`ratatouille_sim_joint_spec` for provers with forward and inverse
cipher queries, run through the joint normalization `normJ`, the two reference runs having one
hash log after it): each query of the run is charged once, at the spend relation's charge; the
failure terms are the permutation model's `failEpsP`. -/
theorem ratatouille_sim_joint_specP (inst : ιI → ByteArray × ℕ × ByteArray)
    (ht : ∀ s, (inst s).2.1 < 2 ^ 64) (labelRows : Bool)
    (hinjI : Function.Injective fun s =>
      (ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows).instEnc ByteArray.empty)
    (pk : ιR → UovPk) (nf : ιR → ByteArray) (d : ιR → ℕ)
    (hd : ∀ s, d s < 2 ^ 64) (cNext ctxIss : ιR → ByteArray)
    (hinjR : Function.Injective fun s =>
      (ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows).instEnc
        ByteArray.empty)
    (PI₀ : OracleComp specP (ByteArray × (ιI × βI)))
    (PI : ιI' → OracleComp specP (ByteArray × (ιI × βI)))
    (PR₀ : OracleComp specP (ByteArray × (ιR × βR)))
    (PR : ιR' → OracleComp specP (ByteArray × (ιR × βR)))
    (JI : Finset ιI') (JR : Finset ιR') (qE : ℕ)
    (hqEI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isRight = true) qE)
    (hqER : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hqI : ∀ j ∈ JI, IsKindQueryBoundP (PI j) q) (hqR₀ : IsKindQueryBoundP PR₀ q)
    (hqR : ∀ j ∈ JR, IsKindQueryBoundP (PR j) q) (nG : ℕ)
    (hnGI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isLeft = true) nG)
    (hnGR₀ : IsQueryBoundP PR₀ (fun t => t.isLeft = true) nG)
    (hnGR : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isLeft = true) nG)
    (hpreI : ∀ π : PTable, PrefixRuns π.fwd (normJ (rataPI labelRows) (rataPS labelRows) π PI₀)
      (fun j => normJ (rataPI labelRows) (rataPS labelRows) π (PI j)) JI)
    (hpreR : ∀ π : PTable, PrefixRuns π.fwd (normJ (rataPI labelRows) (rataPS labelRows) π PR₀)
      (fun j => normJ (rataPI labelRows) (rataPS labelRows) π (PR j)) JR)
    (hsame : ∀ (π : PTable) g,
      tableQueryLog (runE π.fwd (normJ (rataPI labelRows) (rataPS labelRows) π PI₀)) g =
        tableQueryLog (runE π.fwd (normJ (rataPI labelRows) (rataPS labelRows) π PR₀)) g)
    (oa : PTable → OracleComp spec α) (event : PTable → α → Prop)
    (htr : ∀ π g, event π (evalWithAnswerFn (QueryImpl.ofFn g) (oa π)) →
      (∃ j ∈ JI, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s => ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows)
          (normJ (rataPI labelRows) (rataPS labelRows) π (PI j)) π.fwd)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (ratatouilleIssue (inst (stOut r)).1 (inst (stOut r)).2.1 (inst (stOut r)).2.2
            labelRows)
          (fun _ w => Spec.Ratatouille.IssueRel
            (SpecRel.issueInstOf (inst (stOut r)).1 (inst (stOut r)).2.1 (inst (stOut r)).2.2)
            (SpecRel.issueWitOfR w)) r) ∨
      (∃ j ∈ JR, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s => ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows)
          (normJ (rataPI labelRows) (rataPS labelRows) π (PR j)) π.fwd)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (ratatouilleSpend (pk (stOut r)) (nf (stOut r)) (d (stOut r)) (cNext (stOut r))
            (ctxIss (stOut r)) labelRows)
          (fun _ w => Spec.Ratatouille.SpendRel
            (SpecRel.spendInstOf (pk (stOut r)) (nf (stOut r)) (d (stOut r)) (cNext (stOut r))
              (ctxIss (stOut r)))
            (SpecRel.spendWitOf w)) r)) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (oa π)).run' ∅}[event π r] ≤
      (q .h21 + (JI.card + JR.card)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + (JI.card + JR.card)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 * q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + (JI.card + JR.card)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q Ratatouille.uovM (JI.card + JR.card) +
        stmtBindEpsSim q (JI.card + JR.card) + JI.card * failEpsP q qE +
        JR.card * failEpsP q qE := by
  classical
  set stI : ιI → Statement := fun s =>
    ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows
  set stI₀ := ratatouilleIssue ByteArray.empty 0 ByteArray.empty labelRows
  set stR : ιR → Statement := fun s =>
    ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows
  set stR₀ := ratatouilleSpend ⟨ByteArray.empty, ByteArray.empty⟩ ByteArray.empty 0 ByteArray.empty
    ByteArray.empty labelRows
  have hmuI := muIn_injective (stF := stI) (dst := stI₀.dst) (fun _ => rfl) hinjI
  have hmuR := muIn_injective (stF := stR) (dst := stR₀.dst) (fun _ => rfl) hinjR
  have hsep := decOf_sep (fun s => muIn (stI s)) (fun s => muIn (stR s)) fun s s' =>
    muIn_ne_of_dst (by simp only [stI, stR, ratatouilleIssue, ratatouilleSpend]; rfl)
      (by
        simp only [stI, stR, ratatouilleIssue, ratatouilleSpend]
        intro h
        have := congrArg toL h
        simp only [SpecRel.toL_toBA] at this
        revert this
        decide)
  have h := prEvent_sim_joint_leP CrtGen.tables liftInvOk_tables stI (decOf fun s => muIn (stI s))
    (fun s => ratatouilleIssueSys (inst s).1 (inst s).2.1 (inst s).2.2) stI₀ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun s => decOf_apply hmuI s)
    (fun s => Ratatouille.issueSystem_length _ _ _)
    stR (decOf fun s => muIn (stR s))
    (fun s => ratatouilleSpendSysL (pk s) (nf s) (d s) (cNext s) (ctxIss s))
    (fun s => ratatouilleSpendWit GF256.ofBits (pk s).map (fnOf (nf s)) (d s) (fnOf (cNext s))
      (fnOf (ctxIss s)))
    (toBA (VoleMole.Spec.makeDst "rata" 0 'l' '0')) stR₀ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun s => decOf_apply hmuR s)
    (fun s _ => Ratatouille.spendSystem_length _ _ _ _ _ _ _ _)
    (fun s w => prU_comb_bad_le _ _ w fun hW =>
      ratatouille_spend_comb_bad_gf128 _ _ (hd s) _ _ w hW) hsep 9
    (fun s _ => ratatouilleIssueWit (fnOf (inst s).1) (inst s).2.1 (fnOf (inst s).2.2))
    (fun s c1 lb w => ratatouilleIssue_values (inst s).1 (inst s).2.1 (inst s).2.2 labelRows c1
      lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        ratatouilleIssue_extract_chain (inst s).1 (inst s).2.1 (inst s).2.2 labelRows ch hv hA hAS
          hkos hP.1 hQS admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    (fun s _ => ratatouilleSpendWit GF256.ofBits (pk s).map (fnOf (nf s)) (d s) (fnOf (cNext s))
      (fnOf (ctxIss s)))
    (fun s c1 v w => by
      rw [ratatouilleSpend_values]; simp only [ratatouilleSpendSys, ofArr_combinationOf_ba])
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc l hv A hA hAS hkos hQS hcb hP =>
        ratatouilleSpend_extract_chain (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows ch l hv
          hA hAS hkos hP.1 hQS hcb admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    stI₀.params (addIV stR₀.params PI₀) (fun j => addIV stR₀.params (PI j))
    (addIV stR₀.params PR₀) (fun j => addIV stR₀.params (PR j))
    (fun j π g => ivBefore_normP stI₀.params π _ g)
    (fun j π g => ivBefore_normP_addIV stI₀.params stR₀.params π (PR j) g) JI JR qE
    (fun j hj => isQueryBoundP_right_addIV _ (hqEI j hj))
    (fun j hj => isQueryBoundP_right_addIV _ (hqER j hj)) (addH4 q)
    (fun j hj => isKindQueryBoundP_addIV _ (hqI j hj)) (isKindQueryBoundP_addIV _ hqR₀)
    (fun j hj => isKindQueryBoundP_addIV _ (hqR j hj)) (nG + q .h21)
    (fun j hj => isQueryBoundP_left_addIV _ (hnGI j hj) (hqI j hj))
    (isQueryBoundP_left_addIV _ hnGR₀ hqR₀)
    (fun j hj => isQueryBoundP_left_addIV _ (hnGR j hj) (hqR j hj)) hpreI hpreR hsame oa event
    fun π g hev => by
      rcases htr π g hev with ⟨j, hj, hacc, hnex⟩ | ⟨j, hj, hacc, hnex⟩
      · exact Or.inl ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
          SpecRel.issueRel_of_witB _ _ _ (ht _) w hw) he)⟩
      · exact Or.inr ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
          SpecRel.spendRel_of_witB _ _ _ (hd _) _ _ w hw) he)⟩
  rw [failEpsP_addH4] at h
  refine h.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  have hkosI : epsKOS #chal3Blocks (Chain.kosL stI₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stI₀, ratatouilleIssue])
      (by norm_num [stI₀, ratatouilleIssue])
  have hkosR : epsKOS #chal3Blocks (Chain.kosL stR₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stR₀, ratatouilleSpend])
      (by norm_num [stR₀, ratatouilleSpend])
  refine (sim_joint_sum_le stI₀ stR₀ _ _ _ _ 9 _ (addH4 (addH4 q)) JI JR _
    (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) + (2 ^ 128 : ℝ≥0∞)⁻¹) hkosI hkosR
    ((ofReal_epsQS_mono (by norm_num) (by norm_num)).trans le_self_add) le_rfl).trans ?_
  simp only [addH4_of_ne _ (show Kind.h21 ≠ .h4 by decide),
    addH4_of_ne _ (show Kind.h22 ≠ .h4 by decide), addH4_of_ne _ (show Kind.h23 ≠ .h4 by decide),
    chainHitEpsCombSim_addH4, stmtBindEpsSim_addH4, two_mul, Nat.cast_ofNat, add_assoc, le_refl]

end VoleMole.ROM.IC
