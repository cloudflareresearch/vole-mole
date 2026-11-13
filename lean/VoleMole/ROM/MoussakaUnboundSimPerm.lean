import VoleMole.ROM.MoussakaUnboundSim
import VoleMole.ROM.SimPermJointSpec

/-!
# Simultaneous extraction for the unbound Moussaka relations, permutation model

`ROM/MoussakaUnboundSim.lean`'s `moussakaUnbound_sim_joint_spec` with the ideal cipher as random
permutations and inverse queries (`ROM/SimPermJointSpec.lean`): both relations' provers go through
the joint normalization `normJ (mousUPI lr) (mousUPR lr) π`, so the reference runs have one hash
log. The bound is the PRF view's with the failure terms `failEpsP` and the total hash count
`n_G + 2q₂₁` in the `2⁻⁴⁴⁸` term.

* `mousUPI`, `mousUPR`: the unbound relations' parameters.
* **`moussakaUnbound_sim_joint_specP`**.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-- Unbound issuance's parameters. -/
abbrev mousUPI (lr : Bool) : Params :=
  (moussakaUnboundIssue ByteArray.empty ByteArray.empty lr).params

/-- Unbound redemption's parameters. -/
abbrev mousUPR (lr : Bool) : Params :=
  (moussakaUnboundRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty ByteArray.empty
    lr).params

variable {α ιI' ιR' ιI βI ιR βR : Type}

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Unbound issuance and redemption, simultaneous extraction across both relations, spec
relations, permutation model** (`moussakaUnbound_sim_joint_spec` for provers with forward and
inverse cipher queries, run through the joint normalization `normJ`, the two reference runs
having one hash log after it): each query of the run is charged once, at the redemption
relation's charge; the failure terms are the permutation model's `failEpsP`. -/
theorem moussakaUnbound_sim_joint_specP (stI : ιI → Statement) (lr : Bool)
    (inst : ιI → ByteArray × ByteArray)
    (hstI : ∀ s, Unbound.IssueStmt (stI s) lr (inst s).1 (inst s).2)
    (ht : ∀ s, (inst s).1.size = 45)
    (hinjI : Function.Injective fun s => (stI s).instEnc ByteArray.empty)
    (stR : ιR → Statement)
    (anc : ιR → List UovPk) (hn64 : ∀ s, (anc s).length ≤ 64)
    (nf ctxIss ctxRed cd : ιR → ByteArray)
    (hstR : ∀ s, Unbound.RedeemStmt (stR s) lr (anc s) (nf s) (ctxIss s) (ctxRed s))
    (hnf : ∀ s, (nf s).size = 24)
    (hinjR : Function.Injective fun s => (stR s).instEnc ByteArray.empty)
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
    (hpreI : ∀ π : PTable, PrefixRuns π.fwd (normJ (mousUPI lr) (mousUPR lr) π PI₀)
      (fun j => normJ (mousUPI lr) (mousUPR lr) π (PI j)) JI)
    (hpreR : ∀ π : PTable, PrefixRuns π.fwd (normJ (mousUPI lr) (mousUPR lr) π PR₀)
      (fun j => normJ (mousUPI lr) (mousUPR lr) π (PR j)) JR)
    (hsame : ∀ (π : PTable) g,
      tableQueryLog (runE π.fwd (normJ (mousUPI lr) (mousUPR lr) π PI₀)) g =
        tableQueryLog (runE π.fwd (normJ (mousUPI lr) (mousUPR lr) π PR₀)) g)
    (oa : PTable → OracleComp spec α) (event : PTable → α → Prop)
    (htr : ∀ π g, event π (evalWithAnswerFn (QueryImpl.ofFn g) (oa π)) →
      (∃ j ∈ JI,
        let r := evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables stI (normJ (mousUPI lr) (mousUPR lr) π (PI j)) π.fwd)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (stI (stOut r))
          (fun _ w => Spec.MoussakaUnbound.IssueRel
            ⟨toL (inst (stOut r)).1, toL (inst (stOut r)).2⟩
            (SpecRel.uIssueWitOf (toL (inst (stOut r)).2) w)) r) ∨
      (∃ j ∈ JR,
        let r := evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables stR (normJ (mousUPI lr) (mousUPR lr) π (PR j)) π.fwd)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (stR (stOut r))
          (fun _ w => Spec.MoussakaUnbound.RedeemRel
            ⟨(anc (stOut r)).map UovPk.toSpec, toL (nf (stOut r)), toL (ctxIss (stOut r)),
              toL (ctxRed (stOut r)), toL (cd (stOut r))⟩
            (SpecRel.uRedeemWitOf (toL (ctxIss (stOut r))) (toL (ctxRed (stOut r))) w)) r)) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (oa π)).run' ∅}[event π r] ≤
      (q .h21 + (JI.card + JR.card)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + (JI.card + JR.card)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 * q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + (JI.card + JR.card)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q Moussaka.M (JI.card + JR.card) +
        stmtBindEpsSim q (JI.card + JR.card) + JI.card * failEpsP q qE +
        JR.card * failEpsP q qE := by
  classical
  set stI₀ := moussakaUnboundIssue ByteArray.empty ByteArray.empty lr
  set stR₀ := moussakaUnboundRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty
    ByteArray.empty lr
  have hmuI := muIn_injective (stF := stI) (dst := Unbound.issueDst) (fun s => (hstI s).dst) hinjI
  have hmuR := muIn_injective (stF := stR) (dst := Unbound.redeemDst) (fun s => (hstR s).dst)
    hinjR
  have h := prEvent_sim_joint_leP CrtGen.tables liftInvOk_tables stI (decOf fun s => muIn (stI s))
    (fun s => moussakaUnboundIssueSys (inst s).1 (inst s).2) stI₀ (fun s => (hstI s).params)
    (fun s => (hstI s).delayed) (fun s => (hstI s).comb) (fun s => decOf_apply hmuI s)
    (fun s => MoussakaUnbound.uIssueSystem_length _ _)
    stR (decOf fun s => muIn (stR s))
    (fun s => moussakaUnboundRedeemSysL (anc s) (nf s) (ctxIss s) (ctxRed s))
    (fun s => moussakaUnboundRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    Unbound.combDst stR₀ (fun s => (hstR s).params) (fun s => (hstR s).delayed)
    (fun s => (hstR s).comb) (fun s => decOf_apply hmuR s)
    (fun s _ => MoussakaUnbound.uRedeemSystem_length _ _ _ _ _ _ _)
    (fun s w => prU_comb_bad_le _ _ w fun hW =>
      moussaka_unbound_redeem_comb_bad_gf128 _ (by simpa using hn64 s) _ _ _ w hW)
    (unbound_sep (fun s => (hstI s).dst) (fun s => (hstR s).dst)) 9
    (fun s _ => moussakaUnboundIssueWit (fun k => fnOf (inst s).1 k.val) (fnOf (inst s).2))
    (fun s c1 lb w => (hstI s).values c1 lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        Unbound.issue_extract_chain (hstI s) ch hv hA hAS hkos hP.1 hQS admissible deltaBlocks
          deltaBlocks_injOn acc hP.2)
    (fun s _ => moussakaUnboundRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    (fun s c1 v w => by
      rw [(hstR s).values]; simp only [moussakaUnboundRedeemSys, ofArr_combinationOf_ba])
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc l hv A hA hAS hkos hQS hcb hP =>
        Unbound.redeem_extract_chain (hstR s) ch l hv hA hAS hkos hP.1 hQS hcb admissible
          deltaBlocks deltaBlocks_injOn acc hP.2)
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
      · exact Or.inl ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun _ w hw =>
          SpecRel.uIssueRel_of_wit _ _ (ht _) w hw) he)⟩
      · exact Or.inr ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun _ w hw =>
          SpecRel.uRedeemRel_of_wit _ (hn64 _) _ _ _ _ (hnf _) w hw) he)⟩
  rw [failEpsP_addH4] at h
  refine h.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  have hkosI : epsKOS #chal3Blocks (Chain.kosL stI₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _
      (Unbound.moussakaUnboundIssue_stmt ByteArray.empty ByteArray.empty lr).witnessBytes_le
      (Unbound.moussakaUnboundIssue_stmt ByteArray.empty ByteArray.empty lr).qsDegree_le
  have hkosR : epsKOS #chal3Blocks (Chain.kosL stR₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (Unbound.moussakaUnboundRedeem_stmt [] ByteArray.empty
      ByteArray.empty ByteArray.empty ByteArray.empty lr).witnessBytes_le
      (Unbound.moussakaUnboundRedeem_stmt [] ByteArray.empty ByteArray.empty ByteArray.empty
        ByteArray.empty lr).qsDegree_le
  refine (sim_joint_sum_le stI₀ stR₀ _ _ _ _ 9 _ (addH4 (addH4 q)) JI JR _
    (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) + (2 ^ 128 : ℝ≥0∞)⁻¹) hkosI hkosR
    ((ofReal_epsQS_mono (by norm_num) (by norm_num)).trans le_self_add) le_rfl).trans ?_
  simp only [addH4_of_ne _ (show Kind.h21 ≠ .h4 by decide),
    addH4_of_ne _ (show Kind.h22 ≠ .h4 by decide), addH4_of_ne _ (show Kind.h23 ≠ .h4 by decide),
    chainHitEpsCombSim_addH4, stmtBindEpsSim_addH4, two_mul, Nat.cast_ofNat, add_assoc, le_refl]

end VoleMole.ROM.IC
