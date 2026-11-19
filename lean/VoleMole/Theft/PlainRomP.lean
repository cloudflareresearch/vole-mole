import VoleMole.Theft.PlainRom
import VoleMole.ROM.SimPermJointSpec

/-!
# `ROM/`'s simultaneous extraction for the Lean Ratatouille statements, permutation model

`ratatouille_sim_joint_lean` (`Theft/PlainRom.lean`) restates `ratatouille_sim_joint_spec` (PRF
view, forward cipher queries) for the Lean statements `stI`, `stS`. Here the same for the
permutation model (`ratatouille_sim_joint_specP`, `ROM/SimPermJointSpec.lean`): the provers make
forward and inverse cipher queries (`specP`), both relations' provers are run through the joint
normalization `normJ (rataPI true) (rataPS true) π`, and the failure terms are `failEpsP`.

* **`ratatouille_sim_joint_leanP`**.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM VoleMole.ROM.IC
open VoleMole.Privacy.Ratatouille (stI stS stS_values bOf)

variable {ιI' ιR' α βI βR : Type}

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Ratatouille issuance and spend, simultaneous extraction, Lean statements, permutation
model** (`ratatouille_sim_joint_specP` for `stI` and for `stS` with the key `pk₀`): provers with
forward and inverse cipher queries, run through `normJ`; each query of the run charged once; the
witnesses are in the spec relations. -/
theorem ratatouille_sim_joint_leanP (pk₀ : Spec.Ratatouille.PublicKey)
    (PI₀ : OracleComp specP (ByteArray × (Spec.Ratatouille.IssueInstance × βI)))
    (PI : ιI' → OracleComp specP (ByteArray × (Spec.Ratatouille.IssueInstance × βI)))
    (PR₀ : OracleComp specP (ByteArray × (SpendK pk₀ × βR)))
    (PR : ιR' → OracleComp specP (ByteArray × (SpendK pk₀ × βR)))
    (JI : Finset ιI') (JR : Finset ιR') (qE : ℕ)
    (hqEI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isRight = true) qE)
    (hqER : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hqI : ∀ j ∈ JI, IsKindQueryBoundP (PI j) q) (hqR₀ : IsKindQueryBoundP PR₀ q)
    (hqR : ∀ j ∈ JR, IsKindQueryBoundP (PR j) q) (nG : ℕ)
    (hnGI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isLeft = true) nG)
    (hnGR₀ : IsQueryBoundP PR₀ (fun t => t.isLeft = true) nG)
    (hnGR : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isLeft = true) nG)
    (hpreI : ∀ π : PTable, PrefixRuns π.fwd (normJ (rataPI true) (rataPS true) π PI₀)
      (fun j => normJ (rataPI true) (rataPS true) π (PI j)) JI)
    (hpreR : ∀ π : PTable, PrefixRuns π.fwd (normJ (rataPI true) (rataPS true) π PR₀)
      (fun j => normJ (rataPI true) (rataPS true) π (PR j)) JR)
    (hsame : ∀ (π : PTable) g,
      tableQueryLog (runE π.fwd (normJ (rataPI true) (rataPS true) π PI₀)) g =
        tableQueryLog (runE π.fwd (normJ (rataPI true) (rataPS true) π PR₀)) g)
    (oa : PTable → OracleComp spec α) (event : PTable → α → Prop)
    (htr : ∀ π g, event π (evalWithAnswerFn (QueryImpl.ofFn g) (oa π)) →
      (∃ j ∈ JI, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables stI
          (normJ (rataPI true) (rataPS true) π (PI j)) π.fwd);
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (stI (stOut r))
          (fun _ w => Spec.Ratatouille.IssueRel (stOut r) (SpecRel.issueWitOfR w)) r) ∨
      (∃ j ∈ JR, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stK pk₀)
          (normJ (rataPI true) (rataPS true) π (PR j)) π.fwd);
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (stS (stOut r).1)
          (fun _ w => Spec.Ratatouille.SpendRel (stOut r).1 (SpecRel.spendWitOf w)) r)) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (oa π)).run' ∅}[event π r] ≤
      (q .h21 + (JI.card + JR.card)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + (JI.card + JR.card)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 * q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + (JI.card + JR.card)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q Ratatouille.uovM (JI.card + JR.card) +
        stmtBindEpsSim q (JI.card + JR.card) + JI.card * failEpsP q qE +
        JR.card * failEpsP q qE := by
  classical
  set stR : SpendK pk₀ → Statement := stK pk₀
  set stI₀ := ratatouilleIssue ByteArray.empty 0 ByteArray.empty true
  set stR₀ := ratatouilleSpend ⟨ByteArray.empty, ByteArray.empty⟩ ByteArray.empty 0 ByteArray.empty
    ByteArray.empty true
  have hsep := decOf_sep (fun s => muIn (stI s)) (fun s => muIn (stR s)) fun s s' =>
    muIn_ne_of_dst (by simp only [stI, stR, stS, ratatouilleIssue]; rfl)
      (by
        simp only [stI, stR, stS, ratatouilleIssue]
        intro h
        have := congrArg toL h
        simp only [SpecRel.toL_toBA] at this
        revert this
        decide)
  have h := prEvent_sim_joint_leP CrtGen.tables liftInvOk_tables stI (decOf fun s => muIn (stI s))
    (fun s => ratatouilleIssueSys (bOf s.c) s.tInit.toNat (bOf s.ctx)) stI₀ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun s => decOf_apply muIn_stI_injective s)
    (fun s => Ratatouille.issueSystem_length _ _ _)
    stR (decOf fun s => muIn (stR s))
    (fun s l => Ratatouille.spendSystem beta GF256.toBits s.1.pk (fnOf (bOf s.1.nf)) s.1.d.toNat
      (fnOf (bOf s.1.cNext)) (fnOf (bOf s.1.ctx)) l)
    (fun s => ratatouilleSpendWit GF256.ofBits s.1.pk (fnOf (bOf s.1.nf)) s.1.d.toNat
      (fnOf (bOf s.1.cNext)) (fnOf (bOf s.1.ctx)))
    (toBA (VoleMole.Spec.makeDst "rata" 0 'l' '0')) stR₀ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun s => decOf_apply (muIn_stK_injective pk₀) s)
    (fun s _ => Ratatouille.spendSystem_length _ _ _ _ _ _ _ _)
    (fun s w => prU_comb_bad_le _ _ w fun hW =>
      ratatouille_spend_comb_bad_gf128 _ _ (UInt64.toNat_lt _) _ _ w hW) hsep 9
    (fun s _ => ratatouilleIssueWit (fnOf (bOf s.c)) s.tInit.toNat (fnOf (bOf s.ctx)))
    (fun s c1 lb w => ratatouilleIssue_values (bOf s.c) s.tInit.toNat (bOf s.ctx) true c1 lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        ratatouilleIssue_extract_chain (bOf s.c) s.tInit.toNat (bOf s.ctx) true ch hv hA hAS
          hkos hP.1 hQS admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    (fun s _ => ratatouilleSpendWit GF256.ofBits s.1.pk (fnOf (bOf s.1.nf)) s.1.d.toNat
      (fnOf (bOf s.1.cNext)) (fnOf (bOf s.1.ctx)))
    (fun s c1 v w => by
      rw [stS_values]; simp only [Privacy.Ratatouille.csS, ofArr_combinationOf_ba])
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc l hv A hA hAS hkos hQS hcb hP =>
        stS_extract_chain s.1 ch l hv hA hAS hkos hP.1 hQS hcb admissible deltaBlocks
          deltaBlocks_injOn acc hP.2)
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
          SpecRel.issueRel_of_witR _ w hw) he)⟩
      · exact Or.inr ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
          SpecRel.spendRel_of_wit_gen _ _ rfl _ _ _ (fun i _ => by rw [Privacy.Ratatouille.fnOf_bOf])
            (fun i _ => by rw [Privacy.Ratatouille.fnOf_bOf]) (fun i _ => by rw [Privacy.Ratatouille.fnOf_bOf])
            w hw) he)⟩
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

end VoleMole.Theft
