import VoleMole.Theft.PlainMousJoint
import VoleMole.ROM.SimPermJointSpec

/-!
# `ROM/`'s simultaneous extraction for the Lean Moussaka statements, permutation model

`moussaka_sim_joint_lean` (`Theft/PlainMousJoint.lean`) restated for the permutation model
(`moussaka_sim_joint_specP`, `ROM/SimPermJointSpec.lean`): provers with forward and inverse cipher
queries (`specP`), run through the joint normalization `normJ (mousPI true) (mousPR true) π`; the
failure terms are `failEpsP` and the total hash count in the `2⁻⁴⁴⁸` term is `n_G + 2·q₂₁`.

* **`moussaka_sim_joint_leanP`**.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft.Moussaka

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM VoleMole.ROM.IC
open VoleMole.Spec VoleMole.Spec.Moussaka
open VoleMole.Privacy.Moussaka (stR_values csR)

variable {ιI' ιR' α βI βR : Type}

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Moussaka issuance and redemption, simultaneous extraction, Lean statements,
permutation model** (`moussaka_sim_joint_specP` for `stI` on the well-formed issuance instances and `stR` on the
well-formed redemption instances with the keys `kt`): each query of the run charged once, at the
redemption relation's charge; the witnesses are in the spec relations. -/
theorem moussaka_sim_joint_leanP (kt : Bytes → UOVKey)
    (PI₀ : OracleComp specP (ByteArray × (IssW × βI)))
    (PI : ιI' → OracleComp specP (ByteArray × (IssW × βI)))
    (PR₀ : OracleComp specP (ByteArray × (RedK kt × βR)))
    (PR : ιR' → OracleComp specP (ByteArray × (RedK kt × βR)))
    (JI : Finset ιI') (JR : Finset ιR') (qE : ℕ)
    (hqEI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isRight = true) qE)
    (hqER : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hqI : ∀ j ∈ JI, IsKindQueryBoundP (PI j) q) (hqR₀ : IsKindQueryBoundP PR₀ q)
    (hqR : ∀ j ∈ JR, IsKindQueryBoundP (PR j) q) (nG : ℕ)
    (hnGI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isLeft = true) nG)
    (hnGR₀ : IsQueryBoundP PR₀ (fun t => t.isLeft = true) nG)
    (hnGR : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isLeft = true) nG)
    (hpreI : ∀ π : PTable, PrefixRuns π.fwd (normJ (mousPI true) (mousPR true) π PI₀)
      (fun j => normJ (mousPI true) (mousPR true) π (PI j)) JI)
    (hpreR : ∀ π : PTable, PrefixRuns π.fwd (normJ (mousPI true) (mousPR true) π PR₀)
      (fun j => normJ (mousPI true) (mousPR true) π (PR j)) JR)
    (hsame : ∀ (π : PTable) g,
      tableQueryLog (runE π.fwd (normJ (mousPI true) (mousPR true) π PI₀)) g =
        tableQueryLog (runE π.fwd (normJ (mousPI true) (mousPR true) π PR₀)) g)
    (oa : PTable → OracleComp spec α) (event : PTable → α → Prop)
    (htr : ∀ π g, event π (evalWithAnswerFn (QueryImpl.ofFn g) (oa π)) →
      (∃ j ∈ JI, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s : IssW => Privacy.Moussaka.stI s.1)
          (normJ (mousPI true) (mousPR true) π (PI j)) π.fwd)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (Privacy.Moussaka.stI (stOut r).1)
          (fun _ w => Privacy.Moussaka.IssueRelW (stOut r).1
            (SpecRel.issueWitOf (stOut r).1.ctxIss w)) r) ∨
      (∃ j ∈ JR, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s : RedK kt => Privacy.Moussaka.stR s.1)
          (normJ (mousPI true) (mousPR true) π (PR j)) π.fwd)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (Privacy.Moussaka.stR (stOut r).1)
          (fun _ w => Privacy.Moussaka.RedeemRelW (stOut r).1
            (SpecRel.redeemWitOf (stOut r).1.nf (stOut r).1.ctxIss (stOut r).1.ctxRed w)) r)) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (oa π)).run' ∅}[event π r] ≤
      (q .h21 + (JI.card + JR.card)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + (JI.card + JR.card)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 * q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + (JI.card + JR.card)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q Arith.Moussaka.M (JI.card + JR.card) +
        stmtBindEpsSim q (JI.card + JR.card) + JI.card * failEpsP q qE +
        JR.card * failEpsP q qE := by
  classical
  set stIF : IssW → Statement := fun s => Privacy.Moussaka.stI s.1
  set stRF : RedK kt → Statement := fun s => Privacy.Moussaka.stR s.1
  set stI₀ := moussakaIssue ByteArray.empty ByteArray.empty true
  set stR₀ := moussakaRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty ByteArray.empty true
  have hsep := decOf_sep (fun s => muIn (stIF s)) (fun s => muIn (stRF s)) fun s s' =>
    Hit.Mous.muIn_stI_ne_stR s.1 s'.1
  have h := prEvent_sim_joint_leP CrtGen.tables liftInvOk_tables stIF (decOf fun s => muIn (stIF s))
    (fun s => moussakaIssueSys (toBA s.1.t) (toBA s.1.ctxIss)) stI₀ (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun s => decOf_apply muIn_issW_injective s)
    (fun s => Moussaka.issueSystem_length _ _)
    stRF (decOf fun s => muIn (stRF s)) (fun s l => leanRedeemSysL s.1 l)
    (fun s => leanRedeemWit s.1)
    (toBA (VoleMole.Spec.makeDst "mous" 0 'l' '0')) stR₀ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun s => decOf_apply (muIn_redK_injective kt) s)
    (fun s _ => Moussaka.redeemSystem_length _ _ _ _ _ _ _)
    (fun s w => prU_comb_bad_le _ _ w fun hW =>
      moussaka_redeem_comb_bad_gf128 _ (by simpa using s.2.1.2.1) _ _ _ w hW) hsep 9
    (fun s _ => moussakaIssueWit (fun k => fnOf (toBA s.1.t) k.val) (fnOf (toBA s.1.ctxIss)))
    (fun s c1 lb w => moussakaIssue_values (toBA s.1.t) (toBA s.1.ctxIss) true c1 lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        moussakaIssue_extract_chain (toBA s.1.t) (toBA s.1.ctxIss) true ch hv hA hAS
          hkos hP.1 hQS admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    (fun s _ => leanRedeemWit s.1)
    (fun s c1 v w => by
      rw [stR_values]; simp only [csR, ofArr_combinationOf_ba]; rfl)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc l hv A hA hAS hkos hQS hcb hP =>
        stR_extract_chain s.1 ch l hv hA hAS hkos hP.1 hQS hcb admissible deltaBlocks
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
      · refine Or.inl ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw => ?_) he)⟩
        generalize stOut _ = s at hw ⊢
        obtain ⟨⟨t, ci⟩, ht, hci⟩ := s
        have := SpecRel.issueRelW_of_wit (toBA t) (toBA ci)
          (by rw [Privacy.size_toBA]; exact ht) (by rw [Privacy.size_toBA]; exact hci) w hw
        simpa only [SpecRel.toL_toBA] using this
      · refine Or.inr ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw => ?_) he)⟩
        generalize stOut _ = s at hw ⊢
        obtain ⟨⟨an, nf, ci, cr, cd⟩, ⟨_, hn, hnf, hci, hcr, _⟩, _⟩ := s
        have := SpecRel.redeemRelW_of_wit_lean an hn (toBA nf) (toBA ci) (toBA cr) (toBA cd)
          (by rw [Privacy.size_toBA]; exact hnf) (by rw [Privacy.size_toBA]; exact hci)
          (by rw [Privacy.size_toBA]; exact hcr) w hw
        simpa only [SpecRel.toL_toBA] using this
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

end VoleMole.Theft.Moussaka
