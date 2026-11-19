import VoleMole.Theft.PlainUnboundJoint
import VoleMole.ROM.MoussakaUnboundSimPerm

/-!
# `ROM/`'s simultaneous extraction for the Lean unbound Moussaka statements, permutation model

`moussakaUnbound_sim_joint_lean` (`Theft/PlainUnboundJoint.lean`) restated for the permutation
model (`moussakaUnbound_sim_joint_specP`, `ROM/MoussakaUnboundSimPerm.lean`): provers with forward
and inverse cipher queries, run through `normJ (mousUPI true) (mousUPR true) π`; the failure terms
are `failEpsP` and the total hash count in the `2⁻⁴⁴⁸` term is `n_G + 2·q₂₁`.

* **`moussakaUnbound_sim_joint_leanP`**.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft.MoussakaUnbound

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM VoleMole.ROM.IC
open VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Privacy.MoussakaUnbound (toBound stR_values csR)
open VoleMole.Theft.Moussaka (KeysBy anchors_keysBy)

variable {ιI' ιR' α βI βR : Type}

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Unbound issuance and redemption, simultaneous extraction, Lean statements,
permutation model** (`moussakaUnbound_sim_joint_specP` for `stI` on the well-formed unbound issuance instances and
`stR` on the well-formed unbound redemption instances with the keys `kt`): each query of the run
charged once, at the redemption relation's charge; the witnesses are in the spec relations. -/
theorem moussakaUnbound_sim_joint_leanP (kt : Bytes → UOVKey)
    (PI₀ : OracleComp specP (ByteArray × (IssWU × βI)))
    (PI : ιI' → OracleComp specP (ByteArray × (IssWU × βI)))
    (PR₀ : OracleComp specP (ByteArray × (RedKU kt × βR)))
    (PR : ιR' → OracleComp specP (ByteArray × (RedKU kt × βR)))
    (JI : Finset ιI') (JR : Finset ιR') (qE : ℕ)
    (hqEI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isRight = true) qE)
    (hqER : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hqI : ∀ j ∈ JI, IsKindQueryBoundP (PI j) q) (hqR₀ : IsKindQueryBoundP PR₀ q)
    (hqR : ∀ j ∈ JR, IsKindQueryBoundP (PR j) q) (nG : ℕ)
    (hnGI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isLeft = true) nG)
    (hnGR₀ : IsQueryBoundP PR₀ (fun t => t.isLeft = true) nG)
    (hnGR : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isLeft = true) nG)
    (hpreI : ∀ π : PTable, PrefixRuns π.fwd (normJ (mousUPI true) (mousUPR true) π PI₀)
      (fun j => normJ (mousUPI true) (mousUPR true) π (PI j)) JI)
    (hpreR : ∀ π : PTable, PrefixRuns π.fwd (normJ (mousUPI true) (mousUPR true) π PR₀)
      (fun j => normJ (mousUPI true) (mousUPR true) π (PR j)) JR)
    (hsame : ∀ (π : PTable) g,
      tableQueryLog (runE π.fwd (normJ (mousUPI true) (mousUPR true) π PI₀)) g =
        tableQueryLog (runE π.fwd (normJ (mousUPI true) (mousUPR true) π PR₀)) g)
    (oa : PTable → OracleComp spec α) (event : PTable → α → Prop)
    (htr : ∀ π g, event π (evalWithAnswerFn (QueryImpl.ofFn g) (oa π)) →
      (∃ j ∈ JI, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s : IssWU => Privacy.MoussakaUnbound.stI s.1)
          (normJ (mousUPI true) (mousUPR true) π (PI j)) π.fwd)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (Privacy.MoussakaUnbound.stI (stOut r).1)
          (fun _ w => IssueRel (stOut r).1 (SpecRel.uIssueWitOf (stOut r).1.ctxIss w)) r) ∨
      (∃ j ∈ JR, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s : RedKU kt => Privacy.MoussakaUnbound.stR s.1)
          (normJ (mousUPI true) (mousUPR true) π (PR j)) π.fwd)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (Privacy.MoussakaUnbound.stR (stOut r).1)
          (fun _ w => RedeemRel (stOut r).1
            (SpecRel.uRedeemWitOf (stOut r).1.ctxIss (stOut r).1.ctxRed w)) r)) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (oa π)).run' ∅}[event π r] ≤
      (q .h21 + (JI.card + JR.card)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + (JI.card + JR.card)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 * q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + (JI.card + JR.card)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q Arith.Moussaka.M (JI.card + JR.card) +
        stmtBindEpsSim q (JI.card + JR.card) + JI.card * failEpsP q qE +
        JR.card * failEpsP q qE := by
  classical
  set stIF : IssWU → Statement := fun s => Privacy.MoussakaUnbound.stI s.1
  set stRF : RedKU kt → Statement := fun s => Privacy.MoussakaUnbound.stR s.1
  set stI₀ := moussakaUnboundIssue ByteArray.empty ByteArray.empty true
  set stR₀ := moussakaUnboundRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty
    ByteArray.empty true
  have hsep := decOf_sep (fun s => muIn (stIF s)) (fun s => muIn (stRF s)) fun s s' =>
    muIn_stIU_ne_stRU s.1 s'.1
  have h := prEvent_sim_joint_leP CrtGen.tables liftInvOk_tables stIF
    (decOf fun s => muIn (stIF s))
    (fun s => moussakaUnboundIssueSys (toBA s.1.t) (toBA s.1.ctxIss)) stI₀ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun s => decOf_apply muIn_issWU_injective s)
    (fun s => MoussakaUnbound.uIssueSystem_length _ _)
    stRF (decOf fun s => muIn (stRF s)) (fun s l => leanURedeemSysL s.1 l)
    (fun s => leanURedeemWit s.1)
    Unbound.combDst stR₀ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun s => decOf_apply (muIn_redKU_injective kt) s)
    (fun s _ => MoussakaUnbound.uRedeemSystem_length _ _ _ _ _ _ _)
    (fun s w => prU_comb_bad_le _ _ w fun hW =>
      moussaka_unbound_redeem_comb_bad_gf128 _
        (by have h : (s.1).anchors.length ≤ 64 := s.2.1.2.1; simpa using h) _ _ _ w hW) hsep 9
    (fun s _ => moussakaUnboundIssueWit (fun k => fnOf (toBA s.1.t) k.val)
      (fnOf (toBA s.1.ctxIss)))
    (fun s c1 lb w => moussakaUnboundIssue_values (toBA s.1.t) (toBA s.1.ctxIss) true c1 lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        Unbound.issue_extract_chain (Unbound.moussakaUnboundIssue_stmt _ _ true) ch hv hA hAS
          hkos hP.1 hQS admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    (fun s _ => leanURedeemWit s.1)
    (fun s c1 v w => by
      rw [stR_values]; simp only [csR, ofArr_combinationOf_ba]; rfl)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc l hv A hA hAS hkos hQS hcb hP =>
        stRU_extract_chain s.1 ch l hv hA hAS hkos hP.1 hQS hcb admissible deltaBlocks
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
        obtain ⟨⟨t, ci⟩, hwf⟩ := s
        have ht : t.length = 45 := hwf.1
        have := SpecRel.uIssueRel_of_wit (toBA t) (toBA ci)
          (by rw [Privacy.size_toBA]; exact ht) w hw
        simpa only [SpecRel.toL_toBA] using this
      · refine Or.inr ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw => ?_) he)⟩
        generalize stOut _ = s at hw ⊢
        obtain ⟨⟨an, nf, ci, cr, cd⟩, hwf, _⟩ := s
        have hn : an.length ≤ 64 := hwf.2.1
        have hnf : nf.length = 24 := hwf.2.2.1
        have := SpecRel.uRedeemRel_of_wit_lean an hn (toBA nf) (toBA ci) (toBA cr) (toBA cd)
          (by rw [Privacy.size_toBA]; exact hnf) w hw
        simpa only [SpecRel.toL_toBA] using this
  rw [failEpsP_addH4] at h
  refine h.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  have hkosI : epsKOS #chal3Blocks (Chain.kosL stI₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _
      (Unbound.moussakaUnboundIssue_stmt ByteArray.empty ByteArray.empty true).witnessBytes_le
      (Unbound.moussakaUnboundIssue_stmt ByteArray.empty ByteArray.empty true).qsDegree_le
  have hkosR : epsKOS #chal3Blocks (Chain.kosL stR₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (Unbound.moussakaUnboundRedeem_stmt [] ByteArray.empty
      ByteArray.empty ByteArray.empty ByteArray.empty true).witnessBytes_le
      (Unbound.moussakaUnboundRedeem_stmt [] ByteArray.empty ByteArray.empty ByteArray.empty
        ByteArray.empty true).qsDegree_le
  refine (sim_joint_sum_le stI₀ stR₀ _ _ _ _ 9 _ (addH4 (addH4 q)) JI JR _
    (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) + (2 ^ 128 : ℝ≥0∞)⁻¹) hkosI hkosR
    ((ofReal_epsQS_mono (by norm_num) (by norm_num)).trans le_self_add) le_rfl).trans ?_
  simp only [addH4_of_ne _ (show Kind.h21 ≠ .h4 by decide),
    addH4_of_ne _ (show Kind.h22 ≠ .h4 by decide), addH4_of_ne _ (show Kind.h23 ≠ .h4 by decide),
    chainHitEpsCombSim_addH4, stmtBindEpsSim_addH4, two_mul, Nat.cast_ofNat, add_assoc, le_refl]

end VoleMole.Theft.MoussakaUnbound
