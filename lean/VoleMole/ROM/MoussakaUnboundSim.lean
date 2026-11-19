import VoleMole.ROM.MoussakaUnboundSpec
import VoleMole.ROM.SimJointSpec

/-!
# Simultaneous extraction for the unbound Moussaka relations

`ROM/SimExtract.lean` and `ROM/SimJoint.lean` for the unbound relations of
`security/moussaka-unbound.md` (late `ctx_red` binding): one opening enters `1 + N` proofs, the
unbound issuance and every redemption (UF6), and Thm U1 extracts from all of them. For proofs
whose provers share one run (`PrefixRuns`), at the statement-property families of
`Prob/MoussakaUnbound.lean` (`Unbound.IssueStmt`, `Unbound.RedeemStmt`) and the spec relations of
`EndToEnd/MoussakaUnboundSpec.lean`:

* `moussakaUnboundIssue_sim_spec`, `moussakaUnboundRedeem_sim_spec`: each relation alone, the run
  charged once per relation (`m` proofs):

      (q₂₁+m)·2⁻¹⁵⁰ + (q₂₂+m)·ε₂ + (q₂₃+m)·9·2⁻¹²⁸ + hits + stmtBindEpsSim q m + m·failEps q q_E,

  `ε₂ = ε_QS(3816)` (issuance), `ε_QS(7929) + 2⁻¹²⁸ + (n_G + 339)·2⁻⁴⁴⁸` (redemption);
* **`moussakaUnbound_sim_joint_spec`**: both relations together (`m = m_I + m_R`), each query of
  the run charged once, at the redemption relation's charge. The two families are separated by
  their DSTs (`mous1i0`, `mous1r0`).

The bound issuance relation (`mous0i0`, `ε_ext^{iss}` in Thm U1 when the Anchor also runs base
issuance) is a third family; its proofs are charged by `moussakaIssue_sim_spec`, or jointly with
base redemption by `moussaka_sim_joint_spec`, not jointly with the unbound pair.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

variable {ι' α ι β ιI' ιR' ιI βI ιR βR : Type}

/-- **Unbound issuance, simultaneous extraction, spec relation**: provers `P j` whose runs are
prefixes of `P₀`, a family of unbound issuance statements with `t` of 45 bytes and injective
instance encodings. -/
theorem moussakaUnboundIssue_sim_spec (stF : ι → Statement) (lr : Bool)
    (inst : ι → ByteArray × ByteArray)
    (hst : ∀ s, Unbound.IssueStmt (stF s) lr (inst s).1 (inst s).2)
    (ht : ∀ s, (inst s).1.size = 45)
    (hinj : Function.Injective fun s => (stF s).instEnc ByteArray.empty)
    (P₀ : OracleComp specIC (ByteArray × (ι × β))) (P : ι' → OracleComp specIC (ByteArray × (ι × β)))
    (J : Finset ι') (qE : ℕ) (hqE : ∀ j ∈ J, IsQueryBoundP (P j) (fun t => t.isRight = true) qE)
    (q : Kind → ℕ) (hq₀ : IsKindQueryBoundIC P₀ q) (hq : ∀ j ∈ J, IsKindQueryBoundIC (P j) q)
    (nG : ℕ) (hnG₀ : IsQueryBoundP P₀ (fun t => t.isLeft = true) nG)
    (hnG : ∀ j ∈ J, IsQueryBoundP (P j) (fun t => t.isLeft = true) nG)
    (hpre : ∀ E, PrefixRuns E P₀ P J) (oa : CTable → OracleComp spec α)
    (event : CTable → α → Prop)
    (htr : ∀ E g, event E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables stF (P j) E)
      r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r))
        (fun _ w => Spec.MoussakaUnbound.IssueRel
          ⟨toL (inst (stOut r)).1, toL (inst (stOut r)).2⟩
          (SpecRel.uIssueWitOf (toL (inst (stOut r)).2) w)) r) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      (q .h21 + J.card) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + J.card) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
        (q .h23 + J.card) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsSim q J.card +
        stmtBindEpsSim q J.card + J.card * failEps q qE := by
  classical
  set st₀ := moussakaUnboundIssue ByteArray.empty ByteArray.empty lr
  have hmu := muIn_injective (stF := stF) (dst := Unbound.issueDst) (fun s => (hst s).dst) hinj
  have h := prEvent_sim_le CrtGen.tables stF (decOf fun s => muIn (stF s))
    (fun s => moussakaUnboundIssueSys (inst s).1 (inst s).2) liftInvOk_tables st₀
    (fun s => (hst s).params) (fun s => (hst s).delayed) none (fun s => (hst s).comb)
    (fun s => decOf_apply hmu s) (fun s => MoussakaUnbound.uIssueSystem_length _ _) 9
    (fun s _ => moussakaUnboundIssueWit (fun k => fnOf (inst s).1 k.val) (fnOf (inst s).2))
    (fun s c1 lb w => (hst s).values c1 lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        Unbound.issue_extract_chain (hst s) ch hv hA hAS hkos hP.1 hQS admissible deltaBlocks
          deltaBlocks_injOn acc hP.2)
    P₀ P J qE hqE q hq₀ hq nG hnG₀ hnG hpre oa event fun E g hev => by
      obtain ⟨j, hj, hacc, hnex⟩ := htr E g hev
      exact ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun _ w hw =>
        SpecRel.uIssueRel_of_wit _ _ (ht _) w hw) he)⟩
  refine h.trans ?_
  rw [sim_sum_eq]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _
      (Unbound.moussakaUnboundIssue_stmt ByteArray.empty ByteArray.empty lr).witnessBytes_le
      (Unbound.moussakaUnboundIssue_stmt ByteArray.empty ByteArray.empty lr).qsDegree_le
  gcongr
  norm_num

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Unbound redemption, simultaneous extraction, spec relation** (at most 64 Anchors and `nf`
of 24 bytes per statement). -/
theorem moussakaUnboundRedeem_sim_spec (stF : ι → Statement) (lr : Bool)
    (anc : ι → List UovPk) (hn64 : ∀ s, (anc s).length ≤ 64) (nf ctxIss ctxRed cd : ι → ByteArray)
    (hst : ∀ s, Unbound.RedeemStmt (stF s) lr (anc s) (nf s) (ctxIss s) (ctxRed s))
    (hnf : ∀ s, (nf s).size = 24)
    (hinj : Function.Injective fun s => (stF s).instEnc ByteArray.empty)
    (P₀ : OracleComp specIC (ByteArray × (ι × β))) (P : ι' → OracleComp specIC (ByteArray × (ι × β)))
    (J : Finset ι') (qE : ℕ) (hqE : ∀ j ∈ J, IsQueryBoundP (P j) (fun t => t.isRight = true) qE)
    (q : Kind → ℕ) (hq₀ : IsKindQueryBoundIC P₀ q) (hq : ∀ j ∈ J, IsKindQueryBoundIC (P j) q)
    (nG : ℕ) (hnG₀ : IsQueryBoundP P₀ (fun t => t.isLeft = true) nG)
    (hnG : ∀ j ∈ J, IsQueryBoundP (P j) (fun t => t.isLeft = true) nG)
    (hpre : ∀ E, PrefixRuns E P₀ P J) (oa : CTable → OracleComp spec α)
    (event : CTable → α → Prop)
    (htr : ∀ E g, event E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables stF (P j) E)
      r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r))
        (fun _ w => Spec.MoussakaUnbound.RedeemRel
          ⟨(anc (stOut r)).map UovPk.toSpec, toL (nf (stOut r)), toL (ctxIss (stOut r)),
            toL (ctxRed (stOut r)), toL (cd (stOut r))⟩
          (SpecRel.uRedeemWitOf (toL (ctxIss (stOut r))) (toL (ctxRed (stOut r))) w)) r) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      (q .h21 + J.card) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + J.card) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + J.card) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsCombSim q Moussaka.M J.card +
        stmtBindEpsSim q J.card + J.card * failEps q qE := by
  classical
  set st₀ := moussakaUnboundRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty
    ByteArray.empty lr
  have hmu := muIn_injective (stF := stF) (dst := Unbound.redeemDst) (fun s => (hst s).dst) hinj
  have h := prEvent_sim_comb_le CrtGen.tables stF (decOf fun s => muIn (stF s))
    (fun s => moussakaUnboundRedeemSysL (anc s) (nf s) (ctxIss s) (ctxRed s))
    (fun s => moussakaUnboundRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    Unbound.combDst liftInvOk_tables st₀ (fun s => (hst s).params) (fun s => (hst s).delayed)
    (fun s => (hst s).comb) (fun s => decOf_apply hmu s)
    (fun s _ => MoussakaUnbound.uRedeemSystem_length _ _ _ _ _ _ _)
    (fun s w => prU_comb_bad_le _ _ w fun hW =>
      moussaka_unbound_redeem_comb_bad_gf128 _ (by simpa using hn64 s) _ _ _ w hW) 9
    (fun s _ => moussakaUnboundRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    (fun s c1 v w => by
      rw [(hst s).values]; simp only [moussakaUnboundRedeemSys, ofArr_combinationOf_ba])
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc l hv A hA hAS hkos hQS hcb hP =>
        Unbound.redeem_extract_chain (hst s) ch l hv hA hAS hkos hP.1 hQS hcb admissible
          deltaBlocks deltaBlocks_injOn acc hP.2)
    P₀ P J qE hqE q hq₀ hq nG hnG₀ hnG hpre oa event fun E g hev => by
      obtain ⟨j, hj, hacc, hnex⟩ := htr E g hev
      exact ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun _ w hw =>
        SpecRel.uRedeemRel_of_wit _ (hn64 _) _ _ _ _ (hnf _) w hw) he)⟩
  refine h.trans ?_
  rw [sim_comb_sum_eq]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (Unbound.moussakaUnboundRedeem_stmt [] ByteArray.empty
      ByteArray.empty ByteArray.empty ByteArray.empty lr).witnessBytes_le
      (Unbound.moussakaUnboundRedeem_stmt [] ByteArray.empty ByteArray.empty ByteArray.empty
        ByteArray.empty lr).qsDegree_le
  gcongr
  all_goals norm_num

/-- The unbound issuance and redemption statement families are separated by their DSTs. -/
lemma unbound_sep {stI : ιI → Statement} {stR : ιR → Statement}
    (hI : ∀ s, (stI s).dst = Unbound.issueDst) (hR : ∀ s, (stR s).dst = Unbound.redeemDst) :
    ∀ x, (decOf (fun s => muIn (stI s)) x).isSome → (decOf (fun s => muIn (stR s)) x).isSome →
      False :=
  decOf_sep _ _ fun s s' => muIn_ne_of_dst (by rw [hI, hR]; rfl) (by
    rw [hI, hR]
    intro h
    have := congrArg toL h
    simp only [Unbound.issueDst, Unbound.redeemDst, SpecRel.toL_toBA] at this
    revert this
    decide)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Unbound issuance and redemption, simultaneous extraction across both relations, spec
relations** (the hypotheses of `moussakaUnboundIssue_sim_spec` and
`moussakaUnboundRedeem_sim_spec`, with the two reference runs having one hash log): each query of
the run is charged once, at the redemption relation's charge. -/
theorem moussakaUnbound_sim_joint_spec (stI : ιI → Statement) (lr : Bool)
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
    (PI₀ : OracleComp specIC (ByteArray × (ιI × βI)))
    (PI : ιI' → OracleComp specIC (ByteArray × (ιI × βI)))
    (PR₀ : OracleComp specIC (ByteArray × (ιR × βR)))
    (PR : ιR' → OracleComp specIC (ByteArray × (ιR × βR)))
    (JI : Finset ιI') (JR : Finset ιR') (qE : ℕ)
    (hqEI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isRight = true) qE)
    (hqER : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hqI : ∀ j ∈ JI, IsKindQueryBoundIC (PI j) q) (hqR₀ : IsKindQueryBoundIC PR₀ q)
    (hqR : ∀ j ∈ JR, IsKindQueryBoundIC (PR j) q) (nG : ℕ)
    (hnGI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isLeft = true) nG)
    (hnGR₀ : IsQueryBoundP PR₀ (fun t => t.isLeft = true) nG)
    (hnGR : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isLeft = true) nG)
    (hpreI : ∀ E, PrefixRuns E PI₀ PI JI) (hpreR : ∀ E, PrefixRuns E PR₀ PR JR)
    (hsame : ∀ E g, tableQueryLog (runE E PI₀) g = tableQueryLog (runE E PR₀) g)
    (oa : CTable → OracleComp spec α) (event : CTable → α → Prop)
    (htr : ∀ E g, event E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) →
      (∃ j ∈ JI, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables stI (PI j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stI (stOut r))
          (fun _ w => Spec.MoussakaUnbound.IssueRel
            ⟨toL (inst (stOut r)).1, toL (inst (stOut r)).2⟩
            (SpecRel.uIssueWitOf (toL (inst (stOut r)).2) w)) r) ∨
      (∃ j ∈ JR, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables stR (PR j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stR (stOut r))
          (fun _ w => Spec.MoussakaUnbound.RedeemRel
            ⟨(anc (stOut r)).map UovPk.toSpec, toL (nf (stOut r)), toL (ctxIss (stOut r)),
              toL (ctxRed (stOut r)), toL (cd (stOut r))⟩
            (SpecRel.uRedeemWitOf (toL (ctxIss (stOut r))) (toL (ctxRed (stOut r))) w)) r)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      (q .h21 + (JI.card + JR.card)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + (JI.card + JR.card)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + (JI.card + JR.card)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q Moussaka.M (JI.card + JR.card) +
        stmtBindEpsSim q (JI.card + JR.card) + JI.card * failEps q qE + JR.card * failEps q qE := by
  classical
  set stI₀ := moussakaUnboundIssue ByteArray.empty ByteArray.empty lr
  set stR₀ := moussakaUnboundRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty
    ByteArray.empty lr
  have hmuI := muIn_injective (stF := stI) (dst := Unbound.issueDst) (fun s => (hstI s).dst) hinjI
  have hmuR := muIn_injective (stF := stR) (dst := Unbound.redeemDst) (fun s => (hstR s).dst)
    hinjR
  have h := prEvent_sim_joint_le CrtGen.tables liftInvOk_tables stI (decOf fun s => muIn (stI s))
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
    PI₀ PI PR₀ PR JI JR qE hqEI hqER q hqI hqR₀ hqR nG hnGI hnGR₀ hnGR hpreI hpreR hsame oa event
    fun E g hev => by
      rcases htr E g hev with ⟨j, hj, hacc, hnex⟩ | ⟨j, hj, hacc, hnex⟩
      · exact Or.inl ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun _ w hw =>
          SpecRel.uIssueRel_of_wit _ _ (ht _) w hw) he)⟩
      · exact Or.inr ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun _ w hw =>
          SpecRel.uRedeemRel_of_wit _ (hn64 _) _ _ _ _ (hnf _) w hw) he)⟩
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
  refine (sim_joint_sum_le stI₀ stR₀ _ _ _ _ 9 _ q JI JR _
    (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) + (2 ^ 128 : ℝ≥0∞)⁻¹) hkosI hkosR
    ((ofReal_epsQS_mono (by norm_num) (by norm_num)).trans le_self_add) le_rfl).trans ?_
  simp only [Nat.cast_ofNat, add_assoc, le_refl]

end VoleMole.ROM.IC
