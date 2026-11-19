import VoleMole.ROM.SimJoint
import VoleMole.ROM.SimSpec

/-!
# Simultaneous extraction across the two relations of a protocol, spec relations

`ROM/SimJoint.lean`'s joint bound (`prEvent_sim_joint_le`, `sim_joint_sum_le`) for the relation
pairs of the protocol theorems: Moussaka issuance and redemption, Ratatouille issuance and spend.
The two relations of a protocol have distinct DSTs of one length (`mous0i0`/`mous0r0`,
`rata0i0`/`rata0p0`), so no `H₂⁰` input decodes in both statement families (`muIn_ne_of_dst`,
`decOf_sep`). For `m_I` and `m_R` proofs of the two relations whose provers share one run
(`hsame`), `m = m_I + m_R`:

    Pr[some proof of either relation is accepted and its extraction fails]
      ≤ (q₂₁+m)·2⁻¹⁵⁰ + (q₂₂+m)·ε₂ + (q₂₃+m)·9·2⁻¹²⁸ + chainHitEpsCombSim q M m
        + stmtBindEpsSim q m + m·failEps q q_E,

`ε₂` the combined relation's `H₂²` charge (`ε_QS(4409) + 2⁻¹²⁸ + (n_G + 339)·2⁻⁴⁴⁸` for Moussaka
redemption, `ε_QS(12282) + 2⁻¹²⁸ + (n_G + 339)·2⁻⁴⁴⁸` for Ratatouille spend), which dominates the
issuance relation's (`ε_QS(4008)`, `ε_QS(3776)`). `ROM/SimSpec.lean`'s two bounds added pay
`q₂₁·2⁻¹⁵⁰ + q₂₂·(ε₂ + ε₂^I) + q₂₃·9·2⁻¹²⁸ + …` for the run, about twice this.

* `muIn_ne_of_dst`, `decOf_sep`: the separation of the two families.
* **`moussaka_sim_joint_spec`**, **`ratatouille_sim_joint_spec`**.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## Separated statement families -/

/-- **Statements with distinct DSTs of one length have distinct `H₂⁰` inputs.** -/
lemma muIn_ne_of_dst {st st' : Statement} (hs : st.dst.size = st'.dst.size)
    (hne : st.dst ≠ st'.dst) : muIn st ≠ muIn st' := by
  intro h
  apply hne
  have h1 := push_inj h
  set A := st.instEnc ByteArray.empty
  set B := st'.instEnc ByteArray.empty
  have hA : A.size = B.size := by
    have := congrArg ByteArray.size h1
    simp only [ByteArray.size_append] at this
    omega
  have e1 : (A ++ st.dst).extract A.size (A.size + st.dst.size) = st.dst :=
    ByteArray.extract_append_eq_right rfl rfl
  rw [h1, hA, hs, ByteArray.extract_append_eq_right rfl rfl] at e1
  exact e1.symm

/-- **Decoders of disjoint encodings are separated.** -/
lemma decOf_sep {κ κ' : Type} (f : κ → ByteArray) (f' : κ' → ByteArray)
    (h : ∀ s s', f s ≠ f' s') : ∀ x, (decOf f x).isSome → (decOf f' x).isSome → False := by
  classical
  intro x hx hx'
  unfold decOf at hx hx'
  split_ifs at hx hx' with h₁ h₂
  · obtain ⟨s, rfl⟩ := h₁
    obtain ⟨s', hs'⟩ := h₂
    exact h s s' hs'.symm
  all_goals simp at hx hx'

lemma ofReal_epsQS_mono {n n' : ℕ} (h1 : 1 ≤ n) (h : n ≤ n') :
    ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) ≤
      ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') := by
  refine ENNReal.ofReal_le_ofReal ?_
  unfold Seed.epsQS
  have : (1 : ℝ) ≤ n := by exact_mod_cast h1
  have : (n : ℝ) ≤ n' := by exact_mod_cast h
  gcongr

/-! ## Moussaka -/

variable {ιI' ιR' α ιI βI ιR βR : Type}

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Moussaka issuance and redemption, simultaneous extraction across both relations, spec
relations** (the hypotheses of `moussakaIssue_sim_spec` and `moussakaRedeem_sim_spec`, with the
two reference runs having one hash log): each query of the run is charged once, at the
redemption relation's charge. -/
theorem moussaka_sim_joint_spec (inst : ιI → ByteArray × ByteArray)
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
      (∃ j ∈ JI, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s => moussakaIssue (inst s).1 (inst s).2 labelRows) (PI j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (moussakaIssue (inst (stOut r)).1 (inst (stOut r)).2 labelRows)
          (fun _ w => Privacy.Moussaka.IssueRelW
            ⟨toL (inst (stOut r)).1, toL (inst (stOut r)).2⟩
            (SpecRel.issueWitOf (toL (inst (stOut r)).2) w)) r) ∨
      (∃ j ∈ JR, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s => moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows)
          (PR j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (moussakaRedeem (anc (stOut r)) (nf (stOut r)) (ctxIss (stOut r)) (ctxRed (stOut r))
            (cd (stOut r)) labelRows)
          (fun _ w => Privacy.Moussaka.RedeemRelW
            ⟨(anc (stOut r)).map UovPk.toSpec, toL (nf (stOut r)), toL (ctxIss (stOut r)),
              toL (ctxRed (stOut r)), toL (cd (stOut r))⟩
            (SpecRel.redeemWitOf (toL (nf (stOut r))) (toL (ctxIss (stOut r)))
              (toL (ctxRed (stOut r))) w)) r)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      (q .h21 + (JI.card + JR.card)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + (JI.card + JR.card)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + (JI.card + JR.card)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q Moussaka.M (JI.card + JR.card) +
        stmtBindEpsSim q (JI.card + JR.card) + JI.card * failEps q qE + JR.card * failEps q qE := by
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
  have h := prEvent_sim_joint_le CrtGen.tables liftInvOk_tables stI (decOf fun s => muIn (stI s))
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
    PI₀ PI PR₀ PR JI JR qE hqEI hqER q hqI hqR₀ hqR nG hnGI hnGR₀ hnGR hpreI hpreR hsame oa event
    fun E g hev => by
      rcases htr E g hev with ⟨j, hj, hacc, hnex⟩ | ⟨j, hj, hacc, hnex⟩
      · exact Or.inl ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
          SpecRel.issueRelW_of_wit _ _ (ht _) (hciI _) w hw) he)⟩
      · exact Or.inr ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
          SpecRel.redeemRelW_of_wit _ (hn64 _) _ _ _ _ (hnf _) (hci _) (hcr _) w hw) he)⟩
  refine h.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  have hkosI : epsKOS #chal3Blocks (Chain.kosL stI₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stI₀, moussakaIssue]) (by norm_num [stI₀, moussakaIssue])
  have hkosR : epsKOS #chal3Blocks (Chain.kosL stR₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stR₀, moussakaRedeem])
      (by norm_num [stR₀, moussakaRedeem])
  refine (sim_joint_sum_le stI₀ stR₀ _ _ _ _ 9 _ q JI JR _
    (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) + (2 ^ 128 : ℝ≥0∞)⁻¹) hkosI hkosR
    ((ofReal_epsQS_mono (by norm_num) (by norm_num)).trans le_self_add) le_rfl).trans ?_
  simp only [Nat.cast_ofNat, add_assoc, le_refl]

/-! ## Ratatouille -/

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Ratatouille issuance and spend, simultaneous extraction across both relations, spec
relations** (the hypotheses of `ratatouilleIssue_sim_spec` and `ratatouilleSpend_sim_spec`, with
the two reference runs having one hash log): each query of the run is charged once, at the spend
relation's charge. -/
theorem ratatouille_sim_joint_spec (inst : ιI → ByteArray × ℕ × ByteArray)
    (ht : ∀ s, (inst s).2.1 < 2 ^ 64) (labelRows : Bool)
    (hinjI : Function.Injective fun s =>
      (ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows).instEnc ByteArray.empty)
    (pk : ιR → UovPk) (nf : ιR → ByteArray) (d : ιR → ℕ)
    (hd : ∀ s, d s < 2 ^ 64) (cNext ctxIss : ιR → ByteArray)
    (hinjR : Function.Injective fun s =>
      (ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows).instEnc
        ByteArray.empty)
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
      (∃ j ∈ JI, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s => ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows) (PI j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (ratatouilleIssue (inst (stOut r)).1 (inst (stOut r)).2.1 (inst (stOut r)).2.2
            labelRows)
          (fun _ w => Spec.Ratatouille.IssueRel
            (SpecRel.issueInstOf (inst (stOut r)).1 (inst (stOut r)).2.1 (inst (stOut r)).2.2)
            (SpecRel.issueWitOfR w)) r) ∨
      (∃ j ∈ JR, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s => ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows) (PR j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (ratatouilleSpend (pk (stOut r)) (nf (stOut r)) (d (stOut r)) (cNext (stOut r))
            (ctxIss (stOut r)) labelRows)
          (fun _ w => Spec.Ratatouille.SpendRel
            (SpecRel.spendInstOf (pk (stOut r)) (nf (stOut r)) (d (stOut r)) (cNext (stOut r))
              (ctxIss (stOut r)))
            (SpecRel.spendWitOf w)) r)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      (q .h21 + (JI.card + JR.card)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + (JI.card + JR.card)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + (JI.card + JR.card)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q Ratatouille.uovM (JI.card + JR.card) +
        stmtBindEpsSim q (JI.card + JR.card) + JI.card * failEps q qE + JR.card * failEps q qE := by
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
  have h := prEvent_sim_joint_le CrtGen.tables liftInvOk_tables stI (decOf fun s => muIn (stI s))
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
    PI₀ PI PR₀ PR JI JR qE hqEI hqER q hqI hqR₀ hqR nG hnGI hnGR₀ hnGR hpreI hpreR hsame oa event
    fun E g hev => by
      rcases htr E g hev with ⟨j, hj, hacc, hnex⟩ | ⟨j, hj, hacc, hnex⟩
      · exact Or.inl ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
          SpecRel.issueRel_of_witB _ _ _ (ht _) w hw) he)⟩
      · exact Or.inr ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
          SpecRel.spendRel_of_witB _ _ _ (hd _) _ _ w hw) he)⟩
  refine h.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  have hkosI : epsKOS #chal3Blocks (Chain.kosL stI₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stI₀, ratatouilleIssue])
      (by norm_num [stI₀, ratatouilleIssue])
  have hkosR : epsKOS #chal3Blocks (Chain.kosL stR₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stR₀, ratatouilleSpend])
      (by norm_num [stR₀, ratatouilleSpend])
  refine (sim_joint_sum_le stI₀ stR₀ _ _ _ _ 9 _ q JI JR _
    (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) + (2 ^ 128 : ℝ≥0∞)⁻¹) hkosI hkosR
    ((ofReal_epsQS_mono (by norm_num) (by norm_num)).trans le_self_add) le_rfl).trans ?_
  simp only [Nat.cast_ofNat, add_assoc, le_refl]

end VoleMole.ROM.IC
