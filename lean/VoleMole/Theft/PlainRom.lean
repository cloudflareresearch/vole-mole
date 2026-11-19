import VoleMole.Theft.PlainVerQ
import VoleMole.ROM.SimJointSpec

/-!
# `ROM/`'s simultaneous extraction for the Lean Ratatouille statements

`ratatouille_sim_joint_spec` (`ROM/SimJointSpec.lean`) bounds simultaneous extraction for the
verifier's byte-array statements `ratatouilleIssue`, `ratatouilleSpend` (a key with a digest and
an expanded map). The theft games use the Lean statements of `Privacy/RatatouilleLean.lean`: the
issuance statement `stI x` is `ratatouilleIssue` of the instance's bytes, but the spend statement
`stS x` hashes no key and evaluates the spec key `x.pk` (any map, not necessarily the expansion of
a byte string). Here the joint bound is restated for them (`docs/security/ratatouille.md` §5,
item 4 (c)):

* `stS_extract_chain`: `ratatouilleSpend_extract_chain` for `stS x` (the same system, the key's
  map `x.pk`).
* `SpendK pk₀`: the spend instances with the key `pk₀`; their statements are determined by their
  `H₂⁰` inputs (`muIn_stS_inj`), so they decode.
* **`ratatouille_sim_joint_lean`**: `ratatouille_sim_joint_spec` for `stI` and `stS` with one key,
  the witnesses in the spec relations `IssueRel x (issueWitOfR w)`, `SpendRel x (spendWitOf w)`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Verifier.Bridge

open VoleMole.Arith VoleMole.Verifier VoleMole.EndToEnd VoleMole.SeedExtraction

variable [VoleMole.Verifier.HasPrg]

open VoleMole.Privacy.Ratatouille in
/-- **Ratatouille spend for the Lean statement, from the executable verifier's chains**
(`ratatouilleSpend_extract_chain` with the spec key's map). -/
theorem stS_extract_chain {Ch : Type*} (x : Spec.Ratatouille.SpendInstance) (ch : Chain)
    (l : Fin Ratatouille.uovM → GF128)
    (hvals : ∀ y, ch.vals y = (Ratatouille.spendSystem beta GF256.toBits x.pk (fnOf (bOf x.nf))
      x.d.toNat (fnOf (bOf x.cNext)) (fnOf (bOf x.ctx)) l).values y) {A : Finset Blocks}
    (hA : ∀ Δ ∈ A, ch.OnChain (stS x) CrtGen.tables Δ) {S : Set Blocks} (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift CrtGen.tables) (ch.kosQ (stS x) CrtGen.tables)
      (ch.kosD (stS x) CrtGen.tables))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (stS x) CrtGen.tables j Δ =
        v + uStar j * lift CrtGen.tables Δ) →
      ¬(Ratatouille.spendSystem beta GF256.toBits x.pk (fnOf (bOf x.nf)) x.d.toNat
        (fnOf (bOf x.cNext)) (fnOf (bOf x.ctx)) l).Holds (wStar uStar (ch.dc (stS x))) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩ (valVec (Ratatouille.spendSystem beta GF256.toBits x.pk
          (fnOf (bOf x.nf)) x.d.toNat (fnOf (bOf x.cNext)) (fnOf (bOf x.ctx)) l)
          (wStar uStar (ch.dc (stS x)))) ≠ 0)
    (hcomb : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (stS x) CrtGen.tables j Δ =
        v + uStar j * lift CrtGen.tables Δ) →
      (Ratatouille.spendSystem beta GF256.toBits x.pk (fnOf (bOf x.nf)) x.d.toNat
        (fnOf (bOf x.cNext)) (fnOf (bOf x.ctx)) l).Holds (wStar uStar (ch.dc (stS x))) →
      ratatouilleSpendWit GF256.ofBits x.pk (fnOf (bOf x.nf)) x.d.toNat (fnOf (bOf x.cNext))
        (fnOf (bOf x.ctx)) (wStar uStar (ch.dc (stS x))))
    (Z : Finset Ch) (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ y ∈ Z, acc y → δ y ∈ A) :
    (∃ i ∈ known, ratatouilleSpendWit GF256.ofBits x.pk (fnOf (bOf x.nf)) x.d.toNat
        (fnOf (bOf x.cNext)) (fnOf (bOf x.ctx))
        (candidate (F := GF128) (ch.u (stS x)) (ch.dc (stS x)) i)) ∨
      #{y ∈ Z | acc y} ≤ 9 := by
  by_cases hA1 : A.card ≤ 1
  · exact Or.inr (few_of_card_le_one hA1 Z δ hδ acc hclaim1 (by norm_num))
  obtain ⟨uStar, R, hR, hK, hacc⟩ := chain_claim4 liftInvOk_tables (stS x) ch _ hvals
    (Degree.ratatouille_spend_deg _ _ _ _ _ _ _ _) hA hAS hkos hL2
  exact ratatouille_spend_extract_gf128 _ _ _ _ _ _ hK (ch.dc (stS x)) _ _ _ _ R hR hacc
    (hQS (by omega) uStar hK.consistent) (hcomb (by omega) uStar hK.consistent) Z δ hδ acc hclaim1

end VoleMole.Verifier.Bridge

namespace VoleMole.Theft

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM VoleMole.ROM.IC
open VoleMole.Privacy.Ratatouille (stI stS stS_values bOf)

/-- **The spend instances with the key `pk₀`.** -/
abbrev SpendK (pk₀ : Spec.Ratatouille.PublicKey) :=
  {x : Spec.Ratatouille.SpendInstance // x.pk = pk₀}

/-- The spend statement of an instance with the key `pk₀`. -/
abbrev stK (pk₀ : Spec.Ratatouille.PublicKey) (s : SpendK pk₀) : Statement := stS s.1

lemma muIn_stI_injective :
    Function.Injective fun x : Spec.Ratatouille.IssueInstance => muIn (stI x) :=
  fun _ _ h => Hit.Rata.muIn_stI_inj h

lemma muIn_stK_injective (pk₀ : Spec.Ratatouille.PublicKey) :
    Function.Injective fun x : SpendK pk₀ => muIn (stS x.1) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  have e := Hit.Rata.muIn_stS_inj h
  apply Subtype.ext
  show x = y
  calc x = { x with pk := y.pk } := by cases x; simp only at hx ⊢; rw [hx, hy]
    _ = y := e

variable {ιI' ιR' α βI βR : Type}

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Ratatouille issuance and spend, simultaneous extraction, Lean statements**
(`ratatouille_sim_joint_spec` for `stI` and for `stS` with the key `pk₀`): each query of the run
charged once, at the spend relation's charge; the witnesses are in the spec relations. -/
theorem ratatouille_sim_joint_lean (pk₀ : Spec.Ratatouille.PublicKey)
    (PI₀ : OracleComp specIC (ByteArray × (Spec.Ratatouille.IssueInstance × βI)))
    (PI : ιI' → OracleComp specIC (ByteArray × (Spec.Ratatouille.IssueInstance × βI)))
    (PR₀ : OracleComp specIC (ByteArray × (SpendK pk₀ × βR)))
    (PR : ιR' → OracleComp specIC (ByteArray × (SpendK pk₀ × βR)))
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
      (∃ j ∈ JI, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables stI (PI j) E);
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stI (stOut r))
          (fun _ w => Spec.Ratatouille.IssueRel (stOut r) (SpecRel.issueWitOfR w)) r) ∨
      (∃ j ∈ JR, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stK pk₀) (PR j) E);
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stS (stOut r).1)
          (fun _ w => Spec.Ratatouille.SpendRel (stOut r).1 (SpecRel.spendWitOf w)) r)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      (q .h21 + (JI.card + JR.card)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + (JI.card + JR.card)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + (JI.card + JR.card)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q Ratatouille.uovM (JI.card + JR.card) +
        stmtBindEpsSim q (JI.card + JR.card) + JI.card * failEps q qE + JR.card * failEps q qE := by
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
  have h := prEvent_sim_joint_le CrtGen.tables liftInvOk_tables stI (decOf fun s => muIn (stI s))
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
    PI₀ PI PR₀ PR JI JR qE hqEI hqER q hqI hqR₀ hqR nG hnGI hnGR₀ hnGR hpreI hpreR hsame oa event
    fun E g hev => by
      rcases htr E g hev with ⟨j, hj, hacc, hnex⟩ | ⟨j, hj, hacc, hnex⟩
      · exact Or.inl ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
          SpecRel.issueRel_of_witR _ w hw) he)⟩
      · exact Or.inr ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
          SpecRel.spendRel_of_wit_gen _ _ rfl _ _ _ (fun i _ => by rw [Privacy.Ratatouille.fnOf_bOf])
            (fun i _ => by rw [Privacy.Ratatouille.fnOf_bOf]) (fun i _ => by rw [Privacy.Ratatouille.fnOf_bOf])
            w hw) he)⟩
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

end VoleMole.Theft
