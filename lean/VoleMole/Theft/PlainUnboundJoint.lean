import VoleMole.Theft.PlainMousJoint
import VoleMole.Theft.MoussakaUnboundHit
import VoleMole.ROM.MoussakaUnboundSim

/-!
# `ROM/`'s simultaneous extraction for the Lean unbound Moussaka statements

`moussakaUnbound_sim_joint_spec` (`ROM/MoussakaUnboundSim.lean`) bounds simultaneous extraction for
statements with the properties `Unbound.IssueStmt`, `Unbound.RedeemStmt`, whose redemption Anchors
are byte keys (`UovPk`). The unbound game uses the Lean statements of
`Privacy/MoussakaUnboundLean.lean`: the issuance statement `stI x` is `moussakaUnboundIssue` of the
instance's bytes; the redemption statement `stR x` hashes the Anchors' digests (as a bound
redemption, `toBound`) and evaluates their spec maps (any maps, unrelated to the digests). Here the
joint bound is restated for them (`docs/security/moussaka-unbound.md` §5.3), as
`moussaka_sim_joint_lean` (`Theft/PlainMousJoint.lean`) does for bound Moussaka:

* `uRedeemRel_of_wit_lean`: `SpecRel.uRedeemRel_of_wit` for Anchors with any maps.
* `stRU_extract_chain`: `moussakaUnboundRedeem_extract_chain` for `stR x` (the system of the spec
  maps).
* **Statement families that decode.** `IssWU`: the well-formed unbound issuance instances
  (`WfIU`; `muIn_issWU_injective`). `RedKU kt`: the well-formed unbound redemption instances whose
  Anchor keys are the keys `kt d` of their digests (`KeysBy kt` of the bound instance `toBound x`;
  `muIn_redKU_injective`). As for bound Moussaka, the redemption statement hashes the Anchors'
  digests, not their maps, so the family must have one key per digest.
* **`moussakaUnbound_sim_joint_lean`**: `moussakaUnbound_sim_joint_spec` for `stI` on `IssWU` and
  `stR` on `RedKU kt`, with the witnesses in the spec relations `IssueRel`, `RedeemRel`.
* `verOk_stIUW`, `verOk_stRUW`: the well-formed Lean statements' inputs fit the tables with
  `L ≥ 9749` (`LminU`) and `M = Moussaka.M` (`VerOk`). `LminU` (the unbound redemption relation's
  `H₂¹` inputs) is above the `8193` bytes of the verifier's `H₁` leaf inputs, so unlike bound
  Moussaka the table length of the hit bound suffices.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

/-! ## The spec relation for Anchors with any maps -/

namespace VoleMole.EndToEnd.SpecRel

open VoleMole.Arith VoleMole.Verifier VoleMole.Privacy VoleMole.Spec

/-- **Unbound redemption, arithmetized → spec, for Anchors with any maps** (as
`uRedeemRel_of_wit`, whose Anchors are byte keys). -/
theorem uRedeemRel_of_wit_lean (anchors : List UOVKey) (hn : anchors.length ≤ 64)
    (nf ctxIss ctxRed cd : ByteArray) (hnf : nf.size = 24) (w : ℕ → GF128)
    (h : moussakaUnboundRedeemWit GF256.ofBits (anchors.map (·.map)) (fnOf nf) (fnOf ctxIss)
      (fnOf ctxRed) w) :
    Spec.MoussakaUnbound.RedeemRel ⟨anchors, toL nf, toL ctxIss, toL ctxRed, toL cd⟩
      (uRedeemWitOf (toL ctxIss) (toL ctxRed) w) := by
  obtain ⟨wb, hb, u₀, hsel, ⟨hu, hpk⟩, hnfd⟩ := h
  have hu' : u₀ < anchors.length := by simpa using hu
  have hs : uSelOf (bitsOf w) = u₀ := uSelOf_eq (by omega) fun u hu64 => by
    rw [bitsOf_eq hb (by simp only [MoussakaUnbound.uSelBit, MoussakaUnbound.uRedeemOffB,
      MoussakaUnbound.uRedeemWitnessBits]; omega)]
    exact hsel u hu64
  rw [uRedeemWitOf, hs, bytesOf_bitsOf hb (by decide), bytesOf_bitsOf hb (by decide),
    bytesOf_bitsOf hb (by decide)]
  have hK : ∀ i < 16, MoussakaUnbound.uRedeemK wb i =
      Spec.MoussakaUnbound.fn (bytesOf wb 16 16) i := fun i hi => (fn_bytesOf wb 16 hi).symm
  have hR : ∀ i < 16, MoussakaUnbound.uRedeemR wb i =
      Spec.MoussakaUnbound.fn (bytesOf wb 0 16) i := fun i hi => (fn_bytesOf wb 0 hi).symm
  refine ⟨_, _, _, u₀, anchors[u₀]'hu', length_bytesOf _ _ _, length_bytesOf _ _ _,
    length_bytesOf _ _ _, List.getElem?_eq_getElem _, rfl, ?_, ?_⟩
  · refine list_ext_getD (by rw [Spec.length_eval, Spec.MoussakaUnbound.length_ucom])
      fun k hk' => ?_
    rw [Spec.length_eval] at hk'
    rw [getD_eval_bytesOf _ _ _ hk', Spec.MoussakaUnbound.ucom_getD _ _ _ ⟨k, hk'⟩]
    have e := congrArg GF256.val (congrFun hpk ⟨k, hk'⟩)
    have hsd : MoussakaUnbound.uRedeemS GF256.ofBits wb =
        fun i => ⟨Keccak.witByte wb (MoussakaUnbound.uRedeemOffS + i)⟩ :=
      funext (decode_gf256 wb MoussakaUnbound.uRedeemOffS)
    simp only [hsd, MoussakaUnbound.uRedeemTarget, Moussaka.toK_gf256, List.getElem_map] at e
    exact e.trans (congrFun (ucom_congr hK (fun i _ => fnOf_eq_getD ctxIss i) hR) _)
  · refine list_ext_getD (by rw [length_toL, hnf, Spec.MoussakaUnbound.length_derive])
      fun j hj => ?_
    rw [length_toL, hnf] at hj
    rw [← fnOf_eq_getD, Spec.MoussakaUnbound.derive_getD _ _ ⟨j, hj⟩, hnfd ⟨j, hj⟩]
    exact congrFun (derive_congr hK (fun i _ => fnOf_eq_getD ctxRed i)) _

end VoleMole.EndToEnd.SpecRel

/-! ## Extraction from the chains of the Lean unbound redemption statement -/

namespace VoleMole.Verifier.Bridge

open VoleMole.Arith VoleMole.Verifier VoleMole.EndToEnd VoleMole.SeedExtraction

/-- **The Lean unbound redemption statement's system** at a combination vector `l`: the spec maps
of the Anchors. -/
def leanURedeemSysL (x : Spec.MoussakaUnbound.RedeemInstance) (l : Fin Moussaka.M → GF128) :
    System GF128 :=
  MoussakaUnbound.uRedeemSystem beta GF256.toBits (x.anchors.map (·.map)) (fnOf (toBA x.nf))
    (fnOf (toBA x.ctxIss)) (fnOf (toBA x.ctxRed)) l

/-- **The Lean unbound redemption statement's witness predicate** (the spec maps of the
Anchors). -/
def leanURedeemWit (x : Spec.MoussakaUnbound.RedeemInstance) : (ℕ → GF128) → Prop :=
  moussakaUnboundRedeemWit GF256.ofBits (x.anchors.map (·.map)) (fnOf (toBA x.nf))
    (fnOf (toBA x.ctxIss)) (fnOf (toBA x.ctxRed))

variable [VoleMole.Verifier.HasPrg]

open VoleMole.Privacy.MoussakaUnbound in
/-- **Unbound redemption for the Lean statement, from the executable verifier's chains**
(`moussakaUnboundRedeem_extract_chain` with the Anchors' spec maps). -/
theorem stRU_extract_chain {Ch : Type*} (x : Spec.MoussakaUnbound.RedeemInstance) (ch : Chain)
    (l : Fin Moussaka.M → GF128) (hvals : ∀ y, ch.vals y = (leanURedeemSysL x l).values y)
    {A : Finset Blocks} (hA : ∀ Δ ∈ A, ch.OnChain (stR x) CrtGen.tables Δ) {S : Set Blocks}
    (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift CrtGen.tables) (ch.kosQ (stR x) CrtGen.tables)
      (ch.kosD (stR x) CrtGen.tables))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (stR x) CrtGen.tables j Δ =
        v + uStar j * lift CrtGen.tables Δ) →
      ¬(leanURedeemSysL x l).Holds (wStar uStar (ch.dc (stR x))) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩ (valVec (leanURedeemSysL x l) (wStar uStar (ch.dc (stR x)))) ≠ 0)
    (hcomb : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (stR x) CrtGen.tables j Δ =
        v + uStar j * lift CrtGen.tables Δ) →
      (leanURedeemSysL x l).Holds (wStar uStar (ch.dc (stR x))) →
      leanURedeemWit x (wStar uStar (ch.dc (stR x))))
    (Z : Finset Ch) (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ y ∈ Z, acc y → δ y ∈ A) :
    (∃ i ∈ known, leanURedeemWit x (candidate (F := GF128) (ch.u (stR x)) (ch.dc (stR x)) i)) ∨
      #{y ∈ Z | acc y} ≤ 9 := by
  by_cases hA1 : A.card ≤ 1
  · exact Or.inr (few_of_card_le_one hA1 Z δ hδ acc hclaim1 (by norm_num))
  obtain ⟨uStar, R, hR, hK, hacc⟩ := chain_claim4 liftInvOk_tables (stR x) ch _ hvals
    (Degree.moussaka_unbound_redeem_deg _ _ _ _ _ _ _) hA hAS hkos hL2
  exact moussaka_unbound_redeem_extract beta GF256.toBits GF256.ofBits _ _ _ _ _ hK
    (ch.dc (stR x)) _ _ _ _ R hR hacc (hQS (by omega) uStar hK.consistent)
    (hcomb (by omega) uStar hK.consistent) Z δ hδ acc hclaim1

end VoleMole.Verifier.Bridge

/-! ## Statement families that decode -/

namespace VoleMole.Theft.MoussakaUnbound

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM VoleMole.ROM.IC
open VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Privacy.MoussakaUnbound (toBound stR_values csR)
open VoleMole.Theft.Moussaka (KeysBy anchors_keysBy)

/-- **The well-formed unbound issuance instances.** -/
abbrev IssWU := {x : IssueInstance // WfIU x}

/-- **The well-formed unbound redemption instances whose Anchor keys are those of `kt`**
(`KeysBy kt` of the bound instance with the same fields). -/
abbrev RedKU (kt : Bytes → UOVKey) := {x : RedeemInstance // WfRU x ∧ KeysBy kt (toBound x)}

lemma muIn_issWU_injective :
    Function.Injective fun x : IssWU => muIn (Privacy.MoussakaUnbound.stI x.1) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  exact Subtype.ext (muIn_stIU_inj hx hy h)

lemma muIn_redKU_injective (kt : Bytes → UOVKey) :
    Function.Injective fun x : RedKU kt => muIn (Privacy.MoussakaUnbound.stR x.1) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  have e := muIn_stRU_inj hx.1 hy.1 h
  simp only [hashedRU, Hit.Mous.hashedR, toBound, Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5⟩ := e
  apply Subtype.ext
  show x = y
  have ha : x.anchors = y.anchors := by
    rw [show x.anchors = (toBound x).anchors from rfl, anchors_keysBy hx.2,
      show y.anchors = (toBound y).anchors from rfl, anchors_keysBy hy.2]
    exact congrArg (List.map kt) e1
  cases x
  cases y
  simp only at ha e2 e3 e4 e5
  rw [ha, e2, e3, e4, e5]

lemma length_t_of_wfIU {x : IssueInstance} (h : WfIU x) : x.t.length = 45 := h.1

/-! ## The joint bound -/

variable {ιI' ιR' α βI βR : Type}

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Unbound issuance and redemption, simultaneous extraction, Lean statements**
(`moussakaUnbound_sim_joint_spec` for `stI` on the well-formed unbound issuance instances and
`stR` on the well-formed unbound redemption instances with the keys `kt`): each query of the run
charged once, at the redemption relation's charge; the witnesses are in the spec relations. -/
theorem moussakaUnbound_sim_joint_lean (kt : Bytes → UOVKey)
    (PI₀ : OracleComp specIC (ByteArray × (IssWU × βI)))
    (PI : ιI' → OracleComp specIC (ByteArray × (IssWU × βI)))
    (PR₀ : OracleComp specIC (ByteArray × (RedKU kt × βR)))
    (PR : ιR' → OracleComp specIC (ByteArray × (RedKU kt × βR)))
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
          (fun s : IssWU => Privacy.MoussakaUnbound.stI s.1) (PI j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (Privacy.MoussakaUnbound.stI (stOut r).1)
          (fun _ w => IssueRel (stOut r).1 (SpecRel.uIssueWitOf (stOut r).1.ctxIss w)) r) ∨
      (∃ j ∈ JR, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s : RedKU kt => Privacy.MoussakaUnbound.stR s.1) (PR j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (Privacy.MoussakaUnbound.stR (stOut r).1)
          (fun _ w => RedeemRel (stOut r).1
            (SpecRel.uRedeemWitOf (stOut r).1.ctxIss (stOut r).1.ctxRed w)) r)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      (q .h21 + (JI.card + JR.card)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + (JI.card + JR.card)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + (JI.card + JR.card)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q Arith.Moussaka.M (JI.card + JR.card) +
        stmtBindEpsSim q (JI.card + JR.card) + JI.card * failEps q qE + JR.card * failEps q qE := by
  classical
  set stIF : IssWU → Statement := fun s => Privacy.MoussakaUnbound.stI s.1
  set stRF : RedKU kt → Statement := fun s => Privacy.MoussakaUnbound.stR s.1
  set stI₀ := moussakaUnboundIssue ByteArray.empty ByteArray.empty true
  set stR₀ := moussakaUnboundRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty
    ByteArray.empty true
  have hsep := decOf_sep (fun s => muIn (stIF s)) (fun s => muIn (stRF s)) fun s s' =>
    muIn_stIU_ne_stRU s.1 s'.1
  have h := prEvent_sim_joint_le CrtGen.tables liftInvOk_tables stIF
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
    PI₀ PI PR₀ PR JI JR qE hqEI hqER q hqI hqR₀ hqR nG hnGI hnGR₀ hnGR hpreI hpreR hsame oa event
    fun E g hev => by
      rcases htr E g hev with ⟨j, hj, hacc, hnex⟩ | ⟨j, hj, hacc, hnex⟩
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
  refine (sim_joint_sum_le stI₀ stR₀ _ _ _ _ 9 _ q JI JR _
    (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) + (2 ^ 128 : ℝ≥0∞)⁻¹) hkosI hkosR
    ((ofReal_epsQS_mono (by norm_num) (by norm_num)).trans le_self_add) le_rfl).trans ?_
  simp only [Nat.cast_ofNat, add_assoc, le_refl]

/-! ## The inputs fit the tables -/

section VerOk

variable {L : ℕ}

lemma lrom_le_lminU : Theft.Moussaka.Lrom ≤ LminU := by decide

set_option maxRecDepth 100000 in
/-- **The well-formed Lean unbound issuance statement's inputs fit** the tables with
`L ≥ 9749`. -/
lemma verOk_stIUW (hL : LminU ≤ L) {M : ℕ} (x : IssueInstance) (hx : WfIU x) :
    VerOk Privacy.Moussaka.pI L M (Privacy.MoussakaUnbound.stI x) := by
  refine ⟨rfl, by simp [Privacy.MoussakaUnbound.stI, moussakaUnboundIssue, preLen], ?_,
    le_trans ?_ hL, le_trans ?_ hL, le_trans (by decide) hL, ?_⟩
  · rw [size_muIn_stIU hx]; exact le_trans (by decide) hL
  · show 64 + 16 * Privacy.MoussakaUnbound.pI.correctionBytes +
      Privacy.MoussakaUnbound.pI.nMask * Privacy.MoussakaUnbound.pI.nMultBytes + 16 + 0 + 1 ≤
        LminU
    decide
  · show 264 + 0 + Privacy.MoussakaUnbound.pI.witnessBytes + 1 ≤ LminU
    decide
  · intro M' dst h
    exact absurd h (by simp [Privacy.MoussakaUnbound.stI, moussakaUnboundIssue])

set_option maxRecDepth 100000 in
/-- **The well-formed Lean unbound redemption statement's inputs fit** the tables with
`L ≥ 9749` and the combination of `Moussaka.M` equations. -/
lemma verOk_stRUW (hL : LminU ≤ L) (x : RedeemInstance) (hx : WfRU x) :
    VerOk Privacy.Moussaka.pI L Arith.Moussaka.M (Privacy.MoussakaUnbound.stR x) := by
  refine ⟨rfl, by simp [Privacy.MoussakaUnbound.stR, preLen], ?_, le_trans ?_ hL,
    le_trans ?_ hL, le_trans (by decide) hL, ?_⟩
  · exact (size_muIn_stRU_le hx).trans (le_trans (by decide) hL)
  · show 64 + 16 * Privacy.MoussakaUnbound.pR.correctionBytes +
      Privacy.MoussakaUnbound.pR.nMask * Privacy.MoussakaUnbound.pR.nMultBytes + 16 + 0 + 1 ≤
        LminU
    decide
  · show 264 + 0 + Privacy.MoussakaUnbound.pR.witnessBytes + 1 ≤ LminU
    decide
  · intro M' dst h
    simp only [Privacy.MoussakaUnbound.stR, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, le_trans ?_ hL⟩
    decide

end VerOk

end VoleMole.Theft.MoussakaUnbound
