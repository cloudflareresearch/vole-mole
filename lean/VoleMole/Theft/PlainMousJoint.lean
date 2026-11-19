import VoleMole.Theft.PlainRom
import VoleMole.Theft.PlainMous

/-!
# `ROM/`'s simultaneous extraction for the Lean Moussaka statements

`moussaka_sim_joint_spec` (`ROM/SimJointSpec.lean`) bounds simultaneous extraction for the
verifier's byte-array statements `moussakaIssue`, `moussakaRedeem` (Anchors with a digest and an
expanded key). The redirect game uses the Lean statements of `Privacy/MoussakaLean.lean`: the
issuance statement `stI x` is `moussakaIssue` of the instance's bytes; the redemption statement
`stR x` hashes the Anchors' digests and evaluates their spec maps (any maps, unrelated to the
digests). Here the joint bound is restated for them (`docs/security/moussaka.md` §5.3), as
`ratatouille_sim_joint_lean` (`Theft/PlainRom.lean`) does for Ratatouille:

* `redeemRelW_of_wit_lean`: `SpecRel.redeemRelW_of_wit` for Anchors with any maps.
* `stR_extract_chain`: `moussakaRedeem_extract_chain` for `stR x` (the system of the spec maps).
* **Statement families that decode.** `ROM/`'s argument reads a statement back from its `H₂⁰`
  input, so each family must be determined by it. `IssW`: the well-formed issuance instances
  (`WfI`; `muIn_issW_injective`). A redemption statement hashes the Anchors' digests, not their
  maps, so two redemption instances with the same digests and other maps have the same `H₂⁰`
  input. `RedK kt`: the well-formed redemption instances whose Anchor keys are the keys `kt d` of
  their digests (`KeysBy kt`; `muIn_redK_injective`). `kt` is a fixed assignment of keys to
  digests; in C++ a digest is SHAKE256 of the key, so an adversary that uses two keys with one
  digest has found a collision.
* **`moussaka_sim_joint_lean`**: `moussaka_sim_joint_spec` for `stI` on `IssW` and `stR` on
  `RedK kt`, with the witnesses in the spec relations `IssueRelW`, `RedeemRelW`.
* `verOk_stIW`, `verOk_stRW`: the well-formed Lean statements' inputs fit the tables with
  `L ≥ 8193` and `M = Moussaka.M` (`VerOk`). The bound is `8193`, not `Hit.Mous.Lmin = 6293`: the
  verifier's `H₁` leaf inputs (`2⁸·32 + 1` bytes) must be table points too.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

/-! ## The spec relation for Anchors with any maps -/

namespace VoleMole.EndToEnd.SpecRel

open VoleMole.Arith VoleMole.Verifier VoleMole.Privacy VoleMole.Spec VoleMole.Spec.Moussaka

/-- **Moussaka redemption, arithmetized → spec, for Anchors with any maps** (as
`redeemRelW_of_wit`, whose Anchors are expanded byte keys). -/
theorem redeemRelW_of_wit_lean (anchors : List UOVKey) (hn : anchors.length ≤ 64)
    (nf ctxIss ctxRed cd : ByteArray) (hnf : nf.size = 24) (hci : ctxIss.size = 16)
    (hcr : ctxRed.size = 16) (w : ℕ → GF128)
    (h : moussakaRedeemWit GF256.ofBits (anchors.map (·.map)) (fnOf nf) (fnOf ctxIss)
      (fnOf ctxRed) w) :
    Moussaka.RedeemRelW ⟨anchors, toL nf, toL ctxIss, toL ctxRed, toL cd⟩
      (redeemWitOf (toL nf) (toL ctxIss) (toL ctxRed) w) := by
  obtain ⟨wb, hb, u₀, hsel, hrel⟩ := h
  obtain ⟨hu, hk⟩ := (Arith.Moussaka.redeemRel_gf256_iff _ _ _ _ _ wb u₀).1 hrel
  have hu' : u₀ < anchors.length := by simpa using hu
  have hnf' : (toL nf).length = 24 := by rw [length_toL, hnf]
  have hci' : (toL ctxIss).length = 16 := by rw [length_toL, hci]
  have hcr' : (toL ctxRed).length = 16 := by rw [length_toL, hcr]
  have hs : selOf (bitsOf w) = u₀ := selOf_eq (by omega) fun u hu64 => by
    rw [bitsOf_eq hb (by simp only [Arith.Moussaka.selBit, Arith.Moussaka.redeemOffB,
      Arith.Moussaka.redeemWitnessBits]; omega)]
    exact hsel u hu64
  rw [redeemWitOf, hs, bytesOf_bitsOf hb (by decide), bytesOf_bitsOf hb (by decide)]
  refine ⟨⟨_, _, u₀, anchors[u₀]'hu', length_bytesOf _ _ _,
    length_bytesOf _ _ _, List.getElem?_eq_getElem _, rfl, ?_⟩, by simpa using hn, hnf', hci', hcr'⟩
  have hE : Arith.Moussaka.encodeComState (fnOf nf) (fnOf ctxIss) (fnOf ctxRed)
      (Arith.Moussaka.redeemR wb) =
      stateOfBytes (comState (toL nf) (toL ctxIss) (toL ctxRed) (bytesOf wb 0 16)) :=
    VoleMole.Privacy.Moussaka.encodeComState_eq _ _ _ _ hnf' hci' hcr' (length_bytesOf _ _ _)
      _ _ _ _ (fun i _ => fnOf_eq_getD _ _) (fun i _ => fnOf_eq_getD _ _)
      (fun i _ => fnOf_eq_getD _ _) (fun i hi => by rw [getD_bytesOf _ _ hi]; rfl)
  refine list_ext_getD (by rw [length_eval, length_com]) fun k hk' => ?_
  rw [length_eval] at hk'
  rw [getD_eval_bytesOf _ _ _ hk', VoleMole.Privacy.Moussaka.com_getD _ _ _ _ ⟨k, hk'⟩, ← hE]
  have e := hk ⟨k, hk'⟩
  simp only [List.getElem_map] at e ⊢
  rw [show (16 : ℕ) = Arith.Moussaka.redeemOffS from rfl]
  exact e

end VoleMole.EndToEnd.SpecRel

/-! ## Extraction from the chains of the Lean redemption statement -/

namespace VoleMole.Verifier.Bridge

open VoleMole.Arith VoleMole.Verifier VoleMole.EndToEnd VoleMole.SeedExtraction

/-- **The Lean redemption statement's system** at a combination vector `l`: the spec maps of the
Anchors. -/
def leanRedeemSysL (x : Spec.Moussaka.RedeemInstance) (l : Fin Moussaka.M → GF128) :
    System GF128 :=
  Moussaka.redeemSystem beta GF256.toBits (x.anchors.map (·.map)) (fnOf (toBA x.nf))
    (fnOf (toBA x.ctxIss)) (fnOf (toBA x.ctxRed)) l

/-- **The Lean redemption statement's witness predicate** (the spec maps of the Anchors). -/
def leanRedeemWit (x : Spec.Moussaka.RedeemInstance) : (ℕ → GF128) → Prop :=
  moussakaRedeemWit GF256.ofBits (x.anchors.map (·.map)) (fnOf (toBA x.nf))
    (fnOf (toBA x.ctxIss)) (fnOf (toBA x.ctxRed))

variable [VoleMole.Verifier.HasPrg]

open VoleMole.Privacy.Moussaka in
/-- **Moussaka redemption for the Lean statement, from the executable verifier's chains**
(`moussakaRedeem_extract_chain` with the Anchors' spec maps). -/
theorem stR_extract_chain {Ch : Type*} (x : Spec.Moussaka.RedeemInstance) (ch : Chain)
    (l : Fin Moussaka.M → GF128) (hvals : ∀ y, ch.vals y = (leanRedeemSysL x l).values y)
    {A : Finset Blocks} (hA : ∀ Δ ∈ A, ch.OnChain (stR x) CrtGen.tables Δ) {S : Set Blocks}
    (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift CrtGen.tables) (ch.kosQ (stR x) CrtGen.tables)
      (ch.kosD (stR x) CrtGen.tables))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (stR x) CrtGen.tables j Δ =
        v + uStar j * lift CrtGen.tables Δ) →
      ¬(leanRedeemSysL x l).Holds (wStar uStar (ch.dc (stR x))) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩ (valVec (leanRedeemSysL x l) (wStar uStar (ch.dc (stR x)))) ≠ 0)
    (hcomb : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (stR x) CrtGen.tables j Δ =
        v + uStar j * lift CrtGen.tables Δ) →
      (leanRedeemSysL x l).Holds (wStar uStar (ch.dc (stR x))) →
      leanRedeemWit x (wStar uStar (ch.dc (stR x))))
    (Z : Finset Ch) (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ y ∈ Z, acc y → δ y ∈ A) :
    (∃ i ∈ known, leanRedeemWit x (candidate (F := GF128) (ch.u (stR x)) (ch.dc (stR x)) i)) ∨
      #{y ∈ Z | acc y} ≤ 9 := by
  by_cases hA1 : A.card ≤ 1
  · exact Or.inr (few_of_card_le_one hA1 Z δ hδ acc hclaim1 (by norm_num))
  obtain ⟨uStar, R, hR, hK, hacc⟩ := chain_claim4 liftInvOk_tables (stR x) ch _ hvals
    (Degree.moussaka_redeem_deg _ _ _ _ _ _ _) hA hAS hkos hL2
  exact moussaka_redeem_extract_gf128 _ _ _ _ _ hK (ch.dc (stR x)) _ _ _ _ R hR hacc
    (hQS (by omega) uStar hK.consistent) (hcomb (by omega) uStar hK.consistent) Z δ hδ acc hclaim1

end VoleMole.Verifier.Bridge

/-! ## Statement families that decode -/

namespace VoleMole.Theft.Moussaka

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM VoleMole.ROM.IC
open VoleMole.Spec VoleMole.Spec.Moussaka
open VoleMole.Privacy.Moussaka (stR_values csR)

/-- **The Anchor keys are the keys of their digests** under the assignment `kt`. -/
def KeysBy (kt : Bytes → UOVKey) (x : RedeemInstance) : Prop := ∀ pk ∈ x.anchors, pk = kt pk.digest

/-- **The well-formed issuance instances.** -/
abbrev IssW := {x : IssueInstance // Hit.Mous.WfI x}

/-- **The well-formed redemption instances whose Anchor keys are those of `kt`.** -/
abbrev RedK (kt : Bytes → UOVKey) := {x : RedeemInstance // Hit.Mous.WfR x ∧ KeysBy kt x}

lemma muIn_issW_injective : Function.Injective fun x : IssW => muIn (Privacy.Moussaka.stI x.1) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  exact Subtype.ext (Hit.Mous.muIn_stI_inj hx hy h)

lemma anchors_keysBy {kt : Bytes → UOVKey} {x : RedeemInstance} (h : KeysBy kt x) :
    x.anchors = (x.anchors.map (·.digest)).map kt := by
  rw [List.map_map]
  conv_lhs => rw [← List.map_id x.anchors]
  exact List.map_congr_left fun pk hpk => h pk hpk

lemma muIn_redK_injective (kt : Bytes → UOVKey) :
    Function.Injective fun x : RedK kt => muIn (Privacy.Moussaka.stR x.1) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  have e := Hit.Mous.muIn_stR_inj hx.1 hy.1 h
  simp only [Hit.Mous.hashedR, Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5⟩ := e
  apply Subtype.ext
  show x = y
  have ha : x.anchors = y.anchors := by rw [anchors_keysBy hx.2, anchors_keysBy hy.2, e1]
  cases x
  cases y
  simp only at ha e2 e3 e4 e5
  rw [ha, e2, e3, e4, e5]

/-! ## The joint bound -/

variable {ιI' ιR' α βI βR : Type}

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Moussaka issuance and redemption, simultaneous extraction, Lean statements**
(`moussaka_sim_joint_spec` for `stI` on the well-formed issuance instances and `stR` on the
well-formed redemption instances with the keys `kt`): each query of the run charged once, at the
redemption relation's charge; the witnesses are in the spec relations. -/
theorem moussaka_sim_joint_lean (kt : Bytes → UOVKey)
    (PI₀ : OracleComp specIC (ByteArray × (IssW × βI)))
    (PI : ιI' → OracleComp specIC (ByteArray × (IssW × βI)))
    (PR₀ : OracleComp specIC (ByteArray × (RedK kt × βR)))
    (PR : ιR' → OracleComp specIC (ByteArray × (RedK kt × βR)))
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
          (fun s : IssW => Privacy.Moussaka.stI s.1) (PI j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (Privacy.Moussaka.stI (stOut r).1)
          (fun _ w => Privacy.Moussaka.IssueRelW (stOut r).1
            (SpecRel.issueWitOf (stOut r).1.ctxIss w)) r) ∨
      (∃ j ∈ JR, let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
          (fun s : RedK kt => Privacy.Moussaka.stR s.1) (PR j) E)
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (Privacy.Moussaka.stR (stOut r).1)
          (fun _ w => Privacy.Moussaka.RedeemRelW (stOut r).1
            (SpecRel.redeemWitOf (stOut r).1.nf (stOut r).1.ctxIss (stOut r).1.ctxRed w)) r)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      (q .h21 + (JI.card + JR.card)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + (JI.card + JR.card)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + (JI.card + JR.card)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        chainHitEpsCombSim q Arith.Moussaka.M (JI.card + JR.card) +
        stmtBindEpsSim q (JI.card + JR.card) + JI.card * failEps q qE + JR.card * failEps q qE := by
  classical
  set stIF : IssW → Statement := fun s => Privacy.Moussaka.stI s.1
  set stRF : RedK kt → Statement := fun s => Privacy.Moussaka.stR s.1
  set stI₀ := moussakaIssue ByteArray.empty ByteArray.empty true
  set stR₀ := moussakaRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty ByteArray.empty true
  have hsep := decOf_sep (fun s => muIn (stIF s)) (fun s => muIn (stRF s)) fun s s' =>
    Hit.Mous.muIn_stI_ne_stR s.1 s'.1
  have h := prEvent_sim_joint_le CrtGen.tables liftInvOk_tables stIF (decOf fun s => muIn (stIF s))
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
    PI₀ PI PR₀ PR JI JR qE hqEI hqER q hqI hqR₀ hqR nG hnGI hnGR₀ hnGR hpreI hpreR hsame oa event
    fun E g hev => by
      rcases htr E g hev with ⟨j, hj, hacc, hnex⟩ | ⟨j, hj, hacc, hnex⟩
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

/-! ## The inputs fit the tables -/

section VerOk

variable {L : ℕ}

/-- **The table length of the eager step for Moussaka**: the verifier's `H₁` leaf inputs
(`2⁸·32 + 1` bytes) are the longest inputs of the extra table it queries. -/
def Lrom : ℕ := 8193

lemma lmin_le_lrom : Hit.Mous.Lmin ≤ Lrom := by decide

set_option maxRecDepth 100000 in
/-- **The well-formed Lean issuance statement's inputs fit** the tables with `L ≥ 8193`. -/
lemma verOk_stIW (hL : Lrom ≤ L) {M : ℕ} (x : IssueInstance) (hx : Hit.Mous.WfI x) :
    VerOk Privacy.Moussaka.pI L M (Privacy.Moussaka.stI x) := by
  refine ⟨rfl, by simp [Privacy.Moussaka.stI, moussakaIssue, preLen], ?_, le_trans ?_ hL,
    le_trans ?_ hL, hL, ?_⟩
  · rw [Hit.Mous.size_muIn_stI hx]; exact le_trans (by decide) hL
  · show 64 + 16 * Privacy.Moussaka.pI.correctionBytes +
      Privacy.Moussaka.pI.nMask * Privacy.Moussaka.pI.nMultBytes + 16 + 0 + 1 ≤ Lrom
    decide
  · show 264 + 0 + Privacy.Moussaka.pI.witnessBytes + 1 ≤ Lrom
    decide
  · intro M' dst h
    exact absurd h (by simp [Privacy.Moussaka.stI, moussakaIssue])

set_option maxRecDepth 100000 in
/-- **The well-formed Lean redemption statement's inputs fit** the tables with `L ≥ 8193` and the
combination of `Moussaka.M` equations. -/
lemma verOk_stRW (hL : Lrom ≤ L) (x : RedeemInstance) (hx : Hit.Mous.WfR x) :
    VerOk Privacy.Moussaka.pI L Arith.Moussaka.M (Privacy.Moussaka.stR x) := by
  refine ⟨rfl, by simp [Privacy.Moussaka.stR, preLen], ?_, le_trans ?_ hL, le_trans ?_ hL, hL, ?_⟩
  · exact (Hit.Mous.size_muIn_stR_le hx).trans (le_trans (by decide) hL)
  · show 64 + 16 * Privacy.Moussaka.pR.correctionBytes +
      Privacy.Moussaka.pR.nMask * Privacy.Moussaka.pR.nMultBytes + 16 + 0 + 1 ≤ Lrom
    decide
  · show 264 + 0 + Privacy.Moussaka.pR.witnessBytes + 1 ≤ Lrom
    decide
  · intro M' dst h
    simp only [Privacy.Moussaka.stR, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, le_trans ?_ hL⟩
    decide

end VerOk

end VoleMole.Theft.Moussaka
