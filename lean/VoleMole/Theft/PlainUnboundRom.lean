import VoleMole.Theft.PlainUnboundJoint
import VoleMole.Theft.PlainMousRom

/-!
# Plain extraction for the unbound game from `ROM/`'s bound (unbound Moussaka)

The unbound counterpart of `Theft/PlainMousRom.lean`'s `plainSEL_romM`
(`docs/security/moussaka-unbound.md` §5.3): `PlainSEL` for the unbound operations, proved from
`ROM/`'s simultaneous extraction (`moussakaUnbound_sim_joint_lean`), for function rows, the
combination of `Moussaka.M` equations and `L ≥ 9749` (`LminU`).

* **`FreshKU kt`**: the freshness of the bound: the operation's statement is well-formed
  (`WfOpU`) and, for a redemption, its Anchor keys are the keys `kt d` of their digests
  (`KeysOpU`). `ROM/`'s argument decodes a statement from its `H₂⁰` input, which holds the
  Anchors' digests, not their maps.
* **`eRomU`**: `ROM/`'s straight-line extractor on the tables, as `eRomM`: a known tree's candidate
  mapped to the spec witness of the operation (`witOfCandU`: `uIssueWitOf`, `uRedeemWitOf`), if
  one is a witness.
* `outIU`, `outRU kt`: the normalized adversary as `ROM/`'s provers of the two unbound relations.
* `game_badU`: on the tables, a bad output of `PlainSEL` is a bad output of `ROM/`'s game.
* **`plainSEL_romU`**: `PlainSEL` for `eRomU` against `QBudT q qE nG`, for `FreshKU kt`, with the
  error `epsRomU q qE nG` of `moussakaUnbound_sim_joint_lean` with `m = 2` outputs:

      (q₂₁+2)·2^{−150} + (q₂₂+2)·(ε_QS(7929) + 2^{−128} + (n_G+339)·2^{−448})
        + (q₂₃+2)·9·2^{−128} + chainHitEpsCombSim q M 2 + stmtBindEpsSim q 2 + 2·failEps q q_E.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft.MoussakaUnbound

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads VoleMole.EndToEnd
open VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (AnchorSet ctxBytes nfBytes cdBytes)
open VoleMole.Privacy.MoussakaUnbound (toBound)
open VoleMole.Theft.Moussaka (KeysBy)

-- `UCom`, `Derive` and `Com` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

/-! ## The freshness of the bound -/

/-- **The operation's Anchor keys are those of `kt`** (nothing for an issuance). -/
def KeysOpU (kt : Bytes → UOVKey) : UOp → Prop
  | .issue _ _ => True
  | .redeem S' req ci cr cd => KeysBy kt (toBound (stOfR S' req ci cr cd))

/-- **The freshness of `ROM/`'s bound**: a well-formed statement with the Anchor keys of `kt`
(the honest pairs are not used: freshness against them is the programming term's). -/
def FreshKU (kt : Bytes → UOVKey) (_ : Option (IssueInstance × Bytes))
    (_ : Option (RedeemInstance × Bytes)) (op : UOp) : Prop :=
  WfOpU op ∧ KeysOpU kt op

/-! ## The straight-line extractor -/

/-- The spec witness of a candidate, for an operation (the bytes of `uIssueWitOf`,
`uRedeemWitOf` with the statement's fields). -/
def witOfCandU : UOp → (ℕ → Arith.GF128) → Bytes
  | .issue _ ci, w => SpecRel.uIssueWitOf ci w
  | .redeem _ _ ci cr _, w => SpecRel.uRedeemWitOf ci cr w

/-- A known tree's candidate that is a witness of the operation, if there is one. -/
noncomputable def pickU (op : UOp) (K : Finset (Fin BAVC.tau))
    (c : Fin BAVC.tau → ℕ → Arith.GF128) : Bytes := by
  classical
  exact if h : ∃ i ∈ K, RelOp op (witOfCandU op (c i)) then witOfCandU op (c h.choose) else []

lemma relOp_pickU {op : UOp} {K : Finset (Fin BAVC.tau)} {c : Fin BAVC.tau → ℕ → Arith.GF128}
    (h : ∃ i ∈ K, RelOp op (witOfCandU op (c i))) : RelOp op (pickU op K c) := by
  classical
  unfold pickU
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.2

variable {L : ℕ}

/-- **`ROM/`'s straight-line extractor on the unbound tables**: a known tree's candidate that is a
witness of the operation, if there is one (the cipher entries of the query list answered by the
cipher rows, `mu₁` and `iv` read off the extra table). -/
noncomputable def eRomU : Option (IssueInstance × Bytes) → Option (RedeemInstance × Bytes) → UOp →
    List DomIC → Tab3 → Tab3 → (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Moussaka.M → Bytes :=
  fun _ _ op qs _ _ b =>
    pickU op (Ratatouille.rOut (fdU op).1 (fdU op).2 (hbX b.2)
        (Ratatouille.ctOf b.1.2) (cLog (Ratatouille.ctOf b.1.2) qs)).2.1.known
      (candOf (Ratatouille.ctOf b.1.2) (fdU op).1
        (Ratatouille.rOut (fdU op).1 (fdU op).2 (hbX b.2) (Ratatouille.ctOf b.1.2)
          (cLog (Ratatouille.ctOf b.1.2) qs)))

/-! ## The adversary as `ROM/`'s provers -/

lemma wfIU_dummy : WfIU ⟨List.replicate uovM 0, List.replicate ctxBytes 0⟩ := by
  simp [WfIU, Hit.Mous.WfI, toBI]

lemma wfRU_dummy : WfRU ⟨[], List.replicate nfBytes 0, List.replicate ctxBytes 0,
    List.replicate ctxBytes 0, List.replicate cdBytes 0⟩ := by
  simp [WfRU, Hit.Mous.WfR, toBound]

/-- A well-formed unbound issuance instance (the dummy statement). -/
def issWU0 : IssWU := ⟨_, wfIU_dummy⟩

/-- A well-formed unbound redemption instance with no Anchor (the dummy statement). -/
def redKU0 (kt : Bytes → UOVKey) : RedKU kt := ⟨_, wfRU_dummy, fun _ h => by simp [toBound] at h⟩

open Classical in
/-- The issuance relation's output of an operation (a dummy for a redemption or an instance that
is not well-formed). -/
noncomputable def outIU : UOp → ByteArray × (IssWU × Unit)
  | .issue req ci => if h : WfIU (stOfI req ci) then
      (toBA (req.drop uovM), (⟨_, h⟩, ())) else (ByteArray.empty, (issWU0, ()))
  | .redeem _ _ _ _ _ => (ByteArray.empty, (issWU0, ()))

open Classical in
/-- The redemption relation's output of an operation (a dummy for an issuance or an instance that
is not in the family). -/
noncomputable def outRU (kt : Bytes → UOVKey) : UOp → ByteArray × (RedKU kt × Unit)
  | .redeem S' req ci cr cd => if h : WfRU (stOfR S' req ci cr cd) ∧
        KeysBy kt (toBound (stOfR S' req ci cr cd)) then
      (toBA (req.drop nfBytes), (⟨_, h⟩, ())) else (ByteArray.empty, (redKU0 kt, ()))
  | .issue _ _ => (ByteArray.empty, (redKU0 kt, ()))

/-! ## On the tables, the bad event is the game's -/

section Bad

variable {ι : Type}

set_option maxHeartbeats 2000000 in
/-- **On the tables, a bad output of `PlainSEL` is a bad output of `ROM/`'s game** (as
`game_badM`): if the operation is accepted by the Lean verifier and `eRomU` finds no witness, the
game run on the tables (the normalized adversary as the prover `out <$> normT`) accepts, and its
extraction fails (for a witness predicate `Wit` that gives the operation's relation). -/
theorem game_badU (stF : ι → Statement) (out : UOp → ByteArray × (ι × Unit))
    (Wit : ι → (ℕ → Arith.GF128) → Prop) (oa : OracleComp specIC UOp)
    (g₁ g₂ : Tab3) (t : ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M))
    (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes))
    (hfd : fdU (runT (ansP g₁ g₂ t) oa) =
      (stF (out (runT (ansP g₁ g₂ t) oa)).2.1, (out (runT (ansP g₁ g₂ t) oa)).1))
    (hacc : (verRO Privacy.Moussaka.pI (hbX t.2.2) (stF (out (runT (ansP g₁ g₂ t) oa)).2.1)
      (out (runT (ansP g₁ g₂ t) oa)).1 (shOf t)).accept = true)
    (hW : ∀ w, Wit (out (runT (ansP g₁ g₂ t) oa)).2.1 w →
      RelOp (runT (ansP g₁ g₂ t) oa) (witOfCandU (runT (ansP g₁ g₂ t) oa) w))
    (hne : ¬ RelOp (runT (ansP g₁ g₂ t) oa)
      (eRomU p₁ p₂ (runT (ansP g₁ g₂ t) oa) (qlog (ansP g₁ g₂ t) oa) g₁ g₂ t.2)) :
    (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
        (out <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa) (cellP t))).2.2.accept = true ∧
      ¬ @Extracted (icPrg (cellP t).cipher) _
        (stF (stOut (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
          (out <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa) (cellP t)))))
        (fun _ w => Wit (stOut (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t))
          (gameA CrtGen.tables stF (out <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa)
            (cellP t)))) w)
        (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
          (out <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa) (cellP t))) := by
  classical
  set o := runT (ansP g₁ g₂ t) oa with ho
  obtain ⟨hrunN, hqN⟩ := normT_ansP g₁ g₂ t oa
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join (tabP g₁ g₂ t) (cellP t)))
      (out <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa) = out o := by
    rw [← runT_eq_eval, runT_map]
    exact congrArg out hrunN
  have hJ : cipherLog (tableQueryLog (out <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa)
      (join (tabP g₁ g₂ t) (cellP t))) =
      cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa) := by
    rw [tableQueryLog_map', tableQueryLog_eq_qlog, cipherLog_map]
    show cLog (Ratatouille.ctOf t.2.1.2)
      (qlog (ansP g₁ g₂ t) (normT Privacy.Moussaka.pI L Arith.Moussaka.M oa)) = _
    rw [hqN, cLog_filter _ _ fun c => decide_eq_true
      (show OnT Privacy.Moussaka.pI L Arith.Moussaka.M (.inr c) from trivial)]
  have hivP : ivOf (Hashes.ofTable (tabP g₁ g₂ t)) ⟨(stF (out o).2.1).params, (out o).1⟩
      ((stF (out o).2.1).mu1 (Hashes.ofTable (tabP g₁ g₂ t))) =
      ivOf (hbX t.2.2) ⟨(stF (out o).2.1).params, (out o).1⟩
        ((stF (out o).2.1).mu1 (hbX t.2.2)) := by
    rw [ofTable_tabP]
    exact ivOf_congr (recP_hash_ne _ _ _ (by decide) (by decide) (by decide))
      (recP_hash_ne _ _ _ (by decide) (by decide) (by decide))
      (recP_hash_ne _ _ _ (by decide) (by decide) (by decide)) _ _
  have hver : @verify (icPrg (cellP t).cipher) (Hashes.ofTable (tabP g₁ g₂ t)) CrtGen.tables
      (stF (out o).2.1) (out o).1 =
      verRO Privacy.Moussaka.pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t) := by
    rw [ofTable_tabP]
    exact congrFun (@verify_agreeOff_h3 (icPrg (rowFn t.2.1.2)) _ _
      (Hashes.agreeOff_withTable _ _ _ _).symm CrtGen.tables _) _
  have hivV : (verRO Privacy.Moussaka.pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t)).iv =
      ivOf (hbX t.2.2) ⟨(stF (out o).2.1).params, (out o).1⟩
        ((stF (out o).2.1).mu1 (hbX t.2.2)) := by
    have hacc' : (@verify (icPrg (rowFn t.2.1.2)) (recV Privacy.Moussaka.pI (hbX t.2.2) t.1 t.2.1.1)
        CrtGen.tables (stF (out o).2.1) (out o).1).accept = true := hacc
    obtain ⟨-, leaves, hrec, -⟩ := (@accept_iff (icPrg (rowFn t.2.1.2)) _ _ _ _).1 hacc'
    refine (@verify_iv_chal1 (icPrg (rowFn t.2.1.2)) _ _ _ _ hacc' leaves hrec).1.trans ?_
    exact ivOf_congr (recV_hash_ne _ _ _ (by decide) (by decide))
      (recV_hash_ne _ _ _ (by decide) (by decide)) (recV_hash_ne _ _ _ (by decide) (by decide))
      _ _
  have hr := eval_gameA CrtGen.tables stF (out <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa)
    (cellP t) (tabP g₁ g₂ t)
  rw [hP, hJ, hver, hivP] at hr
  generalize evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t))
    (gameA CrtGen.tables stF (out <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa)
      (cellP t)) = R at hr ⊢
  have hS : stOut R = (out o).2.1 := by rw [hr]; rfl
  have hT : R.2.2 = verRO Privacy.Moussaka.pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t) := by
    rw [hr]
  have hKn : R.2.1.known = (Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2)
      (Ratatouille.ctOf t.2.1.2)
        (cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa))).2.1.known := by
    rw [hr]; rfl
  have hK : R.2.1.keys = (Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2)
      (Ratatouille.ctOf t.2.1.2)
        (cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa))).2.1.keys := by
    rw [hr]; rfl
  have h1 : R.1 = (out o).1 := by rw [hr]
  rw [hS, hT]
  refine ⟨hacc, fun he => hne ?_⟩
  obtain ⟨i, hi, hw⟩ := he
  apply relOp_pickU
  rw [hfd]
  refine ⟨i, hKn ▸ hi, hW _ ?_⟩
  have hiv' : R.2.2.iv = (Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2)
      (Ratatouille.ctOf t.2.1.2)
        (cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa))).2.2.iv := by
    rw [hT]; exact hivV
  have hc := candOf_congr (cellP t) (stF (out o).2.1) (r := R)
    (r' := Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2) (Ratatouille.ctOf t.2.1.2)
      (cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa))) h1 hK hiv' i
  exact hc ▸ hw

end Bad

/-! ## Plain extraction from `ROM/`'s bound -/

section Plain

/-- **The error of `ROM/`'s simultaneous extraction** for one unbound issuance and one unbound
redemption output (`moussakaUnbound_sim_joint_lean` with `m = 2`), for `q k` hash queries of kind
`k`, `qE` cipher cells and `nG` hash queries in all. -/
noncomputable def epsRomU (q : Kind → ℕ) (qE nG : ℕ) : ℝ≥0∞ :=
  (q .h21 + 2) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 2) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 2) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    chainHitEpsCombSim q Arith.Moussaka.M 2 + stmtBindEpsSim q 2 + 2 * failEps q qE

lemma epsRomU_ne_top (q : Kind → ℕ) (qE nG : ℕ) : epsRomU q qE nG ≠ ⊤ := by
  simp [epsRomU, chainHitEpsCombSim, chainHitEpsSim, stmtBindEpsSim, failEps, openHashEps,
    ladderEps, ENNReal.mul_eq_top, ENNReal.div_eq_top]

lemma verILUX_eq (x : IssueInstance) (π : Bytes)
    (t : ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :
    verILUX hbX x π t = (verRO Privacy.Moussaka.pI (hbX t.2.2) (Privacy.MoussakaUnbound.stI x)
      (toBA π) (shOf t)).accept := rfl

lemma verRLUX_eq (x : RedeemInstance) (π : Bytes)
    (t : ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :
    verRLUX hbX x π t = (verRO Privacy.Moussaka.pI (hbX t.2.2) (Privacy.MoussakaUnbound.stR x)
      (toBA π) (shOf t)).accept := rfl

lemma allQ_map_normTU {β : Type} (f : UOp → β) (oa : OracleComp specIC UOp) :
    AllQueriesSatisfy (f <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa)
      (OnT Privacy.Moussaka.pI L Arith.Moussaka.M) := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind (allQueriesSatisfy_normT _) fun _ => allQueriesSatisfy_pure _ _

set_option maxHeartbeats 400000 in
/-- **Plain extraction for the unbound game from `ROM/`'s bound** (function rows,
`M = Moussaka.M`, `L ≥ 9749`): `PlainSEL` holds for `ROM/`'s straight-line extractor `eRomU`
against the last stages within `QBudT q qE nG`, for the freshness `FreshKU kt` (well-formed
statements, Anchor keys of `kt`), with the error `epsRomU q qE nG` of
`moussakaUnbound_sim_joint_lean` for one issuance and one redemption output. -/
theorem plainSEL_romU (kt : Bytes → UOVKey) (hL : LminU ≤ L) (q : Kind → ℕ) (qE nG : ℕ) :
    PlainSEL ansP (AccOp (verILUX hbX) (verRLUX hbX)) (FreshKU kt) RelOp
      (eRomU (L := L)) (QBudT q qE nG) (epsRomU q qE nG).toReal := by
  classical
  intro α _ _ p₁ p₂ oa hoa
  rw [pr_eq_toReal_prU]
  refine ENNReal.toReal_mono (epsRomU_ne_top q qE nG) (Prob.prU_prod_le_right _ fun a => ?_)
  -- the normalized adversary as the provers, and the joint game
  set N := normT Privacy.Moussaka.pI L Arith.Moussaka.M (oa a)
  set PI := outIU <$> N
  set PR := outRU kt <$> N
  let m : CTable → OracleComp spec (Out ((IssWU × Unit) × QueryLog specIC) ×
      Out ((RedKU kt × Unit) × QueryLog specIC)) := fun E =>
    gameA CrtGen.tables (fun s : IssWU => Privacy.MoussakaUnbound.stI s.1) PI E >>= fun r₁ =>
      gameA CrtGen.tables (fun s : RedKU kt => Privacy.MoussakaUnbound.stR s.1) PR E >>= fun r₂ =>
        pure (r₁, r₂)
  let ev : CTable → Out ((IssWU × Unit) × QueryLog specIC) ×
      Out ((RedKU kt × Unit) × QueryLog specIC) → Prop := fun E r =>
    (r.1.2.2.accept = true ∧ ¬ @Extracted (icPrg E.cipher) _
      (Privacy.MoussakaUnbound.stI (stOut r.1).1)
      (fun _ w => IssueRel (stOut r.1).1 (SpecRel.uIssueWitOf (stOut r.1).1.ctxIss w)) r.1) ∨
    (r.2.2.2.accept = true ∧ ¬ @Extracted (icPrg E.cipher) _
      (Privacy.MoussakaUnbound.stR (stOut r.2).1)
      (fun _ w => RedeemRel (stOut r.2).1
        (SpecRel.uRedeemWitOf (stOut r.2).1.ctxIss (stOut r.2).1.ctxRed w)) r.2)
  have heval : ∀ E g, evalWithAnswerFn (QueryImpl.ofFn g) (m E) =
      (evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (fun s : IssWU => Privacy.MoussakaUnbound.stI s.1) PI E),
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (fun s : RedKU kt => Privacy.MoussakaUnbound.stR s.1) PR E)) := by
    intro E g
    simp only [m, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  -- `ROM/`'s bound on the joint game
  have hb := (hoa a)
  have hrom := moussakaUnbound_sim_joint_lean kt PI (fun _ : Unit => PI) PR (fun _ : Unit => PR)
    Finset.univ Finset.univ qE
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_normT hb.1.2))
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_normT hb.1.2)) q
    (fun _ _ => (isQueryBound_map_iff _ _ _ _ _).2 (isKindQueryBoundIC_normT hb.1.1))
    ((isQueryBound_map_iff _ _ _ _ _).2 (isKindQueryBoundIC_normT hb.1.1))
    (fun _ _ => (isQueryBound_map_iff _ _ _ _ _).2 (isKindQueryBoundIC_normT hb.1.1)) nG
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_normT hb.2))
    ((isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_normT hb.2))
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_normT hb.2))
    (fun E => prefixRuns_self E PI) (fun E => prefixRuns_self E PR)
    (fun E g => by rw [tableQueryLog_runE_map, tableQueryLog_runE_map]) m ev
    (fun E g hev => by
      rw [heval] at hev
      rcases hev with h | h
      · exact Or.inl ⟨(), Finset.mem_univ _, h⟩
      · exact Or.inr ⟨(), Finset.mem_univ _, h⟩)
  have hrom' : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m E)).run' ∅}[ev E r] ≤
      epsRomU q qE nG := by
    refine hrom.trans (le_of_eq ?_)
    simp only [Finset.card_univ, Fintype.card_unit, epsRomU]
    norm_num
    ring
  -- the joint game queries only table points: the tables are the lazy oracle
  have hI : AllQueriesSatisfy PI (OnT Privacy.Moussaka.pI L Arith.Moussaka.M) :=
    allQ_map_normTU _ _
  have hR : AllQueriesSatisfy PR (OnT Privacy.Moussaka.pI L Arith.Moussaka.M) :=
    allQ_map_normTU _ _
  have hsI : ∀ s : IssWU, VerOk Privacy.Moussaka.pI L Arith.Moussaka.M
      (Privacy.MoussakaUnbound.stI s.1) := fun s => verOk_stIUW hL s.1 s.2
  have hsR : ∀ s : RedKU kt, VerOk Privacy.Moussaka.pI L Arith.Moussaka.M
      (Privacy.MoussakaUnbound.stR s.1) := fun s => verOk_stRUW hL s.1 s.2.1
  have hm : ∀ E, AllQueriesSatisfy (m E) (· ∈ TPts Privacy.Moussaka.pI L Arith.Moussaka.M) :=
    fun E => allQueriesSatisfy_bind
      (gameA_onT (fun s : IssWU => Privacy.MoussakaUnbound.stI s.1) hsI hI E) fun _ =>
        allQueriesSatisfy_bind
          (gameA_onT (fun s : RedKU kt => Privacy.MoussakaUnbound.stR s.1) hsR hR E)
          fun _ => allQueriesSatisfy_pure _ _
  have hbr := pr_tables_eq_ro m hm ev
  rw [pr_eq_toReal_prU] at hbr
  have hfin : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m E)).run' ∅}[ev E r] ≠ ⊤ :=
    ne_top_of_le_ne_top (epsRomU_ne_top q qE nG) hrom'
  rw [← (ENNReal.toReal_eq_toReal_iff' (ne_top_of_le_ne_top ENNReal.one_ne_top
    (Prob.prU_le_one _)) hfin).1 hbr] at hrom'
  refine (Prob.prU_mono fun z hz => ?_).trans hrom'
  -- on the tables, the bad event is the game's
  obtain ⟨hacc, hfr, hne⟩ := hz
  show ev (cellP z.2) (runT (tabP z.1.1 z.1.2 z.2) (m (cellP z.2)))
  rw [runT_eq_eval, heval]
  rcases hop : runT (ansP z.1.1 z.1.2 z.2) (oa a) with ⟨req, ci⟩ | ⟨S', req, ci, cr, cd⟩
  · rw [hop] at hacc hfr
    have hw : WfIU (stOfI req ci) := hfr.1
    have ho : outIU (.issue req ci) = (toBA (req.drop uovM), (⟨_, hw⟩, ())) := by
      simp only [outIU, dite_eq_left hw]
    have hacc' := (verILUX_eq _ _ _).symm.trans hacc.2.2
    exact Or.inl (game_badU (fun s : IssWU => Privacy.MoussakaUnbound.stI s.1) outIU
      (fun s w => IssueRel s.1 (SpecRel.uIssueWitOf s.1.ctxIss w))
      (oa a) z.1.1 z.1.2 z.2 (p₁ a) (p₂ a) (by rw [hop, ho]; rfl) (by rw [hop, ho]; exact hacc')
      (fun w hw' => by rw [hop] at hw' ⊢; rw [ho] at hw'; exact hw') hne)
  · rw [hop] at hacc hfr
    have hw : WfRU (stOfR S' req ci cr cd) ∧ KeysBy kt (toBound (stOfR S' req ci cr cd)) :=
      ⟨hfr.1, hfr.2⟩
    have ho : outRU kt (.redeem S' req ci cr cd) = (toBA (req.drop nfBytes), (⟨_, hw⟩, ())) := by
      simp only [outRU, dite_eq_left hw]
    have hacc' := (verRLUX_eq _ _ _).symm.trans hacc.2.2.2
    exact Or.inr (game_badU (fun s : RedKU kt => Privacy.MoussakaUnbound.stR s.1) (outRU kt)
      (fun s w => RedeemRel s.1 (SpecRel.uRedeemWitOf s.1.ctxIss s.1.ctxRed w))
      (oa a) z.1.1 z.1.2 z.2 (p₁ a) (p₂ a) (by rw [hop, ho]; rfl) (by rw [hop, ho]; exact hacc')
      (fun w hw' => by rw [hop] at hw' ⊢; rw [ho] at hw'; exact hw') hne)

end Plain

end VoleMole.Theft.MoussakaUnbound
