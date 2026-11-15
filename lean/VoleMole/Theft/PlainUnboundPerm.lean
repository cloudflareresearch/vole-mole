import VoleMole.Theft.PlainUnboundJointP
import VoleMole.Theft.PlainUnboundRom
import VoleMole.Theft.PlainMousPerm

/-!
# Plain extraction for the unbound game, permutation rows and inverse queries

The unbound counterpart of `Theft/PlainMousPerm.lean`'s `plainSEL_romMP`: `PlainSEL` for the
unbound operations from `ROM/`'s permutation-model bound (`moussakaUnbound_sim_joint_leanP`), for
permutation rows, an adversary over `specP` with forward and inverse cipher queries, `M =
Moussaka.M` and `L ≥ 9749`.

* **`eRomUP`**: `eRomU` on the cells the queries determine (`toIC π`).
* `game_badUP`, **`plainSEL_romUP`** (error `epsRomUP q q_E (totK Moussaka.M q)`).
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

variable {L : ℕ}

/-! ## The straight-line extractor on the cells of the queries -/

/-- **`ROM/`'s straight-line extractor with inverse queries** (Moussaka): `eRomM` on the cells the
queries determine (`toIC π`), with the permutations' forward rows. -/
noncomputable def eRomUP : Option (IssueInstance × Bytes) → Option (RedeemInstance × Bytes) → UOp →
    List DomP → Tab3 → Tab3 → (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M → Bytes :=
  fun p₁ p₂ op qs g₁ g₂ b =>
    eRomU p₁ p₂ op (qs.map (toIC b.1.2)) g₁ g₂ ((b.1.1, Ratatouille.fnRows b.1.2), b.2)

/-! ## On the tables, the bad event is the game's -/

section Bad

variable {ι : Type}

set_option maxHeartbeats 4000000 in
/-- **On the tables, a bad output of `PlainSEL` is a bad output of `ROM/`'s game** (Moussaka,
permutation model). -/
theorem game_badUP (pN pR' : Params) (stF : ι → Statement) (out : UOp → ByteArray × (ι × Unit))
    (Wit : ι → (ℕ → Arith.GF128) → Prop) (oa : OracleComp specP UOp)
    (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M))
    (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes))
    (hfd : fdU (runT (ansQ g₁ g₂ t) oa) =
      (stF (out (runT (ansQ g₁ g₂ t) oa)).2.1, (out (runT (ansQ g₁ g₂ t) oa)).1))
    (hacc : (verRO Privacy.Moussaka.pI (hbX t.2.2) (stF (out (runT (ansQ g₁ g₂ t) oa)).2.1)
      (out (runT (ansQ g₁ g₂ t) oa)).1 (shOf t)).accept = true)
    (hW : ∀ w, Wit (out (runT (ansQ g₁ g₂ t) oa)).2.1 w →
      RelOp (runT (ansQ g₁ g₂ t) oa) (witOfCandU (runT (ansQ g₁ g₂ t) oa) w))
    (hne : ¬ RelOp (runT (ansQ g₁ g₂ t) oa)
      (eRomUP p₁ p₂ (runT (ansQ g₁ g₂ t) oa) (qlog (ansQ g₁ g₂ t) oa) g₁ g₂ t.2)) :
    (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
        (normJ pN pR' t.2.1.2 (out <$> normTQ Privacy.Moussaka.pI L Arith.Moussaka.M oa))
        (PTable.fwd t.2.1.2))).2.2.accept = true ∧
      ¬ @Extracted (icPrg (PTable.fwd t.2.1.2).cipher) _
        (stF (stOut (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
          (normJ pN pR' t.2.1.2 (out <$> normTQ Privacy.Moussaka.pI L Arith.Moussaka.M oa))
          (PTable.fwd t.2.1.2)))))
        (fun _ w => Wit (stOut (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t))
          (gameA CrtGen.tables stF
            (normJ pN pR' t.2.1.2 (out <$> normTQ Privacy.Moussaka.pI L Arith.Moussaka.M oa))
            (PTable.fwd t.2.1.2)))) w)
        (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
          (normJ pN pR' t.2.1.2 (out <$> normTQ Privacy.Moussaka.pI L Arith.Moussaka.M oa))
          (PTable.fwd t.2.1.2))) := by
  classical
  set o := runT (ansQ g₁ g₂ t) oa with ho
  set π : PTable := t.2.1.2 with hπ
  obtain ⟨hrunN, hqN⟩ := normTQ_ansQ g₁ g₂ t oa
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join (tabP g₁ g₂ t) (PTable.fwd π)))
      (normJ pN pR' π (out <$> normTQ Privacy.Moussaka.pI L Arith.Moussaka.M oa)) = out o := by
    rw [evalWithAnswerFn_normJ, ← runT_eq_eval, runT_map]
    exact congrArg out hrunN
  have hJ : cipherLog (tableQueryLog
      (normJ pN pR' π (out <$> normTQ Privacy.Moussaka.pI L Arith.Moussaka.M oa))
      (join (tabP g₁ g₂ t) (PTable.fwd π))) =
      cLog (Ratatouille.ctOf (Ratatouille.fnRows π)) ((qlog (ansQ g₁ g₂ t) oa).map (toIC π)) := by
    rw [normJ_map, tableQueryLog_map', tableQueryLog_eq_qlog, cipherLog_map]
    show cLog (PTable.fwd π) (qlog (join (tabP g₁ g₂ t) (PTable.fwd π))
      (normJ pN pR' π (normTQ Privacy.Moussaka.pI L Arith.Moussaka.M oa))) = _
    rw [cLog_normJ]
    show cLog (PTable.fwd π) ((qlog (ansQ g₁ g₂ t)
      (normTQ Privacy.Moussaka.pI L Arith.Moussaka.M oa)).map (toIC π)) = _
    rw [hqN, cLog_map_filter _ _ fun c => decide_eq_true
      (show OnTQ Privacy.Moussaka.pI L Arith.Moussaka.M (.inr c) from trivial)]
    rfl
  have hivP : ivOf (Hashes.ofTable (tabP g₁ g₂ t)) ⟨(stF (out o).2.1).params, (out o).1⟩
      ((stF (out o).2.1).mu1 (Hashes.ofTable (tabP g₁ g₂ t))) =
      ivOf (hbX t.2.2) ⟨(stF (out o).2.1).params, (out o).1⟩ ((stF (out o).2.1).mu1 (hbX t.2.2)) := by
    rw [ofTable_tabP]
    exact ivOf_congr (recP_hash_neP _ _ _ (by decide) (by decide) (by decide))
      (recP_hash_neP _ _ _ (by decide) (by decide) (by decide))
      (recP_hash_neP _ _ _ (by decide) (by decide) (by decide)) _ _
  have hver : @verify (icPrg (PTable.fwd π).cipher) (Hashes.ofTable (tabP g₁ g₂ t)) CrtGen.tables
      (stF (out o).2.1) (out o).1 =
        verRO Privacy.Moussaka.pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t) := by
    rw [ofTable_tabP]
    exact congrFun (@verify_agreeOff_h3 (icPrg (rowFn t.2.1.2)) _ _
      (Hashes.agreeOff_withTable _ _ _ _).symm CrtGen.tables _) _
  have hivV : (verRO Privacy.Moussaka.pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t)).iv =
      ivOf (hbX t.2.2) ⟨(stF (out o).2.1).params, (out o).1⟩ ((stF (out o).2.1).mu1 (hbX t.2.2)) := by
    have hacc' : (@verify (icPrg (rowFn t.2.1.2)) (recV Privacy.Moussaka.pI (hbX t.2.2) t.1 t.2.1.1)
        CrtGen.tables (stF (out o).2.1) (out o).1).accept = true := hacc
    obtain ⟨-, leaves, hrec, -⟩ := (@accept_iff (icPrg (rowFn t.2.1.2)) _ _ _ _).1 hacc'
    refine (@verify_iv_chal1 (icPrg (rowFn t.2.1.2)) _ _ _ _ hacc' leaves hrec).1.trans ?_
    exact ivOf_congr (recV_hash_ne _ _ _ (by decide) (by decide))
      (recV_hash_ne _ _ _ (by decide) (by decide)) (recV_hash_ne _ _ _ (by decide) (by decide)) _ _
  have hr := eval_gameA CrtGen.tables stF
    (normJ pN pR' π (out <$> normTQ Privacy.Moussaka.pI L Arith.Moussaka.M oa)) (PTable.fwd π)
    (tabP g₁ g₂ t)
  rw [hP, hJ, hver, hivP] at hr
  generalize evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
    (normJ pN pR' π (out <$> normTQ Privacy.Moussaka.pI L Arith.Moussaka.M oa)) (PTable.fwd π)) = R
    at hr ⊢
  set lg := cLog (Ratatouille.ctOf (Ratatouille.fnRows π)) ((qlog (ansQ g₁ g₂ t) oa).map (toIC π))
  have hS : stOut R = (out o).2.1 := by rw [hr]; rfl
  have hT : R.2.2 = verRO Privacy.Moussaka.pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t) := by
    rw [hr]
  have hKn : R.2.1.known = (Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2)
      (Ratatouille.ctOf (Ratatouille.fnRows π)) lg).2.1.known := by
    rw [hr]; rfl
  have hK : R.2.1.keys = (Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2)
      (Ratatouille.ctOf (Ratatouille.fnRows π)) lg).2.1.keys := by
    rw [hr]; rfl
  have h1 : R.1 = (out o).1 := by rw [hr]
  rw [hS, hT]
  refine ⟨hacc, fun he => hne ?_⟩
  obtain ⟨i, hi, hw⟩ := he
  apply relOp_pickU
  rw [hfd]
  refine ⟨i, hKn ▸ hi, hW _ ?_⟩
  have hiv' : R.2.2.iv = (Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2)
      (Ratatouille.ctOf (Ratatouille.fnRows π)) lg).2.2.iv := by
    rw [hT]; exact hivV
  have hc := candOf_congr (PTable.fwd π) (stF (out o).2.1) (r := R)
    (r' := Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2)
      (Ratatouille.ctOf (Ratatouille.fnRows π)) lg) h1 hK hiv' i
  exact hc ▸ hw

end Bad

/-! ## Plain extraction from `ROM/`'s permutation-model bound -/

section Plain

/-- **The error of `ROM/`'s simultaneous extraction in the permutation model** for one issuance and
one redemption output (`moussakaUnbound_sim_joint_leanP` with `m = 2`). -/
noncomputable def epsRomUP (q : Kind → ℕ) (qE nG : ℕ) : ℝ≥0∞ :=
  (q .h21 + 2) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 2) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 * q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 2) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    chainHitEpsCombSim q Arith.Moussaka.M 2 + stmtBindEpsSim q 2 + 2 * failEpsP q qE

/-- The error is finite for fewer than `2¹²⁸ − 4607` cipher queries. -/
lemma epsRomUP_ne_top (q : Kind → ℕ) {qE : ℕ} (nG : ℕ) (hqE : qE + 4607 < 2 ^ 128) :
    epsRomUP q qE nG ≠ ⊤ := by
  have h1 : pE qE ≠ ⊤ := pE_ne_top (by omega)
  have h2 : pE (qE + 4607) ≠ ⊤ := pE_ne_top hqE
  simp [epsRomUP, chainHitEpsCombSim, chainHitEpsSim, stmtBindEpsSim, failEpsP, openHashEps,
    ladderEps, ENNReal.mul_eq_top, ENNReal.div_eq_top, h1, h2]

lemma verILUX_eqP (x : IssueInstance) (π : Bytes)
    (t : ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :
    verILUX hbX x π t = (verRO Privacy.Moussaka.pI (hbX t.2.2) (Privacy.MoussakaUnbound.stI x) (toBA π)
      (shOf t)).accept := rfl

lemma verRLUX_eqP (x : RedeemInstance) (π : Bytes)
    (t : ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :
    verRLUX hbX x π t = (verRO Privacy.Moussaka.pI (hbX t.2.2) (Privacy.MoussakaUnbound.stR x) (toBA π)
      (shOf t)).accept := rfl

lemma allQ_map_normTQU {β : Type} (f : UOp → β) (oa : OracleComp specP UOp) :
    AllQueriesSatisfy (f <$> normTQ Privacy.Moussaka.pI L Arith.Moussaka.M oa)
      (OnTQ Privacy.Moussaka.pI L Arith.Moussaka.M) := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind (allQueriesSatisfy_normTQ _) fun _ => allQueriesSatisfy_pure _ _

lemma le_of_lminU (hL : LminU ≤ L) : 49 ≤ L := le_trans (by decide) hL

set_option maxHeartbeats 800000 in
/-- **Plain extraction for the unbound game from `ROM/`'s permutation-model bound** (unbound Moussaka,
permutation rows, inverse queries, `M = Moussaka.M`, `L ≥ 9749`): `PlainSEL` holds for `eRomUP`
against the last stages within `QBudP q qE`, for the freshness `FreshKU kt`, with the error
`epsRomUP q qE (totK Moussaka.M q)`. -/
theorem plainSEL_romUP (kt : Bytes → UOVKey) (hL : LminU ≤ L) (q : Kind → ℕ) {qE : ℕ}
    (hqE : qE + 4607 < 2 ^ 128) :
    PlainSEL ansQ (AccOp (verILUX hbX) (verRLUX hbX)) (FreshKU kt) RelOp
      (eRomUP (L := L)) (QBudP q qE) (epsRomUP q qE (totK Arith.Moussaka.M q)).toReal := by
  classical
  intro α _ _ p₁ p₂ oa hoa
  rw [pr_eq_toReal_prU]
  refine ENNReal.toReal_mono (epsRomUP_ne_top _ _ hqE) (Prob.prU_prod_le_right _ fun a => ?_)
  -- the normalized adversary as the provers, and the joint game
  set N := normTQ Privacy.Moussaka.pI L Arith.Moussaka.M (oa a)
  set PI := outIU <$> N
  set PR := outRU kt <$> N
  let m : PTable → OracleComp spec (Out ((IssWU × Unit) × QueryLog specIC) ×
      Out ((RedKU kt × Unit) × QueryLog specIC)) := fun π =>
    gameA CrtGen.tables (fun s : IssWU => Privacy.MoussakaUnbound.stI s.1)
        (normJ (mousUPI true) (mousUPR true) π PI) π.fwd >>= fun r₁ =>
      gameA CrtGen.tables (fun s : RedKU kt => Privacy.MoussakaUnbound.stR s.1)
        (normJ (mousUPI true) (mousUPR true) π PR) π.fwd >>= fun r₂ => pure (r₁, r₂)
  let ev : PTable → Out ((IssWU × Unit) × QueryLog specIC) ×
      Out ((RedKU kt × Unit) × QueryLog specIC) → Prop := fun π r =>
    (r.1.2.2.accept = true ∧ ¬ @Extracted (icPrg π.fwd.cipher) _
      (Privacy.MoussakaUnbound.stI (stOut r.1).1)
      (fun _ w => IssueRel (stOut r.1).1
        (SpecRel.uIssueWitOf (stOut r.1).1.ctxIss w)) r.1) ∨
    (r.2.2.2.accept = true ∧ ¬ @Extracted (icPrg π.fwd.cipher) _
      (Privacy.MoussakaUnbound.stR (stOut r.2).1)
      (fun _ w => RedeemRel (stOut r.2).1
        (SpecRel.uRedeemWitOf (stOut r.2).1.ctxIss (stOut r.2).1.ctxRed w)) r.2)
  have heval : ∀ π g, evalWithAnswerFn (QueryImpl.ofFn g) (m π) =
      (evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (fun s : IssWU => Privacy.MoussakaUnbound.stI s.1)
            (normJ (mousUPI true) (mousUPR true) π PI) π.fwd),
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (fun s : RedKU kt => Privacy.MoussakaUnbound.stR s.1)
            (normJ (mousUPI true) (mousUPR true) π PR) π.fwd)) := by
    intro π g
    simp only [m, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  -- `ROM/`'s bound on the joint game
  have hb := qBudPT_normTQ (p := Privacy.Moussaka.pI) (L := L) (M := Arith.Moussaka.M) (hoa a)
  have hrom := moussakaUnbound_sim_joint_leanP kt PI (fun _ : Unit => PI) PR (fun _ : Unit => PR)
    Finset.univ Finset.univ qE
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 hb.1.2)
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 hb.1.2) q
    (fun _ _ => (isQueryBound_map_iff _ _ _ _ _).2 hb.1.1)
    ((isQueryBound_map_iff _ _ _ _ _).2 hb.1.1)
    (fun _ _ => (isQueryBound_map_iff _ _ _ _ _).2 hb.1.1) (totK Arith.Moussaka.M q)
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 hb.2)
    ((isQueryBoundP_map_iff _ _ _).2 hb.2)
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 hb.2)
    (fun π => prefixRuns_self π.fwd _) (fun π => prefixRuns_self π.fwd _)
    (fun π g => tableQueryLog_runE_normJ_map _ _ π N _ _ g) m ev
    (fun π g hev => by
      rw [heval] at hev
      rcases hev with h | h
      · exact Or.inl ⟨(), Finset.mem_univ _, h⟩
      · exact Or.inr ⟨(), Finset.mem_univ _, h⟩)
  have hrom' : Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (m π)).run' ∅}[ev π r] ≤
      epsRomUP q qE (totK Arith.Moussaka.M q) := by
    refine hrom.trans (le_of_eq ?_)
    simp only [Finset.card_univ, Fintype.card_unit, epsRomUP]
    norm_num
    ring
  -- the joint game queries only table points: the tables are the lazy oracle
  have hsI : ∀ s : IssWU, VerOk Privacy.Moussaka.pI L Arith.Moussaka.M (Privacy.MoussakaUnbound.stI s.1) :=
    fun s => verOk_stIUW hL s.1 s.2
  have hsR : ∀ s : RedKU kt, VerOk Privacy.Moussaka.pI L Arith.Moussaka.M
      (Privacy.MoussakaUnbound.stR s.1) := fun s => verOk_stRUW hL s.1 s.2.1
  have hm : ∀ π, AllQueriesSatisfy (m π) (· ∈ TPts Privacy.Moussaka.pI L Arith.Moussaka.M) :=
    fun π => allQueriesSatisfy_bind
      (gameA_onT (fun s : IssWU => Privacy.MoussakaUnbound.stI s.1) hsI
        (allQ_normJ (le_of_lminU hL) _ _ π (allQ_map_normTQU _ _)) π.fwd) fun _ =>
        allQueriesSatisfy_bind (gameA_onT (fun s : RedKU kt => Privacy.MoussakaUnbound.stR s.1) hsR
          (allQ_normJ (le_of_lminU hL) _ _ π (allQ_map_normTQU _ _)) π.fwd)
          fun _ => allQueriesSatisfy_pure _ _
  have hbr := pr_tables_eq_roP m hm ev
  rw [pr_eq_toReal_prU] at hbr
  have hfin : Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (m π)).run' ∅}[ev π r] ≠ ⊤ :=
    ne_top_of_le_ne_top (epsRomUP_ne_top _ _ hqE) hrom'
  rw [← (ENNReal.toReal_eq_toReal_iff' (ne_top_of_le_ne_top ENNReal.one_ne_top
    (Prob.prU_le_one _)) hfin).1 hbr] at hrom'
  refine (Prob.prU_mono fun z hz => ?_).trans hrom'
  -- on the tables, the bad event is the game's
  obtain ⟨hacc, hfr, hne⟩ := hz
  show ev z.2.2.1.2 (runT (tabP z.1.1 z.1.2 z.2) (m z.2.2.1.2))
  rw [runT_eq_eval, heval]
  rcases hop : runT (ansQ z.1.1 z.1.2 z.2) (oa a) with ⟨req, ci⟩ | ⟨S', req, ci, cr, cd⟩
  · rw [hop] at hacc hfr
    have hw : WfIU (stOfI req ci) := hfr.1
    have ho : outIU (.issue req ci) = (toBA (req.drop uovM), (⟨_, hw⟩, ())) := by
      simp only [outIU, dite_eq_left hw]
    have hacc' := (verILUX_eqP _ _ _).symm.trans hacc.2.2
    exact Or.inl (game_badUP (mousUPI true) (mousUPR true) (fun s : IssWU => Privacy.MoussakaUnbound.stI s.1)
      outIU (fun s w => IssueRel s.1 (SpecRel.uIssueWitOf s.1.ctxIss w))
      (oa a) z.1.1 z.1.2 z.2 (p₁ a) (p₂ a) (by rw [hop, ho]; rfl) (by rw [hop, ho]; exact hacc')
      (fun w hw' => by rw [hop] at hw' ⊢; rw [ho] at hw'; exact hw') hne)
  · rw [hop] at hacc hfr
    have hw : WfRU (stOfR S' req ci cr cd) ∧ KeysBy kt (toBound (stOfR S' req ci cr cd)) :=
      ⟨hfr.1, hfr.2⟩
    have ho : outRU kt (.redeem S' req ci cr cd) = (toBA (req.drop nfBytes), (⟨_, hw⟩, ())) := by
      simp only [outRU, dite_eq_left hw]
    have hacc' := (verRLUX_eqP _ _ _).symm.trans hacc.2.2.2
    exact Or.inr (game_badUP (mousUPI true) (mousUPR true)
      (fun s : RedKU kt => Privacy.MoussakaUnbound.stR s.1) (outRU kt)
      (fun s w => RedeemRel s.1 (SpecRel.uRedeemWitOf s.1.ctxIss s.1.ctxRed w))
      (oa a) z.1.1 z.1.2 z.2 (p₁ a) (p₂ a) (by rw [hop, ho]; rfl) (by rw [hop, ho]; exact hacc')
      (fun w hw' => by rw [hop] at hw' ⊢; rw [ho] at hw'; exact hw') hne)

end Plain

end VoleMole.Theft.MoussakaUnbound
