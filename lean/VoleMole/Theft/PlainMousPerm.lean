import VoleMole.Theft.PlainMousJointP
import VoleMole.Theft.PlainMousRedirect
import VoleMole.Theft.PlainRataPerm

/-!
# Redemption non-malleability with `ROM/`'s plain extraction, permutation rows and inverse queries

The Moussaka counterpart of `Theft/PlainRataPerm.lean` (`docs/security/moussaka.md` §5.3):
`noRedirect_lean_rom` (`Theft/PlainMousRedirect.lean`, function rows, forward queries) restated
with **permutation rows** (`ZKRow.perm`) and an adversary over `specP` with **forward and inverse**
cipher queries (`ansQ`).

* **`eRomMP`**: `eRomM` on the cells the queries determine (`toIC π`).
* `game_badMP`: on the tables, a bad output of `PlainSEL` is a bad output of `ROM/`'s game for the
  jointly normalized prover (`normJ (mousPI true) (mousPR true) π`).
* **`plainSEL_romMP`**: `PlainSEL` for `eRomMP` against `QBudP q q_E`, for `FreshK kt`, with the
  error `epsRomMP q q_E (totK Moussaka.M q)` of `moussaka_sim_joint_leanP` with `m = 2`.
* `progQIPm`, `progQRPm`, `qBudP_redQm`: the patches (forward-only) and the reduction's budget.
* **`noRedirect_lean_romP`**: redemption non-malleability with permutation rows and inverse
  queries, with the extractor's read budget as the hypothesis `hX`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads VoleMole.EndToEnd
open VoleMole.Spec VoleMole.Spec.Moussaka

variable {L : ℕ}

/-! ## The straight-line extractor on the cells of the queries -/

/-- **`ROM/`'s straight-line extractor with inverse queries** (Moussaka): `eRomM` on the cells the
queries determine (`toIC π`), with the permutations' forward rows. -/
noncomputable def eRomMP : Option (IssueInstance × Bytes) → Option (RedeemInstance × Bytes) → MOp →
    List DomP → Tab3 → Tab3 → (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M → Bytes :=
  fun p₁ p₂ op qs g₁ g₂ b =>
    eRomM p₁ p₂ op (qs.map (toIC b.1.2)) g₁ g₂ ((b.1.1, Ratatouille.fnRows b.1.2), b.2)

/-! ## On the tables, the bad event is the game's -/

section Bad

variable {ι : Type}

set_option maxHeartbeats 4000000 in
/-- **On the tables, a bad output of `PlainSEL` is a bad output of `ROM/`'s game** (Moussaka,
permutation model). -/
theorem game_badMP (pN pR' : Params) (stF : ι → Statement) (out : MOp → ByteArray × (ι × Unit))
    (Wit : ι → (ℕ → Arith.GF128) → Prop) (oa : OracleComp specP MOp)
    (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M))
    (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes))
    (hfd : Hit.Mous.fd (runT (ansQ g₁ g₂ t) oa) =
      (stF (out (runT (ansQ g₁ g₂ t) oa)).2.1, (out (runT (ansQ g₁ g₂ t) oa)).1))
    (hacc : (verRO Privacy.Moussaka.pI (hbX t.2.2) (stF (out (runT (ansQ g₁ g₂ t) oa)).2.1)
      (out (runT (ansQ g₁ g₂ t) oa)).1 (shOf t)).accept = true)
    (hW : ∀ w, Wit (out (runT (ansQ g₁ g₂ t) oa)).2.1 w →
      RelOp (runT (ansQ g₁ g₂ t) oa) (witOfCandM (runT (ansQ g₁ g₂ t) oa) w))
    (hne : ¬ RelOp (runT (ansQ g₁ g₂ t) oa)
      (eRomMP p₁ p₂ (runT (ansQ g₁ g₂ t) oa) (qlog (ansQ g₁ g₂ t) oa) g₁ g₂ t.2)) :
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
  apply relOp_pickM
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
one redemption output (`moussaka_sim_joint_leanP` with `m = 2`). -/
noncomputable def epsRomMP (q : Kind → ℕ) (qE nG : ℕ) : ℝ≥0∞ :=
  (q .h21 + 2) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 2) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 * q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 2) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    chainHitEpsCombSim q Arith.Moussaka.M 2 + stmtBindEpsSim q 2 + 2 * failEpsP q qE

/-- The error is finite for fewer than `2¹²⁸ − 4607` cipher queries. -/
lemma epsRomMP_ne_top (q : Kind → ℕ) {qE : ℕ} (nG : ℕ) (hqE : qE + 4607 < 2 ^ 128) :
    epsRomMP q qE nG ≠ ⊤ := by
  have h1 : pE qE ≠ ⊤ := pE_ne_top (by omega)
  have h2 : pE (qE + 4607) ≠ ⊤ := pE_ne_top hqE
  simp [epsRomMP, chainHitEpsCombSim, chainHitEpsSim, stmtBindEpsSim, failEpsP, openHashEps,
    ladderEps, ENNReal.mul_eq_top, ENNReal.div_eq_top, h1, h2]

lemma verILX_eqP (x : IssueInstance) (π : Bytes)
    (t : ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :
    verILX hbX x π t = (verRO Privacy.Moussaka.pI (hbX t.2.2) (Privacy.Moussaka.stI x) (toBA π)
      (shOf t)).accept := rfl

lemma verRLX_eqP (x : RedeemInstance) (π : Bytes)
    (t : ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :
    verRLX hbX x π t = (verRO Privacy.Moussaka.pI (hbX t.2.2) (Privacy.Moussaka.stR x) (toBA π)
      (shOf t)).accept := rfl

lemma allQ_map_normTQM {β : Type} (f : MOp → β) (oa : OracleComp specP MOp) :
    AllQueriesSatisfy (f <$> normTQ Privacy.Moussaka.pI L Arith.Moussaka.M oa)
      (OnTQ Privacy.Moussaka.pI L Arith.Moussaka.M) := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind (allQueriesSatisfy_normTQ _) fun _ => allQueriesSatisfy_pure _ _

lemma le_of_lrom (hL : Lrom ≤ L) : 49 ≤ L := le_trans (by decide) hL

set_option maxHeartbeats 800000 in
/-- **Plain extraction for the redirect game from `ROM/`'s permutation-model bound** (Moussaka,
permutation rows, inverse queries, `M = Moussaka.M`, `L ≥ 8193`): `PlainSEL` holds for `eRomMP`
against the last stages within `QBudP q qE`, for the freshness `FreshK kt`, with the error
`epsRomMP q qE (totK Moussaka.M q)`. -/
theorem plainSEL_romMP (kt : Bytes → UOVKey) (hL : Lrom ≤ L) (q : Kind → ℕ) {qE : ℕ}
    (hqE : qE + 4607 < 2 ^ 128) :
    PlainSEL ansQ (AccOp (verILX hbX) (verRLX hbX)) (FreshK kt) RelOp
      (eRomMP (L := L)) (QBudP q qE) (epsRomMP q qE (totK Arith.Moussaka.M q)).toReal := by
  classical
  intro α _ _ p₁ p₂ oa hoa
  rw [pr_eq_toReal_prU]
  refine ENNReal.toReal_mono (epsRomMP_ne_top _ _ hqE) (Prob.prU_prod_le_right _ fun a => ?_)
  -- the normalized adversary as the provers, and the joint game
  set N := normTQ Privacy.Moussaka.pI L Arith.Moussaka.M (oa a)
  set PI := outIM <$> N
  set PR := outRM kt <$> N
  let m : PTable → OracleComp spec (Out ((IssW × Unit) × QueryLog specIC) ×
      Out ((RedK kt × Unit) × QueryLog specIC)) := fun π =>
    gameA CrtGen.tables (fun s : IssW => Privacy.Moussaka.stI s.1)
        (normJ (mousPI true) (mousPR true) π PI) π.fwd >>= fun r₁ =>
      gameA CrtGen.tables (fun s : RedK kt => Privacy.Moussaka.stR s.1)
        (normJ (mousPI true) (mousPR true) π PR) π.fwd >>= fun r₂ => pure (r₁, r₂)
  let ev : PTable → Out ((IssW × Unit) × QueryLog specIC) ×
      Out ((RedK kt × Unit) × QueryLog specIC) → Prop := fun π r =>
    (r.1.2.2.accept = true ∧ ¬ @Extracted (icPrg π.fwd.cipher) _
      (Privacy.Moussaka.stI (stOut r.1).1)
      (fun _ w => Privacy.Moussaka.IssueRelW (stOut r.1).1
        (SpecRel.issueWitOf (stOut r.1).1.ctxIss w)) r.1) ∨
    (r.2.2.2.accept = true ∧ ¬ @Extracted (icPrg π.fwd.cipher) _
      (Privacy.Moussaka.stR (stOut r.2).1)
      (fun _ w => Privacy.Moussaka.RedeemRelW (stOut r.2).1
        (SpecRel.redeemWitOf (stOut r.2).1.nf (stOut r.2).1.ctxIss (stOut r.2).1.ctxRed w)) r.2)
  have heval : ∀ π g, evalWithAnswerFn (QueryImpl.ofFn g) (m π) =
      (evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (fun s : IssW => Privacy.Moussaka.stI s.1)
            (normJ (mousPI true) (mousPR true) π PI) π.fwd),
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (fun s : RedK kt => Privacy.Moussaka.stR s.1)
            (normJ (mousPI true) (mousPR true) π PR) π.fwd)) := by
    intro π g
    simp only [m, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  -- `ROM/`'s bound on the joint game
  have hb := qBudPT_normTQ (p := Privacy.Moussaka.pI) (L := L) (M := Arith.Moussaka.M) (hoa a)
  have hrom := moussaka_sim_joint_leanP kt PI (fun _ : Unit => PI) PR (fun _ : Unit => PR)
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
      epsRomMP q qE (totK Arith.Moussaka.M q) := by
    refine hrom.trans (le_of_eq ?_)
    simp only [Finset.card_univ, Fintype.card_unit, epsRomMP]
    norm_num
    ring
  -- the joint game queries only table points: the tables are the lazy oracle
  have hsI : ∀ s : IssW, VerOk Privacy.Moussaka.pI L Arith.Moussaka.M (Privacy.Moussaka.stI s.1) :=
    fun s => verOk_stIW hL s.1 s.2
  have hsR : ∀ s : RedK kt, VerOk Privacy.Moussaka.pI L Arith.Moussaka.M
      (Privacy.Moussaka.stR s.1) := fun s => verOk_stRW hL s.1 s.2.1
  have hm : ∀ π, AllQueriesSatisfy (m π) (· ∈ TPts Privacy.Moussaka.pI L Arith.Moussaka.M) :=
    fun π => allQueriesSatisfy_bind
      (gameA_onT (fun s : IssW => Privacy.Moussaka.stI s.1) hsI
        (allQ_normJ (le_of_lrom hL) _ _ π (allQ_map_normTQM _ _)) π.fwd) fun _ =>
        allQueriesSatisfy_bind (gameA_onT (fun s : RedK kt => Privacy.Moussaka.stR s.1) hsR
          (allQ_normJ (le_of_lrom hL) _ _ π (allQ_map_normTQM _ _)) π.fwd)
          fun _ => allQueriesSatisfy_pure _ _
  have hbr := pr_tables_eq_roP m hm ev
  rw [pr_eq_toReal_prU] at hbr
  have hfin : Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (m π)).run' ∅}[ev π r] ≠ ⊤ :=
    ne_top_of_le_ne_top (epsRomMP_ne_top _ _ hqE) hrom'
  rw [← (ENNReal.toReal_eq_toReal_iff' (ne_top_of_le_ne_top ENNReal.one_ne_top
    (Prob.prU_le_one _)) hfin).1 hbr] at hrom'
  refine (Prob.prU_mono fun z hz => ?_).trans hrom'
  -- on the tables, the bad event is the game's
  obtain ⟨hacc, hfr, hne⟩ := hz
  show ev z.2.2.1.2 (runT (tabP z.1.1 z.1.2 z.2) (m z.2.2.1.2))
  rw [runT_eq_eval, heval]
  rcases hop : runT (ansQ z.1.1 z.1.2 z.2) (oa a) with ⟨req, ci⟩ | ⟨S', req, ci, cr, cd⟩
  · rw [hop] at hacc hfr
    have hw : Hit.Mous.WfI (stOfI req ci) := hfr.1.1
    have ho : outIM (.issue req ci) = (toBA (req.drop uovM), (⟨_, hw⟩, ())) := by
      simp only [outIM, dite_eq_left hw]
    have hacc' := (verILX_eqP _ _ _).symm.trans hacc.2.2
    exact Or.inl (game_badMP (mousPI true) (mousPR true) (fun s : IssW => Privacy.Moussaka.stI s.1)
      outIM (fun s w => Privacy.Moussaka.IssueRelW s.1 (SpecRel.issueWitOf s.1.ctxIss w))
      (oa a) z.1.1 z.1.2 z.2 (p₁ a) (p₂ a) (by rw [hop, ho]; rfl) (by rw [hop, ho]; exact hacc')
      (fun w hw' => by rw [hop] at hw' ⊢; rw [ho] at hw'; exact hw'.1) hne)
  · rw [hop] at hacc hfr
    have hw : Hit.Mous.WfR (stOfR S' req ci cr cd) ∧ KeysBy kt (stOfR S' req ci cr cd) :=
      ⟨hfr.1.1, hfr.2⟩
    have ho : outRM kt (.redeem S' req ci cr cd) = (toBA (req.drop nfBytes), (⟨_, hw⟩, ())) := by
      simp only [outRM, dite_eq_left hw]
    have hacc' := (verRLX_eqP _ _ _).symm.trans hacc.2
    exact Or.inr (game_badMP (mousPI true) (mousPR true)
      (fun s : RedK kt => Privacy.Moussaka.stR s.1) (outRM kt)
      (fun s w => Privacy.Moussaka.RedeemRelW s.1
        (SpecRel.redeemWitOf s.1.nf s.1.ctxIss s.1.ctxRed w))
      (oa a) z.1.1 z.1.2 z.2 (p₁ a) (p₂ a) (by rw [hop, ho]; rfl) (by rw [hop, ho]; exact hacc')
      (fun w hw' => by rw [hop] at hw' ⊢; rw [ho] at hw'; exact hw'.1) hne)

end Plain

/-! ## Redemption non-malleability with permutation rows -/

open VoleMole.Privacy.Moussaka

/-- **The issuance simulator's patch, by forward queries in the permutation model.** -/
noncomputable def progQIPm (x : IssueInstance) (c : SimCoins pI) :
    OracleComp specP (K2 pI → Option (ZK.Sim.Bytes 16)) :=
  liftP (progQIm x c)

/-- **The redemption simulator's patch, by forward queries in the permutation model.** -/
noncomputable def progQRPm (x : RedeemInstance) (c : SimCoins pR) :
    OracleComp specP (K2 pI → Option (ZK.Sim.Bytes 16)) :=
  liftP (progQRm x c)

/-- The patches' queries, from the simulated pair. -/
noncomputable def logQIPm (p : Option (IssueInstance × Bytes)) (g₁ g₂ : Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M) : List DomP :=
  (logQIm p g₁ g₂ b).map embIC

noncomputable def logQRPm (p : Option (RedeemInstance × Bytes)) (g₁ g₂ : Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L Arith.Moussaka.M) : List DomP :=
  (logQRm p g₁ g₂ b).map embIC

lemma hpatchIPm (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) (d : DomP) :
    ansQ g₁ g₂ (leanProgIX hbX x c t) d =
      patch2P pI (runT (ansQ g₁ g₂ t) (progQIPm x c)) d (ansQ g₁ g₂ t d) := by
  rcases d with d | c'
  · rw [progQIPm, runT_liftP]
    exact hpatchIm x c g₁ g₂ t (.inl d)
  · rfl

lemma hpatchRPm (x : RedeemInstance) (c : SimCoins pR) (g₁ g₂ : Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) (d : DomP) :
    ansQ g₁ g₂ (leanProgRX hbX x c t) d =
      patch2P pI (runT (ansQ g₁ g₂ t) (progQRPm x c)) d (ansQ g₁ g₂ t d) := by
  rcases d with d | c'
  · rw [progQRPm, runT_liftP]
    exact hpatchRm x c g₁ g₂ t (.inl d)
  · rfl

lemma hpreIPm (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3)
    (t t' : ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) (h : t'.2 = t.2) :
    runT (ansQ g₁ g₂ t') (progQIPm x c) = runT (ansQ g₁ g₂ t) (progQIPm x c) := by
  rw [progQIPm, runT_liftP, runT_liftP]
  exact hpreIm x c g₁ g₂ t t' h

lemma hlogIPm (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) :
    qlog (ansQ g₁ g₂ t) (progQIPm x c) =
      logQIPm (pairO (some x) (simI' (leanSim pI) x c)) g₁ g₂ t.2 := by
  rw [progQIPm, qlog_liftP, hlogIm]
  rfl

lemma hlogRPm (x : RedeemInstance) (c : SimCoins pR) (g₁ g₂ : Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) :
    qlog (ansQ g₁ g₂ t) (progQRPm x c) =
      logQRPm (pairO (some x) (simR' (leanSim pR) x c)) g₁ g₂ t.2 := by
  rw [progQRPm, qlog_liftP, hlogRm]
  rfl

/-- **The reduction's budget in the permutation model**: the two patches' forward queries, then
the adversary's. -/
theorem qBudP_redQm {α : Type} {q : Kind → ℕ} {qE : ℕ} {oa : OracleComp specP α}
    (h : QBudP q qE oa) (x₁ : Option IssueInstance) (c₁ : SimCoins pI)
    (x₂ : Option RedeemInstance) (c₂ : SimCoins pR) :
    QBudP (q + Ratatouille.qPre + Ratatouille.qPre) (qE + verifyCellBound pR + verifyCellBound pI)
      (redQ progQIPm (patch2P pI) progQRPm (patch2P pI) x₁ c₁ x₂ c₂ oa) := by
  have h₂ := Ratatouille.qBudP_progQO (fun x c => qBudP_liftP (qBud_progQRm x c)) x₂ c₂
  have h₁ := Ratatouille.qBudP_progQO (fun x c => qBudP_liftP (qBud_progQIm x c)) x₁ c₁
  refine ⟨?_, ?_⟩
  · refine IsKindQueryBoundP.mono (isKindQueryBoundP_bind h₂.1 fun m₂ =>
      isKindQueryBoundP_bind h₁.1 fun m₁ => isQueryBound_simP _ h.1) fun k => ?_
    simp only [Pi.add_apply]
    omega
  · refine (isQueryBoundP_bind h₂.2 fun m₂ _ => isQueryBoundP_bind h₁.2 fun m₁ _ =>
      isQueryBoundP_simP _ h.2).mono ?_
    omega

/-- **The extractor**: `ROM/`'s straight-line extractor `eRomMP` on the reduction's queries. -/
noncomputable def extRomMP (q : Kind → ℕ) (qE : ℕ) :
    Moussaka.Ext Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)) :=
  extL ansQ (QBudP q qE) logQIPm logQRPm eRomMP

set_option maxHeartbeats 1000000 in
/-- **Redemption non-malleability with permutation rows, inverse cipher queries and `ROM/`'s plain
extraction** (Moussaka, one token): as `noRedirect_lean_rom`, with AES as uniformly random
permutations (`ZKRow.perm`), `M = Moussaka.M`, `L ≥ 8193`, a `HitWf` adversary whose output
redemptions have the Anchor keys of `kt` and whose last stage is the run on the tables of an
oracle computation over `specP` with at most `q k` hash queries of kind `k` and `q_E` cipher
queries, forward or inverse (`hA`; no total hash budget), and `ROM/`'s straight-line extractor on
the records of its queries (`extRomMP`):

    Pr[Bad] ≤ εROPm(pI; q') + εROPm(pR; q') + δ_R + ε_rom
      + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

`ε_rom = epsRomMP q₀ (q_E + cells(pR) + cells(pI)) (totK Moussaka.M q₀)`, `q₀ = q + 2·qPre`,
`q' = (q h3 + x₃, q h5 + x₅ + 936, q_E + x_E + 9214)` with the extractor's read budget `hX`. -/
theorem noRedirect_lean_romP
    (A : Thief Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
    (hw : Hit.Mous.HitWf A) {kt : Bytes → UOVKey} (hk : KeysOut A kt) (hL : Lrom ≤ L)
    {q : Kind → ℕ} {qE x3 x5 xE : ℕ}
    (hqE : qE + verifyCellBound pR + verifyCellBound pI + 4607 < 2 ^ 128)
    (hA : ∀ o₁ o₂, AdmL (QBudP q qE) ansQ (A.out o₁ o₂))
    (hX : ∀ o₁ o₂, StageBudgetX (extRomMP q qE (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE) :
    pr _ (nmReal A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extRomMP q qE)) ≤
      ZKRow.εz (Equiv.Perm Blk) pI (q .h3 + x3) (q .h5 + x5 + 936) (qE + xE + 9214) +
        ZKRow.εz (Equiv.Perm Blk) pR (q .h3 + x3) (q .h5 + x5 + 936) (qE + xE + 9214) +
        pr _ (deltaR A (leanPRX hbX) (leanSim pI) (leanProgIX hbX)) +
        ((epsRomMP (q + Ratatouille.qPre + Ratatouille.qPre)
          (qE + verifyCellBound pR + verifyCellBound pI)
          (totK Arith.Moussaka.M (q + Ratatouille.qPre + Ratatouille.qPre))).toReal +
          Hit.epsHit (q .mu) (q .h21) (q .h22)) +
        owAdv A.ci A.cr (inverter A (extRomMP q qE) (leanSim pI) (leanProgIX hbX) (leanSim pR)
          (leanProgRX hbX)) := by
  have hSB : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) (q .h3) (q .h5) qE := fun o₁ o₂ => by
    obtain ⟨oa, hb, hF⟩ := hA o₁ o₂
    rw [hF]
    exact stageBudgetX_runTQ hb
  have hAH : ∀ F : Tab3 → Tab3 → ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M) → MOp,
      AdmL (QBudP q qE) ansQ F →
      Hit.AdmHit (R := Equiv.Perm Blk) (p := pI) (L := L) (M := Arith.Moussaka.M) (G := Tab3)
        (q .mu) (q .h21) (q .h22) F := by
    rintro F ⟨oa, hb, rfl⟩
    exact admHit_runTQ hb
  have hL' : Hit.Mous.Lmin ≤ L := lmin_le_lrom.trans hL
  have hplain := plainSEL_romMP (L := L) kt hL (q + Ratatouille.qPre + Ratatouille.qPre) hqE
  have hmv0 : ProgMoves (simI' (leanSim pI)) (leanProgIX hbX) (simR' (leanSim pR))
      (leanProgRX hbX) (AccOp (verILX hbX) (verRLX hbX)) Hit.Mous.FreshOk
      (AdmL (QBudP q qE) ansQ) (Hit.epsHit (q .mu) (q .h21) (q .h22)) :=
    progMoves_of_ev (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (accOp_movesX (R := Equiv.Perm Blk) (X := XTab L Arith.Moussaka.M) hbX)
      ((Hit.Mous.progEv_hit hL' (q .mu) (q .h21) (q .h22)).mono hAH)
  have hmv : ProgMoves (simI' (leanSim pI)) (leanProgIX hbX) (simR' (leanSim pR)) (leanProgRX hbX)
      (AccOp (verILX hbX) (verRLX hbX)) (FreshK kt) (AdmL (QBudP q qE) ansQ)
      (Hit.epsHit (q .mu) (q .h21) (q .h22)) :=
    ProgMoves.fresh_mono hmv0 fun _ _ _ h => h.1
  have hse := weakSE2_of_plainL progQIPm (patch2P pI) progQRPm (patch2P pI) logQIPm logQRPm
    hplain hmv (fun _ _ _ => rfl) (fun _ _ _ => rfl) hpatchIPm hpatchRPm
    (fun x c g₁ g₂ s s' h => hpreIPm x c g₁ g₂ s s' h) hlogIPm hlogRPm (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) fun oa x₁ c₁ x₂ c₂ h => qBudP_redQm h x₁ c₁ x₂ c₂
  exact noRedirect_okK (CI := SimCoins pI) (CR := SimCoins pR) A (verILX hbX) (verRLX hbX)
    (extRomMP q qE) (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX) (leanPIX hbX)
    (leanPRX hbX) hw hk (leanPIX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (leanPRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (distI_budgetX' hbX A _ hbX_wf hSB hX) (distR_budgetX' hbX A _ hSB hX) hse hA

end VoleMole.Theft.Moussaka
