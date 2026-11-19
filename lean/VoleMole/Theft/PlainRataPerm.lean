import VoleMole.Theft.PlainEagerP
import VoleMole.Theft.PlainRomP

/-!
# No theft with `ROM/`'s plain extraction, permutation rows and inverse cipher queries (Ratatouille)

`noTheft_lean_rom` (`Theft/PlainRataRom.lean`) has function rows (AES as random functions, the
PRF view) and an adversary that makes forward cipher queries only. Here the theorem is proved
with **permutation rows** (`R = Equiv.Perm Blk`, AES as uniformly random permutations,
`ZKRow.perm` for the zero-knowledge hops) and an adversary whose last stage is an oracle
computation over `ROM/`'s permutation-model oracle `specP`, with **forward and inverse** cipher
queries (`ansQ`, `Theft/PlainPerm.lean`):

* **`eRomP A`**: `ROM/`'s straight-line extractor on the cells the adversary's cipher queries
  determine (`toIC π`: an inverse query `(k, y)` gives the record `(k, π_k⁻¹(y), y)`), i.e. `eRom A`
  on the list mapped by `toIC`.
* `game_badP`: on the tables, a bad output of `PlainSEL` is a bad output of `ROM/`'s game for the
  prover `normJ (rataPI true) (rataPS true) π (out <$> normTQ oa)` (the joint normalization of
  `ROM/SimPermJoint.lean`, whose cipher log is the list of those records, `cLog_normJ`).
* **`plainSEL_romP`**: `PlainSEL` for `eRomP A` against `QBudP q q_E` (per-kind hash budgets and
  `q_E` cipher queries, forward or inverse; no total budget: `totK uovM q`, `qBudPT_normTQ`), with
  the error `epsRomP q q_E (totK uovM q)` of `ratatouille_sim_joint_leanP` with `m = 2`: the
  permutation model's failure terms `failEpsP` and the two `H₄` queries per `H₂¹` query in the
  `2⁻⁴⁴⁸` term.
* `progQIP`, `progQSP` (the patches, forward-only, `liftP`), `qBudP_redQ`: the programming step's
  reduction is within `QBudP (q + 2·qPre) (q_E + cells(pS) + cells(pI))`.
* **`noTheft_lean_romP`**: no theft with permutation rows, inverse queries and `ROM/`'s plain
  extraction, with the extractor's read budget as the hypothesis `hX` (as `noTheft_lean_rom`).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## The straight-line extractor on the cells of the queries -/

namespace Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.EndToEnd

variable {L M : ℕ} {G S : Type}

/-- The function rows of a permutation table. -/
def fnRows (π : PTable) : Blk → Blk → Blk := fun k => ⇑(π k)

lemma ctOf_fnRows (π : PTable) : ctOf (fnRows π) = π.fwd := rfl

/-- **`ROM/`'s straight-line extractor with inverse queries**: `eRom A` on the cells the queries
determine (`toIC π`), with the permutations' forward rows. -/
noncomputable def eRomP (A : Thief Sizes.labelRows G S) :
    Option (IssueInstance × IssueProof Sizes.labelRows) →
      Option (SpendInstance × SpendProof Sizes.labelRows) → Op Sizes.labelRows → List DomP →
      Tab3 → Tab3 → (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L M → Wit :=
  fun p₁ p₂ op qs g₁ g₂ b =>
    eRom A p₁ p₂ op (qs.map (toIC b.1.2)) g₁ g₂ ((b.1.1, fnRows b.1.2), b.2)

end Ratatouille

/-! ## On the tables, the bad event is the game's -/

section Bad

open VoleMole.Spec.Ratatouille VoleMole.EndToEnd
open VoleMole.Privacy.Ratatouille (pI pS)

variable {L M : ℕ} {ι : Type}

lemma recP_hash_neP {p : Params} (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M)) {k : Kind}
    (h3 : k ≠ .h3) (h5 : k ≠ .h5) (h23 : k ≠ .h23) : (recP g₁ g₂ t).hash k = (hbX t.2.2).hash k :=
  funext fun b => recP_other g₁ g₂ t h3 h5 h23 b

variable (A : Ratatouille.Thief Sizes.labelRows Tab3 (ShX (Equiv.Perm Blk) pI (XTab L M)))

set_option maxHeartbeats 4000000 in
/-- **On the tables, a bad output of `PlainSEL` is a bad output of `ROM/`'s game** (permutation
model): if the operation is accepted by the Lean verifier and `eRomP` finds no witness, the game
run on the tables, with the jointly normalized adversary as the prover, accepts and its extraction
fails. -/
theorem game_badP (pN pR : Params) (stF : ι → Statement)
    (out : Op Sizes.labelRows → ByteArray × (ι × Unit))
    (Wit : ι → (ℕ → Arith.GF128) → Prop) (oa : OracleComp specP (Op Sizes.labelRows))
    (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) pI (XTab L M))
    (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows))
    (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows))
    (hfd : Hit.Rata.fd A (runT (ansQ g₁ g₂ t) oa) =
      (stF (out (runT (ansQ g₁ g₂ t) oa)).2.1, (out (runT (ansQ g₁ g₂ t) oa)).1))
    (hacc : (verRO pI (hbX t.2.2) (stF (out (runT (ansQ g₁ g₂ t) oa)).2.1)
      (out (runT (ansQ g₁ g₂ t) oa)).1 (shOf t)).accept = true)
    (hW : ∀ w, Wit (out (runT (ansQ g₁ g₂ t) oa)).2.1 w →
      Ratatouille.RelOp A (runT (ansQ g₁ g₂ t) oa) (Ratatouille.witOfCand w))
    (hne : ¬ Ratatouille.RelOp A (runT (ansQ g₁ g₂ t) oa)
      (Ratatouille.eRomP A p₁ p₂ (runT (ansQ g₁ g₂ t) oa) (qlog (ansQ g₁ g₂ t) oa) g₁ g₂ t.2)) :
    (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
        (normJ pN pR t.2.1.2 (out <$> normTQ pI L M oa)) (PTable.fwd t.2.1.2))).2.2.accept = true ∧
      ¬ @Extracted (icPrg (PTable.fwd t.2.1.2).cipher) _
        (stF (stOut (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
          (normJ pN pR t.2.1.2 (out <$> normTQ pI L M oa)) (PTable.fwd t.2.1.2)))))
        (fun _ w => Wit (stOut (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t))
          (gameA CrtGen.tables stF (normJ pN pR t.2.1.2 (out <$> normTQ pI L M oa))
            (PTable.fwd t.2.1.2)))) w)
        (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
          (normJ pN pR t.2.1.2 (out <$> normTQ pI L M oa)) (PTable.fwd t.2.1.2))) := by
  classical
  set o := runT (ansQ g₁ g₂ t) oa with ho
  set π : PTable := t.2.1.2 with hπ
  obtain ⟨hrunN, hqN⟩ := normTQ_ansQ g₁ g₂ t oa
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join (tabP g₁ g₂ t) (PTable.fwd π)))
      (normJ pN pR π (out <$> normTQ pI L M oa)) = out o := by
    rw [evalWithAnswerFn_normJ, ← runT_eq_eval, runT_map]
    exact congrArg out hrunN
  have hJ : cipherLog (tableQueryLog (normJ pN pR π (out <$> normTQ pI L M oa))
      (join (tabP g₁ g₂ t) (PTable.fwd π))) =
      cLog (Ratatouille.ctOf (Ratatouille.fnRows π)) ((qlog (ansQ g₁ g₂ t) oa).map (toIC π)) := by
    rw [normJ_map, tableQueryLog_map', tableQueryLog_eq_qlog, cipherLog_map]
    show cLog (PTable.fwd π) (qlog (join (tabP g₁ g₂ t) (PTable.fwd π)) (normJ pN pR π (normTQ pI L M oa))) = _
    rw [cLog_normJ]
    show cLog (PTable.fwd π) ((qlog (ansQ g₁ g₂ t) (normTQ pI L M oa)).map (toIC π)) = _
    rw [hqN, cLog_map_filter _ _ fun c => decide_eq_true (show OnTQ pI L M (.inr c) from trivial)]
    rfl
  have hivP : ivOf (Hashes.ofTable (tabP g₁ g₂ t)) ⟨(stF (out o).2.1).params, (out o).1⟩
      ((stF (out o).2.1).mu1 (Hashes.ofTable (tabP g₁ g₂ t))) =
      ivOf (hbX t.2.2) ⟨(stF (out o).2.1).params, (out o).1⟩ ((stF (out o).2.1).mu1 (hbX t.2.2)) := by
    rw [ofTable_tabP]
    exact ivOf_congr (recP_hash_neP _ _ _ (by decide) (by decide) (by decide))
      (recP_hash_neP _ _ _ (by decide) (by decide) (by decide))
      (recP_hash_neP _ _ _ (by decide) (by decide) (by decide)) _ _
  have hver : @verify (icPrg (PTable.fwd π).cipher) (Hashes.ofTable (tabP g₁ g₂ t)) CrtGen.tables
      (stF (out o).2.1) (out o).1 = verRO pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t) := by
    rw [ofTable_tabP]
    exact congrFun (@verify_agreeOff_h3 (icPrg (rowFn t.2.1.2)) _ _
      (Hashes.agreeOff_withTable _ _ _ _).symm CrtGen.tables _) _
  have hivV : (verRO pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t)).iv =
      ivOf (hbX t.2.2) ⟨(stF (out o).2.1).params, (out o).1⟩ ((stF (out o).2.1).mu1 (hbX t.2.2)) := by
    have hacc' : (@verify (icPrg (rowFn t.2.1.2)) (recV pI (hbX t.2.2) t.1 t.2.1.1) CrtGen.tables
        (stF (out o).2.1) (out o).1).accept = true := hacc
    obtain ⟨-, leaves, hrec, -⟩ := (@accept_iff (icPrg (rowFn t.2.1.2)) _ _ _ _).1 hacc'
    refine (@verify_iv_chal1 (icPrg (rowFn t.2.1.2)) _ _ _ _ hacc' leaves hrec).1.trans ?_
    exact ivOf_congr (recV_hash_ne _ _ _ (by decide) (by decide))
      (recV_hash_ne _ _ _ (by decide) (by decide)) (recV_hash_ne _ _ _ (by decide) (by decide)) _ _
  have hr := eval_gameA CrtGen.tables stF (normJ pN pR π (out <$> normTQ pI L M oa)) (PTable.fwd π)
    (tabP g₁ g₂ t)
  rw [hP, hJ, hver, hivP] at hr
  generalize evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t))
    (gameA CrtGen.tables stF (normJ pN pR π (out <$> normTQ pI L M oa)) (PTable.fwd π)) = R at hr ⊢
  set lg := cLog (Ratatouille.ctOf (Ratatouille.fnRows π)) ((qlog (ansQ g₁ g₂ t) oa).map (toIC π))
  have hS : stOut R = (out o).2.1 := by rw [hr]; rfl
  have hT : R.2.2 = verRO pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t) := by rw [hr]
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
  apply Ratatouille.relOp_eRom
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

open VoleMole.Spec.Ratatouille VoleMole.EndToEnd
open VoleMole.Privacy.Ratatouille (pI pS stI stS)

/-- **The error of `ROM/`'s simultaneous extraction in the permutation model** for one issuance and
one spend output (`ratatouille_sim_joint_leanP` with `m = 2`), for `q k` hash queries of kind
`k`, `qE` cipher queries (forward or inverse) and `nG` hash queries in all. -/
noncomputable def epsRomP (q : Kind → ℕ) (qE nG : ℕ) : ℝ≥0∞ :=
  (q .h21 + 2) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 2) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 * q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 2) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    chainHitEpsCombSim q Arith.Ratatouille.uovM 2 + stmtBindEpsSim q 2 + 2 * failEpsP q qE

lemma pE_ne_top {n : ℕ} (h : n < 2 ^ 128) : pE n ≠ ⊤ := by
  unfold pE
  exact ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 (Nat.sub_ne_zero_of_lt h))

/-- The error is finite for fewer than `2¹²⁸ − 4607` cipher queries. -/
lemma epsRomP_ne_top (q : Kind → ℕ) {qE : ℕ} (nG : ℕ) (hqE : qE + 4607 < 2 ^ 128) :
    epsRomP q qE nG ≠ ⊤ := by
  have h1 : pE qE ≠ ⊤ := pE_ne_top (by omega)
  have h2 : pE (qE + 4607) ≠ ⊤ := pE_ne_top hqE
  simp [epsRomP, chainHitEpsCombSim, chainHitEpsSim, stmtBindEpsSim, failEpsP, openHashEps,
    ladderEps, ENNReal.mul_eq_top, ENNReal.div_eq_top, h1, h2]

variable {L : ℕ}

lemma allQ_map_normTQ {β : Type} (f : Op Sizes.labelRows → β)
    (oa : OracleComp specP (Op Sizes.labelRows)) :
    AllQueriesSatisfy (f <$> normTQ pI L Arith.Ratatouille.uovM oa)
      (OnTQ pI L Arith.Ratatouille.uovM) := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind (allQueriesSatisfy_normTQ _) fun _ => allQueriesSatisfy_pure _ _

lemma leanVIRX_eqP (x : IssueInstance) (π : IssueProof Sizes.labelRows)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)) :
    Ratatouille.leanVIRX hbX x π t = (verRO pI (hbX t.2.2) (stI x) (Privacy.Ratatouille.bOf π)
      (shOf t)).accept := rfl

lemma leanVSRX_eqP (x : SpendInstance) (π : SpendProof Sizes.labelRows)
    (t : ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)) :
    Ratatouille.leanVSRX hbX x π t = (verRO pI (hbX t.2.2) (stS x) (Privacy.Ratatouille.bOf π)
      (shOf t)).accept := rfl

lemma le_of_lmin (hL : Hit.Rata.Lmin ≤ L) : 49 ≤ L := le_trans (by decide) hL

/-- **Plain extraction for the theft game from `ROM/`'s permutation-model bound** (Ratatouille,
permutation rows, inverse queries, `M = uovM`, `L ≥ Lmin`): `PlainSEL` holds for `eRomP A`
against the last stages within `QBudP q qE`, with the error `epsRomP q qE (totK uovM q)`. -/
theorem plainSEL_romP
    (A : Ratatouille.Thief Sizes.labelRows Tab3
      (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) (q : Kind → ℕ) {qE : ℕ} (hqE : qE + 4607 < 2 ^ 128) :
    PlainSEL ansQ (Ratatouille.AccOp A (Ratatouille.leanVIRX hbX) (Ratatouille.leanVSRX hbX))
      (Ratatouille.FreshOp A) (Ratatouille.RelOp A) (Ratatouille.eRomP A) (QBudP q qE)
      (epsRomP q qE (totK Arith.Ratatouille.uovM q)).toReal := by
  classical
  intro α _ _ p₁ p₂ oa hoa
  rw [pr_eq_toReal_prU]
  refine ENNReal.toReal_mono (epsRomP_ne_top _ _ hqE) (Prob.prU_prod_le_right _ fun a => ?_)
  -- the normalized adversary as the provers, and the joint game
  set N := normTQ pI L Arith.Ratatouille.uovM (oa a)
  set PI := Ratatouille.outI <$> N
  set PR := Ratatouille.outS A <$> N
  let m : PTable → OracleComp spec (Out ((IssueInstance × Unit) × QueryLog specIC) ×
      Out ((SpendK A.pk × Unit) × QueryLog specIC)) := fun π =>
    gameA CrtGen.tables stI (normJ (rataPI true) (rataPS true) π PI) π.fwd >>= fun r₁ =>
      gameA CrtGen.tables (stK A.pk) (normJ (rataPI true) (rataPS true) π PR) π.fwd >>= fun r₂ =>
        pure (r₁, r₂)
  let ev : PTable → Out ((IssueInstance × Unit) × QueryLog specIC) ×
      Out ((SpendK A.pk × Unit) × QueryLog specIC) → Prop := fun π r =>
    (r.1.2.2.accept = true ∧ ¬ @Extracted (icPrg π.fwd.cipher) _ (stI (stOut r.1))
      (fun _ w => IssueRel (stOut r.1) (SpecRel.issueWitOfR w)) r.1) ∨
    (r.2.2.2.accept = true ∧ ¬ @Extracted (icPrg π.fwd.cipher) _ (stK A.pk (stOut r.2))
      (fun _ w => SpendRel (stOut r.2).1 (SpecRel.spendWitOf w)) r.2)
  have heval : ∀ π g, evalWithAnswerFn (QueryImpl.ofFn g) (m π) =
      (evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables stI (normJ (rataPI true) (rataPS true) π PI) π.fwd),
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stK A.pk) (normJ (rataPI true) (rataPS true) π PR) π.fwd)) := by
    intro π g
    simp only [m, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  -- `ROM/`'s bound on the joint game
  have hb := qBudPT_normTQ (p := pI) (L := L) (M := Arith.Ratatouille.uovM) (hoa a)
  have hrom := ratatouille_sim_joint_leanP A.pk PI (fun _ : Unit => PI) PR (fun _ : Unit => PR)
    Finset.univ Finset.univ qE
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 hb.1.2)
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 hb.1.2) q
    (fun _ _ => (isQueryBound_map_iff _ _ _ _ _).2 hb.1.1)
    ((isQueryBound_map_iff _ _ _ _ _).2 hb.1.1)
    (fun _ _ => (isQueryBound_map_iff _ _ _ _ _).2 hb.1.1) (totK Arith.Ratatouille.uovM q)
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
      epsRomP q qE (totK Arith.Ratatouille.uovM q) := by
    refine hrom.trans (le_of_eq ?_)
    simp only [Finset.card_univ, Fintype.card_unit, epsRomP]
    norm_num
    ring
  -- the joint game queries only table points: the tables are the lazy oracle
  have hm : ∀ π, AllQueriesSatisfy (m π) (· ∈ TPts pI L Arith.Ratatouille.uovM) := fun π =>
    allQueriesSatisfy_bind (gameA_onT stI (fun x => verOk_stI hL x)
      (allQ_normJ (le_of_lmin hL) _ _ π (allQ_map_normTQ _ _)) π.fwd)
      fun _ => allQueriesSatisfy_bind (gameA_onT (stK A.pk) (fun s => verOk_stS hL s.1)
        (allQ_normJ (le_of_lmin hL) _ _ π (allQ_map_normTQ _ _)) π.fwd) fun _ =>
          allQueriesSatisfy_pure _ _
  have hbr := pr_tables_eq_roP m hm ev
  rw [pr_eq_toReal_prU] at hbr
  have hfin : Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (m π)).run' ∅}[ev π r] ≠ ⊤ :=
    ne_top_of_le_ne_top (epsRomP_ne_top _ _ hqE) hrom'
  rw [← (ENNReal.toReal_eq_toReal_iff' (ne_top_of_le_ne_top ENNReal.one_ne_top
    (Prob.prU_le_one _)) hfin).1 hbr] at hrom'
  refine (Prob.prU_mono fun z hz => ?_).trans hrom'
  -- on the tables, the bad event is the game's
  obtain ⟨hacc, -, hne⟩ := hz
  show ev z.2.2.1.2 (runT (tabP z.1.1 z.1.2 z.2) (m z.2.2.1.2))
  rw [runT_eq_eval, heval]
  rcases hop : runT (ansQ z.1.1 z.1.2 z.2) (oa a) with ⟨qq, tt, cc⟩ | ⟨qq, cc, rr⟩
  · rw [hop] at hacc
    have hacc' := (leanVIRX_eqP _ _ _).symm.trans hacc
    exact Or.inl (game_badP A (rataPI true) (rataPS true) stI Ratatouille.outI
      (fun x w => IssueRel x (SpecRel.issueWitOfR w))
      (oa a) z.1.1 z.1.2 z.2 (p₁ a) (p₂ a) (by rw [hop]; rfl) (by rw [hop]; exact hacc')
      (fun w hw => by rw [hop] at hw ⊢; exact hw) hne)
  · rw [hop] at hacc
    have hacc' := (leanVSRX_eqP _ _ _).symm.trans hacc
    exact Or.inr (game_badP A (rataPI true) (rataPS true) (stK A.pk) (Ratatouille.outS A)
      (fun s w => SpendRel s.1 (SpecRel.spendWitOf w))
      (oa a) z.1.1 z.1.2 z.2 (p₁ a) (p₂ a) (by rw [hop]; rfl) (by rw [hop]; exact hacc')
      (fun w hw => by rw [hop] at hw ⊢; exact hw) hne)

end Plain

/-! ## No theft with permutation rows and `ROM/`'s plain extraction -/

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

/-- **The issuance simulator's patch, by forward queries in the permutation model.** -/
noncomputable def progQIP (x : IssueInstance) (c : SimCoins pI) :
    OracleComp specP (K2 pI → Option (ZK.Sim.Bytes 16)) :=
  liftP (progQI x c)

/-- **The spend simulator's patch, by forward queries in the permutation model.** -/
noncomputable def progQSP (x : SpendInstance) (c : SimCoins pS) :
    OracleComp specP (K2 pI → Option (ZK.Sim.Bytes 16)) :=
  liftP (progQS x c)

variable {L M : ℕ}

/-- The patches' queries, from the simulated pair. -/
noncomputable def logQIP (p : Option (IssueInstance × IssueProof Sizes.labelRows)) (g₁ g₂ : Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L M) : List DomP :=
  (logQI p g₁ g₂ b).map embIC

noncomputable def logQSP (p : Option (SpendInstance × SpendProof Sizes.labelRows)) (g₁ g₂ : Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L M) : List DomP :=
  (logQS p g₁ g₂ b).map embIC

lemma hpatchIP (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L M)) (d : DomP) :
    ansQ g₁ g₂ (leanProgIRX hbX x c t) d =
      patch2P pI (runT (ansQ g₁ g₂ t) (progQIP x c)) d (ansQ g₁ g₂ t d) := by
  rw [progQIP, runT_liftP, runT_progQI]
  exact ansQ_prog g₁ g₂ t _ _ d

lemma hpatchSP (x : SpendInstance) (c : SimCoins pS) (g₁ g₂ : Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L M)) (d : DomP) :
    ansQ g₁ g₂ (leanProgSRX hbX x c t) d =
      patch2P pI (runT (ansQ g₁ g₂ t) (progQSP x c)) d (ansQ g₁ g₂ t d) := by
  rw [progQSP, runT_liftP, runT_progQS]
  exact ansQ_prog g₁ g₂ t _ _ d

lemma hpreIP (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3)
    (t t' : ShX (Equiv.Perm Blk) pI (XTab L M)) (h : t'.2 = t.2) :
    runT (ansQ g₁ g₂ t') (progQIP x c) = runT (ansQ g₁ g₂ t) (progQIP x c) := by
  rw [progQIP, runT_liftP, runT_liftP]
  exact hpreI x c g₁ g₂ t t' h

lemma hlogIP (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L M)) :
    qlog (ansQ g₁ g₂ t) (progQIP x c) = logQIP (pairO (some x) (leanSimIR x c)) g₁ g₂ t.2 := by
  rw [progQIP, qlog_liftP, hlogI]
  rfl

lemma hlogSP (x : SpendInstance) (c : SimCoins pS) (g₁ g₂ : Tab3)
    (t : ShX (Equiv.Perm Blk) pI (XTab L M)) :
    qlog (ansQ g₁ g₂ t) (progQSP x c) = logQSP (pairO (some x) (leanSimSR x c)) g₁ g₂ t.2 := by
  rw [progQSP, qlog_liftP, hlogS]
  rfl

lemma qBudP_progQO {I C M' : Type} {progQ : I → C → OracleComp specP M'} {qa : Kind → ℕ}
    {qb : ℕ} (h : ∀ x c, QBudP qa qb (progQ x c)) (x : Option I) (c : C) :
    QBudP qa qb (progQO progQ x c) := by
  rcases x with _ | x
  · exact ⟨trivial, trivial⟩
  · exact ⟨isQueryBound_map_iff _ _ _ _ _ |>.2 (h x c).1, (isQueryBoundP_map_iff _ _ _).2 (h x c).2⟩

/-- **The reduction's budget in the permutation model**: the two patches' forward queries, then
the adversary's. -/
theorem qBudP_redQ {α : Type} {q : Kind → ℕ} {qE : ℕ} {oa : OracleComp specP α}
    (h : QBudP q qE oa) (x₁ : Option IssueInstance) (c₁ : SimCoins pI)
    (x₂ : Option SpendInstance) (c₂ : SimCoins pS) :
    QBudP (q + qPre + qPre) (qE + verifyCellBound pS + verifyCellBound pI)
      (redQ progQIP (patch2P pI) progQSP (patch2P pI) x₁ c₁ x₂ c₂ oa) := by
  have h₂ := qBudP_progQO (fun x c => qBudP_liftP (qBud_progQS x c)) x₂ c₂
  have h₁ := qBudP_progQO (fun x c => qBudP_liftP (qBud_progQI x c)) x₁ c₁
  refine ⟨?_, ?_⟩
  · refine IsKindQueryBoundP.mono (isKindQueryBoundP_bind h₂.1 fun m₂ =>
      isKindQueryBoundP_bind h₁.1 fun m₁ => isQueryBound_simP _ h.1) fun k => ?_
    simp only [Pi.add_apply]
    omega
  · refine (isQueryBoundP_bind h₂.2 fun m₂ _ => isQueryBoundP_bind h₁.2 fun m₁ _ =>
      isQueryBoundP_simP _ h.2).mono ?_
    omega

/-- **The extractor**: `ROM/`'s straight-line extractor `eRomP A` on the reduction's queries. -/
noncomputable def extRomP
    (A : Thief Sizes.labelRows Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (q : Kind → ℕ) (qE : ℕ) :
    Ext Sizes.labelRows Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)) :=
  extL ansQ (QBudP q qE) logQIP logQSP (eRomP A)

/-- **No theft with permutation rows, inverse cipher queries and `ROM/`'s plain extraction**
(Ratatouille, one Client): as `noTheft_lean_rom`, with AES as uniformly random permutations
(`ZKRow.perm`: the hops' error `εROPm`), `M = uovM`, `L ≥ Lmin`, an adversary whose last stage is
the run on the tables of an oracle computation over `specP` with at most `q k` hash queries of
kind `k` and `q_E` cipher queries, forward or inverse (`hA`; no total hash budget), and `ROM/`'s
straight-line extractor on the records of its queries (`extRomP`):

    Pr[Bad] ≤ εROPm(pI; q') + εROPm(pS; q') + δ_S + ε_rom
      + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

`ε_rom = epsRomP q₀ (q_E + cells(pS) + cells(pI)) (totK uovM q₀)`, `q₀ = q + 2·qPre` (`ROM/`'s
simultaneous extraction in the permutation model for the reduction's budget) and
`q' = (q h3 + x₃, q h5 + x₅ + 936, q_E + x_E + 9214)` with the extractor's read budget `hX`. -/
theorem noTheft_lean_romP
    (A : Thief Sizes.labelRows Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE x3 x5 xE : ℕ}
    (hqE : qE + verifyCellBound pS + verifyCellBound pI + 4607 < 2 ^ 128)
    (hA : ∀ o₁ o₂, AdmL (QBudP q qE) ansQ (A.out o₁ o₂))
    (hX : ∀ o₁ o₂, StageBudgetX (extRomP A q qE (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE) :
    pr _ (theftReal A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
        (extRomP A q qE)) ≤
      ZKRow.εz (Equiv.Perm Blk) pI (q .h3 + x3) (q .h5 + x5 + 936) (qE + xE + 9214) +
        ZKRow.εz (Equiv.Perm Blk) pS (q .h3 + x3) (q .h5 + x5 + 936) (qE + xE + 9214) +
        pr _ (deltaS A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX)) +
        ((epsRomP (q + qPre + qPre) (qE + verifyCellBound pS + verifyCellBound pI)
          (totK Arith.Ratatouille.uovM (q + qPre + qPre))).toReal +
          Hit.epsHit (q .mu) (q .h21) (q .h22)) +
        owAdv A.ctx (inverter A (extRomP A q qE) leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX)) := by
  have hSB : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) (q .h3) (q .h5) qE := fun o₁ o₂ => by
    obtain ⟨oa, hb, hF⟩ := hA o₁ o₂
    rw [hF]
    exact stageBudgetX_runTQ hb
  have hAH : ∀ F : Tab3 → Tab3 → ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM) →
      Op Sizes.labelRows, AdmL (QBudP q qE) ansQ F →
      Hit.AdmHit (R := Equiv.Perm Blk) (p := pI) (L := L) (M := Arith.Ratatouille.uovM) (G := Tab3)
        (q .mu) (q .h21) (q .h22) F := by
    rintro F ⟨oa, hb, rfl⟩
    exact admHit_runTQ hb
  exact noTheft_ok (CI := SimCoins pI) (CS := SimCoins pS) A (leanVIRX hbX) (leanVSRX hbX)
    (extRomP A q qE) leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX) (leanPIRX hbX)
    (leanPSRX hbX) (leanPIRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (leanPSRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (distI_budgetX' hbX A _ hbX_wf hSB hX) (distS_budgetX' hbX A _ hSB hX)
    (weakSE2_of_plainL progQIP (patch2P pI) progQSP (patch2P pI) logQIP logQSP
      ((plainSEL_romP A hL _ hqE).mono (fun _ _ _ h => Hit.Rata.FreshOk.freshOp A h)
        (fun _ h => h) le_rfl)
      (progMoves_of_ev (fun _ _ _ => rfl) (fun _ _ _ => rfl) (accOp_movesX hbX A)
        ((Hit.Rata.progEv_hit A hL (q .mu) (q .h21) (q .h22)).mono hAH))
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) hpatchIP hpatchSP
      (fun x c g₁ g₂ s s' h => hpreIP x c g₁ g₂ s s' h) hlogIP hlogSP (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) fun oa x₁ c₁ x₂ c₂ h => qBudP_redQ h x₁ c₁ x₂ c₂)
    hA

end Ratatouille

end VoleMole.Theft
