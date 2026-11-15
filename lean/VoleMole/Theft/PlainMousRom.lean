import VoleMole.Theft.PlainMousJoint
import VoleMole.Theft.PlainRataRom

/-!
# Plain extraction for the redirect game from `ROM/`'s bound (Moussaka)

The Moussaka counterpart of `Theft/PlainRataRom.lean`'s `plainSEL_rom`
(`docs/security/moussaka.md` §5.3): `PlainSEL` for the redirect game, proved from `ROM/`'s
simultaneous extraction (`moussaka_sim_joint_lean`), for function rows, the combination of
`Moussaka.M` equations and `L ≥ 8193` (`Lrom`).

* **`FreshK kt`**: the freshness of the bound: `FreshOk` (the operation's statement is
  well-formed and differs from the simulated one in a hashed field) and, for a redemption, Anchor
  keys that are the keys `kt d` of their digests (`KeysBy`). `ROM/`'s argument decodes a
  statement from its `H₂⁰` input, which holds the Anchors' digests, not their maps; so the
  redemption family must have one key per digest.
* **`eRomM`**: `ROM/`'s straight-line extractor on the redirect tables, as `eRom`: the cipher
  entries of the query list, `mu₁` and `iv` from the extra table, `keysOf`, `knownOf`, and a known
  tree's candidate mapped to the spec witness of the operation (`witOfCandM`), if one is a witness.
* `outIM`, `outRM kt`: the normalized adversary as `ROM/`'s provers of the two relations (the
  operation's statement and proof when it is in the family; a fixed well-formed dummy otherwise).
* `game_badM`: on the tables, a bad output of `PlainSEL` is a bad output of the game.
* **`plainSEL_romM`**: `PlainSEL` for `eRomM` against `QBudT q qE nG`, for `FreshK kt`, with the
  error `epsRomM q qE nG` of `moussaka_sim_joint_lean` with `m = 2` outputs:

      (q₂₁+2)·2^{−150} + (q₂₂+2)·(ε_QS(4409) + 2^{−128} + (n_G+339)·2^{−448})
        + (q₂₃+2)·9·2^{−128} + chainHitEpsCombSim q M 2 + stmtBindEpsSim q 2 + 2·failEps q q_E.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads VoleMole.EndToEnd
open VoleMole.Spec VoleMole.Spec.Moussaka

/-! ## The freshness of the bound -/

/-- **The operation's Anchor keys are those of `kt`** (nothing for an issuance). -/
def KeysOp (kt : Bytes → UOVKey) : MOp → Prop
  | .issue _ _ => True
  | .redeem S' req ci cr cd => KeysBy kt (stOfR S' req ci cr cd)

/-- **The freshness of `ROM/`'s bound**: `FreshOk` and the Anchor keys of `kt`. -/
def FreshK (kt : Bytes → UOVKey) (p₁ : Option (IssueInstance × Bytes))
    (p₂ : Option (RedeemInstance × Bytes)) (op : MOp) : Prop :=
  Hit.Mous.FreshOk p₁ p₂ op ∧ KeysOp kt op

/-! ## The straight-line extractor -/

/-- The spec witness of a candidate, for an operation (the bytes of `issueWitOf`, `redeemWitOf`
with the statement's fields). -/
def witOfCandM : MOp → (ℕ → Arith.GF128) → Bytes
  | .issue _ ci, w => SpecRel.issueWitOf ci w
  | .redeem _ req ci cr _, w => SpecRel.redeemWitOf (req.take nfBytes) ci cr w

/-- A known tree's candidate that is a witness of the operation, if there is one. -/
noncomputable def pickM (op : MOp) (K : Finset (Fin BAVC.tau)) (c : Fin BAVC.tau → ℕ → Arith.GF128) :
    Bytes := by
  classical
  exact if h : ∃ i ∈ K, RelOp op (witOfCandM op (c i)) then witOfCandM op (c h.choose) else []

lemma relOp_pickM {op : MOp} {K : Finset (Fin BAVC.tau)} {c : Fin BAVC.tau → ℕ → Arith.GF128}
    (h : ∃ i ∈ K, RelOp op (witOfCandM op (c i))) : RelOp op (pickM op K c) := by
  classical
  unfold pickM
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec.2

variable {L : ℕ}

/-- **`ROM/`'s straight-line extractor on the redirect tables**: a known tree's candidate that is a
witness of the operation, if there is one (the cipher entries of the query list answered by the
cipher rows, `mu₁` and `iv` read off the extra table). -/
noncomputable def eRomM : Option (IssueInstance × Bytes) → Option (RedeemInstance × Bytes) → MOp →
    List DomIC → Tab3 → Tab3 → (Tab5F × (Blk → Blk → Blk)) × XTab L Arith.Moussaka.M → Bytes :=
  fun _ _ op qs _ _ b =>
    pickM op (Ratatouille.rOut (Hit.Mous.fd op).1 (Hit.Mous.fd op).2 (hbX b.2)
        (Ratatouille.ctOf b.1.2) (cLog (Ratatouille.ctOf b.1.2) qs)).2.1.known
      (candOf (Ratatouille.ctOf b.1.2) (Hit.Mous.fd op).1
        (Ratatouille.rOut (Hit.Mous.fd op).1 (Hit.Mous.fd op).2 (hbX b.2) (Ratatouille.ctOf b.1.2)
          (cLog (Ratatouille.ctOf b.1.2) qs)))

/-! ## The adversary as `ROM/`'s provers -/

lemma wfI_dummy : Hit.Mous.WfI ⟨List.replicate uovM 0, List.replicate ctxBytes 0⟩ := by
  simp [Hit.Mous.WfI]

lemma wfR_dummy : Hit.Mous.WfR ⟨[], List.replicate nfBytes 0, List.replicate ctxBytes 0,
    List.replicate ctxBytes 0, List.replicate cdBytes 0⟩ := by
  simp [Hit.Mous.WfR]

/-- A well-formed issuance instance (the dummy statement). -/
def issW0 : IssW := ⟨_, wfI_dummy⟩

/-- A well-formed redemption instance with no Anchor (the dummy statement). -/
def redK0 (kt : Bytes → UOVKey) : RedK kt := ⟨_, wfR_dummy, fun _ h => by simp at h⟩

open Classical in
/-- The issuance relation's output of an operation (a dummy for a redemption or an instance that
is not well-formed). -/
noncomputable def outIM : MOp → ByteArray × (IssW × Unit)
  | .issue req ci => if h : Hit.Mous.WfI (stOfI req ci) then
      (toBA (req.drop uovM), (⟨_, h⟩, ())) else (ByteArray.empty, (issW0, ()))
  | .redeem _ _ _ _ _ => (ByteArray.empty, (issW0, ()))

open Classical in
/-- The redemption relation's output of an operation (a dummy for an issuance or an instance that
is not in the family). -/
noncomputable def outRM (kt : Bytes → UOVKey) : MOp → ByteArray × (RedK kt × Unit)
  | .redeem S' req ci cr cd => if h : Hit.Mous.WfR (stOfR S' req ci cr cd) ∧
        KeysBy kt (stOfR S' req ci cr cd) then
      (toBA (req.drop nfBytes), (⟨_, h⟩, ())) else (ByteArray.empty, (redK0 kt, ()))
  | .issue _ _ => (ByteArray.empty, (redK0 kt, ()))

/-! ## On the tables, the bad event is the game's -/

section Bad

variable {ι : Type}

set_option maxHeartbeats 2000000 in
/-- **On the tables, a bad output of `PlainSEL` is a bad output of `ROM/`'s game** (as
`game_bad`): if the operation is accepted by the Lean verifier and `eRomM` finds no witness, the
game run on the tables (the normalized adversary as the prover `out <$> normT`) accepts, and its
extraction fails (for a witness predicate `Wit` that gives the operation's relation). -/
theorem game_badM (stF : ι → Statement) (out : MOp → ByteArray × (ι × Unit))
    (Wit : ι → (ℕ → Arith.GF128) → Prop) (oa : OracleComp specIC MOp)
    (g₁ g₂ : Tab3) (t : ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M))
    (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes))
    (hfd : Hit.Mous.fd (runT (ansP g₁ g₂ t) oa) =
      (stF (out (runT (ansP g₁ g₂ t) oa)).2.1, (out (runT (ansP g₁ g₂ t) oa)).1))
    (hacc : (verRO Privacy.Moussaka.pI (hbX t.2.2) (stF (out (runT (ansP g₁ g₂ t) oa)).2.1)
      (out (runT (ansP g₁ g₂ t) oa)).1 (shOf t)).accept = true)
    (hW : ∀ w, Wit (out (runT (ansP g₁ g₂ t) oa)).2.1 w →
      RelOp (runT (ansP g₁ g₂ t) oa) (witOfCandM (runT (ansP g₁ g₂ t) oa) w))
    (hne : ¬ RelOp (runT (ansP g₁ g₂ t) oa)
      (eRomM p₁ p₂ (runT (ansP g₁ g₂ t) oa) (qlog (ansP g₁ g₂ t) oa) g₁ g₂ t.2)) :
    (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
        (out <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa) (cellP t))).2.2.accept = true ∧
      ¬ @Extracted (icPrg (cellP t).cipher) _
        (stF (stOut (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t)) (gameA CrtGen.tables stF
          (out <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa) (cellP t)))))
        (fun _ w => Wit (stOut (evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t))
          (gameA CrtGen.tables stF (out <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa) (cellP t)))) w)
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
      (join (tabP g₁ g₂ t) (cellP t))) = cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa) := by
    rw [tableQueryLog_map', tableQueryLog_eq_qlog, cipherLog_map]
    show cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) (normT Privacy.Moussaka.pI L Arith.Moussaka.M oa)) = _
    rw [hqN, cLog_filter _ _ fun c => decide_eq_true
      (show OnT Privacy.Moussaka.pI L Arith.Moussaka.M (.inr c) from trivial)]
  have hivP : ivOf (Hashes.ofTable (tabP g₁ g₂ t)) ⟨(stF (out o).2.1).params, (out o).1⟩
      ((stF (out o).2.1).mu1 (Hashes.ofTable (tabP g₁ g₂ t))) =
      ivOf (hbX t.2.2) ⟨(stF (out o).2.1).params, (out o).1⟩ ((stF (out o).2.1).mu1 (hbX t.2.2)) := by
    rw [ofTable_tabP]
    exact ivOf_congr (recP_hash_ne _ _ _ (by decide) (by decide) (by decide))
      (recP_hash_ne _ _ _ (by decide) (by decide) (by decide))
      (recP_hash_ne _ _ _ (by decide) (by decide) (by decide)) _ _
  have hver : @verify (icPrg (cellP t).cipher) (Hashes.ofTable (tabP g₁ g₂ t)) CrtGen.tables
      (stF (out o).2.1) (out o).1 = verRO Privacy.Moussaka.pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t) := by
    rw [ofTable_tabP]
    exact congrFun (@verify_agreeOff_h3 (icPrg (rowFn t.2.1.2)) _ _
      (Hashes.agreeOff_withTable _ _ _ _).symm CrtGen.tables _) _
  have hivV : (verRO Privacy.Moussaka.pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t)).iv =
      ivOf (hbX t.2.2) ⟨(stF (out o).2.1).params, (out o).1⟩ ((stF (out o).2.1).mu1 (hbX t.2.2)) := by
    have hacc' : (@verify (icPrg (rowFn t.2.1.2)) (recV Privacy.Moussaka.pI (hbX t.2.2) t.1 t.2.1.1) CrtGen.tables
        (stF (out o).2.1) (out o).1).accept = true := hacc
    obtain ⟨-, leaves, hrec, -⟩ := (@accept_iff (icPrg (rowFn t.2.1.2)) _ _ _ _).1 hacc'
    refine (@verify_iv_chal1 (icPrg (rowFn t.2.1.2)) _ _ _ _ hacc' leaves hrec).1.trans ?_
    exact ivOf_congr (recV_hash_ne _ _ _ (by decide) (by decide))
      (recV_hash_ne _ _ _ (by decide) (by decide)) (recV_hash_ne _ _ _ (by decide) (by decide)) _ _
  have hr := eval_gameA CrtGen.tables stF (out <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa) (cellP t)
    (tabP g₁ g₂ t)
  rw [hP, hJ, hver, hivP] at hr
  generalize evalWithAnswerFn (QueryImpl.ofFn (tabP g₁ g₂ t))
    (gameA CrtGen.tables stF (out <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa) (cellP t)) = R at hr ⊢
  have hS : stOut R = (out o).2.1 := by rw [hr]; rfl
  have hT : R.2.2 = verRO Privacy.Moussaka.pI (hbX t.2.2) (stF (out o).2.1) (out o).1 (shOf t) := by rw [hr]
  have hKn : R.2.1.known = (Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2)
      (Ratatouille.ctOf t.2.1.2) (cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa))).2.1.known := by
    rw [hr]; rfl
  have hK : R.2.1.keys = (Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2)
      (Ratatouille.ctOf t.2.1.2) (cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa))).2.1.keys := by
    rw [hr]; rfl
  have h1 : R.1 = (out o).1 := by rw [hr]
  rw [hS, hT]
  refine ⟨hacc, fun he => hne ?_⟩
  obtain ⟨i, hi, hw⟩ := he
  apply relOp_pickM
  rw [hfd]
  refine ⟨i, hKn ▸ hi, hW _ ?_⟩
  have hiv' : R.2.2.iv = (Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2)
      (Ratatouille.ctOf t.2.1.2) (cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa))).2.2.iv := by
    rw [hT]; exact hivV
  have hc := candOf_congr (cellP t) (stF (out o).2.1) (r := R)
    (r' := Ratatouille.rOut (stF (out o).2.1) (out o).1 (hbX t.2.2) (Ratatouille.ctOf t.2.1.2)
      (cLog (Ratatouille.ctOf t.2.1.2) (qlog (ansP g₁ g₂ t) oa))) h1 hK hiv' i
  exact hc ▸ hw

end Bad

/-! ## Plain extraction from `ROM/`'s bound -/

section Plain

/-- **The error of `ROM/`'s simultaneous extraction** for one issuance and one redemption output
(`moussaka_sim_joint_lean` with `m = 2`), for `q k` hash queries of kind `k`, `qE` cipher cells and
`nG` hash queries in all. -/
noncomputable def epsRomM (q : Kind → ℕ) (qE nG : ℕ) : ℝ≥0∞ :=
  (q .h21 + 2) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 2) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 2) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    chainHitEpsCombSim q Arith.Moussaka.M 2 + stmtBindEpsSim q 2 + 2 * failEps q qE

lemma epsRomM_ne_top (q : Kind → ℕ) (qE nG : ℕ) : epsRomM q qE nG ≠ ⊤ := by
  simp [epsRomM, chainHitEpsCombSim, chainHitEpsSim, stmtBindEpsSim, failEps, openHashEps,
    ladderEps, ENNReal.mul_eq_top, ENNReal.div_eq_top]

lemma verILX_eq (x : IssueInstance) (π : Bytes)
    (t : ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :
    verILX hbX x π t = (verRO Privacy.Moussaka.pI (hbX t.2.2) (Privacy.Moussaka.stI x) (toBA π)
      (shOf t)).accept := rfl

lemma verRLX_eq (x : RedeemInstance) (π : Bytes)
    (t : ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)) :
    verRLX hbX x π t = (verRO Privacy.Moussaka.pI (hbX t.2.2) (Privacy.Moussaka.stR x) (toBA π)
      (shOf t)).accept := rfl

lemma allQ_map_normTM {β : Type} (f : MOp → β) (oa : OracleComp specIC MOp) :
    AllQueriesSatisfy (f <$> normT Privacy.Moussaka.pI L Arith.Moussaka.M oa)
      (OnT Privacy.Moussaka.pI L Arith.Moussaka.M) := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind (allQueriesSatisfy_normT _) fun _ => allQueriesSatisfy_pure _ _

set_option maxHeartbeats 400000 in
/-- **Plain extraction for the redirect game from `ROM/`'s bound** (Moussaka, function rows,
`M = Moussaka.M`, `L ≥ 8193`): `PlainSEL` holds for `ROM/`'s straight-line extractor `eRomM`
against the last stages within `QBudT q qE nG`, for the freshness `FreshK kt` (well-formed
statements, Anchor keys of `kt`), with the error `epsRomM q qE nG` of `moussaka_sim_joint_lean`
for one issuance and one redemption output. -/
theorem plainSEL_romM (kt : Bytes → UOVKey) (hL : Lrom ≤ L) (q : Kind → ℕ) (qE nG : ℕ) :
    PlainSEL ansP (AccOp (verILX hbX) (verRLX hbX)) (FreshK kt) RelOp
      (eRomM (L := L)) (QBudT q qE nG) (epsRomM q qE nG).toReal := by
  classical
  intro α _ _ p₁ p₂ oa hoa
  rw [pr_eq_toReal_prU]
  refine ENNReal.toReal_mono (epsRomM_ne_top q qE nG) (Prob.prU_prod_le_right _ fun a => ?_)
  -- the normalized adversary as the provers, and the joint game
  set N := normT Privacy.Moussaka.pI L Arith.Moussaka.M (oa a)
  set PI := outIM <$> N
  set PR := outRM kt <$> N
  let m : CTable → OracleComp spec (Out ((IssW × Unit) × QueryLog specIC) ×
      Out ((RedK kt × Unit) × QueryLog specIC)) := fun E =>
    gameA CrtGen.tables (fun s : IssW => Privacy.Moussaka.stI s.1) PI E >>= fun r₁ =>
      gameA CrtGen.tables (fun s : RedK kt => Privacy.Moussaka.stR s.1) PR E >>= fun r₂ =>
        pure (r₁, r₂)
  let ev : CTable → Out ((IssW × Unit) × QueryLog specIC) ×
      Out ((RedK kt × Unit) × QueryLog specIC) → Prop := fun E r =>
    (r.1.2.2.accept = true ∧ ¬ @Extracted (icPrg E.cipher) _ (Privacy.Moussaka.stI (stOut r.1).1)
      (fun _ w => Privacy.Moussaka.IssueRelW (stOut r.1).1
        (SpecRel.issueWitOf (stOut r.1).1.ctxIss w)) r.1) ∨
    (r.2.2.2.accept = true ∧ ¬ @Extracted (icPrg E.cipher) _ (Privacy.Moussaka.stR (stOut r.2).1)
      (fun _ w => Privacy.Moussaka.RedeemRelW (stOut r.2).1
        (SpecRel.redeemWitOf (stOut r.2).1.nf (stOut r.2).1.ctxIss (stOut r.2).1.ctxRed w)) r.2)
  have heval : ∀ E g, evalWithAnswerFn (QueryImpl.ofFn g) (m E) =
      (evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (fun s : IssW => Privacy.Moussaka.stI s.1) PI E),
        evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (fun s : RedK kt => Privacy.Moussaka.stR s.1) PR E)) := by
    intro E g
    simp only [m, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  -- `ROM/`'s bound on the joint game
  have hb := (hoa a)
  have hrom := moussaka_sim_joint_lean kt PI (fun _ : Unit => PI) PR (fun _ : Unit => PR)
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
      epsRomM q qE nG := by
    refine hrom.trans (le_of_eq ?_)
    simp only [Finset.card_univ, Fintype.card_unit, epsRomM]
    norm_num
    ring
  -- the joint game queries only table points: the tables are the lazy oracle
  have hI : AllQueriesSatisfy PI (OnT Privacy.Moussaka.pI L Arith.Moussaka.M) := allQ_map_normTM _ _
  have hR : AllQueriesSatisfy PR (OnT Privacy.Moussaka.pI L Arith.Moussaka.M) := allQ_map_normTM _ _
  have hsI : ∀ s : IssW, VerOk Privacy.Moussaka.pI L Arith.Moussaka.M (Privacy.Moussaka.stI s.1) :=
    fun s => verOk_stIW hL s.1 s.2
  have hsR : ∀ s : RedK kt, VerOk Privacy.Moussaka.pI L Arith.Moussaka.M
      (Privacy.Moussaka.stR s.1) := fun s => verOk_stRW hL s.1 s.2.1
  have hm : ∀ E, AllQueriesSatisfy (m E) (· ∈ TPts Privacy.Moussaka.pI L Arith.Moussaka.M) :=
    fun E => allQueriesSatisfy_bind
      (gameA_onT (fun s : IssW => Privacy.Moussaka.stI s.1) hsI hI E) fun _ =>
        allQueriesSatisfy_bind (gameA_onT (fun s : RedK kt => Privacy.Moussaka.stR s.1) hsR hR E)
          fun _ => allQueriesSatisfy_pure _ _
  have hbr := pr_tables_eq_ro m hm ev
  rw [pr_eq_toReal_prU] at hbr
  have hfin : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m E)).run' ∅}[ev E r] ≠ ⊤ :=
    ne_top_of_le_ne_top (epsRomM_ne_top q qE nG) hrom'
  rw [← (ENNReal.toReal_eq_toReal_iff' (ne_top_of_le_ne_top ENNReal.one_ne_top
    (Prob.prU_le_one _)) hfin).1 hbr] at hrom'
  refine (Prob.prU_mono fun z hz => ?_).trans hrom'
  -- on the tables, the bad event is the game's
  obtain ⟨hacc, hfr, hne⟩ := hz
  show ev (cellP z.2) (runT (tabP z.1.1 z.1.2 z.2) (m (cellP z.2)))
  rw [runT_eq_eval, heval]
  rcases hop : runT (ansP z.1.1 z.1.2 z.2) (oa a) with ⟨req, ci⟩ | ⟨S', req, ci, cr, cd⟩
  · rw [hop] at hacc hfr
    have hw : Hit.Mous.WfI (stOfI req ci) := hfr.1.1
    have ho : outIM (.issue req ci) = (toBA (req.drop uovM), (⟨_, hw⟩, ())) := by
      simp only [outIM, dite_eq_left hw]
    have hacc' := (verILX_eq _ _ _).symm.trans hacc.2.2
    exact Or.inl (game_badM (fun s : IssW => Privacy.Moussaka.stI s.1) outIM
      (fun s w => Privacy.Moussaka.IssueRelW s.1 (SpecRel.issueWitOf s.1.ctxIss w))
      (oa a) z.1.1 z.1.2 z.2 (p₁ a) (p₂ a) (by rw [hop, ho]; rfl) (by rw [hop, ho]; exact hacc')
      (fun w hw' => by rw [hop] at hw' ⊢; rw [ho] at hw'; exact hw'.1) hne)
  · rw [hop] at hacc hfr
    have hw : Hit.Mous.WfR (stOfR S' req ci cr cd) ∧ KeysBy kt (stOfR S' req ci cr cd) :=
      ⟨hfr.1.1, hfr.2⟩
    have ho : outRM kt (.redeem S' req ci cr cd) = (toBA (req.drop nfBytes), (⟨_, hw⟩, ())) := by
      simp only [outRM, dite_eq_left hw]
    have hacc' := (verRLX_eq _ _ _).symm.trans hacc.2
    exact Or.inr (game_badM (fun s : RedK kt => Privacy.Moussaka.stR s.1) (outRM kt)
      (fun s w => Privacy.Moussaka.RedeemRelW s.1
        (SpecRel.redeemWitOf s.1.nf s.1.ctxIss s.1.ctxRed w))
      (oa a) z.1.1 z.1.2 z.2 (p₁ a) (p₂ a) (by rw [hop, ho]; rfl) (by rw [hop, ho]; exact hacc')
      (fun w hw' => by rw [hop] at hw' ⊢; rw [ho] at hw'; exact hw'.1) hne)

end Plain

end VoleMole.Theft.Moussaka
