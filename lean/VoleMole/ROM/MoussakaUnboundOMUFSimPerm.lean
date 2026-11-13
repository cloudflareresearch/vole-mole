import VoleMole.ROM.MoussakaUnboundOMUFSim
import VoleMole.ROM.MoussakaUnboundSimPerm
import VoleMole.ROM.MoussakaOMUFSimPerm

/-!
# Unbound Moussaka Theorem U1 with simultaneous extraction, permutation model

`ROM/MoussakaUnboundOMUFSim.lean`'s `omufU_le_num_sim` with the ideal cipher as random
permutations and an adversary that makes **forward and inverse** cipher queries
(`ROM/PermModel.lean`), as `ROM/MoussakaOMUFSimPerm.lean` does for Moussaka. The honest parties
(the Anchors of either variant and the Moderator) read the cipher forward only.

* `moussakaIssue_sim_specP`: bound issuance, simultaneous extraction, spec relation, permutation
  model (`moussakaIssue_sim_spec` with `prEvent_sim_leP`; the provers normalized by
  `normP (mousPI lr) π`).
* `OMUFU.AdversaryP`, `OMUFU.gameP`: the OMUF-U adversary and game of the permutation model (the
  game of `ROM/MoussakaUnboundOMUF.lean` with the honest parties lifted, `liftP`).
  `AdversaryP.toIC lr π`: the adversary at a fixed table, its stages normalized
  (`normJ (mousUPI lr) (mousUPR lr) π`); per table the two games have one output (`gameP_eval`).
* `PBIP`, `PUIP`, `PURP`: the provers, projections of `gameP`. The bound issuance provers run
  through `normP (mousPI lr) π` (`nB`), the unbound ones through the joint normalization of the
  unbound relations (`nU`), so that `moussakaUnbound_sim_joint_specP` applies to them.
  `accepted_BIP`, `accepted_UIP`, `accepted_URP`, **`win_impP`** (as `win_imp`).
* **`omufU_le_simP`** (the reduction), `prEvent_simBI_leP`, `prEvent_simU_leP`,
  **`omufU_le_num_simP`**:

      Pr[Win] ≤ εI^simP(q', q'_E, qI) + εU^simP(q', q'_E, n', qI, qR) + Pr[Coll] + Pr[Forge],

  `εI^simP`, `εU^simP` = `epsIsim`, `epsUsim` with the permutation model's failure terms
  (`failEpsP`) and, for the unbound pair, the joint normalization's two `H₄` queries per `H₂¹`
  query in the total hash count (`n' + 2q'₂₁`), at the budgets of `omufU_le_num`
  (`q' = gameK q qI qR`, `q'_E = gameE lr qE qI qR`, `n' = gameH n qI qR`; `q'_E` counts the
  adversary's forward and inverse cipher queries).

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## Bound issuance, simultaneous extraction, permutation model -/

lemma chainHitEpsSim_addH4 (q : Kind → ℕ) (m : ℕ) :
    chainHitEpsSim (addH4 q) m = chainHitEpsSim q m := by
  simp [chainHitEpsSim, addH4]

variable {ι' α ι β : Type}

/-- **Moussaka issuance, simultaneous extraction, spec relation, permutation model**
(`moussakaIssue_sim_spec` for provers with forward and inverse cipher queries, normalized by
`normP (mousPI lr) π`): the failure terms are the permutation model's `failEpsP`. -/
theorem moussakaIssue_sim_specP (inst : ι → ByteArray × ByteArray)
    (ht : ∀ s, (inst s).1.size = 45) (hci : ∀ s, (inst s).2.size = 16) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (moussakaIssue (inst s).1 (inst s).2 labelRows).instEnc ByteArray.empty)
    (P₀ : OracleComp specP (ByteArray × (ι × β))) (P : ι' → OracleComp specP (ByteArray × (ι × β)))
    (J : Finset ι') (qE : ℕ) (hqE : ∀ j ∈ J, IsQueryBoundP (P j) (fun t => t.isRight = true) qE)
    (q : Kind → ℕ) (hq₀ : IsKindQueryBoundP P₀ q) (hq : ∀ j ∈ J, IsKindQueryBoundP (P j) q)
    (nG : ℕ) (hnG₀ : IsQueryBoundP P₀ (fun t => t.isLeft = true) nG)
    (hnG : ∀ j ∈ J, IsQueryBoundP (P j) (fun t => t.isLeft = true) nG)
    (hpre : ∀ π : PTable, PrefixRuns π.fwd (normP (mousPI labelRows) π P₀)
      (fun j => normP (mousPI labelRows) π (P j)) J)
    (oa : PTable → OracleComp spec α) (event : PTable → α → Prop)
    (htr : ∀ π g, event π (evalWithAnswerFn (QueryImpl.ofFn g) (oa π)) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables
        (fun s => moussakaIssue (inst s).1 (inst s).2 labelRows)
        (normP (mousPI labelRows) π (P j)) π.fwd)
      r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
        (moussakaIssue (inst (stOut r)).1 (inst (stOut r)).2 labelRows)
        (fun _ w => Privacy.Moussaka.IssueRelW
          ⟨toL (inst (stOut r)).1, toL (inst (stOut r)).2⟩
          (SpecRel.issueWitOf (toL (inst (stOut r)).2) w)) r) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (oa π)).run' ∅}[event π r] ≤
      (q .h21 + J.card) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + J.card) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        (q .h23 + J.card) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsSim q J.card +
        stmtBindEpsSim q J.card + J.card * failEpsP q qE := by
  classical
  set stF : ι → Statement := fun s => moussakaIssue (inst s).1 (inst s).2 labelRows
  set st₀ := moussakaIssue ByteArray.empty ByteArray.empty labelRows
  have hmu := muIn_injective (stF := stF) (dst := st₀.dst) (fun _ => rfl) hinj
  have h := prEvent_sim_leP CrtGen.tables stF (decOf fun s => muIn (stF s))
    (fun s => moussakaIssueSys (inst s).1 (inst s).2) liftInvOk_tables st₀ (fun _ => rfl)
    (fun _ => rfl) none (fun _ => rfl) (fun s => decOf_apply hmu s)
    (fun s => Moussaka.issueSystem_length _ _) 9
    (fun s _ => moussakaIssueWit (fun k => fnOf (inst s).1 k.val) (fnOf (inst s).2))
    (fun s c1 lb w => moussakaIssue_values (inst s).1 (inst s).2 labelRows c1 lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        moussakaIssue_extract_chain (inst s).1 (inst s).2 labelRows ch hv hA hAS hkos hP.1 hQS
          admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    P₀ P J qE hqE q hq₀ hq nG hnG₀ hnG hpre oa event fun π g hev => by
      obtain ⟨j, hj, hacc, hnex⟩ := htr π g hev
      exact ⟨j, hj, hacc, fun he => hnex (extracted_mono (fun c1 w hw =>
        SpecRel.issueRelW_of_wit _ _ (ht _) (hci _) w hw) he)⟩
  refine h.trans ?_
  rw [sim_sum_eq]
  simp only [addH4_of_ne _ (show Kind.h21 ≠ .h4 by decide),
    addH4_of_ne _ (show Kind.h22 ≠ .h4 by decide), addH4_of_ne _ (show Kind.h23 ≠ .h4 by decide),
    chainHitEpsSim_addH4, stmtBindEpsSim_addH4]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, moussakaIssue]) (by norm_num [st₀, moussakaIssue])
  gcongr
  norm_num

namespace OMUFU

open VoleMole.ROM.IC.OMUF

attribute [local irreducible] Spec.Moussaka.com Spec.MoussakaUnbound.ucom
  Spec.MoussakaUnbound.derive

/-! ## The game in the permutation model -/

variable {K qR : ℕ}

/-- **An OMUF-U adversary of the permutation model**: as `Adversary`, with forward and inverse
cipher queries. -/
structure AdversaryP (K qR : ℕ) where
  σ : Type
  init : OracleComp specP σ
  query : σ → OracleComp specP (σ × IQ K)
  absorb : σ → IssResp → σ
  final : σ → OracleComp specP (Fin qR → RedQ K)

/-- The joint normalization of the unbound relations. -/
abbrev nU (lr : Bool) (π : PTable) {α : Type} (P : OracleComp specP α) : OracleComp specIC α :=
  normJ (mousUPI lr) (mousUPR lr) π P

/-- The normalization of bound issuance. -/
abbrev nB (lr : Bool) (π : PTable) {α : Type} (P : OracleComp specP α) : OracleComp specIC α :=
  normP (mousPI lr) π P

/-- **The adversary at a fixed permutation table**: its stages normalized (`nU`), an `Adversary`
of the PRF view. -/
def AdversaryP.toIC (lr : Bool) (π : PTable) (A : AdversaryP K qR) : Adversary K qR where
  σ := A.σ
  init := nU lr π A.init
  query s := nU lr π (A.query s)
  absorb := A.absorb
  final s := nU lr π (A.final s)

/-- `n` Issue rounds from the state `s`, the honest Anchors lifted. -/
def runIssP (lr : Bool) (sk : Fin K → Spec.Signer) (A : AdversaryP K qR) :
    ℕ → A.σ → OracleComp specP (A.σ × List (IQ K × Bool))
  | 0, s => pure (s, [])
  | n + 1, s => A.query s >>= fun sq => liftP (anchorU lr sk sq.2) >>= fun ra =>
      runIssP lr sk A n (A.absorb sq.1 ra.1) >>= fun rest => pure (rest.1, (sq.2, ra.2) :: rest.2)

/-- **The OMUF-U game in the permutation model** with `qI` Issue queries. -/
def gameP (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
    (A : AdversaryP K qR) : OracleComp specP (GOut K) :=
  A.init >>= fun s => runIssP lr sk A qI s >>= fun r => A.final r.1 >>= fun R =>
    (fun red => (r.2, red)) <$> liftP (runRed lr pk R)

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
  (A : AdversaryP K qR)

theorem runIssP_eval (g : Table) (π : PTable) (n : ℕ) (s : A.σ) :
    evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (runIssP lr sk A n s) =
      evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (runIss lr sk (A.toIC lr π) n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    show evalWithAnswerFn _ (A.query s >>= fun sq => liftP (anchorU lr sk sq.2) >>= fun ra =>
        runIssP lr sk A n (A.absorb sq.1 ra.1) >>= fun rest =>
          (pure (rest.1, (sq.2, ra.2) :: rest.2) : OracleComp specP _)) =
      evalWithAnswerFn _ (nU lr π (A.query s) >>= fun sq =>
        anchorU lr sk sq.2 >>= fun ra =>
          runIss lr sk (A.toIC lr π) n (A.absorb sq.1 ra.1) >>= fun rest =>
            (pure (rest.1, (sq.2, ra.2) :: rest.2) : OracleComp specIC _))
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, evalWithAnswerFn_liftP,
      evalWithAnswerFn_normJ, ih]
    rfl

/-- **Per table, the game of the permutation model has the output of the PRF view's game of the
adversary at that table.** -/
theorem gameP_eval (g : Table) (π : PTable) :
    evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (gameP lr pk sk qI A) =
      evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (game lr pk sk qI (A.toIC lr π)) := by
  show evalWithAnswerFn _ (A.init >>= fun s => runIssP lr sk A qI s >>= fun r =>
      A.final r.1 >>= fun R => (fun red => (r.2, red)) <$> liftP (runRed lr pk R)) =
    evalWithAnswerFn _ (nU lr π A.init >>= fun s =>
      runIss lr sk (A.toIC lr π) qI s >>= fun r =>
        nU lr π (A.final r.1) >>= fun R =>
          (fun red => (r.2, red)) <$> runRed lr pk R)
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_map, evalWithAnswerFn_liftP, runIssP_eval,
    evalWithAnswerFn_normJ]

/-- **The prover `P^iss_j` of the permutation model** (bound issuance). -/
def PBIP (j : ℕ) : OracleComp specP (ByteArray × (ιI × GOut K)) := projBI j <$> gameP lr pk sk qI A

/-- **The prover `P^u-iss_j` of the permutation model** (unbound issuance). -/
def PUIP (j : ℕ) : OracleComp specP (ByteArray × (ιI × GOut K)) := projUI j <$> gameP lr pk sk qI A

/-- **The prover `P^u-red_j` of the permutation model** (unbound redemption). -/
def PURP (j : ℕ) : OracleComp specP (ByteArray × (ιR K × GOut K)) :=
  projUR j <$> gameP lr pk sk qI A

section Accepted

variable (g : Table) (π : PTable)

/-- **An accepted bound Issue query is accepted by `P^iss_j`'s verifier, at its statement.** -/
theorem accepted_BIP {j : ℕ} {q : IssQ K}
    (hj : (evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd))
      (game lr pk sk qI (A.toIC lr π))).1[j]? = some (.inl q, true)) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stI lr) (nB lr π (PBIP lr pk sk qI A j)) π.fwd)
    r.2.2.accept = true ∧ (stOut r).1 = (q.t, q.ctx) := by
  obtain ⟨-, hrec, -⟩ := game_eval g π.fwd lr pk sk (A.toIC lr π) qI
  obtain ⟨hwf, hv⟩ := hrec _ (List.mem_of_getElem? hj) rfl
  have hsz : q.t.size = 45 ∧ q.ctx.size = 16 := ⟨size_t hwf, hwf.2⟩
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (nB lr π (PBIP lr pk sk qI A j)) =
      (q.pf, (⟨(q.t, q.ctx), hsz⟩, evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd))
        (game lr pk sk qI (A.toIC lr π)))) := by
    rw [nB, evalWithAnswerFn_normP, PBIP, evalWithAnswerFn_map, gameP_eval]
    simp only [projBI, hj, hsz, and_self, dite_true]
  refine ⟨?_, ?_⟩
  · rw [gameA_transcript, sA, hP]; exact hv
  · rw [stOut_gameA, sA, hP]

/-- **An accepted unbound Issue query is accepted by `P^u-iss_j`'s verifier, at its
statement.** -/
theorem accepted_UIP {j : ℕ} {q : IssQ K}
    (hj : (evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd))
      (game lr pk sk qI (A.toIC lr π))).1[j]? = some (.inr q, true)) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stUI lr) (nU lr π (PUIP lr pk sk qI A j)) π.fwd)
    r.2.2.accept = true ∧ (stOut r).1 = (q.t, q.ctx) := by
  obtain ⟨-, hrec, -⟩ := game_eval g π.fwd lr pk sk (A.toIC lr π) qI
  obtain ⟨hwf, hv⟩ := hrec _ (List.mem_of_getElem? hj) rfl
  have hsz : q.t.size = 45 ∧ q.ctx.size = 16 := ⟨size_t_u hwf, hwf.2⟩
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (nU lr π (PUIP lr pk sk qI A j)) =
      (q.pf, (⟨(q.t, q.ctx), hsz⟩, evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd))
        (game lr pk sk qI (A.toIC lr π)))) := by
    rw [nU, evalWithAnswerFn_normJ, PUIP, evalWithAnswerFn_map, gameP_eval]
    simp only [projUI, hj, hsz, and_self, dite_true]
  refine ⟨?_, ?_⟩
  · rw [gameA_transcript, sA, hP]; exact hv
  · rw [stOut_gameA, sA, hP]

/-- **An accepted redemption is accepted by `P^u-red_j`'s verifier, at its statement.** -/
theorem accepted_URP {j : ℕ} {rq : RedQ K}
    (hj : (evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd))
      (game lr pk sk qI (A.toIC lr π))).2[j]? = some (rq, true)) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stUR lr pk) (nU lr π (PURP lr pk sk qI A j)) π.fwd)
    r.2.2.accept = true ∧ (stOut r).1 = (rq.S, rq.nf, rq.ci, rq.cr, rq.cd) := by
  obtain ⟨-, -, -, hrec⟩ := game_eval g π.fwd lr pk sk (A.toIC lr π) qI
  obtain ⟨hwf, hv⟩ := hrec _ (List.mem_of_getElem? hj) rfl
  have hsz : rq.S.length ≤ 64 ∧ rq.nf.size = 24 ∧ rq.ci.size = 16 ∧ rq.cr.size = 16 :=
    ⟨hwf.2.1, size_nf_u hwf, hwf.2.2.2.2.1, hwf.2.2.2.2.2⟩
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (nU lr π (PURP lr pk sk qI A j)) =
      (rq.pf, (⟨(rq.S, rq.nf, rq.ci, rq.cr, rq.cd), hsz⟩,
        evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (game lr pk sk qI (A.toIC lr π)))) := by
    rw [nU, evalWithAnswerFn_normJ, PURP, evalWithAnswerFn_map, gameP_eval]
    simp only [projUR, hj, hsz, and_self, dite_true]
  refine ⟨?_, ?_⟩
  · rw [gameA_transcript, sA, hP]; exact hv
  · rw [stOut_gameA, sA, hP]

end Accepted

/-! ## The reduction -/

/-- **The reductions' run in the permutation model**: the game, then every proof's straight-line
extraction and verification, for the three families (`gameA` of the normalized provers at the
forward table). -/
def extAllP (π : PTable) : OracleComp spec (View K) :=
  runP π (gameP lr pk sk qI A) >>= fun o =>
    (List.range qI).mapM (fun j =>
      gameA CrtGen.tables (stI lr) (nB lr π (PBIP lr pk sk qI A j)) π.fwd) >>= fun ob =>
      (List.range qI).mapM (fun j =>
        gameA CrtGen.tables (stUI lr) (nU lr π (PUIP lr pk sk qI A j)) π.fwd) >>= fun ou =>
        (List.range qR).mapM (fun j =>
          gameA CrtGen.tables (stUR lr pk) (nU lr π (PURP lr pk sk qI A j)) π.fwd) >>= fun orr =>
          pure (o, ob, ou, orr)

theorem extAllP_eval (g : Table) (π : PTable) :
    evalWithAnswerFn (QueryImpl.ofFn g) (extAllP lr pk sk qI A π) =
      (evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (game lr pk sk qI (A.toIC lr π)),
        (List.range qI).map (fun j => evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stI lr) (nB lr π (PBIP lr pk sk qI A j)) π.fwd)),
        (List.range qI).map (fun j => evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stUI lr) (nU lr π (PUIP lr pk sk qI A j)) π.fwd)),
        (List.range qR).map (fun j => evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stUR lr pk) (nU lr π (PURP lr pk sk qI A j)) π.fwd))) := by
  simp only [extAllP, evalWithAnswerFn_bind, evalWithAnswerFn_runP, gameP_eval,
    evalWithAnswerFn_mapM, evalWithAnswerFn_pure]

/-- **The per-table core of Theorem U1 in the permutation model** (`win_imp`): a win means that
some accepted proof (of one of the three families) is not extracted, or `B₁` finds a collision of
`Com ∪ UCom`, or `B₂` a CT-UF^open forgery. -/
theorem win_impP (g : Table) (π : PTable)
    (hwin : Win (evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (gameP lr pk sk qI A))) :
    (∃ j ∈ Finset.range qI, BadBI π.fwd lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (nB lr π (PBIP lr pk sk qI A j)) π.fwd))) ∨
    (∃ j ∈ Finset.range qI, BadUI π.fwd lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUI lr) (nU lr π (PUIP lr pk sk qI A j)) π.fwd))) ∨
    (∃ j ∈ Finset.range qR, BadUR π.fwd lr pk (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUR lr pk) (nU lr π (PURP lr pk sk qI A j)) π.fwd))) ∨
    Coll lr pk π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (extAllP lr pk sk qI A π)) ∨
    Forge lr pk π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (extAllP lr pk sk qI A π)) := by
  classical
  rw [gameP_eval] at hwin
  obtain ⟨hlI, -, hlR, -⟩ := game_eval g π.fwd lr pk sk (A.toIC lr π) qI
  rw [extAllP_eval]
  set E := π.fwd
  set o := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI (A.toIC lr π)) with ho
  set ob := (List.range qI).map (fun j => evalWithAnswerFn (QueryImpl.ofFn g)
    (gameA CrtGen.tables (stI lr) (nB lr π (PBIP lr pk sk qI A j)) E)) with hob
  set ou := (List.range qI).map (fun j => evalWithAnswerFn (QueryImpl.ofFn g)
    (gameA CrtGen.tables (stUI lr) (nU lr π (PUIP lr pk sk qI A j)) E)) with hou
  set orr := (List.range qR).map (fun j => evalWithAnswerFn (QueryImpl.ofFn g)
    (gameA CrtGen.tables (stUR lr pk) (nU lr π (PURP lr pk sk qI A j)) E)) with horr
  by_contra hno
  simp only [BadBI, BadUI, BadUR, not_or, not_exists, not_and, Finset.mem_range, not_not] at hno
  obtain ⟨hB, hU, hR, hC, hF⟩ := hno
  obtain ⟨c, cr, hc⟩ := hwin
  have key := _root_.VoleMole.MoussakaUnbound.collision_or_forgery_unbound comX
    (fun x => x.isRight = true) ctxX keyX Spec.MoussakaUnbound.derive (SX lr pk E (o, ob, ou, orr))
    (Sum.inr '' SUR lr pk E (o, ob, ou, orr))
    (fun x hx => Or.inr (Set.image_mono Set.subset_union_right hx))
    (uissL o) (bissL o) (uredL o) ?_ ?_ ?_ c cr hc
  · rcases key with ⟨x, hx, x', hx', hne, he⟩ | ⟨x, hx, hn1, hn2⟩
    · exact hC ⟨x, hx, x', hx', hne, he⟩
    · obtain ⟨y, hy, rfl⟩ := hx
      have e : comX (Sum.inr y) = ucomO y := by simp only [comX, Sum.elim_inr]
      rw [e] at hn1 hn2
      exact hF ⟨y, hy, fun hs => (mem_sigT hs).elim hn1 hn2⟩
  · intro q hq
    simp only [uissL, List.mem_map, List.mem_filter, Bool.and_eq_true] at hq
    obtain ⟨⟨p, b⟩, ⟨hp, hpb, hpr⟩, rfl⟩ := hq
    rcases p with p | p
    · simp at hpr
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    have hjl : j < qI := by rw [← hlI]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hj' : o.1[j]? = some (.inr p, true) := by rw [hj]; simp_all
    obtain ⟨hacc, hst⟩ := accepted_UIP lr pk sk qI A g π hj'
    obtain ⟨y, hy, hyc, hyt⟩ := opUI_of_ext E lr (hU j hjl hacc)
    refine ⟨.inr y, Or.inr ⟨y, Or.inl ⟨j, p, _, hj', by simp [ou, hjl], hy⟩, rfl⟩, rfl, ?_, ?_⟩
    · simp only [comX, Sum.elim_inr, IQ.q]; rw [hyc, hst]; rfl
    · simp only [ctxX, Sum.elim_inr, IQ.q]; rw [hyt, hst]; rfl
  · intro t ht
    simp only [bissL, List.mem_map, List.mem_filter, Bool.and_eq_true] at ht
    obtain ⟨⟨p, b⟩, ⟨hp, hpb, hpl⟩, rfl⟩ := ht
    rcases p with p | p
    swap
    · simp at hpl
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    have hjl : j < qI := by rw [← hlI]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hj' : o.1[j]? = some (.inl p, true) := by rw [hj]; simp_all
    obtain ⟨hacc, hst⟩ := accepted_BIP lr pk sk qI A g π hj'
    obtain ⟨x, hx, hxc, -⟩ := opBI_of_ext E lr (hB j hjl hacc)
    refine ⟨.inl x, Or.inl ⟨x, ⟨j, p, _, hj', by simp [ob, hjl], hx⟩, rfl⟩, by simp, ?_⟩
    simp only [comX, Sum.elim_inl, IQ.q]; rw [hxc, hst]; rfl
  · intro q hq
    simp only [uredL, List.mem_map, List.mem_filter] at hq
    obtain ⟨p, ⟨hp, hpb⟩, rfl⟩ := hq
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    have hjl : j < qR := by rw [← hlR]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hj' : o.2[j]? = some (p.1, true) := by rw [hj]; cases p; simp_all
    obtain ⟨hacc, hst⟩ := accepted_URP lr pk sk qI A g π hj'
    obtain ⟨y, hy, hyc, hyd⟩ := opUR_of_ext E lr pk (hR j hjl hacc)
    refine ⟨.inr y, ⟨y, ⟨j, p.1, _, hj', by simp [orr, hjl], hy⟩, rfl⟩, rfl, ?_, ?_⟩
    · simp only [ctxX, Sum.elim_inr]; rw [hyc, hst]
    · simp only [keyX, Sum.elim_inr]; rw [hst] at hyd; exact hyd

/-- **Theorem U1 in the permutation model, the reduction, with simultaneous extraction events**
(`omufU_le_sim`). -/
theorem omufU_le_simP :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (runP π (gameP lr pk sk qI A))).run' ∅}[
        Win r] ≤
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        SimBI lr π.fwd v] +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        SimU lr pk π.fwd v] +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        Coll lr pk π.fwd v] +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        Forge lr pk π.fwd v] := by
  have h := prEvent_bind_le_sum4_of_table ($ᵗ PTable) (fun π => runP π (gameP lr pk sk qI A))
    (fun _ r => Win r) {0} {0} (fun _ π => extAllP lr pk sk qI A π)
    (fun π v => SimBI lr π.fwd v) (fun _ π => extAllP lr pk sk qI A π)
    (fun π v => SimU lr pk π.fwd v) (fun π => extAllP lr pk sk qI A π)
    (fun π v => Coll lr pk π.fwd v) (fun π v => Forge lr pk π.fwd v) fun π g hw => by
      rw [evalWithAnswerFn_runP] at hw
      rcases win_impP lr pk sk qI A g π hw with
        ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | hC | hF
      · refine Or.inl ⟨0, Finset.mem_singleton_self 0, ?_⟩
        rw [extAllP_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inl ?_⟩)
        rw [extAllP_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inr ?_⟩)
        rw [extAllP_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · exact Or.inr (Or.inr (Or.inl hC))
      · exact Or.inr (Or.inr (Or.inr hF))
  simpa only [Finset.sum_singleton] using h

/-! ## Query bounds -/

/-- **The adversary's budget in the permutation model**: each stage makes at most `q k` hash
queries of each kind, `qE` cipher queries (forward or inverse) and `n` hash queries in all. -/
structure AdversaryP.Budget (A : AdversaryP K qR) (q : Kind → ℕ) (qE n : ℕ) : Prop where
  init_k : IsKindQueryBoundP A.init q
  init_e : IsQueryBoundP A.init (fun t => t.isRight = true) qE
  init_h : IsQueryBoundP A.init (fun t => t.isLeft = true) n
  query_k : ∀ s, IsKindQueryBoundP (A.query s) q
  query_e : ∀ s, IsQueryBoundP (A.query s) (fun t => t.isRight = true) qE
  query_h : ∀ s, IsQueryBoundP (A.query s) (fun t => t.isLeft = true) n
  final_k : ∀ s, IsKindQueryBoundP (A.final s) q
  final_e : ∀ s, IsQueryBoundP (A.final s) (fun t => t.isRight = true) qE
  final_h : ∀ s, IsQueryBoundP (A.final s) (fun t => t.isLeft = true) n

section Bounds

variable {lr pk sk A} {q : Kind → ℕ} {qE n : ℕ} (hA : A.Budget q qE n)
include hA

theorem runIssP_k (m : ℕ) (s : A.σ) : IsKindQueryBoundP (runIssP lr sk A m s) (m • (q + vK)) := by
  induction m generalizing s with
  | zero => trivial
  | succ m ih =>
    refine (isKindQueryBoundP_bind (hA.query_k s) fun sq =>
      isKindQueryBoundP_bind (isKindQueryBoundP_liftP (anchorU_k lr sk sq.2)) fun ra =>
        isKindQueryBoundP_bind (q₂ := 0) (ob := fun rest =>
          (pure (rest.1, (sq.2, ra.2) :: rest.2) : OracleComp specP (A.σ × List (IQ K × Bool))))
          (ih _) fun _ => trivial).mono (le_of_eq ?_)
    rw [succ_nsmul]; abel

theorem runIssP_e (m : ℕ) (s : A.σ) : IsQueryBoundP (runIssP lr sk A m s)
    (fun t => t.isRight = true) (m * (qE + cellI lr)) := by
  induction m generalizing s with
  | zero => trivial
  | succ m ih =>
    refine (isQueryBoundP_bind (hA.query_e s) fun sq _ =>
      isQueryBoundP_bind (isQueryBoundP_right_liftP (anchorU_e lr sk sq.2)) fun ra _ =>
        isQueryBoundP_bind (m := 0) (ob := fun rest =>
          (pure (rest.1, (sq.2, ra.2) :: rest.2) : OracleComp specP (A.σ × List (IQ K × Bool))))
          (ih _) fun _ _ => trivial).mono (le_of_eq ?_)
    ring

theorem runIssP_h (m : ℕ) (s : A.σ) : IsQueryBoundP (runIssP lr sk A m s)
    (fun t => t.isLeft = true) (m * (n + (2 + verifierTotal))) := by
  induction m generalizing s with
  | zero => trivial
  | succ m ih =>
    refine (isQueryBoundP_bind (hA.query_h s) fun sq _ =>
      isQueryBoundP_bind (isQueryBoundP_left_liftP (anchorU_h lr sk sq.2)) fun ra _ =>
        isQueryBoundP_bind (m := 0) (ob := fun rest =>
          (pure (rest.1, (sq.2, ra.2) :: rest.2) : OracleComp specP (A.σ × List (IQ K × Bool))))
          (ih _) fun _ _ => trivial).mono (le_of_eq ?_)
    ring

theorem gameP_k : IsKindQueryBoundP (gameP lr pk sk qI A) (gameK q qI qR) := by
  unfold gameP
  refine (isKindQueryBoundP_bind hA.init_k fun s =>
    isKindQueryBoundP_bind (runIssP_k hA qI s) fun r =>
      isKindQueryBoundP_bind (hA.final_k r.1) fun R =>
        isKindQueryBoundP_map _ (isKindQueryBoundP_liftP (runRed_k lr pk R))).mono (le_of_eq ?_)
  simp only [gameK, OMUF.gameK, smul_add, add_smul]
  abel

theorem gameP_e :
    IsQueryBoundP (gameP lr pk sk qI A) (fun t => t.isRight = true) (gameE lr qE qI qR) := by
  unfold gameP
  refine (isQueryBoundP_bind hA.init_e fun s _ =>
    isQueryBoundP_bind (runIssP_e hA qI s) fun r _ =>
      isQueryBoundP_bind (hA.final_e r.1) fun R _ =>
        (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_right_liftP (runRed_e lr pk R))).mono
          (le_of_eq ?_)
  simp only [gameE]; ring

theorem gameP_h :
    IsQueryBoundP (gameP lr pk sk qI A) (fun t => t.isLeft = true) (gameH n qI qR) := by
  unfold gameP
  refine (isQueryBoundP_bind hA.init_h fun s _ =>
    isQueryBoundP_bind (runIssP_h hA qI s) fun r _ =>
      isQueryBoundP_bind (hA.final_h r.1) fun R _ =>
        (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_left_liftP (runRed_h lr pk R))).mono
          (le_of_eq ?_)
  simp only [gameH, OMUF.gameH]; ring

end Bounds

/-! ## The simultaneous bounds -/

/-- **The simultaneous extraction failure of the bound issuance proofs, permutation model**
(`epsIsim` with `failEpsP`). -/
noncomputable def epsIsimP (q : Kind → ℕ) (qE m : ℕ) : ℝ≥0∞ :=
  (q .h21 + m) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + m) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
    (q .h23 + m) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsSim q m + stmtBindEpsSim q m +
    m * failEpsP q qE

/-- **The simultaneous extraction failure of the unbound issuance and redemption proofs together,
permutation model** (`epsUsim` with `failEpsP` and the total hash count `n + 2q₂₁`). -/
noncomputable def epsUsimP (q : Kind → ℕ) (qE n mI mR : ℕ) : ℝ≥0∞ :=
  (q .h21 + (mI + mR)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + (mI + mR)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 * q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + (mI + mR)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    chainHitEpsCombSim q Arith.Moussaka.M (mI + mR) + stmtBindEpsSim q (mI + mR) +
    mI * failEpsP q qE + mR * failEpsP q qE

variable {lr pk sk qI A} {q : Kind → ℕ} {qE n : ℕ}

/-- **The bound issuance proofs, simultaneously, permutation model** (`moussakaIssue_sim_specP`). -/
theorem prEvent_simBI_leP (hA : A.Budget q qE n) :
    Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        SimBI lr π.fwd v] ≤ epsIsimP (gameK q qI qR) (gameE lr qE qI qR) qI := by
  have h := moussakaIssue_sim_specP (ι := ιI) (β := GOut K) (fun s => s.1) (fun s => s.2.1)
    (fun s => s.2.2) lr (hinjI lr) (PBIP lr pk sk qI A 0) (fun j => PBIP lr pk sk qI A j)
    (Finset.range qI) _ (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (gameP_e qI hA)) _
    (isKindQueryBoundP_map _ (gameP_k qI hA))
    (fun _ _ => isKindQueryBoundP_map _ (gameP_k qI hA)) _
    ((isQueryBoundP_map_iff _ _ _).2 (gameP_h qI hA))
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (gameP_h qI hA))
    (fun π => prefixRuns_normP_map _ π (gameP lr pk sk qI A) projBI 0 _)
    (extAllP lr pk sk qI A) (fun π v => SimBI lr π.fwd v) fun π g hev => by
      obtain ⟨r, hr, hb⟩ := hev
      rw [extAllP_eval] at hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
      exact ⟨j, Finset.mem_range.2 (List.mem_range.1 hj), hb⟩
  simpa only [Finset.card_range, epsIsimP] using h

/-- **The unbound issuance and redemption proofs, simultaneously and together, permutation
model** (`moussakaUnbound_sim_joint_specP`: both relations' provers are projections of the one
game, jointly normalized). -/
theorem prEvent_simU_leP (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        SimU lr pk π.fwd v] ≤
      epsUsimP (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qI qR := by
  have h := moussakaUnbound_sim_joint_specP (ιI := ιI) (βI := GOut K) (ιR := ιR K) (βR := GOut K)
    (stUI lr) lr (fun s => s.1) (fun s => Unbound.moussakaUnboundIssue_stmt _ _ lr)
    (fun s => s.2.1) (hinjUI lr)
    (stUR lr pk) (fun s => ancR pk s) (fun s => by simpa using s.2.1) (fun s => s.1.2.1)
    (fun s => s.1.2.2.1) (fun s => s.1.2.2.2.1) (fun s => s.1.2.2.2.2)
    (fun s => Unbound.moussakaUnboundRedeem_stmt _ _ _ _ _ lr) (fun s => s.2.2.1)
    (hinjUR lr pk hdig hdinj)
    (PUIP lr pk sk qI A 0) (fun j => PUIP lr pk sk qI A j)
    (PURP lr pk sk qI A 0) (fun j => PURP lr pk sk qI A j)
    (Finset.range qI) (Finset.range qR) _
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (gameP_e qI hA))
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (gameP_e qI hA)) _
    (fun _ _ => isKindQueryBoundP_map _ (gameP_k qI hA))
    (isKindQueryBoundP_map _ (gameP_k qI hA))
    (fun _ _ => isKindQueryBoundP_map _ (gameP_k qI hA)) _
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (gameP_h qI hA))
    ((isQueryBoundP_map_iff _ _ _).2 (gameP_h qI hA))
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (gameP_h qI hA))
    (fun π => prefixRuns_normJ_map _ _ π (gameP lr pk sk qI A) projUI 0 _)
    (fun π => prefixRuns_normJ_map _ _ π (gameP lr pk sk qI A) projUR 0 _)
    (fun π g => tableQueryLog_runE_normJ_map _ _ π _ _ _ g)
    (extAllP lr pk sk qI A) (fun π v => SimU lr pk π.fwd v) fun π g hev => by
      rcases hev with ⟨r, hr, hb⟩ | ⟨r, hr, hb⟩
      · rw [extAllP_eval] at hr
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
        exact Or.inl ⟨j, Finset.mem_range.2 (List.mem_range.1 hj), hb⟩
      · rw [extAllP_eval] at hr
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
        exact Or.inr ⟨j, Finset.mem_range.2 (List.mem_range.1 hj), hb⟩
  simpa only [Finset.card_range, epsUsimP] using h

/-- **Theorem U1 (unforgeability per redemption context) with simultaneous extraction,
permutation model.** For an adversary with forward and inverse cipher queries within its budget
and honest Anchors with distinct 32-byte key digests:

    Pr[Win] ≤ εI^simP(q', q'_E, qI) + εU^simP(q', q'_E, n', qI, qR) + Pr[Coll] + Pr[Forge],

at the budgets of `omufU_le_num`; `Coll` and `Forge` are `B₁`'s and `B₂`'s wins on the extracted
inputs (as in `omufU_le_num_sim`). -/
theorem omufU_le_num_simP (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (runP π (gameP lr pk sk qI A))).run' ∅}[
        Win r] ≤
      epsIsimP (gameK q qI qR) (gameE lr qE qI qR) qI +
      epsUsimP (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qI qR +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        Coll lr pk π.fwd v] +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        Forge lr pk π.fwd v] :=
  (omufU_le_simP lr pk sk qI A).trans (add_le_add (add_le_add (add_le_add
    (prEvent_simBI_leP hA) (prEvent_simU_leP hA hdig hdinj)) le_rfl) le_rfl)

end OMUFU

end VoleMole.ROM.IC
