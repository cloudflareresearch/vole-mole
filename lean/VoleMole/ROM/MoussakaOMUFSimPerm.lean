import VoleMole.ROM.SimPermJointSpec
import VoleMole.ROM.MoussakaOMUFSim

/-!
# Moussaka Theorem 1 with simultaneous extraction, permutation model

`ROM/MoussakaOMUFSim.lean`'s `omuf_le_num_sim` with the ideal cipher as random permutations and an
adversary that makes **forward and inverse** cipher queries (`ROM/PermModel.lean`). The honest
parties (the Anchors' and the Moderator's verifiers) read the cipher forward only.

* `liftP`: a forward-only computation as a computation of the permutation model;
  `runP π G`: a computation of the permutation model against the permutation table `π` (hash
  queries to the random oracle). Query bounds and evaluations of both.
* `AdversaryP`, `gameP`: the OMUF adversary and game of the permutation model (the game of
  `ROM/MoussakaOMUF.lean` with the honest parties lifted). `AdversaryP.toIC lr π`: the adversary
  at a fixed table, its stages normalized (`normJ`); per table the two games have one output
  (`gameP_eval`), so `game_eval` and `win_imp`'s argument apply.
* `PIP`, `PRP`: the provers, projections of `gameP` (specP); their games run the joint
  normalization `normJ (mousPI lr) (mousPR lr) π` (`ROM/PermJoint.lean`). `accepted_IP`,
  `accepted_RP`, **`win_impP`**: a win means an accepted, unextracted proof, a `Com` collision or a
  CT-UF^open forgery among the extracted openings (as `win_imp`).
* **`omuf_le_simP`** (the reduction), **`prEvent_simIR_leP`** (`moussaka_sim_joint_specP`),
  **`omuf_le_num_simP`**:

      Pr[Win] ≤ εIR^simP(q', q'_E, n', qI, qR) + Pr[Coll] + Pr[Forge],

  `εIR^simP` = `epsIRsim` with the permutation model's failure terms (`failEpsP`) and the joint
  normalization's two `H₄` queries per `H₂¹` query in the total hash count (`n' + 2q'₂₁`), at the
  budgets `q' = gameK q qI qR`, `q'_E = gameE lr qE qI qR`, `n' = gameH n qI qR` of `omuf_le_num`
  (`q'_E` counts the adversary's forward and inverse cipher queries and the honest verifiers').
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ROM

/-! ## Forward-only computations and runs in the permutation model -/

section Lift

variable {α β : Type}

/-- **A forward-only computation in the permutation model** (cipher query `c` ↦ forward `c`). -/
def liftP (X : OracleComp specIC α) : OracleComp specP α :=
  OracleComp.construct (C := fun _ => OracleComp specP α)
    (fun a => pure a)
    (fun t _ rec => match t, rec with
      | .inl d, rec => liftM (specP.query (.inl d)) >>= rec
      | .inr c, rec => liftM (specP.query (.inr (true, c))) >>= rec)
    X

@[simp] lemma liftP_pure (a : α) : liftP (pure a : OracleComp specIC α) = pure a := rfl

lemma liftP_inl (d : Dom) (k : specIC.Range (.inl d) → OracleComp specIC α) :
    liftP (liftM (specIC.query (.inl d)) >>= k) =
      liftM (specP.query (.inl d)) >>= fun u => liftP (k u) := rfl

lemma liftP_inr (c : Cell) (k : specIC.Range (.inr c) → OracleComp specIC α) :
    liftP (liftM (specIC.query (.inr c)) >>= k) =
      liftM (specP.query (.inr (true, c))) >>= fun u => liftP (k u) := rfl

theorem evalWithAnswerFn_liftP (h : Table) (π : PTable) (X : OracleComp specIC α) :
    evalWithAnswerFn (QueryImpl.ofFn (joinP h π)) (liftP X) =
      evalWithAnswerFn (QueryImpl.ofFn (join h π.fwd)) X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with d | c
    · rw [liftP_inl]
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      exact ih (h d)
    · rw [liftP_inr]
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      exact ih _

theorem isKindQueryBoundP_liftP {X : OracleComp specIC α} {q : Kind → ℕ}
    (hq : IsKindQueryBoundIC X q) : IsKindQueryBoundP (liftP X) q := by
  induction X using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [IsKindQueryBoundIC, isQueryBound_query_bind_iff] at hq
    rcases t with d | c
    · rw [liftP_inl, IsKindQueryBoundP, isQueryBound_query_bind_iff]
      exact ⟨hq.1, fun u => ih u (hq.2 u)⟩
    · rw [liftP_inr, IsKindQueryBoundP, isQueryBound_query_bind_iff]
      exact ⟨trivial, fun u => ih u (hq.2 u)⟩

theorem isQueryBoundP_right_liftP {X : OracleComp specIC α} {n : ℕ}
    (hn : IsQueryBoundP X (fun t => t.isRight = true) n) :
    IsQueryBoundP (liftP X) (fun t => t.isRight = true) n := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rcases t with d | c
    · rw [liftP_inl, isQueryBoundP_query_bind_iff]
      simp only [Sum.isRight_inl, Bool.false_eq_true, not_false_eq_true, true_or, ite_false,
        true_and] at hn ⊢
      exact fun u => ih u (hn u)
    · rw [liftP_inr, isQueryBoundP_query_bind_iff]
      simp only [Sum.isRight_inr, not_true_eq_false, false_or, ite_true] at hn ⊢
      exact ⟨hn.1, fun u => ih u (hn.2 u)⟩

theorem isQueryBoundP_left_liftP {X : OracleComp specIC α} {n : ℕ}
    (hn : IsQueryBoundP X (fun t => t.isLeft = true) n) :
    IsQueryBoundP (liftP X) (fun t => t.isLeft = true) n := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rcases t with d | c
    · rw [liftP_inl, isQueryBoundP_query_bind_iff]
      simp only [Sum.isLeft_inl, not_true_eq_false, false_or, ite_true] at hn ⊢
      exact ⟨hn.1, fun u => ih u (hn.2 u)⟩
    · rw [liftP_inr, isQueryBoundP_query_bind_iff]
      simp only [Sum.isLeft_inr, Bool.false_eq_true, not_false_eq_true, true_or, ite_false,
        true_and] at hn ⊢
      exact fun u => ih u (hn u)

theorem isKindQueryBoundP_bind {oa : OracleComp specP α} {ob : α → OracleComp specP β}
    {q₁ q₂ : Kind → ℕ} (h₁ : IsKindQueryBoundP oa q₁) (h₂ : ∀ a, IsKindQueryBoundP (ob a) q₂) :
    IsKindQueryBoundP (oa >>= ob) (q₁ + q₂) := by
  refine isQueryBound_bind (combine := (· + ·)) (fun t b₁ b₂ b hb => ?_) (fun t b₁ b₂ b hb => ?_)
    h₁ h₂
  · cases t with
    | inl d => simp only [Pi.add_apply] at hb ⊢; omega
    | inr x => exact ⟨trivial, trivial⟩
  · cases t with
    | inl d =>
      constructor <;> funext k <;> by_cases hk : k = d.1 <;>
        simp [hk, Function.update_of_ne, Pi.add_apply] <;> omega
    | inr x => exact ⟨rfl, rfl⟩

theorem IsKindQueryBoundP.mono {oa : OracleComp specP α} {q q' : Kind → ℕ}
    (h : IsKindQueryBoundP oa q) (hle : q ≤ q') : IsKindQueryBoundP oa q' := by
  induction oa using OracleComp.inductionOn generalizing q q' with
  | pure _ => trivial
  | query_bind t k ih =>
    unfold IsKindQueryBoundP at h ⊢
    rw [isQueryBound_query_bind_iff] at h ⊢
    obtain ⟨hc, hk⟩ := h
    cases t with
    | inl d =>
      refine ⟨lt_of_lt_of_le hc (hle d.1), fun u => ih u (hk u) ?_⟩
      intro k'
      show Function.update q d.1 (q d.1 - 1) k' ≤ Function.update q' d.1 (q' d.1 - 1) k'
      by_cases hk' : k' = d.1
      · rw [hk', Function.update_self, Function.update_self]
        exact Nat.sub_le_sub_right (hle d.1) 1
      · rw [Function.update_of_ne hk', Function.update_of_ne hk']; exact hle k'
    | inr x => exact ⟨trivial, fun u => ih u (hk u) hle⟩

theorem isKindQueryBoundP_map {oa : OracleComp specP α} (f : α → β) {q : Kind → ℕ}
    (h : IsKindQueryBoundP oa q) : IsKindQueryBoundP (f <$> oa) q :=
  (isQueryBound_map_iff _ _ _ _ _).2 h

/-- **A computation of the permutation model against the table `π`**: hash queries to the random
oracle, cipher queries answered by `π` forward or inverse. -/
def runP (π : PTable) (G : OracleComp specP α) : OracleComp spec α :=
  OracleComp.construct (C := fun _ => OracleComp spec α)
    (fun a => pure a)
    (fun t _ rec => match t, rec with
      | .inl d, rec => liftM (spec.query d) >>= rec
      | .inr c, rec => rec (pans π c))
    G

theorem evalWithAnswerFn_runP (g : Table) (π : PTable) (G : OracleComp specP α) :
    evalWithAnswerFn (QueryImpl.ofFn g) (runP π G) =
      evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) G := by
  induction G using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with d | c
    · show evalWithAnswerFn (QueryImpl.ofFn g) (liftM (spec.query d) >>= fun u => runP π (k u)) = _
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      exact ih (g d)
    · show evalWithAnswerFn (QueryImpl.ofFn g) (runP π (k (pans π c))) = _
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      exact ih _

/-- Adding `iv` queries does not change the output. -/
theorem evalWithAnswerFn_addIV (p : Params) (f : ∀ t, AnsP t) (P : OracleComp specP α) :
    evalWithAnswerFn (QueryImpl.ofFn f) (addIV p P) = evalWithAnswerFn (QueryImpl.ofFn f) P := by
  induction P using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with d | c
    · rw [addIV_inl]
      split_ifs <;>
      · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
        exact ih _
    · rw [addIV_inr]
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      exact ih _

/-- **The joint normalization outputs what `P` outputs against the permutation oracle.** -/
theorem evalWithAnswerFn_normJ (pI pR : Params) (h : Table) (π : PTable) (P : OracleComp specP α) :
    evalWithAnswerFn (QueryImpl.ofFn (join h π.fwd)) (normJ pI pR π P) =
      evalWithAnswerFn (QueryImpl.ofFn (joinP h π)) P := by
  rw [normJ, evalWithAnswerFn_normP, evalWithAnswerFn_addIV]

end Lift

namespace OMUF

/-! ## The game in the permutation model -/

variable {K qR : ℕ}

/-- **An OMUF adversary of the permutation model**: as `Adversary`, with forward and inverse
cipher queries. -/
structure AdversaryP (K qR : ℕ) where
  σ : Type
  init : OracleComp specP σ
  query : σ → OracleComp specP (σ × IssQ K)
  absorb : σ → IssResp → σ
  final : σ → OracleComp specP (Fin qR → RedQ K)

/-- **The adversary at a fixed permutation table**: its stages normalized (`normJ`), an
`Adversary` of the PRF view. -/
def AdversaryP.toIC (lr : Bool) (π : PTable) (A : AdversaryP K qR) : Adversary K qR where
  σ := A.σ
  init := normJ (mousPI lr) (mousPR lr) π A.init
  query s := normJ (mousPI lr) (mousPR lr) π (A.query s)
  absorb := A.absorb
  final s := normJ (mousPI lr) (mousPR lr) π (A.final s)

@[simp] lemma AdversaryP.toIC_init (lr : Bool) (π : PTable) (A : AdversaryP K qR) :
    (A.toIC lr π).init = normJ (mousPI lr) (mousPR lr) π A.init := rfl

@[simp] lemma AdversaryP.toIC_query (lr : Bool) (π : PTable) (A : AdversaryP K qR) (s : A.σ) :
    (A.toIC lr π).query s = normJ (mousPI lr) (mousPR lr) π (A.query s) := rfl

@[simp] lemma AdversaryP.toIC_absorb (lr : Bool) (π : PTable) (A : AdversaryP K qR) :
    (A.toIC lr π).absorb = A.absorb := rfl

@[simp] lemma AdversaryP.toIC_final (lr : Bool) (π : PTable) (A : AdversaryP K qR) (s : A.σ) :
    (A.toIC lr π).final s = normJ (mousPI lr) (mousPR lr) π (A.final s) := rfl

/-- `n` Issue rounds from the state `s`, the honest Anchor lifted. -/
def runIssP (lr : Bool) (sk : Fin K → Spec.Signer) (A : AdversaryP K qR) :
    ℕ → A.σ → OracleComp specP (A.σ × List (IssQ K × Bool))
  | 0, s => pure (s, [])
  | n + 1, s => A.query s >>= fun sq => liftP (anchorIC lr sk sq.2) >>= fun ra =>
      runIssP lr sk A n (A.absorb sq.1 ra.1) >>= fun rest => pure (rest.1, (sq.2, ra.2) :: rest.2)

/-- **The OMUF game in the permutation model** with `qI` Issue queries. -/
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
    show evalWithAnswerFn _ (A.query s >>= fun sq => liftP (anchorIC lr sk sq.2) >>= fun ra =>
        runIssP lr sk A n (A.absorb sq.1 ra.1) >>= fun rest =>
          (pure (rest.1, (sq.2, ra.2) :: rest.2) : OracleComp specP _)) =
      evalWithAnswerFn _ (normJ (mousPI lr) (mousPR lr) π (A.query s) >>= fun sq =>
        anchorIC lr sk sq.2 >>= fun ra =>
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
    evalWithAnswerFn _ (normJ (mousPI lr) (mousPR lr) π A.init >>= fun s =>
      runIss lr sk (A.toIC lr π) qI s >>= fun r =>
        normJ (mousPI lr) (mousPR lr) π (A.final r.1) >>= fun R =>
          (fun red => (r.2, red)) <$> runRed lr pk R)
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_map, evalWithAnswerFn_liftP, runIssP_eval,
    evalWithAnswerFn_normJ]

/-- **The prover `P^iss_j` of the permutation model**: the whole game, the `j`-th issuance proof
as output. -/
def PIP (j : ℕ) : OracleComp specP (ByteArray × (ιI × GOut K)) := projI j <$> gameP lr pk sk qI A

/-- **The prover `P^red_j` of the permutation model.** -/
def PRP (j : ℕ) : OracleComp specP (ByteArray × (ιR K × GOut K)) :=
  projR j <$> gameP lr pk sk qI A

/-- The joint normalization of the Moussaka relations. -/
abbrev nJ (π : PTable) {α : Type} (P : OracleComp specP α) : OracleComp specIC α :=
  normJ (mousPI lr) (mousPR lr) π P

section Accepted

variable (g : Table) (π : PTable)

/-- **An accepted Issue query is accepted by `P^iss_j`'s verifier, at its statement.** -/
theorem accepted_IP {j : ℕ} {q : IssQ K}
    (hj : (evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd))
      (game lr pk sk qI (A.toIC lr π))).1[j]? = some (q, true)) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stI lr) (nJ lr π (PIP lr pk sk qI A j)) π.fwd)
    r.2.2.accept = true ∧ (stOut r).1 = (q.t, q.ctx) := by
  obtain ⟨-, hrec, -⟩ := game_eval g π.fwd lr pk sk (A.toIC lr π) qI
  obtain ⟨hwf, hv⟩ := hrec _ (List.mem_of_getElem? hj) rfl
  have hsz : q.t.size = 45 ∧ q.ctx.size = 16 := ⟨size_t hwf, hwf.2⟩
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (nJ lr π (PIP lr pk sk qI A j)) =
      (q.pf, (⟨(q.t, q.ctx), hsz⟩, evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd))
        (game lr pk sk qI (A.toIC lr π)))) := by
    rw [nJ, evalWithAnswerFn_normJ, PIP, evalWithAnswerFn_map, gameP_eval]
    simp only [projI, hj, hsz, and_self, dite_true]
  refine ⟨?_, ?_⟩
  · rw [gameA_transcript, sA, hP]; exact hv
  · rw [stOut_gameA, sA, hP]

/-- **An accepted redemption is accepted by `P^red_j`'s verifier, at its statement.** -/
theorem accepted_RP {j : ℕ} {rq : RedQ K}
    (hj : (evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd))
      (game lr pk sk qI (A.toIC lr π))).2[j]? = some (rq, true)) :
    let r := evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stR lr pk) (nJ lr π (PRP lr pk sk qI A j)) π.fwd)
    r.2.2.accept = true ∧ (stOut r).1 = (rq.S, rq.nf, rq.ci, rq.cr, rq.cd) := by
  obtain ⟨-, -, -, hrec⟩ := game_eval g π.fwd lr pk sk (A.toIC lr π) qI
  obtain ⟨hwf, hv⟩ := hrec _ (List.mem_of_getElem? hj) rfl
  have hsz : rq.S.length ≤ 64 ∧ rq.nf.size = 24 ∧ rq.ci.size = 16 ∧ rq.cr.size = 16 :=
    ⟨hwf.2.1, size_nf hwf, hwf.2.2.2.2.1, hwf.2.2.2.2.2⟩
  have hP : evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (nJ lr π (PRP lr pk sk qI A j)) =
      (rq.pf, (⟨(rq.S, rq.nf, rq.ci, rq.cr, rq.cd), hsz⟩,
        evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (game lr pk sk qI (A.toIC lr π)))) := by
    rw [nJ, evalWithAnswerFn_normJ, PRP, evalWithAnswerFn_map, gameP_eval]
    simp only [projR, hj, hsz, and_self, dite_true]
  refine ⟨?_, ?_⟩
  · rw [gameA_transcript, sA, hP]; exact hv
  · rw [stOut_gameA, sA, hP]

end Accepted

/-! ## The reduction -/

/-- **The reductions' run in the permutation model**: the game, then every proof's straight-line
extraction and verification (`gameA` of the jointly normalized provers at the forward table). -/
def extAllP (π : PTable) : OracleComp spec (GOut K × List (OutI K) × List (OutR K)) :=
  runP π (gameP lr pk sk qI A) >>= fun o =>
    (List.range qI).mapM (fun j =>
      gameA CrtGen.tables (stI lr) (nJ lr π (PIP lr pk sk qI A j)) π.fwd) >>= fun oi =>
      (List.range qR).mapM (fun j =>
        gameA CrtGen.tables (stR lr pk) (nJ lr π (PRP lr pk sk qI A j)) π.fwd) >>=
        fun orr => pure (o, oi, orr)

theorem extAllP_eval (g : Table) (π : PTable) :
    evalWithAnswerFn (QueryImpl.ofFn g) (extAllP lr pk sk qI A π) =
      (evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (game lr pk sk qI (A.toIC lr π)),
        (List.range qI).map (fun j => evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stI lr) (nJ lr π (PIP lr pk sk qI A j)) π.fwd)),
        (List.range qR).map (fun j => evalWithAnswerFn (QueryImpl.ofFn g)
          (gameA CrtGen.tables (stR lr pk) (nJ lr π (PRP lr pk sk qI A j)) π.fwd))) := by
  simp only [extAllP, evalWithAnswerFn_bind, evalWithAnswerFn_runP, gameP_eval,
    evalWithAnswerFn_mapM, evalWithAnswerFn_pure]

/-- **The per-table core of Theorem 1 in the permutation model** (`win_imp`): a win means that
some accepted proof is not extracted, or `B₁` finds a `Com` collision, or `B₂` a CT-UF^open
forgery. -/
theorem win_impP (g : Table) (π : PTable)
    (hwin : Win (evalWithAnswerFn (QueryImpl.ofFn (joinP g π)) (gameP lr pk sk qI A))) :
    (∃ j ∈ Finset.range qI, BadI π.fwd lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (nJ lr π (PIP lr pk sk qI A j)) π.fwd))) ∨
    (∃ j ∈ Finset.range qR, BadR π.fwd lr pk (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stR lr pk) (nJ lr π (PRP lr pk sk qI A j)) π.fwd))) ∨
    Coll lr pk π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (extAllP lr pk sk qI A π)) ∨
    Forge lr pk π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (extAllP lr pk sk qI A π)) := by
  classical
  rw [gameP_eval] at hwin
  obtain ⟨hlI, -, hlR, -⟩ := game_eval g π.fwd lr pk sk (A.toIC lr π) qI
  rw [extAllP_eval]
  set E := π.fwd
  set o := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI (A.toIC lr π)) with ho
  set oi := (List.range qI).map (fun j => evalWithAnswerFn (QueryImpl.ofFn g)
    (gameA CrtGen.tables (stI lr) (nJ lr π (PIP lr pk sk qI A j)) E)) with hoi
  set orr := (List.range qR).map (fun j => evalWithAnswerFn (QueryImpl.ofFn g)
    (gameA CrtGen.tables (stR lr pk) (nJ lr π (PRP lr pk sk qI A j)) E)) with horr
  by_contra hno
  simp only [BadI, BadR, not_or, not_exists, not_and, Finset.mem_range, not_not] at hno
  obtain ⟨hI, hR, hC, hF⟩ := hno
  obtain ⟨c, hc⟩ := hwin
  have key := Moussaka.collision_or_forgery comO (fun x => x.2.1) (fun x => (x.2.2.1, x.1))
    (SI lr E (o, oi, orr) ∪ SR lr pk E (o, oi, orr)) (SR lr pk E (o, oi, orr))
    Set.subset_union_right (issL o) (redL o) ?_ ?_ c hc
  · rcases key with ⟨x, hx, x', hx', hne, he⟩ | ⟨x, hx, hn⟩
    · exact hC ⟨x, hx, x', hx', hne, he⟩
    · exact hF ⟨x, hx, hn⟩
  · intro q hq
    simp only [issL, List.mem_map, List.mem_filter] at hq
    obtain ⟨p, ⟨hp, hpb⟩, rfl⟩ := hq
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    have hjl : j < qI := by rw [← hlI]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hj' : o.1[j]? = some (p.1, true) := by rw [hj]; cases p; simp_all
    obtain ⟨hacc, hst⟩ := accepted_IP lr pk sk qI A g π hj'
    obtain ⟨x, hx, hxc, hxt⟩ := opI_of_ext E lr (hI j hjl hacc)
    refine ⟨x, Or.inl ⟨j, p.1, _, hj', by simp [oi, hjl], hx⟩, ?_, ?_⟩
    · rw [hxc, hst]
    · rw [hxt, hst]
  · intro q hq
    simp only [redL, List.mem_map, List.mem_filter] at hq
    obtain ⟨p, ⟨hp, hpb⟩, rfl⟩ := hq
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    have hjl : j < qR := by rw [← hlR]; exact (List.getElem?_eq_some_iff.1 hj).1
    have hj' : o.2[j]? = some (p.1, true) := by rw [hj]; cases p; simp_all
    obtain ⟨hacc, hst⟩ := accepted_RP lr pk sk qI A g π hj'
    obtain ⟨x, hx, hxc, hxr⟩ := opR_of_ext E lr pk (hR j hjl hacc)
    refine ⟨x, ⟨j, p.1, _, hj', by simp [orr, hjl], hx⟩, ?_, ?_⟩
    · rw [hxc, hst]
    · rw [hxr, hst]

/-- **Theorem 1 in the permutation model, the reduction, with one simultaneous extraction
event.** -/
theorem omuf_le_simP :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (runP π (gameP lr pk sk qI A))).run' ∅}[
        Win r] ≤
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        SimIR lr pk π.fwd v] +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        Coll lr pk π.fwd v] +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        Forge lr pk π.fwd v] := by
  have h := prEvent_bind_le_sum4_of_table ($ᵗ PTable) (fun π => runP π (gameP lr pk sk qI A))
    (fun _ r => Win r) {0} ∅ (fun _ π => extAllP lr pk sk qI A π)
    (fun π v => SimIR lr pk π.fwd v) (fun _ π => extAllP lr pk sk qI A π) (fun _ _ => False)
    (fun π => extAllP lr pk sk qI A π) (fun π v => Coll lr pk π.fwd v)
    (fun π v => Forge lr pk π.fwd v) fun π g hw => by
      rw [evalWithAnswerFn_runP] at hw
      rcases win_impP lr pk sk qI A g π hw with ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | hC | hF
      · refine Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inl ?_⟩
        rw [extAllP_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inr ?_⟩
        rw [extAllP_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · exact Or.inr (Or.inr (Or.inl hC))
      · exact Or.inr (Or.inr (Or.inr hF))
  simpa only [Finset.sum_singleton, Finset.sum_empty, add_zero] using h

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
      isKindQueryBoundP_bind (isKindQueryBoundP_liftP (anchorIC_k lr sk sq.2)) fun ra =>
        isKindQueryBoundP_bind (q₂ := 0) (ob := fun rest =>
          (pure (rest.1, (sq.2, ra.2) :: rest.2) : OracleComp specP (A.σ × List (IssQ K × Bool))))
          (ih _) fun _ => trivial).mono (le_of_eq ?_)
    rw [succ_nsmul]; abel

theorem runIssP_e (m : ℕ) (s : A.σ) : IsQueryBoundP (runIssP lr sk A m s)
    (fun t => t.isRight = true) (m * (qE + verifyCellBound (parI lr))) := by
  induction m generalizing s with
  | zero => trivial
  | succ m ih =>
    refine (isQueryBoundP_bind (hA.query_e s) fun sq _ =>
      isQueryBoundP_bind (isQueryBoundP_right_liftP (anchorIC_e lr sk sq.2)) fun ra _ =>
        isQueryBoundP_bind (m := 0) (ob := fun rest =>
          (pure (rest.1, (sq.2, ra.2) :: rest.2) : OracleComp specP (A.σ × List (IssQ K × Bool))))
          (ih _) fun _ _ => trivial).mono (le_of_eq ?_)
    ring

theorem runIssP_h (m : ℕ) (s : A.σ) : IsQueryBoundP (runIssP lr sk A m s)
    (fun t => t.isLeft = true) (m * (n + (2 + verifierTotal))) := by
  induction m generalizing s with
  | zero => trivial
  | succ m ih =>
    refine (isQueryBoundP_bind (hA.query_h s) fun sq _ =>
      isQueryBoundP_bind (isQueryBoundP_left_liftP (anchorIC_h lr sk sq.2)) fun ra _ =>
        isQueryBoundP_bind (m := 0) (ob := fun rest =>
          (pure (rest.1, (sq.2, ra.2) :: rest.2) : OracleComp specP (A.σ × List (IssQ K × Bool))))
          (ih _) fun _ _ => trivial).mono (le_of_eq ?_)
    ring

theorem gameP_k : IsKindQueryBoundP (gameP lr pk sk qI A) (gameK q qI qR) := by
  unfold gameP
  refine (isKindQueryBoundP_bind hA.init_k fun s =>
    isKindQueryBoundP_bind (runIssP_k hA qI s) fun r =>
      isKindQueryBoundP_bind (hA.final_k r.1) fun R =>
        isKindQueryBoundP_map _ (isKindQueryBoundP_liftP (runRed_k lr pk R))).mono (le_of_eq ?_)
  simp only [gameK, smul_add, add_smul]
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
  simp only [gameH]; ring

end Bounds

/-! ## The bound -/

/-- **The simultaneous extraction failure of the issuance and redemption proofs together, in the
permutation model** (`epsIRsim` with `failEpsP` and the total hash count `n + 2q₂₁`). -/
noncomputable def epsIRsimP (q : Kind → ℕ) (qE n mI mR : ℕ) : ℝ≥0∞ :=
  (q .h21 + (mI + mR)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + (mI + mR)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 * q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + (mI + mR)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    chainHitEpsCombSim q Arith.Moussaka.M (mI + mR) + stmtBindEpsSim q (mI + mR) +
    mI * failEpsP q qE + mR * failEpsP q qE

variable {lr pk sk qI A} {q : Kind → ℕ} {qE n : ℕ}

/-- **The issuance and redemption proofs, simultaneously and together, in the permutation model**
(`moussaka_sim_joint_specP`: both relations' provers are projections of the one game). -/
theorem prEvent_simIR_leP (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        SimIR lr pk π.fwd v] ≤
      epsIRsimP (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qI qR := by
  have h := moussaka_sim_joint_specP (ιI := ιI) (βI := GOut K) (ιR := ιR K) (βR := GOut K)
    (fun s => s.1) (fun s => s.2.1) (fun s => s.2.2) lr (hinjI lr)
    (fun s => ancR pk s)
    (fun s => by simpa using s.2.1) (fun s => s.1.2.1) (fun s => s.1.2.2.1)
    (fun s => s.1.2.2.2.1) (fun s => s.1.2.2.2.2) (fun s => s.2.2.1) (fun s => s.2.2.2.1)
    (fun s => s.2.2.2.2) (hinjR lr pk hdig hdinj)
    (PIP lr pk sk qI A 0) (fun j => PIP lr pk sk qI A j)
    (PRP lr pk sk qI A 0) (fun j => PRP lr pk sk qI A j)
    (Finset.range qI) (Finset.range qR) _
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (gameP_e qI hA))
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (gameP_e qI hA)) _
    (fun _ _ => isKindQueryBoundP_map _ (gameP_k qI hA))
    (isKindQueryBoundP_map _ (gameP_k qI hA))
    (fun _ _ => isKindQueryBoundP_map _ (gameP_k qI hA)) _
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (gameP_h qI hA))
    ((isQueryBoundP_map_iff _ _ _).2 (gameP_h qI hA))
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (gameP_h qI hA))
    (fun π => prefixRuns_normJ_map _ _ π (gameP lr pk sk qI A) projI 0 _)
    (fun π => prefixRuns_normJ_map _ _ π (gameP lr pk sk qI A) projR 0 _)
    (fun π g => tableQueryLog_runE_normJ_map _ _ π _ _ _ g)
    (extAllP lr pk sk qI A) (fun π v => SimIR lr pk π.fwd v) fun π g hev => by
      rcases hev with ⟨r, hr, hb⟩ | ⟨r, hr, hb⟩
      · rw [extAllP_eval] at hr
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
        exact Or.inl ⟨j, Finset.mem_range.2 (List.mem_range.1 hj), hb⟩
      · rw [extAllP_eval] at hr
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
        exact Or.inr ⟨j, Finset.mem_range.2 (List.mem_range.1 hj), hb⟩
  simpa only [Finset.card_range, epsIRsimP] using h

/-- **Theorem 1 (one-more unforgeability) with simultaneous extraction, permutation model.** For
an adversary with forward and inverse cipher queries within its budget and honest Anchors with
distinct 32-byte key digests:

    Pr[Win] ≤ εIR^simP(q', q'_E, n', qI, qR) + Pr[Coll] + Pr[Forge],

at the budgets of `omuf_le_num` (`q' = gameK q qI qR`, `q'_E = gameE lr qE qI qR`,
`n' = gameH n qI qR`); `Coll` and `Forge` are `B₁`'s and `B₂`'s wins on the extracted openings
(as in `omuf_le_num_sim`). -/
theorem omuf_le_num_simP (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (runP π (gameP lr pk sk qI A))).run' ∅}[
        Win r] ≤
      epsIRsimP (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qI qR +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        Coll lr pk π.fwd v] +
      Pr{let π ← $ᵗ PTable; let v ← (simulateQ randomOracle (extAllP lr pk sk qI A π)).run' ∅}[
        Forge lr pk π.fwd v] :=
  (omuf_le_simP lr pk sk qI A).trans (add_le_add (add_le_add
    (prEvent_simIR_leP hA hdig hdinj) le_rfl) le_rfl)

end OMUF

end VoleMole.ROM.IC
