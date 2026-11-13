import VoleMole.ROM.OneMoreLemmaP

/-!
# PomFRIT's one-more game against Lemma P: a derived prover that reads the cipher only by queries

`lean/docs/security/pomfrit.md` §6.4 (gap G8). `ROM/OneMoreLemmaP.lean` relates a failed forgery
(`PFail i`) to the adaptive extraction game of the derived prover `proverI … i`, which reads the
cipher table `E` directly (its `chal1` and its hint `E₁` use `icPrg E.cipher`). The adaptive bound
`pomfritT_accept_le_major` is for provers that reach the cipher only through queries. This file
builds such a prover, `proverP … i`, and relates it to the game table by table.

* `chal1PreIC`: the verifier's steps up to `chal1` (`chal1Pre`) with the cipher as queries (as
  `ROM/VerifyIC.lean`'s `verifyIC`: `mu₁`, `iv`, the tree derivation and the needed cells queried,
  then `chal1Pre` with the PRG of the queried cells); per table it is `chal1Pre` with the ideal
  cipher's PRG (`evalWithAnswerFn_chal1PreIC`).
* **The forger with a void hint** (`wrapIC lr hint0`): the target oracle's answers do not depend on
  the hints, and the ghost of `wrapIC` records, for each target input, the log at its first query.
  So the hint the game stores at `x` is the hint rule at the ghost log of `x`
  (`InvH`, `eval_wrapIC_hint`).
* **The derived prover** (`proverP … i`): the forger (`wrapIC lr hint0`), the verifications of the
  earlier forgeries up to their target queries (`verPreAll`, with `chal1PreIC`, the reduction's own
  queries `auxSpec` and the target oracle's step), then the `i`-th forgery's `chal1`, the
  reduction's queries and its target query. It outputs the `i`-th forgery's proof, its statement
  index (the target oracle's answer and the binders) and, as auxiliary output, its `hash_to_target`
  input `x` and the ghost log of `x`. It reads neither the cipher table nor the hint rule.
* **Table by table** (`eval_proverP`, `log_proverP`): its output is the `i`-th forgery's data in the
  game, the hint the game stores at `x` is the hint rule at the ghost log, and its joint log is the
  forger's log followed by the verification queries.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.EndToEnd.SpecRel VoleMole.ZK.Sim

/-! ## `chal1` with the cipher as queries -/

section Chal1

/-- **`chal1Pre` per table.** -/
lemma evalWithAnswerFn_chal1Pre [HasPrg] (g : Table) (st : Statement) (proof : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn g) (chal1Pre st proof) =
      if (({ params := st.params, bytes := proof } : Proof).checkFormat = false) then none else
      match BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, proof⟩ (st.mu1 (Hashes.ofTable g)))
          (Proof.opening ⟨st.params, proof⟩) (Proof.delta ⟨st.params, proof⟩) with
      | none => none
      | some leaves =>
        some ((Hashes.ofTable g).hash .h21 (chal1Input ⟨st.params, proof⟩ (st.mu1 (Hashes.ofTable g))
          ((Hashes.ofTable g).hash .h1 (BAVC.comInput ((BAVC.leafHashInputs leaves.coms).map
            ((Hashes.ofTable g).hash .h1)))) st.binder1)) := by
  unfold chal1Pre
  by_cases hf : ({ params := st.params, bytes := proof } : Proof).checkFormat = true
  · simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false, evalWithAnswerFn_bind,
      evalWithAnswerFn_mu1Q, evalWithAnswerFn_hashQ, reduceCtorEq]
    split
    · rename_i h; simp only [ivOf] at h ⊢; rw [h]; rfl
    · rename_i leaves h
      simp only [ivOf] at h ⊢
      rw [h]
      simp [evalWithAnswerFn_mapM_hashQ]
  · simp only [Bool.not_eq_true] at hf
    simp [hf]

/-- **`chal1Pre` with two cipher tables that agree at the cells of the reconstruction.** -/
lemma chal1Pre_congr_cells {E E' : Cipher} (g : Table) (st : Statement) (proof : ByteArray)
    (h : ∀ x ∈ cellsE E st.params (ivOf (Hashes.ofTable g) ⟨st.params, proof⟩
      (st.mu1 (Hashes.ofTable g))) (⟨st.params, proof⟩ : Proof).opening
      (⟨st.params, proof⟩ : Proof).delta, E x.1 x.2 = E' x.1 x.2) :
    evalWithAnswerFn (QueryImpl.ofFn g) (@chal1Pre (icPrg E) st proof) =
      evalWithAnswerFn (QueryImpl.ofFn g) (@chal1Pre (icPrg E') st proof) := by
  rw [@evalWithAnswerFn_chal1Pre (icPrg E), @evalWithAnswerFn_chal1Pre (icPrg E'),
    reconstruct_congr_cells h]

/-- **The verifier's steps up to `chal1` with the cipher as queries**: `mu₁` and `iv`, the tree
derivation and the needed cells (queried, as in `verifyIC`), then `chal1Pre` with the PRG of the
queried cells. -/
def chal1PreIC (st : Statement) (proof : ByteArray) : OracleComp specIC (Option ByteArray) := do
  let pf : Proof := ⟨st.params, proof⟩
  let iv ← liftIC (ivQ st proof)
  let A ← treeQ iv pf.opening pf.delta
  let M ← cellsQ st.params iv A
  liftIC (@chal1Pre (icPrg (fillC M)) st proof)

/-- **Per table, `chal1PreIC` is `chal1Pre` with the ideal cipher's PRG.** -/
theorem evalWithAnswerFn_chal1PreIC (g : Table) (E : CTable) (st : Statement) (proof : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (chal1PreIC st proof) =
      evalWithAnswerFn (QueryImpl.ofFn g) (@chal1Pre (icPrg E.cipher) st proof) := by
  simp only [chal1PreIC, evalWithAnswerFn_bind, evalWithAnswerFn_liftIC, evalWithAnswerFn_ivQ,
    evalWithAnswerFn_treeQ]
  rw [evalWithAnswerFn_cellsQ]
  refine (chal1Pre_congr_cells g st proof fun x hx => ?_).symm
  show E x = (_ : Option Blk).getD 0
  erw [lookup_map_self E hx]
  rfl

end Chal1

/-! ## The forger with a void hint, and the ghost of the hints -/

section Hint

/-- The void hint rule. -/
def hint0 : QueryLog specIC → ByteArray → TG := fun _ _ => 0

/-- **The game's state and the void-hint state**: they differ only in the hints (`SameT`), and the
hint the game stores at each answered input is the hint rule at the ghost log of that input. -/
def InvH (hint : QueryLog specIC → ByteArray → TG) (hsH hsP : HTS) (gh : Gh) : Prop :=
  SameT hsH hsP ∧ ∀ x a e, hsH.1 x = some (a, e) → ∃ Lx, gh x = some Lx ∧ e = hint Lx x

lemma SameT.none_iff {s s' : HTS} (h : SameT s s') (x : ByteArray) :
    s.1 x = none ↔ s'.1 x = none := by
  have := h.1 x
  constructor
  · intro hx; rw [hx] at this; exact Option.map_eq_none_iff.1 this.symm
  · intro hx; rw [hx] at this; exact Option.map_eq_none_iff.1 this

/-- The ghost after a target query at `x` with the log `Lx`. -/
def ghStep (hs : HTS) (gh : Gh) (x : ByteArray) (Lx : QueryLog specIC) : Gh :=
  if hs.1 x = none then Function.update gh x (some Lx) else gh

/-- **A target query keeps the invariant.** -/
lemma InvH.step {hint : QueryLog specIC → ByteArray → TG} {hsH hsP : HTS} {gh : Gh}
    (h : InvH hint hsH hsP gh) (x : ByteArray) (Lx : QueryLog specIC) :
    (tStep addHint x (hint Lx x) hsH).1.1 = (tStep addHint x 0 hsP).1.1 ∧
      InvH hint (tStep addHint x (hint Lx x) hsH).2 (tStep addHint x 0 hsP).2
        (ghStep hsP gh x Lx) := by
  obtain ⟨e1, e2⟩ := tStep_sameT h.1 x (hint Lx x) 0
  refine ⟨e1, e2, fun y a e hy => ?_⟩
  obtain ⟨tH, lH, tgH, nH⟩ := hsH
  cases hx : tH x with
  | some v =>
    have hP : hsP.1 x ≠ none := fun hn => by
      have := (h.1.none_iff x).2 hn; simp only at this; rw [hx] at this; cases this
    have hst : tStep addHint x (hint Lx x) (tH, lH, tgH, nH) = (v, (tH, lH, tgH, nH)) := by
      simp [tStep, hx]
    rw [hst] at hy
    simp only [ghStep, hP, ite_false]
    exact h.2 y a e hy
  | none =>
    have hP : hsP.1 x = none := (h.1.none_iff x).1 (by simpa using hx)
    simp only [ghStep, hP, ite_true]
    by_cases hyx : y = x
    · subst hyx
      have hg := tStep_get addHint y (hint Lx y) (tH, lH, tgH, nH)
      rw [hy] at hg
      have hv : (tStep addHint y (hint Lx y) (tH, lH, tgH, nH)).1.2 = hint Lx y := by
        cases lH <;> simp [tStep, hx]
      refine ⟨Lx, by simp, ?_⟩
      rw [← hv, ← Option.some.inj hg]
    · have hk : tH y = some (a, e) := by
        have : (tStep addHint x (hint Lx x) (tH, lH, tgH, nH)).2.1 y = tH y := by
          cases lH <;> simp [tStep, hx, Function.update_of_ne hyx]
        rw [← this]; exact hy
      obtain ⟨Ly, hLy, he⟩ := h.2 y a e hk
      exact ⟨Ly, by rw [Function.update_of_ne hyx]; exact hLy, he⟩

variable (g : Table) (E : CTable) (lr : Bool) (hint : QueryLog specIC → ByteArray → TG)
  (pre : TG → SIss)

/-- **The forger with the hint rule and with the void hint, table by table**: the same output, log
and ghost, and states related by `InvH`. -/
theorem eval_wrapIC_hint {α : Type} (oa : OracleComp specU α) :
    ∀ (L : QueryLog specIC) (hsH hsP : HTS) (gh : Gh), InvH hint hsH hsP gh →
      let a := evalWithAnswerFn (QueryImpl.ofFn (join g E))
        ((simulateQ (wrapIC lr hint pre) oa).run (L, hsH, gh))
      let b := evalWithAnswerFn (QueryImpl.ofFn (join g E))
        ((simulateQ (wrapIC lr hint0 pre) oa).run (L, hsP, gh))
      a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2.2 = b.2.2.2 ∧ InvH hint a.2.2.1 b.2.2.1 a.2.2.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro L hsH hsP gh h; simpa using h
  | query_bind q k ih =>
    intro L hsH hsP gh h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with d | (x | t)
    · simp only [wrapIC, StateT.run_mk, evalWithAnswerFn_bind]
      exact ih _ _ _ _ _ h
    · simp only [wrapIC, StateT.run_mk, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      set ax := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (toHIC (auxSpec lr L x))
      obtain ⟨e1, e2⟩ := h.step x (L ++ ax)
      have hgh : (if hsP.1 x = none then Function.update gh x (some (L ++ ax)) else gh) =
          (if hsH.1 x = none then Function.update gh x (some (L ++ ax)) else gh) := by
        by_cases hx : hsP.1 x = none
        · rw [ite_eq_left hx, ite_eq_left ((h.1.none_iff x).2 hx)]
        · rw [ite_eq_right hx, ite_eq_right (fun h' => hx ((h.1.none_iff x).1 h'))]
      have := ih ((tStep addHint x (hint (L ++ ax) x) hsH).1.1) (L ++ ax) _ _ _ e2
      rw [ghStep] at this
      rw [← hgh]
      simp only [hint0] at this ⊢
      rw [e1] at this ⊢
      exact this
    · simp only [wrapIC, StateT.run_mk, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      refine ih _ _ _ _ _ ⟨⟨h.1.1, h.1.2.1, congrArg (· + 1) h.1.2.2⟩, h.2⟩

end Hint

/-! ## The derived prover -/

section Prover

variable (lr : Bool) (pk : UovPk)

/-- The `i`-th forgery's statement with an empty target (the verifier's steps up to `chal1` do not
read the target). -/
def st0 (sg : ByteArray) : Statement :=
  pomfritRedeemT pk (fun _ => ByteArray.empty) (sB1 lr sg) (sB2 lr sg) lr

/-- **An earlier forgery's verification up to its target query, with the cipher as queries**: the
refresher check, `chal1` (`chal1PreIC`), the reduction's queries at `x` (`auxSpec`, at the forger's
final log `L`), and the target oracle's step with the void hint; the ghost records `L ++ aux` at a
fresh `x`. -/
noncomputable def verPreIC (L : QueryLog specIC) (m sg : ByteArray) (s : HTS × Gh) :
    OracleComp specIC (HTS × Gh) :=
  if toBA (Spec.PomFRIT.commitRefresher (toL (sB2 lr sg))) != sB1 lr sg then pure s else do
  let oc1 ← chal1PreIC (st0 lr pk sg) (sProof lr sg)
  match oc1 with
  | none => pure s
  | some c1 => do
    let x := tgtIn pk lr sg m c1
    let ax ← toHIC (auxSpec lr L x)
    pure ((tStep addHint x 0 s.1).2, ghStep s.1 s.2 x (L ++ ax))

/-- The earlier forgeries, in order. -/
noncomputable def verPreAll (L : QueryLog specIC) :
    List (ByteArray × ByteArray) → HTS × Gh → OracleComp specIC (HTS × Gh)
  | [], s => pure s
  | (m, sg) :: rest, s => verPreIC lr pk L m sg s >>= verPreAll L rest

/-- The auxiliary output of the derived prover: the `i`-th forgery's `hash_to_target` input and the
ghost log of its first target query (`none` if its `chal1` fails). -/
abbrev AuxP := Option (ByteArray × QueryLog specIC)

/-- **The `i`-th forgery up to its target query, with the cipher as queries**: `chal1`, the
reduction's queries, the target query (void hint). Output: the proof, the statement index (the
target oracle's answer, the binders) and the auxiliary output. -/
noncomputable def verLastIC (L : QueryLog specIC) (ms : ByteArray × ByteArray) (s : HTS × Gh) :
    OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × AuxP)) := do
  let oc1 ← chal1PreIC (st0 lr pk ms.2) (sProof lr ms.2)
  match oc1 with
  | none => pure (sProof lr ms.2, ((0, sB1 lr ms.2, sB2 lr ms.2), none))
  | some c1 => do
    let x := tgtIn pk lr ms.2 ms.1 c1
    let ax ← toHIC (auxSpec lr L x)
    pure (sProof lr ms.2, (((tStep addHint x 0 s.1).1.1, sB1 lr ms.2, sB2 lr ms.2),
      some (x, ((ghStep s.1 s.2 x (L ++ ax)) x).getD [])))

/-- **The derived prover of the `i`-th forgery** for the target stream `Lst` and the Issuer `pre`:
the forger with the void hint (`wrapIC lr hint0`), the earlier forgeries' verifications up to their
target queries, then the `i`-th forgery's. It reaches the hashes and the cipher only through
`specIC`. -/
noncomputable def proverP (pre : TG → SIss) (A : Forger) (Lst : List TG) (i : ℕ) :
    OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × AuxP)) := do
  let r ← (simulateQ (wrapIC lr hint0 pre) (A pk)).run ([], hs0 Lst, fun _ => none)
  let s ← verPreAll lr pk r.2.1 (r.1.take i) (r.2.2.1, r.2.2.2)
  verLastIC lr pk r.2.1 (r.1.getD i (ByteArray.empty, ByteArray.empty)) s

end Prover

/-! ## The derived prover, table by table -/

section Eval

variable (g : Table) (T : CrtTables) (lr : Bool) (E : CTable)
  (hint : QueryLog specIC → ByteArray → TG) (pk : UovPk) (pre : TG → SIss)

lemma eval_chal1PreIC_st0 (sg : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (chal1PreIC (st0 lr pk sg) (sProof lr sg)) =
      c1T g lr E pk sg := by
  rw [evalWithAnswerFn_chal1PreIC]; rfl

lemma eval_toHIC_auxSpec (L : QueryLog specIC) (x : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (toHIC (auxSpec lr L x)) = axT g lr L x := by
  rw [eval_toHIC]; rfl

/-- **The earlier verifications keep the invariant.** -/
theorem eval_verPreAll (L : QueryLog specIC) :
    ∀ (l : List (ByteArray × ByteArray)) (hsH : HTS) (s : HTS × Gh), InvH hint hsH s.1 s.2 →
      InvH hint (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss)
          addHint pre) (verAll T lr E hint tgts1 pk L l)).run hsH)).2
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verPreAll lr pk L l s)).1
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verPreAll lr pk L l s)).2
  | [], hsH, s, h => by simpa [verAll, verPreAll] using h
  | (m, sg) :: rest, hsH, s, h => by
    simp only [verAll, verPreAll, eval_htW_bind, simulateQ_pure, StateT.run_pure,
      evalWithAnswerFn_pure, evalWithAnswerFn_bind]
    refine eval_verPreAll L rest _ _ ?_
    rw [eval_verOne]
    unfold verPreIC
    split_ifs with hr
    · simpa using h
    · simp only [evalWithAnswerFn_bind, eval_chal1PreIC_st0]
      cases c1T g lr E pk sg with
      | none => simpa using h
      | some c1 =>
        simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_toHIC_auxSpec]
        exact (h.step _ _).2

/-- **The derived prover's output, table by table**: the `i`-th forgery's proof and statement index
are those of `proverI` (the game's), and the hint the game stores at its target input is the hint
rule at the ghost log. -/
theorem eval_proverP (A : Forger) (Lst : List TG) (i : ℕ) :
    let p := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (proverP lr pk pre A Lst i)
    let q := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (proverI T lr E hint pk pre A Lst i)
    p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ q.2.2 = (p.2.2).elim 0 (fun xl => hint xl.2 xl.1) := by
  intro p q
  set b := evalWithAnswerFn (QueryImpl.ofFn (join g E))
    ((simulateQ (wrapIC lr hint pre) (A pk)).run ([], hs0 Lst, fun _ => none)) with hb
  set b0 := evalWithAnswerFn (QueryImpl.ofFn (join g E))
    ((simulateQ (wrapIC lr hint0 pre) (A pk)).run ([], hs0 Lst, fun _ => none)) with hb0
  have h0 : InvH hint (hs0 Lst) (hs0 Lst) (fun _ => none) :=
    ⟨SameT.refl _, fun x a e hx => by simp [hs0] at hx⟩
  obtain ⟨e1, e2, e3, e4⟩ := eval_wrapIC_hint g E lr hint pre (A pk) [] _ _ _ h0
  rw [← hb, ← hb0] at e1 e2 e3 e4
  have hq : q = (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss)
      addHint pre) (verPart T lr E hint pk i b.2.1 b.1)).run b.2.2.1)).1 := by
    simp only [q, proverI, evalWithAnswerFn_bind, evalWithAnswerFn_map, ← hb, ← eval_htW_htIC]
  have hp : p = evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verLastIC lr pk b.2.1
      (b.1.getD i (ByteArray.empty, ByteArray.empty))
      (evalWithAnswerFn (QueryImpl.ofFn (join g E))
        (verPreAll lr pk b.2.1 (b.1.take i) (b0.2.2.1, b0.2.2.2)))) := by
    simp only [p, proverP, evalWithAnswerFn_bind, ← hb0, e1, e2]
  have hinv := eval_verPreAll g T lr E hint pk pre b.2.1 (b.1.take i) b.2.2.1 (b0.2.2.1, b0.2.2.2)
    (by rw [← e3]; exact e4)
  rw [hq, hp, eval_verPart]
  set hs' := (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) addHint
    pre) (verAll T lr E hint tgts1 pk b.2.1 (b.1.take i))).run b.2.2.1)).2
  set sP := evalWithAnswerFn (QueryImpl.ofFn (join g E))
    (verPreAll lr pk b.2.1 (b.1.take i) (b0.2.2.1, b0.2.2.2))
  unfold verLastIC
  simp only [evalWithAnswerFn_bind, eval_chal1PreIC_st0]
  cases c1T g lr E pk (b.1.getD i (ByteArray.empty, ByteArray.empty)).2 with
  | none => simp
  | some c1 =>
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_toHIC_auxSpec, Option.elim]
    set x := tgtIn pk lr (b.1.getD i (ByteArray.empty, ByteArray.empty)).2
      (b.1.getD i (ByteArray.empty, ByteArray.empty)).1 c1
    set Lx := b.2.1 ++ axT g lr b.2.1 x
    obtain ⟨f1, f2⟩ := hinv.step x Lx
    refine ⟨trivial, by rw [f1], ?_⟩
    have hg := tStep_get addHint x (hint Lx x) hs'
    obtain ⟨Ly, hLy, he⟩ := f2.2 x _ _ hg
    rw [hLy, Option.getD_some]
    exact he

/-! ### The derived prover's log and ghost -/

/-- The part of the derived prover after the forger. -/
noncomputable def contP (pk : UovPk) (i : ℕ)
    (r : List (ByteArray × ByteArray) × QueryLog specIC × HTS × Gh) :
    OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × AuxP)) :=
  verPreAll lr pk r.2.1 (r.1.take i) (r.2.2.1, r.2.2.2) >>= fun s =>
    verLastIC lr pk r.2.1 (r.1.getD i (ByteArray.empty, ByteArray.empty)) s

lemma proverP_eq (A : Forger) (Lst : List TG) (i : ℕ) :
    proverP lr pk pre A Lst i =
      (simulateQ (wrapIC lr hint0 pre) (A pk)).run ([], hs0 Lst, fun _ => none) >>=
        contP lr pk i := rfl

/-- **The derived prover's joint log** is the forger's log followed by the verifications'. -/
theorem log_proverP (A : Forger) (Lst : List TG) (i : ℕ) :
    tableQueryLog (proverP lr pk pre A Lst i) (join g E) =
      (evalWithAnswerFn (QueryImpl.ofFn (join g E))
        ((simulateQ (wrapIC lr hint0 pre) (A pk)).run ([], hs0 Lst, fun _ => none))).2.1 ++
      tableQueryLog (contP lr pk i (evalWithAnswerFn (QueryImpl.ofFn (join g E))
        ((simulateQ (wrapIC lr hint0 pre) (A pk)).run ([], hs0 Lst, fun _ => none)))) (join g E) := by
  rw [proverP_eq, tableQueryLog_bind, log_forger, List.nil_append]

/-- **The ghost invariant**: every answered input has a ghost log, and every ghost log is a log
`Pfx` followed by the reduction's queries at that input, a prefix of the current log. -/
def GhostI (g : Table) (lr : Bool) (cur : QueryLog specIC) (hs : HTS) (gh : Gh) : Prop :=
  (∀ y, hs.1 y ≠ none → ∃ Ly, gh y = some Ly) ∧
    ∀ y Ly, gh y = some Ly → ∃ Pfx, Ly = Pfx ++ axT g lr Pfx y ∧ Ly <+: cur

lemma tStep_ne_none {hs : HTS} {x y : ByteArray} (h : (tStep addHint x 0 hs).2.1 y ≠ none) :
    hs.1 y ≠ none ∨ (y = x ∧ hs.1 x = none) := by
  by_cases hx : hs.1 x = none
  · by_cases hyx : y = x
    · exact Or.inr ⟨hyx, hx⟩
    · left
      obtain ⟨t, l, tg, n⟩ := hs
      simp only at hx
      cases l <;> simpa [tStep, hx, Function.update_of_ne hyx] using h
  · left
    obtain ⟨t, l, tg, n⟩ := hs
    cases hx' : t x with
    | none => exact absurd hx' hx
    | some a => simpa [tStep, hx'] using h

/-- **The forger keeps the ghost invariant.** -/
theorem ghost_wrapIC {α : Type} (oa : OracleComp specU α) :
    ∀ (L : QueryLog specIC) (hs : HTS) (gh : Gh), GhostI g lr L hs gh →
      GhostI g lr (evalWithAnswerFn (QueryImpl.ofFn (join g E))
          ((simulateQ (wrapIC lr hint0 pre) oa).run (L, hs, gh))).2.1
        (evalWithAnswerFn (QueryImpl.ofFn (join g E))
          ((simulateQ (wrapIC lr hint0 pre) oa).run (L, hs, gh))).2.2.1
        (evalWithAnswerFn (QueryImpl.ofFn (join g E))
          ((simulateQ (wrapIC lr hint0 pre) oa).run (L, hs, gh))).2.2.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro L hs gh h; simpa using h
  | query_bind q k ih =>
    intro L hs gh h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with d | (x | t)
    · simp only [wrapIC, StateT.run_mk, evalWithAnswerFn_bind]
      refine ih _ _ _ _ ⟨h.1, fun y Ly hy => ?_⟩
      obtain ⟨Pfx, h1, h2⟩ := h.2 y Ly hy
      exact ⟨Pfx, h1, h2.trans (List.prefix_append _ _)⟩
    · simp only [wrapIC, StateT.run_mk, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      rw [eval_toHIC_auxSpec]
      refine ih _ _ _ _ ⟨fun y hy => ?_, fun y Ly hy => ?_⟩
      · rcases tStep_ne_none hy with hy' | ⟨rfl, hx⟩
        · obtain ⟨Ly, hLy⟩ := h.1 y hy'
          by_cases hyx : hs.1 x = none
          · by_cases hxy : y = x
            · subst hxy; exact absurd hyx hy'
            · exact ⟨Ly, by rw [ite_eq_left hyx, Function.update_of_ne hxy]; exact hLy⟩
          · exact ⟨Ly, by rw [ite_eq_right hyx]; exact hLy⟩
        · exact ⟨_, by rw [ite_eq_left hx, Function.update_self]⟩
      · by_cases hx : hs.1 x = none
        · rw [ite_eq_left hx] at hy
          by_cases hyx : y = x
          · subst hyx
            rw [Function.update_self] at hy
            cases hy
            exact ⟨L, rfl, List.prefix_refl _⟩
          · rw [Function.update_of_ne hyx] at hy
            obtain ⟨Pfx, h1, h2⟩ := h.2 y Ly hy
            exact ⟨Pfx, h1, h2.trans (List.prefix_append _ _)⟩
        · rw [ite_eq_right hx] at hy
          obtain ⟨Pfx, h1, h2⟩ := h.2 y Ly hy
          exact ⟨Pfx, h1, h2.trans (List.prefix_append _ _)⟩
    · simp only [wrapIC, StateT.run_mk, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      exact ih _ _ _ _ h

/-- The ghost invariant after the forger: ghost logs are prefixes of the forger's log `L`, or `L`
followed by the reduction's queries. -/
def GhostV (g : Table) (lr : Bool) (L : QueryLog specIC) (hs : HTS) (gh : Gh) : Prop :=
  (∀ y, hs.1 y ≠ none → ∃ Ly, gh y = some Ly) ∧
    ∀ y Ly, gh y = some Ly → ∃ Pfx, Ly = Pfx ++ axT g lr Pfx y ∧ (Ly <+: L ∨ Pfx = L)

lemma GhostV.step {L : QueryLog specIC} {hs : HTS} {gh : Gh} (h : GhostV g lr L hs gh)
    (x : ByteArray) :
    GhostV g lr L (tStep addHint x 0 hs).2 (ghStep hs gh x (L ++ axT g lr L x)) := by
  refine ⟨fun y hy => ?_, fun y Ly hy => ?_⟩
  · rcases tStep_ne_none hy with hy' | ⟨rfl, hx⟩
    · obtain ⟨Ly, hLy⟩ := h.1 y hy'
      unfold ghStep
      by_cases hyx : hs.1 x = none
      · by_cases hxy : y = x
        · subst hxy; exact absurd hyx hy'
        · exact ⟨Ly, by rw [ite_eq_left hyx, Function.update_of_ne hxy]; exact hLy⟩
      · exact ⟨Ly, by rw [ite_eq_right hyx]; exact hLy⟩
    · exact ⟨_, by rw [ghStep, ite_eq_left hx, Function.update_self]⟩
  · unfold ghStep at hy
    by_cases hx : hs.1 x = none
    · rw [ite_eq_left hx] at hy
      by_cases hyx : y = x
      · subst hyx
        rw [Function.update_self] at hy
        cases hy
        exact ⟨L, rfl, Or.inr rfl⟩
      · rw [Function.update_of_ne hyx] at hy
        exact h.2 y Ly hy
    · rw [ite_eq_right hx] at hy
      exact h.2 y Ly hy

theorem ghost_verPreAll (L : QueryLog specIC) :
    ∀ (l : List (ByteArray × ByteArray)) (s : HTS × Gh), GhostV g lr L s.1 s.2 →
      GhostV g lr L (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verPreAll lr pk L l s)).1
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verPreAll lr pk L l s)).2
  | [], s, h => by simpa [verPreAll] using h
  | (m, sg) :: rest, s, h => by
    simp only [verPreAll, evalWithAnswerFn_bind]
    refine ghost_verPreAll L rest _ ?_
    unfold verPreIC
    split_ifs
    · simpa using h
    · simp only [evalWithAnswerFn_bind, eval_chal1PreIC_st0]
      cases c1T g lr E pk sg with
      | none => simpa using h
      | some c1 =>
        simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_toHIC_auxSpec]
        exact h.step g lr _

/-- **The derived prover's auxiliary output**: the `i`-th forgery's `hash_to_target` input at its
`chal1`, and a ghost log that is a log `Pfx` followed by the reduction's queries at that input,
either a prefix of the forger's log `L` or with `Pfx = L`. -/
theorem aux_proverP (A : Forger) (Lst : List TG) (i : ℕ) :
    let b0 := evalWithAnswerFn (QueryImpl.ofFn (join g E))
      ((simulateQ (wrapIC lr hint0 pre) (A pk)).run ([], hs0 Lst, fun _ => none))
    let ms := b0.1.getD i (ByteArray.empty, ByteArray.empty)
    let p := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (proverP lr pk pre A Lst i)
    (p.2.2 = none → c1T g lr E pk ms.2 = none) ∧
    ∀ x Lx, p.2.2 = some (x, Lx) → ∃ c1 Pfx, c1T g lr E pk ms.2 = some c1 ∧
      x = tgtIn pk lr ms.2 ms.1 c1 ∧ Lx = Pfx ++ axT g lr Pfx x ∧ (Lx <+: b0.2.1 ∨ Pfx = b0.2.1) := by
  intro b0 ms p
  have h0 : GhostI g lr [] (hs0 Lst) (fun _ => none) :=
    ⟨fun y hy => by simp [hs0] at hy, fun y Ly hy => by simp at hy⟩
  have hI := ghost_wrapIC g lr E pre (A pk) [] _ _ h0
  have hV0 : GhostV g lr b0.2.1 b0.2.2.1 b0.2.2.2 :=
    ⟨hI.1, fun y Ly hy => by
      obtain ⟨Pfx, h1, h2⟩ := hI.2 y Ly hy
      exact ⟨Pfx, h1, Or.inl h2⟩⟩
  have hV := ghost_verPreAll g lr E pk b0.2.1 (b0.1.take i) (b0.2.2.1, b0.2.2.2) hV0
  have hp : p = evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verLastIC lr pk b0.2.1 ms
      (evalWithAnswerFn (QueryImpl.ofFn (join g E))
        (verPreAll lr pk b0.2.1 (b0.1.take i) (b0.2.2.1, b0.2.2.2)))) := by
    simp only [p, proverP, evalWithAnswerFn_bind]
    rfl
  set sP := evalWithAnswerFn (QueryImpl.ofFn (join g E))
    (verPreAll lr pk b0.2.1 (b0.1.take i) (b0.2.2.1, b0.2.2.2))
  rw [hp]
  unfold verLastIC
  simp only [evalWithAnswerFn_bind, eval_chal1PreIC_st0]
  cases hc : c1T g lr E pk ms.2 with
  | none => simp
  | some c1 =>
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_toHIC_auxSpec,
      reduceCtorEq, false_implies, Option.some.injEq, Prod.mk.injEq, true_and]
    rintro x Lx ⟨rfl, rfl⟩
    have hst := hV.step g lr (tgtIn pk lr ms.2 ms.1 c1)
    obtain ⟨Ly, hLy⟩ := hst.1 _ (by rw [tStep_get]; simp)
    obtain ⟨Pfx, h1, h2⟩ := hst.2 _ Ly hLy
    rw [hLy, Option.getD_some]
    exact ⟨c1, Pfx, rfl, rfl, h1, h1 ▸ h2⟩

end Eval

end VoleMole.ROM.OneMore.Pomfrit
