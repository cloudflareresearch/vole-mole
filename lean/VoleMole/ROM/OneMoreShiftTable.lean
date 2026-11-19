import VoleMole.ROM.OneMoreLemmaPPrefix

/-!
# PomFRIT's one-more game with any hint type, table by table (for Theorem U2)

`lean/docs/security/pomfrit.md` §6.4 (gap G8). `ROM/OneMoreLemmaP.lean` and
`ROM/OneMoreLemmaPIC.lean` relate the game to the derived prover `proverP … i` for U1's hints only
(one target per query, `addHint`). The derived prover itself reads neither the hint rule nor the
target rule. This file relates the game with **any** hint type `Hn`, programming `φ`, hint rule and
target rule (U2: lists of shifts, `noHint`, `tgts2`) to the same derived prover, table by table.

* **The game's state and the void-hint state** (`SameG`, `InvG`): the same answers, stream and
  Issuer count, and the hint the game stores at each answered input is the hint rule at the ghost
  log of that input (`InvG.step`; for U1's hints this is `InvH`).
* **The forger** (`eval_forgerG`): the game's wrapped forger with the target oracle on a state is,
  table by table, the forger with the cipher as queries and a void hint (`wrapIC lr hintVoid`): the
  same output and log, and states related by `InvG`.
* **The verifications** (`eval_verOneG`, `eval_verAll_splitG`, `eval_verPreAllG`,
  `eval_htW_persistG`): as `eval_verOne` etc. for any `φ`.
* **An accepted forgery, table by table** (`ver_tableG`): if forgery `i` of the game is accepted
  with claim `(x, σ)`, then the forger output `ℓ + 1` forgeries, forgery `i` passes the refresher
  check, the derived prover `proverP … i` outputs `x` with a ghost log `Lx`, the game's table holds
  at `x` the derived prover's answer and the hint rule at `Lx`, the verifier accepts at the
  derived prover's statement, and `σ` is the first extracted candidate (from the forger's log) that
  is a preimage of one of the targets of that answer and hint.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.EndToEnd.SpecRel VoleMole.ZK.Sim

/-! ## States with any hint type -/

section State

variable {Hn : Type}

/-- The reduced state of the target oracle with hints `Hn`. -/
abbrev HTSG (Hn : Type) := (ByteArray → Option (TG × Hn)) × ChW ByteArray Hn TG

/-- The initial reduced state: an empty table, the stream `Lst`, no programmed target, no Issuer
query. -/
def hs0G (Lst : List TG) : HTSG Hn := (fun _ => none, (Lst, fun _ => none, 0))

/-- **A game state and a void-hint state with the same answers, stream and Issuer count.** -/
def SameG (s : HTSG Hn) (s' : HTS) : Prop :=
  (∀ x, (s.1 x).map Prod.fst = (s'.1 x).map Prod.fst) ∧ s.2.1 = s'.2.1 ∧ s.2.2.2 = s'.2.2.2

lemma SameG.none_iff {s : HTSG Hn} {s' : HTS} (h : SameG s s') (x : ByteArray) :
    s.1 x = none ↔ s'.1 x = none := by
  have := h.1 x
  constructor
  · intro hx; rw [hx] at this; exact Option.map_eq_none_iff.1 this.symm
  · intro hx; rw [hx] at this; exact Option.map_eq_none_iff.1 this

/-- **The target oracle's answers do not depend on the hints or the programming.** -/
lemma tStep_sameG (φ : Hn → TG ≃ TG) {s : HTSG Hn} {s' : HTS} (h : SameG s s') (x : ByteArray)
    (e : Hn) (e' : TG) :
    (tStep φ x e s).1.1 = (tStep addHint x e' s').1.1 ∧
      SameG (tStep φ x e s).2 (tStep addHint x e' s').2 := by
  obtain ⟨t, l, tg, n⟩ := s
  obtain ⟨t', l', tg', n'⟩ := s'
  obtain ⟨h1, h2, h3⟩ := h
  simp only at h1 h2 h3
  subst h2 h3
  have hx := h1 x
  unfold tStep
  simp only
  cases hs : t x with
  | some a =>
    cases hs' : t' x with
    | some a' =>
      rw [hs, hs'] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      exact ⟨hx, h1, rfl, rfl⟩
    | none => rw [hs, hs'] at hx; cases hx
  | none =>
    cases hs' : t' x with
    | some a' => rw [hs, hs'] at hx; cases hx
    | none =>
      cases l with
      | nil => exact ⟨rfl, fun y => by by_cases hy : y = x <;> simp [hy, h1 y], rfl, rfl⟩
      | cons u r => exact ⟨rfl, fun y => by by_cases hy : y = x <;> simp [hy, h1 y], rfl, rfl⟩

/-- **The invariant between the game's state and the void-hint state** (`InvH` for any hint
type): the same answers, and the hint the game stores at each answered input is the hint rule at
the ghost log of that input. -/
def InvG (hint : QueryLog specIC → ByteArray → Hn) (hsH : HTSG Hn) (hsP : HTS) (gh : Gh) : Prop :=
  SameG hsH hsP ∧ ∀ x a e, hsH.1 x = some (a, e) → ∃ Lx, gh x = some Lx ∧ e = hint Lx x

/-- **A target query keeps the invariant.** -/
lemma InvG.step (φ : Hn → TG ≃ TG) {hint : QueryLog specIC → ByteArray → Hn} {hsH : HTSG Hn}
    {hsP : HTS} {gh : Gh} (h : InvG hint hsH hsP gh) (x : ByteArray) (Lx : QueryLog specIC) :
    (tStep φ x (hint Lx x) hsH).1.1 = (tStep addHint x 0 hsP).1.1 ∧
      InvG hint (tStep φ x (hint Lx x) hsH).2 (tStep addHint x 0 hsP).2
        (ghStep hsP gh x Lx) := by
  obtain ⟨e1, e2⟩ := tStep_sameG φ h.1 x (hint Lx x) 0
  refine ⟨e1, e2, fun y a e hy => ?_⟩
  obtain ⟨tH, lH, tgH, nH⟩ := hsH
  cases hx : tH x with
  | some v =>
    have hP : hsP.1 x ≠ none := fun hn => by
      have := (h.1.none_iff x).2 hn; simp only at this; rw [hx] at this; cases this
    have hst : tStep φ x (hint Lx x) (tH, lH, tgH, nH) = (v, (tH, lH, tgH, nH)) := by
      simp [tStep, hx]
    rw [hst] at hy
    simp only [ghStep, hP, ite_false]
    exact h.2 y a e hy
  | none =>
    have hP : hsP.1 x = none := (h.1.none_iff x).1 (by simpa using hx)
    simp only [ghStep, hP, ite_true]
    by_cases hyx : y = x
    · subst hyx
      have hg := tStep_get φ y (hint Lx y) (tH, lH, tgH, nH)
      rw [hy] at hg
      have hv : (tStep φ y (hint Lx y) (tH, lH, tgH, nH)).1.2 = hint Lx y := by
        cases lH <;> simp [tStep, hx]
      refine ⟨Lx, by simp, ?_⟩
      rw [← hv, ← Option.some.inj hg]
    · have hk : tH y = some (a, e) := by
        have : (tStep φ x (hint Lx x) (tH, lH, tgH, nH)).2.1 y = tH y := by
          cases lH <;> simp [tStep, hx, Function.update_of_ne hyx]
        rw [← this]; exact hy
      obtain ⟨Ly, hLy, he⟩ := h.2 y a e hk
      exact ⟨Ly, by rw [Function.update_of_ne hyx]; exact hLy, he⟩

lemma InvG.init (hint : QueryLog specIC → ByteArray → Hn) (Lst : List TG) :
    InvG hint (hs0G Lst) (hs0 Lst) (fun _ => none) :=
  ⟨⟨fun _ => rfl, rfl, rfl⟩, fun x a e hx => by simp [hs0G] at hx⟩

end State

/-! ## The game's steps against a hash table, any programming -/

section Eval

variable {Hn : Type} (g : Table) (E : CTable) (lr : Bool) (φ : Hn → TG ≃ TG)
  (hint : QueryLog specIC → ByteArray → Hn) (pre : TG → SIss)

lemma eval_htW_bindG {α β : Type} (m : OracleComp (specC Hn) α) (f : α → OracleComp (specC Hn) β)
    (hs : HTSG Hn) :
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (m >>= f)).run hs) =
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (f (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
        m).run hs)).1)).run
      (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
        m).run hs)).2) := by
  simp only [simulateQ_bind, StateT.run_bind, evalWithAnswerFn_bind]

lemma eval_htW_tqG (x : ByteArray) (h : Hn) (hs : HTSG Hn) :
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (liftM ((specC Hn).query (.inr (.inl (x, h)))) : OracleComp (specC Hn) (TG × Hn))).run hs) =
      tStep φ x h hs := by
  erw [simulateQ_spec_query]
  rfl

lemma eval_htW_tgtG {β : Type} (x : ByteArray) (h : Hn) (f : TG × Hn → β) (hs : HTSG Hn) :
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (f <$> (liftM ((specC Hn).query (.inr (.inl (x, h)))) : OracleComp (specC Hn) (TG × Hn)))).run
        hs) = (f (tStep φ x h hs).1, (tStep φ x h hs).2) := by
  rw [simulateQ_map]
  erw [simulateQ_spec_query]
  rfl

lemma eval_htW_toCG {α : Type} (oa : OracleComp spec α) (hs : HTSG Hn) :
    evalWithAnswerFn (QueryImpl.ofFn g)
      ((simulateQ (htW (AR := Ans) (S := SIss) φ pre) (toC (Hn := Hn) oa)).run hs) =
      (evalWithAnswerFn (QueryImpl.ofFn g) oa, hs) := eval_htW_toC g φ pre oa hs

/-- **The game's forger and the void-hint forger, table by table**: the same output and log, and
states related by `InvG`. -/
theorem eval_forgerG {α : Type} (oa : OracleComp specU α) :
    ∀ (L : QueryLog specIC) (hsH : HTSG Hn) (hsP : HTS) (gh : Gh), InvG hint hsH hsP gh →
      let a := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
        ((simulateQ (wrapImpl lr E hint) oa).run L)).run hsH)
      let b := evalWithAnswerFn (QueryImpl.ofFn (join g E))
        ((simulateQ (wrapIC lr hintVoid pre) oa).run (L, hsP, gh))
      a.1.1 = b.1 ∧ a.1.2 = b.2.1 ∧ InvG hint a.2 b.2.2.1 b.2.2.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro L hsH hsP gh h; simpa using h
  | query_bind q k ih =>
    intro L hsH hsP gh h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with (d | x) | (x | t)
    · simp only [wrapImpl, wrapIC, StateT.run_mk, evalWithAnswerFn_bind]
      exact ih (g d) _ hsH hsP gh h
    · simp only [wrapImpl, wrapIC, StateT.run_mk, simulateQ_pure, StateT.run_pure,
        evalWithAnswerFn_bind, pure_bind]
      exact ih (E x) _ hsH hsP gh h
    · simp only [wrapImpl, wrapIC, auxC, StateT.run_mk, simulateQ_bind, StateT.run_bind,
        evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_htW_toCG, eval_toHIC, eval_htW_tgtG]
      set ax := evalWithAnswerFn (QueryImpl.ofFn g) (auxSpec lr L x)
      obtain ⟨e1, e2⟩ := h.step φ x (L ++ ax)
      have := ih ((tStep φ x (hint (L ++ ax) x) hsH).1.1) (L ++ ax) _ _ _ e2
      simp only [hintVoid]
      rw [← e1]
      exact this
    · simp only [wrapImpl, wrapIC, StateT.run_mk, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
      erw [simulateQ_map, simulateQ_spec_query]
      exact ih _ _ _ _ _ ⟨⟨h.1.1, h.1.2.1, congrArg (· + 1) h.1.2.2⟩, h.2⟩

end Eval

/-! ## The verifications, table by table, any programming -/

section TableVer

variable {Hn : Type} (g : Table) (T : CrtTables) (lr : Bool) (E : CTable) (φ : Hn → TG ≃ TG)
  (hint : QueryLog specIC → ByteArray → Hn) (tgts : TG × Hn → List TG) (pk : UovPk)
  (pre : TG → SIss)

/-- **One verification, table by table** (`eval_verOne` for any programming and target rule). -/
theorem eval_verOneG (L : QueryLog specIC) (m sg : ByteArray) (hs : HTSG Hn) :
    evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (verOne T lr E hint tgts pk L m sg)).run hs) =
    if toBA (Spec.PomFRIT.commitRefresher (toL (sB2 lr sg))) != sB1 lr sg then
      (((ByteArray.empty, none), false), hs)
    else match c1T g lr E pk sg with
      | none => (((ByteArray.empty, none), false), hs)
      | some c1 =>
        let x := tgtIn pk lr sg m c1
        let ah := tStep φ x (hint (L ++ axT g lr L x) x) hs
        let st := pomfritRedeemT pk (fun _ => encT ah.1.1) (sB1 lr sg) (sB2 lr sg) lr
        let ex := evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E ((sProof lr sg, ()), L))
        let t := @verify (VoleMole.ZK.Sim.icPrg E.cipher) (Hashes.ofTable g) T st (sProof lr sg)
        (((x, pick pk (tgts ah.1) (candidates E st (ex.1, ex.2, t))), t.accept), ah.2) := by
  unfold verOne c1T sProof sB1 sB2 axT
  dsimp only
  split_ifs with hr
  · simp
  · rw [eval_htW_bindG, eval_htW_toCG]
    cases hc : evalWithAnswerFn (QueryImpl.ofFn g) (@chal1Pre (VoleMole.ZK.Sim.icPrg E.cipher)
      (pomfritRedeemT pk (fun _ => ByteArray.empty)
        (sg.extract (pomfritParams lr).proofBytes ((pomfritParams lr).proofBytes + 32))
        (sg.extract ((pomfritParams lr).proofBytes + 32) ((pomfritParams lr).proofBytes + 64)) lr)
      (sg.extract 0 (pomfritParams lr).proofBytes)) with
    | none => simp
    | some c1 =>
      simp only [auxC, eval_htW_bindG, eval_htW_toCG, tQ, verTail, eval_htW_tqG, simulateQ_pure,
        StateT.run_pure, evalWithAnswerFn_pure, @evalWithAnswerFn_verifyQ (VoleMole.ZK.Sim.icPrg E.cipher)]

lemma eval_verAll_lengthG (L : QueryLog specIC) :
    ∀ (l : List (ByteArray × ByteArray)) (s : HTSG Hn),
      (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
        (verAll T lr E hint tgts pk L l)).run s)).1.length = l.length
  | [], s => by simp [verAll]
  | (m, sg) :: l, s => by
    simp only [verAll, eval_htW_bindG, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure,
      List.length_cons, eval_verAll_lengthG L l]

/-- `verAll` at a table, split at the `i`-th forgery. -/
theorem eval_verAll_splitG (L : QueryLog specIC) (outs : List (ByteArray × ByteArray))
    (hs : HTSG Hn) (i : ℕ) (hi : i < outs.length) :
    let hs' := (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss)
      φ pre) (verAll T lr E hint tgts pk L (outs.take i))).run hs)).2
    (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (verAll T lr E hint tgts pk L outs)).run hs)).1[i]? =
    some (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (verOne T lr E hint tgts pk L (outs[i]).1 (outs[i]).2)).run hs')).1 := by
  intro hs'
  have hsplit : outs = outs.take i ++ ((outs[i]).1, (outs[i]).2) :: outs.drop (i + 1) := by
    simp
  conv_lhs => rw [hsplit, verAll_append]
  simp only [eval_htW_bindG, verAll, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure]
  have hlen := eval_verAll_lengthG g T lr E φ hint tgts pk pre L
  rw [List.getElem?_append_right (by rw [hlen]; simp)]
  simp [hlen, Nat.min_eq_left hi.le, hs']

lemma eval_verAll_append_sndG (L : QueryLog specIC) (l₁ l₂ : List (ByteArray × ByteArray))
    (hs : HTSG Hn) :
    (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (verAll T lr E hint tgts pk L (l₁ ++ l₂))).run hs)).2 =
    (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (verAll T lr E hint tgts pk L l₂)).run
      (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
        (verAll T lr E hint tgts pk L l₁)).run hs)).2)).2 := by
  rw [verAll_append]
  simp only [eval_htW_bindG, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure]

lemma eval_verAll_single_sndG (L : QueryLog specIC) (m sg : ByteArray) (hs : HTSG Hn) :
    (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (verAll T lr E hint tgts pk L [(m, sg)])).run hs)).2 =
    (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (verOne T lr E hint tgts pk L m sg)).run hs)).2 := by
  simp only [verAll, eval_htW_bindG, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure]

/-- **Target-oracle entries persist** (any programming). -/
theorem eval_htW_persistG {α : Type} (m : OracleComp (specC Hn) α) :
    ∀ (hs : HTSG Hn) {y : ByteArray} {v : TG × Hn}, hs.1 y = some v →
      (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
        m).run hs)).2.1 y = some v := by
  induction m using OracleComp.inductionOn with
  | pure a => intro hs y v h; simpa using h
  | query_bind q k ih =>
    intro hs y v h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evalWithAnswerFn_bind]
    rcases q with d | ⟨x, hh⟩ | t
    · exact ih _ _ h
    · exact ih _ _ (tStep_keep φ x y hh hs h)
    · exact ih _ _ h

/-- **The earlier verifications keep the invariant** (`eval_verPreAll` for any programming). -/
theorem eval_verPreAllG (L : QueryLog specIC) :
    ∀ (l : List (ByteArray × ByteArray)) (hsH : HTSG Hn) (s : HTS × Gh), InvG hint hsH s.1 s.2 →
      InvG hint (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss)
          φ pre) (verAll T lr E hint tgts pk L l)).run hsH)).2
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verPreAll lr pk L l s)).1
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verPreAll lr pk L l s)).2
  | [], hsH, s, h => by simpa [verAll, verPreAll] using h
  | (m, sg) :: rest, hsH, s, h => by
    simp only [verAll, verPreAll, eval_htW_bindG, simulateQ_pure, StateT.run_pure,
      evalWithAnswerFn_pure, evalWithAnswerFn_bind]
    refine eval_verPreAllG L rest _ _ ?_
    rw [eval_verOneG]
    unfold verPreIC
    split_ifs with hr
    · simpa using h
    · simp only [evalWithAnswerFn_bind, eval_chal1PreIC_st0]
      cases c1T g lr E pk sg with
      | none => simpa using h
      | some c1 =>
        simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_toHIC_auxSpec]
        exact (h.step φ _ _).2

end TableVer

/-! ## An accepted forgery, table by table -/

section Accepted

variable {Hn : Type} (g : Table) (T : CrtTables) (lr : Bool) (E : CTable) (φ : Hn → TG ≃ TG)
  (hint : QueryLog specIC → ByteArray → Hn) (tgts : TG × Hn → List TG) (pk : UovPk)
  (pre : TG → SIss) (A : Forger) (Lst : List TG) (ℓ : ℕ)

/-- The game's run at a hash table, from the initial reduced state. -/
noncomputable abbrev runG : (List (ByteArray × SIss) × Bool) × HTSG Hn :=
  evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
    (Acomp T lr E hint tgts pk ℓ A)).run (hs0G Lst))

set_option maxHeartbeats 1600000 in
/-- **An accepted forgery, table by table, any hint type**: if the game's run against `g` is
accepted and claims `(x, σ)` for forgery `i`, then the forger (with the void hint) output `ℓ + 1`
forgeries, forgery `i` passes the refresher check, the derived prover `proverP … i` outputs `x` and
a ghost log `Lx`, the game's table holds at `x` the derived prover's answer and the hint rule at
`Lx`, the verifier accepts the forgery's proof at the derived prover's statement, and `σ` is the
first candidate extracted from the forger's log that is a preimage of one of the targets of that
answer and hint. -/
theorem ver_tableG (i : ℕ) {x : ByteArray} {σ : SIss}
    (hacc : (runG g T lr E φ hint tgts pk pre A Lst ℓ).1.2 = true)
    (hcl : (runG g T lr E φ hint tgts pk pre A Lst ℓ).1.1[i]? = some (x, σ)) :
    let b0 := forgerOut g lr E pk pre A Lst
    let ms := b0.1.getD i (ByteArray.empty, ByteArray.empty)
    let p := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (proverP lr pk pre A Lst i)
    let st := stG lr pk p.2.1
    let t := @verify (icPrg E.cipher) (Hashes.ofTable g) T st (sProof lr ms.2)
    let ex := evalWithAnswerFn (QueryImpl.ofFn g) (extractIC st E ((sProof lr ms.2, ()), b0.2.1))
    i < b0.1.length ∧ b0.1.length = ℓ + 1 ∧ RefreshOk lr ms.2 ∧ p.1 = sProof lr ms.2 ∧
    p.2.1.2 = (sB1 lr ms.2, sB2 lr ms.2) ∧
    ∃ Lx, p.2.2 = some (x, Lx) ∧
      (runG g T lr E φ hint tgts pk pre A Lst ℓ).2.1 x = some (p.2.1.1, hint Lx x) ∧
      t.accept = true ∧ σ = pick pk (tgts (p.2.1.1, hint Lx x)) (candidates E st (ex.1, ex.2, t)) := by
  intro b0 ms p st t ex
  have hz : runG g T lr E φ hint tgts pk pre A Lst ℓ = evalWithAnswerFn (QueryImpl.ofFn g)
      ((simulateQ (htW (AR := Ans) (S := SIss) φ pre) (Acomp T lr E hint tgts pk ℓ A)).run
        (hs0G Lst)) := rfl
  generalize runG g T lr E φ hint tgts pk pre A Lst ℓ = z at hz hacc hcl ⊢
  obtain ⟨f1, f2, f3⟩ := eval_forgerG g E lr φ hint pre (A pk) [] (hs0G Lst) (hs0 Lst)
    (fun _ => none) (InvG.init hint Lst)
  set bH := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
    ((simulateQ (wrapImpl lr E hint) (A pk)).run [])).run (hs0G Lst)) with hbH
  have f1' : bH.1.1 = b0.1 := f1
  have f2' : bH.1.2 = b0.2.1 := f2
  have f3' : InvG hint bH.2 b0.2.2.1 b0.2.2.2 := f3
  clear f1 f2 f3
  unfold Acomp at hz
  rw [eval_htW_bindG, ← hbH] at hz
  try dsimp only at hz
  rw [f1', f2'] at hz
  split_ifs at hz with hlen
  swap
  · rw [hz] at hacc; simp at hacc
  rw [eval_htW_bindG] at hz
  simp only [simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure] at hz
  set outs := b0.1 with houts
  set L := b0.2.1 with hL
  set vsS := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss)
    φ pre) (verAll T lr E hint tgts pk L outs)).run bH.2) with hvsS
  rw [hz] at hacc hcl
  simp only [decide_eq_true_eq] at hacc
  simp only at hcl
  rw [List.getElem?_map] at hcl
  obtain ⟨v, hv, hvx⟩ : ∃ v, vsS.1[i]? = some v ∧ v.1 = (x, σ) := by
    cases hvi : vsS.1[i]? with
    | none => rw [hvi] at hcl; cases hcl
    | some v => rw [hvi] at hcl; exact ⟨v, rfl, Option.some.inj hcl⟩
  have hi : i < outs.length := by
    have := (List.getElem?_eq_some_iff.1 hv).1
    rwa [hvsS, eval_verAll_lengthG] at this
  have hvacc : v.2 = true := hacc.1 v (List.mem_of_getElem? hv)
  have hsplit := eval_verAll_splitG g T lr E φ hint tgts pk pre L outs bH.2 i hi
  rw [← hvsS, hv] at hsplit
  set hsi := (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss)
    φ pre) (verAll T lr E hint tgts pk L (outs.take i))).run bH.2)).2 with hhsi
  simp only [Option.some.injEq] at hsplit
  have hfin : vsS.2 = (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans)
      (S := SIss) φ pre) (verAll T lr E hint tgts pk L (outs.drop (i + 1)))).run
      (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
        (verOne T lr E hint tgts pk L (outs[i]).1 (outs[i]).2)).run hsi)).2)).2 := by
    have hsp : outs = (outs.take i ++ [((outs[i]).1, (outs[i]).2)]) ++ outs.drop (i + 1) := by simp
    rw [hvsS]
    conv_lhs => rw [hsp]
    rw [eval_verAll_append_sndG, eval_verAll_append_sndG, eval_verAll_single_sndG]
  have hgetD : ms = outs[i] := by
    show outs.getD i (ByteArray.empty, ByteArray.empty) = outs[i]
    rw [List.getD_eq_getElem _ _ hi]
  -- the derived prover's run
  have hinv := eval_verPreAllG g T lr E φ hint tgts pk pre L (outs.take i) bH.2
    (b0.2.2.1, b0.2.2.2) f3'
  rw [← hhsi] at hinv
  set sP := evalWithAnswerFn (QueryImpl.ofFn (join g E))
    (verPreAll lr pk L (outs.take i) (b0.2.2.1, b0.2.2.2)) with hsP
  have hp : p = evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verLastIC lr pk L ms sP) := by
    simp only [p, proverP, evalWithAnswerFn_bind]
    rfl
  obtain ⟨hp1, hp2⟩ := out_proverP g lr E pk pre A Lst i
  rw [eval_verOneG] at hsplit hfin
  rw [← hgetD] at hsplit hfin
  split_ifs at hsplit hfin with hrf
  · rw [hsplit] at hvacc; cases hvacc
  have hrfo : RefreshOk lr ms.2 := by unfold RefreshOk; simpa using hrf
  cases hc : c1T g lr E pk ms.2 with
  | none => rw [hc] at hsplit; rw [hsplit] at hvacc; cases hvacc
  | some c1 =>
    rw [hc] at hsplit hfin
    dsimp only at hsplit hfin
    set x0 := tgtIn pk lr ms.2 ms.1 c1 with hx0
    set Lx0 := L ++ axT g lr L x0 with hLx0
    set ah := tStep φ x0 (hint Lx0 x0) hsi with hah
    obtain ⟨g1, g2⟩ := hinv.step φ x0 Lx0
    have hg := tStep_get φ x0 (hint Lx0 x0) hsi
    obtain ⟨Ly, hLy, he⟩ := g2.2 x0 _ _ hg
    have hpv : p = (sProof lr ms.2, (((tStep addHint x0 0 sP.1).1.1, sB1 lr ms.2, sB2 lr ms.2),
        some (x0, Ly))) := by
      rw [hp]
      unfold verLastIC
      simp only [evalWithAnswerFn_bind, eval_chal1PreIC_st0, hc, evalWithAnswerFn_pure,
        eval_toHIC_auxSpec]
      rw [← hx0, ← hLx0, hLy, Option.getD_some]
    have hpa : p.2.1 = (ah.1.1, sB1 lr ms.2, sB2 lr ms.2) := by rw [hpv, ← g1]
    have hst : st = pomfritRedeemT pk (fun _ => encT ah.1.1) (sB1 lr ms.2) (sB2 lr ms.2) lr := by
      show stG lr pk p.2.1 = _
      rw [hpa]; rfl
    have hah1 : ah.1 = (p.2.1.1, hint Ly x0) := by
      rw [hpa]
      exact Prod.ext rfl he
    have ht' : t = @verify (icPrg E.cipher) (Hashes.ofTable g) T
        (pomfritRedeemT pk (fun _ => encT ah.1.1) (sB1 lr ms.2) (sB2 lr ms.2) lr) (sProof lr ms.2) := by
      simp only [t, hst]
    have hex' : ex = evalWithAnswerFn (QueryImpl.ofFn g) (extractIC
        (pomfritRedeemT pk (fun _ => encT ah.1.1) (sB1 lr ms.2) (sB2 lr ms.2) lr) E
          ((sProof lr ms.2, ()), L)) := by
      simp only [ex, hst]; rfl
    have hx : x = x0 ∧ σ = pick pk (tgts ah.1) (candidates E st (ex.1, ex.2, t)) := by
      rw [hsplit] at hvx
      simp only [Prod.mk.injEq] at hvx
      refine ⟨hvx.1.symm, ?_⟩
      rw [← hvx.2, hst, ht', hex']
    obtain ⟨hxx, hσ⟩ := hx
    subst hxx
    refine ⟨hi, hlen, hrfo, hp1, hp2, Ly, by rw [hpv], ?_, ?_, ?_⟩
    · rw [hz]
      show vsS.2.1 x0 = _
      rw [hfin, ← hah1]
      exact eval_htW_persistG g φ pre _ ah.2 (tStep_get φ x0 _ hsi)
    · rw [hsplit] at hvacc
      rw [ht']
      exact hvacc
    · rw [hσ, hah1]

end Accepted

end VoleMole.ROM.OneMore.Pomfrit
