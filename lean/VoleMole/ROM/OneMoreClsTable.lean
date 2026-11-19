import VoleMole.ROM.OneMoreCls

/-!
# The wrapped forger of U1^cls, table by table

`lean/docs/security/pomfrit.md` §6.4 (gap G8-cls). The reduction of Theorem U1^cls runs the forger
`A` wrapped (`wrapE`, `ROM/OneMoreCls.lean`): before each `H₂¹` query the wrapper makes the
decoder's `H₅` queries. This file compares, at fixed hash and cipher tables, the runs of `wrapE E A`
and of `A` with the cipher as queries (`wrapIC`, the void hint):

* `eval_wrapIC_toU`, `eval_coverIC`: the wrapper's own queries, table by table.
* **`eval_wrapIC_clsW`**: the same forgeries and target-oracle state; the joint logs agree once the
  `H₂⁴`, `H₄` and `H₅` entries are removed (`keepK`); and the wrapped run's log covers the decoder
  (`CovL`).

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.ZK.Sim VoleMole.Verifier.Bridge VoleMole.PomFRIT

/-! ## Filters of a joint log -/

/-- The entries that the wrapper does not add: the cipher entries and the hash entries of kinds other
than `H₂⁴`, `H₄`, `H₅`. -/
def keepK (e : (t : DomIC) × AnsIC t) : Bool :=
  match e.1 with
  | .inl d => decide (d.1 ≠ .muDelayed ∧ d.1 ≠ .h4 ∧ d.1 ≠ .h5)
  | .inr _ => true

/-- The `H₁` hash entries of a joint log. -/
def isH1E (e : (t : Dom) × Ans t) : Bool := decide (e.1.1 = .h1)

section Table

variable (g : Table) (E : CTable) (lr : Bool) (pre : TG → SIss)

/-- **A computation against `specIC`, run as the forger's queries by `wrapIC`**: its value, and its
log appended to the wrapper's. -/
theorem eval_wrapIC_toU (hint : QueryLog specIC → ByteArray → TG) {α : Type}
    (m : OracleComp specIC α) :
    ∀ (L : QueryLog specIC) (s : HTS × Gh),
      evalWithAnswerFn (QueryImpl.ofFn (join g E))
        ((simulateQ (wrapIC lr hint pre) (toU m)).run (L, s)) =
      (evalWithAnswerFn (QueryImpl.ofFn (join g E)) m, (L ++ tableQueryLog m (join g E), s)) := by
  induction m using OracleComp.inductionOn with
  | pure a => intro L s; simp [toU]
  | query_bind t k ih =>
    intro L s
    simp only [toU, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at ih ⊢
    erw [simulateQ_spec_query]
    simp only [wrapIC, evalWithAnswerFn_bind]
    have h1 : evalWithAnswerFn (QueryImpl.ofFn (join g E))
        ((StateT.mk fun s => (fun u => (u, s.1 ++ [⟨t, u⟩], s.2)) <$>
          (liftM (OracleSpec.query t) : OracleComp specIC (AnsIC t))).run (L, s)) =
        (join g E t, L ++ [⟨t, join g E t⟩], s) := rfl
    erw [h1, ih]
    erw [tableQueryLog_query_bind, evalWithAnswerFn_liftM_query]
    simp [List.append_assoc]

/-- The `H₅` query at `inp` and its log entry. -/
def h5E (inp : ByteArray) : OracleComp specIC ((t : DomIC) × AnsIC t) :=
  (fun u => (⟨.inl (.h5, inp), u⟩ : (t : DomIC) × AnsIC t)) <$>
    (liftM (specIC.query (.inl (.h5, inp))) : OracleComp specIC (Ans (.h5, inp)))

lemma eval_mapM_h5E (l : List ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (l.mapM h5E) =
        l.map (fun inp => (⟨.inl (.h5, inp), g (.h5, inp)⟩ : (t : DomIC) × AnsIC t)) ∧
      tableQueryLog (l.mapM h5E) (join g E) =
        l.map (fun inp => (⟨.inl (.h5, inp), g (.h5, inp)⟩ : (t : DomIC) × AnsIC t)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mapM_cons, evalWithAnswerFn_bind, evalWithAnswerFn_pure, List.map_cons,
      tableQueryLog_bind, tableQueryLog_pure, List.append_nil, ih.1, ih.2]
    refine ⟨rfl, ?_⟩
    simp only [h5E]
    erw [tableQueryLog_query]
    rfl

/-- The wrapper's queries before `x₁`, table by table. -/
noncomputable def covLog (L : QueryLog specIC) (x1 : ByteArray) : QueryLog specIC :=
  ⟨.inl muCell, g muCell⟩ :: ⟨.inl (ivCell lr x1 (g muCell).ba), g (ivCell lr x1 (g muCell).ba)⟩ ::
    (decIns lr E L x1 (g (ivCell lr x1 (g muCell).ba)).ba).map
      fun inp => (⟨.inl (.h5, inp), g (.h5, inp)⟩ : (t : DomIC) × AnsIC t)

theorem eval_coverIC (L : QueryLog specIC) (x1 : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (coverIC lr E L x1) = covLog g E lr L x1 ∧
      tableQueryLog (coverIC lr E L x1) (join g E) = covLog g E lr L x1 := by
  have h := eval_mapM_h5E g E (decIns lr E L x1 (g (ivCell lr x1 (g muCell).ba)).ba)
  unfold coverIC
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, tableQueryLog_bind, tableQueryLog_pure,
    List.append_nil]
  erw [evalWithAnswerFn_liftM_query, evalWithAnswerFn_liftM_query]
  erw [tableQueryLog_query, tableQueryLog_query]
  refine ⟨?_, ?_⟩
  · erw [h.1]; rfl
  · erw [h.2]; rfl

end Table

/-! ## Congruences: what the decoder's inputs read off the log -/

section Congr

lemma firstIn_filter_h1 (ok : ByteArray → Bool) (a : ByteArray) (G : QueryLog spec) :
    firstIn .h1 ok a (G.filter isH1E) = firstIn .h1 ok a G := by
  unfold firstIn
  rw [List.find?_filter]
  congr 2
  funext e
  simp only [isH1E]
  by_cases h : e.1.1 = .h1 <;> simp [h]

lemma comPre_filter (G : QueryLog spec) : comPre (G.filter isH1E) = comPre G := by
  funext x i j
  simp only [comPre, firstIn_filter_h1]

lemma comPre_congr {G G' : QueryLog spec} (h : G.filter isH1E = G'.filter isH1E) :
    comPre G = comPre G' := by
  rw [← comPre_filter G, h, comPre_filter]

lemma keyPre_congr (E : CTable) {G G' : QueryLog spec} {J J' : QueryLog specIC}
    (hG : G.filter isH1E = G'.filter isH1E) (hJ : cipherLog J = cipherLog J') (iv x : ByteArray) :
    keyPre E G J iv x = keyPre E G' J' iv x := by
  funext i j
  simp only [keyPre, comPre_congr hG, hJ]

lemma deadPre_congr (E : CTable) {G G' : QueryLog spec} {J J' : QueryLog specIC}
    (hG : G.filter isH1E = G'.filter isH1E) (hJ : cipherLog J = cipherLog J') (iv x : ByteArray) :
    deadPre E G J iv x = deadPre E G' J' iv x := by
  funext i
  simp only [deadPre, comPre_congr hG, hJ]

/-- **The decoder's inputs read the log through its `H₁` entries and its cipher entries.** -/
lemma decIns_congr (lr : Bool) (E : CTable) {L L' : QueryLog specIC}
    (hG : (hashEnt L).filter isH1E = (hashEnt L').filter isH1E) (hJ : cipherLog L = cipherLog L')
    (x1 iv : ByteArray) : decIns lr E L x1 iv = decIns lr E L' x1 iv := by
  simp only [decIns, pcOf, aliveOf, keyPre_congr E hG hJ, deadPre_congr E hG hJ]

end Congr

/-! ## The wrapped run and the plain run -/

section Core

variable (g : Table) (E : CTable) (lr : Bool) (pre : TG → SIss)

/-- **The relation between the wrapper's log `Lw`, the wrapped run's joint log `L` and the plain
run's joint log `L'`**: `Lw` and `L` have the same `H₁` and cipher entries; `L` and `L'` agree up to
the `H₂⁴`, `H₄`, `H₅` entries; `L` covers the decoder. -/
lemma eval_wrapIC_queryL (hint : QueryLog specIC → ByteArray → TG) (d : DomIC) (L : QueryLog specIC)
    (s : HTS × Gh) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) ((simulateQ (wrapIC lr hint pre)
      (liftM (specU.query (.inl d)) : OracleComp specU (AnsIC d))).run (L, s)) =
      (join g E d, (L ++ [⟨d, join g E d⟩], s)) := by
  erw [simulateQ_spec_query]
  rfl

/-- The wrapper's queries before the query `d`, table by table. -/
noncomputable def cvOf (Lw : QueryLog specIC) : DomIC → QueryLog specIC
  | .inl (k, x1) => if k = .h21 then covLog g E lr Lw x1 else []
  | .inr _ => []

lemma eval_coverAt (Lw : QueryLog specIC) (d : DomIC) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (coverAt lr E Lw d) = cvOf g E lr Lw d ∧
      tableQueryLog (coverAt lr E Lw d) (join g E) = cvOf g E lr Lw d := by
  rcases d with ⟨k, x1⟩ | c
  · by_cases hk : k = .h21
    · subst hk; simpa [coverAt, cvOf] using eval_coverIC g E lr Lw x1
    · simp [coverAt, cvOf, hk]
  · simp [coverAt, cvOf]

structure RelW (Lw L L' : QueryLog specIC) : Prop where
  h1 : (hashEnt Lw).filter isH1E = (hashEnt L).filter isH1E
  ciph : cipherLog Lw = cipherLog L
  keep : L.filter keepK = L'.filter keepK
  cov : CovL lr E g L

lemma ivX_eq_ivCell (x1 : ByteArray) :
    ivX (stE lr) x1 g = (g (ivCell lr x1 (g muCell).ba)).ba := by
  simp only [ivX, mu1_stE]
  rfl

lemma covLog_keep (Lw : QueryLog specIC) (x1 : ByteArray) :
    (covLog g E lr Lw x1).filter keepK = [] := by
  simp [covLog, keepK, muCell, ivCell, List.filter_map, Function.comp_def]

lemma cvOf_keep (Lw : QueryLog specIC) (d : DomIC) : (cvOf g E lr Lw d).filter keepK = [] := by
  rcases d with ⟨k, x1⟩ | c
  · by_cases hk : k = .h21
    · simp [cvOf, hk, covLog_keep]
    · simp [cvOf, hk]
  · simp [cvOf]

lemma hashEnt_filter_h1_of_keep {C : QueryLog specIC} (h : C.filter keepK = []) :
    (hashEnt C).filter isH1E = [] := by
  rw [List.filter_eq_nil_iff] at h
  induction C with
  | nil => rfl
  | cons e C ih =>
    have ih' := ih fun a ha => h a (List.mem_cons_of_mem _ ha)
    obtain ⟨t, u⟩ := e
    cases t with
    | inl d =>
      have hk := h _ List.mem_cons_self
      have hd : d.1 ≠ .h1 := by
        intro hd; simp [keepK, hd] at hk
      simp [hashEnt, isH1E, hd, ih']
    | inr c => simp [keepK] at h

lemma cipherLog_of_keep {C : QueryLog specIC} (h : C.filter keepK = []) : cipherLog C = [] := by
  rw [List.filter_eq_nil_iff] at h
  unfold cipherLog
  rw [List.filterMap_eq_nil_iff]
  intro e he
  obtain ⟨t, u⟩ := e
  cases t with
  | inl d => rfl
  | inr c => have := h _ he; simp [keepK] at this

lemma not_h21_of_keep {C : QueryLog specIC} (h : C.filter keepK = []) (x1 : ByteArray) :
    (.inl (.h21, x1) : DomIC) ∉ C.map Sigma.fst := by
  intro hm
  obtain ⟨e, he, he1⟩ := List.mem_map.1 hm
  have : e ∈ C.filter keepK := List.mem_filter.2 ⟨he, by simp [keepK, he1]⟩
  rw [h] at this
  simp at this

/-- **A hash or cipher query keeps the relation.** -/
lemma relW_hash {Lw L L' : QueryLog specIC} (h : RelW g E lr Lw L L') (d : DomIC) :
    RelW g E lr (Lw ++ cvOf g E lr Lw d ++ [⟨d, join g E d⟩])
      (L ++ cvOf g E lr Lw d ++ [⟨d, join g E d⟩]) (L' ++ [⟨d, join g E d⟩]) := by
  have hk := cvOf_keep g E lr Lw d
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hashEnt_append, List.filter_append, h.h1]
  · simp only [IC.cipherLog_append, h.ciph]
  · simp only [List.filter_append, hk, h.keep, List.append_nil]
  · intro x1 hx inp hinp
    by_cases hL : (.inl (.h21, x1) : DomIC) ∈ L.map Sigma.fst
    · rw [List.append_assoc, logBefore_append_of_mem _ hL] at hinp ⊢
      exact h.cov x1 (mem_hashLog.2 hL) inp hinp
    · have hC := not_h21_of_keep hk x1
      have hLC : (.inl (.h21, x1) : DomIC) ∉ (L ++ cvOf g E lr Lw d).map Sigma.fst := by
        rw [List.map_append, List.mem_append, not_or]; exact ⟨hL, hC⟩
      have hd : d = .inl (.h21, x1) := by
        have := mem_hashLog.1 hx
        rw [List.map_append, List.mem_append] at this
        rcases this with h' | h'
        · exact absurd h' hLC
        · simp at h'; exact h'.symm
      subst hd
      rw [logBefore_append_of_not_mem _ hLC] at hinp ⊢
      simp only [logBefore_cons_self, List.append_nil] at hinp ⊢
      have hdec : decIns lr E (L ++ cvOf g E lr Lw (.inl (.h21, x1))) x1 (ivX (stE lr) x1 g) =
          decIns lr E Lw x1 (g (ivCell lr x1 (g muCell).ba)).ba := by
        rw [ivX_eq_ivCell]
        refine decIns_congr lr E ?_ ?_ _ _
        · rw [hashEnt_append, List.filter_append, hashEnt_filter_h1_of_keep hk, List.append_nil,
            h.h1]
        · rw [IC.cipherLog_append, cipherLog_of_keep hk, List.append_nil, h.ciph]
      rw [hdec] at hinp
      refine mem_hashLog.2 (List.mem_map.2 ⟨⟨.inl (.h5, inp), g (.h5, inp)⟩, ?_, rfl⟩)
      refine List.mem_append_right _ ?_
      simp only [cvOf, ite_true, covLog]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨inp, hinp, rfl⟩))

lemma eval_wrapIC_queryT (x : ByteArray) (L : QueryLog specIC) (hs : HTS) (gh : Gh) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) ((simulateQ (wrapIC lr hintVoid pre)
      (liftM (specU.query (.inr (.inl x))) : OracleComp specU TG)).run (L, hs, gh)) =
      ((tStep addHint x 0 hs).1.1, (L ++ axT g lr L x, (tStep addHint x 0 hs).2,
        if hs.1 x = none then Function.update gh x (some (L ++ axT g lr L x)) else gh)) := by
  erw [simulateQ_spec_query]
  show evalWithAnswerFn (QueryImpl.ofFn (join g E)) (toHIC (auxSpec lr L x) >>= fun ax => pure _) = _
  rw [evalWithAnswerFn_bind]
  erw [evalWithAnswerFn_pure, eval_toHIC]
  rfl

lemma eval_wrapIC_queryI (t : TG) (L : QueryLog specIC) (hs : HTS) (gh : Gh) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) ((simulateQ (wrapIC lr hintVoid pre)
      (liftM (specU.query (.inr (.inr t))) : OracleComp specU SIss)).run (L, hs, gh)) =
      (pre t, (L, (hs.1, hs.2.1, hs.2.2.1, hs.2.2.2 + 1), gh)) := by
  erw [simulateQ_spec_query]
  rfl

lemma axT_keep (L : QueryLog specIC) (x : ByteArray) :
    (axT g lr L x).filter keepK = [⟨.inl (.h3, x), g (.h3, x)⟩] := by
  cases hx : x1Of L x with
  | some x1 => rw [axT_of_some g lr hx]; simp [keepK, muCell, ivCell]
  | none => rw [axT_of_none g lr hx]; simp [keepK, muCell]

lemma axT_h1 (L : QueryLog specIC) (x : ByteArray) : (hashEnt (axT g lr L x)).filter isH1E = [] := by
  cases hx : x1Of L x with
  | some x1 => rw [axT_of_some g lr hx]; simp [hashEnt, isH1E, muCell, ivCell]
  | none => rw [axT_of_none g lr hx]; simp [hashEnt, isH1E, muCell]

lemma axT_cipher (L : QueryLog specIC) (x : ByteArray) : cipherLog (axT g lr L x) = [] := by
  cases hx : x1Of L x with
  | some x1 => rw [axT_of_some g lr hx]; rfl
  | none => rw [axT_of_none g lr hx]; rfl

lemma axT_not_h21 (L : QueryLog specIC) (x x1 : ByteArray) :
    (.inl (.h21, x1) : DomIC) ∉ (axT g lr L x).map Sigma.fst := by
  cases hx : x1Of L x with
  | some x1 => rw [axT_of_some g lr hx]; simp [muCell, ivCell]
  | none => rw [axT_of_none g lr hx]; simp [muCell]

/-- **A target query keeps the relation.** -/
lemma relW_ht {Lw L L' : QueryLog specIC} (h : RelW g E lr Lw L L') (x : ByteArray) :
    RelW g E lr Lw (L ++ axT g lr L x) (L' ++ axT g lr L' x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hashEnt_append, List.filter_append, axT_h1, List.append_nil, h.h1]
  · rw [IC.cipherLog_append, axT_cipher, List.append_nil, h.ciph]
  · rw [List.filter_append, List.filter_append, axT_keep, axT_keep, h.keep]
  · intro x1 hx inp hinp
    have hL : (.inl (.h21, x1) : DomIC) ∈ L.map Sigma.fst := by
      have := mem_hashLog.1 hx
      rw [List.map_append, List.mem_append] at this
      exact this.resolve_right (axT_not_h21 g lr L x x1)
    rw [logBefore_append_of_mem _ hL] at hinp ⊢
    exact h.cov x1 (mem_hashLog.2 hL) inp hinp

theorem eval_wrapIC_clsW {α : Type} (oa : OracleComp specU α) :
    ∀ (Lw L L' : QueryLog specIC) (s : HTS × Gh) (gh' : Gh), RelW g E lr Lw L L' →
      let b := evalWithAnswerFn (QueryImpl.ofFn (join g E))
        ((simulateQ (wrapIC lr hintVoid pre) ((simulateQ (clsW lr E) oa).run Lw)).run (L, s))
      let c := evalWithAnswerFn (QueryImpl.ofFn (join g E))
        ((simulateQ (wrapIC lr hintVoid pre) oa).run (L', s.1, gh'))
      b.1.1 = c.1 ∧ b.2.2.1 = c.2.2.1 ∧ RelW g E lr b.1.2 b.2.1 c.2.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro Lw L L' s gh' h; simpa using h
  | query_bind q k ih =>
    intro Lw L L' s gh' h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with d | (x | t)
    · simp only [clsW, StateT.run_mk, simulateQ_bind, StateT.run_bind, evalWithAnswerFn_bind]
      rw [eval_wrapIC_toU]
      erw [eval_wrapIC_queryL g E lr pre hintVoid d, eval_wrapIC_queryL g E lr pre hintVoid d]
      simp only [simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure, (eval_coverAt g E lr Lw d).1,
        (eval_coverAt g E lr Lw d).2]
      exact ih (join g E d) _ _ _ s gh' (relW_hash g E lr h d)
    · simp only [clsW, StateT.run_mk, simulateQ_map, StateT.run_map]
      simp only [wrapIC, StateT.run_mk, evalWithAnswerFn_bind, evalWithAnswerFn_pure, bind_map_left]
      erw [eval_wrapIC_queryT g E lr pre x L s.1 s.2]
      simp only [eval_toHIC, hintVoid]
      exact ih _ Lw _ _ _ _ (relW_ht g E lr h x)
    · simp only [clsW, StateT.run_mk, simulateQ_map, StateT.run_map]
      simp only [wrapIC, StateT.run_mk, evalWithAnswerFn_bind, evalWithAnswerFn_pure, bind_map_left]
      erw [eval_wrapIC_queryI g E lr pre t L s.1 s.2]
      exact ih _ Lw _ _ _ _ h

/-- **The wrapped forger's run and the forger's, table by table** (void hint, from the start): the
same forgeries and target-oracle state, logs that agree up to the `H₂⁴`, `H₄`, `H₅` entries, and the
wrapped run's log covers the decoder. -/
theorem eval_wrapE (A : Forger) (pk : UovPk) (hs : HTS) :
    let b := evalWithAnswerFn (QueryImpl.ofFn (join g E))
      ((simulateQ (wrapIC lr hintVoid pre) (wrapE lr E A pk)).run ([], hs, fun _ => none))
    let c := evalWithAnswerFn (QueryImpl.ofFn (join g E))
      ((simulateQ (wrapIC lr hintVoid pre) (A pk)).run ([], hs, fun _ => none))
    b.1 = c.1 ∧ b.2.2.1 = c.2.2.1 ∧ b.2.1.filter keepK = c.2.1.filter keepK ∧ CovL lr E g b.2.1 := by
  intro b c
  have h0 : RelW g E lr [] [] [] :=
    ⟨rfl, rfl, rfl, fun x1 hx => by simp [hashLog] at hx⟩
  obtain ⟨e1, e2, e3⟩ := eval_wrapIC_clsW g E lr pre (A pk) [] [] [] (hs, fun _ => none)
    (fun _ => none) h0
  have hb : b = (fun z => (z.1.1, z.2)) (evalWithAnswerFn (QueryImpl.ofFn (join g E))
      ((simulateQ (wrapIC lr hintVoid pre) ((simulateQ (clsW lr E) (A pk)).run [])).run
        ([], hs, fun _ => none))) := by
    simp only [b, wrapE, StateT.run'_eq, simulateQ_map, StateT.run_map, evalWithAnswerFn_map]
  rw [hb]
  exact ⟨e1, e2, e3.keep, e3.cov⟩

end Core

/-! ## The derived provers of the wrapped forger and of the forger -/

section Derived

variable (g : Table) (E : CTable) (lr : Bool) (pk : UovPk) (pre : TG → SIss)

/-- The hash entries kept by `keepK`. -/
def keepH (e : (t : Dom) × Ans t) : Bool := decide (e.1.1 ≠ .muDelayed ∧ e.1.1 ≠ .h4 ∧ e.1.1 ≠ .h5)

lemma hashEnt_filter_keepK (L : QueryLog specIC) : hashEnt (L.filter keepK) = (hashEnt L).filter keepH := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨t, u⟩ := e
    cases t with
    | inl d => by_cases h : keepH ⟨d, u⟩ <;> simp_all [hashEnt, keepK, keepH]
    | inr c => simp [hashEnt, keepK, List.filter_cons, ih]

lemma firstIn_filter_of {k : Kind} (p : (t : Dom) × Ans t → Bool) (hp : ∀ e, e.1.1 = k → p e = true)
    (ok : ByteArray → Bool) (a : ByteArray) (G : QueryLog spec) :
    firstIn k ok a (G.filter p) = firstIn k ok a G := by
  unfold firstIn
  rw [List.find?_filter]
  congr 2
  funext e
  by_cases h : e.1.1 = k
  · simp [hp e h, h]
  · simp [h]

lemma x1Of_congr {L L' : QueryLog specIC} (h : L.filter keepK = L'.filter keepK) (x : ByteArray) :
    x1Of L x = x1Of L' x := by
  have hp : ∀ e : (t : Dom) × Ans t, e.1.1 = .h21 → keepH e = true := fun e he => by
    simp [keepH, he]
  unfold x1Of
  rw [← firstIn_filter_of keepH hp, ← hashEnt_filter_keepK, h, hashEnt_filter_keepK,
    firstIn_filter_of keepH hp]

lemma auxSpec_congr {L L' : QueryLog specIC} (h : ∀ x, x1Of L x = x1Of L' x) (x : ByteArray) :
    auxSpec lr L x = auxSpec lr L' x := by
  unfold auxSpec; rw [h x]

set_option maxRecDepth 20000 in
lemma verPreIC_congr {L L' : QueryLog specIC} (h : ∀ x, x1Of L x = x1Of L' x) (m sg : ByteArray)
    {s s' : HTS × Gh} (hs : s.1 = s'.1) :
    (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verPreIC lr pk L m sg s)).1 =
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verPreIC lr pk L' m sg s')).1 ∧
      tableQueryLog (verPreIC lr pk L m sg s) (join g E) =
        tableQueryLog (verPreIC lr pk L' m sg s') (join g E) := by
  unfold verPreIC
  split_ifs with hr
  · simp [hs]
  · simp only [evalWithAnswerFn_bind, tableQueryLog_bind, eval_chal1PreIC_st0]
    cases c1T g lr E pk sg with
    | none => simp [hs]
    | some c1 =>
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, tableQueryLog_bind,
        tableQueryLog_pure, auxSpec_congr lr h, hs]
      exact ⟨trivial, trivial⟩

lemma verPreAll_congr {L L' : QueryLog specIC} (h : ∀ x, x1Of L x = x1Of L' x) :
    ∀ (l : List (ByteArray × ByteArray)) (s s' : HTS × Gh), s.1 = s'.1 →
      (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verPreAll lr pk L l s)).1 =
          (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verPreAll lr pk L' l s')).1 ∧
        tableQueryLog (verPreAll lr pk L l s) (join g E) =
          tableQueryLog (verPreAll lr pk L' l s') (join g E)
  | [], s, s', hs => by simp [verPreAll, hs]
  | (m, sg) :: rest, s, s', hs => by
    obtain ⟨e1, e2⟩ := verPreIC_congr g E lr pk h m sg hs
    obtain ⟨f1, f2⟩ := verPreAll_congr h rest _ _ e1
    simp only [verPreAll, evalWithAnswerFn_bind, tableQueryLog_bind, e2, f1, f2]
    exact ⟨trivial, trivial⟩

set_option maxRecDepth 20000 in
lemma verLastIC_congr {L L' : QueryLog specIC} (h : ∀ x, x1Of L x = x1Of L' x)
    (ms : ByteArray × ByteArray) {s s' : HTS × Gh} (hs : s.1 = s'.1) :
    (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verLastIC lr pk L ms s)).1 =
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verLastIC lr pk L' ms s')).1 ∧
      (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verLastIC lr pk L ms s)).2.1 =
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verLastIC lr pk L' ms s')).2.1 ∧
      tableQueryLog (verLastIC lr pk L ms s) (join g E) =
        tableQueryLog (verLastIC lr pk L' ms s') (join g E) := by
  unfold verLastIC
  simp only [evalWithAnswerFn_bind, tableQueryLog_bind, eval_chal1PreIC_st0]
  cases c1T g lr E pk ms.2 with
  | none => simp
  | some c1 =>
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, tableQueryLog_bind,
      tableQueryLog_pure, auxSpec_congr lr h, hs]
    exact ⟨trivial, trivial, trivial⟩

lemma contP_congr (i : ℕ) {r r' : List (ByteArray × ByteArray) × QueryLog specIC × HTS × Gh}
    (h1 : r.1 = r'.1) (h2 : r.2.2.1 = r'.2.2.1) (hx : ∀ x, x1Of r.2.1 x = x1Of r'.2.1 x) :
    (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (contP lr pk i r)).1 =
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (contP lr pk i r')).1 ∧
      (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (contP lr pk i r)).2.1 =
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) (contP lr pk i r')).2.1 ∧
      tableQueryLog (contP lr pk i r) (join g E) = tableQueryLog (contP lr pk i r') (join g E) := by
  unfold contP
  obtain ⟨e1, e2⟩ := verPreAll_congr g E lr pk hx (r.1.take i) (r.2.2.1, r.2.2.2)
    (r'.2.2.1, r'.2.2.2) h2
  rw [← h1]
  obtain ⟨f1, f2, f3⟩ := verLastIC_congr g E lr pk hx (r.1.getD i (ByteArray.empty, ByteArray.empty)) e1
  simp only [evalWithAnswerFn_bind, tableQueryLog_bind, e2, f1, f2, f3]
  exact ⟨trivial, trivial, trivial⟩

/-- **The derived provers of the wrapped forger and of the forger, table by table**: the same proof
and statement, and joint logs that agree up to the `H₂⁴`, `H₄`, `H₅` entries; the wrapped one's
forger log covers the decoder. -/
theorem eval_proverP_wrapE (A : Forger) (Lst : List TG) (i : ℕ) :
    let p' := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (proverP lr pk pre (wrapE lr E A) Lst i)
    let p := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (proverP lr pk pre A Lst i)
    p'.1 = p.1 ∧ p'.2.1 = p.2.1 ∧
      (tableQueryLog (proverP lr pk pre (wrapE lr E A) Lst i) (join g E)).filter keepK =
        (tableQueryLog (proverP lr pk pre A Lst i) (join g E)).filter keepK := by
  intro p' p
  obtain ⟨e1, e2, e3, -⟩ := eval_wrapE g E lr pre A pk (hs0 Lst)
  have hx := x1Of_congr e3
  obtain ⟨f1, f2, f3⟩ := contP_congr g E lr pk i e1 e2 hx
  refine ⟨?_, ?_, ?_⟩
  · simp only [p', p, proverP_eq, evalWithAnswerFn_bind]; exact f1
  · simp only [p', p, proverP_eq, evalWithAnswerFn_bind]; exact f2
  · rw [log_proverP, log_proverP, List.filter_append, List.filter_append, e3, f3]

end Derived

end VoleMole.ROM.OneMore.Pomfrit
