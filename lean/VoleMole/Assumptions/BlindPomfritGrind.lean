import VoleMole.Assumptions.PomClientLean
import VoleMole.ROM.FreshGuess

/-!
# Grinding answers at a prefix computed without `H₂³` are uniform (lazy random oracle)

`lean/docs/security/pomfrit.md` G9. The completeness failure of a PomFRIT session is `GrindBad` of
the `2³²` `H₂³` answers at its grinding prefix (`ZK/HopsH23.lean`; `≤ 2⁻¹¹³`,
`ZK/GrindNum.lean`). In the game the prefix is computed by the run itself, against the same lazy
random oracle. If that computation makes no `H₂³` query, the answers at the prefix's grinding
points are fresh, hence uniform: **`prEvent_grindBad_le`**,

    Pr[GrindBad(H₂³ answers at pfx's output)] ≤ 2⁻¹¹³,

for every computation `pfx` (over the world of `Assumptions/BlindPomfrit.lean`: the forger's
random oracle and the hashes) with no `H₂³` query (`NoH23W`). Proof: the lazy oracle as a uniform
table on a finite key set (`ROM/ExtractReduce.lean`, `prEvent_eq_extendTable`), then the class
counting of `ROM/FreshGuess.lean` (`card_finOf_mul_le`) with the `2³²` grinding cells of a prefix
as one block: updating the block changes neither the prefix (`pfx` does not read it,
`eval_congr_allQ`) nor the event's class.

Generic table lemmas used later: `eval_congr_allQ` (a computation's value depends only on the
cells it may query), `allQ_simulateQ_run` (query predicates through a stateful simulation),
`eval_run_inv` (an invariant of a stateful simulation evaluated at a table).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec Finset VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.OneMore
  VoleMole.ROM.OneMore.Pomfrit VoleMole.Verifier VoleMole.ZK.Sim VoleMole.Assumptions.Blind
open scoped ENNReal

namespace VoleMole.Assumptions.BlindPomfrit

/-! ## Generic facts about evaluation at a table -/

section Generic

variable {D : Type} {R : D → Type} {α : Type}

/-- **A computation's value at a table depends only on the cells it may query.** -/
theorem eval_congr_allQ {oa : OracleComp (ofFn R) α} {P : D → Prop} (h : AllQueriesSatisfy oa P)
    {g g' : (d : D) → R d} (hg : ∀ d, P d → g d = g' d) :
    evalWithAnswerFn (QueryImpl.ofFn g) oa = evalWithAnswerFn (QueryImpl.ofFn g') oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
    rw [hg t h.1]
    exact ih _ (h.2 _)

variable {ι ι' σ : Type} {sp : OracleSpec ι} {sp' : OracleSpec ι'}

/-- **Query predicates through a stateful simulation.** -/
theorem allQ_simulateQ_run (h : QueryImpl sp (StateT σ (OracleComp sp'))) {P : ι' → Prop}
    (hh : ∀ q s, AllQueriesSatisfy ((h q).run s) P) :
    ∀ (oa : OracleComp sp α) (s : σ), AllQueriesSatisfy ((simulateQ h oa).run s) P := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro s; exact allQueriesSatisfy_pure _ _
  | query_bind q k ih =>
    intro s
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (hh q s) fun p => ih p.1 p.2

/-- Query predicates through a stateless simulation. -/
theorem allQ_simulateQ (h : QueryImpl sp (OracleComp sp')) {P : ι' → Prop}
    (hh : ∀ q, AllQueriesSatisfy (h q) P) :
    ∀ (oa : OracleComp sp α), AllQueriesSatisfy (simulateQ h oa) P := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact allQueriesSatisfy_bind (hh q) fun p => ih p

/-- **An invariant of a stateful simulation, evaluated at a table.** -/
theorem eval_run_inv (g : (d : D) → R d) (h : QueryImpl sp (StateT σ (OracleComp (ofFn R))))
    (I : σ → Prop)
    (hI : ∀ q s, I s → I (evalWithAnswerFn (QueryImpl.ofFn g) ((h q).run s)).2) :
    ∀ (oa : OracleComp sp α) (s : σ), I s →
      I (evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ h oa).run s)).2 := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro s hs; exact hs
  | query_bind q k ih =>
    intro s hs
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evalWithAnswerFn_bind]
    exact ih _ _ (hI q s hs)

end Generic

/-! ## The grinding block in the game's world -/

section Block

variable {DR : Type} [DecidableEq DR] {AR : DR → Type}

/-- Not an `H₂³` query (the forger's own oracle, or a hash of another kind). -/
def NoH23W : DR ⊕ Dom → Prop
  | .inl _ => True
  | .inr d => d.1 ≠ .h23

/-- The `H₂³` cell of a grinding point. -/
abbrev gcell (pre : ByteArray) (c : Fin nGrind) : DR ⊕ Dom := .inr (.h23, grindInput pre c)

/-- **The `2³²` `H₂³` answers at a prefix's grinding points**, queried in the game's world. -/
def blockW (pre : ByteArray) : OracleComp (ofFn (WB AR)) (Fin nGrind → Bytes 16) :=
  (fun l c => l.getD c.val 0) <$> (List.finRange nGrind).mapM fun c =>
    (liftM ((ofFn (WB AR)).query (gcell pre c)) : OracleComp (ofFn (WB AR)) (Bytes 16))

lemma getD_map_finRange {β : Type} (N : ℕ) (f : Fin N → β) (d : β) (c : Fin N) :
    ((List.finRange N).map f).getD c.val d = f c := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

omit [DecidableEq DR] in
lemma eval_blockW (g : (d : DR ⊕ Dom) → WB AR d) (pre : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn g) (blockW (AR := AR) pre) =
      fun c => (g (gcell pre c) : Bytes 16) := by
  unfold blockW
  rw [evalWithAnswerFn_map, evalWithAnswerFn_mapM]
  funext c
  exact getD_map_finRange nGrind _ 0 c

end Block

/-! ## The bound -/

section Bound

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, Fintype (AR d)]
  [∀ d, Nonempty (AR d)] [∀ d, SampleableType (AR d)]

/-- The answers of the game's world are finite. -/
instance instFinWB : ∀ d, Fintype (WB AR d)
  | .inl d => inferInstanceAs (Fintype (AR d))
  | .inr d => inferInstanceAs (Fintype (Ans d))

instance instNeWB : ∀ d, Nonempty (WB AR d)
  | .inl d => inferInstanceAs (Nonempty (AR d))
  | .inr _ => ⟨fun _ => 0⟩

omit [DecidableEq DR] [∀ d, Fintype (AR d)] [∀ d, Nonempty (AR d)] [∀ d, SampleableType (AR d)] in
lemma gcell_zero_inj {p p' : ByteArray} (h : gcell (DR := DR) p 0 = gcell p' 0) : p = p' := by
  simp only [gcell, Sum.inr.injEq, Prod.mk.injEq, true_and, grindInput] at h
  have h1 := push_injective 11 h
  rw [Bridge.pushLE32_eq p, Bridge.pushLE32_eq p'] at h1
  have hs : p.size = p'.size := by
    have := congrArg ByteArray.size h1
    simpa [ByteArray.size_append] using this
  have e1 : (p ++ AES.pushLE32 ByteArray.empty (0 : Fin nGrind).val.toUInt32).extract 0 p.size = p :=
    ByteArray.extract_append_eq_left rfl
  rw [h1, hs, ByteArray.extract_append_eq_left rfl] at e1
  exact e1.symm

omit [DecidableEq DR] [∀ d, Fintype (AR d)] [∀ d, Nonempty (AR d)] [∀ d, SampleableType (AR d)] in
lemma gcell_inj {p : ByteArray} {c c' : Fin nGrind} (h : gcell (DR := DR) p c = gcell p c') :
    c = c' := by
  simp only [gcell, Sum.inr.injEq, Prod.mk.injEq, true_and] at h
  exact grindInput_injective p h

variable (S : Finset (DR ⊕ Dom))

/-- Writing the block of `pre`'s grinding cells. -/
noncomputable def updW (pre : ByteArray) (w : Fin nGrind → Bytes 16) (x : DR ⊕ Dom) (v : WB AR x) :
    WB AR x := by
  classical
  exact if h : ∃ c, x = gcell pre c then
      cast (congrArg (WB AR) h.choose_spec).symm (w h.choose : WB AR (gcell pre h.choose))
    else v

omit [∀ d, Fintype (AR d)] [∀ d, Nonempty (AR d)] [∀ d, SampleableType (AR d)] in
lemma updW_updW (pre : ByteArray) (w w' : Fin nGrind → Bytes 16) (x : DR ⊕ Dom) (v : WB AR x) :
    updW pre w' x (updW pre w x v) = updW pre w' x v := by
  unfold updW
  split_ifs <;> rfl

omit [∀ d, Fintype (AR d)] [∀ d, Nonempty (AR d)] [∀ d, SampleableType (AR d)] in
lemma updW_gcell (pre : ByteArray) (w : Fin nGrind → Bytes 16) (c : Fin nGrind) (v : WB AR (gcell pre c)) :
    (updW pre w (gcell pre c) v : Bytes 16) = w c := by
  unfold updW
  have h : ∃ c', gcell (DR := DR) pre c = gcell pre c' := ⟨c, rfl⟩
  rw [dite_eq_left h]
  have key : ∀ c' (e : gcell (DR := DR) pre c = gcell pre c'),
      (cast (congrArg (WB AR) e).symm (w c' : WB AR (gcell pre c')) : Bytes 16) = w c := by
    intro c' e
    have hc := gcell_inj e
    subst hc
    rfl
  exact key _ h.choose_spec

omit [∀ d, Fintype (AR d)] [∀ d, Nonempty (AR d)] [∀ d, SampleableType (AR d)] in
lemma updW_ne (pre : ByteArray) (w : Fin nGrind → Bytes 16) (x : DR ⊕ Dom) (hx : NoH23W x)
    (v : WB AR x) : updW pre w x v = v := by
  unfold updW
  rw [dite_eq_right]
  rintro ⟨c, rfl⟩
  exact hx rfl

/-- Reading the block of `pre`'s grinding cells from a restricted table. -/
noncomputable def rdW (G : (d : S) → WB AR d.val) (pre : ByteArray) : Fin nGrind → Bytes 16 := by
  classical
  exact fun c => if h : gcell pre c ∈ S then (G ⟨gcell pre c, h⟩ : Bytes 16) else 0

/-- The prefix of a block's first cell. -/
noncomputable def preOf (d : DR ⊕ Dom) : ByteArray := by
  classical
  exact if h : ∃ p, d = gcell p 0 then h.choose else .empty

omit [DecidableEq DR] [∀ d, Fintype (AR d)] [∀ d, Nonempty (AR d)] [∀ d, SampleableType (AR d)] in
lemma preOf_gcell (p : ByteArray) : preOf (gcell (DR := DR) p 0) = p := by
  unfold preOf
  have h : ∃ p', gcell (DR := DR) p 0 = gcell p' 0 := ⟨p, rfl⟩
  rw [dite_eq_left h]
  exact (gcell_zero_inj h.choose_spec).symm

/-- Writing the block of the index `i` (a block's first cell). -/
noncomputable def upI (G : (d : S) → WB AR d.val) : Option S → (Fin nGrind → Bytes 16) →
    (d : S) → WB AR d.val
  | none, _ => G
  | some i, w => fun d => updW (preOf i.val) w d.val (G d)

/-- Reading the block of the index `i`. -/
noncomputable def rdI (G : (d : S) → WB AR d.val) : Option S → Fin nGrind → Bytes 16
  | none => fun _ _ => 0
  | some i => rdW S G (preOf i.val)

omit [∀ d, Fintype (AR d)] [∀ d, Nonempty (AR d)] [∀ d, SampleableType (AR d)] in
lemma upI_upI (G : (d : S) → WB AR d.val) (i : Option S) (w w' : Fin nGrind → Bytes 16) :
    upI S (upI S G i w) i w' = upI S G i w' := by
  cases i with
  | none => rfl
  | some i => funext d; exact updW_updW _ _ _ _ _

omit [∀ d, Fintype (AR d)] [∀ d, Nonempty (AR d)] [∀ d, SampleableType (AR d)] in
lemma upI_rdI (G : (d : S) → WB AR d.val) (i : Option S) : upI S G i (rdI S G i) = G := by
  cases i with
  | none => rfl
  | some i =>
    funext d
    obtain ⟨x, hx⟩ := d
    show updW (preOf i.val) (rdW S G (preOf i.val)) x (G ⟨x, hx⟩) = G ⟨x, hx⟩
    by_cases h : ∃ c, x = gcell (preOf i.val) c
    · obtain ⟨c, rfl⟩ := h
      have := updW_gcell (AR := AR) (preOf i.val) (rdW S G (preOf i.val)) c (G ⟨_, hx⟩)
      refine this.trans ?_
      exact dite_eq_left hx
    · unfold updW
      rw [dite_eq_right h]

omit [∀ d, Fintype (AR d)] [∀ d, Nonempty (AR d)] [∀ d, SampleableType (AR d)] in
lemma rdI_upI (G : (d : S) → WB AR d.val) (i : S) (hv : ∀ c, gcell (preOf i.val) c ∈ S)
    (w : Fin nGrind → Bytes 16) : rdI S (upI S G (some i) w) (some i) = w := by
  funext c
  simp only [rdI, upI, rdW]
  exact (dite_eq_left (hv c)).trans (updW_gcell (preOf i.val) w c _)

omit [DecidableEq DR] [∀ d, Fintype (AR d)] [∀ d, Nonempty (AR d)] [∀ d, SampleableType (AR d)] in
lemma mem_log_blockW (g : (d : DR ⊕ Dom) → WB AR d) (pre : ByteArray) (c : Fin nGrind) :
    gcell pre c ∈ (tableQueryLog (blockW (AR := AR) pre) g).map Sigma.fst := by
  unfold blockW
  simp only [map_eq_bind_pure_comp]
  rw [tableQueryLog_bind, Function.comp_def, tableQueryLog_pure, List.append_nil]
  have key : ∀ l : List (Fin nGrind), c ∈ l → gcell pre c ∈ (tableQueryLog (l.mapM fun c =>
      (liftM ((ofFn (WB AR)).query (gcell pre c)) : OracleComp (ofFn (WB AR)) (Bytes 16))) g).map
        Sigma.fst := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons a l ih =>
      rw [List.mapM_cons, tableQueryLog_bind]
      erw [tableQueryLog_query_bind]
      simp only [List.cons_append, List.map_cons]
      rcases List.mem_cons.1 hl with rfl | hl
      · exact List.mem_cons_self
      · refine List.mem_cons_of_mem _ ?_
        rw [tableQueryLog_bind, tableQueryLog_pure, List.append_nil]
        exact ih hl
  exact key _ (List.mem_finRange c)

/-- **The grinding answers at a prefix computed without `H₂³` are bad with probability
`≤ 2⁻¹¹³`**, against the lazy random oracle of the game's world. -/
theorem prEvent_grindBad_le (pfx : OracleComp (ofFn (WB AR)) ByteArray)
    (hpfx : AllQueriesSatisfy pfx NoH23W) :
    Pr{let r ← (simulateQ randomOracle (pfx >>= blockW)).run' ∅}[GrindBad CrtGen.tables r] ≤
      (2 ^ 113 : ℝ≥0∞)⁻¹ := by
  classical
  set oa := pfx >>= blockW (AR := AR)
  let S := possibleQueryKeys oa
  have hS : AllQueriesSatisfy oa (· ∈ S) := allQueriesSatisfy_possibleQueryKeys oa
  rw [prEvent_eq_extendTable S oa hS]
  let Ω := (d : S) → WB AR d.val
  let _ : SampleableType Ω := IC.sampleSub (R := WB AR) S
  let preG : Ω → ByteArray := fun G => evalWithAnswerFn (QueryImpl.ofFn (extendTable S G)) pfx
  have hev_eq : ∀ G, evalWithAnswerFn (QueryImpl.ofFn (extendTable S G)) oa =
      fun c => (extendTable S G (gcell (preG G) c) : Bytes 16) := fun G => by
    simp only [oa, evalWithAnswerFn_bind, eval_blockW]
    rfl
  let ev : Ω → Prop := fun G => GrindBad CrtGen.tables (evalWithAnswerFn
    (QueryImpl.ofFn (extendTable S G)) oa)
  -- the cells of the block at an event table are in `S`
  have hcellS : ∀ G c, gcell (preG G) c ∈ S := fun G c => by
    have hl := mem_log_blockW (AR := AR) (extendTable S G) (preG G) c
    obtain ⟨e, he, hee⟩ := List.mem_map.1 hl
    have : e ∈ tableQueryLog oa (extendTable S G) := by
      simp only [oa, tableQueryLog_bind]
      exact List.mem_append_right _ he
    exact hee ▸ allQueriesSatisfy_tableQueryLog hS _ e this
  let t : Ω → Option S := fun G => some ⟨gcell (preG G) 0, hcellS G 0⟩
  -- updating the block keeps the prefix
  have hupd : ∀ G w, preG (upI S G (t G) w) = preG G := fun G w => by
    refine eval_congr_allQ hpfx fun x hx => ?_
    simp only [extendTable]
    split_ifs with hxS
    · show updW (preOf (gcell (preG G) 0)) w x (G ⟨x, hxS⟩) = G ⟨x, hxS⟩
      exact updW_ne _ _ _ hx _
    · rfl
  have hrd : ∀ G, rdI S G (t G) = evalWithAnswerFn (QueryImpl.ofFn (extendTable S G)) oa :=
    fun G => by
      rw [hev_eq]
      funext c
      show rdW S G (preOf (gcell (preG G) 0)) c = _
      rw [preOf_gcell]
      simp only [rdW, extendTable]
      rw [dite_eq_left (hcellS G c)]
      exact dite_eq_left (hcellS G c)
  have hnat := card_finOf_mul_le (Ω := Ω) (I := Option S) (W := Fin nGrind → Bytes 16) (upI S)
    (rdI S) (fun i => ∃ d, i = some d ∧ ∀ c, gcell (preOf d.val) c ∈ S) (upI_upI S) (upI_rdI S)
    (fun G i w ⟨d, hd, hv⟩ => by subst hd; exact rdI_upI S G d hv w) ev t
    (fun _ => finOf (GrindBad CrtGen.tables)) (#(finOf (GrindBad CrtGen.tables)))
    (fun G _ => ⟨_, rfl, fun c => by rw [show (⟨gcell (preG G) 0, hcellS G 0⟩ : S).val =
      gcell (preG G) 0 from rfl, preOf_gcell]; exact hcellS G c⟩)
    (fun G _ w => ⟨by simp only [t, hupd], rfl⟩) (fun _ _ => le_rfl)
    (fun G hG => by rw [hrd]; exact mem_finOf.2 hG)
  have hcardW : Fintype.card (Fin nGrind → Bytes 16) ≠ 0 := Fintype.card_ne_zero
  have hev' : Pr{let G ← $ᵗ Ω}[ev G] = (#(finOf ev) : ℝ≥0∞) / Fintype.card Ω := by
    rw [@SampleableType.prEvent_uniformSample _ _ _ ev (Classical.decPred ev), finOf_eq]
  show Pr{let G ← $ᵗ Ω}[ev G] ≤ _
  rw [hev']
  have hN0 : (Fintype.card Ω : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hNt : (Fintype.card Ω : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.div_le_iff hN0 hNt]
  -- the grinding bound, as a ratio of cardinalities
  have hg := grindBad_le_113
  unfold Privacy.pr at hg
  rw [← finOf_eq] at hg
  set K := #(finOf (GrindBad CrtGen.tables))
  set M := Fintype.card (Fin nGrind → Bytes 16)
  have hKM : (K : ℝ≥0∞) / M ≤ (2 ^ 113 : ℝ≥0∞)⁻¹ := by
    have hM0 : (0 : ℝ) < M := Nat.cast_pos.2 (Nat.pos_of_ne_zero hcardW)
    have hr : (K : ℝ) / M ≤ ((2 : ℝ) ^ 113)⁻¹ := by
      have := hg
      rw [one_div] at this
      exact this
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_div_of_pos hM0,
      show (2 ^ 113 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (((2 : ℝ) ^ 113)⁻¹) by
        rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp]
    exact ENNReal.ofReal_le_ofReal hr
  have hMt : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hM0' : (M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hcardW
  have hcast : (#(finOf ev) : ℝ≥0∞) * M ≤ K * Fintype.card Ω := by exact_mod_cast hnat
  calc (#(finOf ev) : ℝ≥0∞) = #(finOf ev) * M / M := by rw [ENNReal.mul_div_cancel_right hM0' hMt]
    _ ≤ K * Fintype.card Ω / M := ENNReal.div_le_div_right hcast _
    _ = K / M * Fintype.card Ω := by rw [ENNReal.mul_div_right_comm]
    _ ≤ (2 ^ 113 : ℝ≥0∞)⁻¹ * Fintype.card Ω := mul_le_mul_of_nonneg_right hKM (by simp)

end Bound

end VoleMole.Assumptions.BlindPomfrit
