import VoleMole.Theft.PlainPerm
import VoleMole.Theft.PlainVerQ

/-!
# The theft tables with permutation rows and `ROM/`'s permutation-model experiment

`Theft/PlainEager.lean` relates the theft tables with function rows to `ROM/`'s experiment (a
uniform cipher table, then the lazy random oracle). Here the same with **permutation rows**:
`ROM/`'s permutation-model bounds (`ROM/SimPermJoint*.lean`) draw a uniform permutation table
`π : PTable`, run the prover through the joint normalization `normJ p_I p_R π` (inverse queries
recorded as forward ones, `H₄` queries of the `iv` added), and let the straight-line extractor
read the normalized cipher log.

* `tabEquivP`: the slices and the tables are a table on the table points and a permutation table.
* **`pr_tables_eq_roP`**: for computations that query only table points, an event's probability on
  the tables is its probability in `ROM/`'s permutation-model experiment.
* `size_ivIn`, `allQ_normJ`: the normalization's `H₄` queries are table points when `L ≥ 49`, so
  the normalized adversary queries only table points (`OnT`).
* `toIC π`: a forward or inverse query as the cipher cell it determines (`(k, π_k⁻¹(y))` for an
  inverse query), and **`cLog_normJ`**: the cipher log of the normalized run is the list of those
  cells (`cLog`), so the extractor can compute it from the adversary's queries and the table.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## The slices and the tables as one table on the table points and a permutation table -/

section Equiv

variable {p : Params} {L M : ℕ}

/-- **The slices and the tables are a table on the table points and a permutation table.** -/
def tabEquivP : (Tab3 × Tab3) × ShX (Equiv.Perm Blk) p (XTab L M) ≃
    ((k : TK p L) → Ans (tpt p L M k)) × PTable where
  toFun z := (tabOf z.1.1 z.1.2 z.2, z.2.2.1.2)
  invFun y := ((fun k => y.1 (.inl (false, k)), fun k => y.1 (.inl (true, k))),
    (fun a => y.1 (.inr (.inl a)), ((fun a => y.1 (.inr (.inr (.inl a))), y.2),
      (fun a => y.1 (.inr (.inr (.inr (.inl a)))),
        fun a => y.1 (.inr (.inr (.inr (.inr (.inl a))))),
        fun a => y.1 (.inr (.inr (.inr (.inr (.inr (.inl a)))))),
        fun a => y.1 (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))),
        fun a => y.1 (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))))),
        fun a => y.1 (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))))),
        fun a => y.1 (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr a)))))))))))))
  left_inv z := rfl
  right_inv y := by
    refine Prod.ext (funext fun k => ?_) rfl
    rcases k with ⟨b, a⟩ | a | a | a | a | a | a | a | a | a
    · cases b <;> rfl
    all_goals rfl

end Equiv

/-! ## The tables and the lazy random oracle, permutation model -/

section Bridge

variable {p : Params} {L M : ℕ} {X : Type}

set_option maxRecDepth 100000 in
/-- **The joint experiment as a uniform permutation table and a uniform table on `S`**, for
computations that query only keys of `S`. -/
theorem prEvent_jointP_eq_prU (S : Finset Dom) (m : PTable → OracleComp spec X)
    (hS : ∀ π, AllQueriesSatisfy (m π) (· ∈ S)) (ev : PTable → X → Prop)
    [SampleableType ((d : S) → Ans d.val)] :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (m π)).run' ∅}[ev π r] =
      Prob.prU (PTable × ((d : S) → Ans d.val)) fun z =>
        ev z.1 (evalWithAnswerFn (QueryImpl.ofFn (extendTable S z.2)) (m z.1)) := by
  have h := prEvent_uniform_bind_eq (A := PTable) (B := (d : S) → Ans d.val) fun π g =>
    ev π (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m π))
  rw [← h]
  let : MeasurableSpace PTable := ⊤
  calc Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (m π)).run' ∅}[ev π r]
      = ∫⁻ π, Pr{let r ← (simulateQ randomOracle (m π)).run' ∅}[ev π r] ∂𝒟[$ᵗ PTable] :=
        prEvent_bind_of_discrete _ _
    _ = ∫⁻ π, Pr{let g ← $ᵗ ((d : S) → Ans d.val)}[
          ev π (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m π))] ∂𝒟[$ᵗ PTable] :=
        MeasureTheory.lintegral_congr fun π => prEvent_randomOracle_eq_eager (m π) S (hS π) (ev π)
    _ = _ := (prEvent_bind_of_discrete _ _).symm

set_option maxRecDepth 10000 in
/-- **The tables with permutation rows are `ROM/`'s permutation-model experiment.** For
computations `m π` against the hash oracles that query only table points, an event's probability
on uniform slices and tables (`tabP`, SHAKE elsewhere; the permutation table `t.2.1.2`) is its
probability with a uniform permutation table and the lazy random oracle. -/
theorem pr_tables_eq_roP (m : PTable → OracleComp spec X)
    (hm : ∀ π, AllQueriesSatisfy (m π) (· ∈ TPts p L M)) (ev : PTable → X → Prop) :
    pr ((Tab3 × Tab3) × ShX (Equiv.Perm Blk) p (XTab L M)) (fun z =>
        ev z.2.2.1.2 (runT (tabP z.1.1 z.1.2 z.2) (m z.2.2.1.2))) =
      (Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (m π)).run' ∅}[ev π r]).toReal := by
  classical
  let : SampleableType ((d : TPts p L M) → Ans d.val) := SampleableType.ofFintype _
  rw [prEvent_jointP_eq_prU _ m hm ev, pr_eq_toReal_prU]
  congr 1
  let e : (Tab3 × Tab3) × ShX (Equiv.Perm Blk) p (XTab L M) ≃
      PTable × ((d : TPts p L M) → Ans d.val) :=
    tabEquivP.trans ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (ptsEquiv p L M)))
  rw [Prob.prU_map_equiv e]
  refine Prob.prU_congr fun z => ?_
  show _ ↔ ev z.2.2.1.2 (evalWithAnswerFn (QueryImpl.ofFn (extendTable (TPts p L M)
    (ptsEquiv p L M (tabOf z.1.1 z.1.2 z.2)))) (m z.2.2.1.2))
  rw [← runT_eq_eval]
  refine iff_of_eq (congrArg _ (runT_congr_of_allQueries _ _ (hm _) _ _ fun d hd => ?_))
  obtain ⟨k, rfl⟩ := (mem_TPts p L M).1 hd
  rw [tabP_tpt]
  have h := extendTable_subtype (TPts p L M) (ptsEquiv p L M (tabOf z.1.1 z.1.2 z.2))
    (tptEquiv p L M k)
  rw [ptsEquiv_tpt] at h
  exact h.symm

end Bridge

/-! ## The normalization's queries are table points -/

section OnT

variable {p : Params} {L M : ℕ} {α : Type}

/-- The `H₄` input of an `H₂¹` input has at most 49 bytes. -/
lemma size_ivIn (p' : Params) (x : ByteArray) : (ivIn p' x).size ≤ 49 := by
  simp only [ivIn, xIvPre, ByteArray.size_push, ByteArray.size_append, ByteArray.size_extract]
  omega

lemma ivIn_mem (hL : 49 ≤ L) (p' : Params) (x : ByteArray) :
    ((.h4, ivIn p' x) : Dom) ∈ TPts p L M :=
  mem_TPts_encL (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) ((size_ivIn p' x).trans hL)

/-- Adding the `iv` queries keeps the queries at table points. -/
theorem allQ_addIV (hL : 49 ≤ L) (p' : Params) {P : OracleComp specP α}
    (hP : AllQueriesSatisfy P (OnTQ p L M)) : AllQueriesSatisfy (addIV p' P) (OnTQ p L M) := by
  induction P using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).1 hP
    rcases t with d | c
    · rw [addIV_inl]
      split
      · exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨ivIn_mem hL p' d.2, fun _ =>
          (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨ht, fun u => ih u (hk u)⟩⟩
      · exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨ht, fun u => ih u (hk u)⟩
    · rw [addIV_inr]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨trivial, fun u => ih u (hk u)⟩

/-- The forward normalization keeps the queries at table points. -/
theorem allQ_normP (hL : 49 ≤ L) (p' : Params) (π : PTable) {P : OracleComp specP α}
    (hP : AllQueriesSatisfy P (OnTQ p L M)) : AllQueriesSatisfy (normP p' π P) (OnT p L M) := by
  induction P using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).1 hP
    rcases t with d | ⟨b, c⟩
    · rw [normP_inl]
      split
      · exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨ivIn_mem hL p' d.2, fun _ =>
          (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨ht, fun u => ih u (hk u)⟩⟩
      · exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨ht, fun u => ih u (hk u)⟩
    · cases b
      · rw [normP_inv]
        exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨trivial, fun _ => ih _ (hk _)⟩
      · rw [normP_fwd]
        exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨trivial, fun u => ih u (hk u)⟩

/-- **The joint normalization of a computation at table points queries table points.** -/
theorem allQ_normJ (hL : 49 ≤ L) (pI pR : Params) (π : PTable) {P : OracleComp specP α}
    (hP : AllQueriesSatisfy P (OnTQ p L M)) :
    AllQueriesSatisfy (normJ pI pR π P) (OnT p L M) :=
  allQ_normP hL pI π (allQ_addIV hL pR hP)

end OnT

/-! ## The cipher log of the normalized run -/

section Log

variable {α : Type}

/-- **The cell a query determines**: a hash query is kept; a forward query `(k, z)` is the cell
`(k, z)`, an inverse query `(k, y)` the cell `(k, π_k⁻¹(y))`. -/
def toIC (π : PTable) : DomP → DomIC
  | .inl d => .inl d
  | .inr (true, c) => .inr c
  | .inr (false, c) => .inr (c.1, (π c.1).symm c.2)

lemma cLog_inl (E : CTable) (d : Dom) (l : List DomIC) : cLog E (.inl d :: l) = cLog E l := rfl

lemma cLog_inr (E : CTable) (c : Cell) (l : List DomIC) :
    cLog E (.inr c :: l) = ⟨c, E c⟩ :: cLog E l := rfl

/-- The cipher log of the forward normalization: the cells of the queries. -/
theorem cLog_normP (p : Params) (π : PTable) (h : Table) (P : OracleComp specP α) :
    cLog π.fwd (qlog (join h π.fwd) (normP p π P)) =
      cLog π.fwd ((qlog (joinP h π) P).map (toIC π)) := by
  induction P using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with d | ⟨b, c⟩
    · rw [normP_inl, qlog_query_bind, List.map_cons]
      split
      · rw [qlog_query_bind, qlog_query_bind]
        exact (ih _)
      · rw [qlog_query_bind]
        exact (ih _)
    · cases b
      · rw [normP_inv, qlog_query_bind, qlog_query_bind, List.map_cons]
        exact congrArg (List.cons _) (ih _)
      · rw [normP_fwd, qlog_query_bind, qlog_query_bind, List.map_cons]
        exact congrArg (List.cons _) (ih _)

/-- Adding the `iv` queries does not change the cells of the queries. -/
theorem cLog_addIV (p : Params) (π : PTable) (f : (d : DomP) → AnsP d) (P : OracleComp specP α) :
    cLog π.fwd ((qlog f (addIV p P)).map (toIC π)) = cLog π.fwd ((qlog f P).map (toIC π)) := by
  induction P using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with d | c
    · rw [addIV_inl, qlog_query_bind]
      split
      · rw [qlog_query_bind, qlog_query_bind]
        exact ih _
      · rw [qlog_query_bind]
        exact ih _
    · rw [addIV_inr, qlog_query_bind, qlog_query_bind, List.map_cons, List.map_cons]
      rcases c with ⟨b, c⟩
      cases b
      · exact congrArg (List.cons _) (ih _)
      · exact congrArg (List.cons _) (ih _)

/-- **The cipher log of the joint normalization's run is the list of the cells of the queries.** -/
theorem cLog_normJ (pI pR : Params) (π : PTable) (h : Table) (P : OracleComp specP α) :
    cLog π.fwd (qlog (join h π.fwd) (normJ pI pR π P)) =
      cLog π.fwd ((qlog (joinP h π) P).map (toIC π)) :=
  (cLog_normP pI π h (addIV pR P)).trans (cLog_addIV pR π _ P)

/-- Hash queries do not enter the cipher log. -/
lemma cLog_map_filter (π : PTable) (P : DomP → Bool) (hP : ∀ c, P (.inr c) = true)
    (l : List DomP) : cLog π.fwd ((l.filter P).map (toIC π)) = cLog π.fwd (l.map (toIC π)) := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rcases d with d | c
    · by_cases h : P (.inl d) = true
      · rw [List.filter_cons_of_pos h]; exact ih
      · rw [List.filter_cons_of_neg h]; exact ih
    · rw [List.filter_cons_of_pos (hP c), List.map_cons, List.map_cons]
      rcases c with ⟨b, c⟩
      cases b <;> exact congrArg (List.cons _) ih

end Log

end VoleMole.Theft
