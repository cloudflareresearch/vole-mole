import VoleMole.ROM.Accept
import VoleMole.ROM.CipherBind

/-!
# The soundness game with the ideal cipher (plan M6): `ε_bind` replaced

`ROM/Accept.lean` bounds the soundness game against the hash oracles, for any CTR PRG (`HasPrg`),
assuming a bound `ε_bind` on the binding failure `bindFail`. `ROM/CipherBind.lean` bounds the
binding failure of the BAVC reconstruction in the ideal-cipher model, for a prover that queries
the cipher and a *fixed* hash table. Here the two are joined.

* **The prover** `P : OracleComp specIC (ByteArray × β)` queries the hash oracles of
  `ROM/Basic.lean` and the cipher cells of `ROM/CipherBind.lean` (`specIC`, one random oracle on
  `Dom ⊕ Cell`), at most `q_E` times the cipher (`IsQueryBoundP P Sum.isRight q_E`) and `q k` times
  each hash domain `k` (`IsKindQueryBoundIC`).
* **The game at a cipher table `E`**: `proverIC st E P` is `P` with the cipher answered by `E`
  (`runE`, which also returns `P`'s cipher log) followed by the **straight-line extractor** (it
  queries `mu₁` and `iv`, and computes the leaf keys from the log, the table and the proof:
  `keysOf`, `knownOf`; the log is kept in `aux` for the events), and the verifier runs with the
  ideal-cipher PRG `icPrg E.cipher` (`game` of `ROM/Verifier.lean` at that instance). The
  experiment draws `E` uniformly, then runs the game against the lazy hash oracle.
* `runH h P`: `P` with the hashes answered by a fixed table `h`, a cipher-only prover;
  `evalWithAnswerFn_runE`: against `h`, `runE E P` returns `P`'s output against both tables and
  the log of `runH h P` against `E`.
* **`prEvent_joint_le_add`** (the bridge): if for every complete hash table `h` an event of the
  game has cipher probability `≤ c + ` that of another, the same holds in the joint experiment
  (the lazy hash oracle replaced by a uniform table on the finite set of the possible queries of
  all the games, `prEvent_randomOracle_eq_eager`, and the two draws swapped).
* **`prEvent_joint_bindFail_le`**: `Pr[bindFail] ≤ 2·q_E²·2⁻²⁵⁶ + Pr[DeadOpenOut]`, from
  `ROM/CipherBind.lean`'s `binds_or_coll_or_dead` and `prEvent_coll_le` at every hash table.
* **`prEvent_joint_le_of_bindFail`**: any bound of `ROM/Accept.lean` taken at each cipher table
  with `ε_bind := Pr[bindFail]` (`hbind := le_rfl`) holds in the joint experiment with that term
  replaced by `2·q_E²·2⁻²⁵⁶ + Pr[DeadOpenOut]`.
* **`moussakaIssue_accept_le_ic`**: `moussakaIssue_accept_le` in the joint experiment, with
  `ε_bind` replaced by `2·q_E²·2⁻²⁵⁶ + ε_open`, `ε_open` a bound on `DeadOpenOut` (an accepted
  proof opens a leaf whose key the prover never queried at that leaf's points). The other four
  relations' bounds go through `prEvent_joint_le_of_bindFail` in the same way (not stated here;
  the combined relations also need `P`'s total hash-query count transferred to `proverIC`).

What `ε_open` still contains (`L0-L2` §5): the linking of the verifier's leaf commitments to the
`H₁` preimages committed before the chain's `H₂¹` query (L1.4, `Coll₁`, `Hit₁`) and L2(a) (a
leaf with no key evaluated before the chain is not opened), both ordering facts about the hash
and cipher queries, as for the "same chain" step. `hsame` (the keys committed at the chain's
`H₂¹` input are the extractor's) and `hL2` stay as in `ROM/Accept.lean`.
-/

open Finset OracleComp OracleSpec
open MeasureTheory
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## The hash oracles and the cipher in one oracle -/

/-- A query of the combined oracle: a hash query or a cipher cell. -/
abbrev DomIC := Dom ⊕ Cell

/-- The answer of a combined query. -/
abbrev AnsIC : DomIC → Type := Sum.elim Ans fun _ => Blk

/-- **The hash oracles and the ideal cipher**, one random oracle on `Dom ⊕ Cell`. -/
abbrev specIC : OracleSpec DomIC := OracleSpec.ofFn AnsIC

/-- The complete combined table of a hash table and a cipher table. -/
def join (h : Table) (E : CTable) : ∀ d, AnsIC d
  | .inl d => h d
  | .inr x => E x

variable {α : Type}

/-- **`P` with the cipher answered by `E`**, returning `P`'s output and its cipher log. -/
def runE (E : CTable) (P : OracleComp specIC α) : OracleComp spec (α × QueryLog cspec) :=
  OracleComp.construct (C := fun _ => OracleComp spec (α × QueryLog cspec))
    (fun a => pure (a, []))
    (fun t _ rec => match t, rec with
      | .inl d, rec => liftM (spec.query d) >>= rec
      | .inr x, rec => (fun r => (r.1, ⟨x, E x⟩ :: r.2)) <$> rec (E x))
    P

/-- **`P` with the hashes answered by `h`**: a prover against the cipher only. -/
def runH (h : Table) (P : OracleComp specIC α) : OracleComp cspec α :=
  OracleComp.construct (C := fun _ => OracleComp cspec α)
    (fun a => pure a)
    (fun t _ rec => match t, rec with
      | .inl d, rec => rec (h d)
      | .inr x, rec => liftM (cspec.query x) >>= rec)
    P

@[simp] lemma runE_pure (E : CTable) (a : α) :
    runE E (pure a : OracleComp specIC α) = pure (a, []) := rfl

lemma runE_inl (E : CTable) (d : Dom) (k : specIC.Range (.inl d) → OracleComp specIC α) :
    runE E (liftM (specIC.query (.inl d)) >>= k) = liftM (spec.query d) >>= fun u => runE E (k u) :=
  rfl

lemma runE_inr (E : CTable) (x : Cell) (k : specIC.Range (.inr x) → OracleComp specIC α) :
    runE E (liftM (specIC.query (.inr x)) >>= k) =
      (fun r => (r.1, ⟨x, E x⟩ :: r.2)) <$> runE E (k (E x)) :=
  rfl

@[simp] lemma runH_pure (h : Table) (a : α) : runH h (pure a : OracleComp specIC α) = pure a := rfl

lemma runH_inl (h : Table) (d : Dom) (k : specIC.Range (.inl d) → OracleComp specIC α) :
    runH h (liftM (specIC.query (.inl d)) >>= k) = runH h (k (h d)) := rfl

lemma runH_inr (h : Table) (x : Cell) (k : specIC.Range (.inr x) → OracleComp specIC α) :
    runH h (liftM (specIC.query (.inr x)) >>= k) = liftM (cspec.query x) >>= fun u => runH h (k u) :=
  rfl

/-- **Against a hash table `h`, `runE E P` is `P` against both tables**, with the log of the
cipher-only prover `runH h P` against `E`. -/
theorem evalWithAnswerFn_runE (h : Table) (E : CTable) (P : OracleComp specIC α) :
    evalWithAnswerFn (QueryImpl.ofFn h) (runE E P) =
      (evalWithAnswerFn (QueryImpl.ofFn (join h E)) P, tableQueryLog (runH h P) E) := by
  induction P using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    cases t with
    | inl d =>
      rw [runE_inl, runH_inl]
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      exact ih (h d)
    | inr x =>
      rw [runE_inr, runH_inr]
      simp only [evalWithAnswerFn_map, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
        QueryImpl.ofFn_apply, tableQueryLog_query_bind]
      rw [ih (E x)]
      rfl

/-- Against `E`, the cipher-only prover `runH h P` is `P` against both tables. -/
theorem evalWithAnswerFn_runH (h : Table) (E : CTable) (P : OracleComp specIC α) :
    evalWithAnswerFn (QueryImpl.ofFn E) (runH h P) =
      evalWithAnswerFn (QueryImpl.ofFn (join h E)) P := by
  induction P using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    cases t with
    | inl d =>
      rw [runH_inl]
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      exact ih (h d)
    | inr x =>
      rw [runH_inr]
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      exact ih (E x)

/-! ## Query bounds -/

/-- **At most `q k` queries to each hash domain `k`** (cipher queries are free here). -/
def IsKindQueryBoundIC (P : OracleComp specIC α) (q : Kind → ℕ) : Prop :=
  IsQueryBound P q (fun t b => match t with | .inl d => 0 < b d.1 | .inr _ => True)
    (fun t b => match t with | .inl d => Function.update b d.1 (b d.1 - 1) | .inr _ => b)

/-- The hash queries of `runE E P` are `P`'s. -/
theorem isKindQueryBound_runE (E : CTable) {P : OracleComp specIC α} {q : Kind → ℕ}
    (hP : IsKindQueryBoundIC P q) : IsKindQueryBound (runE E P) q := by
  induction P using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [IsKindQueryBoundIC, isQueryBound_query_bind_iff] at hP
    cases t with
    | inl d =>
      rw [runE_inl]
      exact isKindQueryBound_query_bind_iff.2 ⟨hP.1, fun u => ih u (hP.2 u)⟩
    | inr x =>
      rw [runE_inr]
      exact (isQueryBound_map_iff _ _ _ _ _).2 (ih (E x) (hP.2 (E x)))

/-- The cipher queries of `runH h P` are `P`'s. -/
theorem isTotalQueryBound_runH (h : Table) {P : OracleComp specIC α} {n : ℕ}
    (hP : IsQueryBoundP P (fun t => t.isRight = true) n) : IsTotalQueryBound (runH h P) n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hP
    cases t with
    | inl d =>
      rw [runH_inl]
      simpa using ih (h d) (hP.2 (h d))
    | inr x =>
      rw [runH_inr]
      simp only [Sum.isRight_inr, not_true_eq_false, false_or, ite_true] at hP
      exact isTotalQueryBound_query_bind_iff.2 ⟨hP.1, fun u => ih u (hP.2 u)⟩

/-! ## The lazy hash oracle as a uniform table, and the two draws swapped -/

section Eager

variable {X : Type}

/-- **The lazy random oracle is a uniform table** on a finite set `S` of keys containing every
possible query (VCVio's restriction to `S`, then its eager form). -/
theorem prEvent_randomOracle_eq_eager (oa : OracleComp spec X) (S : Finset Dom)
    (hS : AllQueriesSatisfy oa (· ∈ S)) [SampleableType ((d : S) → Ans d.val)] (p : X → Prop) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[p r] =
      Pr{let g ← $ᵗ ((d : S) → Ans d.val)}[
        p (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) oa)] := by
  classical
  let small := restrictQueries S oa hS
  have hrun : (simulateQ randomOracle small).run' ∅ = (simulateQ randomOracle oa).run' ∅ :=
    randomOracle_restrictQueries S oa hS ∅
  rw [← hrun]
  let : MeasurableSpace X := ⊤
  have heager := evalDist_simulateQ_randomOracle_run'_eq_completeTable small ∅
  simp only [completeTable_empty] at heager
  rw [(EvalDistEq.of_evalDist_eq heager).prEvent_eq p]
  have key : ∀ g : (d : S) → Ans d.val, evalWithAnswerFn (QueryImpl.ofFn g) small =
      evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) oa := fun g => by
    have hrestrict : (fun d : S => extendTable S g d.val) = g :=
      funext fun d => extendTable_subtype S g d
    have := evalWithAnswerFn_restrictQueries S oa hS (extendTable S g)
    rwa [hrestrict] at this
  simp only [prEvent_norm, key]

/-- One finite key set contains the possible queries of all the computations of a family indexed
by cipher tables. -/
lemma exists_allQueriesSatisfy (m : CTable → OracleComp spec X) :
    ∃ S : Finset Dom, ∀ E, AllQueriesSatisfy (m E) (· ∈ S) := by
  have hfin : (⋃ E, (possibleQueryKeys (m E) : Set Dom)).Finite :=
    Set.finite_iUnion fun E => (possibleQueryKeys (m E)).finite_toSet
  refine ⟨hfin.toFinset, fun E => (allQueriesSatisfy_possibleQueryKeys (m E)).mono fun d hd => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_iUnion]
  exact ⟨E, hd⟩

/-- **The bridge between the joint experiment and a fixed hash table.** The cipher table `E` is
drawn uniformly, then the game `m E` runs against the lazy hash oracle. If, for every complete
hash table `g`, the event `ev` has cipher probability at most `c` plus that of `ev'`, the same
holds in the joint experiment. (The hash oracle becomes a uniform table on the finite set of the
possible queries of all the games `m E`, and the two draws are swapped.) -/
theorem prEvent_joint_le_add (m : CTable → OracleComp spec X) (ev ev' : CTable → X → Prop)
    (c : ℝ≥0∞)
    (h : ∀ g : Table, Pr{let E ← $ᵗ CTable}[ev E (evalWithAnswerFn (QueryImpl.ofFn g) (m E))] ≤
      c + Pr{let E ← $ᵗ CTable}[ev' E (evalWithAnswerFn (QueryImpl.ofFn g) (m E))]) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m E)).run' ∅}[ev E r] ≤
      c + Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m E)).run' ∅}[ev' E r] := by
  classical
  obtain ⟨S, hS⟩ := exists_allQueriesSatisfy m
  let _ : ∀ d : S, Fintype (Ans d.val) := fun _ => inferInstance
  let _ : SampleableType ((d : S) → Ans d.val) := SampleableType.ofFintype _
  let : MeasurableSpace CTable := ⊤
  let : MeasurableSpace ((d : S) → Ans d.val) := ⊤
  have hjoint : ∀ p : CTable → X → Prop,
      Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m E)).run' ∅}[p E r] =
        ∫⁻ g, Pr{let E ← $ᵗ CTable}[
          p E (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m E))]
          ∂𝒟[$ᵗ ((d : S) → Ans d.val)] := by
    intro p
    calc Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (m E)).run' ∅}[p E r]
        = ∫⁻ E, Pr{let r ← (simulateQ randomOracle (m E)).run' ∅}[p E r] ∂𝒟[$ᵗ CTable] :=
          prEvent_bind_of_discrete _ _
      _ = ∫⁻ E, Pr{let g ← $ᵗ ((d : S) → Ans d.val)}[
            p E (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m E))] ∂𝒟[$ᵗ CTable] :=
          lintegral_congr fun E => prEvent_randomOracle_eq_eager (m E) S (hS E) (p E)
      _ = Pr{let E ← $ᵗ CTable; let g ← $ᵗ ((d : S) → Ans d.val)}[
            p E (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m E))] :=
          (prEvent_bind_of_discrete _ _).symm
      _ = Pr{let g ← $ᵗ ((d : S) → Ans d.val); let E ← $ᵗ CTable}[
            p E (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m E))] :=
          prEvent_bind_map_swap _ _ _
      _ = _ := prEvent_bind_of_discrete _ _
  rw [hjoint ev, hjoint ev']
  calc ∫⁻ g, Pr{let E ← $ᵗ CTable}[
          ev E (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m E))]
          ∂𝒟[$ᵗ ((d : S) → Ans d.val)]
      ≤ ∫⁻ g, (c + Pr{let E ← $ᵗ CTable}[
          ev' E (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m E))])
          ∂𝒟[$ᵗ ((d : S) → Ans d.val)] := lintegral_mono fun g => h (extendTable S g)
    _ = c * 𝒟[$ᵗ ((d : S) → Ans d.val)] Set.univ + ∫⁻ g, Pr{let E ← $ᵗ CTable}[
          ev' E (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) (m E))]
          ∂𝒟[$ᵗ ((d : S) → Ans d.val)] := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ _ := add_le_add (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)) le_rfl

/-- **Averaging over the cipher table**: a bound for every cipher table holds on average. -/
theorem prEvent_avg_le_add (m : CTable → ProbComp X) (ev ev' : CTable → X → Prop) (c : ℝ≥0∞)
    (h : ∀ E, Pr{let r ← m E}[ev E r] ≤ c + Pr{let r ← m E}[ev' E r]) :
    Pr{let E ← $ᵗ CTable; let r ← m E}[ev E r] ≤ c + Pr{let E ← $ᵗ CTable; let r ← m E}[ev' E r] := by
  let : MeasurableSpace CTable := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  calc ∫⁻ E, Pr{let r ← m E}[ev E r] ∂𝒟[$ᵗ CTable]
      ≤ ∫⁻ E, (c + Pr{let r ← m E}[ev' E r]) ∂𝒟[$ᵗ CTable] := lintegral_mono h
    _ = c * 𝒟[$ᵗ CTable] Set.univ + ∫⁻ E, Pr{let r ← m E}[ev' E r] ∂𝒟[$ᵗ CTable] := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ _ := add_le_add (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)) le_rfl

end Eager

/-! ## The prover with the straight-line extractor, and the game -/

section Game

variable {β : Type}

/-- The trees whose hidden leaf has a logged witness: the extractor's known trees (`L0-L2` §6). -/
def knownOf (log : QueryLog cspec) (E : CTable) (iv opening : ByteArray) : Finset (Fin BAVC.tau) :=
  univ.filter fun i => (extractKey log E iv i (opening.extract (32 * i) (32 * i + 32))).isSome

/-- **The prover `P` with the straight-line extractor, at the cipher table `E`**: `P` with the
cipher answered by `E` (and its cipher log), then the extractor queries `mu₁` and `iv` and computes
the leaf keys (`keysOf`) and the known trees (`knownOf`) from the log, `E` and the proof. The log
is kept in `aux`. -/
def proverIC (st : Statement) (E : CTable) (P : OracleComp specIC (ByteArray × β)) :
    OracleComp spec (ByteArray × ExtData (β × QueryLog cspec)) := do
  let r ← runE E P
  let pf : Proof := { params := st.params, bytes := r.1.1 }
  let mu1 ← mu1Q st
  let iv ← hashQ .h4 ((pf.ivPre ++ mu1).push 4)
  pure (r.1.1,
    { keys := keysOf r.2 E iv pf.opening pf.delta
      known := knownOf r.2 E iv pf.opening
      aux := (r.1.2, r.2) })

/-- **The game at the cipher table `E`**: `proverIC`, then the verifier with the ideal-cipher PRG
`icPrg E.cipher`, against the hash oracles. -/
def gameIC (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β)) (E : CTable) :
    OracleComp spec (Out (β × QueryLog cspec)) :=
  @game (icPrg E.cipher) _ T st (proverIC st E P)

/-- The extractor's queries: `mu₁` (`H₂⁰` or `H₂⁴`) and `iv` (`H₄`). -/
def extractorQueries : Kind → ℕ := fun k => if k = .h4 ∨ k = .mu ∨ k = .muDelayed then 1 else 0

/-- **The hash queries of `proverIC`**: `P`'s and the extractor's two. -/
theorem isKindQueryBound_proverIC (st : Statement) (E : CTable) {P : OracleComp specIC (ByteArray × β)}
    {q : Kind → ℕ} (hq : IsKindQueryBoundIC P q) :
    IsKindQueryBound (proverIC st E P) (q + extractorQueries) := by
  unfold proverIC
  refine isKindQueryBound_bind (isKindQueryBound_runE E hq) fun r => ?_
  have h4 : ∀ k : Kind, k ≠ .h4 → ∀ mu1 : ByteArray,
      IsKindQueryBound (hashQ .h4 ((Proof.ivPre ⟨st.params, r.1.1⟩ ++ mu1).push 4) >>= fun iv =>
        (pure (r.1.1,
          { keys := keysOf r.2 E iv (Proof.opening ⟨st.params, r.1.1⟩)
              (Proof.delta ⟨st.params, r.1.1⟩)
            known := knownOf r.2 E iv (Proof.opening ⟨st.params, r.1.1⟩)
            aux := (r.1.2, r.2) }) :
          OracleComp spec (ByteArray × ExtData (β × QueryLog cspec))))
        (Function.update extractorQueries k (extractorQueries k - 1)) := by
    intro k hk mu1
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨?_, fun _ => trivial⟩
    rw [Function.update_of_ne (Ne.symm hk)]
    simp [extractorQueries]
  unfold mu1Q
  split
  · exact isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [extractorQueries], fun u =>
      h4 .muDelayed (by decide) u.ba⟩
  · exact isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [extractorQueries], fun u =>
      h4 .mu (by decide) u.ba⟩

/-- Against a hash table `h`, the extractor's data are computed from `P`'s output against both
tables, the cipher log of `runH h P` and the verifier's `iv`. -/
theorem evalWithAnswerFn_proverIC (h : Table) (st : Statement) (E : CTable)
    (P : OracleComp specIC (ByteArray × β)) :
    let r := evalWithAnswerFn (QueryImpl.ofFn (join h E)) P
    let log := tableQueryLog (runH h P) E
    let pf : Proof := { params := st.params, bytes := r.1 }
    let iv := ivOf (Hashes.ofTable h) pf (st.mu1 (Hashes.ofTable h))
    evalWithAnswerFn (QueryImpl.ofFn h) (proverIC st E P) =
      (r.1,
        { keys := keysOf log E iv pf.opening pf.delta
          known := knownOf log E iv pf.opening
          aux := (r.2, log) }) := by
  simp only [proverIC, evalWithAnswerFn_bind, evalWithAnswerFn_runE, evalWithAnswerFn_mu1Q,
    evalWithAnswerFn_hashQ, evalWithAnswerFn_pure, ivOf, Hashes.ofTable_hash]

/-- **A dead leaf is opened by an accepted proof**: the verifier accepts, and some non-hidden leaf
key of its reconstruction was queried by the prover at neither of that leaf's points. -/
def DeadOpenOut (st : Statement) (E : CTable) (r : Out (β × QueryLog cspec)) : Prop :=
  r.2.2.accept = true ∧ DeadOpen r.2.1.aux.2 E r.2.2.iv (Proof.opening ⟨st.params, r.1⟩)
    (Proof.delta ⟨st.params, r.1⟩)

/-- **The binding failure for a fixed hash table**: over the cipher table, the binding failure
of the game has probability at most `2·q_E²·2⁻²⁵⁶` plus that of an opened dead leaf. -/
theorem pr_bindFail_le_table (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (h : Table) :
    Pr{let E ← $ᵗ CTable}[@bindFail (icPrg E.cipher) _ st
        (evalWithAnswerFn (QueryImpl.ofFn h) (gameIC T st P E))] ≤
      2 * qE ^ 2 * (2 ^ 256)⁻¹ + Pr{let E ← $ᵗ CTable}[DeadOpenOut st E
        (evalWithAnswerFn (QueryImpl.ofFn h) (gameIC T st P E))] := by
  have hn := isTotalQueryBound_runH h hqE
  have hpt : ∀ E : CTable, @bindFail (icPrg E.cipher) _ st
      (evalWithAnswerFn (QueryImpl.ofFn h) (gameIC T st P E)) →
      freshBadC (runH h P) ∅ E collBad ∨
        DeadOpenOut st E (evalWithAnswerFn (QueryImpl.ofFn h) (gameIC T st P E)) := by
    intro E hb
    let _ : HasPrg := icPrg E.cipher
    obtain ⟨hacc, hnb⟩ := hb
    simp only [gameIC, evalWithAnswerFn_game, evalWithAnswerFn_proverIC] at hacc hnb ⊢
    set π := (evalWithAnswerFn (QueryImpl.ofFn (join h E)) P).1
    obtain ⟨-, leaves, hr, -⟩ := (accept_iff _ T st π).1 hacc
    obtain ⟨hiv, -⟩ := verify_iv_chal1 _ T st π hacc hr
    rcases binds_or_coll_or_dead (runH h P) E (ivOf (Hashes.ofTable h) ⟨st.params, π⟩
        (st.mu1 (Hashes.ofTable h))) (Proof.opening ⟨st.params, π⟩)
        (Proof.delta ⟨st.params, π⟩) with hB | hC | hD
    · exact absurd (fun leaves' hr' => hB leaves' (hiv ▸ hr')) hnb
    · exact Or.inl hC
    · exact Or.inr ⟨hacc, by rw [hiv]; exact hD⟩
  refine (prEvent_mono _ _ (fun E => freshBadC (runH h P) ∅ E collBad ∨
    DeadOpenOut st E (evalWithAnswerFn (QueryImpl.ofFn h) (gameIC T st P E))) hpt).trans
    ((prEvent_or_le _ _ _).trans (add_le_add ?_ le_rfl))
  exact prEvent_coll_le (runH h P) qE hn (fun E => freshBadC (runH h P) ∅ E collBad) fun _ h => h

/-- **The binding failure in the joint experiment** (the cipher table drawn uniformly, then the
game against the lazy hash oracle): at most `2·q_E²·2⁻²⁵⁶` plus the probability that an accepted
proof opens a dead leaf. -/
theorem prEvent_joint_bindFail_le (T : CrtTables) (st : Statement)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[
        @bindFail (icPrg E.cipher) _ st r] ≤
      2 * qE ^ 2 * (2 ^ 256)⁻¹ +
        Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[
          DeadOpenOut st E r] :=
  prEvent_joint_le_add (gameIC T st P) (fun E r => @bindFail (icPrg E.cipher) _ st r)
    (fun E r => DeadOpenOut st E r) _ (pr_bindFail_le_table T st P qE hqE)


/-- **Any per-table bound with `ε_bind = Pr[bindFail]` holds in the joint experiment with the
binding term made explicit**: if for every cipher table `E` the event `ev` of the game has
probability at most `c` plus that of `bindFail` (`ROM/Accept.lean`'s bounds, with `hbind := le_rfl`),
then in the joint experiment `Pr[ev] ≤ c + 2·q_E²·2⁻²⁵⁶ + Pr[DeadOpenOut]`. -/
theorem prEvent_joint_le_of_bindFail (T : CrtTables) (st : Statement)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE)
    (ev : CTable → Out (β × QueryLog cspec) → Prop) (c : ℝ≥0∞)
    (h : ∀ E, Pr{let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[ev E r] ≤
      c + Pr{let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[
        @bindFail (icPrg E.cipher) _ st r]) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[ev E r] ≤
      c + (2 * qE ^ 2 * (2 ^ 256)⁻¹ +
        Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[
          DeadOpenOut st E r]) :=
  (prEvent_avg_le_add _ _ _ _ h).trans
    (add_le_add le_rfl (prEvent_joint_bindFail_le T st P qE hqE))

/-! ## Moussaka issuance in the ideal-cipher model -/

/-- **Moussaka issuance in the random-oracle and ideal-cipher model**: the cipher table `E` drawn
uniformly, the prover `P` (at most `q_E` cipher queries, `q k` queries to each hash domain `k`) with
the straight-line extractor of `proverIC`, the executable verifier with the ideal cipher; the
verifier accepts and the extractor's candidate is not an issuance witness with probability

    ≤ (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·ε_QS(4008) + (Q+1)·9·2⁻¹²⁸ + 2·q_E²·2⁻²⁵⁶ + ε_open + ε_dead + ε_chain,

`moussakaIssue_accept_le` with `ε_bind` replaced by `2·q_E²·2⁻²⁵⁶ + ε_open`, where `ε_open` bounds
`DeadOpenOut` (an accepted proof opening a leaf whose key `P` never queried at that leaf's
points). The other assumptions are those of `moussakaIssue_accept_le`, for every cipher table
(the committed chain data may depend on it). -/
theorem moussakaIssue_accept_le_ic (t ctxIss : ByteArray) (labelRows : Bool)
    (preOf midOf : CTable → ByteArray → Table → Chain)
    (accOf : CTable → ByteArray → Table → Prob.Bytes 16 → Prop)
    (hC : ∀ E, (ChainData.ofSys (st := moussakaIssue t ctxIss labelRows) (preOf E) (midOf E)
      (moussakaIssueSys t ctxIss) (accOf E)).Committed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q)
    (chainFail deadFail : CTable → Out (β × QueryLog cspec) → Prop) {εo εd εs : ℝ≥0∞}
    (hopen : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaIssue t ctxIss labelRows) P E)).run' ∅}[
        DeadOpenOut (moussakaIssue t ctxIss labelRows) E r] ≤ εo)
    (hdead : ∀ E, Pr{let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaIssue t ctxIss labelRows) P E)).run' ∅}[deadFail E r] ≤ εd)
    (hchain : ∀ E, Pr{let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaIssue t ctxIss labelRows) P E)).run' ∅}[chainFail E r] ≤ εs)
    (hsame : ∀ (E : CTable) (g : Table), let _ : HasPrg := icPrg E.cipher
      let st := moussakaIssue t ctxIss labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC CrtGen.tables st P E)
      r.2.2.accept = true → ¬chainFail E r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      let ch := runChain (Hashes.ofTable g) CrtGen.tables st r.1 leaves r.2.1.keys
      SameChain st CrtGen.tables (preOf E) (midOf E) (accOf E) g ch
        (runX (Hashes.ofTable g) st r.1 leaves) (runY (Hashes.ofTable g) st ch) (runZ st ch))
    (hL2 : ∀ (E : CTable) (g : Table), let _ : HasPrg := icPrg E.cipher
      let st := moussakaIssue t ctxIss labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC CrtGen.tables st P E)
      r.2.2.accept = true → ¬chainFail E r → ¬deadFail E r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      ∀ i ∉ r.2.1.known, IsFixed ((onSet st CrtGen.tables (runChain (Hashes.ofTable g)
        CrtGen.tables st r.1 leaves r.2.1.keys) chal3Blocks : Finset Blocks) : Set Blocks) i) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaIssue t ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (moussakaIssue t ctxIss labelRows)
          (fun _ => moussakaIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + (2 * qE ^ 2 * (2 ^ 256)⁻¹ + εo) + εd + εs := by
  classical
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128)
  -- For each cipher table, `moussakaIssue_accept_le` with `ε_bind` the game's own `Pr[bindFail]`.
  have hE : ∀ E : CTable, Pr{let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaIssue t ctxIss labelRows) P E)).run' ∅}[
      r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (moussakaIssue t ctxIss labelRows)
        (fun _ => moussakaIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)) r] ≤
      (A + εd + εs) + Pr{let r ← (simulateQ randomOracle
        (gameIC CrtGen.tables (moussakaIssue t ctxIss labelRows) P E)).run' ∅}[
        @bindFail (icPrg E.cipher) _ (moussakaIssue t ctxIss labelRows) r] := by
    intro E
    have h := @moussakaIssue_accept_le (icPrg E.cipher) _ t ctxIss labelRows (preOf E) (midOf E)
      (accOf E) (hC E) (proverIC (moussakaIssue t ctxIss labelRows) E P) (q + extractorQueries)
      (isKindQueryBound_proverIC _ E hq) (chainFail E) (deadFail E) _ _ _ le_rfl (hdead E)
      (hchain E) (hsame E) (hL2 E)
    simp only [gameIC]
    refine h.trans (le_of_eq ?_)
    simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero]
    ring
  calc _ ≤ _ := prEvent_joint_le_of_bindFail CrtGen.tables _ P qE hqE _ _ hE
    _ ≤ (A + εd + εs) + (2 * qE ^ 2 * (2 ^ 256)⁻¹ + εo) :=
        add_le_add le_rfl (add_le_add le_rfl hopen)
    _ = _ := by ring

end Game

end VoleMole.ROM.IC
