import VoleMole.ROM.AdaptGame

/-!
# Extract, then reduce: protocol games built from single-proof extraction

A protocol-level reduction (balance, unforgeability) runs an adversary against an honest party
that verifies proofs, extracts a witness from every accepted proof, and turns a win into either an
extraction failure or a break of a further assumption (binding, a signature forgery). The
single-proof theorems of `ROM/` bound extraction failures for *one* prover that outputs *one*
statement and proof (`ROM/AdaptGame.lean`, `gameA`). This file supplies the protocol-independent
glue:

* **Comparison across computations, per table** (`prEvent_le_of_table`,
  `prEvent_le_sum_of_table`, `prEvent_bind_le_sum_of_table`). Against the lazy random oracle, an
  event of one deterministic oracle computation is bounded by events of others when it is so
  pointwise in the complete hash table: if for every table `g`, `P (oa at g)` implies that some
  `Q i (ob i at g)` holds, then `Pr[P | oa] ≤ Σ_i Pr[Q i | ob i]`. Proof: restrict all of them to
  one finite key set (VCVio's `restrictQueries`), pass to an eager uniform table
  (`evalDist_simulateQ_randomOracle_run'_eq_completeTable`), and use the union bound there. This
  is how a game's event is charged to the single-proof games of the `j`-th proof, each run in its
  own experiment.
* **Rounds** (`RoundAdv`, `roundsM`). An adversary that makes `n` calls to an honest party,
  written once for any monad: as a VCVio computation against the hashes and the cipher (`specIC`,
  for the extraction provers), or as a pure function of the tables (`Id`), with the evaluation
  lemma `evalWithAnswerFn_roundsM` between them and the transcript lemma `roundsT_trace`.
* **The `j`-th prover** (`proverAt`): the adversary and the honest party up to round `j`, then
  the adversary's `j`-th request, read as a proof and a statement index. Its output per table is
  the `j`-th request of the full run (`evalWithAnswerFn_proverAt`), and its queries are at most
  `j` rounds and one more request (`isKindQueryBoundIC_proverAt`, `isQueryBoundP_proverAt`).

The honest party here is any computation against `specIC`. For a party that verifies proofs with
the executable verifier this needs the verifier's cipher evaluations as queries; see
`ROM/RatatouilleBalance.lean`, `VerifierIC`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Verifier VoleMole.ROM

/-! ## Comparing events of different computations against one lazy random oracle -/

section Table

variable {D : Type} [DecidableEq D] {R : D → Type} [∀ d, Fintype (R d)] [∀ d, Nonempty (R d)]
  [∀ d, SampleableType (R d)] {α β : Type}

/-- Uniform tables on a finite key set. -/
noncomputable local instance sampleSub (S : Finset D) : SampleableType ((d : S) → R d.val) :=
  SampleableType.piOfFintype _

/-- **Lazy = eager on a finite key set.** For a key set `S` containing every query of `oa`, the
lazy random oracle gives each event of `oa` the probability of the event at a uniform table on
`S` (extended arbitrarily outside `S`). -/
theorem prEvent_eq_extendTable (S : Finset D) (oa : OracleComp (OracleSpec.ofFn R) α)
    (hS : AllQueriesSatisfy oa (· ∈ S)) (P : α → Prop) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[P r] =
      Pr{let G ← $ᵗ ((d : S) → R d.val)}[P (evalWithAnswerFn (QueryImpl.ofFn (extendTable S G)) oa)] := by
  let : MeasurableSpace α := ⊤
  have e1 : (simulateQ randomOracle (restrictQueries S oa hS)).run' ∅ =
      (simulateQ randomOracle oa).run' ∅ := randomOracle_restrictQueries S oa hS ∅
  rw [← e1]
  have h1 := evalDist_simulateQ_randomOracle_run'_eq_completeTable (restrictQueries S oa hS) ∅
  simp only [completeTable_empty] at h1
  rw [(EvalDistEq.of_evalDist_eq h1).prEvent_eq P]
  simp only [prEvent_norm]
  congr 2
  funext G
  have hG : (fun d : S => extendTable S G d.val) = G := funext (extendTable_subtype S G)
  have ha := evalWithAnswerFn_restrictQueries S oa hS (extendTable S G)
  rw [hG] at ha
  rw [ha]

/-- **Per-table comparison.** If at every complete table the event `P` of `oa` implies the event
`Q` of `ob`, then `Pr[P | oa] ≤ Pr[Q | ob]` against the lazy random oracle. -/
theorem prEvent_le_of_table (oa : OracleComp (OracleSpec.ofFn R) α)
    (ob : OracleComp (OracleSpec.ofFn R) β) (P : α → Prop) (Q : β → Prop)
    (h : ∀ g : (d : D) → R d, P (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      Q (evalWithAnswerFn (QueryImpl.ofFn g) ob)) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[P r] ≤
      Pr{let r ← (simulateQ randomOracle ob).run' ∅}[Q r] := by
  classical
  let S := possibleQueryKeys oa ∪ possibleQueryKeys ob
  have ha : AllQueriesSatisfy oa (· ∈ S) := (allQueriesSatisfy_possibleQueryKeys oa).mono
    fun d hd => Finset.mem_union_left _ hd
  have hb : AllQueriesSatisfy ob (· ∈ S) := (allQueriesSatisfy_possibleQueryKeys ob).mono
    fun d hd => Finset.mem_union_right _ hd
  rw [prEvent_eq_extendTable S oa ha, prEvent_eq_extendTable S ob hb]
  exact prEvent_mono _ _ _ fun G hG => h _ hG

/-- **Per-table union bound across computations.** If at every complete table the event `P` of
`oa` implies that some `ob i` (`i ∈ J`) returns `true`, then
`Pr[P | oa] ≤ Σ_{i ∈ J} Pr[ob i = true]` against the lazy random oracle. -/
theorem prEvent_le_sum_of_table {ι : Type} (oa : OracleComp (OracleSpec.ofFn R) α) (J : Finset ι)
    (ob : ι → OracleComp (OracleSpec.ofFn R) Bool) (P : α → Prop)
    (h : ∀ g : (d : D) → R d, P (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ i ∈ J, evalWithAnswerFn (QueryImpl.ofFn g) (ob i) = true) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[P r] ≤
      ∑ i ∈ J, Pr{let b ← (simulateQ randomOracle (ob i)).run' ∅}[b = true] := by
  classical
  let S := possibleQueryKeys oa ∪ J.biUnion fun i => possibleQueryKeys (ob i)
  have ha : AllQueriesSatisfy oa (· ∈ S) := (allQueriesSatisfy_possibleQueryKeys oa).mono
    fun d hd => Finset.mem_union_left _ hd
  have hb : ∀ i ∈ J, AllQueriesSatisfy (ob i) (· ∈ S) := fun i hi =>
    (allQueriesSatisfy_possibleQueryKeys (ob i)).mono fun d hd =>
      Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, hd⟩)
  rw [prEvent_eq_extendTable S oa ha]
  rw [Finset.sum_congr rfl fun i hi => prEvent_eq_extendTable S (ob i) (hb i hi) (· = true)]
  refine le_trans (prEvent_mono _ _ (fun G => ∃ i ∈ J,
    evalWithAnswerFn (QueryImpl.ofFn (extendTable S G)) (ob i) = true) fun G hG => h _ hG) ?_
  exact prEvent_exists_finset_le J _ _

/-- **The same, after a common draw** (e.g. the cipher table): if for every draw `E` and every
complete hash table the event of `oa E` implies that some `ob i E` returns `true`, then the
probability of the event is at most the sum of the probabilities that each `ob i` returns
`true`. -/
theorem prEvent_bind_le_sum_of_table {ι T : Type} (mT : ProbComp T)
    (oa : T → OracleComp (OracleSpec.ofFn R) α) (J : Finset ι)
    (ob : ι → T → OracleComp (OracleSpec.ofFn R) Bool) (P : T → α → Prop)
    (h : ∀ E (g : (d : D) → R d), P E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) →
      ∃ i ∈ J, evalWithAnswerFn (QueryImpl.ofFn g) (ob i E) = true) :
    Pr{let E ← mT; let r ← (simulateQ randomOracle (oa E)).run' ∅}[P E r] ≤
      ∑ i ∈ J, Pr{let E ← mT; let b ← (simulateQ randomOracle (ob i E)).run' ∅}[b = true] := by
  let : MeasurableSpace T := ⊤
  have hle : ∀ E, Pr{let r ← (simulateQ randomOracle (oa E)).run' ∅}[P E r] ≤
      ∑ i ∈ J, Pr{let b ← (simulateQ randomOracle (ob i E)).run' ∅}[b = true] := fun E =>
    prEvent_le_sum_of_table (oa E) J (fun i => ob i E) (P E) (h E)
  rw [prEvent_bind_of_discrete]
  refine le_trans (MeasureTheory.lintegral_mono hle) ?_
  rw [MeasureTheory.lintegral_finsetSum _ fun _ _ => measurable_from_top]
  refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
  rw [prEvent_bind_of_discrete]


/-- `mapM` against a complete table is the list of the evaluations. -/
theorem evalWithAnswerFn_mapM {ι' : Type} {sp : OracleSpec ι'} (f : QueryImpl sp Id) {γ : Type}
    (h : γ → OracleComp sp α) (l : List γ) :
    evalWithAnswerFn f (l.mapM h) = l.map fun x => evalWithAnswerFn f (h x) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.mapM_cons, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih, List.map_cons]

omit [∀ d, Fintype (R d)] [∀ d, Nonempty (R d)] in
/-- An event read off a computation through `decide` is the event of the computation. -/
theorem prEvent_map_decide {T : Type} (mT : ProbComp T) (oa : T → OracleComp (OracleSpec.ofFn R) α)
    (P : T → α → Prop) [∀ E r, Decidable (P E r)] :
    Pr{let E ← mT; let b ← (simulateQ randomOracle ((fun r => decide (P E r)) <$> oa E)).run' ∅}[
      b = true] = Pr{let E ← mT; let r ← (simulateQ randomOracle (oa E)).run' ∅}[P E r] := by
  let : MeasurableSpace T := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  refine congrArg _ (funext fun E => ?_)
  rw [simulateQ_map, StateT.run'_map', prEvent_map]
  simp

end Table


/-! ## The single-proof game, per table, and the extracted witness -/

section Single

variable {ι β : Type}

/-- **Per table, the adaptive game's output**: `P`'s proof, `P`'s statement index, and the
executable verifier's transcript on them. -/
theorem gameA_out (T : CrtTables) (stF : ι → Statement) (P : OracleComp specIC (ByteArray × (ι × β)))
    (E : CTable) (g : Table) :
    (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)).1 =
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).1 ∧
      stOut (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)) =
        (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2.1 ∧
      (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF P E)).2.2 =
        @verify (VoleMole.ZK.Sim.icPrg E.cipher) (Hashes.ofTable g) T
          (stF (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2.1)
          (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).1 := by
  refine ⟨?_, stOut_gameA T stF P E g, ?_⟩
  · rw [evalWithAnswerFn_gameA, gameIC_eq_bind, evalWithAnswerFn_bind, evalWithAnswerFn_map,
      evalWithAnswerFn_proverIC]
  · rw [evalWithAnswerFn_gameA, gameIC_eq_bind, evalWithAnswerFn_bind, evalWithAnswerFn_map,
      evalWithAnswerFn_proverIC]
    exact @evalWithAnswerFn_verifyQ (VoleMole.ZK.Sim.icPrg E.cipher) g T _ _

variable [HasPrg]

open Classical in
/-- **The extracted witness** of a game output: the candidate of the first known tree that is a
witness (`Extracted`), if any. -/
noncomputable def extWit (st : Statement) (W : ByteArray → (ℕ → Arith.GF128) → Prop) (r : Out β) :
    Option (ℕ → Arith.GF128) :=
  if h : Extracted st W r then
    some (VoleMole.EndToEnd.candidate (F := Arith.GF128) ((outChain r).u st) ((outChain r).dc st)
      (Classical.choose h))
  else none

/-- If extraction succeeds, the extracted witness is a witness. -/
theorem extWit_spec {st : Statement} {W : ByteArray → (ℕ → Arith.GF128) → Prop} {r : Out β}
    (h : Extracted st W r) : ∃ w, extWit st W r = some w ∧ W r.2.2.chal1 w := by
  classical
  refine ⟨_, ?_, (Classical.choose_spec h).2⟩
  simp only [extWit, h, dite_true]

end Single

/-! ## Query bounds against the hashes and the cipher -/

section Bounds

variable {α β : Type}

/-- Per-kind hash bounds add up along a bind (cipher queries are free). -/
theorem isKindQueryBoundIC_bind {oa : OracleComp specIC α} {ob : α → OracleComp specIC β}
    {q₁ q₂ : Kind → ℕ} (h₁ : IsKindQueryBoundIC oa q₁) (h₂ : ∀ a, IsKindQueryBoundIC (ob a) q₂) :
    IsKindQueryBoundIC (oa >>= ob) (q₁ + q₂) := by
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

/-- A per-kind hash bound holds for any larger budget. -/
theorem IsKindQueryBoundIC.mono {oa : OracleComp specIC α} {q q' : Kind → ℕ}
    (h : IsKindQueryBoundIC oa q) (hle : q ≤ q') : IsKindQueryBoundIC oa q' := by
  induction oa using OracleComp.inductionOn generalizing q q' with
  | pure _ => trivial
  | query_bind t k ih =>
    unfold IsKindQueryBoundIC at h ⊢
    rw [isQueryBound_query_bind_iff] at h ⊢
    obtain ⟨hc, hk⟩ := h
    cases t with
    | inl d =>
      refine ⟨lt_of_lt_of_le hc (hle d.1), fun u => ih u (hk u) fun k' => ?_⟩
      show Function.update q d.1 (q d.1 - 1) k' ≤ Function.update q' d.1 (q' d.1 - 1) k'
      by_cases hk' : k' = d.1
      · rw [hk', Function.update_self, Function.update_self]
        exact Nat.sub_le_sub_right (hle d.1) 1
      · rw [Function.update_of_ne hk', Function.update_of_ne hk']; exact hle k'
    | inr x => exact ⟨trivial, fun u => ih u (hk u) hle⟩

end Bounds

/-! ## Rounds: an adversary against an honest party -/

section Rounds

/-- **An adversary making calls to an honest party**: from its state it computes the next request
(against the hashes and the cipher) and its next state, and it absorbs each response. -/
structure RoundAdv (S Q R : Type) where
  init : S
  next : S → OracleComp specIC (Q × S)
  recv : S → R → S

variable {m : Type → Type} [Monad m] {S Q R W : Type}

/-- **One round**, in any monad: the adversary's request, the honest party's response, the
transcript extended by the pair. -/
def roundM (next : S → m (Q × S)) (serve : W → Q → m (R × W)) (recv : S → R → S)
    (x : S × W × List (Q × R)) : m (S × W × List (Q × R)) := do
  let a ← next x.1
  let b ← serve x.2.1 a.1
  pure (recv a.2 b.1, b.2, x.2.2 ++ [(a.1, b.1)])

/-- **`n` rounds**, in any monad. -/
def roundsM (next : S → m (Q × S)) (serve : W → Q → m (R × W)) (recv : S → R → S) :
    ℕ → S × W × List (Q × R) → m (S × W × List (Q × R))
  | 0, x => pure x
  | n + 1, x => roundsM next serve recv n x >>= roundM next serve recv

/-- **`n` rounds as a function** (the run against fixed tables). -/
def roundsT (next : S → Q × S) (serve : W → Q → R × W) (recv : S → R → S) (n : ℕ)
    (x : S × W × List (Q × R)) : S × W × List (Q × R) :=
  roundsM (m := Id) next serve recv n x

/-- The request and response of the round played from `y`. -/
def recOf (next : S → Q × S) (serve : W → Q → R × W) (y : S × W × List (Q × R)) : Q × R :=
  ((next y.1).1, (serve y.2.1 (next y.1).1).1)

lemma roundsT_succ (next : S → Q × S) (serve : W → Q → R × W) (recv : S → R → S) (n : ℕ)
    (x : S × W × List (Q × R)) :
    roundsT next serve recv (n + 1) x =
      (recv (next (roundsT next serve recv n x).1).2
          (serve (roundsT next serve recv n x).2.1 (next (roundsT next serve recv n x).1).1).1,
        (serve (roundsT next serve recv n x).2.1 (next (roundsT next serve recv n x).1).1).2,
        (roundsT next serve recv n x).2.2 ++ [recOf next serve (roundsT next serve recv n x)]) :=
  rfl

/-- **The transcript of a run**: round `k` is played from the state after `k` rounds. -/
theorem roundsT_trace (next : S → Q × S) (serve : W → Q → R × W) (recv : S → R → S) (n : ℕ)
    (x : S × W × List (Q × R)) :
    (roundsT next serve recv n x).2.2 =
      x.2.2 ++ (List.range n).map fun k => recOf next serve (roundsT next serve recv k x) := by
  induction n with
  | zero => show x.2.2 = x.2.2 ++ []; simp
  | succ n ih => rw [roundsT_succ, ih, List.range_succ, List.map_append, List.append_assoc]; rfl

/-- **Per table, the oracle run is the function run.** -/
theorem evalWithAnswerFn_roundsM {ι' : Type} {sp : OracleSpec ι'} (f : QueryImpl sp Id)
    (next : S → OracleComp sp (Q × S)) (serve : W → Q → OracleComp sp (R × W))
    (recv : S → R → S) (nextT : S → Q × S) (serveT : W → Q → R × W)
    (hn : ∀ s, evalWithAnswerFn f (next s) = nextT s)
    (hs : ∀ w q, evalWithAnswerFn f (serve w q) = serveT w q) (n : ℕ)
    (x : S × W × List (Q × R)) :
    evalWithAnswerFn f (roundsM next serve recv n x) = roundsT nextT serveT recv n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [roundsM, evalWithAnswerFn_bind, ih, roundM, hn, hs, evalWithAnswerFn_pure]
    rfl

variable (A : RoundAdv S Q R) (serve : W → Q → OracleComp specIC (R × W))

/-- `n` rounds: per-kind hash queries. -/
theorem isKindQueryBoundIC_roundsM {qA qS : Kind → ℕ}
    (hA : ∀ s, IsKindQueryBoundIC (A.next s) qA) (hS : ∀ w q, IsKindQueryBoundIC (serve w q) qS)
    (n : ℕ) (x : S × W × List (Q × R)) :
    IsKindQueryBoundIC (roundsM A.next serve A.recv n x) (n • (qA + qS)) := by
  induction n generalizing x with
  | zero => trivial
  | succ n ih =>
    rw [succ_nsmul]
    refine isKindQueryBoundIC_bind (ih x) fun y => ?_
    have : IsKindQueryBoundIC (roundM A.next serve A.recv y) (qA + (qS + 0)) := by
      unfold roundM
      exact isKindQueryBoundIC_bind (hA y.1) fun a =>
        isKindQueryBoundIC_bind (hS y.2.1 a.1) fun b => isQueryBound_pure _ _ _ _
    simpa only [add_zero] using this

/-- `n` rounds: queries satisfying `p` (e.g. cipher queries, hash queries). -/
theorem isQueryBoundP_roundsM (p : DomIC → Prop) [DecidablePred p] {a s : ℕ}
    (hA : ∀ s, IsQueryBoundP (A.next s) p a) (hS : ∀ w q, IsQueryBoundP (serve w q) p s)
    (n : ℕ) (x : S × W × List (Q × R)) :
    IsQueryBoundP (roundsM A.next serve A.recv n x) p (n * (a + s)) := by
  induction n generalizing x with
  | zero => trivial
  | succ n ih =>
    rw [Nat.succ_mul]
    refine isQueryBoundP_bind (ih x) fun y _ => ?_
    have : IsQueryBoundP (roundM A.next serve A.recv y) p (a + (s + 0)) := by
      unfold roundM
      exact isQueryBoundP_bind (hA y.1) fun b _ =>
        isQueryBoundP_bind (hS y.2.1 b.1) fun c _ => isQueryBoundP_pure p _ 0
    simpa only [add_zero] using this

/-- **The `j`-th prover**: the adversary and the honest party for `j` rounds, then the
adversary's `j`-th request, read as a proof with a statement index (`pick`). -/
def proverAt {ι β : Type} (w₀ : W) (pick : Q → ByteArray × (ι × β)) (j : ℕ) :
    OracleComp specIC (ByteArray × (ι × β)) := do
  let x ← roundsM A.next serve A.recv j (A.init, w₀, [])
  let a ← A.next x.1
  pure (pick a.1)

/-- **Per table, the `j`-th prover outputs the `j`-th request of the run.** -/
theorem evalWithAnswerFn_proverAt {ι β : Type} (f : QueryImpl specIC Id) (nextT : S → Q × S)
    (serveT : W → Q → R × W) (hn : ∀ s, evalWithAnswerFn f (A.next s) = nextT s)
    (hs : ∀ w q, evalWithAnswerFn f (serve w q) = serveT w q) (w₀ : W)
    (pick : Q → ByteArray × (ι × β)) (j : ℕ) :
    evalWithAnswerFn f (proverAt A serve w₀ pick j) =
      pick (nextT (roundsT nextT serveT A.recv j (A.init, w₀, [])).1).1 := by
  simp only [proverAt, evalWithAnswerFn_bind, evalWithAnswerFn_roundsM f A.next serve A.recv nextT
    serveT hn hs, hn, evalWithAnswerFn_pure]

/-- The `j`-th prover's per-kind hash queries: `j` rounds and one request. -/
theorem isKindQueryBoundIC_proverAt {ι β : Type} {qA qS : Kind → ℕ}
    (hA : ∀ s, IsKindQueryBoundIC (A.next s) qA) (hS : ∀ w q, IsKindQueryBoundIC (serve w q) qS)
    (w₀ : W) (pick : Q → ByteArray × (ι × β)) (j : ℕ) :
    IsKindQueryBoundIC (proverAt A serve w₀ pick j) ((j + 1) • (qA + qS)) := by
  refine IsKindQueryBoundIC.mono (q := j • (qA + qS) + (qA + 0)) ?_ ?_
  · unfold proverAt
    exact isKindQueryBoundIC_bind (isKindQueryBoundIC_roundsM A serve hA hS j _) fun x =>
      isKindQueryBoundIC_bind (q₂ := 0) (hA x.1) fun a => isQueryBound_pure (pick a.1) _ _ _
  · intro k; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_zero, Nat.succ_mul]; omega

/-- The `j`-th prover's queries satisfying `p`. -/
theorem isQueryBoundP_proverAt {ι β : Type} (p : DomIC → Prop) [DecidablePred p] {a s : ℕ}
    (hA : ∀ s, IsQueryBoundP (A.next s) p a) (hS : ∀ w q, IsQueryBoundP (serve w q) p s)
    (w₀ : W) (pick : Q → ByteArray × (ι × β)) (j : ℕ) :
    IsQueryBoundP (proverAt A serve w₀ pick j) p ((j + 1) * (a + s)) := by
  refine IsQueryBoundP.mono (n := j * (a + s) + (a + 0)) ?_ (by rw [Nat.succ_mul]; omega)
  unfold proverAt
  exact isQueryBoundP_bind (isQueryBoundP_roundsM A serve p hA hS j _) fun x _ =>
    isQueryBoundP_bind (hA x.1) fun b _ => isQueryBoundP_pure p _ 0

end Rounds


/-! ## A verifier that queries the cipher -/

/-- **A cipher-querying implementation of the executable verifier**: a computation against the
hashes and the cipher whose decision, on every hash table `g` and cipher table `E`, is the
executable verifier's (with the ideal-cipher PRG of `E`), with at most `qV k` hash queries of kind
`k`, `nV` hash queries in all and `eV` cipher queries. An honest party that verifies with it is a
computation against `specIC`, so the `j`-th prover of a game (`proverAt`) can re-run its
verifications, and the straight-line extractor sees their cipher queries. -/
structure VerifierIC (T : CrtTables) (verQ : Statement → ByteArray → OracleComp specIC Bool)
    (qV : Kind → ℕ) (nV eV : ℕ) : Prop where
  eval : ∀ (g : Table) (E : CTable) st pf, evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verQ st pf) =
    (@verify (VoleMole.ZK.Sim.icPrg E.cipher) (Hashes.ofTable g) T st pf).accept
  kinds : ∀ st pf, IsKindQueryBoundIC (verQ st pf) qV
  hashes : ∀ st pf, IsQueryBoundP (verQ st pf) (fun t => t.isLeft = true) nV
  cipher : ∀ st pf, IsQueryBoundP (verQ st pf) (fun t => t.isRight = true) eV

end VoleMole.ROM.IC
