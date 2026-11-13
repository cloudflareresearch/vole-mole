import VoleMole.ZK.ReadsInterleave
import VoleMole.ROM.TableReads
import VoleMole.ROM.PrivacyReads

/-!
# Interleaved sessions under a scheduler that reads the tables

`ZK/ReadsInterleave.lean` proves the interleaving lemma for a scheduler that is a function of the
transcript (`next : transcript → Act`). Here the scheduler **reads the tables itself**: each step
is a VCVio oracle computation over the table oracle (`ROM.Reads.TSpec`: the challenge sessions'
`H₃` slices and the shared tables), run on the game's tables (`ROM.Reads.runT`), and its read set
at that step is the log of its queries (`ROM.Reads.qlog`). Consistency is by construction
(`ROM.Reads.runT_congr`), and its budget per step is the syntactic query bound (`QBudget`).

Each stretch of the schedule also **stops when the scheduler says so** (`stop`, a predicate on the
transcript, checked before each step; at most `L` steps): the games use it to let the challenge
start, and the challenge answers complete, at steps the scheduler chooses. (A fixed number of
steps is `stop = fun _ => false`.)

* *The model* (`stepO`, `runO`, `logO`): one step runs the scheduler's computation on the answers
  `f` and the session tables `t`, and the chosen action as in `stepT`; `logO` collects the
  scheduler's queries along the run.
* **The interleaving lemma with a table-reading scheduler** (`GoodO`, `GoodO.run`): for tables of
  any type `T`, with the scheduler's answers `fT t` and the sessions' tables `π t`, a transcript
  function built from constants, external events and stretches of the schedule is determined by
  the sessions' current read sets (`RQl`, on `π t`) together with the scheduler's queries so far
  (`G t`), and so are those queries. So the read set of the run is **the union of the sessions'
  read sets and the scheduler's per-step read sets**.
* *Counting* (`countP_logO_le`): `L` steps of a scheduler whose every step is within a query bound
  `a` make at most `L·a` queries of that class.
* *Four slices* (`ROM.Reads.ins4`, `read_ins4`): the scheduler's answers with slice `j` of four
  replaced by the table's slice are `readAt` at `j`, for the per-slice budgets of Moussaka and
  Ratatouille.
* **The packaged reader** (`GoodO.sreads`): on `Tb R p` with the scheduler reading slice `j` (the
  other slices fixed) and the shared tables, a good transcript is `SReads` with the sessions'
  `n·b` plus the scheduler's queries: slice `c₃`, `H₂³` `n·b₂ + c₂`, `H₅` `n·b₅ + c₅`, cipher
  `n·b_E + c_E`.
-/

open Finset OracleComp OracleSpec

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
open VoleMole.ROM.Reads (TKey TSpec QBudget readAt rsOf read_congr countP_qlog_le
  card_toFinset_filterMap_le)

section InterleaveOC

variable {R : Type} {p : Params} {C M O E : Type} {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-! ## The run -/

section Run

variable (n : ℕ) (out : ℕ → C → List M → Tb R p → O)
  (next : List (Ev C M O E) → OracleComp spec (Act C M))

/-- **One step of a table-reading scheduler**: its computation run on the answers `f`, and the
chosen action's result on the sessions' tables `t`. -/
def stepO (tr : List (Ev C M O E)) (f : (k : ι) → spec k) (t : Tb R p) : List (Ev C M O E) :=
  tr ++ [.act (ROM.Reads.runT f (next tr))
    (resO n out (sessSt n tr) (ROM.Reads.runT f (next tr)) t)]

variable (stop : List (Ev C M O E) → Bool)

/-- **At most `L` steps, until `stop`** (checked before each step). -/
def runO : ℕ → List (Ev C M O E) → ((k : ι) → spec k) → Tb R p → List (Ev C M O E)
  | 0, tr, _, _ => tr
  | L + 1, tr, f, t => if stop tr then tr else runO L (stepO n out next tr f t) f t

/-- **The scheduler's queries along the run.** -/
def logO : ℕ → List (Ev C M O E) → ((k : ι) → spec k) → Tb R p → List ι
  | 0, _, _, _ => []
  | L + 1, tr, f, t =>
    if stop tr then [] else ROM.Reads.qlog f (next tr) ++ logO L (stepO n out next tr f t) f t

/-- **Counting**: `L` steps, each within the query bound `a` for the class `P`, make at most
`L·a` queries of that class. -/
lemma countP_logO_le (P : ι → Bool) {a : ℕ}
    (h : ∀ tr, IsQueryBoundP (next tr) (fun k => P k = true) a) :
    ∀ (L : ℕ) (tr : List (Ev C M O E)) (f : (k : ι) → spec k) (t : Tb R p),
      (logO n out next stop L tr f t).countP P ≤ L * a := by
  intro L
  induction L with
  | zero => intro tr f t; simp [logO]
  | succ L ih =>
    intro tr f t
    simp only [logO]
    split_ifs
    · simp
    · rw [List.countP_append, Nat.succ_mul]
      have := countP_qlog_le (next tr) f P (h tr)
      have := ih (stepO n out next tr f t) f t
      omega

variable {next} in
/-- **A scheduler that reads no table** (`pure` at every step) and never stops early runs as in
`ZK/ReadsInterleave.lean`: the earlier model is the special case. -/
lemma runO_pure (nx : List (Ev C M O E) → Act C M) (f : (k : ι) → spec k) (t : Tb R p) :
    ∀ (L : ℕ) (tr : List (Ev C M O E)),
      runO n out (fun tr => (pure (nx tr) : OracleComp spec (Act C M))) (fun _ => false) L tr f t =
        runT n out nx L tr t := by
  intro L
  induction L with
  | zero => intro tr; rfl
  | succ L ih =>
    intro tr
    simp only [runO, Bool.false_eq_true, ↓reduceIte, runT]
    rw [← ih]
    rfl

end Run

/-! ## The interleaving lemma -/

section Good

variable {n : ℕ} {out : ℕ → C → List M → Tb R p → O} {Q : ℕ → C → List M → Tb R p → RS p}
  {next : List (Ev C M O E) → OracleComp spec (Act C M)} {T : Type}

variable (n Q) in
/-- **A transcript function read off the sessions' read sets and the scheduler's queries**: two
tables that agree on the union of the sessions' read sets (on the sessions' tables `π t`) and on
the scheduler's queries `G t` (through its answers `fT t`) give the same transcript and the same
queries. -/
def GoodO (fT : T → (k : ι) → spec k) (π : T → Tb R p) (F : T → List (Ev C M O E))
    (G : T → List ι) : Prop :=
  ∀ t t', AgT (RQl Q (π t) 0 (sessSt n (F t))) (π t) (π t') → (∀ k ∈ G t, fT t k = fT t' k) →
    F t' = F t ∧ G t' = G t

variable {fT : T → (k : ι) → spec k} {π : T → Tb R p}

/-- A constant transcript is read off nothing. -/
lemma GoodO.const (tr : List (Ev C M O E)) :
    GoodO n Q fT π (fun _ => tr) (fun _ => ([] : List ι)) := fun _ _ _ _ => ⟨rfl, rfl⟩

/-- **An external event** changes no session. -/
lemma GoodO.ext {F : T → List (Ev C M O E)} {G : T → List ι} (hF : GoodO n Q fT π F G) (e : E) :
    GoodO n Q fT π (fun t => F t ++ [.ext e]) G := by
  intro t t' h hg
  rw [sessSt_append] at h
  obtain ⟨e1, e2⟩ := hF t t' h hg
  exact ⟨by show F t' ++ _ = F t ++ _; rw [e1], e2⟩

/-- **One step of the table-reading scheduler**: its queries are added to the read set. -/
lemma GoodO.step (hS : SessReads out Q) {F : T → List (Ev C M O E)} {G : T → List ι}
    (hF : GoodO n Q fT π F G) :
    GoodO n Q fT π (fun t => stepO n out next (F t) (fT t) (π t))
      (fun t => G t ++ ROM.Reads.qlog (fT t) (next (F t))) := by
  intro t t' h hg
  simp only [stepO, sessSt_append] at h
  obtain ⟨e1, e2⟩ := hF t t' (AgT.mono (RQl_le_upd hS _ _ _ _) h)
    fun k hk => hg k (List.mem_append_left _ hk)
  obtain ⟨e3, e4⟩ := ROM.Reads.runT_congr (next (F t)) (fT t) (fT t')
    fun k hk => hg k (List.mem_append_right _ hk)
  refine ⟨?_, ?_⟩
  · show stepO n out next (F t') (fT t') (π t') = stepO n out next (F t) (fT t) (π t)
    simp only [stepO, e1, e4]
    rw [resO_congr hS _ _ _ h]
  · show G t' ++ ROM.Reads.qlog (fT t') (next (F t')) = G t ++ ROM.Reads.qlog (fT t) (next (F t))
    rw [e1, e2, e3]

/-- The sessions' read sets only grow along a run. -/
lemma le_runO (hS : SessReads out Q) (stop : List (Ev C M O E) → Bool) (f : (k : ι) → spec k)
    (tb : Tb R p) : ∀ (L : ℕ) (tr : List (Ev C M O E)),
      RS.Le (RQl Q tb 0 (sessSt n tr)) (RQl Q tb 0 (sessSt n (runO n out next stop L tr f tb))) := by
  intro L
  induction L with
  | zero => intro tr; exact RS.Le.refl _
  | succ L ih =>
    intro tr
    simp only [runO]
    split_ifs
    · exact RS.Le.refl _
    · refine RS.Le.trans ?_ (ih _)
      simp only [stepO, sessSt_append]
      exact RQl_le_upd hS _ _ _ _

/-- **The interleaving lemma with a table-reading scheduler**: at most `L` steps until `stop`,
after any good start; the scheduler's queries along the run join the read set. -/
lemma GoodO.run (hS : SessReads out Q) (stop : List (Ev C M O E) → Bool) :
    ∀ (L : ℕ) {F : T → List (Ev C M O E)} {G : T → List ι}, GoodO n Q fT π F G →
      GoodO n Q fT π (fun t => runO n out next stop L (F t) (fT t) (π t))
        (fun t => G t ++ logO n out next stop L (F t) (fT t) (π t)) := by
  intro L
  induction L with
  | zero => intro F G hF; simpa [runO, logO] using hF
  | succ L ih =>
    intro F G hF t t' h hg
    have hgo : ∀ k ∈ G t, fT t k = fT t' k := fun k hk => hg k (List.mem_append_left _ hk)
    have hle := le_runO (n := n) (next := next) hS stop (fT t) (π t) (L + 1) (F t)
    obtain ⟨e1, e2⟩ := hF t t' (AgT.mono hle h) hgo
    show runO n out next stop (L + 1) (F t') (fT t') (π t') = runO n out next stop (L + 1) (F t) (fT t) (π t) ∧
      G t' ++ logO n out next stop (L + 1) (F t') (fT t') (π t') =
        G t ++ logO n out next stop (L + 1) (F t) (fT t) (π t)
    rw [e1, e2]
    cases hst : stop (F t) with
    | true =>
      simp [runO, logO, hst]
    | false =>
      have h2 := ih (hF.step (next := next) hS)
      simp only [runO, logO, hst, Bool.false_eq_true, ↓reduceIte] at h hg ⊢
      have hg' : ∀ k ∈ (G t ++ ROM.Reads.qlog (fT t) (next (F t))) ++
          logO n out next stop L (stepO n out next (F t) (fT t) (π t)) (fT t) (π t),
          fT t k = fT t' k := fun k hk => hg k (by simpa only [List.append_assoc] using hk)
      obtain ⟨e3, e4⟩ := h2 t t' h hg'
      dsimp only at e3 e4
      rw [e1] at e3
      rw [e1, e2] at e4
      refine ⟨e3, ?_⟩
      simpa only [List.append_assoc] using e4

/-- **A good transcript is consistent**: its sessions' read sets and its queries are those at
`t`. -/
lemma GoodO.cons (hS : SessReads out Q) {F : T → List (Ev C M O E)} {G : T → List ι}
    (hF : GoodO n Q fT π F G) (t t' : T) (h : AgT (RQl Q (π t) 0 (sessSt n (F t))) (π t) (π t'))
    (hg : ∀ k ∈ G t, fT t k = fT t' k) :
    RQl Q (π t') 0 (sessSt n (F t')) = RQl Q (π t) 0 (sessSt n (F t)) ∧ F t' = F t ∧ G t' = G t := by
  obtain ⟨e1, e2⟩ := hF t t' h hg
  exact ⟨by rw [e1]; exact RQl_cons hS _ h, e1, e2⟩

end Good

/-- `Rd3.bind` for a reader given as `F g = f (m g) g`. -/
lemma Rd3.bindEq {X Y : Type*} {m : Tab3 → Y} {f : Y → Tab3 → X} {F : Tab3 → X} {a b : ℕ}
    (hF : ∀ g, F g = f (m g) g) (hm : Rd3 m a) (hf : ∀ y, Rd3 (f y) b) : Rd3 F (a + b) := by
  have e : F = fun g => f (m g) g := funext hF
  subst e
  exact hm.bind hf

/-! ## The packaged reader: one slice and the shared tables -/

section Pack

variable {n : ℕ} {out : ℕ → C → List M → Tb R p → O} {Q : ℕ → C → List M → Tb R p → RS p}
  {ι' : Type} [DecidableEq ι']

/-- **The read sets of a good transcript on one slice and the shared tables**: the scheduler's
slice-`j` queries, and the union of the sessions' and the scheduler's shared-table reads. -/
def rsIL (j : ι') (S : RS p) (l : List (TKey ι' (preLen p))) : RS p :=
  ((rsOf j l).1, S.2.1 ∪ (rsOf j l).2.1, S.2.2.1 ∪ (rsOf j l).2.2.1, S.2.2.2 ∪ (rsOf j l).2.2.2)

/-- **A good transcript is a consistent table reader** of one slice and the shared tables (the
sessions read the shared tables only, `π t = (default, t.2)`), with the sessions' `n·b` and the
scheduler's queries: slice `c₃`, `H₂³` `n·b₂ + c₂`, `H₅` `n·b₅ + c₅`, cipher `n·b_E + c_E`. -/
theorem GoodO.sreads (hS : SessReads out Q) {j : ι'} {fT : Tb R p → (k : TKey ι' (preLen p)) → TKey.Ans R k}
    (hfT : ∀ (t t' : Tb R p) (l : List (TKey ι' (preLen p))), AgT (rsOf j l) t t' →
      ∀ k ∈ l, fT t k = fT t' k)
    {F : Tb R p → List (Ev C M O E)} {G : Tb R p → List (TKey ι' (preLen p))}
    (hF : GoodO (spec := TSpec ι' R (preLen p)) n Q fT (fun t => ((default : Tab3), t.2)) F G)
    {b2 b5 bE c3 c2 c5 cE : ℕ}
    (hb : ∀ j c h t, (Q j c h t).2.1.card ≤ b2 ∧ (Q j c h t).2.2.1.card ≤ b5 ∧
      (Q j c h t).2.2.2.card ≤ bE)
    (hG : ∀ t, (G t).countP (TKey.isH3 j) ≤ c3 ∧ (G t).countP TKey.isH2 ≤ c2 ∧
      (G t).countP TKey.isH5 ≤ c5 ∧ (G t).countP TKey.isIC ≤ cE) :
    SReads p F c3 (n * b2 + c2) (n * b5 + c5) (n * bE + cE) := by
  classical
  let S : Tb R p → RS p := fun t => RQl Q ((default : Tab3), t.2) 0 (sessSt n (F t))
  refine ⟨fun t => rsIL j (S t) (G t), fun t t' h => ?_, fun t => ?_⟩
  · obtain ⟨h3, h2, h5, hE⟩ := h
    have hA : AgT (S t) ((default : Tab3), t.2) ((default : Tab3), t'.2) :=
      ⟨fun _ _ => rfl, fun k hk => h2 k (mem_union_left _ hk),
        fun k hk => h5 k (mem_union_left _ hk), fun k hk => hE k (mem_union_left _ hk)⟩
    have hR : AgT (rsOf j (G t)) t t' :=
      ⟨h3, fun k hk => h2 k (mem_union_right _ hk), fun k hk => h5 k (mem_union_right _ hk),
        fun k hk => hE k (mem_union_right _ hk)⟩
    obtain ⟨e1, e2, e3⟩ := hF.cons hS t t' hA (hfT t t' (G t) hR)
    refine ⟨?_, e2⟩
    show rsIL j (S t') (G t') = rsIL j (S t) (G t)
    simp only [S] at e1 ⊢
    rw [e1, e3]
  · have hl := sessSt_length_le n (F t)
    have s2 := (card_RQl (Q := Q) (fun r => r.2.1) (fun _ _ => rfl) rfl ((default : Tab3), t.2)
      (fun j c h => (hb j c h _).1) (sessSt n (F t)) 0).trans (Nat.mul_le_mul_right b2 hl)
    have s5 := (card_RQl (Q := Q) (fun r => r.2.2.1) (fun _ _ => rfl) rfl ((default : Tab3), t.2)
      (fun j c h => (hb j c h _).2.1) (sessSt n (F t)) 0).trans (Nat.mul_le_mul_right b5 hl)
    have sE := (card_RQl (Q := Q) (fun r => r.2.2.2) (fun _ _ => rfl) rfl ((default : Tab3), t.2)
      (fun j c h => (hb j c h _).2.2) (sessSt n (F t)) 0).trans (Nat.mul_le_mul_right bE hl)
    obtain ⟨g3, g2, g5, gE⟩ := hG t
    have k3 : ((G t).filterMap (TKey.get3 j)).toFinset.card ≤ c3 :=
      (card_toFinset_filterMap_le _ _).trans (by simpa only [TKey.isSome_get3] using g3)
    have k2 : ((G t).filterMap TKey.get2).toFinset.card ≤ c2 :=
      (card_toFinset_filterMap_le _ _).trans (by simpa only [TKey.isSome_get2] using g2)
    have k5 : ((G t).filterMap TKey.get5).toFinset.card ≤ c5 :=
      (card_toFinset_filterMap_le _ _).trans (by simpa only [TKey.isSome_get5] using g5)
    have kE : ((G t).filterMap TKey.getE).toFinset.card ≤ cE :=
      (card_toFinset_filterMap_le _ _).trans (by simpa only [TKey.isSome_getE] using gE)
    exact ⟨k3, (card_union_le _ _).trans (add_le_add s2 k2),
      (card_union_le _ _).trans (add_le_add s5 k5), (card_union_le _ _).trans (add_le_add sE kE)⟩

/-- **The query budget of a scheduler bounds its queries along runs**: `L` steps of a scheduler
within `QBudget a₃ a₂ a₅ a_E` per step make at most `L·a₃` queries to slice `j`, `L·a₂` to `H₂³`,
`L·a₅` to `H₅`, `L·a_E` to the cipher. -/
lemma countP_logO_qb {m : ℕ} {R' : Type} {next : List (Ev C M O E) → OracleComp (TSpec ι' R' m) (Act C M)}
    {a3 a2 a5 aE : ℕ} (hN : ∀ tr, QBudget (next tr) a3 a2 a5 aE) (j : ι')
    (stop : List (Ev C M O E) → Bool) (L : ℕ) (tr : List (Ev C M O E))
    (f : (k : TKey ι' m) → TKey.Ans R' k) (t : Tb R p) :
    (logO n out next stop L tr f t).countP (TKey.isH3 j) ≤ L * a3 ∧
      (logO n out next stop L tr f t).countP TKey.isH2 ≤ L * a2 ∧
      (logO n out next stop L tr f t).countP TKey.isH5 ≤ L * a5 ∧
      (logO n out next stop L tr f t).countP TKey.isIC ≤ L * aE :=
  ⟨countP_logO_le n out next stop _ (fun tr => (hN tr).h3 j) L tr f t,
    countP_logO_le n out next stop _ (fun tr => (hN tr).h2) L tr f t,
    countP_logO_le n out next stop _ (fun tr => (hN tr).h5) L tr f t,
    countP_logO_le n out next stop _ (fun tr => (hN tr).hE) L tr f t⟩

end Pack

end InterleaveOC

end VoleMole.ZK.Sim

/-! ## Four slices, one replaced -/

namespace VoleMole.ROM.Reads

open VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

/-- **Four slices with the one at position `j` replaced by `g`.** -/
def ins4 : Bool × Bool → (Tab3 × Tab3) × (Tab3 × Tab3) → Tab3 → (Tab3 × Tab3) × (Tab3 × Tab3)
  | (false, false), sl, g => ((g, sl.1.2), sl.2)
  | (false, true), sl, g => ((sl.1.1, g), sl.2)
  | (true, false), sl, g => (sl.1, (g, sl.2.2))
  | (true, true), sl, g => (sl.1, (sl.2.1, g))

lemma update_sl4 (j : Bool × Bool) (sl : (Tab3 × Tab3) × (Tab3 × Tab3)) (g : Tab3) :
    Function.update (sl4 sl) j g = sl4 (ins4 j sl g) := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := sl
  rcases j with ⟨_ | _, _ | _⟩
  · exact sl4_ff a b c d g
  · exact sl4_ft a b c d g
  · exact sl4_tf a b c d g
  · exact sl4_tt a b c d g

/-- **The answers with slice `j` replaced by the table's slice** are `readAt` at `j`. -/
lemma read_ins4 {R : Type} {p : Params}
    (j : Bool × Bool) (sl : (Tab3 × Tab3) × (Tab3 × Tab3))
    (t : Tb R p) :
    TKey.read (m := preLen p) (sl4 (ins4 j sl t.1)) t.2 = readAt (sl4 sl) j t := by
  rw [readAt, update_sl4]

end VoleMole.ROM.Reads
