import VCVio.OracleComp.QueryTracking.QueryBound
import VoleMole.ZK.AdaptRO

/-!
# Table readers as oracle computations: consistency by construction

The table-reading theorems (`ZK.Sim.zk_adaptive`, `ZK.Sim.lean_zeroKnowledgeROA` and the privacy
games of `Privacy/MoussakaRA.lean`, `Privacy/RatatouilleRA.lean`, `Privacy/PomFRITRA.lean`) take
the adversary's table-reading interaction as a *function* of the tables together with the
semantic hypothesis `ZK.Sim.SReads`: query sets `Q t`, bounded per table, that are **consistent**
(a table agreeing with `t` on `Q t` has the same query sets and the same output).

`SReads` is not automatic for a function of the tables: the reader `t ↦ t.1` (the whole `H₃`
slice) has no query sets of fewer than `2¹²⁸` slice keys (`not_sReads_slice`), so a budget must
be stated somewhere. What *is* automatic is consistency. Here an interaction is written as a
VCVio oracle computation over the tables (`TSpec n R m`: `n` `H₃` slices, `H₂³` with `m`-byte
prefixes, `H₅`, the cipher rows), run deterministically on the tables (`runT`). Its read set is
the log of its queries along the run (`qlog`), consistent by construction (`runT_congr`), and its
budget is VCVio's syntactic per-class query bound (`IsQueryBoundP`, collected in `QBudget`).

* **`sReads_runT`**: an oracle computation within `QBudget a₃ a₂ a₅ a_E`, run on the slices `sl`
  with slice `j` and the shared tables taken from `t`, is `SReads p · a₃ a₂ a₅ a_E`.
* **`sReads_runT₁`**, **`zk_adaptive_oc`**, **`lean_zeroKnowledgeROA_oc`**: the single-proof
  theorems for a statement chosen by an oracle computation, with no `SReads` hypothesis.

The privacy games' corollaries are in `ROM/PrivacyReads.lean`.
-/

open OracleComp OracleSpec

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ROM.Reads

open VoleMole.ZK VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy
open VoleMole.Arith

/-! ## The table oracle -/

/-- **A query to the tables**: slice `i` of `H₃` at a 16-byte key, `H₂³` at a grinding point
(an `m`-byte prefix and a counter), `H₅` at a 37-byte key, the cipher row of a key. -/
inductive TKey (n : Type) (m : ℕ) : Type
  | h3 (i : n) (x : Bytes 16)
  | h2 (k : Bytes m × Fin nGrind)
  | h5 (x : Bytes 37)
  | ic (x : Blk)

namespace TKey

variable {n : Type} {m : ℕ}

/-- The answer type of a query (`R` the cipher rows). -/
abbrev Ans (R : Type) : TKey n m → Type
  | h3 _ _ => Bytes 32
  | h2 _ => Bytes 16
  | h5 _ => Bytes 4
  | ic _ => R

/-- A query to slice `j`. -/
def isH3 [DecidableEq n] (j : n) : TKey n m → Bool
  | h3 i _ => decide (i = j)
  | _ => false

/-- A query to `H₂³`. -/
def isH2 : TKey n m → Bool
  | h2 _ => true
  | _ => false

/-- A query to `H₅`. -/
def isH5 : TKey n m → Bool
  | h5 _ => true
  | _ => false

/-- A query to the cipher. -/
def isIC : TKey n m → Bool
  | ic _ => true
  | _ => false

/-- The slice-`j` key of a query. -/
def get3 [DecidableEq n] (j : n) : TKey n m → Option (Bytes 16)
  | h3 i x => if i = j then some x else none
  | _ => none

/-- The `H₂³` key of a query. -/
def get2 : TKey n m → Option (Bytes m × Fin nGrind)
  | h2 k => some k
  | _ => none

/-- The `H₅` key of a query. -/
def get5 : TKey n m → Option (Bytes 37)
  | h5 x => some x
  | _ => none

/-- The cipher key of a query. -/
def getE : TKey n m → Option Blk
  | ic x => some x
  | _ => none

lemma isSome_get3 [DecidableEq n] (j : n) (k : TKey n m) : (k.get3 j).isSome = k.isH3 j := by
  cases k <;> simp [get3, isH3]
  split <;> simp_all

lemma isSome_get2 (k : TKey n m) : k.get2.isSome = k.isH2 := by cases k <;> rfl
lemma isSome_get5 (k : TKey n m) : k.get5.isSome = k.isH5 := by cases k <;> rfl
lemma isSome_getE (k : TKey n m) : k.getE.isSome = k.isIC := by cases k <;> rfl

end TKey

/-- **The table oracle**: one query per table key, answered by the key's entry. -/
abbrev TSpec (n R : Type) (m : ℕ) : OracleSpec (TKey n m) := OracleSpec.ofFn (TKey.Ans R)

/-- **The answers of the tables**: the slices `sl` and the shared tables `s` (a `ShG R p` for
`m = preLen p`; stated with `m` so that tables of parameters with equal prefix lengths answer the
same queries). -/
def TKey.read {n R : Type} {m : ℕ} (sl : n → Tab3)
    (s : ((Bytes m × Fin nGrind) → Bytes 16) × Tab5F × (Blk → R)) : (k : TKey n m) → TKey.Ans R k
  | h3 i x => sl i x
  | h2 k => s.1 k
  | h5 x => s.2.1 x
  | ic x => s.2.2 x

/-! ## Running an oracle computation on fixed answers -/

section Run

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}

/-- **The run of an oracle computation** with every query `k` answered by `f k`. -/
def runT (f : (k : ι) → spec k) : OracleComp spec α → α
  | .pure x => x
  | .queryBind t k => runT f (k (f t))

/-- **The queries of the run**, in order. -/
def qlog (f : (k : ι) → spec k) : OracleComp spec α → List ι
  | .pure _ => []
  | .queryBind t k => t :: qlog f (k (f t))

/-- **The run is consistent**: answers that agree with `f` on the run's queries give the same
queries and the same output. -/
theorem runT_congr (oa : OracleComp spec α) (f f' : (k : ι) → spec k)
    (h : ∀ k ∈ qlog f oa, f k = f' k) : qlog f' oa = qlog f oa ∧ runT f' oa = runT f oa := by
  induction oa with
  | pure x => exact ⟨rfl, rfl⟩
  | queryBind t k ih =>
    have ht : f t = f' t := h t (by simp [qlog])
    have h' : ∀ k' ∈ qlog f (k (f t)), f k' = f' k' := fun k' hk => h k' (by simp [qlog, hk])
    obtain ⟨e1, e2⟩ := ih (f t) h'
    simp only [qlog, runT, ← ht]
    exact ⟨by rw [e1], e2⟩

/-- **A query bound bounds the run's queries** of that class. -/
theorem countP_qlog_le (oa : OracleComp spec α) (f : (k : ι) → spec k) (P : ι → Bool) {a : ℕ}
    (h : IsQueryBoundP oa (fun k => P k = true) a) : (qlog f oa).countP P ≤ a := by
  induction oa generalizing a with
  | pure x => simp [qlog]
  | queryBind t k ih =>
    have h' := (isQueryBoundP_query_bind_iff (fun k => P k = true) t k a).1 h
    have hk := ih (f t) (h'.2 (f t))
    simp only [qlog, List.countP_cons]
    by_cases hp : P t = true
    · simp only [hp, ↓reduceIte] at hk ⊢
      have : 0 < a := h'.1.resolve_left (by simp [hp])
      omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hk ⊢
      omega

lemma card_toFinset_filterMap_le {β : Type} [DecidableEq β] (l : List ι) (g : ι → Option β) :
    (l.filterMap g).toFinset.card ≤ l.countP fun k => (g k).isSome := by
  refine (List.toFinset_card_le _).trans (le_of_eq ?_)
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases hg : g a with _ | b
    · simp [hg, ih]
    · simp [hg, ih]

end Run

/-! ## Oracle computations are consistent table readers -/

/-- **The budget of an oracle computation over the tables**: at most `a₃` queries to each slice,
`a₂` to `H₂³`, `a₅` to `H₅` and `a_E` cipher rows, on every run (VCVio's `IsQueryBoundP`). -/
structure QBudget {n R : Type} [DecidableEq n] {m : ℕ} {α : Type}
    (oa : OracleComp (TSpec n R m) α) (a3 a2 a5 aE : ℕ) : Prop where
  h3 : ∀ j : n, IsQueryBoundP oa (fun k => k.isH3 j = true) a3
  h2 : IsQueryBoundP oa (fun k => k.isH2 = true) a2
  h5 : IsQueryBoundP oa (fun k => k.isH5 = true) a5
  hE : IsQueryBoundP oa (fun k => k.isIC = true) aE

namespace QBudget

variable {n R : Type} [DecidableEq n] {m : ℕ} {α β : Type}

lemma pure (x : α) : QBudget (pure x : OracleComp (TSpec n R m) α) 0 0 0 0 :=
  ⟨fun _ => trivial, trivial, trivial, trivial⟩

lemma mono {oa : OracleComp (TSpec n R m) α} {a3 a2 a5 aE b3 b2 b5 bE : ℕ}
    (h : QBudget oa a3 a2 a5 aE) (h3 : a3 ≤ b3) (h2 : a2 ≤ b2) (h5 : a5 ≤ b5) (hE : aE ≤ bE) :
    QBudget oa b3 b2 b5 bE :=
  ⟨fun j => (h.h3 j).mono h3, h.h2.mono h2, h.h5.mono h5, h.hE.mono hE⟩

/-- **Sequencing** adds the budgets. -/
lemma bind {oa : OracleComp (TSpec n R m) α} {ob : α → OracleComp (TSpec n R m) β}
    {a3 a2 a5 aE b3 b2 b5 bE : ℕ} (ha : QBudget oa a3 a2 a5 aE)
    (hb : ∀ x, QBudget (ob x) b3 b2 b5 bE) :
    QBudget (oa >>= ob) (a3 + b3) (a2 + b2) (a5 + b5) (aE + bE) :=
  ⟨fun j => isQueryBoundP_bind (ha.h3 j) fun x _ => (hb x).h3 j,
    isQueryBoundP_bind ha.h2 fun x _ => (hb x).h2, isQueryBoundP_bind ha.h5 fun x _ => (hb x).h5,
    isQueryBoundP_bind ha.hE fun x _ => (hb x).hE⟩

/-- One query to slice `i`. -/
lemma query_h3 (i : n) (x : Bytes 16) :
    QBudget (liftM ((TSpec n R m).query (TKey.h3 i x)) : OracleComp (TSpec n R m) _) 1 0 0 0 := by
  refine ⟨fun j => ?_, ?_, ?_, ?_⟩ <;> refine (isQueryBoundP_query_iff _ _ _).2 ?_ <;>
    simp [TKey.isH3, TKey.isH2, TKey.isH5, TKey.isIC]

end QBudget

variable {n R : Type} [DecidableEq n] {p : Params} {α : Type}

/-- The tables `t` (a slice and the shared tables) in place `j` of the slices `sl`. -/
def readAt (sl : n → Tab3) (j : n) (t : Tb R p) : (k : TKey n (preLen p)) → TKey.Ans R k :=
  TKey.read (m := preLen p) (Function.update sl j t.1) t.2

/-- The read sets of a run: its queries to slice `j` and to the shared tables. -/
def rsOf (j : n) (l : List (TKey n (preLen p))) : RS p :=
  ((l.filterMap (TKey.get3 j)).toFinset, (l.filterMap TKey.get2).toFinset,
    (l.filterMap TKey.get5).toFinset, (l.filterMap TKey.getE).toFinset)

lemma read_congr (sl : n → Tab3) (j : n) (t t' : Tb R p) (l : List (TKey n (preLen p)))
    (h : AgT (rsOf j l) t t') : ∀ k ∈ l, readAt sl j t k = readAt sl j t' k := by
  obtain ⟨h3, h2, h5, hE⟩ := h
  intro k hk
  cases k with
  | h3 i x =>
    by_cases hij : i = j
    · subst hij
      have hx : x ∈ (rsOf (p := p) i l).1 :=
        List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hk, by simp [TKey.get3]⟩)
      simpa [readAt, TKey.read] using h3 x hx
    · simp [readAt, TKey.read, Function.update_of_ne hij]
  | h2 k => exact h2 k (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hk, rfl⟩))
  | h5 x => exact h5 x (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hk, rfl⟩))
  | ic x => exact hE x (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hk, rfl⟩))

/-- **An oracle computation over the tables is a consistent table reader** (`SReads`) of each
slice (the others fixed) and the shared tables, with its query budget: the read sets are the
queries of the run. -/
theorem sReads_runT {oa : OracleComp (TSpec n R (preLen p)) α} {a3 a2 a5 aE : ℕ}
    (h : QBudget oa a3 a2 a5 aE) (sl : n → Tab3) (j : n) :
    SReads p (fun t : Tb R p => runT (readAt sl j t) oa) a3 a2 a5 aE := by
  classical
  refine ⟨fun t => rsOf j (qlog (readAt sl j t) oa), fun t t' ht => ?_, fun t => ?_⟩
  · obtain ⟨e1, e2⟩ := runT_congr oa _ _ (read_congr sl j t t' _ ht)
    exact ⟨by simp only [e1], e2⟩
  · have c := fun (P : TKey n (preLen p) → Bool) {b : ℕ}
        (hP : IsQueryBoundP oa (fun k => P k = true) b) =>
      countP_qlog_le oa (readAt sl j t) P hP
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine (card_toFinset_filterMap_le _ _).trans ?_
      simpa only [TKey.isSome_get3] using c _ (h.h3 j)
    · refine (card_toFinset_filterMap_le _ _).trans ?_
      simpa only [TKey.isSome_get2] using c _ h.h2
    · refine (card_toFinset_filterMap_le _ _).trans ?_
      simpa only [TKey.isSome_get5] using c _ h.h5
    · refine (card_toFinset_filterMap_le _ _).trans ?_
      simpa only [TKey.isSome_getE] using c _ h.hE

/-- `sReads_runT` for a reader given as a function equal to the run. -/
theorem sReads_of_eq {X : Type} {S : Tb R p → X} {oa : OracleComp (TSpec n R (preLen p)) X}
    {a3 a2 a5 aE : ℕ} (h : QBudget oa a3 a2 a5 aE) (sl : n → Tab3) (j : n)
    (hS : ∀ t, S t = runT (readAt sl j t) oa) : SReads p S a3 a2 a5 aE := by
  have e : S = fun t => runT (readAt sl j t) oa := funext hS
  rw [e]
  exact sReads_runT h sl j

/-- **A reader with one slice**: an oracle computation over one slice and the shared tables. -/
theorem sReads_runT₁ {oa : OracleComp (TSpec Unit R (preLen p)) α} {a3 a2 a5 aE : ℕ}
    (h : QBudget oa a3 a2 a5 aE) :
    SReads p (fun t : Tb R p => runT (TKey.read (m := preLen p) (fun _ => t.1) t.2) oa)
      a3 a2 a5 aE := by
  refine sReads_of_eq h (fun _ => fun _ => 0) () fun t => ?_
  have : Function.update (fun _ : Unit => fun _ : Bytes 16 => (0 : Bytes 32)) () t.1 =
      fun _ => t.1 := funext fun u => by cases u; simp
  simp only [readAt, this]

/-! ## A budget must be stated: the whole slice is no bounded reader -/

/-- **`SReads` is not automatic**: the reader that outputs its whole `H₃` slice has no consistent
query sets of fewer than `2¹²⁸` slice keys (a key off the query set can be changed). So the
budget is a genuine hypothesis; for an oracle computation it is the syntactic `QBudget`. -/
theorem not_sReads_slice [Nonempty R] {s3 s2 s5 sE : ℕ} (hs : s3 < 2 ^ 128) :
    ¬ SReads p (fun t : Tb R p => t.1) s3 s2 s5 sE := by
  classical
  rintro ⟨Q, hQ, hc⟩
  let t : Tb R p := (fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => Classical.arbitrary R)
  have hlt : (Q t).1.card < (Finset.univ : Finset (Bytes 16)).card := by
    rw [Finset.card_univ, card_bytes16]
    exact lt_of_le_of_lt (hc t).1 hs
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  let t' : Tb R p := (Function.update t.1 x fun _ => 1, t.2)
  have e := (hQ t t' ⟨fun k hk => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩).2
  · have e' := congrFun (congrFun e x) 0
    simp [t', t] at e'
  · have hk' : k ≠ x := fun h => hx (h ▸ hk)
    simp [t', Function.update_of_ne hk']

/-! ## The single-proof theorems for a statement chosen by an oracle computation -/

/-- **The admissible table readers as oracle computations**: `Sx` is the run of an oracle
computation over one slice and the shared tables with query budget `(s₃, s₂, s₅, s_E)`. -/
def OCReader (R : Type) (p : Params) (s3 s2 s5 sE : ℕ) (X : Type) (Sx : Tb R p → X) : Prop :=
  ∃ oa : OracleComp (TSpec Unit R (preLen p)) X, QBudget oa s3 s2 s5 sE ∧
    Sx = fun t => runT (TKey.read (m := preLen p) (fun _ => t.1) t.2) oa

lemma OCReader.sReads {s3 s2 s5 sE : ℕ} {X : Type} {Sx : Tb R p → X}
    (h : OCReader R p s3 s2 s5 sE X Sx) : SReads p Sx s3 s2 s5 sE := by
  obtain ⟨oa, hb, rfl⟩ := h
  exact sReads_runT₁ hb

section ZK

variable [Fintype R] [Nonempty R] [CipherRow R] [ZKPRow R] (Hb : Hashes)

/-- **Zero knowledge for a statement chosen by an oracle computation over the tables**
(`zk_adaptive` with the reader `runT oa`; no `SReads` hypothesis: `oa`'s query budget
`QBudget s₃ s₂ s₅ s_E` is syntactic, and consistency holds by construction). -/
theorem zk_adaptive_oc {X : Type} (p : Params) (hlr : p.labelRows = true) (hsp : SmallParams p)
    (hHb : HashesWF Hb) (stOf : X → Statement) (wOf : X → ByteArray)
    (cs : X → ByteArray → ByteArray → System GF128) (hst : ∀ x, (stOf x).params = p)
    (hzk : ∀ x, ZKHyp CrtGen.tables (stOf x) (wOf x) (cs x))
    (oa : OracleComp (TSpec Unit R (preLen p)) X) {s3 s2 s5 sE : ℕ} (hS : QBudget oa s3 s2 s5 sE)
    {q3 q5 qE : ℕ} (D : X → Except String ByteArray → Tb R p → Prop)
    (hD : ∀ x, Budget p q3 q5 qE (fun o g s => D x o (g, s))) :
    let S : Tb R p → X := fun t => runT (TKey.read (m := preLen p) (fun _ => t.1) t.2) oa
    |pr (Bytes 16 × Tb R p) (fun z =>
        D (S z.2) (realRO p Hb (stOf (S z.2)) (wOf (S z.2)) z.1 z.2.1 z.2.2) z.2) -
      pr (SimCoins p × Tb R p) (fun z =>
        D (S z.2) (simulate p z.1) (z.2.1, progRO p Hb (stOf (S z.2)) z.1 z.2.2))| ≤
      εAdG R p p.qsDegree q3 q5 qE s3 s2 s5 sE :=
  zk_adaptive Hb p hlr hsp hHb stOf wOf cs hst hzk _ (sReads_runT₁ hS) D hD

/-- **The Lean prover is `ZeroKnowledgeROA` against oracle-computation readers**
(`lean_zeroKnowledgeROA` with the admissible readers `OCReader`: no `SReads` hypothesis). -/
theorem lean_zeroKnowledgeROA_oc {I W O : Type*} (p : Params) (stOf : I → Statement)
    (hp : ∀ x, (stOf x).params = p) (hlr : p.labelRows = true) (enc : I → W → ByteArray)
    (Rl : I → W → Prop) (cs : I → ByteArray → ByteArray → System GF128)
    (h : ∀ x w, Rl x w → ZKHyp CrtGen.tables (stOf x) (enc x w) (cs x)) (hHb : HashesWF Hb)
    (hsp : SmallParams p) (q3 q5 qE s3 s2 s5 sE : ℕ) (φ : Except String ByteArray → O) :
    ZeroKnowledgeROA Rl (fun x w ρ g (s : ShG R p) => φ (realRO p Hb (stOf x) (enc x w) ρ g s))
      (fun _ c => φ (simulate p c)) (fun x c (s : ShG R p) => progRO p Hb (stOf x) c s)
      (OCReader R p s3 s2 s5 sE) (Budget p q3 q5 qE)
      (εAdG R p p.qsDegree q3 q5 qE s3 s2 s5 sE) :=
  (lean_zeroKnowledgeROA Hb p stOf hp hlr enc Rl cs h hHb hsp q3 q5 qE s3 s2 s5 sE φ).mono
    (fun _ _ hS => hS.sReads) (fun _ h => h) le_rfl

end ZK

end VoleMole.ROM.Reads
