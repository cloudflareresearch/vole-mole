import VoleMole.Theft.PlainLog
import VoleMole.ROM.PrefixIC

/-!
# The tables of the theft games as `ROM/`'s oracle, and query budgets

The last stage of a theft adversary reads the two `H₃` slices and the shared tables
`ShX R p (XTab L M)` (`H₂³`, `H₅`, the cipher rows, and the extra table of `H₁`, `H₂⁰`, `H₂⁴`,
`H₄`, `H₂¹`, `H₂²`, `H_comb` on inputs of at most `L` bytes). Here those tables answer the oracle
of `ROM/`'s soundness theorems, `specIC` (a hash query `(k, x)` of any kind and input, or a cipher
**cell** `(key, block)`):

* `recP g₁ g₂ t`: the hash record of the slices and the tables: the verifier's record `recV` on
  the base record `hbX` of the extra table (`H₂³`, `H₅` and the seven extra hashes are the
  tables on their table points, SHAKE elsewhere), with the two slices answering `H₃` at the
  17-byte inputs `encSl` (an input no party of the games queries otherwise).
* **`ansP g₁ g₂ t`**: the answers of `specIC`: `recP`'s hashes (as `Kind.outLen` bytes) and the
  cipher cells `(k, z) ↦ row(E k)(z)`. `ofTable_tabP`: the hashes of the answer table are `recP`.
* **`QBud q qE oa`**: `oa` makes at most `q k` hash queries of kind `k` and `qE` cipher queries
  (`ROM/`'s `IsKindQueryBoundIC`, `IsQueryBoundP`).
* **`stageBudgetX_runT`**: an oracle computation within `QBud q qE`, run on the tables, has the
  read budget `StageBudgetX (q h3) (q h5) qE` of the theft theorems: a slice is read at its `H₃`
  queries, `H₅` at its `H₅` queries, the cipher at the rows of its cell queries (a cell read is
  one row read, so `qE` cells read at most `qE` rows).
* **`admHit_runT`**: it reads each chain table (`H₂⁰`, `H₂¹`, `H₂²` on short inputs) by a decision
  tree with `q mu`, `q h21`, `q h22` queries (`Hit.AdmHit`).
* `runT_vPreIC`: the prefix computation `vPreIC` run on the tables is the simulator's prefix
  (`outPre`, with `rec5 (hbX x) G5` and the cipher rows).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open OracleComp OracleSpec

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## Runs and VCVio's evaluation -/

section Eval

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}

/-- `runT` is VCVio's evaluation with the answer function. -/
lemma runT_eq_eval (f : (k : ι) → spec k) (oa : OracleComp spec α) :
    runT f oa = evalWithAnswerFn (QueryImpl.ofFn f) oa := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih =>
    show runT f (k (f t)) = evalWithAnswerFn (QueryImpl.ofFn f) (liftM (spec.query t) >>= k)
    rw [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, ih]
    rfl

end Eval

/-! ## The answers -/

section Answers

variable {R : Type} [CipherRow R] {p : Params} {L M : ℕ}

/-- A slice key as 17 bytes: the 16-byte key and the slice's index. -/
def slv (k : Bool × Bytes 16) : Bytes 17 :=
  fun i => if h : i.val < 16 then k.2 ⟨i, h⟩ else if k.1 then 1 else 0

lemma slv_injective : Function.Injective slv := by
  rintro ⟨b, y⟩ ⟨b', y'⟩ h
  have hb := congrFun h ⟨16, by omega⟩
  have hy : y = y' := funext fun i => by
    have := congrFun h ⟨i, by omega⟩
    simpa [slv, i.isLt] using this
  subst hy
  cases b <;> cases b' <;> simp_all [slv]

/-- **The `H₃` inputs of the slices** (17 bytes; no party of the games queries them otherwise). -/
def encSl (k : Bool × Bytes 16) : ByteArray := ba (slv k)

lemma encSl_injective : Function.Injective encSl := fun _ _ h => slv_injective (ba_injective h)

/-- The two slices as one table. -/
def slT (g₁ g₂ : Tab3) (k : Bool × Bytes 16) : Bytes Kind.h3.outLen := if k.1 then g₂ k.2 else g₁ k.2

/-- **The hash record of the slices and the tables**: `H₃` the slices at `encSl`, `H₅` and `H₂³`
the tables (`recV`), the extra hashes the extra table (`hbX`), SHAKE elsewhere. -/
noncomputable def recP (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) : Hashes :=
  (recV p (hbX t.2.2) t.1 t.2.1.1).withTable .h3 encSl (slT g₁ g₂)

omit [CipherRow R] in
lemma recP_wf (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) : HashesWF (recP g₁ g₂ t) :=
  (((hbX_wf t.2.2).withTable .h23 _ _).withTable .h5 _ _).withTable .h3 _ _

omit [CipherRow R] in
lemma recV_hash_h3 (t : ShX R p (XTab L M)) (b : ByteArray) :
    (recV p (hbX t.2.2) t.1 t.2.1.1).hash .h3 b = (hbX t.2.2).hash .h3 b :=
  (Hashes.withTable_ne _ _ _ (by decide) _ _ _).trans (Hashes.withTable_ne _ _ _ (by decide) _ _ _)

omit [CipherRow R] in
open Classical in
/-- `recP` at `H₃`: the slices at `encSl`. -/
lemma recP_h3 (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) (b : ByteArray) :
    (recP g₁ g₂ t).hash .h3 b = if h : ∃ a, encSl a = b then ba (slT g₁ g₂ h.choose) else
      (hbX t.2.2).hash .h3 b := by
  refine (Hit.withTable_self (recV p (hbX t.2.2) t.1 t.2.1.1) .h3 encSl (slT g₁ g₂) b).trans ?_
  rw [recV_hash_h3]
  split_ifs <;> rfl

omit [CipherRow R] in
open Classical in
/-- `recP` at `H₅`: the table at `enc5`. -/
lemma recP_h5 (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) (b : ByteArray) :
    (recP g₁ g₂ t).hash .h5 b = if h : ∃ a, enc5 a = b then ba (t.2.1.1 h.choose) else
      (hbX t.2.2).hash .h5 b := by
  refine (Hashes.withTable_ne (recV p (hbX t.2.2) t.1 t.2.1.1) .h3 .h5 (by decide) encSl
    (slT g₁ g₂) b).trans ((Hit.withTable_self ((hbX t.2.2).withTable .h23 (enc2 p) t.1) .h5 enc5
    t.2.1.1 b).trans ?_)
  rw [Hashes.withTable_ne (hbX t.2.2) .h23 .h5 (by decide) (enc2 p) t.1 b]
  split_ifs <;> rfl

omit [CipherRow R] in
open Classical in
/-- `recP` at `H₂³`: the table at `enc2`. -/
lemma recP_h23 (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) (b : ByteArray) :
    (recP g₁ g₂ t).hash .h23 b = if h : ∃ a, enc2 p a = b then ba (t.1 h.choose) else
      (hbX t.2.2).hash .h23 b :=
  (Hashes.withTable_ne (recV p (hbX t.2.2) t.1 t.2.1.1) .h3 .h23 (by decide) encSl
    (slT g₁ g₂) b).trans ((Hashes.withTable_ne ((hbX t.2.2).withTable .h23 (enc2 p) t.1) .h5 .h23
    (by decide) enc5 t.2.1.1 b).trans ((Hit.withTable_self (hbX t.2.2) .h23 (enc2 p) t.1 b).trans
    (by split_ifs <;> rfl)))

omit [CipherRow R] in
/-- `recP` elsewhere: the base record of the extra table. -/
lemma recP_other (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) {k : Kind} (h3 : k ≠ .h3)
    (h5 : k ≠ .h5) (h23 : k ≠ .h23) (b : ByteArray) :
    (recP g₁ g₂ t).hash k b = (hbX t.2.2).hash k b :=
  (Hashes.withTable_ne (recV p (hbX t.2.2) t.1 t.2.1.1) .h3 k h3 encSl (slT g₁ g₂) b).trans
    ((Hashes.withTable_ne ((hbX t.2.2).withTable .h23 (enc2 p) t.1) .h5 k h5 enc5 t.2.1.1 b).trans
    (Hashes.withTable_ne (hbX t.2.2) .h23 k h23 (enc2 p) t.1 b))

/-- **The answer table of the hashes.** -/
noncomputable def tabP (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) : Table :=
  fun d => blk d.1.outLen ((recP g₁ g₂ t).hash d.1 d.2)

/-- **The cipher cells**: `(k, z) ↦ row(E k)(z)`. -/
def cellP (t : ShX R p (XTab L M)) : CTable := fun c => rowFn t.2.1.2 c.1 c.2

/-- **The answers of `specIC` on the slices and the tables.** -/
noncomputable def ansP (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) : (d : DomIC) → AnsIC d :=
  join (tabP g₁ g₂ t) (cellP t)

lemma ansP_inl (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) (d : Dom) :
    ansP g₁ g₂ t (.inl d) = tabP g₁ g₂ t d := rfl

lemma ansP_inr (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) (c : Cell) :
    ansP g₁ g₂ t (.inr c) = cellP t c := rfl

omit [CipherRow R] in
/-- **The hashes of the answer table are `recP`.** -/
lemma ofTable_tabP (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) :
    Hashes.ofTable (tabP g₁ g₂ t) = recP g₁ g₂ t := by
  show Hashes.mk _ = recP g₁ g₂ t
  cases h : recP g₁ g₂ t with
  | mk H =>
    congr 1
    funext k b
    have hs := recP_wf g₁ g₂ t k b
    rw [h] at hs
    show ba (blk k.outLen ((recP g₁ g₂ t).hash k b)) = H k b
    rw [h]
    exact ba_blk_of_size hs

/-- The cipher of the cells is the rows. -/
lemma cipher_cellP (t : ShX R p (XTab L M)) : (cellP t).cipher = rowFn t.2.1.2 := rfl

/-- **The prefix computation, run on the tables**, is the simulator's prefix with the base
record of the extra table, the `H₅` table and the cipher rows. -/
theorem runT_vPreIC (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) (T : CrtTables) (st : Statement)
    (b : ByteArray) :
    runT (ansP g₁ g₂ t) (vPreIC T st b) =
      @vPre (icPrg (rowFn t.2.1.2)) (rec5 (hbX t.2.2) t.2.1.1) T st b := by
  rw [runT_eq_eval, ansP, evalWithAnswerFn_vPreIC, ofTable_tabP, cipher_cellP]
  have h1 : (recP g₁ g₂ t).AgreeOff .h3 (recV p (hbX t.2.2) t.1 t.2.1.1) :=
    (Hashes.agreeOff_withTable _ _ _ _).symm
  have h2 : (recV p (hbX t.2.2) t.1 t.2.1.1).AgreeOff .h23 (rec5 (hbX t.2.2) t.2.1.1) :=
    (Hashes.agreeOff_withTable _ _ _ _).symm.withTable_other (by decide) _ _
  rw [@vPre_agreeOff (icPrg (rowFn t.2.1.2)) _ _ _ unread_h3 h1,
    @vPre_agreeOff (icPrg (rowFn t.2.1.2)) _ _ _ unread_h23 h2]

end Answers

/-! ## Query budgets -/

section Budget

variable {α : Type}

/-- **The query budget**: at most `q k` hash queries of kind `k` and `qE` cipher cells. -/
def QBud (q : Kind → ℕ) (qE : ℕ) (oa : OracleComp specIC α) : Prop :=
  IsKindQueryBoundIC oa q ∧ IsQueryBoundP oa (fun t => t.isRight = true) qE

/-- A hash query of kind `k`. -/
def kindB (k : Kind) : DomIC → Bool
  | .inl d => decide (d.1 = k)
  | .inr _ => false

/-- **The queries of one kind**, from the per-kind budget. -/
lemma isQueryBoundP_kind {oa : OracleComp specIC α} {q : Kind → ℕ} (h : IsKindQueryBoundIC oa q)
    (k : Kind) : IsQueryBoundP oa (fun d => kindB k d = true) (q k) := by
  refine IsQueryBoundP.proj (p := fun d => kindB k d = true) (fun b => b k) (fun t b hc hp => ?_) (fun t b hc => ?_) h
  · cases t with
    | inl d =>
      simp only [kindB, decide_eq_true_eq] at hp
      subst hp
      exact hc
    | inr x => simp [kindB] at hp
  · cases t with
    | inl d =>
      by_cases hk : d.1 = k
      · subst hk; simp [kindB]
      · simp [kindB, hk, Function.update_of_ne (Ne.symm hk)]
    | inr x => simp [kindB]

/-- The number of queries of one kind in a run. -/
lemma countP_kind_le {oa : OracleComp specIC α} {q : Kind → ℕ} (h : IsKindQueryBoundIC oa q)
    (k : Kind) (f : (d : DomIC) → AnsIC d) : (qlog f oa).countP (kindB k) ≤ q k :=
  countP_qlog_le oa f (kindB k) (isQueryBoundP_kind h k)

/-- **A run reads a component at the keys its queries decode to.** If the answers `f`, `f'` agree
at every query whose key (`dec`) they agree at, the runs agree; the keys are at most as many as
the queries of a class `P` containing the decodable ones. -/
lemma runT_congr_dec {K : Type} [DecidableEq K] (oa : OracleComp specIC α)
    (f f' : (d : DomIC) → AnsIC d) (dec : DomIC → Option K) (Q : Finset K)
    (hQ : ∀ d ∈ qlog f oa, ∀ k, dec d = some k → k ∈ Q)
    (hf : ∀ d, (∀ k, dec d = some k → k ∈ Q) → f d = f' d) : runT f' oa = runT f oa :=
  (runT_congr oa f f' fun d hd => hf d (hQ d hd)).2

lemma card_dec_le {K : Type} [DecidableEq K] (oa : OracleComp specIC α) (f : (d : DomIC) → AnsIC d)
    (dec : DomIC → Option K) (P : DomIC → Bool) {n : ℕ}
    (hP : IsQueryBoundP oa (fun d => P d = true) n) (hdec : ∀ d k, dec d = some k → P d = true) :
    ((qlog f oa).filterMap dec).toFinset.card ≤ n := by
  refine (card_toFinset_filterMap_le _ _).trans ((List.countP_mono_left fun d _ hd => ?_).trans
    (countP_qlog_le oa f P hP))
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (by simpa using hd)
  exact hdec d k hk

lemma mem_dec {K : Type} [DecidableEq K] {l : List DomIC} {dec : DomIC → Option K} {d : DomIC}
    (hd : d ∈ l) {k : K} (hk : dec d = some k) : k ∈ (l.filterMap dec).toFinset :=
  List.mem_toFinset.2 (List.mem_filterMap.2 ⟨d, hd, hk⟩)

end Budget

/-! ## Read budgets of a run on the tables -/

section Reads

variable {R : Type} [CipherRow R] {p : Params} {L M : ℕ} {α : Type}

open Classical in
/-- The `H₅` key of a query. -/
noncomputable def dec5 : DomIC → Option (Bytes 37)
  | .inl d => if d.1 = .h5 then (if h : ∃ a, enc5 a = d.2 then some h.choose else none) else none
  | .inr _ => none

open Classical in
/-- The key of a query to slice `j`. -/
noncomputable def dec3 (j : Bool) : DomIC → Option (Bytes 16)
  | .inl d => if d.1 = .h3 then (if h : ∃ a, encSl a = d.2 then
      (if h.choose.1 = j then some h.choose.2 else none) else none) else none
  | .inr _ => none

/-- The row of a cipher query. -/
def decE : DomIC → Option Blk
  | .inl _ => none
  | .inr c => some c.1

lemma dec5_kind {d : DomIC} {k : Bytes 37} (h : dec5 d = some k) : kindB .h5 d = true := by
  rcases d with ⟨k', b⟩ | c
  · simp only [dec5] at h
    split_ifs at h with h1
    simp [kindB, h1]
  · simp [dec5] at h

lemma dec3_kind {j : Bool} {d : DomIC} {k : Bytes 16} (h : dec3 j d = some k) :
    kindB .h3 d = true := by
  rcases d with ⟨k', b⟩ | c
  · simp only [dec3] at h
    split_ifs at h with h1
    simp [kindB, h1]
  · simp [dec3] at h

lemma decE_right {d : DomIC} {k : Blk} (h : decE d = some k) : d.isRight = true := by
  rcases d with d | c
  · simp [decE] at h
  · rfl

/-- The answers with another `H₅` table agree at every query whose `H₅` key they agree at. -/
lemma ansP_h5 (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) (G5 : Tab5F) (d : DomIC)
    (hd : ∀ k, dec5 d = some k → t.2.1.1 k = G5 k) :
    ansP g₁ g₂ t d = ansP g₁ g₂ (t.1, ((G5, t.2.1.2), t.2.2)) d := by
  classical
  rcases d with ⟨k, b⟩ | c
  · show blk _ ((recP g₁ g₂ t).hash k b) = blk _ ((recP g₁ g₂ (t.1, ((G5, t.2.1.2), t.2.2))).hash k b)
    by_cases h5 : k = .h5
    · subst h5
      rw [recP_h5, recP_h5]
      by_cases h : ∃ a, enc5 a = b
      · rw [dite_eq_left h, dite_eq_left h, hd h.choose (by simp only [dec5, ite_true, dite_eq_left h])]
      · rw [dite_eq_right h, dite_eq_right h]
    · by_cases h3 : k = .h3
      · subst h3
        rw [recP_h3, recP_h3]
      · by_cases h23 : k = .h23
        · subst h23
          rw [recP_h23, recP_h23]
        · rw [recP_other _ _ _ h3 h5 h23, recP_other _ _ _ h3 h5 h23]
  · rfl

/-- The answers with another slice `j` agree at every query whose slice key they agree at. -/
lemma ansP_h3 (g₁ g₂ g' : Tab3) (j : Bool) (t : ShX R p (XTab L M)) (d : DomIC)
    (hd : ∀ k, dec3 j d = some k → (if j then g₂ else g₁) k = g' k) :
    ansP g₁ g₂ t d = ansP (if j then g₁ else g') (if j then g' else g₂) t d := by
  classical
  rcases d with ⟨k, b⟩ | c
  · show blk _ ((recP g₁ g₂ t).hash k b) =
      blk _ ((recP (if j then g₁ else g') (if j then g' else g₂) t).hash k b)
    by_cases h3 : k = .h3
    · subst h3
      rw [recP_h3, recP_h3]
      by_cases h : ∃ a, encSl a = b
      · rw [dite_eq_left h, dite_eq_left h]
        have hd' := fun y (hy : h.choose = (j, y)) => hd y (by
          simp only [dec3, ite_true, dite_eq_left h, hy])
        rcases hc : h.choose with ⟨i, y⟩
        rw [hc] at hd'
        have hv : slT g₁ g₂ (i, y) = slT (if j then g₁ else g') (if j then g' else g₂) (i, y) := by
          cases i <;> cases j <;> simp only [slT, Bool.false_eq_true, ite_true, ite_false] at hd' ⊢
          all_goals first | rfl | exact hd' y rfl
        rw [hv]
      · rw [dite_eq_right h, dite_eq_right h]
    · by_cases h5 : k = .h5
      · subst h5
        rw [recP_h5, recP_h5]
      · by_cases h23 : k = .h23
        · subst h23
          rw [recP_h23, recP_h23]
        · rw [recP_other _ _ _ h3 h5 h23, recP_other _ _ _ h3 h5 h23]
  · rw [ansP_inr, ansP_inr]

/-- The answers with other cipher rows agree at every query whose row they agree at. -/
lemma ansP_E (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) (E : Blk → R) (d : DomIC)
    (hd : ∀ k, decE d = some k → t.2.1.2 k = E k) :
    ansP g₁ g₂ t d = ansP g₁ g₂ (t.1, ((t.2.1.1, E), t.2.2)) d := by
  rcases d with ⟨k, b⟩ | c
  · rfl
  · show rowFn t.2.1.2 c.1 c.2 = rowFn E c.1 c.2
    rw [rowFn_congr (hd c.1 rfl)]

/-- **The read budget of a run on the tables**: the slices at its `H₃` queries, `H₅` at its `H₅`
queries, the cipher at the rows of its cell queries. -/
theorem stageBudgetX_runT {oa : OracleComp specIC α} {q : Kind → ℕ} {qE : ℕ} (h : QBud q qE oa) :
    StageBudgetX (R := R) (p := p) (X := XTab L M)
      (fun g₁ g₂ t => runT (ansP g₁ g₂ t) oa) (q .h3) (q .h5) qE := by
  classical
  intro x
  refine ⟨fun g₂ s => ?_, fun g₁ s => ?_, fun g₁ g₂ => ?_, fun g₁ g₂ => ?_⟩
  · refine ⟨fun g₁ => ((qlog (ansP g₁ g₂ (atX s x)) oa).filterMap (dec3 false)).toFinset,
      fun g₁ => card_dec_le _ _ _ _ (isQueryBoundP_kind h.1 .h3) fun _ _ => dec3_kind,
      fun g₁ g' hg => ?_⟩
    exact runT_congr_dec oa _ _ (dec3 false) _ (fun d hd k hk => mem_dec hd hk)
      fun d hd => ansP_h3 g₁ g₂ g' false _ d fun k hk => by simpa using hg k (hd k hk)
  · refine ⟨fun g₂ => ((qlog (ansP g₁ g₂ (atX s x)) oa).filterMap (dec3 true)).toFinset,
      fun g₂ => card_dec_le _ _ _ _ (isQueryBoundP_kind h.1 .h3) fun _ _ => dec3_kind,
      fun g₂ g' hg => ?_⟩
    exact runT_congr_dec oa _ _ (dec3 true) _ (fun d hd k hk => mem_dec hd hk)
      fun d hd => ansP_h3 g₁ g₂ g' true _ d fun k hk => by simpa using hg k (hd k hk)
  · refine ⟨fun s => ((qlog (ansP g₁ g₂ (atX s x)) oa).filterMap dec5).toFinset,
      fun s => card_dec_le _ _ _ _ (isQueryBoundP_kind h.1 .h5) fun _ _ => dec5_kind,
      fun s G5 hg => ?_⟩
    exact runT_congr_dec oa _ _ dec5 _ (fun d hd k hk => mem_dec hd hk)
      fun d hd => ansP_h5 g₁ g₂ (atX s x) G5 d fun k hk => hg k (hd k hk)
  · refine ⟨fun s => ((qlog (ansP g₁ g₂ (atX s x)) oa).filterMap decE).toFinset,
      fun s => card_dec_le _ _ _ _ h.2 fun _ _ => decE_right, fun s E hg => ?_⟩
    exact runT_congr_dec oa _ _ decE _ (fun d hd k hk => mem_dec hd hk)
      fun d hd => ansP_E g₁ g₂ (atX s x) E d fun k hk => hg k (hd k hk)

end Reads

/-! ## Decision trees on the chain tables -/

section Tree

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} {K Y : Type}

/-- **A run is a decision tree in a table `T`** with as many queries as the run makes of a class
`P` that contains every query whose answer depends on `T` (each at one key of `T`). -/
theorem qtree_runT [Nonempty Y] (a : (K → Y) → (d : ι) → spec d) (P : ι → Prop) [DecidablePred P]
    (hdep : ∀ d, (∀ T T', a T d = a T' d) ∨ (P d ∧ ∃ κ, ∀ T T', T κ = T' κ → a T d = a T' d))
    (oa : OracleComp spec α) {n : ℕ} (h : IsQueryBoundP oa P n) :
    ComOW.QTree (fun T => runT (a T) oa) n := by
  induction oa generalizing n with
  | pure x => exact .ret _ _
  | queryBind t k ih =>
    have h' := (isQueryBoundP_query_bind_iff P t k n).1 h
    rcases hdep t with hc | ⟨hp, κ, hκ⟩
    · let T₀ : K → Y := fun _ => Classical.arbitrary Y
      have e : (fun T => runT (a T) (queryBind t k)) =
          fun T => runT (a T) (k (a T₀ t)) := by
        funext T
        show runT (a T) (k (a T t)) = _
        rw [hc T T₀]
      rw [e]
      exact ih (a T₀ t) ((h'.2 _).mono (by split <;> omega))
    · have hn : 0 < n := h'.1.resolve_left (not_not.2 hp)
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have e : (fun T => runT (a T) (queryBind t k)) =
          fun T => (fun v T => runT (a T) (k (a (fun _ => v) t))) (T κ) T := by
        funext T
        show runT (a T) (k (a T t)) = _
        rw [hκ T (fun _ => T κ) rfl]
      rw [e]
      refine ComOW.QTree.ask κ (fun v T => runT (a T) (k (a (fun _ => v) t))) m fun v => ih _ ?_
      have := h'.2 (a (fun _ => v) t)
      simpa [hp] using this

end Tree

end VoleMole.Theft
