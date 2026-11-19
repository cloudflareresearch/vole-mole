import VoleMole.Theft.PlainTotal
import VoleMole.ROM.MoussakaOMUFSimPerm
import VoleMole.ZK.ReadsROPerm

/-!
# The theft tables as `ROM/`'s oracle with permutation rows and inverse queries

`Theft/PlainOracle.lean` answers `ROM/`'s forward-only oracle `specIC` (hash queries and cipher
cells) on the theft tables. With **permutation rows** (`R = Equiv.Perm Blk`, AES as uniformly
random permutations, `ZKRow.perm`) the adversary may also query the inverse cipher. Here the
tables answer `ROM/`'s oracle of the permutation model, `specP` (`ROM/PermModel.lean`: hash
queries, forward queries `(true, (k, z)) ↦ π_k(z)` and inverse queries `(false, (k, y)) ↦
π_k⁻¹(y)`), and the facts the theft theorems need about a run are restated for it:

* **`ansQ g₁ g₂ t`**: `recP`'s hashes and the permutation table `t.2.1.2` with inverses
  (`joinP (tabP g₁ g₂ t) t.2.1.2`); on hash queries it is `ansP`.
* `liftP` (`ROM/MoussakaOMUFSimPerm.lean`, forward-only computations): `runT_liftP`, `qlog_liftP`.
* **`QBudP q qE oa`**: at most `q k` hash queries of kind `k` and `qE` cipher queries, forward or
  inverse.
* **`stageBudgetX_runTQ`**: the read budget `StageBudgetX (q h3) (q h5) qE`: a forward or inverse
  query under key `k` reads the row (the permutation) `k`.
* **`admHit_runTQ`**: the chain tables are read by decision trees (`Hit.AdmHit`).
* `patch2P`, `ansQ_prog`: the simulators' programming as a patch of the answers.
* **`normTQ`**: hash queries off the table points answered by SHAKE locally (`normTQ_ansQ`), with
  the total hash budget `totK M q` (`qBudPT_normTQ`).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## The answers -/

section Answers

variable {p : Params} {L M : ℕ}

/-- **The answers of `specP` on the slices and the tables with permutation rows**: the hashes of
`recP`, forward and inverse queries to the permutations. -/
noncomputable def ansQ (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M)) :
    (d : DomP) → AnsP d :=
  joinP (tabP g₁ g₂ t) t.2.1.2

lemma ansQ_inl (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M)) (d : Dom) :
    ansQ g₁ g₂ t (.inl d) = ansP g₁ g₂ t (.inl d) := rfl

lemma ansQ_inr (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M)) (c : PCell) :
    ansQ g₁ g₂ t (.inr c) = pans t.2.1.2 c := rfl

/-- The cipher cells of the permutation rows are the forward table. -/
lemma cellP_perm (t : ShX (Equiv.Perm Blk) p (XTab L M)) : cellP t = PTable.fwd t.2.1.2 := rfl

/-- **A forward-only query as a query of the permutation model.** -/
def embIC : DomIC → DomP
  | .inl d => .inl d
  | .inr c => .inr (true, c)

variable {α : Type}

/-- **A forward-only computation, run on the permutation tables**, is its run on the forward
tables. -/
lemma runT_liftP (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M))
    (X : OracleComp specIC α) : runT (ansQ g₁ g₂ t) (liftP X) = runT (ansP g₁ g₂ t) X := by
  rw [runT_eq_eval, runT_eq_eval]
  exact evalWithAnswerFn_liftP _ _ X

lemma qlog_liftP (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M))
    (X : OracleComp specIC α) :
    qlog (ansQ g₁ g₂ t) (liftP X) = (qlog (ansP g₁ g₂ t) X).map embIC := by
  induction X using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t' k ih =>
    rcases t' with d | c
    · rw [liftP_inl, qlog_query_bind, qlog_query_bind, List.map_cons]
      exact congrArg (List.cons _) (ih _)
    · rw [liftP_inr, qlog_query_bind, qlog_query_bind, List.map_cons]
      exact congrArg (List.cons _) (ih _)

end Answers

/-! ## Query budgets -/

section Budget

variable {α : Type}

/-- **The query budget with inverse queries**: at most `q k` hash queries of kind `k` and `qE`
cipher queries (forward or inverse). -/
def QBudP (q : Kind → ℕ) (qE : ℕ) (oa : OracleComp specP α) : Prop :=
  IsKindQueryBoundP oa q ∧ IsQueryBoundP oa (fun t => t.isRight = true) qE

/-- `QBudP` and at most `nG` hash queries in all. -/
def QBudPT (q : Kind → ℕ) (qE nG : ℕ) (oa : OracleComp specP α) : Prop :=
  QBudP q qE oa ∧ IsQueryBoundP oa (fun t => t.isLeft = true) nG

/-- A hash query of kind `k`. -/
def kindBP (k : Kind) : DomP → Bool
  | .inl d => decide (d.1 = k)
  | .inr _ => false

/-- **The queries of one kind**, from the per-kind budget. -/
lemma isQueryBoundP_kindP {oa : OracleComp specP α} {q : Kind → ℕ} (h : IsKindQueryBoundP oa q)
    (k : Kind) : IsQueryBoundP oa (fun d => kindBP k d = true) (q k) := by
  refine IsQueryBoundP.proj (p := fun d => kindBP k d = true) (fun b => b k)
    (fun t b hc hp => ?_) (fun t b hc => ?_) h
  · cases t with
    | inl d =>
      simp only [kindBP, decide_eq_true_eq] at hp
      subst hp
      exact hc
    | inr x => simp [kindBP] at hp
  · cases t with
    | inl d =>
      by_cases hk : d.1 = k
      · subst hk; simp [kindBP]
      · simp [kindBP, hk, Function.update_of_ne (Ne.symm hk)]
    | inr x => simp [kindBP]

/-- **A run reads a component at the keys its queries decode to** (any oracle). -/
lemma runT_congr_decG {ι : Type} {spec : OracleSpec.{0, 0} ι} {K : Type} [DecidableEq K]
    (oa : OracleComp spec α) (f f' : (d : ι) → spec d) (dec : ι → Option K) (Q : Finset K)
    (hQ : ∀ d ∈ qlog f oa, ∀ k, dec d = some k → k ∈ Q)
    (hf : ∀ d, (∀ k, dec d = some k → k ∈ Q) → f d = f' d) : runT f' oa = runT f oa :=
  (runT_congr oa f f' fun d hd => hf d (hQ d hd)).2

lemma card_dec_leG {ι : Type} {spec : OracleSpec.{0, 0} ι} {K : Type} [DecidableEq K]
    (oa : OracleComp spec α) (f : (d : ι) → spec d) (dec : ι → Option K) (P : ι → Bool) {n : ℕ}
    (hP : IsQueryBoundP oa (fun d => P d = true) n) (hdec : ∀ d k, dec d = some k → P d = true) :
    ((qlog f oa).filterMap dec).toFinset.card ≤ n := by
  refine (card_toFinset_filterMap_le _ _).trans ((List.countP_mono_left fun d _ hd => ?_).trans
    (countP_qlog_le oa f P hP))
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (by simpa using hd)
  exact hdec d k hk

lemma mem_decG {ι : Type} {K : Type} [DecidableEq K] {l : List ι} {dec : ι → Option K} {d : ι}
    (hd : d ∈ l) {k : K} (hk : dec d = some k) : k ∈ (l.filterMap dec).toFinset :=
  List.mem_toFinset.2 (List.mem_filterMap.2 ⟨d, hd, hk⟩)

/-- A forward-only computation keeps its budget in the permutation model. -/
lemma qBudP_liftP {X : OracleComp specIC α} {q : Kind → ℕ} {qE : ℕ} (h : QBud q qE X) :
    QBudP q qE (liftP X) :=
  ⟨isKindQueryBoundP_liftP h.1, isQueryBoundP_right_liftP h.2⟩

end Budget

/-! ## Read budgets of a run on the tables -/

section Reads

variable {p : Params} {L M : ℕ} {α : Type}

/-- The `H₅` key of a query. -/
noncomputable def dec5P : DomP → Option (Bytes 37)
  | .inl d => dec5 (.inl d)
  | .inr _ => none

/-- The key of a query to slice `j`. -/
noncomputable def dec3P (j : Bool) : DomP → Option (Bytes 16)
  | .inl d => dec3 j (.inl d)
  | .inr _ => none

/-- **The row of a cipher query**, forward or inverse. -/
def decEP : DomP → Option Blk
  | .inl _ => none
  | .inr c => some c.2.1

lemma dec5P_kind {d : DomP} {k : Bytes 37} (h : dec5P d = some k) : kindBP .h5 d = true := by
  rcases d with d | c
  · simpa [kindBP, kindB] using dec5_kind (d := .inl d) h
  · simp [dec5P] at h

lemma dec3P_kind {j : Bool} {d : DomP} {k : Bytes 16} (h : dec3P j d = some k) :
    kindBP .h3 d = true := by
  rcases d with d | c
  · simpa [kindBP, kindB] using dec3_kind (d := .inl d) h
  · simp [dec3P] at h

lemma decEP_right {d : DomP} {k : Blk} (h : decEP d = some k) : d.isRight = true := by
  rcases d with d | c
  · simp [decEP] at h
  · rfl

lemma ansQ_h5 (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M)) (G5 : Tab5F) (d : DomP)
    (hd : ∀ k, dec5P d = some k → t.2.1.1 k = G5 k) :
    ansQ g₁ g₂ t d = ansQ g₁ g₂ (t.1, ((G5, t.2.1.2), t.2.2)) d := by
  rcases d with d | c
  · exact ansP_h5 g₁ g₂ t G5 (.inl d) hd
  · rfl

lemma ansQ_h3 (g₁ g₂ g' : Tab3) (j : Bool) (t : ShX (Equiv.Perm Blk) p (XTab L M)) (d : DomP)
    (hd : ∀ k, dec3P j d = some k → (if j then g₂ else g₁) k = g' k) :
    ansQ g₁ g₂ t d = ansQ (if j then g₁ else g') (if j then g' else g₂) t d := by
  rcases d with d | c
  · exact ansP_h3 g₁ g₂ g' j t (.inl d) hd
  · rw [ansQ_inr, ansQ_inr]

lemma ansQ_E (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M)) (E : Blk → Equiv.Perm Blk)
    (d : DomP) (hd : ∀ k, decEP d = some k → t.2.1.2 k = E k) :
    ansQ g₁ g₂ t d = ansQ g₁ g₂ (t.1, ((t.2.1.1, E), t.2.2)) d := by
  rcases d with d | ⟨b, c⟩
  · rfl
  · have h := hd c.1 rfl
    rw [ansQ_inr, ansQ_inr]
    cases b
    · exact congrArg (fun σ : Equiv.Perm Blk => σ.symm c.2) h
    · exact congrArg (fun σ : Equiv.Perm Blk => σ c.2) h

/-- **The read budget of a run on the permutation tables**: the slices at its `H₃` queries, `H₅`
at its `H₅` queries, the permutations at the keys of its forward and inverse queries. -/
theorem stageBudgetX_runTQ {oa : OracleComp specP α} {q : Kind → ℕ} {qE : ℕ}
    (h : QBudP q qE oa) :
    StageBudgetX (R := Equiv.Perm Blk) (p := p) (X := XTab L M)
      (fun g₁ g₂ t => runT (ansQ g₁ g₂ t) oa) (q .h3) (q .h5) qE := by
  classical
  intro x
  refine ⟨fun g₂ s => ?_, fun g₁ s => ?_, fun g₁ g₂ => ?_, fun g₁ g₂ => ?_⟩
  · refine ⟨fun g₁ => ((qlog (ansQ g₁ g₂ (atX s x)) oa).filterMap (dec3P false)).toFinset,
      fun g₁ => card_dec_leG _ _ _ _ (isQueryBoundP_kindP h.1 .h3) fun _ _ => dec3P_kind,
      fun g₁ g' hg => ?_⟩
    exact runT_congr_decG oa _ _ (dec3P false) _ (fun d hd k hk => mem_decG hd hk)
      fun d hd => ansQ_h3 g₁ g₂ g' false _ d fun k hk => by simpa using hg k (hd k hk)
  · refine ⟨fun g₂ => ((qlog (ansQ g₁ g₂ (atX s x)) oa).filterMap (dec3P true)).toFinset,
      fun g₂ => card_dec_leG _ _ _ _ (isQueryBoundP_kindP h.1 .h3) fun _ _ => dec3P_kind,
      fun g₂ g' hg => ?_⟩
    exact runT_congr_decG oa _ _ (dec3P true) _ (fun d hd k hk => mem_decG hd hk)
      fun d hd => ansQ_h3 g₁ g₂ g' true _ d fun k hk => by simpa using hg k (hd k hk)
  · refine ⟨fun s => ((qlog (ansQ g₁ g₂ (atX s x)) oa).filterMap dec5P).toFinset,
      fun s => card_dec_leG _ _ _ _ (isQueryBoundP_kindP h.1 .h5) fun _ _ => dec5P_kind,
      fun s G5 hg => ?_⟩
    exact runT_congr_decG oa _ _ dec5P _ (fun d hd k hk => mem_decG hd hk)
      fun d hd => ansQ_h5 g₁ g₂ (atX s x) G5 d fun k hk => hg k (hd k hk)
  · refine ⟨fun s => ((qlog (ansQ g₁ g₂ (atX s x)) oa).filterMap decEP).toFinset,
      fun s => card_dec_leG _ _ _ _ h.2 fun _ _ => decEP_right, fun s E hg => ?_⟩
    exact runT_congr_decG oa _ _ decEP _ (fun d hd k hk => mem_decG hd hk)
      fun d hd => ansQ_E g₁ g₂ (atX s x) E d fun k hk => hg k (hd k hk)

end Reads

/-! ## The chain tables are read by decision trees -/

section Hit

variable {p : Params} {L M : ℕ} {α : Type}

/-- The dependence of the answers on one chain table, as `hdep_chain`. -/
lemma hdep_chainQ {Y : Type} (g₁ g₂ : Tab3) (G2 : Tab2G p) (G5E : Tab5F × (Blk → Equiv.Perm Blk))
    (set : (KL L → Y) → XTab L M) (k₀ : Kind)
    (hoff : ∀ T T', (hbX (set T)).AgreeOff k₀ (hbX (set T')))
    (hon : ∀ b, Hit.keyL L b = none → ∀ T T', (hbX (set T)).hash k₀ b = (hbX (set T')).hash k₀ b)
    (hkey : ∀ b κ, Hit.keyL L b = some κ → ∀ T T', T κ = T' κ →
      (hbX (set T)).hash k₀ b = (hbX (set T')).hash k₀ b) (d : DomP) :
    (∀ T T', ansQ g₁ g₂ ((G2, (G5E, set T)) : ShX (Equiv.Perm Blk) p (XTab L M)) d =
        ansQ g₁ g₂ ((G2, (G5E, set T')) : ShX (Equiv.Perm Blk) p (XTab L M)) d) ∨
      (kindBP k₀ d = true ∧ ∃ κ, ∀ T T', T κ = T' κ →
        ansQ g₁ g₂ ((G2, (G5E, set T)) : ShX (Equiv.Perm Blk) p (XTab L M)) d =
          ansQ g₁ g₂ ((G2, (G5E, set T')) : ShX (Equiv.Perm Blk) p (XTab L M)) d) := by
  rcases d with d | c
  · rcases hdep_chain (R := Equiv.Perm Blk) (p := p) g₁ g₂ G2 G5E set k₀ hoff hon hkey (.inl d)
      with h | ⟨hk, κ, hκ⟩
    · exact Or.inl h
    · exact Or.inr ⟨by simpa [kindBP, kindB] using hk, κ, hκ⟩
  · exact Or.inl fun T T' => by rw [ansQ_inr, ansQ_inr]

/-- **A run on the permutation tables reads the chain tables by decision trees** with as many
queries as it makes to `H₂⁰`, `H₂¹`, `H₂²` (`Hit.AdmHit`). -/
theorem admHit_runTQ {oa : OracleComp specP α} {q : Kind → ℕ} {qE : ℕ} (h : QBudP q qE oa) :
    Hit.AdmHit (R := Equiv.Perm Blk) (p := p) (L := L) (M := M) (q .mu) (q .h21) (q .h22)
      (fun g₁ g₂ t => runT (ansQ g₁ g₂ t) oa) := by
  intro g₁ g₂
  refine ⟨fun G2 G5E x => ?_, fun G2 G5E x => ?_, fun G2 G5E x => ?_⟩
  · have hd := hdep_chainQ (p := p) g₁ g₂ G2 G5E (fun T => Hit.setMu T x) .mu
      (fun T T' => Hit.hbX_agreeOff_mu T T' x) (fun b hb T T' => hbX_mu_none hb T T' x)
      (fun b κ hb T T' hT => hbX_mu_some hb T T' x hT)
    exact qtree_runT _ (fun d => kindBP .mu d = true) hd oa (isQueryBoundP_kindP h.1 .mu)
  · have hd := hdep_chainQ (p := p) g₁ g₂ G2 G5E (fun T => Hit.set21 T x) .h21
      (fun T T' => Hit.hbX_agreeOff_21 T T' x) (fun b hb T T' => hbX_21_none hb T T' x)
      (fun b κ hb T T' hT => hbX_21_some hb T T' x hT)
    exact qtree_runT _ (fun d => kindBP .h21 d = true) hd oa (isQueryBoundP_kindP h.1 .h21)
  · have hd := hdep_chainQ (p := p) g₁ g₂ G2 G5E (fun T => Hit.set22 T x) .h22
      (fun T T' => Hit.hbX_agreeOff_22 T T' x) (fun b hb T T' => hbX_22_none hb T T' x)
      (fun b κ hb T T' hT => hbX_22_some hb T T' x hT)
    exact qtree_runT _ (fun d => kindBP .h22 d = true) hd oa (isQueryBoundP_kindP h.1 .h22)

end Hit

/-! ## The simulators' programming as a patch of the answers -/

section Patch

variable {p : Params} {L M : ℕ}

/-- **The patch of the answers by a partial `H₂³` table** (`patch2` on hash queries). -/
noncomputable def patch2P (p : Params) (m : K2 p → Option (Bytes 16)) :
    (d : DomP) → AnsP d → AnsP d
  | .inl d => patch2 p m (.inl d)
  | .inr _ => fun u => u

/-- **A programming at the grinding points of `pre` patches the answers** (`patch2P`). -/
lemma ansQ_prog (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M)) (pre : ByteArray)
    (g : Grind) (d : DomP) :
    ansQ g₁ g₂ ((programAt (key2 p pre) g t.1, t.2) : ShX (Equiv.Perm Blk) p (XTab L M)) d =
      patch2P p (mOf p pre g) d (ansQ g₁ g₂ t d) := by
  rcases d with d | c
  · exact ansP_prog g₁ g₂ t pre g (.inl d)
  · rfl

/-- **The answers on another `H₂³` table** agree at every query that is not an `H₂³` query. -/
lemma ansQ_G2 (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M)) (G2 : Tab2G p) (d : DomP)
    (hd : kindBP .h23 d = false) :
    ansQ g₁ g₂ ((G2, t.2) : ShX (Equiv.Perm Blk) p (XTab L M)) d = ansQ g₁ g₂ t d := by
  rcases d with d | c
  · exact ansP_G2 g₁ g₂ t G2 (.inl d) (by simpa [kindBP, kindB] using hd)
  · rfl

end Patch

/-! ## SHAKE answered locally off the table points -/

section Norm

variable (p : Params) (L M : ℕ) {α : Type}

/-- **The normalized computation** (`normT` with inverse queries): a hash query at a table point
and every cipher query are made; a hash query off the table points is answered by SHAKE. -/
noncomputable def normTQ : OracleComp specP α → OracleComp specP α
  | .pure x => pure x
  | .queryBind (.inl d) k => if d ∈ TPts p L M then
      liftM (specP.query (.inl d)) >>= fun u => normTQ (k u) else normTQ (k (shakeAns d))
  | .queryBind (.inr c) k => liftM (specP.query (.inr c)) >>= fun u => normTQ (k u)

/-- The queries the normalized computation makes: hash queries at table points, cipher
queries. -/
def OnTQ : DomP → Prop
  | .inl d => d ∈ TPts p L M
  | .inr _ => True

noncomputable instance : DecidablePred (OnTQ p L M) := Classical.decPred _

variable {p L M}

lemma normTQ_inl_pos {d : Dom} (hd : d ∈ TPts p L M) (k : AnsP (.inl d) → OracleComp specP α) :
    normTQ p L M (.queryBind (.inl d) k) =
      liftM (specP.query (.inl d)) >>= fun u => normTQ p L M (k u) := by
  simp only [normTQ, hd, ite_true]

lemma normTQ_inl_neg {d : Dom} (hd : d ∉ TPts p L M) (k : AnsP (.inl d) → OracleComp specP α) :
    normTQ p L M (.queryBind (.inl d) k) = normTQ p L M (k (shakeAns d)) := by
  simp only [normTQ, hd, ite_false]

/-- **The normalized run**: on answers that are SHAKE off the table points, the run is the
computation's, and its queries are the computation's at table points and the cipher queries. -/
theorem normTQ_run (f : (d : DomP) → AnsP d) (hf : ∀ d, d ∉ TPts p L M → f (.inl d) = shakeAns d)
    (oa : OracleComp specP α) :
    runT f (normTQ p L M oa) = runT f oa ∧
      qlog f (normTQ p L M oa) = (qlog f oa).filter fun d => decide (OnTQ p L M d) := by
  induction oa with
  | pure x => exact ⟨rfl, rfl⟩
  | queryBind t k ih =>
    rcases t with d | c
    · by_cases hd : d ∈ TPts p L M
      · rw [normTQ_inl_pos hd]
        refine ⟨(ih (f (.inl d))).1, ?_⟩
        show (Sum.inl d) :: qlog f (normTQ p L M (k (f (.inl d)))) = _
        rw [(ih _).2]
        show _ = List.filter _ ((Sum.inl d) :: qlog f (k (f (.inl d))))
        exact (List.filter_cons_of_pos (p := fun d => decide (OnTQ p L M d))
          (decide_eq_true (show OnTQ p L M (.inl d) from hd))).symm
      · rw [normTQ_inl_neg hd]
        have hf' : f (.inl d) = shakeAns d := hf d hd
        refine ⟨?_, ?_⟩
        · show runT f (normTQ p L M (k (shakeAns d))) = runT f (k (f (.inl d)))
          rw [hf']
          exact (ih _).1
        · show qlog f (normTQ p L M (k (shakeAns d))) =
            List.filter _ ((Sum.inl d) :: qlog f (k (f (.inl d))))
          rw [List.filter_cons_of_neg (p := fun d => decide (OnTQ p L M d))
            (by rw [decide_eq_true_eq]; exact hd), hf']
          exact (ih _).2
    · refine ⟨(ih (f (.inr c))).1, ?_⟩
      show (Sum.inr c) :: qlog f (normTQ p L M (k (f (.inr c)))) = _
      rw [(ih _).2]
      show _ = List.filter _ ((Sum.inr c) :: qlog f (k (f (.inr c))))
      exact (List.filter_cons_of_pos (p := fun d => decide (OnTQ p L M d))
        (decide_eq_true (show OnTQ p L M (.inr c) from trivial))).symm

/-- **The normalized computation queries only table points and the cipher.** -/
theorem allQueriesSatisfy_normTQ (oa : OracleComp specP α) :
    AllQueriesSatisfy (normTQ p L M oa) (OnTQ p L M) := by
  induction oa with
  | pure x => exact allQueriesSatisfy_pure _ _
  | queryBind t k ih =>
    rcases t with d | c
    · by_cases hd : d ∈ TPts p L M
      · rw [normTQ_inl_pos hd]
        exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨hd, fun u => ih u⟩
      · rw [normTQ_inl_neg hd]
        exact ih _
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨trivial, fun u => ih u⟩

/-- The normalized computation keeps every query bound of a class. -/
theorem isQueryBoundP_normTQ {P : DomP → Prop} [DecidablePred P] {oa : OracleComp specP α}
    {n : ℕ} (h : IsQueryBoundP oa P n) : IsQueryBoundP (normTQ p L M oa) P n := by
  induction oa generalizing n with
  | pure x => trivial
  | queryBind t k ih =>
    have h' := (isQueryBoundP_query_bind_iff P t k n).1 h
    rcases t with d | c
    · by_cases hd : d ∈ TPts p L M
      · rw [normTQ_inl_pos hd]
        exact (isQueryBoundP_query_bind_iff P _ _ n).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩
      · rw [normTQ_inl_neg hd]
        exact ih _ ((h'.2 _).mono (by split <;> omega))
    · exact (isQueryBoundP_query_bind_iff P _ _ n).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩

/-- The normalized computation keeps the per-kind hash bounds. -/
theorem isKindQueryBoundP_normTQ {oa : OracleComp specP α} {q : Kind → ℕ}
    (h : IsKindQueryBoundP oa q) : IsKindQueryBoundP (normTQ p L M oa) q := by
  induction oa generalizing q with
  | pure x => trivial
  | queryBind t k ih =>
    have h' := (isQueryBound_query_bind_iff t k q _ _).1 h
    rcases t with d | c
    · by_cases hd : d ∈ TPts p L M
      · rw [normTQ_inl_pos hd]
        exact (isQueryBound_query_bind_iff _ _ q _ _).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩
      · rw [normTQ_inl_neg hd]
        refine ih _ ((show IsKindQueryBoundP (k (shakeAns d)) (Function.update q d.1 (q d.1 - 1))
          from h'.2 _).mono fun k' => ?_)
        by_cases hk : k' = d.1
        · subst hk; simp
        · simp [Function.update_of_ne hk]
    · exact (isQueryBound_query_bind_iff _ _ q _ _).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩

/-- **A computation whose hash queries all have kinds in `K` makes at most `Σ_{k ∈ K} q k` hash
queries** (permutation model). -/
theorem isQueryBoundP_left_of_kindsP {K : Finset Kind} {oa : OracleComp specP α} {q : Kind → ℕ}
    (hK : AllQueriesSatisfy oa fun t => match t with | .inl d => d.1 ∈ K | .inr _ => True)
    (h : IsKindQueryBoundP oa q) :
    IsQueryBoundP oa (fun t => t.isLeft = true) (∑ k ∈ K, q k) := by
  classical
  induction oa generalizing q with
  | pure x => trivial
  | queryBind t k ih =>
    obtain ⟨ht, hk⟩ := (allQueriesSatisfy_query_bind_iff t k _).1 hK
    have h' := (isQueryBound_query_bind_iff t k q _ _).1 h
    rcases t with d | c
    · have hd : d.1 ∈ K := ht
      have hpos : 0 < q d.1 := h'.1
      have hsum : ∑ j ∈ K, Function.update q d.1 (q d.1 - 1) j = ∑ j ∈ K, q j - 1 := by
        rw [Finset.sum_update_of_mem hd, ← Finset.add_sum_erase K q hd,
          Finset.sdiff_singleton_eq_erase]
        omega
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr ?_, fun u => ?_⟩
      · exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hd)
      · have := ih u (hk u) (h'.2 u)
        rw [hsum] at this
        simpa using this
    · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp), fun u => ?_⟩
      simpa using ih u (hk u) (h'.2 u)

/-- **The normalized computation is within the total budget `totK M q`.** -/
theorem qBudPT_normTQ {oa : OracleComp specP α} {q : Kind → ℕ} {qE : ℕ} (h : QBudP q qE oa) :
    QBudPT q qE (totK M q) (normTQ p L M oa) := by
  refine ⟨⟨isKindQueryBoundP_normTQ h.1, isQueryBoundP_normTQ h.2⟩, ?_⟩
  refine isQueryBoundP_left_of_kindsP ?_ (isKindQueryBoundP_normTQ h.1)
  refine (allQueriesSatisfy_normTQ oa).mono ?_
  rintro (d | c) hd
  · exact kind_mem_of_TPts hd
  · trivial

/-- **On the tables, the normalized run is the computation's**, with the queries at table points
and the cipher queries. -/
theorem normTQ_ansQ (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M))
    (oa : OracleComp specP α) :
    runT (ansQ g₁ g₂ t) (normTQ p L M oa) = runT (ansQ g₁ g₂ t) oa ∧
      qlog (ansQ g₁ g₂ t) (normTQ p L M oa) =
        (qlog (ansQ g₁ g₂ t) oa).filter fun d => decide (OnTQ p L M d) :=
  normTQ_run _ (fun _ hd => tabP_off g₁ g₂ t hd) oa

end Norm

end VoleMole.Theft
