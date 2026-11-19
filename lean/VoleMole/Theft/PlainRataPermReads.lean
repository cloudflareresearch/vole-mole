import VoleMole.Theft.PlainRataPerm
import VoleMole.Theft.PlainRataReads

/-!
# The read budget of `ROM/`'s extractor with inverse queries (Ratatouille)

`noTheft_lean_romP` (`Theft/PlainRataPerm.lean`) has the read budget `hX` of its extractor
`extRomP A q qE` as a hypothesis. Here it is proved, as `stageBudgetX_extRom`
(`Theft/PlainRataReads.lean`) for function rows:

* `runs_congrG`, `card_runs_leG`: `runs_congr`, `card_runs_le` for any oracle.
* `romRowsP`: the rows `eRomP` reads besides its input: the keys of the forward and inverse
  queries (`decEP`), the reconstruction's rows (`treeRows`) and the zero key's (`zeroRow`).
  **`eRomP_congr`**: `eRomP` reads neither the slices nor `H₅`, and the permutations only in
  `romRowsP` (an inverse query `(k, y)` reads `π_k⁻¹`, i.e. the row `k`).
* **`stageBudgetX_extRomP`**: `extRomP` reads each `H₃` slice at `q h3` keys, `H₅` at
  `q h5 + 624` and the permutation table at `qE + cells(pS) + cells(pI) + 4608` rows.
* **`noTheft_lean_romP'`**: `noTheft_lean_romP` without `hX`:

      Pr[Bad] ≤ εROPm(pI; q') + εROPm(pS; q') + δ_S + ε_rom
        + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

  `q' = (2·q h3, 2·q h5 + 1560, 2·q_E + 211958)`, for `q_E + 202743 < 2¹²⁸`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## Three runs that read a component, any oracle -/

section Runs

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β₂ β₁ : Type} {K : Type} [DecidableEq K]

/-- **Three runs agree** when their answers agree at every query whose key (`dec`) is in `Q`
(`runs_congr` for any oracle). -/
lemma runs_congrG (dec : ι → Option K) (Q : Finset K) {f₀ f f₀' f' : (d : ι) → spec d}
    (oa₂ : OracleComp spec β₂) (oa₁ : OracleComp spec β₁) (oa : OracleComp spec α)
    (hQ : ((qlog f₀ oa₂ ++ (qlog f₀ oa₁ ++ qlog f oa)).filterMap dec).toFinset ⊆ Q)
    (h₀ : ∀ d, (∀ k, dec d = some k → k ∈ Q) → f₀ d = f₀' d)
    (h : ∀ d, (∀ k, dec d = some k → k ∈ Q) → f d = f' d) :
    qlog f₀' oa₂ ++ (qlog f₀' oa₁ ++ qlog f' oa) = qlog f₀ oa₂ ++ (qlog f₀ oa₁ ++ qlog f oa) ∧
      runT f' oa = runT f oa := by
  have hm : ∀ d ∈ qlog f₀ oa₂ ++ (qlog f₀ oa₁ ++ qlog f oa), ∀ k, dec d = some k → k ∈ Q :=
    fun d hd k hk => hQ (mem_decG hd hk)
  have e₂ := runT_congr oa₂ f₀ f₀' fun d hd => h₀ d (hm d (by simp [hd]))
  have e₁ := runT_congr oa₁ f₀ f₀' fun d hd => h₀ d (hm d (by simp [hd]))
  have e := runT_congr oa f f' fun d hd => h d (hm d (by simp [hd]))
  exact ⟨by rw [e₂.1, e₁.1, e.1], e.2⟩

/-- **The keys of three runs' queries**, from their query bounds (any oracle). -/
lemma card_runs_leG (dec : ι → Option K) (P : ι → Bool)
    (hdec : ∀ d k, dec d = some k → P d = true) (f₀ f : (d : ι) → spec d)
    {oa₂ : OracleComp spec β₂} {oa₁ : OracleComp spec β₁} {oa : OracleComp spec α} {n₂ n₁ n : ℕ}
    (h₂ : IsQueryBoundP oa₂ (fun d => P d = true) n₂)
    (h₁ : IsQueryBoundP oa₁ (fun d => P d = true) n₁) (h : IsQueryBoundP oa (fun d => P d = true) n) :
    ((qlog f₀ oa₂ ++ (qlog f₀ oa₁ ++ qlog f oa)).filterMap dec).toFinset.card ≤ n₂ + n₁ + n := by
  have hc : ∀ l : List ι, l.countP (fun d => (dec d).isSome) ≤ l.countP P :=
    fun l => List.countP_mono_left fun d _ hd => by
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (by simpa using hd)
      exact hdec d k hk
  refine (card_toFinset_filterMap_le _ _).trans ?_
  rw [List.countP_append, List.countP_append]
  have a₂ := (hc _).trans (countP_qlog_le oa₂ f₀ P h₂)
  have a₁ := (hc _).trans (countP_qlog_le oa₁ f₀ P h₁)
  have a := (hc _).trans (countP_qlog_le oa f P h)
  omega

end Runs

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

variable {L M : ℕ} {G S : Type}

/-! ## The rows `eRomP` reads -/

/-- The cells of the queries have the queries' keys. -/
lemma filterMap_decE_toIC (π : PTable) (qs : List DomP) :
    (qs.map (toIC π)).filterMap decE = qs.filterMap decEP := by
  induction qs with
  | nil => rfl
  | cons d qs ih =>
    rcases d with d | ⟨b, c⟩
    · exact ih
    · cases b <;> exact congrArg (List.cons _) ih

/-- **The rows `eRomP` reads**: the keys of the cipher queries, the reconstruction's rows and the
zero key's row. -/
noncomputable def romRowsP (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows)
    (qs : List DomP) (π : PTable) (x : XTab L M) : Finset Blk :=
  romRows A op (qs.map (toIC π)) (fnRows π) x

lemma romRowsP_eq (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows) (qs : List DomP)
    (π : PTable) (x : XTab L M) :
    romRowsP A op qs π x = insert zeroRow ((qs.filterMap decEP).toFinset ∪
      treeRows (fnRows π) (ivOf (hbX x) ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩
          ((Hit.Rata.fd A op).1.mu1 (hbX x)))
        (Proof.opening ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩)
        (Proof.delta ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩)) := by
  unfold romRowsP romRows
  rw [filterMap_decE_toIC]

lemma card_romRowsP_le (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows) (qs : List DomP)
    (π : PTable) (x : XTab L M) :
    (romRowsP A op qs π x).card ≤ (qs.filterMap decEP).toFinset.card + 4608 := by
  have h := card_romRows_le A op (qs.map (toIC π)) (fnRows π) x
  rw [filterMap_decE_toIC] at h
  exact h

/-- The cells of the queries on two permutation tables that agree at the queries' keys. -/
lemma map_toIC_congr {π π' : PTable} {qs : List DomP}
    (h : ∀ k ∈ (qs.filterMap decEP).toFinset, π k = π' k) :
    qs.map (toIC π') = qs.map (toIC π) := by
  refine List.map_congr_left fun d hd => ?_
  rcases d with d | ⟨b, c⟩
  · rfl
  · cases b
    · show Sum.inr (c.1, (π' c.1).symm c.2) = Sum.inr (c.1, (π c.1).symm c.2)
      rw [h c.1 (mem_decG hd rfl)]
    · rfl

/-- **`eRomP` reads neither the slices nor `H₅`, and the permutations only in `romRowsP`.** -/
theorem eRomP_congr (A : Thief Sizes.labelRows G S)
    (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows))
    (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows)) (op : Op Sizes.labelRows)
    (qs : List DomP) (g₁ g₂ g₁' g₂' : Tab3) (G5 G5' : Tab5F) {π π' : PTable}
    (x : XTab L M) (h : ∀ k ∈ romRowsP A op qs π x, π k = π' k) :
    eRomP A p₁ p₂ op qs g₁' g₂' ((G5', π'), x) = eRomP A p₁ p₂ op qs g₁ g₂ ((G5, π), x) := by
  have hq : qs.map (toIC π') = qs.map (toIC π) := map_toIC_congr fun k hk =>
    h k (by rw [romRowsP_eq]; exact mem_insert_of_mem (mem_union_left _ hk))
  show eRom A p₁ p₂ op (qs.map (toIC π')) g₁' g₂' ((G5', fnRows π'), x) =
    eRom A p₁ p₂ op (qs.map (toIC π)) g₁ g₂ ((G5, fnRows π), x)
  rw [hq]
  exact eRom_congr A p₁ p₂ op _ g₁ g₂ g₁' g₂' G5 G5' x fun k hk =>
    congrArg (fun σ : Equiv.Perm Blk => (σ : Blk → Blk)) (h k hk)

/-! ## The extractor's read budget -/

/-- The extractor's query list on the tables `t`: the two prefixes' (forward) queries, then the
last stage's. -/
noncomputable def qsRP {α : Type} (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows))
    (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows)) (oa : OracleComp specP α)
    (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) pI (XTab L M)) : List DomP :=
  qlog (ansQ g₁ g₂ ((fun _ => 0, t.2) : ShX (Equiv.Perm Blk) pI (XTab L M))) (liftP (vQS p₂)) ++
    (qlog (ansQ g₁ g₂ ((fun _ => 0, t.2) : ShX (Equiv.Perm Blk) pI (XTab L M))) (liftP (vQI p₁)) ++
      qlog (ansQ g₁ g₂ t) oa)

lemma logQIP_eq (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows)) (g₁ g₂ : Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L M) :
    logQIP p₁ g₁ g₂ b =
      qlog (ansQ g₁ g₂ ((fun _ => 0, b) : ShX (Equiv.Perm Blk) pI (XTab L M))) (liftP (vQI p₁)) := by
  rw [qlog_liftP, ← logQI_eq]
  rfl

lemma logQSP_eq (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows)) (g₁ g₂ : Tab3)
    (b : (Tab5F × (Blk → Equiv.Perm Blk)) × XTab L M) :
    logQSP p₂ g₁ g₂ b =
      qlog (ansQ g₁ g₂ ((fun _ => 0, b) : ShX (Equiv.Perm Blk) pI (XTab L M))) (liftP (vQS p₂)) := by
  rw [qlog_liftP, ← logQS_eq]
  rfl

variable {L : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The read budget of `ROM/`'s extractor with inverse queries**: for an adversary whose last
stage is the run of an oracle computation within `QBudP q qE`, `extRomP` reads each `H₃` slice at
`q h3` keys, `H₅` at `q h5 + 624` and the permutation table at `qE + cells(pS) + cells(pI) + 4608`
rows. -/
theorem stageBudgetX_extRomP
    (A : Thief Sizes.labelRows Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
    {q : Kind → ℕ} {qE : ℕ} (hA : ∀ o₁ o₂, AdmL (QBudP q qE) ansQ (A.out o₁ o₂))
    (o₁ : Except Error (IssueRequest Sizes.labelRows))
    (o₂ : Except Error (SpendRequest Sizes.labelRows)) :
    StageBudgetX (extRomP A q qE (stI A o₁) (stS A o₂) (A.out o₁ o₂)) (q .h3) (q .h5 + 624)
      (qE + verifyCellBound pS + verifyCellBound pI + 4608) := by
  obtain ⟨oa, hb, he⟩ := extL_of_admL (logQ₁ := logQIP) (logQ₂ := logQSP) (e := eRomP A) (hA o₁ o₂)
  set p₁ := stI A o₁
  set p₂ := stS A o₂
  have hfun : extRomP A q qE p₁ p₂ (A.out o₁ o₂) = fun g₁ g₂ t =>
      eRomP A p₁ p₂ (runT (ansQ g₁ g₂ t) oa) (qsRP p₁ p₂ oa g₁ g₂ t) g₁ g₂ t.2 := by
    unfold extRomP
    rw [he]
    funext g₁ g₂ t
    rw [logQIP_eq, logQSP_eq]
    rfl
  rw [hfun]
  intro x
  have hS := qBudP_liftP (qBud_vQS p₂)
  have hI := qBudP_liftP (qBud_vQI p₁)
  refine ⟨fun g₂ s => ?_, fun g₁ s => ?_, fun g₁ g₂ => ?_, fun g₁ g₂ => ?_⟩
  · -- the first slice
    refine ⟨fun g₁ => ((qsRP p₁ p₂ oa g₁ g₂ (atX s x)).filterMap (dec3P false)).toFinset,
      fun g₁ => (card_runs_leG (dec3P false) (kindBP .h3) (fun _ _ => dec3P_kind) _ _
        (isQueryBoundP_kindP hS.1 .h3) (isQueryBoundP_kindP hI.1 .h3)
        (isQueryBoundP_kindP hb.1 .h3)).trans (by simp [qPre, extractorQueries, vPreQueries]),
      fun g₁ g' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runs_congrG (dec3P false) _ (f₀' := ansQ g' g₂ _)
      (f' := ansQ g' g₂ (atX s x)) (liftP (vQS p₂)) (liftP (vQI p₁)) oa subset_rfl
      (fun d hd => ansQ_h3 g₁ g₂ g' false _ d fun k hk => by simpa using hg k (hd k hk))
      (fun d hd => ansQ_h3 g₁ g₂ g' false _ d fun k hk => by simpa using hg k (hd k hk))
    show eRomP A p₁ p₂ _ (qsRP p₁ p₂ oa g' g₂ (atX s x)) _ _ _ =
      eRomP A p₁ p₂ _ (qsRP p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    unfold qsRP
    rw [e1, e2]
    rfl
  · -- the second slice
    refine ⟨fun g₂ => ((qsRP p₁ p₂ oa g₁ g₂ (atX s x)).filterMap (dec3P true)).toFinset,
      fun g₂ => (card_runs_leG (dec3P true) (kindBP .h3) (fun _ _ => dec3P_kind) _ _
        (isQueryBoundP_kindP hS.1 .h3) (isQueryBoundP_kindP hI.1 .h3)
        (isQueryBoundP_kindP hb.1 .h3)).trans (by simp [qPre, extractorQueries, vPreQueries]),
      fun g₂ g' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runs_congrG (dec3P true) _ (f₀' := ansQ g₁ g' _)
      (f' := ansQ g₁ g' (atX s x)) (liftP (vQS p₂)) (liftP (vQI p₁)) oa subset_rfl
      (fun d hd => ansQ_h3 g₁ g₂ g' true _ d fun k hk => by simpa using hg k (hd k hk))
      (fun d hd => ansQ_h3 g₁ g₂ g' true _ d fun k hk => by simpa using hg k (hd k hk))
    show eRomP A p₁ p₂ _ (qsRP p₁ p₂ oa g₁ g' (atX s x)) _ _ _ =
      eRomP A p₁ p₂ _ (qsRP p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    unfold qsRP
    rw [e1, e2]
    rfl
  · -- `H₅`
    refine ⟨fun s => ((qsRP p₁ p₂ oa g₁ g₂ (atX s x)).filterMap dec5P).toFinset,
      fun s => (card_runs_leG dec5P (kindBP .h5) (fun _ _ => dec5P_kind) _ _
        (isQueryBoundP_kindP hS.1 .h5) (isQueryBoundP_kindP hI.1 .h5)
        (isQueryBoundP_kindP hb.1 .h5)).trans
          (by simp [qPre, extractorQueries, vPreQueries]; omega),
      fun s G5 hg => ?_⟩
    obtain ⟨e1, e2⟩ := runs_congrG dec5P _
      (f₀' := ansQ g₁ g₂ ((fun _ => 0, (atX (s.1, G5, s.2.2) x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
      (f' := ansQ g₁ g₂ (atX (s.1, G5, s.2.2) x)) (liftP (vQS p₂)) (liftP (vQI p₁)) oa subset_rfl
      (fun d hd => ansQ_h5 g₁ g₂ ((fun _ => 0, (atX s x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)) G5 d fun k hk => hg k (hd k hk))
      (fun d hd => ansQ_h5 g₁ g₂ (atX s x) G5 d fun k hk => hg k (hd k hk))
    show eRomP A p₁ p₂ _ (qsRP p₁ p₂ oa g₁ g₂ (atX (s.1, G5, s.2.2) x)) _ _ _ =
      eRomP A p₁ p₂ _ (qsRP p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    unfold qsRP
    rw [e1, e2]
    exact eRomP_congr A p₁ p₂ _ _ g₁ g₂ g₁ g₂ s.2.1 G5 x fun _ _ => rfl
  · -- the permutations
    refine ⟨fun s => romRowsP A (runT (ansQ g₁ g₂ (atX s x)) oa) (qsRP p₁ p₂ oa g₁ g₂ (atX s x))
        s.2.2 x,
      fun s => (card_romRowsP_le _ _ _ _ _).trans ?_, fun s E hg => ?_⟩
    · have := card_runs_leG decEP (fun d => d.isRight) (fun _ _ => decEP_right)
        (ansQ g₁ g₂ ((fun _ => 0, (atX s x).2) :
          ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
        (ansQ g₁ g₂ (atX s x)) hS.2 hI.2 hb.2
      unfold qsRP
      omega
    have hsub : ((qsRP p₁ p₂ oa g₁ g₂ (atX s x)).filterMap decEP).toFinset ⊆
        romRowsP A (runT (ansQ g₁ g₂ (atX s x)) oa) (qsRP p₁ p₂ oa g₁ g₂ (atX s x)) s.2.2 x := by
      rw [romRowsP_eq]
      exact fun k hk => mem_insert_of_mem (mem_union_left _ hk)
    obtain ⟨e1, e2⟩ := runs_congrG decEP _
      (f₀' := ansQ g₁ g₂ ((fun _ => 0, (atX (s.1, s.2.1, E) x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
      (f' := ansQ g₁ g₂ (atX (s.1, s.2.1, E) x)) (liftP (vQS p₂)) (liftP (vQI p₁)) oa hsub
      (fun d hd => ansQ_E g₁ g₂ ((fun _ => 0, (atX s x).2) :
        ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)) E d fun k hk => hg k (hd k hk))
      (fun d hd => ansQ_E g₁ g₂ (atX s x) E d fun k hk => hg k (hd k hk))
    show eRomP A p₁ p₂ (runT (ansQ g₁ g₂ (atX (s.1, s.2.1, E) x)) oa)
        (qsRP p₁ p₂ oa g₁ g₂ (atX (s.1, s.2.1, E) x)) _ _ _ =
      eRomP A p₁ p₂ (runT (ansQ g₁ g₂ (atX s x)) oa) (qsRP p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    have e1' : qsRP p₁ p₂ oa g₁ g₂ (atX (s.1, s.2.1, E) x) = qsRP p₁ p₂ oa g₁ g₂ (atX s x) := e1
    rw [e1', e2]
    exact eRomP_congr A p₁ p₂ _ _ g₁ g₂ g₁ g₂ s.2.1 s.2.1 x hg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **No theft with permutation rows, inverse cipher queries and `ROM/`'s plain extraction,
without a read-budget hypothesis** (Ratatouille, one Client): `noTheft_lean_romP` with the
extractor's read budget proved (`stageBudgetX_extRomP`). AES as uniformly random permutations
(the hops' error `εROPm`), `M = uovM`, `L ≥ Lmin`, an adversary whose last stage is the run on the
tables of an oracle computation over `specP` with at most `q k` hash queries of kind `k` and
`q_E < 2¹²⁸ − 202743` cipher queries, forward or inverse (`hA`; no total hash budget):

    Pr[Bad] ≤ εROPm(pI; q') + εROPm(pS; q') + δ_S + ε_rom
      + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

`q' = (2·q h3, 2·q h5 + 1560, 2·q_E + 211958)`, `ε_rom = epsRomP q₀ (q_E + cells(pS) + cells(pI))
(totK uovM q₀)`, `q₀ = q + 2·qPre`. -/
theorem noTheft_lean_romP'
    (A : Thief Sizes.labelRows Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE : ℕ} (hqE : qE + 202743 < 2 ^ 128)
    (hA : ∀ o₁ o₂, AdmL (QBudP q qE) ansQ (A.out o₁ o₂)) :
    pr _ (theftReal A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
        (extRomP A q qE)) ≤
      ZKRow.εz (Equiv.Perm Blk) pI (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 211958) +
        ZKRow.εz (Equiv.Perm Blk) pS (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 211958) +
        pr _ (deltaS A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX)) +
        ((epsRomP (q + qPre + qPre) (qE + verifyCellBound pS + verifyCellBound pI)
          (totK Arith.Ratatouille.uovM (q + qPre + qPre))).toReal +
          Hit.epsHit (q .mu) (q .h21) (q .h22)) +
        owAdv A.ctx (inverter A (extRomP A q qE) leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX)) := by
  have hq : qE + verifyCellBound pS + verifyCellBound pI + 4607 < 2 ^ 128 := by
    have e : qE + verifyCellBound pS + verifyCellBound pI + 4607 = qE + 202743 := by
      rw [verifyCellBound_pI, verifyCellBound_pS]
    rw [e]; exact hqE
  have h := noTheft_lean_romP A hL hq hA fun o₁ o₂ => stageBudgetX_extRomP A hA o₁ o₂
  have e3 : q .h3 + q .h3 = 2 * q .h3 := by ring
  have e5 : q .h5 + (q .h5 + 624) + 936 = 2 * q .h5 + 1560 := by ring
  have eE : qE + (qE + verifyCellBound pS + verifyCellBound pI + 4608) + 9214 = 2 * qE + 211958 := by
    rw [verifyCellBound_pI, verifyCellBound_pS]; ring
  rw [e3, e5, eE] at h
  exact h

end Ratatouille

end VoleMole.Theft
