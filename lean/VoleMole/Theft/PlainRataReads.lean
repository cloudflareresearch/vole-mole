import VoleMole.Theft.PlainRataRom
import VoleMole.ROM.ExtractCells

/-!
# The read budget of `ROM/`'s extractor in the theft game (Ratatouille)

`noTheft_lean_rom` (`Theft/PlainRataRom.lean`) has the read budget `hX` of its extractor
`extRom A q qE nG` as a hypothesis. Here it is proved (`docs/security/ratatouille.md` §5, item 4
(d)), with the cell and row sets of `ROM/ExtractCells.lean`:

* `extL_of_admL`: on a last stage that is the run of `oa` (`AdmL`), the extractor `extL` is `e` on
  the run's output and on the queries of the two patches and of `oa`.
* `vQI`, `vQS`: the patches' prefix computations as one oracle computation each (`logQI_eq`,
  `logQS_eq`), with `QBud qPre (cells p)` (`qBud_vQI`, `qBud_vQS`).
* `romRows`: the rows `eRom` reads besides its input: the cipher keys of the query list
  (`decE`), the reconstruction's rows (`treeRows`) and the zero key's (`zeroRow`).
  **`eRom_congr`**: `eRom` reads neither the slices nor `H₅`, and the cipher only in `romRows`.
* **`stageBudgetX_extRom`**: for an adversary whose last stage is the run of an oracle
  computation within `QBudT q qE nG`, `extRom` reads each `H₃` slice at `q h3` keys, `H₅` at
  `q h5 + 624` (the adversary's and the two prefixes' `312` gate inputs each) and the cipher at
  `qE + cells(pS) + cells(pI) + 4608` rows (the adversary's and the prefixes' cells, `cells(p) =
  verifyCellBound p`, and `4607 + 1` rows for the reconstruction and the zero key).
* **`noTheft_lean_rom'`**: `noTheft_lean_rom` without `hX`:

      Pr[Bad] ≤ εz(pI; q') + εz(pS; q') + δ_S + ε_rom
        + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

  `q' = (2·q h3, 2·q h5 + 1560, 2·qE + cells(pS) + cells(pI) + 13822)`, `cells(pI) = 55292`,
  `cells(pS) = 142844` (`verifyCellBound_pI`, `verifyCellBound_pS`).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## The extractor on a realization -/

section ExtL

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {I₁ I₂ P₁ P₂ G A B Out W : Type}

/-- **On a realized last stage, `extL` is `e` on the run and its queries.** -/
lemma extL_of_admL {ans : G → G → A × B → (i : ι) → spec i} {Bud : OracleComp spec Out → Prop}
    {logQ₁ : Option (I₁ × P₁) → G → G → B → List ι} {logQ₂ : Option (I₂ × P₂) → G → G → B → List ι}
    {e : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → List ι → G → G → B → W}
    {F : G → G → A × B → Out} (h : AdmL Bud ans F) :
    ∃ oa, Bud oa ∧ ∀ p₁ p₂, extL ans Bud logQ₁ logQ₂ e p₁ p₂ F = fun g₁ g₂ s =>
      e p₁ p₂ (runT (ans g₁ g₂ s) oa)
        (logQ₂ p₂ g₁ g₂ s.2 ++ (logQ₁ p₁ g₁ g₂ s.2 ++ qlog (ans g₁ g₂ s) oa)) g₁ g₂ s.2 := by
  refine ⟨h.choose, h.choose_spec.1, fun p₁ p₂ => funext fun g₁ => funext fun g₂ => funext fun s => ?_⟩
  unfold extL
  rw [dite_eq_left h, congrFun (congrFun (congrFun h.choose_spec.2 g₁) g₂) s]

end ExtL

/-! ## Three runs that read a component -/

section Runs

variable {α : Type} {K : Type} [DecidableEq K]

/-- **Three runs agree** when their answers agree at every query whose key (`dec`) is in `Q`, and
`Q` holds the keys of their queries. -/
lemma runs_congr (dec : DomIC → Option K) (Q : Finset K) {f₀ f f₀' f' : (d : DomIC) → AnsIC d}
    (oa₂ oa₁ : OracleComp specIC ByteArray) (oa : OracleComp specIC α)
    (hQ : ((qlog f₀ oa₂ ++ (qlog f₀ oa₁ ++ qlog f oa)).filterMap dec).toFinset ⊆ Q)
    (h₀ : ∀ d, (∀ k, dec d = some k → k ∈ Q) → f₀ d = f₀' d)
    (h : ∀ d, (∀ k, dec d = some k → k ∈ Q) → f d = f' d) :
    qlog f₀' oa₂ ++ (qlog f₀' oa₁ ++ qlog f' oa) = qlog f₀ oa₂ ++ (qlog f₀ oa₁ ++ qlog f oa) ∧
      runT f' oa = runT f oa := by
  have hm : ∀ d ∈ qlog f₀ oa₂ ++ (qlog f₀ oa₁ ++ qlog f oa), ∀ k, dec d = some k → k ∈ Q :=
    fun d hd k hk => hQ (mem_dec hd hk)
  have e₂ := runT_congr oa₂ f₀ f₀' fun d hd => h₀ d (hm d (by simp [hd]))
  have e₁ := runT_congr oa₁ f₀ f₀' fun d hd => h₀ d (hm d (by simp [hd]))
  have e := runT_congr oa f f' fun d hd => h d (hm d (by simp [hd]))
  exact ⟨by rw [e₂.1, e₁.1, e.1], e.2⟩

/-- **The keys of three runs' queries**, from their query bounds. -/
lemma card_runs_le (dec : DomIC → Option K) (P : DomIC → Bool)
    (hdec : ∀ d k, dec d = some k → P d = true) (f₀ f : (d : DomIC) → AnsIC d)
    {oa₂ oa₁ : OracleComp specIC ByteArray} {oa : OracleComp specIC α} {n₂ n₁ n : ℕ}
    (h₂ : IsQueryBoundP oa₂ (fun d => P d = true) n₂)
    (h₁ : IsQueryBoundP oa₁ (fun d => P d = true) n₁) (h : IsQueryBoundP oa (fun d => P d = true) n) :
    ((qlog f₀ oa₂ ++ (qlog f₀ oa₁ ++ qlog f oa)).filterMap dec).toFinset.card ≤ n₂ + n₁ + n := by
  have hc : ∀ l : List DomIC, l.countP (fun d => (dec d).isSome) ≤ l.countP P :=
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

/-! ## The patches' queries as runs -/

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

/-- The issuance patch's prefix computation (none for no proof). -/
noncomputable def vQI : Option (IssueInstance × IssueProof Sizes.labelRows) → OracleComp specIC ByteArray
  | none => pure ByteArray.empty
  | some (x, π) => vPreIC CrtGen.tables (Privacy.Ratatouille.stI x) (bOf π)

/-- The spend patch's prefix computation (none for no proof). -/
noncomputable def vQS : Option (SpendInstance × SpendProof Sizes.labelRows) → OracleComp specIC ByteArray
  | none => pure ByteArray.empty
  | some (x, π) => vPreIC CrtGen.tables (Privacy.Ratatouille.stS x) (bOf π)

variable {R : Type} [CipherRow R] {L M : ℕ}

lemma logQI_eq (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows)) (g₁ g₂ : Tab3)
    (b : (Tab5F × (Blk → R)) × XTab L M) :
    logQI p₁ g₁ g₂ b = qlog (ansP g₁ g₂ ((fun _ => 0, b) : ShX R pI (XTab L M))) (vQI p₁) := by
  rcases p₁ with _ | ⟨x, π⟩ <;> rfl

lemma logQS_eq (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows)) (g₁ g₂ : Tab3)
    (b : (Tab5F × (Blk → R)) × XTab L M) :
    logQS p₂ g₁ g₂ b = qlog (ansP g₁ g₂ ((fun _ => 0, b) : ShX R pI (XTab L M))) (vQS p₂) := by
  rcases p₂ with _ | ⟨x, π⟩ <;> rfl

lemma qBud_vQI (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows)) :
    QBud qPre (verifyCellBound pI) (vQI p₁) := by
  rcases p₁ with _ | ⟨x, π⟩
  · exact ⟨trivial, trivial⟩
  · exact ⟨isKindQueryBoundIC_vPreIC _ _ _, isQueryBoundP_right_vPreIC _ _ _⟩

lemma qBud_vQS (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows)) :
    QBud qPre (verifyCellBound pS) (vQS p₂) := by
  rcases p₂ with _ | ⟨x, π⟩
  · exact ⟨trivial, trivial⟩
  · exact ⟨isKindQueryBoundIC_vPreIC _ _ _, isQueryBoundP_right_vPreIC _ _ _⟩

set_option maxRecDepth 100000 in
lemma verifyCellBound_pI : verifyCellBound pI = 55292 := by
  rw [verifyCellBound_eq]; decide

set_option maxRecDepth 100000 in
lemma verifyCellBound_pS : verifyCellBound pS = 142844 := by
  rw [verifyCellBound_eq]; decide

/-! ## The rows `eRom` reads -/

variable {G S : Type}

/-- The cipher entries of a query list, on two tables that agree at its cells. -/
lemma cLog_congr {E E' : CTable} {qs : List DomIC} (h : ∀ c, Sum.inr c ∈ qs → E c = E' c) :
    cLog E qs = cLog E' qs := by
  induction qs with
  | nil => rfl
  | cons d qs ih =>
    have ih' := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    rcases d with d | c
    · exact ih'
    · exact congrArg₂ List.cons (by rw [h c List.mem_cons_self]) ih'

/-- The logged keys of the cipher entries of a query list are its cells' rows. -/
lemma logKeys_cLog_subset (E : CTable) (qs : List DomIC) :
    logKeys (cLog E qs) ⊆ (qs.filterMap decE).toFinset := by
  intro k hk
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hk)
  obtain ⟨d, hd, hdy⟩ := List.mem_filterMap.1 hy
  rcases d with d | c
  · simp at hdy
  · cases hdy
    exact mem_dec hd rfl

/-- **The rows `eRom` reads**: the cells' rows of the query list, the reconstruction's rows of the
operation's proof, and the zero key's row. -/
noncomputable def romRows (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows) (qs : List DomIC)
    (E : Blk → Blk → Blk) (x : XTab L M) : Finset Blk :=
  insert zeroRow ((qs.filterMap decE).toFinset ∪
    treeRows E (ivOf (hbX x) ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩
        ((Hit.Rata.fd A op).1.mu1 (hbX x)))
      (Proof.opening ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩)
      (Proof.delta ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩))

lemma card_romRows_le (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows) (qs : List DomIC)
    (E : Blk → Blk → Blk) (x : XTab L M) :
    (romRows A op qs E x).card ≤ (qs.filterMap decE).toFinset.card + 4608 :=
  (card_insert_le _ _).trans (by
    have := (card_union_le _ _).trans (Nat.add_le_add_left (card_treeRows_le E
      (ivOf (hbX x) ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩
        ((Hit.Rata.fd A op).1.mu1 (hbX x)))
      (Proof.opening ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩)
      (Proof.delta ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩))
      (qs.filterMap decE).toFinset.card)
    omega)

/-- A known tree's candidate that is a witness of the operation, if there is one (`eRom`'s
choice). -/
noncomputable def pickW (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows)
    (K : Finset (Fin BAVC.tau)) (c : Fin BAVC.tau → ℕ → Arith.GF128) : Wit := by
  classical
  exact if h : ∃ i ∈ K, RelOp A op (witOfCand (c i)) then witOfCand (c h.choose) else witOfCand 0

/-- `eRom` from its known trees and candidates. -/
lemma eRom_eq (A : Thief Sizes.labelRows G S) (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows))
    (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows)) (op : Op Sizes.labelRows)
    (qs : List DomIC) (g₁ g₂ : Tab3) (G5 : Tab5F) (E : Blk → Blk → Blk) (x : XTab L M) :
    eRom A p₁ p₂ op qs g₁ g₂ ((G5, E), x) = pickW A op
      (rOut (Hit.Rata.fd A op).1 (Hit.Rata.fd A op).2 (hbX x) (ctOf E) (cLog (ctOf E) qs)).2.1.known
      (candOf (ctOf E) (Hit.Rata.fd A op).1
        (rOut (Hit.Rata.fd A op).1 (Hit.Rata.fd A op).2 (hbX x) (ctOf E) (cLog (ctOf E) qs))) :=
  rfl

/-- **`eRom` reads neither the slices nor `H₅`, and the cipher only in `romRows`.** -/
theorem eRom_congr (A : Thief Sizes.labelRows G S)
    (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows))
    (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows)) (op : Op Sizes.labelRows)
    (qs : List DomIC) (g₁ g₂ g₁' g₂' : Tab3) (G5 G5' : Tab5F) {E E' : Blk → Blk → Blk}
    (x : XTab L M) (h : ∀ k ∈ romRows A op qs E x, E k = E' k) :
    eRom A p₁ p₂ op qs g₁' g₂' ((G5', E'), x) = eRom A p₁ p₂ op qs g₁ g₂ ((G5, E), x) := by
  rw [eRom_eq, eRom_eq]
  have hc : cLog (ctOf E') qs = cLog (ctOf E) qs :=
    (cLog_congr fun c hc => by
      show E c.1 c.2 = E' c.1 c.2
      rw [h c.1 (mem_insert_of_mem (mem_union_left _ (mem_dec hc rfl)))]).symm
  rw [hc]
  unfold romRows at h
  generalize Hit.Rata.fd A op = f at h ⊢
  generalize cLog (ctOf E) qs = log at hc ⊢
  have hsub : logKeys log ⊆ (qs.filterMap decE).toFinset := hc ▸ logKeys_cLog_subset _ _
  have hrows : ∀ c : Cell, c.1 ∈ extractRows log (ctOf E).cipher
      (ivOf (hbX x) ⟨f.1.params, f.2⟩ (f.1.mu1 (hbX x))) (Proof.opening ⟨f.1.params, f.2⟩)
      (Proof.delta ⟨f.1.params, f.2⟩) → ctOf E c = ctOf E' c := by
    intro c hc
    show E c.1 c.2 = E' c.1 c.2
    refine congrFun (h c.1 ?_) c.2
    rcases mem_insert.1 hc with hc | hc
    · exact hc ▸ mem_insert_self _ _
    · rcases mem_union.1 hc with hc | hc
      · exact mem_insert_of_mem (mem_union_left _ (hsub hc))
      · exact mem_insert_of_mem (mem_union_right _ hc)
  obtain ⟨hk, hkn, hu⟩ := extract_congr_rows hrows
  have hr : rOut f.1 f.2 (hbX x) (ctOf E') log = rOut f.1 f.2 (hbX x) (ctOf E) log := by
    unfold rOut
    rw [← hk, ← hkn]
  rw [hr]
  generalize hR : rOut f.1 f.2 (hbX x) (ctOf E) log = r
  have hu' : ∀ (i : Fin BAVC.tau) (j : ℕ), @uBit (icPrg (ctOf E').cipher) f.1.params (outChain r).iv
      ((outChain r).corr f.1) (outChain r).keys i j =
      @uBit (icPrg (ctOf E).cipher) f.1.params (outChain r).iv ((outChain r).corr f.1)
        (outChain r).keys i j := by
    intro i j
    subst hR
    have := hu f.1.params (ivOf (hbX x) ⟨f.1.params, f.2⟩ (f.1.mu1 (hbX x)))
      ((outChain (rOut f.1 f.2 (hbX x) (ctOf E) log)).corr f.1) i j
    rw [← hk] at this
    exact this.symm
  have hcand : candOf (ctOf E') f.1 r = candOf (ctOf E) f.1 r := by
    funext i
    unfold candOf Chain.u
    simp only [hu']
  rw [hcand]

/-! ## The extractor's read budget -/

/-- The extractor's query list on the tables `t`: the two prefixes' queries (on the tables with
`H₂³` zero, as `logQI`, `logQS`), then the last stage's. -/
noncomputable def qsR {α : Type} {L M : ℕ} (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows))
    (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows)) (oa : OracleComp specIC α)
    (g₁ g₂ : Tab3) (t : ShX (Blk → Blk) pI (XTab L M)) : List DomIC :=
  qlog (ansP g₁ g₂ ((fun _ => 0, t.2) : ShX (Blk → Blk) pI (XTab L M))) (vQS p₂) ++
    (qlog (ansP g₁ g₂ ((fun _ => 0, t.2) : ShX (Blk → Blk) pI (XTab L M))) (vQI p₁) ++
      qlog (ansP g₁ g₂ t) oa)

variable {L : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The read budget of `ROM/`'s extractor in the theft game**: for an adversary whose last stage
is the run of an oracle computation within `QBudT q qE nG`, `extRom` reads each `H₃` slice at
`q h3` keys, `H₅` at `q h5 + 624` (the last stage's and the two prefixes' `312` gate inputs) and
the cipher at `qE + cells(pS) + cells(pI) + 4608` rows (the last stage's and the prefixes' cells,
the reconstruction's `4607` rows and the zero key's). -/
theorem stageBudgetX_extRom
    (A : Thief Sizes.labelRows Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
    {q : Kind → ℕ} {qE nG : ℕ} (hA : ∀ o₁ o₂, AdmL (QBudT q qE nG) ansP (A.out o₁ o₂))
    (o₁ : Except Error (IssueRequest Sizes.labelRows))
    (o₂ : Except Error (SpendRequest Sizes.labelRows)) :
    StageBudgetX (extRom A q qE nG (stI A o₁) (stS A o₂) (A.out o₁ o₂)) (q .h3) (q .h5 + 624)
      (qE + verifyCellBound pS + verifyCellBound pI + 4608) := by
  obtain ⟨oa, hb, he⟩ := extL_of_admL (logQ₁ := logQI) (logQ₂ := logQS) (e := eRom A) (hA o₁ o₂)
  set p₁ := stI A o₁
  set p₂ := stS A o₂
  have hfun : extRom A q qE nG p₁ p₂ (A.out o₁ o₂) = fun g₁ g₂ t =>
      eRom A p₁ p₂ (runT (ansP g₁ g₂ t) oa) (qsR p₁ p₂ oa g₁ g₂ t) g₁ g₂ t.2 := by
    unfold extRom
    rw [he]
    funext g₁ g₂ t
    rw [logQI_eq, logQS_eq]
    rfl
  rw [hfun]
  intro x
  have hS := qBud_vQS p₂
  have hI := qBud_vQI p₁
  refine ⟨fun g₂ s => ?_, fun g₁ s => ?_, fun g₁ g₂ => ?_, fun g₁ g₂ => ?_⟩
  · -- the first slice
    refine ⟨fun g₁ => ((qsR p₁ p₂ oa g₁ g₂ (atX s x)).filterMap (dec3 false)).toFinset,
      fun g₁ => (card_runs_le (dec3 false) (kindB .h3) (fun _ _ => dec3_kind) _ _
        (isQueryBoundP_kind hS.1 .h3) (isQueryBoundP_kind hI.1 .h3)
        (isQueryBoundP_kind hb.1.1 .h3)).trans (by simp [qPre, extractorQueries, vPreQueries]),
      fun g₁ g' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runs_congr (dec3 false) _ (f₀' := ansP g' g₂ _) (f' := ansP g' g₂ (atX s x))
      (vQS p₂) (vQI p₁) oa subset_rfl
      (fun d hd => ansP_h3 g₁ g₂ g' false _ d fun k hk => by simpa using hg k (hd k hk))
      (fun d hd => ansP_h3 g₁ g₂ g' false _ d fun k hk => by simpa using hg k (hd k hk))
    show eRom A p₁ p₂ _ (qsR p₁ p₂ oa g' g₂ (atX s x)) _ _ _ = eRom A p₁ p₂ _ (qsR p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    unfold qsR
    rw [e1, e2]
    rfl
  · -- the second slice
    refine ⟨fun g₂ => ((qsR p₁ p₂ oa g₁ g₂ (atX s x)).filterMap (dec3 true)).toFinset,
      fun g₂ => (card_runs_le (dec3 true) (kindB .h3) (fun _ _ => dec3_kind) _ _
        (isQueryBoundP_kind hS.1 .h3) (isQueryBoundP_kind hI.1 .h3)
        (isQueryBoundP_kind hb.1.1 .h3)).trans (by simp [qPre, extractorQueries, vPreQueries]),
      fun g₂ g' hg => ?_⟩
    obtain ⟨e1, e2⟩ := runs_congr (dec3 true) _ (f₀' := ansP g₁ g' _) (f' := ansP g₁ g' (atX s x))
      (vQS p₂) (vQI p₁) oa subset_rfl
      (fun d hd => ansP_h3 g₁ g₂ g' true _ d fun k hk => by simpa using hg k (hd k hk))
      (fun d hd => ansP_h3 g₁ g₂ g' true _ d fun k hk => by simpa using hg k (hd k hk))
    show eRom A p₁ p₂ _ (qsR p₁ p₂ oa g₁ g' (atX s x)) _ _ _ = eRom A p₁ p₂ _ (qsR p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    unfold qsR
    rw [e1, e2]
    rfl
  · -- `H₅`
    refine ⟨fun s => ((qsR p₁ p₂ oa g₁ g₂ (atX s x)).filterMap dec5).toFinset,
      fun s => (card_runs_le dec5 (kindB .h5) (fun _ _ => dec5_kind) _ _
        (isQueryBoundP_kind hS.1 .h5) (isQueryBoundP_kind hI.1 .h5)
        (isQueryBoundP_kind hb.1.1 .h5)).trans (by simp [qPre, extractorQueries, vPreQueries]; omega),
      fun s G5 hg => ?_⟩
    obtain ⟨e1, e2⟩ := runs_congr dec5 _
      (f₀' := ansP g₁ g₂ ((fun _ => 0, (atX (s.1, G5, s.2.2) x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
      (f' := ansP g₁ g₂ (atX (s.1, G5, s.2.2) x)) (vQS p₂) (vQI p₁) oa subset_rfl
      (fun d hd => ansP_h5 g₁ g₂ ((fun _ => 0, (atX s x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)) G5 d fun k hk => hg k (hd k hk))
      (fun d hd => ansP_h5 g₁ g₂ (atX s x) G5 d fun k hk => hg k (hd k hk))
    show eRom A p₁ p₂ _ (qsR p₁ p₂ oa g₁ g₂ (atX (s.1, G5, s.2.2) x)) _ _ _ =
      eRom A p₁ p₂ _ (qsR p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    unfold qsR
    rw [e1, e2]
    exact eRom_congr A p₁ p₂ _ _ g₁ g₂ g₁ g₂ s.2.1 G5 x fun _ _ => rfl
  · -- the cipher
    refine ⟨fun s => romRows A (runT (ansP g₁ g₂ (atX s x)) oa) (qsR p₁ p₂ oa g₁ g₂ (atX s x)) s.2.2 x,
      fun s => (card_romRows_le _ _ _ _ _).trans ?_, fun s E hg => ?_⟩
    · have := card_runs_le decE (fun d => d.isRight) (fun _ _ => decE_right)
        (ansP g₁ g₂ ((fun _ => 0, (atX s x).2) : ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
        (ansP g₁ g₂ (atX s x)) hS.2 hI.2 hb.1.2
      unfold qsR
      omega
    obtain ⟨e1, e2⟩ := runs_congr decE _
      (f₀' := ansP g₁ g₂ ((fun _ => 0, (atX (s.1, s.2.1, E) x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
      (f' := ansP g₁ g₂ (atX (s.1, s.2.1, E) x)) (vQS p₂) (vQI p₁) oa
      (fun k hk => mem_insert_of_mem (mem_union_left _ hk))
      (fun d hd => ansP_E g₁ g₂ ((fun _ => 0, (atX s x).2) :
        ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)) E d fun k hk => hg k (hd k hk))
      (fun d hd => ansP_E g₁ g₂ (atX s x) E d fun k hk => hg k (hd k hk))
    show eRom A p₁ p₂ (runT (ansP g₁ g₂ (atX (s.1, s.2.1, E) x)) oa)
        (qsR p₁ p₂ oa g₁ g₂ (atX (s.1, s.2.1, E) x)) _ _ _ =
      eRom A p₁ p₂ (runT (ansP g₁ g₂ (atX s x)) oa) (qsR p₁ p₂ oa g₁ g₂ (atX s x)) _ _ _
    have e1' : qsR p₁ p₂ oa g₁ g₂ (atX (s.1, s.2.1, E) x) = qsR p₁ p₂ oa g₁ g₂ (atX s x) := e1
    rw [e1', e2]
    exact eRom_congr A p₁ p₂ _ _ g₁ g₂ g₁ g₂ s.2.1 s.2.1 x hg

/-- **No theft with `ROM/`'s plain extraction, without a read-budget hypothesis** (Ratatouille,
one Client): `noTheft_lean_rom` with the extractor's read budget proved (`stageBudgetX_extRom`).
Function rows, `M = uovM`, `L ≥ Lmin`, an adversary whose last stage is the run on the tables of an
oracle computation with at most `q k` hash queries of kind `k`, `nG` in all and `q_E` cipher cells
(`hA`), and `ROM/`'s straight-line extractor (`extRom`):

    Pr[Bad] ≤ εz(pI; q') + εz(pS; q') + δ_S + ε_rom
      + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

`q' = (2·q h3, 2·q h5 + 1560, 2·q_E + 211958)` and `ε_rom = epsRom (q + 2·qPre)
(q_E + cells(pS) + cells(pI)) (nG + 2·338)`. -/
theorem noTheft_lean_rom'
    (A : Thief Sizes.labelRows Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE nG : ℕ}
    (hA : ∀ o₁ o₂, AdmL (QBudT q qE nG) ansP (A.out o₁ o₂)) :
    pr _ (theftReal A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
        (extRom A q qE nG)) ≤
      ZKRow.εz (Blk → Blk) pI (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 211958) +
        ZKRow.εz (Blk → Blk) pS (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 211958) +
        pr _ (deltaS A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX)) +
        ((epsRom (q + qPre + qPre) (qE + verifyCellBound pS + verifyCellBound pI)
          (nG + 338 + 338)).toReal + Hit.epsHit (q .mu) (q .h21) (q .h22)) +
        owAdv A.ctx (inverter A (extRom A q qE nG) leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX)) := by
  have h := noTheft_lean_rom A hL hA fun o₁ o₂ => stageBudgetX_extRom A hA o₁ o₂
  have e3 : q .h3 + q .h3 = 2 * q .h3 := by ring
  have e5 : q .h5 + (q .h5 + 624) + 936 = 2 * q .h5 + 1560 := by ring
  have eE : qE + (qE + verifyCellBound pS + verifyCellBound pI + 4608) + 9214 = 2 * qE + 211958 := by
    rw [verifyCellBound_pI, verifyCellBound_pS]; ring
  rw [e3, e5, eE] at h
  exact h

end Ratatouille

end VoleMole.Theft
