import VoleMole.Theft.PlainOracle

/-!
# No theft with plain extraction from the adversary's query log

`noTheft_leanX_hit` (`Theft/HitTheft.lean`) keeps plain extraction `PlainSE` as a hypothesis, for
an extractor `extOf e` that sees neither `H₂³` nor the adversary's queries, against last stages
with certificate-size read budgets. Here the theorem is restated in the shape of `ROM/`'s
extraction bounds (`docs/security/ratatouille.md` §5, items 1–3):

* the adversary's last stage is the run on the tables of an oracle computation over `specIC`
  (hash queries of every kind, **cipher cells**) with query bounds `QBud q q_E`
  (`Theft/PlainOracle.lean`); its read budgets and its decision trees on the chain tables follow
  (`stageBudgetX_runT`, `admHit_runT`);
* the extractor `extLR e` is `e` on the **list of queries** of the programming step's reduction:
  the queries that recompute the simulated proofs' grinding prefixes (`vPreIC`), then those of
  the adversary's last stage (`extL`);
* plain extraction (`PlainSEL`) is against the oracle computations within the budget
  `QBud (q + 2·(extractorQueries + vPreQueries)) (q_E + cells(pS) + cells(pI))`, the reduction's.

* `progQI`, `progQS`: the simulators' patches, computed by queries (`runT_progQI`); `hpatchI`,
  `hpatchS`, `hpreI`, `hpreS`, `hlogI`, `hlogS`: the hypotheses of `weakSE2_of_plainL`.
* `distI_budgetX'`, `distS_budgetX'`: the hop budgets for any extractor on the tables with the
  extra table (`distI_budgetX` is for extractors given at each value of the extra table).
* **`noTheft_leanX_hitL`**:

      Pr[Bad] ≤ εz(pI; q') + εz(pS; q') + δ_S + ε_plain
        + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

  `q' = (q h3 + x₃, q h5 + x₅ + 936, q_E + x_E + 9214)`, with `PlainSEL` the remaining
  extraction hypothesis.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open OracleComp OracleSpec

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

variable {R : Type} [CipherRow R] {L M : ℕ}

lemma vecOf_ok_bOf {n : ℕ} {b : ByteArray} (h : b.size = n) :
    vecOf n (.ok b) = some ⟨b.data, h⟩ ∧ bOf (⟨b.data, h⟩ : Spec.Ratatouille.Bytes n) = b := by
  refine ⟨by simp [vecOf, h], ?_⟩
  simp [bOf, toBA]


/-! ## The simulators' patches -/

/-- **The issuance simulator's patch, by queries**: the programmed values at the grinding points of
the prefix recomputed from the simulated proof (`vPreIC`; the empty prefix if the simulation
fails). -/
noncomputable def progQI (x : IssueInstance) (c : SimCoins pI) :
    OracleComp specIC (K2 pI → Option (ZK.Sim.Bytes 16)) :=
  match simulate pI c with
  | .error _ => pure (mOf pI ByteArray.empty c.1.2.1)
  | .ok b => (fun pre => mOf pI pre c.1.2.1) <$>
      vPreIC CrtGen.tables (Privacy.Ratatouille.stI x) b

/-- **The spend simulator's patch, by queries.** -/
noncomputable def progQS (x : SpendInstance) (c : SimCoins pS) :
    OracleComp specIC (K2 pI → Option (ZK.Sim.Bytes 16)) :=
  match simulate pS c with
  | .error _ => pure (mOf pI ByteArray.empty c.1.2.1)
  | .ok b => (fun pre => mOf pI pre c.1.2.1) <$>
      vPreIC CrtGen.tables (Privacy.Ratatouille.stS x) b

/-- The patches' queries, from the simulated pair. -/
noncomputable def logQI : Option (IssueInstance × IssueProof Sizes.labelRows) → Tab3 → Tab3 →
    (Tab5F × (Blk → R)) × XTab L M → List DomIC
  | none, _, _, _ => []
  | some (x, π), g₁, g₂, b => qlog (ansP g₁ g₂ ((fun _ => 0, b) : ShX R pI (XTab L M)))
      (vPreIC CrtGen.tables (Privacy.Ratatouille.stI x) (bOf π))

noncomputable def logQS : Option (SpendInstance × SpendProof Sizes.labelRows) → Tab3 → Tab3 →
    (Tab5F × (Blk → R)) × XTab L M → List DomIC
  | none, _, _, _ => []
  | some (x, π), g₁, g₂, b => qlog (ansP g₁ g₂ ((fun _ => 0, b) : ShX R pI (XTab L M)))
      (vPreIC CrtGen.tables (Privacy.Ratatouille.stS x) (bOf π))

lemma runT_progQI (g₁ g₂ : Tab3) (t : ShX R pI (XTab L M)) (x : IssueInstance) (c : SimCoins pI) :
    runT (ansP g₁ g₂ t) (progQI x c) = mOf pI (@outPre (icPrg (rowFn t.2.1.2)) (hbX t.2.2)
      CrtGen.tables (Privacy.Ratatouille.stI x) t.2.1.1 (simulate pI c)) c.1.2.1 := by
  unfold progQI
  split <;> rename_i h <;> rw [h]
  · rfl
  · rw [runT_map, runT_vPreIC]
    rfl

lemma runT_progQS (g₁ g₂ : Tab3) (t : ShX R pI (XTab L M)) (x : SpendInstance) (c : SimCoins pS) :
    runT (ansP g₁ g₂ t) (progQS x c) = mOf pI (@outPre (icPrg (rowFn t.2.1.2)) (hbX t.2.2)
      CrtGen.tables (Privacy.Ratatouille.stS x) t.2.1.1 (simulate pS c)) c.1.2.1 := by
  unfold progQS
  split <;> rename_i h <;> rw [h]
  · rfl
  · rw [runT_map, runT_vPreIC]
    rfl

lemma hpatchI (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3) (t : ShX R pI (XTab L M))
    (d : DomIC) : ansP g₁ g₂ (leanProgIRX hbX x c t) d =
      patch2 pI (runT (ansP g₁ g₂ t) (progQI x c)) d (ansP g₁ g₂ t d) := by
  rw [runT_progQI]
  exact ansP_prog g₁ g₂ t _ _ d

lemma hpatchS (x : SpendInstance) (c : SimCoins pS) (g₁ g₂ : Tab3) (t : ShX R pI (XTab L M))
    (d : DomIC) : ansP g₁ g₂ (leanProgSRX hbX x c t) d =
      patch2 pI (runT (ansP g₁ g₂ t) (progQS x c)) d (ansP g₁ g₂ t d) := by
  rw [runT_progQS]
  exact ansP_prog g₁ g₂ t _ _ d

lemma hpreI (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3) (t t' : ShX R pI (XTab L M))
    (h : t'.2 = t.2) : runT (ansP g₁ g₂ t') (progQI x c) = runT (ansP g₁ g₂ t) (progQI x c) := by
  rw [runT_progQI, runT_progQI, h]

lemma hlogI (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3) (t : ShX R pI (XTab L M)) :
    qlog (ansP g₁ g₂ t) (progQI x c) = logQI (pairO (some x) (leanSimIR x c)) g₁ g₂ t.2 := by
  unfold progQI leanSimIR
  split <;> rename_i h
  · rw [h]; rfl
  · rw [h]
    obtain ⟨e1, e2⟩ := vecOf_ok_bOf (n := Sizes.labelRows.issue)
      ((simulate_ok_size h).trans (by decide))
    rw [e1]
    simp only [pairO, logQI, e2]
    rw [qlog_map, ← qlog_vPreIC_G2 g₁ g₂ t (fun _ => 0)]

lemma hlogS (x : SpendInstance) (c : SimCoins pS) (g₁ g₂ : Tab3) (t : ShX R pI (XTab L M)) :
    qlog (ansP g₁ g₂ t) (progQS x c) = logQS (pairO (some x) (leanSimSR x c)) g₁ g₂ t.2 := by
  unfold progQS leanSimSR
  split <;> rename_i h
  · rw [h]; rfl
  · rw [h]
    obtain ⟨e1, e2⟩ := vecOf_ok_bOf (n := Sizes.labelRows.spend)
      ((simulate_ok_size h).trans (by decide))
    rw [e1]
    simp only [pairO, logQS, e2]
    rw [qlog_map, ← qlog_vPreIC_G2 g₁ g₂ t (fun _ => 0)]

/-! ## The reduction's budget -/

/-- The hash queries of one patch: the prefix's. -/
def qPre : Kind → ℕ := extractorQueries + vPreQueries

lemma qBud_progQI (x : IssueInstance) (c : SimCoins pI) :
    QBud qPre (verifyCellBound pI) (progQI x c) := by
  unfold progQI
  split
  · exact ⟨trivial, trivial⟩
  · exact ⟨isQueryBound_map_iff _ _ _ _ _ |>.2 (isKindQueryBoundIC_vPreIC _ _ _),
      (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_right_vPreIC _ _ _)⟩

lemma qBud_progQS (x : SpendInstance) (c : SimCoins pS) :
    QBud qPre (verifyCellBound pS) (progQS x c) := by
  unfold progQS
  split
  · exact ⟨trivial, trivial⟩
  · exact ⟨isQueryBound_map_iff _ _ _ _ _ |>.2 (isKindQueryBoundIC_vPreIC _ _ _),
      (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_right_vPreIC _ _ _)⟩

lemma qBud_progQO {I C M' : Type} {progQ : I → C → OracleComp specIC M'} {qa : Kind → ℕ} {qb : ℕ}
    (h : ∀ x c, QBud qa qb (progQ x c)) (x : Option I) (c : C) :
    QBud qa qb (progQO progQ x c) := by
  rcases x with _ | x
  · exact ⟨trivial, trivial⟩
  · exact ⟨isQueryBound_map_iff _ _ _ _ _ |>.2 (h x c).1, (isQueryBoundP_map_iff _ _ _).2 (h x c).2⟩

/-- **The reduction's budget**: the two patches' queries, then the adversary's. -/
theorem qBud_redQ {α : Type} {q : Kind → ℕ} {qE : ℕ} {oa : OracleComp specIC α}
    (h : QBud q qE oa) (x₁ : Option IssueInstance) (c₁ : SimCoins pI) (x₂ : Option SpendInstance)
    (c₂ : SimCoins pS) :
    QBud (q + qPre + qPre) (qE + verifyCellBound pS + verifyCellBound pI)
      (redQ progQI (patch2 pI) progQS (patch2 pI) x₁ c₁ x₂ c₂ oa) := by
  have h₂ := qBud_progQO qBud_progQS x₂ c₂
  refine ⟨?_, ?_⟩
  · refine (isKindQueryBoundIC_bind h₂.1 fun m₂ => isKindQueryBoundIC_bind
      (qBud_progQO qBud_progQI x₁ c₁).1 fun m₁ => isQueryBound_simP _ h.1).mono fun k => ?_
    simp only [Pi.add_apply]
    omega
  · refine (isQueryBoundP_bind h₂.2 fun m₂ _ => isQueryBoundP_bind
      (qBud_progQO qBud_progQI x₁ c₁).2 fun m₁ _ => isQueryBoundP_simP _ h.2).mono ?_
    omega

/-! ## The hop budgets for any extractor on the tables with the extra table -/

section Hops

variable (Hb : XTab L M → Hashes) (A : Thief Sizes.labelRows Tab3 (ShX R pI (XTab L M)))
  (ext : Ext Sizes.labelRows Tab3 (ShX R pI (XTab L M))) {a3 a5 aE x3 x5 xE : ℕ}

lemma accOp_atX (op : Op Sizes.labelRows) (x : XTab L M) (s : ShR R) :
    AccOp A (leanVIRX Hb) (leanVSRX Hb) op (atX s x) =
      AccOp (atT A x) (leanVIRH (Hb x)) (leanVSRH (Hb x)) op s := by
  cases op <;> rfl

/-- **The bad event reads what the last stage, the extractor and the verifiers read**, at every
value of the extra table. -/
theorem bad_budgetX (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudgetX (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE) (x : XTab L M)
    (ω : Sec) (o₁ : Except Error (IssueRequest Sizes.labelRows))
    (o₂ : Except Error (SpendRequest Sizes.labelRows)) :
    StageBudget (fun g₁ g₂ s => Bad A (leanVIRX Hb) (leanVSRX Hb) ext ω o₁ o₂ g₁ g₂ (atX s x))
      (a3 + x3) (a5 + (x5 + 312)) (aE + (xE + 4607)) := by
  have h := (hA o₁ o₂ x).event (V := AccOp (atT A x) (leanVIRH (Hb x)) (leanVSRH (Hb x)))
    (fun op w acc => acc ∧ FreshOp A (stI A o₁) (stS A o₂) op ∧
      (¬ RelOp A op w ∨ OpensOp (K₁ A ω A.tInit) (K₂ A ω (tNext A o₁)) op w))
    (hX o₁ o₂ x) (accOp_rd5 (atT A x) _ _ (leanVIRH_rd5 (Hb x)) (leanVSRH_rd5 (Hb x)))
    (accOp_rdE (atT A x) _ _ (leanVIRH_rdE (Hb x)) (leanVSRH_rdE (Hb x)))
  have e : (fun g₁ g₂ s => Bad A (leanVIRX Hb) (leanVSRX Hb) ext ω o₁ o₂ g₁ g₂ (atX s x)) =
      fun g₁ g₂ s => (A.out o₁ o₂ g₁ g₂ (atX s x) |> fun op =>
        AccOp (atT A x) (leanVIRH (Hb x)) (leanVSRH (Hb x)) op s ∧
        FreshOp A (stI A o₁) (stS A o₂) op ∧
        (¬ RelOp A op (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂) g₁ g₂ (atX s x)) ∨
          OpensOp (K₁ A ω A.tInit) (K₂ A ω (tNext A o₁)) op
            (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂) g₁ g₂ (atX s x)))) := by
    funext g₁ g₂ s
    simp only [Bad, accE, freshE, relE, opensE, accOp_atX]
  rw [e]
  exact h

/-- **The first hop's budget**, for any extractor on the tables with the extra table. -/
theorem distI_budgetX' (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudgetX (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (ω : Sec) (r₂ : Coins 16) (g₂ : Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distI A (leanPIRX Hb) (leanPSRX Hb) (leanVIRX Hb) (leanVSRX Hb) ext ω r₂ g₂) := by
  intro x
  have hB := bad_budgetX Hb A ext hA hX x ω
  have h : Budget pI (a3 + x3) (624 + (a5 + (x5 + 312))) (4607 + (aE + (xE + 4607)))
      (fun o g s => distI A (leanPIRX Hb) (leanPSRX Hb) (leanVIRX Hb) (leanVSRX Hb) ext ω r₂ g₂ o g
        (atX s x)) := by
    refine ⟨fun o s => (hB _ _).h3₁ g₂ s, fun o G3 => ?_, fun o G3 => ?_⟩
    · exact (specS_rd5 (atT A x) (leanPIRH (Hb x)) (leanPSRH (Hb x)) (leanPSRH_rd5 (Hb x)) ω _
        r₂ g₂).bind (f := fun o₂ s => Bad A (leanVIRX Hb) (leanVSRX Hb) ext ω (reqI A (K₁ A ω) o)
          o₂ G3 g₂ (atX s x)) fun o₂ => (hB _ o₂).h5 G3 g₂
    · exact (specS_rdE (atT A x) (leanPIRH (Hb x)) (leanPSRH (Hb x)) (leanPSRH_rdE (hHb x)) ω _
        r₂ g₂).bind (f := fun o₂ s => Bad A (leanVIRX Hb) (leanVSRX Hb) ext ω (reqI A (K₁ A ω) o)
          o₂ G3 g₂ (atX s x)) fun o₂ => (hB _ o₂).hE G3 g₂
  exact h.mono le_rfl (by omega) (by omega)

/-- **The second hop's budget**, for any extractor on the tables with the extra table. -/
theorem distS_budgetX' (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudgetX (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (ω : Sec) (c₁ : SimCoins pI) (g₁ : Tab3) :
    BudgetX pS (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distS A (leanVIRX Hb) (leanVSRX Hb) ext leanSimIR (leanProgIRX Hb) ω c₁ g₁) := by
  intro x
  have hB := bad_budgetX Hb A ext hA hX x ω
  have hL := isProg_progO (fun i c => leanProgIRH_isProg (R := R) (Hb x) i c) (xIo A (K₁ A ω)) c₁
  have h : Budget pI (a3 + x3) (a5 + (x5 + 312) + 312) (aE + (xE + 4607) + 4607)
      (fun o g s => distS A (leanVIRX Hb) (leanVSRX Hb) ext leanSimIR (leanProgIRX Hb) ω c₁ g₁ o g
        (atX s x)) := by
    refine ⟨fun o s => ?_, fun o G3 => ?_, fun o G3 => ?_⟩
    · simp only [distS, D₂, pgI, leanProgIRX, progO_progX]
      exact (hB _ _).h3₂ g₁ _
    · simp only [distS, D₂, pgI, leanProgIRX, progO_progX]
      exact ((hB _ _).h5 g₁ G3).comp_prog hL
    · simp only [distS, D₂, pgI, leanProgIRX, progO_progX]
      exact ((hB _ _).hE g₁ G3).comp_prog hL
  have h' := h.mono le_rfl (q5' := a5 + x5 + 936) (qE' := aE + xE + 9214) (by omega) (by omega)
  -- (`pI` and `pS` have the same `H₂³` table type)
  exact ⟨h'.h3, h'.h5, h'.hE⟩

end Hops

/-! ## No theft -/

section Theorem

/-- **The extractor**: `e` on the reduction's queries (`extL`). -/
noncomputable def extLR (q : Kind → ℕ) (qE : ℕ)
    (e : Option (IssueInstance × IssueProof Sizes.labelRows) →
      Option (SpendInstance × SpendProof Sizes.labelRows) → Op Sizes.labelRows → List DomIC →
      Tab3 → Tab3 → (Tab5F × (Blk → R)) × XTab L M → Wit) :
    Ext Sizes.labelRows Tab3 (ShX R pI (XTab L M)) :=
  extL ansP (QBud q qE) logQI logQS e

variable [Fintype R] [Nonempty R] [ZKRow R]

/-- **No theft with the other hashes random tables, `ε_hit` bounded, and plain extraction from the
adversary's query log.** As `noTheft_leanX_hit`, for an adversary whose last stage is the run on
the tables of an oracle computation with at most `q k` hash queries of kind `k` and `q_E` cipher
cells (`hA`), and the extractor `extLR e`, which sees the queries of the programming step's
reduction (the recomputation of the simulated proofs' prefixes, then the adversary's):

    Pr[Bad] ≤ εz(pI; q') + εz(pS; q') + δ_S + ε_plain
      + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

`q' = (q h3 + x₃, q h5 + x₅ + 936, q_E + x_E + 9214)` (`x₃, x₅, x_E` the extractor's reads,
`hX`). Plain extraction (`hplain`, `PlainSEL`) is against the oracle computations within the
budget of the reduction: `q + 2·(extractorQueries + vPreQueries)` hash queries and
`q_E + cells(pS) + cells(pI)` cipher cells. -/
theorem noTheft_leanX_hitL (A : Thief Sizes.labelRows Tab3 (ShX R pI (XTab L M)))
    (hL : Hit.Rata.Lmin ≤ L)
    {e : Option (IssueInstance × IssueProof Sizes.labelRows) →
      Option (SpendInstance × SpendProof Sizes.labelRows) → Op Sizes.labelRows → List DomIC →
      Tab3 → Tab3 → (Tab5F × (Blk → R)) × XTab L M → Wit}
    {q : Kind → ℕ} {qE x3 x5 xE : ℕ} {ε₀ : ℝ}
    (hA : ∀ o₁ o₂, AdmL (QBud q qE) ansP (A.out o₁ o₂))
    (hX : ∀ o₁ o₂, StageBudgetX (extLR q qE e (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hplain : PlainSEL ansP (AccOp A (leanVIRX hbX) (leanVSRX hbX)) (FreshOp A) (RelOp A) e
      (QBud (q + qPre + qPre) (qE + verifyCellBound pS + verifyCellBound pI)) ε₀) :
    pr _ (theftReal A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
        (extLR q qE e)) ≤
      ZKRow.εz R pI (q .h3 + x3) (q .h5 + x5 + 936) (qE + xE + 9214) +
        ZKRow.εz R pS (q .h3 + x3) (q .h5 + x5 + 936) (qE + xE + 9214) +
        pr _ (deltaS A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX)) +
        (ε₀ + Hit.epsHit (q .mu) (q .h21) (q .h22)) +
        owAdv A.ctx (inverter A (extLR q qE e) leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX)) := by
  have hSB : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) (q .h3) (q .h5) qE := fun o₁ o₂ => by
    obtain ⟨oa, hb, hF⟩ := hA o₁ o₂
    rw [hF]
    exact stageBudgetX_runT hb
  have hAH : ∀ F : Tab3 → Tab3 → ShX R pI (XTab L M) → Op Sizes.labelRows,
      AdmL (QBud q qE) ansP F →
      Hit.AdmHit (R := R) (p := pI) (L := L) (M := M) (G := Tab3) (q .mu) (q .h21) (q .h22) F := by
    rintro F ⟨oa, hb, rfl⟩
    exact admHit_runT hb
  exact noTheft_ok (CI := SimCoins pI) (CS := SimCoins pS) A (leanVIRX hbX) (leanVSRX hbX)
    (extLR q qE e) leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX) (leanPIRX hbX)
    (leanPSRX hbX) (leanPIRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (leanPSRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (distI_budgetX' hbX A _ hbX_wf hSB hX) (distS_budgetX' hbX A _ hSB hX)
    (weakSE2_of_plainL progQI (patch2 pI) progQS (patch2 pI) logQI logQS
      (hplain.mono (fun _ _ _ h => Hit.Rata.FreshOk.freshOp A h) (fun _ h => h) le_rfl)
      (progMoves_of_ev (fun _ _ _ => rfl) (fun _ _ _ => rfl) (accOp_movesX hbX A)
        ((Hit.Rata.progEv_hit A hL (q .mu) (q .h21) (q .h22)).mono hAH))
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) hpatchI hpatchS
      (fun x c g₁ g₂ s s' h => hpreI x c g₁ g₂ s s' h) hlogI hlogS (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) fun oa x₁ c₁ x₂ c₂ h => qBud_redQ h x₁ c₁ x₂ c₂)
    hA

end Theorem

end Ratatouille

end VoleMole.Theft
