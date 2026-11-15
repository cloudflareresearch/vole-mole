import VoleMole.Theft.PlainRata
import VoleMole.Theft.MoussakaHit

/-!
# Redemption non-malleability with plain extraction from the adversary's query log

The Moussaka counterpart of `Theft/PlainRata.lean`: `noRedirect_leanX_hit` restated with the
adversary's last stage an oracle computation over `specIC` with query bounds (`QBud q q_E`), the
extractor `extLM e` reading the queries of the programming step's reduction (`extL`), and plain
extraction `PlainSEL` against the reduction's budget.

* `progQIm`, `progQRm`: the simulators' patches by queries. The Moussaka simulators always output
  bytes (`leanSim`: the empty string if grinding fails), so the patch always recomputes the
  prefix of the output bytes (`vPreIC`), and uses the empty prefix when the simulation failed (as
  `progRO` does).
* `distI_budgetX'`, `distR_budgetX'`: the hop budgets for any extractor on the tables with the
  extra table.
* **`noRedirect_leanX_hitL`**: as `noRedirect_leanX_hit` (`L ≥ 6293`, `HitWf`),

      Pr[Bad] ≤ εz(pI; q') + εz(pR; q') + δ_R + ε_plain
        + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

  `q' = (q h3 + x₃, q h5 + x₅ + 936, q_E + x_E + 9214)`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open OracleComp OracleSpec

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

variable {R : Type} [CipherRow R] {L M : ℕ}

/-! ## The simulators' patches -/

/-- The prefix the programming uses: the recomputed one, or the empty one if the simulation
failed. -/
def preOf {p : Params} (c : SimCoins p) (pre : ByteArray) : ByteArray :=
  match simulate p c with
  | .error _ => ByteArray.empty
  | .ok _ => pre

/-- **The issuance simulator's patch, by queries.** -/
noncomputable def progQIm (x : IssueInstance) (c : SimCoins pI) :
    OracleComp specIC (K2 pI → Option (ZK.Sim.Bytes 16)) :=
  (fun pre => mOf pI (preOf c pre) c.1.2.1) <$>
    vPreIC CrtGen.tables (Privacy.Moussaka.stI x) (toBA (leanSim pI x c))

/-- **The redemption simulator's patch, by queries.** -/
noncomputable def progQRm (x : RedeemInstance) (c : SimCoins pR) :
    OracleComp specIC (K2 pI → Option (ZK.Sim.Bytes 16)) :=
  (fun pre => mOf pI (preOf c pre) c.1.2.1) <$>
    vPreIC CrtGen.tables (Privacy.Moussaka.stR x) (toBA (leanSim pR x c))

/-- The patches' queries, from the simulated pair. -/
noncomputable def logQIm : Option (IssueInstance × Bytes) → Tab3 → Tab3 →
    (Tab5F × (Blk → R)) × XTab L M → List DomIC
  | none, _, _, _ => []
  | some (x, π), g₁, g₂, b => qlog (ansP g₁ g₂ ((fun _ => 0, b) : ShX R pI (XTab L M)))
      (vPreIC CrtGen.tables (Privacy.Moussaka.stI x) (toBA π))

noncomputable def logQRm : Option (RedeemInstance × Bytes) → Tab3 → Tab3 →
    (Tab5F × (Blk → R)) × XTab L M → List DomIC
  | none, _, _, _ => []
  | some (x, π), g₁, g₂, b => qlog (ansP g₁ g₂ ((fun _ => 0, b) : ShX R pI (XTab L M)))
      (vPreIC CrtGen.tables (Privacy.Moussaka.stR x) (toBA π))

lemma toBA_toL' (b : ByteArray) : toBA (toL b) = b := by
  rw [Privacy.toL_eq]
  cases b
  rfl

lemma outPre_preOf {p : Params} (Hb : Hashes) (st : Statement) (E : Cipher) (G5 : Tab5F)
    (c : SimCoins p) :
    @outPre (icPrg E) Hb CrtGen.tables st G5 (simulate p c) =
      preOf c (@vPre (icPrg E) (rec5 Hb G5) CrtGen.tables st (toBA (leanSim p st c))) := by
  unfold preOf leanSim
  split <;> rename_i h <;> rw [h]
  · rfl
  · show _ = @vPre (icPrg E) (rec5 Hb G5) CrtGen.tables st (toBA (toL _))
    rw [toBA_toL']
    rfl

lemma hpatchIm (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3) (t : ShX R pI (XTab L M))
    (d : DomIC) : ansP g₁ g₂ (leanProgIX hbX x c t) d =
      patch2 pI (runT (ansP g₁ g₂ t) (progQIm x c)) d (ansP g₁ g₂ t d) := by
  rw [progQIm, runT_map, runT_vPreIC]
  have e := outPre_preOf (hbX t.2.2) (Privacy.Moussaka.stI x) (rowFn t.2.1.2) t.2.1.1 c
  simp only [leanSim] at e ⊢
  rw [← e]
  exact ansP_prog g₁ g₂ t _ _ d

lemma hpatchRm (x : RedeemInstance) (c : SimCoins pR) (g₁ g₂ : Tab3) (t : ShX R pI (XTab L M))
    (d : DomIC) : ansP g₁ g₂ (leanProgRX hbX x c t) d =
      patch2 pI (runT (ansP g₁ g₂ t) (progQRm x c)) d (ansP g₁ g₂ t d) := by
  rw [progQRm, runT_map, runT_vPreIC]
  have e := outPre_preOf (hbX t.2.2) (Privacy.Moussaka.stR x) (rowFn t.2.1.2) t.2.1.1 c
  simp only [leanSim] at e ⊢
  rw [← e]
  exact ansP_prog g₁ g₂ t _ _ d

lemma hpreIm (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3) (t t' : ShX R pI (XTab L M))
    (h : t'.2 = t.2) : runT (ansP g₁ g₂ t') (progQIm x c) = runT (ansP g₁ g₂ t) (progQIm x c) := by
  rw [progQIm, runT_map, runT_map, runT_vPreIC, runT_vPreIC, h]

lemma hlogIm (x : IssueInstance) (c : SimCoins pI) (g₁ g₂ : Tab3) (t : ShX R pI (XTab L M)) :
    qlog (ansP g₁ g₂ t) (progQIm x c) =
      logQIm (pairO (some x) (simI' (leanSim pI) x c)) g₁ g₂ t.2 := by
  rw [progQIm, qlog_map, ← qlog_vPreIC_G2 g₁ g₂ t (fun _ => 0)]
  rfl

lemma hlogRm (x : RedeemInstance) (c : SimCoins pR) (g₁ g₂ : Tab3) (t : ShX R pI (XTab L M)) :
    qlog (ansP g₁ g₂ t) (progQRm x c) =
      logQRm (pairO (some x) (simR' (leanSim pR) x c)) g₁ g₂ t.2 := by
  rw [progQRm, qlog_map, ← qlog_vPreIC_G2 g₁ g₂ t (fun _ => 0)]
  rfl

/-! ## The reduction's budget -/

lemma qBud_progQIm (x : IssueInstance) (c : SimCoins pI) :
    QBud Ratatouille.qPre (verifyCellBound pI) (progQIm x c) :=
  ⟨isQueryBound_map_iff _ _ _ _ _ |>.2 (isKindQueryBoundIC_vPreIC _ _ _),
    (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_right_vPreIC _ _ _)⟩

lemma qBud_progQRm (x : RedeemInstance) (c : SimCoins pR) :
    QBud Ratatouille.qPre (verifyCellBound pR) (progQRm x c) :=
  ⟨isQueryBound_map_iff _ _ _ _ _ |>.2 (isKindQueryBoundIC_vPreIC _ _ _),
    (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_right_vPreIC _ _ _)⟩

/-- **The reduction's budget**: the two patches' queries, then the adversary's. -/
theorem qBud_redQm {α : Type} {q : Kind → ℕ} {qE : ℕ} {oa : OracleComp specIC α}
    (h : QBud q qE oa) (x₁ : Option IssueInstance) (c₁ : SimCoins pI) (x₂ : Option RedeemInstance)
    (c₂ : SimCoins pR) :
    QBud (q + Ratatouille.qPre + Ratatouille.qPre) (qE + verifyCellBound pR + verifyCellBound pI)
      (redQ progQIm (patch2 pI) progQRm (patch2 pI) x₁ c₁ x₂ c₂ oa) := by
  have h₂ := Ratatouille.qBud_progQO qBud_progQRm x₂ c₂
  refine ⟨?_, ?_⟩
  · refine (isKindQueryBoundIC_bind h₂.1 fun m₂ => isKindQueryBoundIC_bind
      (Ratatouille.qBud_progQO qBud_progQIm x₁ c₁).1 fun m₁ => isQueryBound_simP _ h.1).mono
      fun k => ?_
    simp only [Pi.add_apply]
    omega
  · refine (isQueryBoundP_bind h₂.2 fun m₂ _ => isQueryBoundP_bind
      (Ratatouille.qBud_progQO qBud_progQIm x₁ c₁).2 fun m₁ _ => isQueryBoundP_simP _ h.2).mono ?_
    omega

/-! ## The hop budgets for any extractor on the tables with the extra table -/

section Hops

variable (Hb : XTab L M → Hashes) (A : Thief Tab3 (ShX R pI (XTab L M)))
  (ext : Moussaka.Ext Tab3 (ShX R pI (XTab L M))) {a3 a5 aE x3 x5 xE : ℕ}

/-- **The bad event reads what the last stage, the extractor and the verifiers read**, at every
value of the extra table. -/
theorem bad_budgetX (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudgetX (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (x : XTab L M) (ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) :
    StageBudget (fun g₁ g₂ s => Bad A (verILX Hb) (verRLX Hb) ext ω o₁ o₂ g₁ g₂ (atX s x))
      (a3 + x3) (a5 + (x5 + 312)) (aE + (xE + 4607)) := by
  have h := (hA o₁ o₂ x).event (V := AccOp (verILH (Hb x)) (verRLH (Hb x)))
    (fun op w acc => acc ∧ FreshOp (stI A o₁) (stR A o₁ o₂) op ∧
      (¬ RelOp op w ∨ OpensOp (tOf A ω) op w))
    (hX o₁ o₂ x) (accOp_rd5 _ _ (verILH_rd5 (Hb x)) (verRLH_rd5 (Hb x)))
    (accOp_rdE _ _ (verILH_rdE (Hb x)) (verRLH_rdE (Hb x)))
  have e : (fun g₁ g₂ s => Bad A (verILX Hb) (verRLX Hb) ext ω o₁ o₂ g₁ g₂ (atX s x)) =
      fun g₁ g₂ s => (A.out o₁ o₂ g₁ g₂ (atX s x) |> fun op =>
        AccOp (verILH (Hb x)) (verRLH (Hb x)) op s ∧ FreshOp (stI A o₁) (stR A o₁ o₂) op ∧
        (¬ RelOp op (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) g₁ g₂ (atX s x)) ∨
          OpensOp (tOf A ω) op (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) g₁ g₂ (atX s x)))) := by
    funext g₁ g₂ s
    simp only [Bad, accE, freshE, relE, opensE, accOp_atX]
  rw [e]
  exact h

/-- **The first hop's budget**, for any extractor on the tables with the extra table. -/
theorem distI_budgetX' (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudgetX (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (ω : Sec) (r₂ : Coins proveSeedBytes) (g₂ : Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distI A (leanPRX Hb) (verILX Hb) (verRLX Hb) ext ω r₂ g₂) := by
  intro x
  have hB := bad_budgetX Hb A ext hA hX x ω
  have h : Budget pI (a3 + x3) (624 + (a5 + (x5 + 312))) (4607 + (aE + (xE + 4607)))
      (fun o g s => distI A (leanPRX Hb) (verILX Hb) (verRLX Hb) ext ω r₂ g₂ o g (atX s x)) := by
    refine ⟨fun o s => ?_, fun o G3 => ?_, fun o G3 => ?_⟩
    · simp only [distI, D₁, specR_atT]
      exact (hB _ _).h3₁ g₂ s
    · simp only [distI, D₁, specR_atT]
      exact (specR_rd5 (atT A x) (leanPRH (Hb x)) (leanPRH_rd5 (Hb x)) ω _ r₂ g₂).bind
        (f := fun o₂ s => Bad A (verILX Hb) (verRLX Hb) ext ω (reqI (tOf A ω) (some o)) o₂ G3 g₂
          (atX s x)) fun o₂ => (hB _ o₂).h5 G3 g₂
    · simp only [distI, D₁, specR_atT]
      exact (specR_rdE (atT A x) (leanPRH (Hb x)) (leanPRH_rdE (hHb x)) ω _ r₂ g₂).bind
        (f := fun o₂ s => Bad A (verILX Hb) (verRLX Hb) ext ω (reqI (tOf A ω) (some o)) o₂ G3 g₂
          (atX s x)) fun o₂ => (hB _ o₂).hE G3 g₂
  exact h.mono le_rfl (by omega) (by omega)

/-- **The second hop's budget**, for any extractor on the tables with the extra table. -/
theorem distR_budgetX' (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudgetX (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (ω : Sec) (c₁ : SimCoins pI) (g₁ : Tab3) :
    BudgetX pR (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distR A (verILX Hb) (verRLX Hb) ext (leanSim pI) (leanProgIX Hb) ω c₁ g₁) := by
  intro x
  have hB := bad_budgetX Hb A ext hA hX x ω
  have hL := isProg_progO (fun i c => progRO_isProg (R := R) (p := pI) (Hb := Hb x)
    (st := Privacy.Moussaka.stI i) c) (some ⟨tOf A ω, A.ci⟩) c₁
  have h : Budget pI (a3 + x3) (a5 + (x5 + 312) + 312) (aE + (xE + 4607) + 4607)
      (fun o g s => distR A (verILX Hb) (verRLX Hb) ext (leanSim pI) (leanProgIX Hb) ω c₁ g₁ o g
        (atX s x)) := by
    refine ⟨fun o s => ?_, fun o G3 => ?_, fun o G3 => ?_⟩
    · simp only [distR, D₂, pgIP, leanProgIX, progO_progX]
      exact (hB _ _).h3₂ g₁ _
    · simp only [distR, D₂, pgIP, leanProgIX, progO_progX]
      exact ((hB _ _).h5 g₁ G3).comp_prog hL
    · simp only [distR, D₂, pgIP, leanProgIX, progO_progX]
      exact ((hB _ _).hE g₁ G3).comp_prog hL
  have h' := h.mono le_rfl (q5' := a5 + x5 + 936) (qE' := aE + xE + 9214) (by omega) (by omega)
  -- (`pI` and `pR` have the same `H₂³` table type)
  exact ⟨h'.h3, h'.h5, h'.hE⟩

end Hops

/-! ## Redemption non-malleability -/

section Theorem

/-- **The extractor**: `e` on the reduction's queries (`extL`). -/
noncomputable def extLM (q : Kind → ℕ) (qE : ℕ)
    (e : Option (IssueInstance × Bytes) → Option (RedeemInstance × Bytes) → MOp → List DomIC →
      Tab3 → Tab3 → (Tab5F × (Blk → R)) × XTab L M → Bytes) :
    Moussaka.Ext Tab3 (ShX R pI (XTab L M)) :=
  extL ansP (QBud q qE) logQIm logQRm e

variable [Fintype R] [Nonempty R] [ZKRow R]

/-- **Redemption non-malleability with the other hashes random tables, `ε_hit` bounded, and plain
extraction from the adversary's query log** (as `noTheft_leanX_hitL`):

    Pr[Bad] ≤ εz(pI; q') + εz(pR; q') + δ_R + ε_plain
      + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

`q' = (q h3 + x₃, q h5 + x₅ + 936, q_E + x_E + 9214)`, for adversaries with `HitWf` whose last
stage is the run of an oracle computation within `QBud q q_E`. -/
theorem noRedirect_leanX_hitL (A : Thief Tab3 (ShX R pI (XTab L M))) (hw : Hit.Mous.HitWf A)
    (hL : Hit.Mous.Lmin ≤ L)
    {e : Option (IssueInstance × Bytes) → Option (RedeemInstance × Bytes) → MOp → List DomIC →
      Tab3 → Tab3 → (Tab5F × (Blk → R)) × XTab L M → Bytes}
    {q : Kind → ℕ} {qE x3 x5 xE : ℕ} {ε₀ : ℝ}
    (hA : ∀ o₁ o₂, AdmL (QBud q qE) ansP (A.out o₁ o₂))
    (hX : ∀ o₁ o₂, StageBudgetX (extLM q qE e (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hplain : PlainSEL ansP (AccOp (verILX hbX) (verRLX hbX)) FreshOp RelOp e
      (QBud (q + Ratatouille.qPre + Ratatouille.qPre) (qE + verifyCellBound pR + verifyCellBound pI))
      ε₀) :
    pr _ (nmReal A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extLM q qE e)) ≤
      ZKRow.εz R pI (q .h3 + x3) (q .h5 + x5 + 936) (qE + xE + 9214) +
        ZKRow.εz R pR (q .h3 + x3) (q .h5 + x5 + 936) (qE + xE + 9214) +
        pr _ (deltaR A (leanPRX hbX) (leanSim pI) (leanProgIX hbX)) +
        (ε₀ + Hit.epsHit (q .mu) (q .h21) (q .h22)) +
        owAdv A.ci A.cr (inverter A (extLM q qE e) (leanSim pI) (leanProgIX hbX) (leanSim pR)
          (leanProgRX hbX)) := by
  have hSB : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) (q .h3) (q .h5) qE := fun o₁ o₂ => by
    obtain ⟨oa, hb, hF⟩ := hA o₁ o₂
    rw [hF]
    exact stageBudgetX_runT hb
  have hAH : ∀ F : Tab3 → Tab3 → ShX R pI (XTab L M) → MOp, AdmL (QBud q qE) ansP F →
      Hit.AdmHit (R := R) (p := pI) (L := L) (M := M) (G := Tab3) (q .mu) (q .h21) (q .h22) F := by
    rintro F ⟨oa, hb, rfl⟩
    exact admHit_runT hb
  exact Hit.Mous.noRedirect_ok (CI := SimCoins pI) (CR := SimCoins pR) A (verILX hbX) (verRLX hbX)
    (extLM q qE e) (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX) (leanPIX hbX)
    (leanPRX hbX) hw (leanPIX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (leanPRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    (distI_budgetX' hbX A _ hbX_wf hSB hX) (distR_budgetX' hbX A _ hSB hX)
    (weakSE2_of_plainL progQIm (patch2 pI) progQRm (patch2 pI) logQIm logQRm
      (hplain.mono (fun _ _ _ h => h.freshOp) (fun _ h => h) le_rfl)
      (progMoves_of_ev (fun _ _ _ => rfl) (fun _ _ _ => rfl) (accOp_movesX (R := R) hbX)
        ((Hit.Mous.progEv_hit hL (q .mu) (q .h21) (q .h22)).mono hAH))
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) hpatchIm hpatchRm
      (fun x c g₁ g₂ s s' h => hpreIm x c g₁ g₂ s s' h) hlogIm hlogRm (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) fun oa x₁ c₁ x₂ c₂ h => qBud_redQm h x₁ c₁ x₂ c₂)
    hA

end Theorem

end VoleMole.Theft.Moussaka
