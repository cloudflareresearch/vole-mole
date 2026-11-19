import VoleMole.Theft.Hit

/-!
# No theft with `ε_hit` bounded

`Theft/Hit.lean` bounds `ε_hit` (`progEv_hit`) for the freshness `FreshOk`: a spend is compared
with the simulated spend's statement under the adversary's key. The Lean spend statement does not
hash the key, so for simulated statements under another key the bound would need more than the
chain. In the theft game the Client's spend statement has the adversary's key, so the two
freshness notions agree there (`freshOk_stS`), and weak simulation-extractability for `FreshOk`
suffices (`sim_se_le_ok`, `noTheft_ok`).

* **`noTheft_leanX_hit`**: `noTheft_leanX_plain` with `ε_hit` replaced by its bound,

      Pr[Bad] ≤ εz(pI; q) + εz(pS; q) + δ_S + ε_plain
        + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

  for adversaries whose last stage reads the chain tables `H₂⁰`, `H₂¹`, `H₂²` (inputs of at most
  `L ≥ 14357` bytes) with `q_μ`, `q₂₁`, `q₂₂` queries (`AdmHit`).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy

/-- Plain extraction for a stronger freshness. -/
lemma PlainSE.fresh_mono {I₁ I₂ P₁ P₂ G A B Out W : Type*} [Fintype G] [Fintype A] [Fintype B]
    {Acc : Out → A × B → Prop} {Fresh Fresh' : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop}
    {Rel : Out → W → Prop} {e : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → G → G → B → W}
    {Adm : (G → G → A × B → Out) → Prop} {ε : ℝ} (h : PlainSE Acc Fresh Rel e Adm ε)
    (hF : ∀ p₁ p₂ o, Fresh' p₁ p₂ o → Fresh p₁ p₂ o) : PlainSE Acc Fresh' Rel e Adm ε :=
  fun α _ _ p₁ p₂ F hF' => (Privacy.pr_mono fun _ hz => ⟨hz.1, hF _ _ _ hz.2.1, hz.2.2⟩).trans
    (h α p₁ p₂ F hF')

/-- `ε_hit` for a smaller class of adversaries. -/
lemma ProgEv.mono {I₁ I₂ P₁ P₂ G A B Out : Type*} {C₁ C₂ : Type} [Fintype G] [Fintype A]
    [Fintype B] [Fintype C₁] [Fintype C₂] {sim₁ : I₁ → C₁ → Option P₁}
    {prog₁ : I₁ → C₁ → A × B → A × B} {sim₂ : I₂ → C₂ → Option P₂}
    {prog₂ : I₂ → C₂ → A × B → A × B} {Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop}
    {E : Out → A × B → A × B → Prop} {Adm Adm' : (G → G → A × B → Out) → Prop} {ε : ℝ}
    (h : ProgEv sim₁ prog₁ sim₂ prog₂ Fresh E Adm ε) (hA : ∀ F, Adm' F → Adm F) :
    ProgEv sim₁ prog₁ sim₂ prog₂ Fresh E Adm' ε :=
  fun α _ _ x₁ x₂ out hout => h α x₁ x₂ out fun a π₁ π₂ => hA _ (hout a π₁ π₂)

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

section Ok

variable {Z : Sizes} {G S : Type} (A : Thief Z G S)
  (verI : IssueInstance → IssueProof Z → S → Bool)
  (verS : SpendInstance → SpendProof Z → S → Bool) (ext : Ext Z G S)
  {CI CS : Type} (simI : IssueInstance → CI → Option (IssueProof Z))
  (progI : IssueInstance → CI → S → S) (simS : SpendInstance → CS → Option (SpendProof Z))
  (progS : SpendInstance → CS → S → S)
  [Fintype CI] [Fintype CS] [Fintype G] [Fintype S]

/-- **`sim_se_le` for the freshness with the adversary's key.** -/
theorem sim_se_le_ok {AdmE : (G → G → S → Op Z) → Prop} {εSE : ℝ}
    (hse : WeakSE2 simI progI simS progS (AccOp A verI verS) (Hit.Rata.FreshOk A) (RelOp A) ext
      AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr ((Sec × (CI × G)) × ((CS × G) × S))
        (simG (simIss A simI) (pgI A progI) (simSp A simS) (pgS A progS) (seEv A verI verS ext)) ≤
      εSE := by
  have h := hse Sec (fun ω => xIo A (K₁ A ω))
    (fun ω π₁ => xS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) (reqI A (K₁ A ω) π₁))
    (fun ω π₁ π₂ => A.out (reqI A (K₁ A ω) π₁)
      (reqS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) (reqI A (K₁ A ω) π₁) π₂))
    fun _ _ _ => hAE _ _
  refine le_of_eq_of_le (pr_congr fun z => ?_) h
  simp only [simG, seEv, accE, freshE, relE, simIss, simSp, pgI, pgS]
  rw [← Hit.Rata.freshOk_stS]
  simp only [stI_reqI, stS_reqS]

variable (PI : IssueInstance → IssueWitness → Rho → G → S → Option (IssueProof Z))
  (PS : SpendInstance → SpendWitness → Rho → G → S → Option (SpendProof Z))

/-- **No theft with weak simulation-extractability for `FreshOk`** (`noTheft`, whose `WeakSE2` is
for `FreshOp`; the two agree on the game's statements, `sim_se_le_ok`). -/
theorem noTheft_ok [Nonempty CI] [Nonempty CS] [Nonempty G] [Nonempty S]
    {AdmI : (Option (IssueProof Z) → G → S → Prop) → Prop}
    {AdmS : (Option (SpendProof Z) → G → S → Prop) → Prop}
    {AdmE : (G → G → S → Op Z) → Prop} {εI εS εSE : ℝ}
    (hzkI : ZeroKnowledgeRO IssueRel (PI' PI) simI progI AdmI εI) (hεI : 0 ≤ εI)
    (hzkS : ZeroKnowledgeRO SpendRel (PS' PS) simS progS AdmS εS) (hεS : 0 ≤ εS)
    (hAI : ∀ ω r₂ g₂, AdmI (distI A PI PS verI verS ext ω r₂ g₂))
    (hAS : ∀ ω c₁ g₁, AdmS (distS A verI verS ext simI progI ω c₁ g₁))
    (hse : WeakSE2 simI progI simS progS (AccOp A verI verS) (Hit.Rata.FreshOk A) (RelOp A) ext AdmE
      εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr _ (theftReal A PI PS verI verS ext) ≤
      εI + εS + pr _ (deltaS A PI PS simI progI) + εSE +
        owAdv A.ctx (inverter A ext simI progI simS progS) := by
  have h := theft_le (Ω := Sec) (ρ₁ := Coins 16) (ρ₂ := Coins 16) (C₁ := CI) (C₂ := CS) (G := G)
    (S := S) (specI A PI PS) (simIss A simI) (pgI A progI) (specS A PI PS) (simSp A simS)
    (pgS A progS) (accE A verI verS) (freshE A) (relE A ext) (opensE A ext) (ε₁ := εI) (ε₂ := εS)
    (fun ω r₂ g₂ => by
      have := zk_step hzkI hεI (xwI A ω) (xwI_rel A ω) (reqI A (K₁ A ω))
        (D₁ (specS A PI PS) (Bad A verI verS ext) ω r₂ g₂)
        (fun _ _ _ => hAI ω r₂ g₂)
      rw [xwI_fst] at this
      simp only [specI_eq]
      exact this)
    (fun ω c₁ g₁ => by
      have := zk_step hzkS hεS (xwS A ω (simIss A simI ω c₁)) (xwS_rel A ω _)
        (reqS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) (simIss A simI ω c₁))
        (D₂ (simIss A simI) (pgI A progI) (Bad A verI verS ext) ω c₁ g₁)
        (fun _ _ _ => hAS ω c₁ g₁)
      rw [xwS_fst] at this
      simp only [specS_eq]
      exact this)
  have hse' : pr ((Sec × (CI × G)) × ((CS × G) × S))
      (simG (simIss A simI) (pgI A progI) (simSp A simS) (pgS A progS)
        (fun ω o₁ o₂ g₁ g₂ s => accE A verI verS ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧
          ¬ relE A ext ω o₁ o₂ g₁ g₂ s)) ≤ εSE :=
    sim_se_le_ok A verI verS ext simI progI simS progS hse hAE
  have hop := sim_opens_le A ext simI progI simS progS
  have hd : pr ((Sec × (CI × G)) × ((Coins 16 × G) × S)) (deltaS A PI PS simI progI) =
      pr ((Sec × (CI × G)) × ((Coins 16 × G) × S)) (deltaG (simIss A simI) (pgI A progI) (specS A PI PS)) :=
    rfl
  have hr : pr ((Sec × (Coins 16 × G)) × ((Coins 16 × G) × S)) (theftReal A PI PS verI verS ext) =
      pr ((Sec × (Coins 16 × G)) × ((Coins 16 × G) × S)) (realG (specI A PI PS) (specS A PI PS)
        (fun ω o₁ o₂ g₁ g₂ s => accE A verI verS ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧
          (¬ relE A ext ω o₁ o₂ g₁ g₂ s ∨ opensE A ext ω o₁ o₂ g₁ g₂ s))) :=
    rfl
  rw [hr, hd]
  linarith

end Ok

section X

open VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

variable {R : Type} [CipherRow R] {L M : ℕ}

/-- **No theft with the other hashes random tables and `ε_hit` bounded.** As
`noTheft_leanX_plain` with the concrete extra table `XTab L M` (`hbX`, `L ≥ 14357`), the
programming term bounded by `progEv_hit`: for an adversary whose last stage reads `(a₃, a₅, a_E)`
and the chain tables with `(q_μ, q₂₁, q₂₂)` queries (`AdmHit`, implied by its class `Adm`), and
an extractor `extOf e` that reads `(x₃, x₅, x_E)`,

    Pr[Bad] ≤ εz(pI; q) + εz(pS; q) + δ_S + ε_plain
      + 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸) + Adv^ow(inverter),

`q = (a₃ + x₃, a₅ + x₅ + 936, a_E + x_E + 9214)`. Plain extraction (`hplain`) stays a hypothesis,
against a class `Adm₀` that contains the last stage composed with both programmings (`hadm`). -/
theorem noTheft_leanX_hit [Fintype R] [Nonempty R] [ZKRow R]
    (A : Thief Sizes.labelRows Tab3 (ShX R pI (XTab L M))) (hL : Hit.Rata.Lmin ≤ L)
    {e : Option (IssueInstance × IssueProof Sizes.labelRows) →
      Option (SpendInstance × SpendProof Sizes.labelRows) → Op Sizes.labelRows → Tab3 → Tab3 →
      (Tab5F × (Blk → R)) × XTab L M → Wit}
    {Adm Adm₀ : (Tab3 → Tab3 → ShX R pI (XTab L M) → Op Sizes.labelRows) → Prop} {ε₀ : ℝ}
    {a3 a5 aE x3 x5 xE qMu q21 q22 : ℕ}
    (hA : ∀ o₁ o₂, StageBudgetX (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudgetX (extOf e (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hplain : PlainSE (AccOp A (leanVIRX hbX) (leanVSRX hbX)) (FreshOp A) (RelOp A) e Adm₀ ε₀)
    (hAdm : ∀ o₁ o₂, Adm (A.out o₁ o₂)) (hAH : ∀ F, Adm F → Hit.AdmHit qMu q21 q22 F)
    (hadm : ∀ F x₁ c₁ x₂ c₂, Adm F → Adm₀ (fun g₁ g₂ t =>
      F g₁ g₂ (progT (leanProgIRX hbX) (leanProgSRX hbX) x₁ c₁ x₂ c₂ t))) :
    pr _ (theftReal A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX) (extOf e)) ≤
      ZKRow.εz R pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ZKRow.εz R pS (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        pr _ (deltaS A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX)) +
        (ε₀ + Hit.epsHit qMu q21 q22) +
        owAdv A.ctx (inverter A (extOf e) leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX)) :=
  noTheft_ok (CI := SimCoins pI) (CS := SimCoins pS) A (leanVIRX hbX) (leanVSRX hbX) (extOf e)
    leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX) (leanPIRX hbX) (leanPSRX hbX)
    (leanPIRX_zkRO hbX_wf _ _ _) (ZKRow.εz_nonneg _ _ _ _) (leanPSRX_zkRO hbX_wf _ _ _)
    (ZKRow.εz_nonneg _ _ _ _)
    (distI_budgetX A (fun x => extOf fun p₁ p₂ o g₁ g₂ b => e p₁ p₂ o g₁ g₂ (b, x)) hbX_wf hA
      (fun x o₁ o₂ => hX o₁ o₂ x))
    (distS_budgetX hbX A (fun x => extOf fun p₁ p₂ o g₁ g₂ b => e p₁ p₂ o g₁ g₂ (b, x)) hA
      (fun x o₁ o₂ => hX o₁ o₂ x))
    (weakSE2_of_plain (hplain.fresh_mono fun _ _ _ h => Hit.Rata.FreshOk.freshOp A h)
      (progMoves_of_ev (fun _ _ _ => rfl) (fun _ _ _ => rfl) (accOp_movesX hbX A)
        ((Hit.Rata.progEv_hit A hL qMu q21 q22).mono hAH))
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) hadm) hAdm

end X

end Ratatouille

end VoleMole.Theft
