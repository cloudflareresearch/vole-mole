import VoleMole.Theft.RatatouilleLean
import VoleMole.Theft.MoussakaLean
import VoleMole.ZK.VerifyReadsRO

/-!
# The read budgets of the non-malleability hops, from the budgets of their parts

`noTheft_lean` and `noRedirect_lean` (`Theft/RatatouilleLean.lean`, `Theft/MoussakaLean.lean`)
assume that the two zero-knowledge hops' distinguishers (`distI`, `distS`, `distR`) have read
budgets `(q₃, q₅, q_E)` (`ZK.Sim.Budget`). Each distinguisher is made of the adversary's last
stage, the extractor, the verifier on the adversary's operation, and (first hop) the real second
prover or (second hop) the first simulation's programming. Here the hop budgets are **proved**
from budgets of the adversary's last stage and of the extractor alone, with the Lean verifiers:

* **`StageBudget F q₃ q₅ q_E`**: a last stage `F g₁ g₂ s` (the two proofs' `H₃` slices and the
  shared tables) reads each slice at `q₃` keys, `H₅` at `q₅` and the cipher at `q_E` keys (the
  other arguments fixed). `StageBudget.event`: an event of a last stage, an extractor and a
  verifier on the stage's output reads the sum.
* **The Lean verifiers** on the shared tables (`leanVIR`, `leanVSR` for Ratatouille, `verIL`,
  `verRL` for Moussaka: `ZK.Sim.verRO` with SHAKE for the hashes that are not tables) read `H₅` at
  `312` keys and the cipher at `4607` (`verRO_rd5`, `verRO_rdE`).
* **The hops**: with the Lean provers (`H₅` at `624`, cipher at `4607`, `realROb_rd5`,
  `realROb_rdE`) and the Lean simulators' programming (`IsProg … 312 4607`, `progRO_isProg`), a
  last stage with budget `(a₃, a₅, a_E)` and an extractor with budget `(x₃, x₅, x_E)` give
  both hops the budget

      (a₃ + x₃,  a₅ + x₅ + 936,  a_E + x_E + 9214)

  (`distI_budgetL`, `distS_budgetL`; Moussaka `distI_budgetL`, `distR_budgetL`).
* **`noTheft_lean_reads`**, **`noRedirect_lean_reads`**: the two theorems with the Lean verifiers
  and these budgets; their remaining hypotheses are the budgets of the adversary and the
  extractor (as `A.Budget` in the privacy theorems) and weak simulation-extractability.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

/-! ## Budgets of a last stage -/

section Stage

variable {R : Type} {p : VoleMole.Verifier.Params} {X Y W : Type*}

/-- **The read budget of a last stage** `F g₁ g₂ s`: each `H₃` slice at `q3` keys, `H₅` at `q5`,
the cipher at `qE` keys, the other arguments fixed. -/
structure StageBudget (F : Tab3 → Tab3 → ShG R p → X) (q3 q5 qE : ℕ) : Prop where
  h3₁ : ∀ g₂ s, Rd3 (fun g₁ => F g₁ g₂ s) q3
  h3₂ : ∀ g₁ s, Rd3 (fun g₂ => F g₁ g₂ s) q3
  h5 : ∀ g₁ g₂, Rd5 (F g₁ g₂) q5
  hE : ∀ g₁ g₂, RdE (F g₁ g₂) qE

/-- A constant last stage reads nothing. -/
lemma StageBudget.const (x : X) : StageBudget (R := R) (p := p) (fun _ _ _ => x) 0 0 0 :=
  ⟨fun _ _ => Rd3.const x, fun _ _ => Rd3.const x, fun _ _ => Rd5.const x, fun _ _ => RdE.const x⟩

lemma StageBudget.mono {F : Tab3 → Tab3 → ShG R p → X} {q3 q5 qE q3' q5' qE' : ℕ}
    (h : StageBudget F q3 q5 qE) (h3 : q3 ≤ q3') (h5 : q5 ≤ q5') (hE : qE ≤ qE') :
    StageBudget F q3' q5' qE' :=
  ⟨fun g s => (h.h3₁ g s).mono h3, fun g s => (h.h3₂ g s).mono h3, fun g g' => (h.h5 g g').mono h5,
    fun g g' => (h.hE g g').mono hE⟩

/-- **An event of a last stage `F`, an extractor `E` and a verifier `V` on `F`'s output** reads
what the three read. -/
theorem StageBudget.event {F : Tab3 → Tab3 → ShG R p → X} {E : Tab3 → Tab3 → ShG R p → W}
    {V : X → ShG R p → Y} {a3 a5 aE x3 x5 xE v5 vE : ℕ} (Φ : X → W → Y → Prop)
    (hF : StageBudget F a3 a5 aE) (hE : StageBudget E x3 x5 xE)
    (hV5 : ∀ o, Rd5 (V o) v5) (hVE : ∀ o, RdE (V o) vE) :
    StageBudget (fun g₁ g₂ s => Φ (F g₁ g₂ s) (E g₁ g₂ s) (V (F g₁ g₂ s) s))
      (a3 + x3) (a5 + (x5 + v5)) (aE + (xE + vE)) where
  h3₁ g₂ s := (hF.h3₁ g₂ s).bind (f := fun o g₁ => Φ o (E g₁ g₂ s) (V o s))
    fun o => (hE.h3₁ g₂ s).map fun w => Φ o w (V o s)
  h3₂ g₁ s := (hF.h3₂ g₁ s).bind (f := fun o g₂ => Φ o (E g₁ g₂ s) (V o s))
    fun o => (hE.h3₂ g₁ s).map fun w => Φ o w (V o s)
  h5 g₁ g₂ := (hF.h5 g₁ g₂).bind (f := fun o s => Φ o (E g₁ g₂ s) (V o s))
    fun o => (hE.h5 g₁ g₂).bind (f := fun w s => Φ o w (V o s)) fun w => (hV5 o).map (Φ o w)
  hE g₁ g₂ := (hF.hE g₁ g₂).bind (f := fun o s => Φ o (E g₁ g₂ s) (V o s))
    fun o => (hE.hE g₁ g₂).bind (f := fun w s => Φ o w (V o s)) fun w => (hVE o).map (Φ o w)

end Stage

/-! ## Optional proofs and programmings -/

section Opt

variable {R : Type} {p : VoleMole.Verifier.Params} {I W' ρ C P : Type*}

/-- A real proof of an optional statement reads what the prover reads. -/
lemma rd5_proveO {prove : I → W' → ρ → Tab3 → ShG R p → Option P} {a : ℕ}
    (h : ∀ x w r g, Rd5 (prove x w r g) a) (xw : Option (I × W')) (r : ρ) (g : Tab3) :
    Rd5 (fun s => proveO prove xw r g s) a := by
  rcases xw with _ | ⟨x, w⟩
  · exact (Rd5.const none).mono (Nat.zero_le _)
  · exact h x w r g

lemma rdE_proveO {prove : I → W' → ρ → Tab3 → ShG R p → Option P} {a : ℕ}
    (h : ∀ x w r g, RdE (prove x w r g) a) (xw : Option (I × W')) (r : ρ) (g : Tab3) :
    RdE (fun s => proveO prove xw r g s) a := by
  rcases xw with _ | ⟨x, w⟩
  · exact (RdE.const none).mono (Nat.zero_le _)
  · exact h x w r g

/-- The programming of an optional statement is a programming. -/
lemma isProg_progO {prog : I → C → ShG R p → ShG R p} {a b : ℕ} (h : ∀ x c, IsProg (prog x c) a b)
    (x : Option I) (c : C) : IsProg (progO prog x c) a b := by
  rcases x with _ | x
  · exact IsProg.id.mono (Nat.zero_le _) (Nat.zero_le _)
  · exact h x c

end Opt

/-! ## Ratatouille -/

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

section Generic

variable {R : Type} {p : Params} {Z : Sizes} (A : Thief Z Tab3 (ShG R p))
  (verI : IssueInstance → IssueProof Z → ShG R p → Bool)
  (verS : SpendInstance → SpendProof Z → ShG R p → Bool) (ext : Ext Z Tab3 (ShG R p))
  {a3 a5 aE x3 x5 xE v5 vE : ℕ}

/-- The acceptance of an operation reads what the verifiers read. -/
lemma accOp_rd5 (hI : ∀ x π, Rd5 (verI x π) v5) (hS : ∀ x π, Rd5 (verS x π) v5) (op : Op Z) :
    Rd5 (AccOp A verI verS op) v5 := by
  cases op with
  | issue q t c => exact (hI _ _).map (· = true)
  | spend q c x => exact (hS _ _).map (· = true)

lemma accOp_rdE (hI : ∀ x π, RdE (verI x π) vE) (hS : ∀ x π, RdE (verS x π) vE) (op : Op Z) :
    RdE (AccOp A verI verS op) vE := by
  cases op with
  | issue q t c => exact (hI _ _).map (· = true)
  | spend q c x => exact (hS _ _).map (· = true)

/-- **The bad event reads what the adversary's last stage, the extractor and the verifiers
read.** -/
theorem bad_budget (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hI5 : ∀ x π, Rd5 (verI x π) v5) (hS5 : ∀ x π, Rd5 (verS x π) v5)
    (hIE : ∀ x π, RdE (verI x π) vE) (hSE : ∀ x π, RdE (verS x π) vE) (ω : Sec)
    (o₁ : Except Error (IssueRequest Z)) (o₂ : Except Error (SpendRequest Z)) :
    StageBudget (fun g₁ g₂ s => Bad A verI verS ext ω o₁ o₂ g₁ g₂ s) (a3 + x3) (a5 + (x5 + v5))
      (aE + (xE + vE)) :=
  (hA o₁ o₂).event (V := AccOp A verI verS)
    (fun op w acc => acc ∧ FreshOp A (stI A o₁) (stS A o₂) op ∧
      (¬ RelOp A op w ∨ OpensOp (K₁ A ω A.tInit) (K₂ A ω (tNext A o₁)) op w))
    (hX o₁ o₂) (accOp_rd5 A verI verS hI5 hS5) (accOp_rdE A verI verS hIE hSE)

variable (PI : IssueInstance → IssueWitness → Rho → Tab3 → ShG R p → Option (IssueProof Z))
  (PS : SpendInstance → SpendWitness → Rho → Tab3 → ShG R p → Option (SpendProof Z))
  {s5 sE : ℕ}

lemma specS_rd5 (hPS : ∀ x w ρ g, Rd5 (PS x w ρ g) s5) (ω : Sec) (req : Except Error (IssueRequest Z))
    (ρ : Coins 16) (g : Tab3) : Rd5 (specS A PI PS ω req ρ g) s5 := by
  have e : specS A PI PS ω req ρ g = fun s =>
      reqS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) req (proveO (PS' PS) (xwS A ω req) ρ g s) :=
    funext fun s => specS_eq A PI PS ω req ρ g s
  rw [e]
  exact (rd5_proveO (fun x w r g => hPS x w (vec r) g) _ _ _).map _

lemma specS_rdE (hPS : ∀ x w ρ g, RdE (PS x w ρ g) sE) (ω : Sec) (req : Except Error (IssueRequest Z))
    (ρ : Coins 16) (g : Tab3) : RdE (specS A PI PS ω req ρ g) sE := by
  have e : specS A PI PS ω req ρ g = fun s =>
      reqS A (vec ω.1.1) (K₁ A ω) (K₂ A ω) req (proveO (PS' PS) (xwS A ω req) ρ g s) :=
    funext fun s => specS_eq A PI PS ω req ρ g s
  rw [e]
  exact (rdE_proveO (fun x w r g => hPS x w (vec r) g) _ _ _).map _

/-- **The first hop's budget**: the last stage, the extractor and the verifiers, after the real
spend prover. -/
theorem distI_budget (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hI5 : ∀ x π, Rd5 (verI x π) v5) (hS5 : ∀ x π, Rd5 (verS x π) v5)
    (hIE : ∀ x π, RdE (verI x π) vE) (hSE : ∀ x π, RdE (verS x π) vE)
    (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) s5) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) sE)
    (ω : Sec) (r₂ : Coins 16) (g₂ : Tab3) :
    Budget p (a3 + x3) (s5 + (a5 + (x5 + v5))) (sE + (aE + (xE + vE)))
      (distI A PI PS verI verS ext ω r₂ g₂) := by
  have hB := bad_budget A verI verS ext hA hX hI5 hS5 hIE hSE ω
  exact ⟨fun o s => (hB _ _).h3₁ g₂ s,
    fun o G3 => (specS_rd5 A PI PS hPS5 ω _ r₂ g₂).bind (f := fun o₂ s =>
      Bad A verI verS ext ω (reqI A (K₁ A ω) o) o₂ G3 g₂ s) fun o₂ => (hB _ o₂).h5 G3 g₂,
    fun o G3 => (specS_rdE A PI PS hPSE ω _ r₂ g₂).bind (f := fun o₂ s =>
      Bad A verI verS ext ω (reqI A (K₁ A ω) o) o₂ G3 g₂ s) fun o₂ => (hB _ o₂).hE G3 g₂⟩

variable {CI : Type} (simI : IssueInstance → CI → Option (IssueProof Z))
  (progI : IssueInstance → CI → ShG R p → ShG R p)

/-- **The second hop's budget**: the last stage, the extractor and the verifiers, on the tables
the simulated issuance programs. -/
theorem distS_budget {m5 mE : ℕ}
    (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hI5 : ∀ x π, Rd5 (verI x π) v5) (hS5 : ∀ x π, Rd5 (verS x π) v5)
    (hIE : ∀ x π, RdE (verI x π) vE) (hSE : ∀ x π, RdE (verS x π) vE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (ω : Sec) (c₁ : CI) (g₁ : Tab3) :
    Budget p (a3 + x3) (a5 + (x5 + v5) + m5) (aE + (xE + vE) + mE)
      (distS A verI verS ext simI progI ω c₁ g₁) := by
  have hB := bad_budget A verI verS ext hA hX hI5 hS5 hIE hSE ω
  have hL := isProg_progO hpI (xIo A (K₁ A ω)) c₁
  exact ⟨fun o s => (hB _ _).h3₂ g₁ _, fun o G3 => ((hB _ _).h5 g₁ G3).comp_prog hL,
    fun o G3 => ((hB _ _).hE g₁ G3).comp_prog hL⟩

end Generic

section Lean

variable {R : Type} [CipherRow R]

/-- **The Lean issuance verifier on the shared tables** (`ZK.Sim.verRO`). -/
noncomputable def leanVIR : IssueInstance → IssueProof Sizes.labelRows → ShR R → Bool :=
  fun x π s => (verRO pI Hashes.shake (Privacy.Ratatouille.stI x) (bOf π) s).accept

/-- **The Lean spend verifier on the shared tables.** -/
noncomputable def leanVSR : SpendInstance → SpendProof Sizes.labelRows → ShR R → Bool :=
  fun x π s => (verRO pS Hashes.shake (Privacy.Ratatouille.stS x) (bOf π) s).accept

lemma leanVIR_rd5 (x : IssueInstance) (π : IssueProof Sizes.labelRows) :
    Rd5 (leanVIR (R := R) x π) 312 :=
  (verRO_rd5 (Privacy.Ratatouille.stI x) (bOf π)).map Transcript.accept

lemma leanVIR_rdE (x : IssueInstance) (π : IssueProof Sizes.labelRows) :
    RdE (leanVIR (R := R) x π) 4607 :=
  (verRO_rdE (Privacy.Ratatouille.stI x) (bOf π)).map Transcript.accept

lemma leanVSR_rd5 (x : SpendInstance) (π : SpendProof Sizes.labelRows) :
    Rd5 (leanVSR (R := R) x π) 312 :=
  (verRO_rd5 (p := pS) (Privacy.Ratatouille.stS x) (bOf π)).map Transcript.accept

lemma leanVSR_rdE (x : SpendInstance) (π : SpendProof Sizes.labelRows) :
    RdE (leanVSR (R := R) x π) 4607 :=
  (verRO_rdE (p := pS) (Privacy.Ratatouille.stS x) (bOf π)).map Transcript.accept

lemma leanPSR_rd5 (x : SpendInstance) (w : SpendWitness) (ρ : Rho) (g : Tab3) :
    Rd5 (leanPSR (R := R) x w ρ g) 624 :=
  (realROb_rd5 (p := pS) (Hb := Hashes.shake) (st := Privacy.Ratatouille.stS x) (w := encS x w)
    (bOf ρ) g).map (vecOf Sizes.labelRows.spend)

lemma leanPSR_rdE (x : SpendInstance) (w : SpendWitness) (ρ : Rho) (g : Tab3) :
    RdE (leanPSR (R := R) x w ρ g) 4607 :=
  (realROb_rdE (p := pS) (st := Privacy.Ratatouille.stS x) (w := encS x w) hashesWF_shake
    (bOf ρ) g).map (vecOf Sizes.labelRows.spend)

variable (A : Thief Sizes.labelRows Tab3 (ShR R)) (ext : Ext Sizes.labelRows Tab3 (ShR R))
  {a3 a5 aE x3 x5 xE : ℕ}

/-- **The first hop's budget with the Lean prover and verifiers.** -/
theorem distI_budgetL (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (ω : Sec) (r₂ : Coins 16) (g₂ : Tab3) :
    Budget pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distI A leanPIR leanPSR leanVIR leanVSR ext ω r₂ g₂) :=
  (distI_budget A leanVIR leanVSR ext leanPIR leanPSR hA hX leanVIR_rd5 leanVSR_rd5 leanVIR_rdE
    leanVSR_rdE leanPSR_rd5 leanPSR_rdE ω r₂ g₂).mono le_rfl (by omega) (by omega)

/-- **The second hop's budget with the Lean simulator's programming and verifiers.** -/
theorem distS_budgetL (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (ω : Sec) (c₁ : SimCoins pI) (g₁ : Tab3) :
    Budget pS (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distS A leanVIR leanVSR ext leanSimIR leanProgIR ω c₁ g₁) := by
  have h := (distS_budget A leanVIR leanVSR ext leanSimIR leanProgIR hA hX leanVIR_rd5
    leanVSR_rd5 leanVIR_rdE leanVSR_rdE (fun x c => progRO_isProg c) ω c₁ g₁).mono le_rfl
    (q5' := a5 + x5 + 936) (qE' := aE + xE + 9214) (by omega) (by omega)
  -- (`pI` and `pS` have the same `H₂³` table type)
  exact ⟨h.h3, h.h5, h.hE⟩

variable [Fintype R] [Nonempty R] [ZKRow R]

/-- **No theft with the Lean prover and verifiers, the hops' budgets proved.** For an adversary
whose last stage reads `(a₃, a₅, a_E)` and an extractor that reads `(x₃, x₅, x_E)`:

    Pr[Bad] ≤ εz(pI; q₃, q₅, q_E) + εz(pS; q₃, q₅, q_E) + δ_S + ε_SE + Adv^ow(inverter),

with `(q₃, q₅, q_E) = (a₃ + x₃, a₅ + x₅ + 936, a_E + x_E + 9214)`. Weak simulation-extractability
(`hse`) is the remaining hypothesis. -/
theorem noTheft_lean_reads {AdmE : (Tab3 → Tab3 → ShR R → Op Sizes.labelRows) → Prop} {εSE : ℝ}
    (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hse : WeakSE2 leanSimIR leanProgIR leanSimSR leanProgSR (AccOp A leanVIR leanVSR) (FreshOp A)
      (RelOp A) ext AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr _ (theftReal A leanPIR leanPSR leanVIR leanVSR ext) ≤
      ZKRow.εz R pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ZKRow.εz R pS (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        pr _ (deltaS A leanPIR leanPSR leanSimIR leanProgIR) + εSE +
        owAdv A.ctx (inverter A ext leanSimIR leanProgIR leanSimSR leanProgSR) :=
  noTheft_lean A leanVIR leanVSR ext (distI_budgetL A ext hA hX) (distS_budgetL A ext hA hX) hse hAE

end Lean

end Ratatouille

/-! ## Moussaka -/

namespace Moussaka

open VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka

section Generic

variable {R : Type} {p : Params} (A : Thief Tab3 (ShG R p))
  (verI : IssueInstance → Bytes → ShG R p → Bool) (verR : RedeemInstance → Bytes → ShG R p → Bool)
  (ext : Moussaka.Ext Tab3 (ShG R p))
  {a3 a5 aE x3 x5 xE v5 vE : ℕ}

lemma accOp_rd5 (hI : ∀ x π, Rd5 (verI x π) v5) (hR : ∀ x π, Rd5 (verR x π) v5) (op : MOp) :
    Rd5 (AccOp verI verR op) v5 := by
  cases op with
  | issue req ci => exact (hI _ _).map fun b => req.length = issueRequestBytes ∧
      ci.length = ctxBytes ∧ b = true
  | redeem S' req ci cr cd => exact (hR _ _).map fun b => req.length = redeemRequestBytes ∧ b = true

lemma accOp_rdE (hI : ∀ x π, RdE (verI x π) vE) (hR : ∀ x π, RdE (verR x π) vE) (op : MOp) :
    RdE (AccOp verI verR op) vE := by
  cases op with
  | issue req ci => exact (hI _ _).map fun b => req.length = issueRequestBytes ∧
      ci.length = ctxBytes ∧ b = true
  | redeem S' req ci cr cd => exact (hR _ _).map fun b => req.length = redeemRequestBytes ∧ b = true

/-- **The bad event reads what the adversary's last stage, the extractor and the verifiers
read.** -/
theorem bad_budget (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hI5 : ∀ x π, Rd5 (verI x π) v5) (hR5 : ∀ x π, Rd5 (verR x π) v5)
    (hIE : ∀ x π, RdE (verI x π) vE) (hRE : ∀ x π, RdE (verR x π) vE) (ω : Sec) (o₁ : Bytes)
    (o₂ : Except Error Bytes) :
    StageBudget (fun g₁ g₂ s => Bad A verI verR ext ω o₁ o₂ g₁ g₂ s) (a3 + x3) (a5 + (x5 + v5))
      (aE + (xE + vE)) :=
  (hA o₁ o₂).event (V := AccOp verI verR)
    (fun op w acc => acc ∧ FreshOp (stI A o₁) (stR A o₁ o₂) op ∧
      (¬ RelOp op w ∨ OpensOp (tOf A ω) op w))
    (hX o₁ o₂) (accOp_rd5 verI verR hI5 hR5) (accOp_rdE verI verR hIE hRE)

variable (PR : Bytes → RedeemInstance → Bytes → Tab3 → ShG R p → Bytes) {s5 sE : ℕ}

lemma specR_rd5 (hPR : ∀ w x ρ g, Rd5 (PR w x ρ g) s5) (ω : Sec) (req : Bytes)
    (ρ : Coins proveSeedBytes) (g : Tab3) : Rd5 (specR A PR ω req ρ g) s5 := by
  have e : specR A PR ω req ρ g = fun s =>
      reqR A (List.ofFn ω.1) (tOf A ω) req (proveO (PR' PR) (xwR A ω req) ρ g s) :=
    funext fun s => specR_eq A PR ω req ρ g s
  rw [e]
  exact (rd5_proveO (fun x w r g => (hPR w x (List.ofFn r) g).map some) _ _ _).map _

lemma specR_rdE (hPR : ∀ w x ρ g, RdE (PR w x ρ g) sE) (ω : Sec) (req : Bytes)
    (ρ : Coins proveSeedBytes) (g : Tab3) : RdE (specR A PR ω req ρ g) sE := by
  have e : specR A PR ω req ρ g = fun s =>
      reqR A (List.ofFn ω.1) (tOf A ω) req (proveO (PR' PR) (xwR A ω req) ρ g s) :=
    funext fun s => specR_eq A PR ω req ρ g s
  rw [e]
  exact (rdE_proveO (fun x w r g => (hPR w x (List.ofFn r) g).map some) _ _ _).map _

/-- **The first hop's budget.** -/
theorem distI_budget (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hI5 : ∀ x π, Rd5 (verI x π) v5) (hR5 : ∀ x π, Rd5 (verR x π) v5)
    (hIE : ∀ x π, RdE (verI x π) vE) (hRE : ∀ x π, RdE (verR x π) vE)
    (hPR5 : ∀ w x ρ g, Rd5 (PR w x ρ g) s5) (hPRE : ∀ w x ρ g, RdE (PR w x ρ g) sE)
    (ω : Sec) (r₂ : Coins proveSeedBytes) (g₂ : Tab3) :
    Budget p (a3 + x3) (s5 + (a5 + (x5 + v5))) (sE + (aE + (xE + vE)))
      (distI A PR verI verR ext ω r₂ g₂) := by
  have hB := bad_budget A verI verR ext hA hX hI5 hR5 hIE hRE ω
  exact ⟨fun o s => (hB _ _).h3₁ g₂ s,
    fun o G3 => (specR_rd5 A PR hPR5 ω _ r₂ g₂).bind (f := fun o₂ s =>
      Bad A verI verR ext ω (reqI (tOf A ω) (some o)) o₂ G3 g₂ s) fun o₂ => (hB _ o₂).h5 G3 g₂,
    fun o G3 => (specR_rdE A PR hPRE ω _ r₂ g₂).bind (f := fun o₂ s =>
      Bad A verI verR ext ω (reqI (tOf A ω) (some o)) o₂ G3 g₂ s) fun o₂ => (hB _ o₂).hE G3 g₂⟩

variable {CI : Type} (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → ShG R p → ShG R p)

/-- **The second hop's budget.** -/
theorem distR_budget {m5 mE : ℕ}
    (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hI5 : ∀ x π, Rd5 (verI x π) v5) (hR5 : ∀ x π, Rd5 (verR x π) v5)
    (hIE : ∀ x π, RdE (verI x π) vE) (hRE : ∀ x π, RdE (verR x π) vE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (ω : Sec) (c₁ : CI) (g₁ : Tab3) :
    Budget p (a3 + x3) (a5 + (x5 + v5) + m5) (aE + (xE + vE) + mE)
      (distR A verI verR ext simI progI ω c₁ g₁) := by
  have hB := bad_budget A verI verR ext hA hX hI5 hR5 hIE hRE ω
  have hL := isProg_progO hpI (some ⟨tOf A ω, A.ci⟩) c₁
  exact ⟨fun o s => (hB _ _).h3₂ g₁ _, fun o G3 => ((hB _ _).h5 g₁ G3).comp_prog hL,
    fun o G3 => ((hB _ _).hE g₁ G3).comp_prog hL⟩

end Generic

section Lean

variable {R : Type} [CipherRow R]

/-- **The Lean issuance verifier on the shared tables** (`ZK.Sim.verRO`). -/
noncomputable def verIL : IssueInstance → Bytes → ShM R → Bool := fun x pf s =>
  (verRO pI Hashes.shake (Privacy.Moussaka.stI x) (toBA pf) s).accept

/-- **The Lean redemption verifier on the shared tables.** -/
noncomputable def verRL : RedeemInstance → Bytes → ShM R → Bool := fun x pf s =>
  (verRO pR Hashes.shake (Privacy.Moussaka.stR x) (toBA pf) s).accept

lemma verIL_rd5 (x : IssueInstance) (pf : Bytes) : Rd5 (verIL (R := R) x pf) 312 :=
  (verRO_rd5 (Privacy.Moussaka.stI x) (toBA pf)).map Transcript.accept

lemma verIL_rdE (x : IssueInstance) (pf : Bytes) : RdE (verIL (R := R) x pf) 4607 :=
  (verRO_rdE (Privacy.Moussaka.stI x) (toBA pf)).map Transcript.accept

lemma verRL_rd5 (x : RedeemInstance) (pf : Bytes) : Rd5 (verRL (R := R) x pf) 312 :=
  (verRO_rd5 (p := pR) (Privacy.Moussaka.stR x) (toBA pf)).map Transcript.accept

lemma verRL_rdE (x : RedeemInstance) (pf : Bytes) : RdE (verRL (R := R) x pf) 4607 :=
  (verRO_rdE (p := pR) (Privacy.Moussaka.stR x) (toBA pf)).map Transcript.accept

lemma leanPR_rd5' (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPR (R := R) w x rho g) 624 :=
  (realROb_rd5 (p := pR) (Hb := Hashes.shake) (st := Privacy.Moussaka.stR x) (w := toBA w)
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

lemma leanPR_rdE' (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    RdE (leanPR (R := R) w x rho g) 4607 :=
  (realROb_rdE (p := pR) (st := Privacy.Moussaka.stR x) (w := toBA w) hashesWF_shake
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

variable (A : Thief Tab3 (ShM R)) (ext : Moussaka.Ext Tab3 (ShM R)) {a3 a5 aE x3 x5 xE : ℕ}

/-- **The first hop's budget with the Lean prover and verifiers.** -/
theorem distI_budgetL (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (ω : Sec) (r₂ : Coins proveSeedBytes) (g₂ : Tab3) :
    Budget pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distI A leanPR verIL verRL ext ω r₂ g₂) :=
  (distI_budget A verIL verRL ext leanPR hA hX verIL_rd5 verRL_rd5 verIL_rdE verRL_rdE
    leanPR_rd5' leanPR_rdE' ω r₂ g₂).mono le_rfl (by omega) (by omega)

/-- **The second hop's budget with the Lean simulator's programming and verifiers.** -/
theorem distR_budgetL (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (ω : Sec) (c₁ : SimCoins pI) (g₁ : Tab3) :
    Budget pR (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distR A verIL verRL ext (leanSim pI) leanProgI ω c₁ g₁) := by
  have h := (distR_budget A verIL verRL ext (leanSim pI) leanProgI hA hX verIL_rd5 verRL_rd5
    verIL_rdE verRL_rdE (fun x c => progRO_isProg c) ω c₁ g₁).mono le_rfl
    (q5' := a5 + x5 + 936) (qE' := aE + xE + 9214) (by omega) (by omega)
  -- (`pI` and `pR` have the same `H₂³` table type)
  exact ⟨h.h3, h.h5, h.hE⟩

variable [Fintype R] [Nonempty R] [ZKRow R]

/-- **Redemption non-malleability with the Lean prover and verifiers, the hops' budgets
proved.** For an adversary whose last stage reads `(a₃, a₅, a_E)` and an extractor that reads
`(x₃, x₅, x_E)`:

    Pr[Bad] ≤ εz(pI; q₃, q₅, q_E) + εz(pR; q₃, q₅, q_E) + δ_R + ε_SE + Adv^ow(inverter),

with `(q₃, q₅, q_E) = (a₃ + x₃, a₅ + x₅ + 936, a_E + x_E + 9214)`. Weak simulation-extractability
(`hse`) is the remaining hypothesis. -/
theorem noRedirect_lean_reads {AdmE : (Tab3 → Tab3 → ShM R → MOp) → Prop} {εSE : ℝ}
    (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hse : WeakSE2 (simI' (leanSim pI)) leanProgI (simR' (leanSim pR)) leanProgR
      (AccOp verIL verRL) FreshOp RelOp ext AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr _ (nmReal A leanPI leanPR verIL verRL ext) ≤
      ZKRow.εz R pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ZKRow.εz R pR (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        pr _ (deltaR A leanPR (leanSim pI) leanProgI) + εSE +
        owAdv A.ci A.cr (inverter A ext (leanSim pI) leanProgI (leanSim pR) leanProgR) :=
  noRedirect_lean A verIL verRL ext (distI_budgetL A ext hA hX) (distR_budgetL A ext hA hX) hse hAE

end Lean

end Moussaka

end VoleMole.Theft
