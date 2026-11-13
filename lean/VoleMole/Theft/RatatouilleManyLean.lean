import VoleMole.Theft.RatatouilleMany
import VoleMole.Theft.ManyReads
import VoleMole.Theft.SimExtractLean

/-!
# Ratatouille no theft for `U` Clients and `M` spends, with the Lean prover

`noTheftN` (`Theft/RatatouilleMany.lean`) at the executable Lean prover, verifiers and simulators
in the random-oracle and ideal-cipher model of `Privacy/RatatouilleRO.lean`, in three steps, as
`noTheft_lean`, `noTheft_lean_reads` and `noTheft_lean_plain` for one Client.

* **`noTheftN_lean`**: both zero-knowledge hypotheses are theorems (`leanPIR_zkRO`,
  `leanPSR_zkRO`). The hops' read budgets and `WeakSEN` are hypotheses.
* **`noTheftN_lean_reads`**: the hops' read budgets are proved (`distPI_budgetL`,
  `distPS_budgetL`, from `distN_budget`, `Theft/ManyReads.lean`). With the Lean verifiers, if the
  adversary's last stage reads `(a₃, a₅, a_E)` (`StageBudgetN`) and the extractor `(x₃, x₅, x_E)`,
  every hop has the budget

      q = (a₃ + x₃,  a₅ + x₅ + 312 + (U + M − 1)·624,  a_E + x_E + (U + M)·4607)

  (the verifier `312`/`4607`; each later real proof `624`/`4607`; each earlier programming
  `312`/`4607`). At `U + M = 2` this is the budget of `noTheft_lean_reads`.
* **`weakSEN_ratatouille`**: `WeakSEN` for the Lean simulators and verifiers, extractor
  `extOfN e`, from plain extraction (`PlainSEN`, the adversary's budget after `U + M`
  programmings) and one programmed-point term per simulated proof (`SlotEvN i … HitKeyR`: the
  fresh forgery's verifier reads `H₂³` at a grinding key whose prefix is the recomputed prefix of
  simulated proof `i`), by `weakSEN_of_plain` and `progMovesN_of_slots`
  (`Theft/ManyPlain.lean`).
* **`noTheftN_lean_plain`**:

      Pr[BadN] ≤ U·εz(pI; q) + M·εz(pS; q) + Σ_i δ_i + ε_plain + Σ_i ε_hit,i
                   + Σ_j Adv^ow(inverter j).

`PlainSEN` and the `SlotEvN` terms are hypotheses (see `Theft/SimExtract.lean` for why they are
not provable in this model), as are the explicit terms `δ_i` and `Adv^ow`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.Ratatouille

open VoleMole.Privacy VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille VoleMole.ZK.Sim
  VoleMole.Verifier VoleMole.Verifier.Bridge

variable {U M : ℕ}

/-! ## Zero knowledge discharged -/

section ZK

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R] [ZKRow R]

/-- **No theft for `U` honest Clients and `M` honest spends, with the Lean prover**:

    Pr[BadN] ≤ U·εz(pI; q₃, q₅, q_E) + M·εz(pS; q₃, q₅, q_E) + Σ_i δ_i + ε_SE
                 + Σ_j Adv^ow(inverter j). -/
theorem noTheftN_lean (A : ThiefN Sizes.labelRows U M Tab3 (ShR R))
    (verI : IssueInstance → IssueProof Sizes.labelRows → ShR R → Bool)
    (verS : SpendInstance → SpendProof Sizes.labelRows → ShR R → Bool)
    (ext : ExtN Sizes.labelRows U M Tab3 (ShR R)) {q3 q5 qE : ℕ}
    {AdmE : ((Fin (U + M) → Tab3) → ShR R → Op Sizes.labelRows) → Prop} {εSE : ℝ}
    (hAI : ∀ i : Fin (U + M), i.val < U → ∀ ω τ, Budget pI q3 q5 qE
      (distPI A leanPIR leanPSR leanSimIR leanProgIR leanSimSR leanProgSR verI verS ext i ω τ))
    (hAS : ∀ i : Fin (U + M), U ≤ i.val → ∀ ω τ, Budget pS q3 q5 qE
      (distPS A leanPIR leanPSR leanSimIR leanProgIR leanSimSR leanProgSR verI verS ext i ω τ))
    (hse : WeakSEN (U + M) (simM leanSimIR leanSimSR) (progM leanProgIR leanProgSR)
      (AccOp A.base verI verS) (FreshOpN A) (RelOp A.base) ext AdmE εSE)
    (hAE : ∀ iss sp, AdmE (A.out iss sp)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (ShR R))
        (theftRealN A leanPIR leanPSR verI verS ext) ≤
      U * ZKRow.εz R pI q3 q5 qE + M * ZKRow.εz R pS q3 q5 qE +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (ShR R))
          (deltaNR A leanPIR leanPSR leanSimIR leanProgIR leanSimSR leanProgSR i) +
        εSE +
        ∑ j : Fin (U + M), owAdvK (inverterN A leanSimIR leanProgIR leanSimSR leanProgSR ext j) := by
  have hI := leanPIR_zkRO (R := R) q3 q5 qE
  have hS := leanPSR_zkRO (R := R) q3 q5 qE
  exact noTheftN (CI := SimCoins pI) (CS := SimCoins pS) A leanPIR leanPSR leanSimIR leanProgIR
    leanSimSR leanProgSR verI verS ext hI (ZKRow.εz_nonneg _ _ _ _) hS (ZKRow.εz_nonneg _ _ _ _)
    hAI hAS hse hAE

end ZK

/-! ## The hops' budgets, for any provers, verifiers and programmings on the tables -/

section Generic

variable {R : Type} {p : Params} {Z : Sizes} (A : ThiefN Z U M Tab3 (ShG R p))
  (verI : IssueInstance → IssueProof Z → ShG R p → Bool)
  (verS : SpendInstance → SpendProof Z → ShG R p → Bool) (ext : ExtN Z U M Tab3 (ShG R p))
  {a3 a5 aE x3 x5 xE v5 vE : ℕ}

/-- **The bad event reads what the adversary's last stage, the extractor and the verifiers
read.** -/
theorem bad_budgetN (hA : ∀ iss sp, StageBudgetN (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetN (ext l (opN A pb l)) x3 x5 xE)
    (hI5 : ∀ x π, Rd5 (verI x π) v5) (hS5 : ∀ x π, Rd5 (verS x π) v5)
    (hIE : ∀ x π, RdE (verI x π) vE) (hSE : ∀ x π, RdE (verS x π) vE) (ω : SecN U M)
    (l : LogR Z) :
    StageBudgetN (BadN A verI verS ext ω l) (a3 + x3) (a5 + (x5 + v5)) (aE + (xE + vE)) :=
  (show StageBudgetN (opN A (pubOf ω) l) a3 a5 aE from hA _ _).event
    (V := AccOp A.base verI verS)
    (fun op w acc => acc ∧ FreshOpN A l op ∧ (¬ RelOp A.base op w ∨
      ∃ j : Fin (U + M), ∃ c, comAt A (pubOf ω) l j = some c ∧ ∃ o ∈ opensOf op w, comOf o = c))
    (hX _ l) (accOp_rd5 A.base verI verS hI5 hS5) (accOp_rdE A.base verI verS hIE hSE)

variable (PI : IssueInstance → IssueWitness → Rho → Tab3 → ShG R p → Option (IssueProof Z))
  (PS : SpendInstance → SpendWitness → Rho → Tab3 → ShG R p → Option (SpendProof Z))
  {s5 sE : ℕ}

lemma PN_rd5 (hPI : ∀ x w ρ g, Rd5 (PI x w ρ g) s5) (hPS : ∀ x w ρ g, Rd5 (PS x w ρ g) s5)
    (ω : SecN U M) (l : LogR Z) (r : Coins 16) (g : Tab3) : Rd5 (PN A PI PS ω l r g) s5 :=
  (rd5_proveO (prove := PM PI PS) (rd5_sumProveO (fun x w r g => hPI x w (vec r) g)
    (fun x w r g => hPS x w (vec r) g)) (xwN A ω l) r g).map (pairO (xN A (pubOf ω) l))

lemma PN_rdE (hPI : ∀ x w ρ g, RdE (PI x w ρ g) sE) (hPS : ∀ x w ρ g, RdE (PS x w ρ g) sE)
    (ω : SecN U M) (l : LogR Z) (r : Coins 16) (g : Tab3) : RdE (PN A PI PS ω l r g) sE :=
  (rdE_proveO (prove := PM PI PS) (rdE_sumProveO (fun x w r g => hPI x w (vec r) g)
    (fun x w r g => hPS x w (vec r) g)) (xwN A ω l) r g).map (pairO (xN A (pubOf ω) l))

variable {CI CS : Type} [Nonempty CI] [Nonempty CS]
  (simI : IssueInstance → CI → Option (IssueProof Z))
  (progI : IssueInstance → CI → ShG R p → ShG R p)
  (simS : SpendInstance → CS → Option (SpendProof Z))
  (progS : SpendInstance → CS → ShG R p → ShG R p) {m5 mE : ℕ}

/-- **The budget of every hop's distinguisher** (`distN` of the game). -/
theorem distN_budgetR (hA : ∀ iss sp, StageBudgetN (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetN (ext l (opN A pb l)) x3 x5 xE)
    (hI5 : ∀ x π, Rd5 (verI x π) v5) (hS5 : ∀ x π, Rd5 (verS x π) v5)
    (hIE : ∀ x π, RdE (verI x π) vE) (hSE : ∀ x π, RdE (verS x π) vE)
    (hPI5 : ∀ x w ρ g, Rd5 (PI x w ρ g) s5) (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) s5)
    (hPIE : ∀ x w ρ g, RdE (PI x w ρ g) sE) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) sE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpS : ∀ x c, IsProg (progS x c) m5 mE)
    (i : Fin (U + M)) (ω : SecN U M) (τ : Fin (U + M) → Slot (Coins 16) (CI × CS) Tab3) :
    Budget p (a3 + x3) ((U + M - (i.val + 1)) * s5 + (a5 + (x5 + v5)) + i.val * m5)
      ((U + M - (i.val + 1)) * sE + (aE + (xE + vE)) + i.val * mE)
      (distN (PN A PI PS) (fun ω => SmP A simI simS (pubOf ω))
        (fun ω => pgP A progI progS (pubOf ω)) (BadN A verI verS ext) i ω τ) :=
  distN_budget (PN A PI PS) (fun ω => SmP A simI simS (pubOf ω))
    (fun ω => pgP A progI progS (pubOf ω)) (BadN A verI verS ext)
    (PN_rd5 A PI PS hPI5 hPS5) (PN_rdE A PI PS hPIE hPSE)
    (fun _ _ c => isProg_progO (isProg_sumProg hpI hpS) _ c)
    (fun ω l => bad_budgetN A verI verS ext hA hX hI5 hS5 hIE hSE ω l) i ω τ

end Generic

/-! ## The Lean prover, verifiers and simulators -/

section Lean

variable {R : Type} [CipherRow R]

lemma leanPIR_rd5 (x : IssueInstance) (w : IssueWitness) (ρ : Rho) (g : Tab3) :
    Rd5 (leanPIR (R := R) x w ρ g) 624 :=
  (realROb_rd5 (p := pI) (Hb := Hashes.shake) (st := Privacy.Ratatouille.stI x) (w := encI x w)
    (bOf ρ) g).map (vecOf Sizes.labelRows.issue)

lemma leanPIR_rdE (x : IssueInstance) (w : IssueWitness) (ρ : Rho) (g : Tab3) :
    RdE (leanPIR (R := R) x w ρ g) 4607 :=
  (realROb_rdE (p := pI) (st := Privacy.Ratatouille.stI x) (w := encI x w) hashesWF_shake
    (bOf ρ) g).map (vecOf Sizes.labelRows.issue)

variable (A : ThiefN Sizes.labelRows U M Tab3 (ShR R))
  (ext : ExtN Sizes.labelRows U M Tab3 (ShR R)) {a3 a5 aE x3 x5 xE : ℕ}

/-- **The budget of an issuance hop with the Lean prover, verifiers and simulators.** -/
theorem distPI_budgetL (hA : ∀ iss sp, StageBudgetN (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetN (ext l (opN A pb l)) x3 x5 xE) (i : Fin (U + M)) (ω : SecN U M)
    (τ : Fin (U + M) → Slot (Coins 16) (SimCoins pI × SimCoins pS) Tab3) :
    Budget pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPI A leanPIR leanPSR leanSimIR leanProgIR leanSimSR leanProgSR leanVIR leanVSR ext
        i ω τ) :=
  ((distN_budgetR A leanVIR leanVSR ext leanPIR leanPSR leanSimIR leanProgIR leanSimSR leanProgSR
    hA hX leanVIR_rd5 leanVSR_rd5 leanVIR_rdE leanVSR_rdE leanPIR_rd5 leanPSR_rd5 leanPIR_rdE
    leanPSR_rdE (fun x c => progRO_isProg c) leanProgSR_isProg i ω τ).mono le_rfl
    (by have := i.isLt; omega) (by have := i.isLt; omega)).comp
    (fun o : Option (IssueProof Sizes.labelRows) => pairO (xN A (pubOf ω)
      (simPre (fun ω => SmP A leanSimIR leanSimSR (pubOf ω))
        (fun ω => pgP A leanProgIR leanProgSR (pubOf ω)) ω (tapeC τ) i).1) (o.map Sum.inl))

/-- **The budget of a spend hop with the Lean prover, verifiers and simulators.** -/
theorem distPS_budgetL (hA : ∀ iss sp, StageBudgetN (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetN (ext l (opN A pb l)) x3 x5 xE) (i : Fin (U + M)) (ω : SecN U M)
    (τ : Fin (U + M) → Slot (Coins 16) (SimCoins pI × SimCoins pS) Tab3) :
    Budget pS (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPS A leanPIR leanPSR leanSimIR leanProgIR leanSimSR leanProgSR leanVIR leanVSR ext
        i ω τ) := by
  have h := ((distN_budgetR A leanVIR leanVSR ext leanPIR leanPSR leanSimIR leanProgIR leanSimSR
    leanProgSR hA hX leanVIR_rd5 leanVSR_rd5 leanVIR_rdE leanVSR_rdE leanPIR_rd5 leanPSR_rd5
    leanPIR_rdE leanPSR_rdE (fun x c => progRO_isProg c) leanProgSR_isProg i ω τ).mono le_rfl
    (q5' := a5 + x5 + 312 + (U + M - 1) * 624) (qE' := aE + xE + (U + M) * 4607)
    (by have := i.isLt; omega) (by have := i.isLt; omega)).comp
    (fun o : Option (SpendProof Sizes.labelRows) => pairO (xN A (pubOf ω)
      (simPre (fun ω => SmP A leanSimIR leanSimSR (pubOf ω))
        (fun ω => pgP A leanProgIR leanProgSR (pubOf ω)) ω (tapeC τ) i).1) (o.map Sum.inr))
  -- (`pI` and `pS` have the same `H₂³` table type)
  exact ⟨h.h3, h.h5, h.hE⟩

section Reads

variable [Fintype R] [Nonempty R] [ZKRow R]

/-- **No theft for `U` Clients and `M` spends with the Lean prover and verifiers, the hops'
budgets proved.** For an adversary whose last stage reads `(a₃, a₅, a_E)` and an extractor that
reads `(x₃, x₅, x_E)`:

    Pr[BadN] ≤ U·εz(pI; q) + M·εz(pS; q) + Σ_i δ_i + ε_SE + Σ_j Adv^ow(inverter j),

`q = (a₃ + x₃, a₅ + x₅ + 312 + (U + M − 1)·624, a_E + x_E + (U + M)·4607)`. Weak
simulation-extractability (`hse`) is the remaining hypothesis. -/
theorem noTheftN_lean_reads
    {AdmE : ((Fin (U + M) → Tab3) → ShR R → Op Sizes.labelRows) → Prop} {εSE : ℝ}
    (hA : ∀ iss sp, StageBudgetN (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetN (ext l (opN A pb l)) x3 x5 xE)
    (hse : WeakSEN (U + M) (simM leanSimIR leanSimSR) (progM leanProgIR leanProgSR)
      (AccOp A.base leanVIR leanVSR) (FreshOpN A) (RelOp A.base) ext AdmE εSE)
    (hAE : ∀ iss sp, AdmE (A.out iss sp)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (ShR R))
        (theftRealN A leanPIR leanPSR leanVIR leanVSR ext) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pS (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (ShR R))
          (deltaNR A leanPIR leanPSR leanSimIR leanProgIR leanSimSR leanProgSR i) +
        εSE +
        ∑ j : Fin (U + M), owAdvK (inverterN A leanSimIR leanProgIR leanSimSR leanProgSR ext j) :=
  noTheftN_lean A leanVIR leanVSR ext (fun i _ ω τ => distPI_budgetL A ext hA hX i ω τ)
    (fun i _ ω τ => distPS_budgetL A ext hA hX i ω τ) hse hAE

end Reads

/-! ## Weak simulation-extractability from plain extraction -/

/-- **`k` is the verifier's `H₂³` key of an operation** on the tables `s`: the grinding key of
`chal3`'s input. -/
def PtR (op : Op Sizes.labelRows) (s : ShR R) (k : K2 pI) : Prop :=
  match op with
  | .issue q t c => enc2 pI k = vPoint (p := pI) Hashes.shake
      (Privacy.Ratatouille.stI (opXI q t c)) (bOf (issueReqProof q)) s
  | .spend q c _ => enc2 pS k = vPoint (p := pS) Hashes.shake
      (Privacy.Ratatouille.stS (opXS A.base q c)) (bOf (SpendReq.parse q).proof) s

/-- **`k` is a key the simulation of a statement may program**: its prefix is the grinding prefix
`chal2 ‖ qs_check ‖ ã` recomputed from the simulated proof (coins `c`) on `H₅` and the cipher. -/
noncomputable def MvR (x : RI) (c : SimCoins pI × SimCoins pS) (b : Tab5F × (Blk → R))
    (k : K2 pI) : Prop :=
  match x with
  | .inl x => k.1 = blk (preLen pI) (@outPre (icPrg (rowFn b.2)) Hashes.shake CrtGen.tables
      (Privacy.Ratatouille.stI x) b.1 (simulate pI c.1))
  | .inr x => k.1 = blk (preLen pS) (@outPre (icPrg (rowFn b.2)) Hashes.shake CrtGen.tables
      (Privacy.Ratatouille.stS x) b.1 (simulate pS c.2))

/-- **The operation's verifier reads `H₂³` at a key the simulation of `x` may program**: the
forgery's grinding prefix equals the recomputed prefix of that simulated proof. -/
noncomputable def HitKeyR (x : RI) (c : SimCoins pI × SimCoins pS) (op : Op Sizes.labelRows)
    (s : ShR R) : Prop :=
  ∃ k, PtR A op s k ∧ MvR x c s.2 k

lemma progM_snd (x : RI) (c : SimCoins pI × SimCoins pS) (s : ShR R) :
    (progM leanProgIR leanProgSR x c s).2 = s.2 := by
  rcases x with x | x <;> rfl

lemma progM_moved (x : RI) (c : SimCoins pI × SimCoins pS) (s : ShR R) (k : K2 pI)
    (hk : (progM leanProgIR leanProgSR x c s).1 k ≠ s.1 k) : MvR x c s.2 k := by
  rcases x with x | x
  · exact progRO_moved (p := pI) Hashes.shake (Privacy.Ratatouille.stI x) c.1 s k hk
  · exact progRO_moved (p := pS) Hashes.shake (Privacy.Ratatouille.stS x) c.2 s k hk

lemma accOp_ptR (op : Op Sizes.labelRows) (s' s : ShR R) (h2 : s'.2 = s.2)
    (h' : AccOp A.base leanVIR leanVSR op s') (h : ¬ AccOp A.base leanVIR leanVSR op s) :
    ∃ k, PtR A op s k ∧ s'.1 k ≠ s.1 k := by
  have hm := accOp_moves A.base op s' s h2 h' h
  cases op <;> exact hm

variable [Fintype R]

/-- **Weak simulation-extractability of the Lean simulators and verifiers with `U + M` simulated
proofs, from plain extraction** (`PlainSEN`, the adversary's budget after `U + M` programmings)
and, for each simulated proof `i`, fresh forgeries whose verifier reads a key that proof may
program (`SlotEvN i … HitKeyR`). -/
theorem weakSEN_ratatouille
    {e : LogR Sizes.labelRows → Op Sizes.labelRows → (Fin (U + M) → Tab3) →
      Tab5F × (Blk → R) → Wit} {ε₀ : ℝ} {εh : Fin (U + M) → ℝ}
    (hplain : PlainSEN (U + M) (AccOp A.base leanVIR leanVSR) (FreshOpN A) (RelOp A.base) e
      (fun F => StageBudgetN F a3 (a5 + (U + M) * 312) (aE + (U + M) * 4607)) ε₀)
    (hhit : ∀ i, SlotEvN (U + M) i (simM leanSimIR leanSimSR) (progM leanProgIR leanProgSR)
      (FreshOpN A) (HitKeyR A) (fun F => StageBudgetN F a3 a5 aE) (εh i)) :
    WeakSEN (U + M) (simM leanSimIR leanSimSR) (progM leanProgIR leanProgSR)
      (AccOp A.base leanVIR leanVSR) (FreshOpN A) (RelOp A.base) (extOfN e)
      (fun F => StageBudgetN F a3 a5 aE) (ε₀ + ∑ i, εh i) :=
  weakSEN_of_plain hplain
    (progMovesN_of_slots progM_snd (accOp_ptR A) progM_moved hhit) progM_snd
    fun _ _ hL hF => hF.comp_prog
      (hL.isProg (isProg_sumProg (fun _ c => progRO_isProg c) leanProgSR_isProg))

variable [Nonempty R] [ZKRow R]

/-- **No theft for `U` Clients and `M` spends with the Lean prover, verifiers and simulators,
with plain extraction.** For an adversary whose last stage reads `(a₃, a₅, a_E)` and an
extractor `extOfN e` (which does not read `H₂³`) that reads `(x₃, x₅, x_E)`:

    Pr[BadN] ≤ U·εz(pI; q) + M·εz(pS; q) + Σ_i δ_i + ε_plain + Σ_i ε_hit,i
                 + Σ_j Adv^ow(inverter j),

`q = (a₃ + x₃, a₅ + x₅ + 312 + (U + M − 1)·624, a_E + x_E + (U + M)·4607)`. -/
theorem noTheftN_lean_plain
    {e : LogR Sizes.labelRows → Op Sizes.labelRows → (Fin (U + M) → Tab3) →
      Tab5F × (Blk → R) → Wit} {ε₀ : ℝ} {εh : Fin (U + M) → ℝ}
    (hA : ∀ iss sp, StageBudgetN (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetN (extOfN e l (opN A pb l)) x3 x5 xE)
    (hplain : PlainSEN (U + M) (AccOp A.base leanVIR leanVSR) (FreshOpN A) (RelOp A.base) e
      (fun F => StageBudgetN F a3 (a5 + (U + M) * 312) (aE + (U + M) * 4607)) ε₀)
    (hhit : ∀ i, SlotEvN (U + M) i (simM leanSimIR leanSimSR) (progM leanProgIR leanProgSR)
      (FreshOpN A) (HitKeyR A) (fun F => StageBudgetN F a3 a5 aE) (εh i)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (ShR R))
        (theftRealN A leanPIR leanPSR leanVIR leanVSR (extOfN e)) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pS (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (ShR R))
          (deltaNR A leanPIR leanPSR leanSimIR leanProgIR leanSimSR leanProgSR i) +
        (ε₀ + ∑ i, εh i) +
        ∑ j : Fin (U + M),
          owAdvK (inverterN A leanSimIR leanProgIR leanSimSR leanProgSR (extOfN e) j) :=
  noTheftN_lean_reads A (extOfN e) hA hX (weakSEN_ratatouille A hplain hhit) hA

end Lean

end VoleMole.Theft.Ratatouille
