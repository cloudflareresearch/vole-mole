import VoleMole.Theft.SimExtractLean

/-!
# The Lean prover, verifiers and simulators of the theft theorems, for any base hash record

`Theft/Reads.lean` and `Theft/SimExtractLean.lean` state the theft theorems with SHAKE
(`Hashes.shake`) for the hashes that are not tables (`H₁`, `H₂⁰`, `H₂¹`, `H₂²`, `H₄`, `H_comb`).
Nothing in their proofs uses SHAKE: the zero-knowledge theorem (`ZKRow.zk`), the read budgets
(`realROb_rd5`, `verRO_rd5`, `progRO_isProg`, …) and the programming step (`verRO_accept_moved`)
hold for every base record `Hb` with outputs of the right lengths (`HashesWF`). Here the same
objects and theorems are stated for any such `Hb`:

* Ratatouille: `leanPIRH`, `leanPSRH` (provers), `leanProgIRH`, `leanProgSRH` (programmings),
  `leanVIRH`, `leanVSRH` (verifiers); `leanPIRH_zkRO`, `leanPSRH_zkRO`; `distI_budgetLH`,
  `distS_budgetLH`; `accOp_movesH`; **`noTheft_leanH_plain`**.
* Moussaka: `leanPIH`, `leanPRH`, `leanProgIH`, `leanProgRH`, `verILH`, `verRLH`; `leanPIH_zkRO`,
  `leanPRH_zkRO`; `distI_budgetLH`, `distR_budgetLH`; `accOp_movesH`; **`noRedirect_leanH_plain`**.

At `Hb = Hashes.shake` they are the objects of the earlier files (`leanPIRH_shake`, …, by `rfl`).
`Theft/Tables.lean` takes `Hb` from a random table and averages.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

/-! ## Ratatouille -/

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

section H

variable {R : Type} [CipherRow R] (Hb : Hashes)

/-- The Lean issuance prover on the tables, base record `Hb`. -/
noncomputable def leanPIRH : ProverI R Sizes.labelRows := fun x w ρ g s =>
  vecOf _ (realROb pI Hb (Privacy.Ratatouille.stI x) (encI x w) (bOf ρ) g s)

/-- The Lean spend prover on the tables, base record `Hb`. -/
noncomputable def leanPSRH : ProverS R Sizes.labelRows := fun x w ρ g s =>
  vecOf _ (realROb pS Hb (Privacy.Ratatouille.stS x) (encS x w) (bOf ρ) g s)

/-- The simulators' programmings, base record `Hb`. -/
noncomputable def leanProgIRH (x : IssueInstance) (c : SimCoins pI) : ShR R → ShR R :=
  progRO pI Hb (Privacy.Ratatouille.stI x) c
noncomputable def leanProgSRH (x : SpendInstance) (c : SimCoins pS) : ShR R → ShR R :=
  progRO pS Hb (Privacy.Ratatouille.stS x) c

/-- The Lean verifiers on the shared tables, base record `Hb`. -/
noncomputable def leanVIRH : IssueInstance → IssueProof Sizes.labelRows → ShR R → Bool :=
  fun x π s => (verRO pI Hb (Privacy.Ratatouille.stI x) (bOf π) s).accept
noncomputable def leanVSRH : SpendInstance → SpendProof Sizes.labelRows → ShR R → Bool :=
  fun x π s => (verRO pS Hb (Privacy.Ratatouille.stS x) (bOf π) s).accept

lemma leanPIRH_shake : leanPIRH (R := R) Hashes.shake = leanPIR := rfl
lemma leanPSRH_shake : leanPSRH (R := R) Hashes.shake = leanPSR := rfl
lemma leanProgIRH_shake : leanProgIRH (R := R) Hashes.shake = leanProgIR := rfl
lemma leanProgSRH_shake : leanProgSRH (R := R) Hashes.shake = leanProgSR := rfl
lemma leanVIRH_shake : leanVIRH (R := R) Hashes.shake = leanVIR := rfl
lemma leanVSRH_shake : leanVSRH (R := R) Hashes.shake = leanVSR := rfl

variable {Hb}

/-- **Zero knowledge of the Lean issuance prover, for any base record.** -/
theorem leanPIRH_zkRO [Fintype R] [ZKRow R] (hHb : HashesWF Hb) (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO IssueRel
      (fun x w (ρ : Coins 16) g (s : ShR R) => leanPIRH Hb x w (vec ρ) g s) leanSimIR
      (leanProgIRH Hb) (Budget pI q3 q5 qE) (ZKRow.εz R pI q3 q5 qE) := by
  have h := (lean_zeroKnowledgeROG (R := R) Hb pI Privacy.Ratatouille.stI (fun _ => rfl) rfl encI
    IssueRel csI zkHypI hHb (smallParams_of_le (by decide) (by decide)) q3 q5 qE).transfer
    id (fun _ w => w) (fun _ _ h => h) (vecOf Sizes.labelRows.issue)
    (Adm' := Budget pI q3 q5 qE) (fun D hD => Budget.comp _ hD)
  have e : (fun x w (ρ : Coins 16) g (s : ShR R) => leanPIRH Hb x w (vec ρ) g s) =
      fun x w r g s => vecOf _ (realRO pI Hb (Privacy.Ratatouille.stI (id x)) (encI (id x) w) r g
        s) := by
    funext x w ρ g s
    simp only [leanPIRH, realRO, bOf_vec, id]
  rw [e]
  exact h

/-- **Zero knowledge of the Lean spend prover, for any base record.** -/
theorem leanPSRH_zkRO [Fintype R] [ZKRow R] (hHb : HashesWF Hb) (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO SpendRel
      (fun x w (ρ : Coins 16) g (s : ShR R) => leanPSRH Hb x w (vec ρ) g s) leanSimSR
      (leanProgSRH Hb) (Budget pS q3 q5 qE) (ZKRow.εz R pS q3 q5 qE) := by
  have h := (lean_zeroKnowledgeROG (R := R) Hb pS Privacy.Ratatouille.stS (fun _ => rfl) rfl encS
    SpendRel csS zkHypS hHb (smallParams_of_le (by decide) (by decide)) q3 q5 qE).transfer
    id (fun _ w => w) (fun _ _ h => h) (vecOf Sizes.labelRows.spend)
    (Adm' := Budget pS q3 q5 qE) (fun D hD => Budget.comp _ hD)
  have e : (fun x w (ρ : Coins 16) g (s : ShR R) => leanPSRH Hb x w (vec ρ) g s) =
      fun x w r g s => vecOf _ (realRO pS Hb (Privacy.Ratatouille.stS (id x)) (encS (id x) w) r g
        s) := by
    funext x w ρ g s
    simp only [leanPSRH, realRO, bOf_vec, id]
  rw [e]
  exact h

variable (Hb)

lemma leanVIRH_rd5 (x : IssueInstance) (π : IssueProof Sizes.labelRows) :
    Rd5 (leanVIRH (R := R) Hb x π) 312 :=
  (verRO_rd5 (Privacy.Ratatouille.stI x) (bOf π)).map Transcript.accept

lemma leanVIRH_rdE (x : IssueInstance) (π : IssueProof Sizes.labelRows) :
    RdE (leanVIRH (R := R) Hb x π) 4607 :=
  (verRO_rdE (Privacy.Ratatouille.stI x) (bOf π)).map Transcript.accept

lemma leanVSRH_rd5 (x : SpendInstance) (π : SpendProof Sizes.labelRows) :
    Rd5 (leanVSRH (R := R) Hb x π) 312 :=
  (verRO_rd5 (p := pS) (Privacy.Ratatouille.stS x) (bOf π)).map Transcript.accept

lemma leanVSRH_rdE (x : SpendInstance) (π : SpendProof Sizes.labelRows) :
    RdE (leanVSRH (R := R) Hb x π) 4607 :=
  (verRO_rdE (p := pS) (Privacy.Ratatouille.stS x) (bOf π)).map Transcript.accept

lemma leanPSRH_rd5 (x : SpendInstance) (w : SpendWitness) (ρ : Rho) (g : Tab3) :
    Rd5 (leanPSRH (R := R) Hb x w ρ g) 624 :=
  (realROb_rd5 (p := pS) (Hb := Hb) (st := Privacy.Ratatouille.stS x) (w := encS x w)
    (bOf ρ) g).map (vecOf Sizes.labelRows.spend)

variable {Hb}

lemma leanPSRH_rdE (hHb : HashesWF Hb) (x : SpendInstance) (w : SpendWitness) (ρ : Rho)
    (g : Tab3) : RdE (leanPSRH (R := R) Hb x w ρ g) 4607 :=
  (realROb_rdE (p := pS) (st := Privacy.Ratatouille.stS x) (w := encS x w) hHb
    (bOf ρ) g).map (vecOf Sizes.labelRows.spend)

variable (A : Thief Sizes.labelRows Tab3 (ShR R)) (ext : Ext Sizes.labelRows Tab3 (ShR R))
  {a3 a5 aE x3 x5 xE : ℕ}

/-- **The first hop's budget**, base record `Hb`. -/
theorem distI_budgetLH (hHb : HashesWF Hb)
    (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (ω : Sec) (r₂ : Coins 16) (g₂ : Tab3) :
    Budget pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distI A (leanPIRH Hb) (leanPSRH Hb) (leanVIRH Hb) (leanVSRH Hb) ext ω r₂ g₂) :=
  (distI_budget A (leanVIRH Hb) (leanVSRH Hb) ext (leanPIRH Hb) (leanPSRH Hb) hA hX
    (leanVIRH_rd5 Hb) (leanVSRH_rd5 Hb) (leanVIRH_rdE Hb) (leanVSRH_rdE Hb) (leanPSRH_rd5 Hb)
    (leanPSRH_rdE hHb) ω r₂ g₂).mono le_rfl (by omega) (by omega)

variable (Hb) in
/-- **The second hop's budget**, base record `Hb`. -/
theorem distS_budgetLH (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (ω : Sec) (c₁ : SimCoins pI) (g₁ : Tab3) :
    Budget pS (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distS A (leanVIRH Hb) (leanVSRH Hb) ext leanSimIR (leanProgIRH Hb) ω c₁ g₁) := by
  have h := (distS_budget A (leanVIRH Hb) (leanVSRH Hb) ext leanSimIR (leanProgIRH Hb) hA hX
    (leanVIRH_rd5 Hb) (leanVSRH_rd5 Hb) (leanVIRH_rdE Hb) (leanVSRH_rdE Hb)
    (fun x c => progRO_isProg c) ω c₁ g₁).mono le_rfl
    (q5' := a5 + x5 + 936) (qE' := aE + xE + 9214) (by omega) (by omega)
  exact ⟨h.h3, h.h5, h.hE⟩

variable (Hb)

/-- The spend simulator's programming, on the shared tables. -/
lemma leanProgSRH_isProg (x : SpendInstance) (c : SimCoins pS) :
    IsProg (p := pI) (leanProgSRH (R := R) Hb x c) 312 4607 := by
  have h := progRO_isProg (R := R) (p := pS) (Hb := Hb) (st := Privacy.Ratatouille.stS x) c
  exact ⟨h.1, h.2.1, h.2.2⟩

lemma leanProgIRH_isProg (x : IssueInstance) (c : SimCoins pI) :
    IsProg (leanProgIRH (R := R) Hb x c) 312 4607 :=
  progRO_isProg c

lemma leanVIRH_eq (x : IssueInstance) (π : IssueProof Sizes.labelRows) (s : ShR R) :
    leanVIRH Hb x π s = (verRO pI Hb (Privacy.Ratatouille.stI x) (bOf π) s).accept := rfl

lemma leanVSRH_eq (x : SpendInstance) (π : SpendProof Sizes.labelRows) (s : ShR R) :
    leanVSRH Hb x π s = (verRO pS Hb (Privacy.Ratatouille.stS x) (bOf π) s).accept := rfl

/-- **The verifier's `H₂³` point of an operation is a programmed point**, base record `Hb`. -/
def HitOpH (op : Op Sizes.labelRows) (s' s : ShR R) : Prop :=
  match op with
  | .issue q t c => HitPt (p := pI) Hb (Privacy.Ratatouille.stI (opXI q t c))
      (bOf (issueReqProof q)) s' s
  | .spend q c _ => HitPt (p := pS) Hb (Privacy.Ratatouille.stS (opXS A q c))
      (bOf (SpendReq.parse q).proof) s' s

/-- **The programming moves the Lean verifiers only at their `H₂³` point**, base record `Hb`. -/
theorem accOp_movesH (op : Op Sizes.labelRows) (s' s : ShR R) (h2 : s'.2 = s.2)
    (h' : AccOp A (leanVIRH Hb) (leanVSRH Hb) op s')
    (h : ¬ AccOp A (leanVIRH Hb) (leanVSRH Hb) op s) : HitOpH Hb A op s' s := by
  cases op with
  | issue q t c =>
    rw [accOp_issue, leanVIRH_eq] at h' h
    exact verRO_accept_moved (p := pI) _ _ _ s' s h2 h' h
  | spend q c x =>
    rw [accOp_spend, leanVSRH_eq] at h' h
    exact verRO_accept_moved (p := pS) _ _ _ s' s h2 h' h

variable {Hb} [Fintype R] [Nonempty R] [ZKRow R]

/-- **No theft with the Lean prover, verifiers and simulators, for any base record `Hb`**
(`noTheft_lean_plain` is the case `Hb = Hashes.shake`):

    Pr[Bad] ≤ εz(pI; q) + εz(pS; q) + δ_S + ε_plain + ε_hit + Adv^ow(inverter),

`q = (a₃ + x₃, a₅ + x₅ + 936, a_E + x_E + 9214)`. -/
theorem noTheft_leanH_plain (hHb : HashesWF Hb)
    {e : Option (IssueInstance × IssueProof Sizes.labelRows) →
      Option (SpendInstance × SpendProof Sizes.labelRows) → Op Sizes.labelRows → Tab3 → Tab3 →
      Tab5F × (Blk → R) → Wit} {ε₀ εh : ℝ}
    (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (extOf e (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hplain : PlainSE (AccOp A (leanVIRH Hb) (leanVSRH Hb)) (FreshOp A) (RelOp A) e
      (fun F => StageBudget F a3 (a5 + 624) (aE + 9214)) ε₀)
    (hhit : ProgEv leanSimIR (leanProgIRH Hb) leanSimSR (leanProgSRH Hb) (FreshOp A)
      (HitOpH Hb A) (fun F => StageBudget F a3 a5 aE) εh) :
    pr _ (theftReal A (leanPIRH Hb) (leanPSRH Hb) (leanVIRH Hb) (leanVSRH Hb) (extOf e)) ≤
      ZKRow.εz R pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ZKRow.εz R pS (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        pr _ (deltaS A (leanPIRH Hb) (leanPSRH Hb) leanSimIR (leanProgIRH Hb)) + (ε₀ + εh) +
        owAdv A.ctx (inverter A (extOf e) leanSimIR (leanProgIRH Hb) leanSimSR
          (leanProgSRH Hb)) :=
  noTheft (CI := SimCoins pI) (CS := SimCoins pS) A (leanPIRH Hb) (leanPSRH Hb) (leanVIRH Hb)
    (leanVSRH Hb) (extOf e) leanSimIR (leanProgIRH Hb) leanSimSR (leanProgSRH Hb)
    (leanPIRH_zkRO hHb _ _ _) (ZKRow.εz_nonneg _ _ _ _) (leanPSRH_zkRO hHb _ _ _)
    (ZKRow.εz_nonneg _ _ _ _) (distI_budgetLH A (extOf e) hHb hA hX)
    (distS_budgetLH Hb A (extOf e) hA hX)
    (weakSE2_of_plain hplain
      (progMoves_of_ev (fun _ _ _ => rfl) (fun _ _ _ => rfl) (accOp_movesH Hb A) hhit)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      fun _ x₁ c₁ x₂ c₂ hF => hF.comp_prog
        (isProg_progT (leanProgIRH_isProg Hb) (leanProgSRH_isProg Hb) x₁ c₁ x₂ c₂)) hA

end H

end Ratatouille

/-! ## Moussaka -/

namespace Moussaka

open VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka

section H

variable {R : Type} [CipherRow R] (Hb : Hashes)

/-- The Lean issuance prover on the tables, base record `Hb`. -/
noncomputable def leanPIH : ProverRO R IssueInstance := fun w x rho g s =>
  toL ((realROb pI Hb (Privacy.Moussaka.stI x) (toBA w) (toBA rho) g s).toOption.getD .empty)

/-- The Lean redemption prover on the tables, base record `Hb`. -/
noncomputable def leanPRH : ProverRO R RedeemInstance := fun w x rho g s =>
  toL ((realROb pR Hb (Privacy.Moussaka.stR x) (toBA w) (toBA rho) g s).toOption.getD .empty)

/-- The simulators' programmings, base record `Hb`. -/
noncomputable def leanProgIH (x : IssueInstance) (c : SimCoins pI) : ShM R → ShM R :=
  progRO pI Hb (Privacy.Moussaka.stI x) c
noncomputable def leanProgRH (x : RedeemInstance) (c : SimCoins pR) : ShM R → ShM R :=
  progRO pR Hb (Privacy.Moussaka.stR x) c

/-- The Lean verifiers on the shared tables, base record `Hb`. -/
noncomputable def verILH : IssueInstance → Bytes → ShM R → Bool := fun x pf s =>
  (verRO pI Hb (Privacy.Moussaka.stI x) (toBA pf) s).accept
noncomputable def verRLH : RedeemInstance → Bytes → ShM R → Bool := fun x pf s =>
  (verRO pR Hb (Privacy.Moussaka.stR x) (toBA pf) s).accept

lemma leanPIH_shake : leanPIH (R := R) Hashes.shake = leanPI := rfl
lemma leanPRH_shake : leanPRH (R := R) Hashes.shake = leanPR := rfl
lemma leanProgIH_shake : leanProgIH (R := R) Hashes.shake = leanProgI := rfl
lemma leanProgRH_shake : leanProgRH (R := R) Hashes.shake = leanProgR := rfl
lemma verILH_shake : verILH (R := R) Hashes.shake = verIL := rfl
lemma verRLH_shake : verRLH (R := R) Hashes.shake = verRL := rfl

variable {Hb}

/-- **Zero knowledge of the Lean issuance prover, for any base record.** -/
theorem leanPIH_zkRO [Fintype R] [ZKRow R] (hHb : HashesWF Hb) (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPIH Hb w x (List.ofFn ρ) g s)
      (leanSim pI) (leanProgIH Hb) (Budget pI q3 q5 qE) (ZKRow.εz R pI q3 q5 qE) := by
  have h := (lean_zeroKnowledgeROG (R := R) Hb pI Privacy.Moussaka.stI (fun _ => rfl) rfl
    (fun _ w => toBA w) IssueRelW csI zkHypI hHb
    (smallParams_of_le (by decide) (by decide)) q3 q5 qE).transfer
    id (fun _ w => w) (fun _ _ h => h) (fun o => toL (o.toOption.getD .empty))
    (fun D hD => Budget.comp _ hD)
  have e : (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPIH Hb w x (List.ofFn ρ) g s) =
      fun x w r g s => toL ((realRO pI Hb (Privacy.Moussaka.stI (id x)) (toBA w) r g
        s).toOption.getD .empty) := by
    funext x w ρ g s
    simp only [leanPIH, realRO, toBA_ofFn, id]
  rw [e]
  exact h

/-- **Zero knowledge of the Lean redemption prover, for any base record.** -/
theorem leanPRH_zkRO [Fintype R] [ZKRow R] (hHb : HashesWF Hb) (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPRH Hb w x (List.ofFn ρ) g s)
      (leanSim pR) (leanProgRH Hb) (Budget pR q3 q5 qE) (ZKRow.εz R pR q3 q5 qE) := by
  have h := (lean_zeroKnowledgeROG (R := R) Hb pR Privacy.Moussaka.stR (fun _ => rfl) rfl
    (fun _ w => toBA w) RedeemRelW csR zkHypR hHb
    (smallParams_of_le (by decide) (by decide)) q3 q5 qE).transfer
    id (fun _ w => w) (fun _ _ h => h) (fun o => toL (o.toOption.getD .empty))
    (fun D hD => Budget.comp _ hD)
  have e : (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPRH Hb w x (List.ofFn ρ) g s) =
      fun x w r g s => toL ((realRO pR Hb (Privacy.Moussaka.stR (id x)) (toBA w) r g
        s).toOption.getD .empty) := by
    funext x w ρ g s
    simp only [leanPRH, realRO, toBA_ofFn, id]
  rw [e]
  exact h

variable (Hb)

lemma verILH_rd5 (x : IssueInstance) (pf : Bytes) : Rd5 (verILH (R := R) Hb x pf) 312 :=
  (verRO_rd5 (Privacy.Moussaka.stI x) (toBA pf)).map Transcript.accept

lemma verILH_rdE (x : IssueInstance) (pf : Bytes) : RdE (verILH (R := R) Hb x pf) 4607 :=
  (verRO_rdE (Privacy.Moussaka.stI x) (toBA pf)).map Transcript.accept

lemma verRLH_rd5 (x : RedeemInstance) (pf : Bytes) : Rd5 (verRLH (R := R) Hb x pf) 312 :=
  (verRO_rd5 (p := pR) (Privacy.Moussaka.stR x) (toBA pf)).map Transcript.accept

lemma verRLH_rdE (x : RedeemInstance) (pf : Bytes) : RdE (verRLH (R := R) Hb x pf) 4607 :=
  (verRO_rdE (p := pR) (Privacy.Moussaka.stR x) (toBA pf)).map Transcript.accept

lemma leanPRH_rd5 (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPRH (R := R) Hb w x rho g) 624 :=
  (realROb_rd5 (p := pR) (Hb := Hb) (st := Privacy.Moussaka.stR x) (w := toBA w)
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

variable {Hb}

lemma leanPRH_rdE (hHb : HashesWF Hb) (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    RdE (leanPRH (R := R) Hb w x rho g) 4607 :=
  (realROb_rdE (p := pR) (st := Privacy.Moussaka.stR x) (w := toBA w) hHb
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

variable (A : Thief Tab3 (ShM R)) (ext : Moussaka.Ext Tab3 (ShM R)) {a3 a5 aE x3 x5 xE : ℕ}

/-- **The first hop's budget**, base record `Hb`. -/
theorem distI_budgetLH (hHb : HashesWF Hb)
    (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (ω : Sec) (r₂ : Coins proveSeedBytes) (g₂ : Tab3) :
    Budget pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distI A (leanPRH Hb) (verILH Hb) (verRLH Hb) ext ω r₂ g₂) :=
  (distI_budget A (verILH Hb) (verRLH Hb) ext (leanPRH Hb) hA hX (verILH_rd5 Hb) (verRLH_rd5 Hb)
    (verILH_rdE Hb) (verRLH_rdE Hb) (leanPRH_rd5 Hb) (leanPRH_rdE hHb) ω r₂ g₂).mono le_rfl
    (by omega) (by omega)

variable (Hb) in
/-- **The second hop's budget**, base record `Hb`. -/
theorem distR_budgetLH (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (ω : Sec) (c₁ : SimCoins pI) (g₁ : Tab3) :
    Budget pR (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214)
      (distR A (verILH Hb) (verRLH Hb) ext (leanSim pI) (leanProgIH Hb) ω c₁ g₁) := by
  have h := (distR_budget A (verILH Hb) (verRLH Hb) ext (leanSim pI) (leanProgIH Hb) hA hX
    (verILH_rd5 Hb) (verRLH_rd5 Hb) (verILH_rdE Hb) (verRLH_rdE Hb)
    (fun x c => progRO_isProg c) ω c₁ g₁).mono le_rfl
    (q5' := a5 + x5 + 936) (qE' := aE + xE + 9214) (by omega) (by omega)
  exact ⟨h.h3, h.h5, h.hE⟩

variable (Hb)

/-- The redemption simulator's programming, on the shared tables. -/
lemma leanProgRH_isProg (x : RedeemInstance) (c : SimCoins pR) :
    IsProg (p := pI) (leanProgRH (R := R) Hb x c) 312 4607 := by
  have h := progRO_isProg (R := R) (p := pR) (Hb := Hb) (st := Privacy.Moussaka.stR x) c
  exact ⟨h.1, h.2.1, h.2.2⟩

lemma leanProgIH_isProg (x : IssueInstance) (c : SimCoins pI) :
    IsProg (leanProgIH (R := R) Hb x c) 312 4607 :=
  progRO_isProg c

lemma verILH_eq (x : IssueInstance) (pf : Bytes) (s : ShM R) :
    verILH Hb x pf s = (verRO pI Hb (Privacy.Moussaka.stI x) (toBA pf) s).accept := rfl

lemma verRLH_eq (x : RedeemInstance) (pf : Bytes) (s : ShM R) :
    verRLH Hb x pf s = (verRO pR Hb (Privacy.Moussaka.stR x) (toBA pf) s).accept := rfl

/-- **The verifier's `H₂³` point of an operation is a programmed point**, base record `Hb`. -/
def HitOpH (op : MOp) (s' s : ShM R) : Prop :=
  match op with
  | .issue req ci => HitPt (p := pI) Hb (Privacy.Moussaka.stI (stOfI req ci))
      (toBA (req.drop uovM)) s' s
  | .redeem S' req ci cr cd => HitPt (p := pR) Hb
      (Privacy.Moussaka.stR (stOfR S' req ci cr cd)) (toBA (req.drop nfBytes)) s' s

/-- **The programming moves the Lean verifiers only at their `H₂³` point**, base record `Hb`. -/
theorem accOp_movesH (op : MOp) (s' s : ShM R) (h2 : s'.2 = s.2)
    (h' : AccOp (verILH Hb) (verRLH Hb) op s') (h : ¬ AccOp (verILH Hb) (verRLH Hb) op s) :
    HitOpH Hb op s' s := by
  cases op with
  | issue req ci =>
    rw [accOp_issue, verILH_eq] at h' h
    exact verRO_accept_moved (p := pI) _ _ _ s' s h2 h'.2.2 fun hn => h ⟨h'.1, h'.2.1, hn⟩
  | redeem S' req ci cr cd =>
    rw [accOp_redeem, verRLH_eq] at h' h
    exact verRO_accept_moved (p := pR) _ _ _ s' s h2 h'.2 fun hn => h ⟨h'.1, hn⟩

variable {Hb} [Fintype R] [Nonempty R] [ZKRow R]

/-- **Redemption non-malleability with the Lean prover, verifiers and simulators, for any base
record `Hb`** (`noRedirect_lean_plain` is the case `Hb = Hashes.shake`):

    Pr[Bad] ≤ εz(pI; q) + εz(pR; q) + δ_R + ε_plain + ε_hit + Adv^ow(inverter),

`q = (a₃ + x₃, a₅ + x₅ + 936, a_E + x_E + 9214)`. -/
theorem noRedirect_leanH_plain (hHb : HashesWF Hb)
    {e : Option (IssueInstance × Bytes) → Option (RedeemInstance × Bytes) → MOp → Tab3 → Tab3 →
      Tab5F × (Blk → R) → Bytes} {ε₀ εh : ℝ}
    (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (extOf e (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hplain : PlainSE (AccOp (verILH Hb) (verRLH Hb)) FreshOp RelOp e
      (fun F => StageBudget F a3 (a5 + 624) (aE + 9214)) ε₀)
    (hhit : ProgEv (simI' (leanSim pI)) (leanProgIH Hb) (simR' (leanSim pR)) (leanProgRH Hb)
      FreshOp (HitOpH (R := R) Hb) (fun F => StageBudget F a3 a5 aE) εh) :
    pr _ (nmReal A (leanPIH Hb) (leanPRH Hb) (verILH Hb) (verRLH Hb) (extOf e)) ≤
      ZKRow.εz R pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ZKRow.εz R pR (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        pr _ (deltaR A (leanPRH Hb) (leanSim pI) (leanProgIH Hb)) + (ε₀ + εh) +
        owAdv A.ci A.cr (inverter A (extOf e) (leanSim pI) (leanProgIH Hb) (leanSim pR)
          (leanProgRH Hb)) :=
  noRedirect (CI := SimCoins pI) (CR := SimCoins pR) A (leanPIH Hb) (leanPRH Hb) (verILH Hb)
    (verRLH Hb) (extOf e) (leanSim pI) (leanProgIH Hb) (leanSim pR) (leanProgRH Hb)
    (leanPIH_zkRO hHb _ _ _) (ZKRow.εz_nonneg _ _ _ _) (leanPRH_zkRO hHb _ _ _)
    (ZKRow.εz_nonneg _ _ _ _) (distI_budgetLH A (extOf e) hHb hA hX)
    (distR_budgetLH Hb A (extOf e) hA hX)
    (weakSE2_of_plain hplain
      (progMoves_of_ev (fun _ _ _ => rfl) (fun _ _ _ => rfl) (accOp_movesH (R := R) Hb) hhit)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      fun _ x₁ c₁ x₂ c₂ hF => hF.comp_prog
        (isProg_progT (leanProgIH_isProg Hb) (leanProgRH_isProg Hb) x₁ c₁ x₂ c₂)) hA

end H

end Moussaka

end VoleMole.Theft
