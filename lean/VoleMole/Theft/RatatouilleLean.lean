import VoleMole.Theft.Ratatouille
import VoleMole.Privacy.RatatouilleRO

/-!
# Ratatouille no theft with the Lean prover (zero-knowledge hops discharged)

`noTheft` (`Theft/Ratatouille.lean`) at the executable Lean prover in the random-oracle and
ideal-cipher model of `Privacy/RatatouilleRO.lean` (`leanPIR`, `leanPSR`: the prover with SHAKE
for the hashes that are not tables, label rows; the tables `H₃` slices `Tab3` and the shared
`ShR R = H₂³ × H₅ × cipher`, AES rows in `R`). Both zero-knowledge hypotheses are theorems
(`leanPIR_zkRO`, `leanPSR_zkRO`), with error `ZKRow.εz R p q₃ q₅ q_E` for distinguishers with
read budgets `(q₃, q₅, q_E)`. What remains as hypotheses:

* `hAI`, `hAS`: the two hops' distinguishers have those budgets. They consist of the adversary's
  last stage, the verifiers on its output, the extractor and (in the first hop) the real spend
  prover, so they hold when those read the tables at bounded numbers of keys; the read
  composition lemmas of `ZK/ReadsRO.lean` (`Rd5.bind`, `realRO_rd5`, …) prove them from the
  budgets of those parts: `noTheft_lean_reads` (`Theft/Reads.lean`).
* `hse`: weak simulation-extractability of the Lean simulators (`WeakSE2`), L8 on paper;
  `noTheft_lean_plain` (`Theft/SimExtractLean.lean`) reduces it to plain extraction.
* `δ_S` stays an explicit probability (as `δS₁` of `unlinkabilityRO`), and `Adv^ow` is the
  explicit inverter's advantage.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.Ratatouille

open VoleMole.Privacy VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille VoleMole.ZK.Sim

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R] [ZKRow R]

/-- **No theft with the Lean prover**:

    Pr[Bad] ≤ εz(pI; q₃, q₅, q_E) + εz(pS; q₃, q₅, q_E) + δ_S + ε_SE + Adv^ow(inverter). -/
theorem noTheft_lean (A : Thief Sizes.labelRows Tab3 (ShR R))
    (verI : IssueInstance → IssueProof Sizes.labelRows → ShR R → Bool)
    (verS : SpendInstance → SpendProof Sizes.labelRows → ShR R → Bool)
    (ext : Ext Sizes.labelRows Tab3 (ShR R)) {q3 q5 qE : ℕ}
    {AdmE : (Tab3 → Tab3 → ShR R → Op Sizes.labelRows) → Prop} {εSE : ℝ}
    (hAI : ∀ ω r₂ g₂, Budget pI q3 q5 qE (distI A leanPIR leanPSR verI verS ext ω r₂ g₂))
    (hAS : ∀ ω c₁ g₁, Budget pS q3 q5 qE (distS A verI verS ext leanSimIR leanProgIR ω c₁ g₁))
    (hse : WeakSE2 leanSimIR leanProgIR leanSimSR leanProgSR (AccOp A verI verS) (FreshOp A)
      (RelOp A) ext AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr _ (theftReal A leanPIR leanPSR verI verS ext) ≤
      ZKRow.εz R pI q3 q5 qE + ZKRow.εz R pS q3 q5 qE +
        pr _ (deltaS A leanPIR leanPSR leanSimIR leanProgIR) + εSE +
        owAdv A.ctx (inverter A ext leanSimIR leanProgIR leanSimSR leanProgSR) := by
  have hI := leanPIR_zkRO (R := R) q3 q5 qE
  have hS := leanPSR_zkRO (R := R) q3 q5 qE
  exact noTheft (CI := SimCoins pI) (CS := SimCoins pS) A leanPIR leanPSR verI verS ext leanSimIR
    leanProgIR leanSimSR leanProgSR hI (ZKRow.εz_nonneg _ _ _ _) hS (ZKRow.εz_nonneg _ _ _ _) hAI
    hAS hse hAE

end VoleMole.Theft.Ratatouille
