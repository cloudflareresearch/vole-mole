import VoleMole.Theft.Moussaka
import VoleMole.Privacy.MoussakaRO

/-!
# Moussaka redemption non-malleability with the Lean prover (zero-knowledge hops discharged)

`noRedirect` (`Theft/Moussaka.lean`) at the executable Lean prover in the random-oracle and
ideal-cipher model of `Privacy/MoussakaRO.lean` (`leanPI`, `leanPR`, simulator `leanSim`,
programming `leanProgI`, `leanProgR`; tables `Tab3` and `ShM R`). Both zero-knowledge hypotheses
are theorems (`leanPI_zkRO`, `leanPR_zkRO`), with error `ZKRow.εz R p q₃ q₅ q_E`. What remains as
hypotheses is as for Ratatouille (`Theft/RatatouilleLean.lean`): the read budgets of the hops'
distinguishers (`hAI`, `hAR`), weak simulation-extractability (`hse`, L8 on paper), and the explicit
terms `δ_R` and `Adv^ow`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R] [ZKRow R]

/-- **Redemption non-malleability with the Lean prover**:

    Pr[Bad] ≤ εz(pI; q₃, q₅, q_E) + εz(pR; q₃, q₅, q_E) + δ_R + ε_SE + Adv^ow(inverter). -/
theorem noRedirect_lean (A : Thief Tab3 (ShM R)) (verI : IssueInstance → Bytes → ShM R → Bool)
    (verR : RedeemInstance → Bytes → ShM R → Bool) (ext : Ext Tab3 (ShM R)) {q3 q5 qE : ℕ}
    {AdmE : (Tab3 → Tab3 → ShM R → MOp) → Prop} {εSE : ℝ}
    (hAI : ∀ ω r₂ g₂, Budget pI q3 q5 qE (distI A leanPR verI verR ext ω r₂ g₂))
    (hAR : ∀ ω c₁ g₁, Budget pR q3 q5 qE (distR A verI verR ext (leanSim pI) leanProgI ω c₁ g₁))
    (hse : WeakSE2 (simI' (leanSim pI)) leanProgI (simR' (leanSim pR)) leanProgR
      (AccOp verI verR) FreshOp RelOp ext AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr _ (nmReal A leanPI leanPR verI verR ext) ≤
      ZKRow.εz R pI q3 q5 qE + ZKRow.εz R pR q3 q5 qE +
        pr _ (deltaR A leanPR (leanSim pI) leanProgI) + εSE +
        owAdv A.ci A.cr (inverter A ext (leanSim pI) leanProgI (leanSim pR) leanProgR) := by
  have hI := leanPI_zkRO (R := R) q3 q5 qE
  have hR := leanPR_zkRO (R := R) q3 q5 qE
  exact noRedirect (CI := SimCoins pI) (CR := SimCoins pR) A leanPI leanPR verI verR ext
    (leanSim pI) leanProgI (leanSim pR) leanProgR hI (ZKRow.εz_nonneg _ _ _ _) hR
    (ZKRow.εz_nonneg _ _ _ _) hAI hAR hse hAE

end VoleMole.Theft.Moussaka
