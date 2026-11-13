import VoleMole.Theft.MoussakaMany
import VoleMole.Privacy.MoussakaRO

/-!
# Moussaka Theorem 3 for `U` tokens and `M` redemptions, with the Lean prover

`noRedirectN` (`Theft/MoussakaMany.lean`) at the executable Lean prover in the random-oracle and
ideal-cipher model of `Privacy/MoussakaRO.lean`, as `noRedirect_lean` (`Theft/MoussakaLean.lean`)
for one token. Both zero-knowledge hypotheses are theorems (`leanPI_zkRO`, `leanPR_zkRO`). What
remains as hypotheses: the read budgets of the hops' distinguishers (`hAI`, `hAR`), weak
simulation-extractability with `U + M` simulated proofs (`hse`, `WeakSEN`, L8 on paper), and the
explicit terms `δ_i` and `Adv^ow`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R] [ZKRow R] {U M : ℕ}

/-- **Redemption non-malleability for `U` honest tokens and `M` honest redemptions, with the Lean
prover**:

    Pr[BadN] ≤ U·εz(pI; q₃, q₅, q_E) + M·εz(pR; q₃, q₅, q_E) + Σ_i δ_i + ε_SE
                 + Σ_h Adv^ow(inverter h). -/
theorem noRedirectN_lean (A : ThiefN U M Tab3 (ShM R))
    (verI : IssueInstance → Bytes → ShM R → Bool) (verR : RedeemInstance → Bytes → ShM R → Bool)
    (ext : ExtN U M Tab3 (ShM R)) {q3 q5 qE : ℕ}
    {AdmE : ((Fin (U + M) → Tab3) → ShM R → MOp) → Prop} {εSE : ℝ}
    (hAI : ∀ i : Fin (U + M), i.val < U → ∀ ω τ, Budget pI q3 q5 qE
      (distPN A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR verI verR ext i ω τ))
    (hAR : ∀ i : Fin (U + M), U ≤ i.val → ∀ ω τ, Budget pR q3 q5 qE
      (distPN A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR verI verR ext i ω τ))
    (hse : WeakSEN (U + M) (simM (leanSim pI) (leanSim pR)) (progM leanProgI leanProgR)
      (AccOp verI verR) FreshOpN RelOp ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
        (nmRealN A leanPI leanPR verI verR ext) ≤
      U * ZKRow.εz R pI q3 q5 qE + M * ZKRow.εz R pR q3 q5 qE +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
          (deltaNM A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR i) +
        εSE +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) leanProgI (leanSim pR) leanProgR ext h) :=
  noRedirectN (CI := SimCoins pI) (CR := SimCoins pR) A leanPI leanPR (leanSim pI) leanProgI
    (leanSim pR) leanProgR verI verR ext (leanPI_zkRO (R := R) q3 q5 qE) (ZKRow.εz_nonneg _ _ _ _)
    (leanPR_zkRO (R := R) q3 q5 qE) (ZKRow.εz_nonneg _ _ _ _) hAI hAR hse hAE

end VoleMole.Theft.Moussaka
