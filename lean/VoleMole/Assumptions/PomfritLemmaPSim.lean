import VoleMole.Assumptions.PomfritLemmaP
import VoleMole.ROM.OneMoreLemmaPSim

/-!
# PomFRIT's Theorem U1 with simultaneous extraction, against the standalone OMPR game

`lean/docs/security/pomfrit.md` §6.4 (G8). `pomfrit_U1_ompr` (`Assumptions/UOVLinks.lean`) with
the term `Pr[∃ i, PFail i]` bounded by `prEvent_pfail_sim_le` (`ROM/OneMoreLemmaPSim.lean`): each
query of the forger's run is charged once, not once per forgery.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier
open VoleMole.ROM.OneMore VoleMole.ROM.OneMore.Pomfrit

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (lr : Bool) (A : Forger)

/-- **Theorem U1 with simultaneous extraction**: the standalone OMPR advantage of the reduction
(`n = Q_T + ℓ + 1` labelled targets, `ℓ` preimage queries) plus `pfailSimEps`
(`prEvent_pfail_sim_le`). -/
theorem pomfrit_U1_ompr_sim (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A addHint (e1P lr) tgts1}[PomWin ℓ r] ≤
      advOMPR (pomTrap KG pre) (QT + (ℓ + 1)) ℓ
        (red addHint (advC ℓ CrtGen.tables lr A (e1P lr) tgts1)) +
      pfailSimEps (qP qA QT ℓ) (eP lr qE ℓ) (nP nA QT ℓ) ℓ :=
  (pomfrit_U1_ompr KG pre ℓ QT CrtGen.tables lr A (e1P lr) hA.ht).trans
    (add_le_add le_rfl (prEvent_pfail_sim_le KG pre lr A _ ℓ hdig hA))

end VoleMole.Assumptions.UOV.Links
