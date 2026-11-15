import VoleMole.Assumptions.PomfritLemmaPSim
import VoleMole.Assumptions.PomfritShiftSim
import VoleMole.ROM.OneMoreShiftSimPerm

/-!
# PomFRIT's Theorems U1 and U2 with simultaneous extraction, AES as random permutations, against
the standalone OMPR games

`lean/docs/security/pomfrit.md` §6.4, `lean/docs/probabilistic-plan.md` §2o. `pomfrit_U1_ompr_sim`
and `pomfrit_U2_omprShift_sim` (`Assumptions/PomfritLemmaPSim.lean`,
`Assumptions/PomfritShiftSim.lean`) for a forger that makes forward and inverse queries to AES
modelled as a family of uniform random permutations (`ForgerP`, `gameP`,
`ROM/OneMorePerm.lean`): `pomfrit_U1_simP`, `pomfrit_U2_simP` with the experiment written as the
standalone OMPR (`advOMPR`) and OMPR⊕17 (`advOMPRShift`) advantages of the reduction.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier
open VoleMole.ROM.OneMore VoleMole.ROM.OneMore.Pomfrit

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (lr : Bool) (A : ForgerP)

/-- **Theorem U1 with simultaneous extraction, AES as random permutations with inverse queries**:
the standalone OMPR advantage of the reduction (`n = Q_T + ℓ + 1` labelled targets, `ℓ` preimage
queries) plus `pfailSimEpsP` (`prEvent_pfail_sim_leP`). -/
theorem pomfrit_U1_ompr_simP (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBoundP A qA nA qE QT) :
    Pr{let r ← gameP KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A addHint (e1P lr) tgts1}[
        PomWin ℓ r] ≤
      advOMPR (pomTrap KG pre) (QT + (ℓ + 1)) ℓ
        (red addHint (advCP ℓ CrtGen.tables lr A (e1P lr) tgts1)) +
      pfailSimEpsP (qP (addH4 qA) QT ℓ) (eP lr qE ℓ) (nP (nA + qA .h21) QT ℓ) ℓ :=
  pomfrit_U1_simP KG pre lr A ℓ hdig hA

/-- **Theorem U2 with simultaneous extraction, AES as random permutations with inverse queries**:
the standalone OMPR⊕17 advantage of the reduction plus `sfailSimEpsP`
(`prEvent_shiftFail_sim_leP`). -/
theorem pomfrit_U2_omprShift_simP (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBoundP A qA nA qE QT) :
    Pr{let r ← gameP KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A noHint (hintS lr) tgts2}[
        PomWin ℓ r] ≤
      advOMPRShift (pomTrap KG pre) BAVC.tau (QT + (ℓ + 1)) ℓ
        (red noHint (advCP ℓ CrtGen.tables lr A (hintS lr) tgts2)) +
      sfailSimEpsP (qP (addH4 qA) QT ℓ) (eP lr qE ℓ) (nP (nA + qA .h21) QT ℓ) ℓ :=
  pomfrit_U2_simP KG pre lr A ℓ hdig hA

end VoleMole.Assumptions.UOV.Links
