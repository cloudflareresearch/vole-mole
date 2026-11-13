import VoleMole.Assumptions.PomfritShift
import VoleMole.ROM.OneMoreShiftSim

/-!
# PomFRIT's Theorem U2 with simultaneous extraction, against the standalone OMPR⊕τ game

`lean/docs/security/pomfrit.md` §6.2, §6.4 (G8). `pomfrit_U2_omprShift` (`Assumptions/UOVLinks.lean`)
with U2's shift rule (`hintS`) and the term `Pr[∃ i, ShiftFail i]` bounded by
`prEvent_shiftFail_sim_le` (`ROM/OneMoreShiftSim.lean`): each query of the forger's run is charged
once, not once per forgery.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier
open VoleMole.ROM.OneMore VoleMole.ROM.OneMore.Pomfrit

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (lr : Bool) (A : Forger)

/-- **Theorem U2 with simultaneous extraction**: the standalone OMPR⊕17 advantage of the reduction
(`n = Q_T + ℓ + 1` labelled targets, `ℓ` preimage queries) plus `sfailSimEps`
(`prEvent_shiftFail_sim_le`). -/
theorem pomfrit_U2_omprShift_sim (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A noHint (hintS lr) tgts2}[
        PomWin ℓ r] ≤
      advOMPRShift (pomTrap KG pre) BAVC.tau (QT + (ℓ + 1)) ℓ
        (red noHint (advC ℓ CrtGen.tables lr A (hintS lr) tgts2)) +
      sfailSimEps (qP qA QT ℓ) (eP lr qE ℓ) (nP nA QT ℓ) ℓ :=
  (pomfrit_U2_omprShift KG pre ℓ QT CrtGen.tables lr A BAVC.tau (shP lr) hA.ht).trans
    (add_le_add le_rfl (prEvent_shiftFail_sim_le KG pre lr A _ ℓ hdig hA))

end VoleMole.Assumptions.UOV.Links
