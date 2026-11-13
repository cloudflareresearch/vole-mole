import VoleMole.Assumptions.PomfritLemmaP
import VoleMole.ROM.OneMoreShiftBound

/-!
# PomFRIT's Theorem U2 with every term explicit, against the standalone OMPR⊕τ game

`lean/docs/security/pomfrit.md` §6.2, §6.4 (G8). `pomfrit_U2_omprShift` (`Assumptions/UOVLinks.lean`)
with U2's shift rule (`hintS`: the prefixes of all alive trees, `τ = 17`) and the term
`Pr[∃ i, ShiftFail i]` bounded by `prEvent_shiftFail_le` (`ROM/OneMoreShiftBound.lean`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier
open VoleMole.ROM.OneMore VoleMole.ROM.OneMore.Pomfrit

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (lr : Bool) (A : Forger)

/-- **Theorem U2, every term explicit**: the standalone OMPR⊕17 advantage of the reduction
(`n = Q_T + ℓ + 1` labelled targets, `ℓ` preimage queries, at most `17` shifts per request) plus
`(ℓ + 1)·sfailEps` (`prEvent_shiftFail_le`), which has no `2⁻⁷¹` term. -/
theorem pomfrit_U2_omprShift_explicit (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A noHint (hintS lr) tgts2}[
        PomWin ℓ r] ≤
      advOMPRShift (pomTrap KG pre) BAVC.tau (QT + (ℓ + 1)) ℓ
        (red noHint (advC ℓ CrtGen.tables lr A (hintS lr) tgts2)) +
      (ℓ + 1) * sfailEps (qP qA QT ℓ) (eP lr qE ℓ) (nP nA QT ℓ) :=
  (pomfrit_U2_omprShift KG pre ℓ QT CrtGen.tables lr A BAVC.tau (shP lr) hA.ht).trans
    (add_le_add le_rfl (prEvent_shiftFail_le KG pre lr A _ ℓ hdig hA))

end VoleMole.Assumptions.UOV.Links
