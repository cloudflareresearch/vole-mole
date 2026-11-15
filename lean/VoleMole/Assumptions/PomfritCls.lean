import VoleMole.Assumptions.UOVLinks
import VoleMole.ROM.OneMoreClsQueries

/-!
# PomFRIT's Theorem U1^cls against the standalone OMPR game

`lean/docs/security/pomfrit.md` §6.4 (G8-cls), `pomfrit-lemmap-tight.md` §6A.3. `pomfrit_U1_cls_sim'`
and `pomfrit_U1_cls'` (`ROM/OneMoreClsQueries.lean`) with the standalone OMPR advantage of
`Assumptions/UOV.lean` (`advOMPR`, labelled targets on demand) of U1's reduction run with the wrapped
forger (`wrapE`) and the class extractor `E₁^cls` (`e1C`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier
open VoleMole.ROM.OneMore VoleMole.ROM.OneMore.Pomfrit

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (lr : Bool) (A : Forger)

/-- **Theorem U1^cls with simultaneous extraction** against the standalone OMPR game
(`n = Q_T + ℓ + 1` labelled targets, `ℓ` preimage queries), the forger's budget only. -/
theorem pomfrit_U1_ompr_cls_sim (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A addHint (e1C lr) tgts1}[
        PomWin ℓ r] ≤
      advOMPR (pomTrap KG pre) (QT + (ℓ + 1)) ℓ
        (red addHint (advCE ℓ CrtGen.tables lr (fun E => wrapE lr E A) (e1C lr) tgts1)) +
      clsSimEps (qP (qW qA NdC) QT ℓ) (eP lr qE ℓ) (nP (nW nA qA NdC) QT ℓ) ℓ :=
  pomfrit_U1_cls_sim' KG pre ℓ lr A hdig hA

/-- **Theorem U1^cls, union over the forgeries**, against the standalone OMPR game. -/
theorem pomfrit_U1_ompr_cls (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A addHint (e1C lr) tgts1}[
        PomWin ℓ r] ≤
      advOMPR (pomTrap KG pre) (QT + (ℓ + 1)) ℓ
        (red addHint (advCE ℓ CrtGen.tables lr (fun E => wrapE lr E A) (e1C lr) tgts1)) +
      (ℓ + 1) * clsFailEps (qP (qW qA NdC) QT ℓ) (eP lr qE ℓ) (nP (nW nA qA NdC) QT ℓ) :=
  pomfrit_U1_cls' KG pre ℓ lr A hdig hA

end VoleMole.Assumptions.UOV.Links
