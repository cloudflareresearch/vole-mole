import VoleMole.Assumptions.PomfritCls
import VoleMole.Assumptions.PomfritPermSim
import VoleMole.ROM.OneMoreClsPerm

/-!
# PomFRIT's Theorem U1^cls with AES as random permutations, against the standalone OMPR game

`lean/docs/security/pomfrit.md` §6.4 (G8-cls), `pomfrit-lemmap-tight.md` §6A.5.
`pomfrit_U1_cls_simP` (`ROM/OneMoreClsPerm.lean`) with the standalone OMPR advantage of
`Assumptions/UOV.lean` (`advOMPR`, labelled targets on demand) of U1's reduction run with the
forger normalized and wrapped (`wrapEP`) and the class extractor `E₁^cls` (`e1C`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier
open VoleMole.ROM.OneMore VoleMole.ROM.OneMore.Pomfrit

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (lr : Bool) (A : ForgerP)

/-- **Theorem U1^cls with simultaneous extraction, AES as random permutations with inverse
queries**, against the standalone OMPR game (`n = Q_T + ℓ + 1` labelled targets, `ℓ` preimage
queries), the forger's budget only. -/
theorem pomfrit_U1_ompr_cls_simP (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBoundP A qA nA qE QT) :
    Pr{let r ← gameP KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A addHint (e1C lr) tgts1}[
        PomWin ℓ r] ≤
      advOMPR (pomTrap KG pre) (QT + (ℓ + 1)) ℓ
        (red addHint (advCPE ℓ CrtGen.tables lr (wrapEP lr A) (e1C lr) tgts1)) +
      clsSimEpsP (qP (qW (addH4 qA) NdC) QT ℓ) (eP lr qE ℓ)
        (nP (nW (nA + qA .h21) (addH4 qA) NdC) QT ℓ) ℓ :=
  pomfrit_U1_cls_simP KG pre lr A ℓ hdig hA

end VoleMole.Assumptions.UOV.Links
