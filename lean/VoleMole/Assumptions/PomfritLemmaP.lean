import VoleMole.Assumptions.UOVLinks
import VoleMole.ROM.OneMoreLemmaPBound

/-!
# PomFRIT's Theorem U1 with Lemma P's term explicit, against the standalone OMPR game

`lean/docs/security/pomfrit.md` §6.4 (G8). `pomfrit_U1_ompr` (`Assumptions/UOVLinks.lean`) with
the term `Pr[∃ i, PFail i]` bounded by `prEvent_pfail_le` (`ROM/OneMoreLemmaPBound.lean`): every
term of Theorem U1 is explicit, for Lemma P's `E₁` (`e1P`) and a key generation with 32-byte key
digests.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier
open VoleMole.ROM.OneMore VoleMole.ROM.OneMore.Pomfrit

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (lr : Bool) (A : Forger)

/-- **Theorem U1, every term explicit**: the standalone OMPR advantage of the reduction (`n =
Q_T + ℓ + 1` labelled targets, `ℓ` preimage queries) plus `(ℓ + 1)·pfailEps`, Lemma P's failure
per forgery (`prEvent_pfail_le`). -/
theorem pomfrit_U1_ompr_explicit (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A addHint (e1P lr) tgts1}[PomWin ℓ r] ≤
      advOMPR (pomTrap KG pre) (QT + (ℓ + 1)) ℓ
        (red addHint (advC ℓ CrtGen.tables lr A (e1P lr) tgts1)) +
      (ℓ + 1) * pfailEps (qP qA QT ℓ) (eP lr qE ℓ) (nP nA QT ℓ) :=
  (pomfrit_U1_ompr KG pre ℓ QT CrtGen.tables lr A (e1P lr) hA.ht).trans
    (add_le_add le_rfl (prEvent_pfail_le KG pre lr A _ ℓ hdig hA))

end VoleMole.Assumptions.UOV.Links
