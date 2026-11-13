import VoleMole.Audit.Nonvacuous
import VoleMole.Privacy.MoussakaMainPU
import VoleMole.ZK.HopsMainIC

/-!
# Audit of the (PU) results on `main`

* **`zk_rom_ic_h23_main_num` applies to `main`'s statements.** It is instantiated at Moussaka's
  issuance statement on `main` (`withP (stI x) pIm`), any instance and valid witness, SHAKE for
  the hashes that are not tables, and a distinguisher that reads nothing: `MainP`, `ZKHyp`,
  `HashesWF` and `SmallParams` hold for the real objects.
* **`anonymity_main_pu` applies.** With the adversary `mM` of `Audit/Nonvacuous.lean` (constant
  guess, empty read sets: `q₅ = 0`), every hypothesis holds; the four `puAdv` terms stay as they
  are, since they are terms of the bound and not hypotheses.
* **(PU) is not vacuous and not unconditional.** `puAdv` of the exhaustive predictor against the
  concrete `Com` is `1` (`PU.puAdv_bruteForce`), so no bound on `puAdv` holds for all predictors:
  (PU) is a computational assumption. In the ideal-permutation model the bound
  `puAdvPerm_moussaka_le` is instantiated for a predictor that makes one forward query and
  outputs one candidate (`q = c = 1`).

No `sorry`, no `axiom`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.MainPU

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Privacy.PU VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka VoleMole.Arith

/-- `zk_rom_ic_h23_main_num` at Moussaka's issuance statement on `main`, for a distinguisher that
reads no table. -/
example (x : IssueInstance) (w : Spec.Bytes) (h : IssueRelW x w) :=
  zk_rom_ic_h23_main_num Hashes.shake (withP (stI x) pIm) (toBA w) mainP_pIm (zkHypIm x w h)
    hashesWF_shake small_pIm (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ => ∅) (fun _ _ _ _ _ _ _ => Iff.rfl) (q3 := 0) (fun _ _ _ _ _ => le_rfl)
    (fun _ _ _ _ _ => ∅) (fun _ _ _ _ _ _ _ => Iff.rfl)
    (fun _ _ _ _ _ => ∅) (fun _ _ _ _ _ _ _ => Iff.rfl) (qE := 0) (fun _ _ _ _ _ => le_rfl)

/-- `anonymity_main_pu` for the adversary of `Audit/Nonvacuous.lean`. -/
example [HasPrg] (idx : AnchorSet → UOVKey → ℕ) :=
  anonymity_main_pu Audit.mM idx Audit.mM_budget Audit.mM_cons (q5 := 0)
    (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl) (εhide := 0)
    (fun _ _ _ => (hidingAdv_true _ _).le)

/-- **(PU) for the concrete `Com` is computational**: the exhaustive predictor has advantage `1`. -/
example (A : AdversaryM) :
    puAdv (comM A) (bruteForce (Aux := Unit) (comM A)) = 1 :=
  puAdv_bruteForce _

/-- A predictor with one forward query and one candidate. -/
def oneQuery (ci cr : Spec.Bytes) (n : Coins 24) (t : Coins 45) (_ : Unit) :
    PTree KState (Finset (Coins 16)) :=
  .fwd (XM ci cr n fun _ => 0) fun y => .done (if trunc 45 55 y = t then {fun _ => 0} else ∅)

/-- `puAdvPerm_moussaka_le` for `oneQuery`: at most `2/(2¹²⁸ − 1) + 1/(2⁴⁴⁰ − 1)`. -/
example (ci cr : Spec.Bytes) :
    puAdvPerm (XM ci cr) (trunc 45 55) (oneQuery ci cr) ≤
      ((1 : ℕ) + (1 : ℕ)) / (2 ^ 128 - (1 : ℕ) : ℝ) + (1 : ℕ) / (2 ^ 440 - (1 : ℕ) : ℝ) :=
  puAdvPerm_moussaka_le ci cr (oneQuery ci cr)
    (fun _ _ _ => PTree.Bound.fwd _ _ 0 fun _ => PTree.Bound.done _ 0)
    (fun n t a π => by
      show (if _ then _ else _ : Finset (Coins 16)).card ≤ 1
      split_ifs <;> simp)
    (by norm_num)

end VoleMole.Audit.MainPU
