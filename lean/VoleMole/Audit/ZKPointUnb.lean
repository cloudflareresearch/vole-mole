import VoleMole.Theft.JointUnbNumJ
import VoleMole.Audit.TheftJointZK

/-!
# Audit of the joint step for the unbound Moussaka game (zk-unb)

* **The headline theorem's hypotheses are met**: `nmUN_lean_numJ` has the hypotheses of
  `nmUN_lean_numL` (per-kind budgets and the cipher budget `≤ 2⁶⁴`, `U, M ≤ 2³⁰`, `L ≥ LminU`,
  `HitWfN`, `KeysOutNU`, the PRF bound) and is instantiated here at the well-formed trivial
  adversary of the earlier audits (`thiefNUW`), with its last stage a constant redemption and the
  trivial PRF bound; its bound is `2⁻⁵⁴` instead of `(U + M)·2⁻⁵⁵ + 2⁻⁵⁹`.
* **The unbound game is the joint game** (`PN_eq`, `SmP_eq`, `pgP_eq`) and its event, the hit of
  an honest token included, is read by one consistent game reader (`badGRd_cons`,
  `badGRd_reads`), within the stated budgets (`badGRd_bnd`, `badGRd_T3`, `badGRd_cls`).
* **A failed run's log entry has no `iv`**: the unbound game logs `toL` of the proof, the empty
  list for a failed run, so the `iv` decoder `ivA` reads an `iv` only off a proof of the
  parameters' size (`pI_proofBytes_pos`, `pR_proofBytes_pos`: the empty proof is not one).
* **The refused slots' reserved `iv`s** (`Moussaka.ivR` of `Theft/JointMousIv.lean`,
  Ratatouille's `ivR` on the Moussaka extra table) are distinct (`rsvK_inj`), and the simulated
  game's `iv`s are the `H₄` table's blocks or absent with no hypothesis (`ivs_view`). A redemption slot is refused when the token does not finalize or no
  Anchor verifies it, which the adversary controls, so up to `M` slots can be refused: the
  correction of `Audit/ZKPoint5.lean` (`refused_overlap_big`) applies here too.

The headline theorems' axioms are `propext`, `Classical.choice`, `Quot.sound` only (checked in a
scratch file). No `sorry`, no `axiom`.
-/

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.ZKPointUnb

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Theft VoleMole.ROM VoleMole.ROM.IC
open VoleMole.ROM.Reads VoleMole.Verifier
open OracleComp OracleSpec

open VoleMole.Theft.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
  VoleMole.Privacy.MoussakaUnbound
open VoleMole.Spec.Moussaka (ctxBytes cdBytes)
open VoleMole.Audit.TheftManyHit (thiefNUW hitWfN_thiefNUW)
open VoleMole.Audit.Theft (setW)
open VoleMole.Audit.UnboundRest (prf1Adv_le_one)
open VoleMole.Audit.TheftPlainUnbound (keysOutNU_thiefNUW)

variable {U M : ℕ}

/-- **`nmUN_lean_numJ` applies** at the well-formed trivial adversary, every per-kind budget and
the cipher budget `2⁶⁴`, any `U, M ≤ 2³⁰`. -/
example [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) (pts : Fin (M + 1) → Coins ctxBytes)
    (hpts : Function.Injective pts) :=
  nmUN_lean_numJ (L := LminU) (thiefNUW U M _ _) hitWfN_thiefNUW keysOutNU_thiefNUW le_rfl
    (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩) pts hpts
    (fun _ _ => prf1Adv_le_one _ _)

/-- **The reserved inputs of different slots differ.** -/
theorem rsvK_distinct {L i j : ℕ} (hL : 49 ≤ L) (hi : i < 2 ^ 32) (hj : j < 2 ^ 32) (h : i ≠ j) :
    Ratatouille.rsvK (L := L) i ≠ Ratatouille.rsvK j :=
  fun e => h (Ratatouille.rsvK_inj (by omega) hi hj e)

/-- **The empty proof of a failed run is not a proof of either unbound system's size.** -/
theorem empty_not_proof : pI.proofBytes ≠ 0 ∧ pR.proofBytes ≠ 0 :=
  ⟨pI_proofBytes_pos, pR_proofBytes_pos⟩

end VoleMole.Audit.ZKPointUnb
