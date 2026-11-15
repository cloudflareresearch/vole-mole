import VoleMole.Theft.JointInst

/-!
# The joint step for Ratatouille's theft game

`real_sim_leN_leanA` (`Theft/JointLeanSum.lean`) applied to the theft game THEFT^{U,M} with the
Lean provers (`Theft/JointInst.lean`: the game is the joint game `gP proveJ (xJ A) (wJ A)`) and the
event `BadN` with `ROM/`'s extractor, read by `badGRd` (`Theft/JointBad.lean`):

    |Pr_real[BadN] − Pr_sim[BadN]| ≤ (Σ_i (εZK/(1 − βZK) + (1 + B)·Pr[deltaN i]) + J) / (1 − N·B),

**`theft_joint_le`**, for every `J` that bounds the summed charges of the active slots in the
simulated game (`nZKA`; bounded in `Theft/JointIv.lean`). The game reader's budgets are
`a₃ = q h3`, `a₅ = N·312 + q h5 + 312`, `a_E = 2·(N·cells(pS) + q_E) + 9215`
(`badGRd_bnd`), and the honest readers' `(max(312, 624), max(4607, 4607)) = (624, 4607)`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

section Theft

variable {U M L : ℕ}

/-- The game reader's `H₅` budget. -/
def a5R (N : ℕ) (q : Kind → ℕ) : ℕ := N * 312 + q .h5 + 312

/-- The game reader's cipher budget (keys). -/
def aER (N qE : ℕ) : ℕ := 2 * (N * verifyCellBound pS + qE) + 9215

variable (A : ThiefN Sizes.labelRows U M Tab3 (TabR L)) {q : Kind → ℕ} {qE nG : ℕ}
  (hA : ∀ iss sp, AdmLN (QBudT q qE nG) ansPN (A.out iss sp))

/-- The theft game's real slot, simulated slot and programming, as the joint game's. -/
lemma theftRealN_eq :
    theftRealN A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX) (extRomN A q qE nG) =
      realGN (C := SimCoins pI × SimCoins pS) (gP proveJ (xJ A) (wJ A))
        (BadN A (leanVIRX hbX) (leanVSRX hbX) (extRomN A q qE nG)) := by
  unfold theftRealN
  rw [PN_eq]

lemma theftSimN_eq :
    theftSimN A leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX)
        (BadN A (leanVIRX hbX) (leanVSRX hbX) (extRomN A q qE nG)) =
      simGN (ρ := ZK.Sim.Bytes 16) (gS simJ (xJ A)) (gPg progJ (xJ A))
        (BadN A (leanVIRX hbX) (leanVSRX hbX) (extRomN A q qE nG)) := by
  unfold theftSimN
  rw [SmP_eq, pgP_eq]

lemma deltaNR_eq (i : Fin (U + M)) :
    deltaNR A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX) leanSimSR
        (leanProgSRX hbX) i =
      deltaN (gP proveJ (xJ A) (wJ A)) (gS simJ (xJ A)) (gPg progJ (xJ A)) i := by
  unfold deltaNR
  rw [PN_eq, SmP_eq, pgP_eq]

set_option maxHeartbeats 1000000 in
/-- **The joint step for Ratatouille's theft game.** For an adversary whose last stage is the run
of an oracle computation within `QBudT q q_E n_G` (`hA`), `ROM/`'s extractor, any `iv` for the
refused slots (`ivN`), and any `J` bounding the summed charges of the active slots in the
simulated game:

    |Pr_real[BadN] − Pr_sim[BadN]| ≤ (Σ_i (εZK/(1 − βZK) + (1 + B)·Pr[deltaNR i]) + J)/(1 − N·B),

`N = U + M`, budgets `(a₃, a₅, a_E) = (q h3, N·312 + q h5 + 312, 2·(N·cells(pS) + q_E) + 9215)`,
honest readers `(624, 4607)`. -/
theorem theft_joint_le (ivN : XR L → ℕ → Option ByteArray)
    (h3 : (q .h3 : ℝ) < 2 ^ 128)
    (hE : 221 * ((aER (U + M) qE + (U + M) * max 4607 4607 + 4607 : ℕ) : ℝ) < 2 ^ 128)
    (hβ : βZK (a5R (U + M) q + (U + M) * max 312 624)
      (aER (U + M) qE + (U + M) * max 4607 4607) < 1)
    {J : ℝ}
    (hJ : ∑ i ∈ range (U + M), ∑ k, wZK (q .h3) (a5R (U + M) q + (U + M) * max 312 624)
        (aER (U + M) qE + (U + M) * max 4607 4607) k *
      exU _ (fun z => (nZKA actJ (ivJ ivN) (xJ A) (badGRd A hA) (max 312 624) (max 4607 4607) i k
        (viewN (C := SimCoins pI × SimCoins pS) (ρ := ZK.Sim.Bytes 16)
          (gP proveJ (xJ A) (wJ A)) (gS simJ (xJ A)) (gPg progJ (xJ A)) (U + M) z) : ℝ)) ≤ J)
    (hNB : ((U + M : ℕ) : ℝ) * ∑ k, wZK (q .h3) (a5R (U + M) q + (U + M) * max 312 624)
        (aER (U + M) qE + (U + M) * max 4607 4607) k *
      MZK (U + M) (q .h3) (a5R (U + M) q) (aER (U + M) qE) (max 312 624) (max 4607 4607) k < 1) :
    |pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (TabR L))
        (theftRealN A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
          (extRomN A q qE nG)) -
      pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (TabR L))
        (theftSimN A leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX)
          (BadN A (leanVIRX hbX) (leanVSRX hbX) (extRomN A q qE nG)))| ≤
      (∑ i : Fin (U + M), (εZK (aER (U + M) qE + (U + M) * max 4607 4607) /
          (1 - βZK (a5R (U + M) q + (U + M) * max 312 624)
            (aER (U + M) qE + (U + M) * max 4607 4607)) +
        (1 + ∑ k, wZK (q .h3) (a5R (U + M) q + (U + M) * max 312 624)
            (aER (U + M) qE + (U + M) * max 4607 4607) k *
          MZK (U + M) (q .h3) (a5R (U + M) q) (aER (U + M) qE) (max 312 624) (max 4607 4607) k) *
          pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (TabR L))
            (deltaNR A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX) leanSimSR
              (leanProgSRX hbX) i)) + J) /
        (1 - ((U + M : ℕ) : ℝ) * ∑ k, wZK (q .h3) (a5R (U + M) q + (U + M) * max 312 624)
            (aER (U + M) qE + (U + M) * max 4607 4607) k *
          MZK (U + M) (q .h3) (a5R (U + M) q) (aER (U + M) qE) (max 312 624) (max 4607 4607) k) := by
  rw [theftRealN_eq, theftSimN_eq]
  simp only [deltaNR_eq]
  exact real_sim_leN_leanA proveJ simJ progJ
    (fun x xI c s => osumProg_keep (g₁ := progI x) (g₂ := progS x) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) xI.2 c s) RelJ actJ (ivJ ivN) (xJ A) (wJ A)
    (relJ_xJ A) progRdJ (progRdJ_conf ivN) proveRdJ
    (fun x xI w r g' hw => proveRdJ_conf ivN x xI w r g' hw) (badGRd A hA) (badGRd_cons A hA)
    (badGRd_bnd A hA) h3 hE hβ (fun x => zkExpJ ivN x h3 hE hβ) hJ hNB _ (badGRd_reads A hA)

end Theft

end Ratatouille

end VoleMole.Theft
