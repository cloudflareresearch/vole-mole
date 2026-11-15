import VoleMole.Theft.JointIv
import VoleMole.Theft.PlainTotalRom

/-!
# No theft for `U` Clients and `M` spends with the joint step at points (Ratatouille)

The many-token theft bound of `Theft/NumLin.lean` (`noTheftN_lean_numL`) is linear in `U + M`:
`(U + M)·2⁻⁵⁵ + 2⁻⁵⁹`. Here the hops are replaced by the joint step at points:

* **`theft_sim_le`**: in the simulated game, `Pr[BadN] ≤ ε_SE + Σ_j Adv^ow(inverter j)`, with
  `ε_SE` `ROM/`'s simultaneous extraction for the reduction's budget (as in `noTheftN_lean_rom`);
* **`noTheftN_lean_joint`**: `Pr_real[BadN] ≤ joint + ε_SE + Σ_j Adv^ow`, with `joint` the right
  side of `theft_joint_le` at `J` of `theft_J_le` and the refused slots' `iv`s `ivR`;
* **`noTheftN_lean_numJ`**: numerically, with every per-kind hash budget and the cipher budget at
  most `2⁶⁴` and `U, M ≤ 2³⁰`, `Pr[BadN] ≤ 2⁻⁵⁴ + Σ_j Adv^ow(inverter j)`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads VoleMole.ZK.IC

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

/-- **`pFail ≤ 2⁻¹¹³`.** -/
lemma pFail_le : pFail ≤ 1 / 2 ^ 113 := by
  have e : pFail = pr Grind (fun g => firstHit g = none) := by
    rw [pr_eq_exU]; rfl
  rw [e]
  exact (Privacy.pr_mono fun g hg => Or.inl hg).trans grindBad_le_113

section Sim

variable {U M L : ℕ} (A : ThiefN Sizes.labelRows U M Tab3 (TabR L))

set_option maxHeartbeats 4000000 in
/-- **The simulated game's theft event**: `ROM/`'s simultaneous extraction for the reduction's
budget, and the inverters. -/
theorem theft_sim_le (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE nG : ℕ}
    (hA : ∀ iss sp, AdmLN (QBudT q qE nG) ansPN (A.out iss sp)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (TabR L))
        (theftSimN A leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX)
          (BadN A (leanVIRX hbX) (leanVSRX hbX) (extRomN A q qE nG))) ≤
      ((epsRom (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pS)
          (nG + (U + M) * 338)).toReal +
        (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
      ∑ j : Fin (U + M), owAdvK (inverterN A leanSimIR (leanProgIRX hbX) leanSimSR
        (leanProgSRX hbX) (extRomN A q qE nG) j) := by
  have hAH : ∀ F : (Fin (U + M) → Tab3) → TabR L → Op Sizes.labelRows,
      AdmLN (QBudT q qE nG) ansPN F →
      Hit.AdmHitN (R := Blk → Blk) (p := pI) (L := L) (M := Arith.Ratatouille.uovM)
        (N := U + M) (G := Tab3) (q .mu) (q .h21) (q .h22) F := by
    rintro F ⟨oa, hb, rfl⟩
    exact admHitN_runTN hb.1
  have hse := sim_se_leN_ok A leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX)
    (leanVIRX hbX) (leanVSRX hbX) (extRomN A q qE nG)
    (weakSEN_of_plainL progQM (patch2 pI) logQM (plainSENL_rom A hL _ _ _ (FreshOkN A))
      ((progMovesN_hit A hL (q .mu) (q .h21) (q .h22)).mono hAH) progM_sndR hpatchM hlogM
      logQM_none fun oa ys hl h => hl ▸ qBudT_redQN h ys)
    hA
  have hop := sim_opens_leN A leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX)
    (extRomN A q qE nG)
  have hor : pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (TabR L))
      (theftSimN A leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX)
        (BadN A (leanVIRX hbX) (leanVSRX hbX) (extRomN A q qE nG))) ≤
      pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (TabR L))
        (theftSimN A leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX)
          (seEvN A (leanVIRX hbX) (leanVSRX hbX) (extRomN A q qE nG))) +
      pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (TabR L))
        (theftSimN A leanSimIR (leanProgIRX hbX) leanSimSR (leanProgSRX hbX)
          (opensN A (extRomN A q qE nG))) := by
    refine (Privacy.pr_mono fun z hz => ?_).trans (pr_or_le _ _)
    obtain ⟨h1, h2, h3 | h3⟩ := hz
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr h3
  linarith

end Sim

end Ratatouille

end VoleMole.Theft
