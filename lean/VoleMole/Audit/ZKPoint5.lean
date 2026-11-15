import VoleMole.Theft.JointNumJ

/-!
# Audit of the joint step for Ratatouille's theft game (zk-point5)

* **The headline theorem's hypotheses are met**: an adversary whose last stage is a constant
  operation is a run within any budget (`admLN_const`), so `noTheftN_lean_numJ` applies to it
  (`noTheftN_numJ_const`). The hypotheses of `noTheftN_lean_numJ` are those of
  `noTheftN_lean_numL` (per-kind budgets and the cipher budget `≤ 2⁶⁴`, `U, M ≤ 2³⁰`,
  `L ≥ Lmin`); its bound is `2⁻⁵⁴` instead of `(U + M)·2⁻⁵⁵ + 2⁻⁵⁹`.
* **The theft game is the joint game** (`PN_eq`, `SmP_eq`, `pgP_eq`) and its event is read by one
  consistent game reader (`badGRd_cons`, `badGRd_reads`), within the stated budgets
  (`badGRd_bnd`, `badGRd_T3`, `badGRd_cls`).
* **The refused slots' reserved `iv`s are distinct** (`rsvK_inj`), and the simulated game's
  `iv`s are the `H₄` table's blocks or absent with no hypothesis (`ivs_view`).
* **Correction (refused slots)**: with no `iv`, a refused slot is charged to every other slot
  through the overlap term; with `M = 2³⁰` refused spends among `N = 2³¹` slots that term,
  `2N·M·w_E·4607`, is about `2⁻⁴⁶` (`refused_overlap_big`: above `2⁻⁴⁷`), far above the `2⁻⁵⁴`
  target. The reserved `iv`s (`ivR`) remove it.

The headline theorems' axioms are `propext`, `Classical.choice`, `Quot.sound` only (checked in a
scratch file). No `sorry`, no `axiom`.
-/

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.ZKPoint5

open VoleMole.Privacy VoleMole.ZK VoleMole.ZK.Sim VoleMole.ZK.IC VoleMole.Verifier
  VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.Theft VoleMole.ROM VoleMole.ROM.IC
  VoleMole.ROM.Reads VoleMole.Theft.Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

/-- **A constant last stage is a run within any budget.** -/
theorem admLN_const {U M L : ℕ} (q : Kind → ℕ) (qE : ℕ) (op : Op Sizes.labelRows) :
    AdmLN (N := U + M) (QBud q qE) (ansPN (R := Blk → Blk) (p := pI) (L := L)
      (M := Arith.Ratatouille.uovM)) (fun _ _ => op) :=
  ⟨pure op, ⟨trivial, trivial⟩, rfl⟩

/-- **`noTheftN_lean_numJ` applies** to every adversary whose last stage is a constant operation. -/
theorem noTheftN_numJ_const {U M L : ℕ} (A : ThiefN Sizes.labelRows U M Tab3 (TabR L))
    (hout : ∃ op : Op Sizes.labelRows, ∀ iss sp, A.out iss sp = fun _ _ => op)
    (hL : Hit.Rata.Lmin ≤ L) (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (TabR L))
        (theftRealN A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
          (extRomN A (fun _ => 0) 0 (totK Arith.Ratatouille.uovM (fun _ => 0)))) ≤
      1 / 2 ^ 54 + ∑ j : Fin (U + M), owAdvK (inverterN A leanSimIR (leanProgIRX hbX) leanSimSR
        (leanProgSRX hbX) (extRomN A (fun _ => 0) 0 (totK Arith.Ratatouille.uovM (fun _ => 0))) j) := by
  obtain ⟨op, hop⟩ := hout
  exact noTheftN_lean_numJ A hL (fun _ => by norm_num) (by norm_num) hU hM fun iss sp => by
    rw [hop iss sp]; exact admLN_const _ _ op

/-- **The reserved inputs of different slots differ.** -/
theorem rsvK_distinct {L i j : ℕ} (hL : 49 ≤ L) (hi : i < 2 ^ 32) (hj : j < 2 ^ 32) (h : i ≠ j) :
    rsvK (L := L) i ≠ rsvK j := fun e => h (rsvK_inj (by omega) hi hj e)

/-- **The refused slots' overlap charge without reserved `iv`s** is above `2⁻⁴⁷` at `N = 2³¹`,
`M = 2³⁰`, with `w_E ≥ 221·2⁻¹²⁸`. -/
theorem refused_overlap_big : (1 : ℝ) / 2 ^ 47 ≤ 2 * 2 ^ 31 * 2 ^ 30 * (221 / 2 ^ 128 * 4607) := by
  norm_num

/-- **Grinding fails with probability at most `2⁻¹¹³`**, so the failed simulations' term is tiny. -/
theorem pFail_small : pFail ≤ 1 / 2 ^ 113 := pFail_le

end VoleMole.Audit.ZKPoint5
