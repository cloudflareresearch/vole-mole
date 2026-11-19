import VoleMole.Theft.JointMousNumJ
import VoleMole.Audit.TheftJointZK
import VoleMole.Audit.ZKPoint5

/-!
# Audit of the joint step for Moussaka's redirect game (zk-mous)

* **The headline theorem's hypotheses are met**: `noRedirectN_lean_numJ` is instantiated at the
  well-formed trivial adversary of the earlier audits (`thiefNMW`, `HitWfN`, the keys `ktW`), at
  every per-kind hash budget and the cipher budget `2⁶⁴` and any `U, M ≤ 2³⁰`
  (`noRedirectN_numJ_trivial`), and for every adversary whose last stage is a constant operation
  (`noRedirectN_numJ_const`). The hypotheses of `noRedirectN_lean_numJ` are those of
  `noRedirectN_lean_numL` (`numJ_numL_same`: one list of hypotheses gives both); its bound is
  `2⁻⁵⁴` instead of `(U + M)·2⁻⁵⁵ + 2⁻⁵⁹`.
* **The redirect game is the joint game** (`PN_eq`, `SmP_eq`, `pgP_eq`) and its event is read by
  one consistent game reader (`badGRd_cons`, `badGRd_reads`), within the stated budgets
  (`badGRd_bnd`, `badGRd_T3`, `badGRd_cls`).
* **An empty proof has no `iv`** (`ivA_nil`): a failed real or simulated proof is logged as the
  empty proof (the spec's `getD .empty`), and its slot is charged as an absent `iv`; a successful
  simulation's proof is never empty (`toL_ok_ne`).
* **The refused slots' reserved `iv`s are distinct** (`rsvK_distinct`), and the simulated game's
  `iv`s are the `H₄` table's blocks or absent with no hypothesis (`ivs_view`). The correction for
  refused slots of `Audit/ZKPoint5.lean` applies here too: a redemption slot is refused when the
  token did not finalize or no key of the set verifies it, and without the reserved `iv`s
  (`ivR`) `M = 2³⁰` refused redemptions cost about `2⁻⁴⁶` (`refused_overlap_big`).

The headline theorems' axioms are `propext`, `Classical.choice`, `Quot.sound` only (checked in a
scratch file). No `sorry`, no `axiom`.
-/

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.ZKPointMous

open VoleMole.Privacy VoleMole.ZK VoleMole.ZK.Sim VoleMole.ZK.IC VoleMole.Verifier
  VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.Theft VoleMole.ROM VoleMole.ROM.IC
  VoleMole.ROM.Reads VoleMole.Theft.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka
open VoleMole.Audit.Theft (setW)
open VoleMole.Audit.TheftManyHit (thiefNMW hitWfN_thiefNMW)
open VoleMole.Audit.TheftPlainMany (keysOutN_thiefNMW)

variable {U M L : ℕ}

/-- **A constant last stage is a run within any budget.** -/
theorem admLN_const (q : Kind → ℕ) (qE : ℕ) (op : MOp) :
    AdmLN (N := U + M) (QBud q qE) (ansPN (R := Blk → Blk) (p := pI) (L := L)
      (M := Arith.Moussaka.M)) (fun _ _ => op) :=
  ⟨pure op, ⟨trivial, trivial⟩, rfl⟩

/-- **`noRedirectN_lean_numJ` at the well-formed trivial adversary**, every budget `2⁶⁴`, any
`U, M ≤ 2³⁰`. -/
theorem noRedirectN_numJ_trivial [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabM Lrom))
        (nmRealN (thiefNMW U M Tab3 (TabM Lrom)) (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX)
          (extRomMN (fun _ => 2 ^ 64) (2 ^ 64) (totK Arith.Moussaka.M (fun _ => 2 ^ 64)))) ≤
      1 / 2 ^ 54 + ∑ h : Fin U, owAdv ((thiefNMW U M Tab3 (TabM Lrom)).ci h)
        ((thiefNMW U M Tab3 (TabM Lrom)).cr h)
        (inverterN (thiefNMW U M Tab3 (TabM Lrom)) (leanSim pI) (leanProgIX hbX) (leanSim pR)
          (leanProgRX hbX)
          (extRomMN (L := Lrom) (fun _ => 2 ^ 64) (2 ^ 64) (totK Arith.Moussaka.M (fun _ => 2 ^ 64)))
          h) :=
  noRedirectN_lean_numJ (L := Lrom) (thiefNMW U M _ _) hitWfN_thiefNMW keysOutN_thiefNMW le_rfl
    (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    (fun _ _ => admLN_const _ _ _)

/-- **`noRedirectN_lean_numJ` applies** to every well-formed adversary with the keys of `kt`
whose last stage is a constant operation. -/
theorem noRedirectN_numJ_const (A : ThiefN U M Tab3 (TabM L)) (hw : HitWfN A)
    {kt : Bytes → UOVKey} (hk : KeysOutN A kt)
    (hout : ∃ op : MOp, ∀ reqs reds, A.out reqs reds = fun _ _ => op)
    (hL : Lrom ≤ L) (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabM L))
        (nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX)
          (extRomMN (fun _ => 0) 0 (totK Arith.Moussaka.M (fun _ => 0)))) ≤
      1 / 2 ^ 54 + ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
        (inverterN A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)
          (extRomMN (fun _ => 0) 0 (totK Arith.Moussaka.M (fun _ => 0))) h) := by
  obtain ⟨op, hop⟩ := hout
  exact noRedirectN_lean_numJ A hw hk hL (fun _ => by norm_num) (by norm_num) hU hM
    fun reqs reds => by rw [hop reqs reds]; exact admLN_const _ _ op

/-- **The same hypotheses give both bounds**: `noRedirectN_lean_numL`'s `(U + M)·2⁻⁵⁵ + 2⁻⁵⁹`
and `noRedirectN_lean_numJ`'s `2⁻⁵⁴`. -/
theorem numJ_numL_same (A : ThiefN U M Tab3 (TabM L)) (hw : HitWfN A) {kt : Bytes → UOVKey}
    (hk : KeysOutN A kt) (hL : Lrom ≤ L) {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64)
    (hqE : qE ≤ 2 ^ 64) (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30)
    (hA : ∀ reqs reds, AdmLN (QBud q qE) ansPN (A.out reqs reds)) :
    let P := pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabM L))
      (nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX)
        (extRomMN q qE (totK Arith.Moussaka.M q)))
    let S := ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
      (inverterN A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)
        (extRomMN q qE (totK Arith.Moussaka.M q)) h)
    P ≤ ((U + M : ℕ) : ℝ) / 2 ^ 55 + 1 / 2 ^ 59 + S ∧ P ≤ 1 / 2 ^ 54 + S :=
  ⟨noRedirectN_lean_numL A hw hk hL hq hqE hU hM hA,
    noRedirectN_lean_numJ A hw hk hL hq hqE hU hM hA⟩

/-- **An empty proof has no `iv`.** -/
theorem ivA_nil (x : XM L) (y y' : MI) : ivA x y (some (y', [])) = none := by
  rcases y with y | y <;> simp [ivA]

/-- **The reserved inputs of different slots differ.** -/
theorem rsvK_distinct {i j : ℕ} (hL : 49 ≤ L) (hi : i < 2 ^ 32) (hj : j < 2 ^ 32) (h : i ≠ j) :
    Ratatouille.rsvK (L := L) i ≠ Ratatouille.rsvK j :=
  VoleMole.Audit.ZKPoint5.rsvK_distinct hL hi hj h

/-- **The refused slots' overlap charge without reserved `iv`s** is above `2⁻⁴⁷` at `N = 2³¹`,
`M = 2³⁰`, with `w_E ≥ 221·2⁻¹²⁸`. -/
theorem refused_overlap_big :
    (1 : ℝ) / 2 ^ 47 ≤ 2 * 2 ^ 31 * 2 ^ 30 * (221 / 2 ^ 128 * 4607) :=
  VoleMole.Audit.ZKPoint5.refused_overlap_big

end VoleMole.Audit.ZKPointMous
