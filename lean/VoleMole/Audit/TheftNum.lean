import VoleMole.Theft.Num
import VoleMole.Audit.TheftPlainPerm

/-!
# Audit of the numeric theft theorems and of the collision bounds

* The ten numeric headline theorems (`Theft/Num.lean`) are instantiated at the trivial adversaries
  of the earlier audits, **at the largest budgets they allow**: every per-kind hash budget and the
  cipher budget `2⁶⁴`, and in the games with many tokens any `U, M ≤ 2³⁰`. One Client or token:
  `noTheft_lean_num`, `noTheft_lean_numP` (also at `thiefInv`, an inverse cipher query),
  `noRedirect_lean_num`, `noRedirect_lean_numP`; `U` tokens: `noTheftN_lean_num`,
  `noTheftN_lean_numP`, `noRedirectN_lean_num`, `noRedirectN_lean_numP`, `nmUN_lean_num`,
  `nmUN_lean_numP`.
* The collision bounds (`Theft/DeltaBound.lean`) are instantiated at the theorems' tables (`hbX`
  on `XTab`, both row types).
* The parameter facts behind the permutation-row bound (`PermOk`: one hidden-row block, at most
  `56` VOLE column blocks) are checked for the six parameter sets, and `zkB` at one Client's
  budgets is below `2⁻⁵⁵`.

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.TheftNum

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Theft VoleMole.ROM VoleMole.ROM.IC
open VoleMole.ROM.Reads VoleMole.Verifier
open OracleComp OracleSpec

/-! ## The numbers -/

set_option exponentiation.threshold 300 in
/-- One hop's zero-knowledge error at one Client's budgets is below `2⁻⁵⁵`. -/
example : zkB (2 ^ 65) (2 ^ 65 + 1560) (2 ^ 65 + 2 ^ 18) ≤ 1 / 2 ^ 55 := by
  norm_num [zkB]

/-- The permutation-row bound applies to the six parameter sets. -/
example : PermOk Privacy.Ratatouille.pI ∧ PermOk Privacy.Ratatouille.pS ∧
    PermOk Privacy.Moussaka.pI ∧ PermOk Privacy.Moussaka.pR ∧
    PermOk Privacy.MoussakaUnbound.pI ∧ PermOk Privacy.MoussakaUnbound.pR :=
  ⟨permOk_pIR, permOk_pSR, permOk_pIM, permOk_pRM, permOk_pIU, permOk_pRU⟩

section Rat

open VoleMole.Theft.Ratatouille VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille
open VoleMole.Audit.Theft (thief0 zeroSpend)
open VoleMole.Audit.TheftPerm (thiefInv admL_thiefInv)

/-- `deltaS_le` at the theorem's tables. -/
example (A : Thief Sizes.labelRows Tab3
    (ShX (Blk → Blk) pI (XTab Hit.Rata.Lmin Arith.Ratatouille.uovM))) :=
  deltaS_le (R := Blk → Blk) hbX_wf A

/-- `noTheft_lean_num` at the trivial thief, every budget `2⁶⁴`. -/
example := noTheft_lean_num (L := Hit.Rata.Lmin) (thief0 _ _ _) le_rfl
  (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl
  fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0), ⟨trivial, trivial⟩, rfl⟩

/-- `noTheft_lean_numP` at the trivial thief with permutation rows, every budget `2⁶⁴`. -/
example := noTheft_lean_numP (L := Hit.Rata.Lmin) (thief0 _ _ _) le_rfl
  (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl
  fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0), ⟨trivial, trivial⟩, rfl⟩

/-- `noTheft_lean_numP` at a thief with an inverse cipher query. -/
example := noTheft_lean_numP (L := Hit.Rata.Lmin) thiefInv le_rfl (q := 0) (qE := 1)
  (fun _ => by simp) (by norm_num) admL_thiefInv

end Rat

section Many

open VoleMole.Theft.Ratatouille VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille
open VoleMole.Audit.TheftManyR (thiefNR)
open VoleMole.Audit.Theft (zeroSpend)

variable {U M : ℕ}

/-- `deltaNR_le` at the theorem's tables, permutation rows. -/
example (A : ThiefN Sizes.labelRows U M Tab3
    (ShX (Equiv.Perm Blk) pI (XTab Hit.Rata.Lmin Arith.Ratatouille.uovM))) (i : Fin (U + M)) :=
  deltaNR_le (R := Equiv.Perm Blk) hbX_wf A i

/-- `noTheftN_lean_num` at the trivial adversary, every budget `2⁶⁴`, any `U, M ≤ 2³⁰`. -/
example [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) :=
  noTheftN_lean_num (L := Hit.Rata.Lmin) (thiefNR _ U M _ _) le_rfl (q := fun _ => 2 ^ 64)
    (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0), ⟨trivial, trivial⟩, rfl⟩

/-- `noTheftN_lean_numP` at the trivial adversary with permutation rows, every budget `2⁶⁴`,
any `U, M ≤ 2³⁰`. -/
example [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) :=
  noTheftN_lean_numP (L := Hit.Rata.Lmin) (thiefNR _ U M _ _) le_rfl (q := fun _ => 2 ^ 64)
    (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0), ⟨trivial, trivial⟩, rfl⟩

end Many

section Mous

open VoleMole.Theft.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka
open VoleMole.Audit.Theft (setW ktW keysOut_thiefW thiefW hitWf_thiefW)
open VoleMole.Audit.TheftManyHit (thiefNMW hitWfN_thiefNMW)
open VoleMole.Audit.TheftPlainMany (keysOutN_thiefNMW)

variable {U M : ℕ}

/-- `deltaR_le` at the theorem's tables. -/
example (A : Thief Tab3 (ShX (Blk → Blk) pI (XTab Lrom Arith.Moussaka.M))) :=
  deltaR_le (R := Blk → Blk) hbX_wf A

/-- `noRedirect_lean_num` at the well-formed trivial adversary, every budget `2⁶⁴`. -/
example :=
  noRedirect_lean_num (L := Lrom) (thiefW _ _) hitWf_thiefW keysOut_thiefW le_rfl
    (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩)

/-- `noRedirect_lean_numP` at the well-formed trivial adversary with permutation rows, every
budget `2⁶⁴`. -/
example :=
  noRedirect_lean_numP (L := Lrom) (thiefW _ _) hitWf_thiefW keysOut_thiefW le_rfl
    (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩)

/-- `noRedirectN_lean_num` at the well-formed trivial adversary, every budget `2⁶⁴`, any
`U, M ≤ 2³⁰`. -/
example [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) :=
  noRedirectN_lean_num (L := Lrom) (thiefNMW U M _ _) hitWfN_thiefNMW keysOutN_thiefNMW le_rfl
    (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩)

/-- `noRedirectN_lean_numP` at the well-formed trivial adversary with permutation rows. -/
example [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) :=
  noRedirectN_lean_numP (L := Lrom) (thiefNMW U M _ _) hitWfN_thiefNMW keysOutN_thiefNMW le_rfl
    (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩)

end Mous

section Unbound

open VoleMole.Theft.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
  VoleMole.Privacy.MoussakaUnbound
open VoleMole.Spec.Moussaka (ctxBytes cdBytes)
open VoleMole.Audit.TheftManyHit (thiefNUW hitWfN_thiefNUW)
open VoleMole.Audit.Theft (setW ktW)
open VoleMole.Audit.UnboundRest (prf1Adv_le_one)
open VoleMole.Audit.TheftPlainUnbound (keysOutNU_thiefNUW)

variable {U M : ℕ}

/-- `nmUN_lean_num` at the well-formed trivial adversary, every budget `2⁶⁴`, any
`U, M ≤ 2³⁰`. -/
example [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) (pts : Fin (M + 1) → Coins ctxBytes)
    (hpts : Function.Injective pts) :=
  nmUN_lean_num (L := LminU) (thiefNUW U M _ _) hitWfN_thiefNUW keysOutNU_thiefNUW le_rfl
    (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩) pts hpts
    (fun _ _ => prf1Adv_le_one _ _)

/-- `nmUN_lean_numP` at the well-formed trivial adversary with permutation rows. -/
example [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) (pts : Fin (M + 1) → Coins ctxBytes)
    (hpts : Function.Injective pts) :=
  nmUN_lean_numP (L := LminU) (thiefNUW U M _ _) hitWfN_thiefNUW keysOutNU_thiefNUW le_rfl
    (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩) pts hpts
    (fun _ _ => prf1Adv_le_one _ _)

end Unbound

end VoleMole.Audit.TheftNum
