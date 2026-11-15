import VoleMole.Audit.TheftPlainRom
import VoleMole.Theft.PlainMousRedirect

/-!
# Audit of redemption non-malleability with `ROM/`'s plain extraction

* **The hypotheses can hold together.** `noRedirect_lean_rom` (`Theft/PlainMousRedirect.lean`) is
  instantiated at the well-formed trivial adversary of `Audit/Theft.lean` (`thiefW`, `HitWf` by
  `hitWf_thiefW`), with `L = 8193` (`Lrom`): its last stage is the run of `pure op`, within
  `QBudT 0 0 0`; its one Anchor key is the key of its digest under the constant assignment
  `ktW` (`keysOut_thiefW`). The extractor's read budget is taken at the table sizes
  (`stageBudget_univ`), which checks consistency only.
* `plainSEL_romM` has no hypothesis but the table length; its error `epsRomM` is finite
  (`epsRomM_ne_top`).

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Theft VoleMole.ROM VoleMole.ROM.IC
open OracleComp OracleSpec

section Mous

open VoleMole.Theft.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka

/-- The key assignment of `thiefW`: every digest names its one Anchor key. -/
def ktW : Bytes → UOVKey := fun _ => ⟨List.replicate digestBytes 0, fun _ => 0⟩

/-- `thiefW`'s output redemptions have the keys of `ktW`. -/
lemma keysOut_thiefW {G S : Type} : KeysOut (thiefW G S) ktW := by
  intro o₁ o₂ g₁ g₂ s pk hpk
  simp only [setW, stOfR, List.mem_singleton] at hpk
  subst hpk
  rfl

/-- `noRedirect_lean_rom`'s hypotheses hold for the well-formed trivial adversary, with
`L = Lrom` and the extractor's read budget at the table sizes. -/
example :=
  noRedirect_lean_rom (L := Lrom) (thiefW _ _) hitWf_thiefW keysOut_thiefW le_rfl
    (q := 0) (qE := 0) (nG := 0)
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨⟨trivial, trivial⟩, trivial⟩, rfl⟩)
    (fun _ _ _ => stageBudget_univ _)

example (q : Kind → ℕ) (qE nG : ℕ) : epsRomM q qE nG ≠ ⊤ := epsRomM_ne_top q qE nG

end Mous

end VoleMole.Audit.Theft
