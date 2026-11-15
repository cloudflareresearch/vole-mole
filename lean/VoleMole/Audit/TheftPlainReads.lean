import VoleMole.Audit.TheftPlainRom
import VoleMole.Theft.PlainRataReads

/-!
# Audit of no theft with `ROM/`'s plain extraction and its read budget

* **The hypotheses can hold together.** `noTheft_lean_rom'` (`Theft/PlainRataReads.lean`) has no
  read-budget hypothesis; it is instantiated at the trivial thief of `Audit/Theft.lean` (`thief0`,
  `L = Lmin`), whose last stage is the run of `pure op`, within `QBudT 0 0 0`.
* For that thief the extractor's read budget is `(0, 624, 202744)` (`stageBudgetX_extRom`): the two
  prefixes' `H₅` gate inputs and cells, the reconstruction's rows and the zero key's.

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Theft VoleMole.ROM VoleMole.ROM.IC
open OracleComp OracleSpec

section Rat

open VoleMole.Theft.Ratatouille VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille

/-- The trivial thief's last stage is within `QBudT 0 0 0`. -/
lemma admL_thief0 :
    ∀ o₁ o₂, AdmL (QBudT 0 0 0) ansP ((thief0 Sizes.labelRows Tab3
      (ShX (Blk → Blk) pI (XTab Hit.Rata.Lmin Arith.Ratatouille.uovM))).out o₁ o₂) :=
  fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0), ⟨⟨trivial, trivial⟩, trivial⟩, rfl⟩

/-- `noTheft_lean_rom'`'s hypotheses hold for the trivial thief, with `L = Lmin`. -/
example := noTheft_lean_rom' (L := Hit.Rata.Lmin) (thief0 _ _ _) le_rfl admL_thief0

/-- The extractor's read budget for the trivial thief. -/
example (o₁ o₂) := stageBudgetX_extRom (L := Hit.Rata.Lmin) (thief0 _ _ _) admL_thief0 o₁ o₂

end Rat

end VoleMole.Audit.Theft
