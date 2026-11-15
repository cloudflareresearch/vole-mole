import VoleMole.Audit.Theft
import VoleMole.Theft.PlainRataRom

/-!
# Audit of no theft with `ROM/`'s plain extraction

* **The hypotheses can hold together.** `noTheft_lean_rom` (`Theft/PlainRataRom.lean`) is
  instantiated at the trivial thief of `Audit/Theft.lean` (`thief0`, `L = Lmin`): its last stage
  is the run of `pure op`, within `QBudT 0 0 0` (`hA`). The extractor is `ROM/`'s, fixed by the
  theorem; its read budget (`hX`, item 4 (d) of `docs/security/ratatouille.md` §5) is taken here
  at the sizes of the tables (`stageBudget_univ`: a stage reads at most every key). This checks
  that the hypotheses are consistent, not that the zero-knowledge terms are small at that budget.
* `plainSEL_rom` has no hypothesis but the table length (`L ≥ Lmin`); its error is
  `epsRom` (`epsRom_ne_top`: finite).

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Theft VoleMole.ROM VoleMole.ROM.IC
open OracleComp OracleSpec

set_option maxRecDepth 100000 in
/-- **Every stage reads at most every key.** -/
lemma stageBudget_univ {R : Type} [CipherRow R] {p : VoleMole.Verifier.Params} {X : Type}
    (F : Tab3 → Tab3 → ShG R p → X) :
    StageBudget F (Fintype.card (Bytes 16)) (Fintype.card (Bytes 37)) (Fintype.card Blk) := by
  refine ⟨fun g₂ s => ⟨fun _ => Finset.univ, fun _ => Finset.card_le_univ _, fun g g' h => ?_⟩,
    fun g₁ s => ⟨fun _ => Finset.univ, fun _ => Finset.card_le_univ _, fun g g' h => ?_⟩,
    fun g₁ g₂ => ⟨fun _ => Finset.univ, fun _ => Finset.card_le_univ _, fun s G5 h => ?_⟩,
    fun g₁ g₂ => ⟨fun _ => Finset.univ, fun _ => Finset.card_le_univ _, fun s E h => ?_⟩⟩
  · rw [show g' = g from funext fun k => (h k (Finset.mem_univ _)).symm]
  · rw [show g' = g from funext fun k => (h k (Finset.mem_univ _)).symm]
  · rw [show G5 = s.2.1 from funext fun k => (h k (Finset.mem_univ _)).symm]
  · rw [show E = s.2.2 from funext fun k => (h k (Finset.mem_univ _)).symm]

section Rat

open VoleMole.Theft.Ratatouille VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille

/-- `noTheft_lean_rom`'s hypotheses hold for the trivial thief (the run of `pure op`, no query),
with `L = Lmin` and the extractor's read budget at the table sizes. -/
example :=
  noTheft_lean_rom (L := Hit.Rata.Lmin) (thief0 _ _ _) le_rfl (q := 0) (qE := 0) (nG := 0)
    (fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0),
      ⟨⟨trivial, trivial⟩, trivial⟩, rfl⟩)
    (fun _ _ _ => stageBudget_univ _)

end Rat

end VoleMole.Audit.Theft
