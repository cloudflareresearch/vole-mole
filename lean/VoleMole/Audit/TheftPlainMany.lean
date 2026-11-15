import VoleMole.Theft.PlainMousManyRom
import VoleMole.Audit.TheftManyR
import VoleMole.Audit.TheftManyHit
import VoleMole.Audit.TheftPlainMous

/-!
# Audit of the many-token theorems with `ROM/`'s plain extraction

* **The hypotheses can hold together.** `noTheftN_lean_rom'` (`Theft/PlainRataManyRom.lean`) is
  instantiated at the trivial adversary of `Audit/TheftManyR.lean` (`thiefNR`, `L = Lmin`), whose
  last stage is the run of `pure op` on the `N` slices, within `QBudT 0 0 0`, for every `U ≥ 1`
  and `M`. `noRedirectN_lean_rom'` (`Theft/PlainMousManyRom.lean`) is instantiated at the
  well-formed trivial adversary of `Audit/TheftManyHit.lean` (`thiefNMW`, `HitWfN`), with
  `L = 8193` (`Lrom`); its one Anchor key is the key of its digest under the constant assignment
  `ktW` (`keysOutN_thiefNMW`).
* For those adversaries the extractors' read budgets are proved (`stageBudgetNX_extRomN`,
  `stageBudgetNX_extRomMN`): `(0, N·312, N·cells + 4608)`.
* `PlainSENL` and `weakSEN_of_plainL` (`Theft/ManyPlainLog.lean`): `PlainSENL` holds with error
  `1` (`plainSENL_one`).

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.TheftPlainMany

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Theft VoleMole.ROM VoleMole.ROM.IC
open OracleComp OracleSpec

variable {U M : ℕ}

section Rat

open VoleMole.Theft.Ratatouille VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille
open VoleMole.Audit.TheftManyR (thiefNR)
open VoleMole.Audit.Theft (zeroSpend)

/-- The trivial adversary's last stage is within `QBudT 0 0 0`. -/
lemma admLN_thiefNR [NeZero U] :
    ∀ iss sp, AdmLN (QBudT 0 0 0) ansPN ((thiefNR Sizes.labelRows U M Tab3
      (ShX (Blk → Blk) pI (XTab Hit.Rata.Lmin Arith.Ratatouille.uovM))).out iss sp) :=
  fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0), ⟨⟨trivial, trivial⟩, trivial⟩,
    rfl⟩

/-- `noTheftN_lean_rom'`'s hypotheses hold for the trivial adversary, with `L = Lmin`. -/
example [NeZero U] :=
  noTheftN_lean_rom' (L := Hit.Rata.Lmin) (thiefNR _ U M _ _) le_rfl admLN_thiefNR

/-- The extractor's read budget for the trivial adversary. -/
example [NeZero U] (iss sp) (l : LogR Sizes.labelRows) :=
  stageBudgetNX_extRomN (L := Hit.Rata.Lmin) (thiefNR _ U M _ _) (admLN_thiefNR iss sp) l

end Rat

section Mous

open VoleMole.Theft.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka
open VoleMole.Audit.TheftManyHit (thiefNMW hitWfN_thiefNMW)
open VoleMole.Audit.Theft (setW ktW)

/-- `thiefNMW`'s output redemptions have the keys of `ktW`. -/
lemma keysOutN_thiefNMW [NeZero U] {G S : Type} : KeysOutN (thiefNMW U M G S) ktW := by
  intro reqs reds g s pk hpk
  simp only [setW, stOfR, List.mem_singleton] at hpk
  subst hpk
  rfl

/-- The well-formed trivial adversary's last stage is within `QBudT 0 0 0`. -/
lemma admLN_thiefNMW [NeZero U] :
    ∀ reqs reds, AdmLN (QBudT 0 0 0) ansPN ((thiefNMW U M Tab3
      (ShX (Blk → Blk) pI (XTab Lrom Arith.Moussaka.M))).out reqs reds) :=
  fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨⟨trivial, trivial⟩, trivial⟩, rfl⟩

/-- `noRedirectN_lean_rom'`'s hypotheses hold for the well-formed trivial adversary, with
`L = Lrom`. -/
example [NeZero U] :=
  noRedirectN_lean_rom' (L := Lrom) (thiefNMW U M _ _) hitWfN_thiefNMW keysOutN_thiefNMW le_rfl
    admLN_thiefNMW

/-- The extractor's read budget for the well-formed trivial adversary. -/
example [NeZero U] (reqs reds) (l : Log) :=
  stageBudgetNX_extRomMN (L := Lrom) (N := U + M) (admLN_thiefNMW (M := M) reqs reds) l

end Mous

end VoleMole.Audit.TheftPlainMany
