import VoleMole.Audit.Theft
import VoleMole.Theft.PlainMous

/-!
# Audit of the theft theorems with plain extraction from the query log

* **The hypotheses can hold together.** `noTheft_leanX_hitL` (`Theft/PlainRata.lean`) and
  `noRedirect_leanX_hitL` (`Theft/PlainMous.lean`) are instantiated at the trivial adversaries of
  `Audit/Theft.lean` (`thief0`, `thiefW`): their last stage is the run of the oracle computation
  `pure op`, within the budget `QBud 0 0` (`hA`); the extractor is constant, so it reads nothing
  (`hX`); plain extraction is taken with error `1` (`plainSEL_one`). The bound then has
  `ε_hit = epsHit 0 0 0`. This checks that the hypotheses are consistent, not that `ε_plain` is
  small.
* **The extractor sees the queries.** `qlog_query_cell`: the query list of a last stage that
  queries one cipher cell `(k, z)` is `[.inr (k, z)]`, whatever the tables; so an extractor of
  `PlainSEL` reads the key `k` of a cipher query off the list (the case `PlainSE`'s `extOf e` misses:
  a key derived from an `H₂³` answer).

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Theft VoleMole.ROM VoleMole.ROM.IC
open OracleComp OracleSpec

/-- **The query list shows the cipher keys**: a last stage that queries the cell `(k, z)` has the
query list `[(k, z)]` on every table. -/
theorem qlog_query_cell {L M : ℕ} (g₁ g₂ : Tab3) (t : ShX (Blk → Blk) pI (XTab L M)) (c : Cell) :
    VoleMole.ROM.Reads.qlog (ansP g₁ g₂ t)
      (liftM (specIC.query (.inr c)) : OracleComp specIC (AnsIC (.inr c))) = [.inr c] := rfl

section Rat

open VoleMole.Theft.Ratatouille VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille

/-- `noTheft_leanX_hitL`'s hypotheses hold for the trivial thief (the run of `pure op`, no query)
and a constant extractor, with `L = Lmin`. -/
example (M : ℕ) :=
  noTheft_leanX_hitL (R := Blk → Blk) (L := Hit.Rata.Lmin) (M := M) (thief0 _ _ _) le_rfl
    (e := fun _ _ _ _ _ _ _ => wit0) (q := 0) (qE := 0) (x3 := 0) (x5 := 0) (xE := 0) (ε₀ := 1)
    (fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0), ⟨trivial, trivial⟩, rfl⟩)
    (fun _ _ _ => StageBudget.const _) (plainSEL_one _ _ _ _ _ _)

end Rat

section Mous

open VoleMole.Theft.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka

/-- `noRedirect_leanX_hitL`'s hypotheses hold for the well-formed trivial adversary (the run of
`pure op`, no query) and a constant extractor, with `L = Lmin`. -/
example (M : ℕ) :=
  noRedirect_leanX_hitL (R := Blk → Blk) (L := Hit.Mous.Lmin) (M := M) (thiefW _ _) hitWf_thiefW
    le_rfl (e := fun _ _ _ _ _ _ _ => []) (q := 0) (qE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (ε₀ := 1)
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩)
    (fun _ _ _ => StageBudget.const _) (plainSEL_one _ _ _ _ _ _)

end Mous

end VoleMole.Audit.Theft
