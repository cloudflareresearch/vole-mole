import VoleMole.Theft.PlainRataPermReads
import VoleMole.Theft.PlainMousPermReads
import VoleMole.Theft.PlainRataManyPerm
import VoleMole.Theft.PlainMousManyPerm
import VoleMole.Theft.PlainUnboundManyPerm
import VoleMole.Theft.PlainTotalRom
import VoleMole.Audit.TheftPlainReads
import VoleMole.Audit.TheftPlainMany
import VoleMole.Audit.TheftPlainUnbound

/-!
# Audit of the theft theorems with permutation rows and without a total hash budget

* **Permutation rows, inverse queries.** `noTheft_lean_romP'` (`Theft/PlainRataPermReads.lean`)
  is instantiated at the trivial thief of `Audit/Theft.lean` (`thief0`, `L = Lmin`) on the tables
  with permutation rows, and at a thief whose last stage makes one **inverse** cipher query
  (`admL_thiefInv`, within `QBudP 0 1`): the class of adversaries contains inverse queries.
  `epsRomP` is finite below `2¹²⁸ − 4607` cipher queries (`epsRomP_ne_top`).
* `noTheftN_lean_romP'` (`Theft/PlainRataManyPerm.lean`) is instantiated at the trivial
  adversary of `Audit/TheftManyR.lean` (`thiefNR`, `U = M = 1`) with permutation rows, and
  `noRedirectN_lean_romP'` (`Theft/PlainMousManyPerm.lean`) at `thiefNMW` (`U = M = 1`), and
  `nmUN_lean_romP'` (`Theft/PlainUnboundManyPerm.lean`) at `thiefNUW` (`U = M = 1`).
* `noRedirect_lean_romP'` (`Theft/PlainMousPermReads.lean`) is instantiated at the well-formed
  trivial adversary of `Audit/TheftPlainMous.lean` (`thiefW`, `L = Lrom`) with permutation rows.
* **No total budget.** `noTheft_lean_romK`, `noTheftN_lean_romK`, `noRedirect_lean_romK`,
  `noRedirectN_lean_romK`, `nmUN_lean_romK` (`Theft/PlainTotalRom.lean`) are instantiated at the
  trivial adversaries of the audits of the `*_lean_rom'` theorems, within `QBud 0 0` (no total
  hash budget). `noTheft_lean_romK` is also instantiated at a thief that makes one hash query of
  kind `H_comb` with a parameter other than `uovM` (`admL_thiefComb`): a kind outside `kindsT uovM`
  that per-kind bounds allow and the total `totK uovM q = 0` does not count (the query is off the
  table points, answered by SHAKE).

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.TheftPerm

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Theft VoleMole.ROM VoleMole.ROM.IC
open VoleMole.ROM.Reads VoleMole.Verifier
open OracleComp OracleSpec

section Rat

open VoleMole.Theft.Ratatouille VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille
open VoleMole.Audit.Theft (thief0 zeroSpend)

/-- One inverse cipher query, then a fixed spend. -/
noncomputable def oaInv : OracleComp specP (Op Sizes.labelRows) :=
  liftM (specP.query (.inr (false, (0, 0)))) >>= fun _ =>
    pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0)

/-- A thief whose last stage makes one inverse cipher query, then outputs a fixed spend. -/
noncomputable def thiefInv : Thief Sizes.labelRows Tab3
    (ShX (Equiv.Perm Blk) pI (XTab Hit.Rata.Lmin Arith.Ratatouille.uovM)) :=
  { thief0 Sizes.labelRows Tab3
      (ShX (Equiv.Perm Blk) pI (XTab Hit.Rata.Lmin Arith.Ratatouille.uovM)) with
    out := fun _ _ g₁ g₂ t => runT (ansQ g₁ g₂ t) oaInv }

/-- `thiefInv`'s last stage is within `QBudP 0 1`: one inverse query, no hash query. -/
lemma admL_thiefInv : ∀ o₁ o₂, AdmL (QBudP 0 1) ansQ (thiefInv.out o₁ o₂) :=
  fun _ _ => ⟨oaInv, ⟨(isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨trivial, fun _ => trivial⟩,
    (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr (by decide), fun _ => trivial⟩⟩, rfl⟩

/-- `noTheft_lean_romP'`'s hypotheses hold for a thief with an inverse query, `L = Lmin`. -/
example := noTheft_lean_romP' (L := Hit.Rata.Lmin) thiefInv le_rfl (q := 0) (qE := 1)
  (by norm_num) admL_thiefInv

/-- `noTheft_lean_romP'`'s hypotheses hold for the trivial thief with permutation rows. -/
example := noTheft_lean_romP' (L := Hit.Rata.Lmin) (thief0 _ _ _) le_rfl (q := 0) (qE := 0)
  (by norm_num) fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0),
    ⟨trivial, trivial⟩, rfl⟩

/-- The error of `plainSEL_romP` is finite below `2¹²⁸ − 4607` cipher queries. -/
example (q : Kind → ℕ) (qE nG : ℕ) (h : qE + 4607 < 2 ^ 128) : epsRomP q qE nG ≠ ⊤ :=
  epsRomP_ne_top q nG h

/-- `noTheft_lean_romK`'s hypotheses hold for the trivial thief, within `QBud 0 0`. -/
example := noTheft_lean_romK (L := Hit.Rata.Lmin) (thief0 _ _ _) le_rfl (q := 0) (qE := 0)
  fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0), ⟨trivial, trivial⟩, rfl⟩

/-- The kind `H_comb` at a parameter other than `uovM` is not a kind of the table points. -/
example : Kind.comb 7 ∉ kindsT Arith.Ratatouille.uovM := by
  simp only [kindsT, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, Kind.comb.injEq,
    false_or]
  decide

/-- One hash query of kind `H_comb` at the parameter `7`, then a fixed spend. -/
noncomputable def oaComb : OracleComp specIC (Op Sizes.labelRows) :=
  liftM (specIC.query (.inl (.comb 7, ByteArray.empty))) >>= fun _ =>
    pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0)

/-- A thief whose last stage makes one hash query of kind `H_comb` at the parameter `7`. -/
noncomputable def thiefComb : Thief Sizes.labelRows Tab3
    (ShX (Blk → Blk) pI (XTab Hit.Rata.Lmin Arith.Ratatouille.uovM)) :=
  { thief0 Sizes.labelRows Tab3
      (ShX (Blk → Blk) pI (XTab Hit.Rata.Lmin Arith.Ratatouille.uovM)) with
    out := fun _ _ g₁ g₂ t => runT (ansP g₁ g₂ t) oaComb }

/-- `thiefComb`'s last stage is within `QBud q 0` with one `H_comb` query at `7`; its total over
`kindsT uovM` is `0`. -/
lemma admL_thiefComb :
    ∀ o₁ o₂, AdmL (QBud (Function.update 0 (.comb 7) 1) 0) ansP (thiefComb.out o₁ o₂) :=
  fun _ _ => ⟨oaComb, ⟨(isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨by simp, fun _ => trivial⟩,
    (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp), fun _ => trivial⟩⟩, rfl⟩

example : totK Arith.Ratatouille.uovM (Function.update 0 (.comb 7) 1) = 0 := by
  simp [totK, kindsT, Function.update, Arith.Ratatouille.uovM]

/-- `noTheft_lean_romK`'s hypotheses hold for `thiefComb`. -/
example := noTheft_lean_romK (L := Hit.Rata.Lmin) thiefComb le_rfl admL_thiefComb

end Rat

section Many

open VoleMole.Theft.Ratatouille VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille
open VoleMole.Audit.TheftManyR (thiefNR)
open VoleMole.Audit.Theft (zeroSpend)

variable {U M : ℕ}

/-- `noTheftN_lean_romK`'s hypotheses hold for the trivial adversary, within `QBud 0 0`. -/
example [NeZero U] :=
  noTheftN_lean_romK (L := Hit.Rata.Lmin) (thiefNR _ U M _ _) le_rfl (q := 0) (qE := 0)
    fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0), ⟨trivial, trivial⟩, rfl⟩

/-- `noTheftN_lean_romP'`'s hypotheses hold for the trivial adversary with permutation rows, one
Client and one spend. -/
example :=
  noTheftN_lean_romP' (L := Hit.Rata.Lmin) (U := 1) (M := 1) (thiefNR _ 1 1 _ _) le_rfl (q := 0)
    (qE := 0) (by norm_num)
    fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0), ⟨trivial, trivial⟩, rfl⟩

end Many

section Mous

open VoleMole.Theft.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka
open VoleMole.Audit.Theft (setW ktW keysOut_thiefW thiefW hitWf_thiefW)
open VoleMole.Audit.TheftManyHit (thiefNMW hitWfN_thiefNMW)
open VoleMole.Audit.TheftPlainMany (keysOutN_thiefNMW)

variable {U M : ℕ}

/-- `noRedirect_lean_romP'`'s hypotheses hold for the well-formed trivial adversary with
permutation rows. -/
example :=
  noRedirect_lean_romP' (L := Lrom) (thiefW _ _) hitWf_thiefW keysOut_thiefW le_rfl
    (q := 0) (qE := 0) (by norm_num)
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩)

/-- The error of `plainSEL_romMP` is finite below `2¹²⁸ − 4607` cipher queries. -/
example (q : Kind → ℕ) (qE nG : ℕ) (h : qE + 4607 < 2 ^ 128) : epsRomMP q qE nG ≠ ⊤ :=
  epsRomMP_ne_top q nG h

/-- `noRedirect_lean_romK`'s hypotheses hold for the well-formed trivial adversary. -/
example :=
  noRedirect_lean_romK (L := Lrom) (thiefW _ _) hitWf_thiefW keysOut_thiefW le_rfl
    (q := 0) (qE := 0)
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩)

/-- `noRedirectN_lean_romK`'s hypotheses hold for the well-formed trivial adversary. -/
example [NeZero U] :=
  noRedirectN_lean_romK (L := Lrom) (thiefNMW U M _ _) hitWfN_thiefNMW keysOutN_thiefNMW le_rfl
    (q := 0) (qE := 0)
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩)

/-- `noRedirectN_lean_romP'`'s hypotheses hold for the well-formed trivial adversary with
permutation rows, one token and one redemption. -/
example :=
  noRedirectN_lean_romP' (L := Lrom) (U := 1) (M := 1) (thiefNMW 1 1 _ _) hitWfN_thiefNMW
    keysOutN_thiefNMW le_rfl (q := 0) (qE := 0) (by norm_num)
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

/-- `nmUN_lean_romK`'s hypotheses hold for the well-formed trivial adversary. -/
example [NeZero U] (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts) :=
  nmUN_lean_romK (L := LminU) (thiefNUW U M _ _) hitWfN_thiefNUW keysOutNU_thiefNUW le_rfl
    (q := 0) (qE := 0)
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩) pts hpts
    (fun _ _ => prf1Adv_le_one _ _)

/-- `nmUN_lean_romP'`'s hypotheses hold for the well-formed trivial adversary with permutation
rows, one token and one redemption. -/
example (pts : Fin (1 + 1) → Coins ctxBytes) (hpts : Function.Injective pts) :=
  nmUN_lean_romP' (L := LminU) (U := 1) (M := 1) (thiefNUW 1 1 _ _) hitWfN_thiefNUW
    keysOutNU_thiefNUW le_rfl (q := 0) (qE := 0) (by norm_num)
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩) pts hpts
    (fun _ _ => prf1Adv_le_one _ _)

end Unbound

end VoleMole.Audit.TheftPerm
