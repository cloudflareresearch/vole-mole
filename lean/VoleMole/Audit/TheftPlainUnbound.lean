import VoleMole.Theft.PlainUnboundManyRom
import VoleMole.Audit.TheftManyHit
import VoleMole.Audit.TheftPlainMous
import VoleMole.Audit.UnboundMany

/-!
# Audit of unbound Moussaka with `ROM/`'s plain extraction

* **The hypotheses can hold together.** `nmUN_lean_rom'` (`Theft/PlainUnboundManyRom.lean`) is
  instantiated at the well-formed trivial unbound adversary of `Audit/TheftManyHit.lean`
  (`thiefNUW`, `HitWfN`), with `L = 9749` (`LminU`), for every `U ≥ 1` and `M`, and with an
  injective family of `M + 1` contexts (any family; one exists for `M < 2¹²⁸`, `exists_pts`); its
  one Anchor key is the key of its digest under the constant assignment `ktW`
  (`keysOutNU_thiefNUW`); its last stage is the run of `pure op` on the `N` slices, within
  `QBudT 0 0 0` (`admLN_thiefNUW`). `nmUN_lean_rom_one` is instantiated at `U = M = 1`. The PRF
  hypothesis is taken with `ε_prf = 1` (`prf1Adv_le_one`).
* For that adversary the extractor's read budget is proved (`stageBudgetNX_extRomUN`):
  `(0, N·312, N·cells(pR) + 4608)`.
* `plainSEL_romU` has no hypothesis but the table length; its error `epsRomU` is finite
  (`epsRomU_ne_top`).

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.TheftPlainUnbound

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Theft VoleMole.ROM VoleMole.ROM.IC
open VoleMole.Theft.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
  VoleMole.Privacy.MoussakaUnbound
open VoleMole.Spec.Moussaka (ctxBytes cdBytes)
open VoleMole.Audit.TheftManyHit (thiefNUW hitWfN_thiefNUW)
open VoleMole.Audit.Theft (setW ktW)
open VoleMole.Audit.UnboundRest (prf1Adv_le_one)
open OracleComp OracleSpec

variable {U M : ℕ}

/-- `thiefNUW`'s output redemptions have the keys of `ktW`. -/
lemma keysOutNU_thiefNUW [NeZero U] {G S : Type} : KeysOutNU (thiefNUW U M G S) ktW := by
  intro reqs reds g s pk hpk
  simp only [toBound, setW, stOfR, List.mem_singleton] at hpk
  subst hpk
  rfl

/-- The well-formed trivial adversary's last stage is within `QBudT 0 0 0`. -/
lemma admLN_thiefNUW [NeZero U] :
    ∀ reqs reds, AdmLN (QBudT 0 0 0) ansPN ((thiefNUW U M Tab3
      (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab LminU Arith.Moussaka.M))).out reqs reds) :=
  fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨⟨trivial, trivial⟩, trivial⟩, rfl⟩

/-- `nmUN_lean_rom'`'s hypotheses hold for the well-formed trivial adversary, with
`L = LminU`. -/
example [NeZero U] (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts) :=
  nmUN_lean_rom' (L := LminU) (thiefNUW U M _ _) hitWfN_thiefNUW keysOutNU_thiefNUW le_rfl
    admLN_thiefNUW pts hpts (fun _ _ => prf1Adv_le_one _ _)

/-- `nmUN_lean_rom_one`'s hypotheses hold for the well-formed trivial adversary with one token
and one redemption. -/
example (pts : Fin (1 + 1) → Coins ctxBytes) (hpts : Function.Injective pts) :=
  nmUN_lean_rom_one (L := LminU) (thiefNUW 1 1 _ _) hitWfN_thiefNUW keysOutNU_thiefNUW le_rfl
    admLN_thiefNUW pts hpts (fun _ _ => prf1Adv_le_one _ _)

/-- The extractor's read budget for the well-formed trivial adversary. -/
example [NeZero U] (reqs reds) (l : Log) :=
  stageBudgetNX_extRomUN (L := LminU) (N := U + M) (admLN_thiefNUW (M := M) reqs reds) l

/-- The error of `plainSEL_romU` is finite. -/
example (q : Kind → ℕ) (qE nG : ℕ) : epsRomU q qE nG ≠ ⊤ := epsRomU_ne_top q qE nG

end VoleMole.Audit.TheftPlainUnbound
