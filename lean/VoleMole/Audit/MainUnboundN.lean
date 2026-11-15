import VoleMole.Audit.MainUnboundAll
import VoleMole.Privacy.MoussakaUnboundNCMainLeanN

/-!
# Audit of Theorem U5(b) on `main` with `n` queries (`Privacy/MoussakaUnboundNCMain*N.lean`)

* **`anonymityNC_main_U_sharedAllN` applies to one Client answering every query with one
  statement**: the Moderator `uNCN` asks the same query `uq SL` (token `false`, swap flag `true`,
  the set `SL` of both issuers, one context) `n` times, so in each world one Client answers every
  query. Every redemption proof has the same statement and witness, hence the same prefix
  `wPrefix ‖ μ₁`: the case where the prefix-collision
  term `collNH` of `anonymityNC_main_U_sharedAll` is `1`. Here the bound has no such term; the
  reads are consistent at budgets `0`, the sets contain both issuers, and every PRF reduction has
  advantage `0`.
* **`anonymityNC_main_U_leanN` applies** to the same Moderator with the trapdoor signers of
  `Audit/Liveness.lean`, the issuance proofs `main`'s Lean prover.
* `main_sharedAll_leN` and `pr_bstarN_sim_le` are instantiated through these.

No `sorry`, no `axiom`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.MainUnboundN

open VoleMole.Spec VoleMole.Privacy VoleMole.Privacy.MoussakaUnbound VoleMole.ZK.Sim
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Audit.MainUnbound
open VoleMole.Audit.MainUnboundAll VoleMole.Audit.Live VoleMole.Spec.Moussaka

/-- **One Client, one statement, `n` times**: every query is `uq SL`; constant guess, no table
reads. -/
noncomputable def uNCN : AdversaryUNCH :=
  ⟨fun _ => 0, pkL, fun _ => Audit.uq SL, fun _ _ _ _ => True, fun _ _ _ _ => ∅⟩

theorem uNCN_cons : uNCN.ConsH 0 0 :=
  ⟨fun _ => rdUH_const True _, fun _ => rdUH_const ∅ _⟩

theorem uNCN_contains : Contains uNCN.unc.nc := fun H c => by
  refine ⟨pkL c, ?_, rfl⟩
  cases c <;> simp [AdversaryUNCH.unc, AdversaryUNC.nc, uNCN, Audit.uq, SL]

theorem redNN_uNCN (n : ℕ) (b : Bool) (z : RestN n) : prfAdvNC (redNN uNCN n b z) ≤ 0 := by
  show prfAdvNC (fun _ => True) ≤ 0
  exact prfAdvNC_true.le

/-- `anonymityNC_main_U_sharedAllN` for `uNCN`: every hypothesis holds, with `εprf = 0`. -/
example (PI : NIZK MoussakaUnbound.IssueInstance) (n : ℕ) :=
  anonymityNC_main_U_sharedAllN uNCN PI (fun c => skI (digL c)) n (fun _ => skI_correct _)
    uNCN_contains uNCN_cons (q5 := 0) (fun _ _ _ _ => le_rfl) (εprf := 0) (redNN_uNCN n)

/-- `anonymityNC_main_U_leanN` for `uNCN` with `main`'s Lean issuance prover. -/
example [HasPrg] (n : ℕ) :=
  anonymityNC_main_U_leanN uNCN (fun c => skI (digL c)) n (fun _ => skI_correct _)
    uNCN_contains uNCN_cons (q5 := 0) (fun _ _ _ _ => le_rfl) (εprf := 0) (redNN_uNCN n)

/-- The two redemptions of `uNCN` have one statement in every world: the same query, the same
token. -/
example (b : Bool) (x₀ x₁ : IssT) (H H' : MoussakaUnbound.Hist) :
    ptNC uNCN.unc.nc PIaccU (fun c => skI (digL c)) b x₀ x₁ (uNCN.next H) =
      ptNC uNCN.unc.nc PIaccU (fun c => skI (digL c)) b x₀ x₁ (uNCN.next H') := rfl

end VoleMole.Audit.MainUnboundN
