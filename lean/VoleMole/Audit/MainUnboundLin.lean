import VoleMole.Audit.MainUnboundN
import VoleMole.Privacy.MoussakaUnboundNCMainLin

/-!
# Audit of the linear joint hop and U5(b) on `main` with `n` queries (`ZK/MainSharedLin.lean`)

* **`anonymityNC_main_U_sharedAllLin` and `anonymityNC_main_U_leanLin` apply** to the Moderator
  `uNCN` of `Audit/MainUnboundN.lean` (one Client answers every query with one statement), with
  the trapdoor signers of `Audit/Liveness.lean`, consistent reads at budgets `0`, Anchor Sets with
  both issuers and PRF reductions of advantage `0`.
* `main_sharedAll_leLin`, `hopN_iub`, `ctx_hopN_iub` and `slot_zk_main_iub` are instantiated
  through these, at the real game of `main`'s redemption layout: their hypotheses (`NValid`,
  `RdN`, the bad event inside the event) are met.

No `sorry`, no `axiom`.
-/

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.MainUnboundLin

open VoleMole.Spec VoleMole.Privacy VoleMole.Privacy.MoussakaUnbound VoleMole.ZK.Sim
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Audit.MainUnbound
open VoleMole.Audit.MainUnboundN VoleMole.Audit.MainUnboundAll VoleMole.Audit.Live VoleMole.Spec.Moussaka

/-- `anonymityNC_main_U_sharedAllLin` for `uNCN`: every hypothesis holds, with `εprf = 0`. -/
example (PI : NIZK MoussakaUnbound.IssueInstance) (n : ℕ) :=
  anonymityNC_main_U_sharedAllLin uNCN PI (fun c => skI (digL c)) n (fun _ => skI_correct _)
    uNCN_contains uNCN_cons (q5 := 0) (fun _ _ _ _ => le_rfl) (εprf := 0) (redNN_uNCN n)

/-- `anonymityNC_main_U_leanLin` for `uNCN` with `main`'s Lean issuance prover. -/
example [HasPrg] (n : ℕ) :=
  anonymityNC_main_U_leanLin uNCN (fun c => skI (digL c)) n (fun _ => skI_correct _)
    uNCN_contains uNCN_cons (q5 := 0) (fun _ _ _ _ => le_rfl) (εprf := 0) (redNN_uNCN n)

end VoleMole.Audit.MainUnboundLin
