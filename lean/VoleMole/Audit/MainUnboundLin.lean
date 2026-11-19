import VoleMole.Audit.MainUnboundN
import VoleMole.Privacy.MoussakaUnboundNCMainLin
import VoleMole.Privacy.MoussakaUnboundMainN

/-!
# Audit of the linear joint hop and U5(b) on `main` with `n` queries (`ZK/MainSharedLin.lean`)

* **`anonymityNC_main_U_sharedAllLin` and `anonymityNC_main_U_leanLin` apply** to the Moderator
  `uNCN` of `Audit/MainUnboundN.lean` (one Client answers every query with one statement), with
  the trapdoor signers of `Audit/Liveness.lean`, consistent reads at budgets `0`, Anchor Sets with
  both issuers and PRF reductions of advantage `0`.
* **`anonymityU_main_sharedAllN` (U5(a), `n` adaptive queries) applies to one Client answering
  every query with one statement**: the adversary `uAN` asks the query `uq S0` `n` times (a
  constant guess, no table reads), the case where the two-query theorem's prefix-collision term
  `collUH` is `1`. The reads are consistent at budgets `0` and every PRF reduction has advantage
  `0`; the (PU) advantages are explicit probabilities of predictors with at most
  `(n + 2)·(312(n + 2) + 1)` candidates.
* `main_sharedAll_leLin`, `hopN_iub`, `ctx_hopN_iub` and `slot_zk_main_iub` are instantiated
  through these, at the real games of `main`'s issuance and redemption layouts: their hypotheses
  (`NValid`, `RdN`, the bad event inside the event) are met.

No `sorry`, no `axiom`.
-/

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.MainUnboundLin

open VoleMole.Spec VoleMole.Privacy VoleMole.Privacy.MoussakaUnbound VoleMole.ZK.Sim
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Audit.MainUnbound
open VoleMole.Audit.MainUnboundN VoleMole.Audit.MainUnboundAll VoleMole.Audit.Live VoleMole.Spec.Moussaka
open VoleMole.Privacy.PU

/-- `anonymityNC_main_U_sharedAllLin` for `uNCN`: every hypothesis holds, with `εprf = 0`. -/
example (PI : NIZK MoussakaUnbound.IssueInstance) (n : ℕ) :=
  anonymityNC_main_U_sharedAllLin uNCN PI (fun c => skI (digL c)) n (fun _ => skI_correct _)
    uNCN_contains uNCN_cons (q5 := 0) (fun _ _ _ _ => le_rfl) (εprf := 0) (redNN_uNCN n)

/-- `anonymityNC_main_U_leanLin` for `uNCN` with `main`'s Lean issuance prover. -/
example [HasPrg] (n : ℕ) :=
  anonymityNC_main_U_leanLin uNCN (fun c => skI (digL c)) n (fun _ => skI_correct _)
    uNCN_contains uNCN_cons (q5 := 0) (fun _ _ _ _ => le_rfl) (εprf := 0) (redNN_uNCN n)

/-! ## U5(a) with `n` adaptive queries -/

/-- **One Client, one statement, `n` times** (colluding): every query is `uq S0`; constant guess,
no table reads. -/
def uAN : AdversaryUAH :=
  ⟨fun _ => 0, fun _ => Audit.k0, fun _ _ _ => 0, fun _ _ _ => Audit.uq Audit.S0,
    fun _ _ _ _ _ _ => True, fun _ _ _ _ _ _ => ∅⟩

theorem uAN_cons : uAN.ConsH 0 0 :=
  ⟨fun _ _ _ => rdUH_const True _, fun _ _ _ => rdUH_const ∅ _⟩

/-- `anonymityU_main_sharedAllN` for `uAN`: every hypothesis holds, with `εprf = 0`. -/
example (n : ℕ) :=
  anonymityU_main_sharedAllN uAN n uAN_cons (εprf := 0) (fun _ _ => (prfAdv_true _).le)

/-- The predictors of `uAN` output at most `(n + 2)·(312(n + 2) + 1)` candidates. -/
example (n : ℕ) (b : Bool) (t₀ t₁ : Spec.Bytes) (O : Bool → Coins ctxBytes → Spec.Bytes)
    (z : RestAN n) : (candAN uAN n b t₀ t₁ O z).card ≤ (n + 2) * (0 + (n + 2) * 312 + 1) :=
  card_candAN_le uAN n (q5 := 0) (fun _ _ _ _ _ _ => le_rfl) b t₀ t₁ O z

/-- Every query of `uAN` is the same, so in each world one Client answers all of them with one
statement. -/
example (q₀ q₁ : Spec.Bytes) (H H' : MoussakaUnbound.Hist) : uAN.next q₀ q₁ H = uAN.next q₀ q₁ H' :=
  rfl

end VoleMole.Audit.MainUnboundLin
