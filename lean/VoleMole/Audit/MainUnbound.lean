import VoleMole.Audit.Nonvacuous
import VoleMole.Privacy.MoussakaUnboundNCMain
import VoleMole.Audit.Liveness

/-!
# Audit of Theorem U5(a) on `main` (`Privacy/MoussakaUnboundMain*.lean`)

* **`anonymityU_main_pu` applies**: for the adversary `uM` (two queries `uq S0`, a constant guess,
  no table reads) the budgets hold at `0`, the empty `H₅` read sets are consistent, and every PRF
  reduction has advantage `0` (`prfAdv_true`), so the hypotheses hold with `εprf = 0`. The (PU)
  advantages are explicit probabilities, not hypotheses.
* **The predictors are small**: at most `3·(q₅ + 1)` candidates (`card_predU_le`), here `3`.
* **The ideal-permutation bound applies to `UCom`** (`puAdvPerm_unbound_le`), for every predictor
  tree with `q < 2¹²⁸` queries.
* **`anonymityNC_main_U` (U5(b) on `main`) applies with a non-trivial signer and sets that contain
  both issuers**: the Moderator `uNCM` has the two keys `pkL c` of `Audit/Liveness.lean` (trapdoor
  signers `skI (digL c)`) and queries the set `SL` of both (`uNCM_contains`); the budgets,
  consistency and the PRF hypothesis (`εprf = 0`, constant guess) hold.

No `sorry`, no `axiom`.
-/

open Finset

set_option synthInstance.maxSize 1024
set_option exponentiation.threshold 600

namespace VoleMole.Audit.MainUnbound

open VoleMole.Spec VoleMole.Privacy VoleMole.Privacy.MoussakaUnbound VoleMole.ZK.Sim
open VoleMole.Privacy.MainChain VoleMole.Privacy.PU VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Spec.Moussaka (ctxBytes)

/-- The colluding adversary on `main` with two queries, a constant guess and no table reads. -/
def uM : AdversaryUM :=
  ⟨fun _ => 0, fun _ => Audit.k0, fun _ _ _ => 0, fun _ _ _ => Audit.uq Audit.S0,
    fun _ _ _ _ => True, fun _ _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ => ∅⟩

theorem uM_budget : uM.Budget 0 0 :=
  ⟨fun _ _ _ _ _ _ => Audit.rdV_const _, fun _ _ _ _ _ _ => Audit.rdV_const _,
    fun _ _ _ _ _ _ => Audit.rdV_const _, fun _ _ _ _ _ _ => Audit.rdV_const _⟩

theorem uM_cons : uM.Cons := fun _ _ _ => Audit.vcons_const True

/-- A distinguisher that always accepts has PRF advantage `0`. -/
theorem prfAdv_true (ci : Spec.Bytes) : prfAdv ci (fun _ => True) = 0 := by
  unfold prfAdv; simp [pr_const]

/-- `anonymityU_main_pu` for `uM`: every hypothesis holds, with `εprf = 0`. -/
example [HasPrg] :=
  anonymityU_main_pu uM uM_budget uM_cons (q5 := 0) (fun _ _ _ _ => le_rfl)
    (fun _ _ _ _ => le_rfl) (εprf := 0) (fun _ _ _ => (prfAdv_true _).le)

/-- The predictors of `uM` output at most `3` candidates. -/
example [HasPrg] (b : Bool) (t₀ t₁ k₀ k₁ : Spec.Bytes) (k : AuxU) (c : Bool) :
    (predU uM b t₀ t₁ k₀ k₁ k c).card ≤ 3 * (0 + 1) :=
  card_predU_le uM (q5 := 0) (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
    (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl) b t₀ t₁ k₀ k₁ k c

/-- The ideal-permutation bound for `UCom`, for a predictor that outputs one candidate and makes no
query: `1/2¹²⁸`. -/
example (ci : Spec.Bytes) (r₀ : Coins 16) :=
  puAdvPerm_unbound_le (Aux := Unit) ci (fun _ _ _ => .done {r₀}) (q := 0) (c := 1)
    (fun _ _ _ => PTree.Bound.done _ _) (fun _ _ _ _ => by simp [PTree.run]) (by norm_num)

section NC

open VoleMole.Audit.Live VoleMole.Spec.Moussaka

/-- A non-colluding Moderator on `main` with the keys `pkL`, both queries in `SL`, a constant guess
and no table reads. -/
noncomputable def uNCM : AdversaryUNC :=
  ⟨fun _ => 0, pkL, fun _ => Audit.uq SL, fun _ _ => True, fun _ _ => ∅, fun _ _ => ∅⟩

theorem uNCM_budget : uNCM.Budget 0 0 :=
  ⟨fun _ _ => Audit.rdV_const _, fun _ _ => Audit.rdV_const _⟩

theorem uNCM_cons : uNCM.Cons := fun _ => Audit.vcons_const True

/-- **Every query's set contains both issuers.** -/
theorem uNCM_contains : Contains uNCM.nc := fun _ c =>
  ⟨pkL c, by cases c <;> simp [AdversaryUNC.nc, uNCM, Audit.uq, SL], rfl⟩

/-- A distinguisher that always accepts has PRF advantage `0` (without the commitments). -/
theorem prfAdvNC_true : prfAdvNC (fun _ => True) = 0 := by
  unfold prfAdvNC; simp [pr_const]

/-- `anonymityNC_main_U` for `uNCM`: every hypothesis holds, with `εprf = 0`. -/
example [HasPrg] (PI : NIZK MoussakaUnbound.IssueInstance) :=
  anonymityNC_main_U uNCM PI (fun c => skI (digL c)) (fun _ => skI_correct _) uNCM_contains
    uNCM_budget uNCM_cons (q5 := 0) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (εprf := 0)
    (fun _ _ _ => (prfAdvNC_true).le)

end NC

end VoleMole.Audit.MainUnbound
