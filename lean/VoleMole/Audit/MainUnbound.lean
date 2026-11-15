import VoleMole.Audit.Nonvacuous
import VoleMole.Privacy.MoussakaUnboundMainPU

/-!
# Audit of Theorem U5(a) on `main` (`Privacy/MoussakaUnboundMain*.lean`)

* **`anonymityU_main_pu` applies**: for the adversary `uM` (two queries `uq S0`, a constant guess,
  no table reads) the budgets hold at `0`, the empty `H₅` read sets are consistent, and every PRF
  reduction has advantage `0` (`prfAdv_true`), so the hypotheses hold with `εprf = 0`. The (PU)
  advantages are explicit probabilities, not hypotheses.
* **The predictors are small**: at most `3·(q₅ + 1)` candidates (`card_predU_le`), here `3`.
* **The ideal-permutation bound applies to `UCom`** (`puAdvPerm_unbound_le`), for every predictor
  tree with `q < 2¹²⁸` queries.

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

end VoleMole.Audit.MainUnbound
