import VoleMole.Audit.MainShared
import VoleMole.Privacy.RatatouilleMainPU
import VoleMole.Privacy.RatatouilleMainSharedPU

/-!
# Audit of Ratatouille's (PU) reduction on `main` (`lean/docs/zk.md` §4.2, §4.3)

* **`unlinkability_main_pu` applies**: for the Issuer `rM` of `Audit/Nonvacuous.lean` (constant
  guess, empty `H₅` read sets) every hypothesis holds, with `q₅ = 0` and `εhide = 0`. The six
  `puAdv` terms are terms of the bound, not hypotheses.
* **`unlinkability_main_shared` applies**: for `rS` (constant guess, no reads) `AdversarySR.Cons`
  holds at `0, 0` and hiding with `εhide = 0`. `rS` has `T_init = 1`, so the four proofs are made.
  `rSR k₀` reads the shared `H₅` table at `k₀` and satisfies `Cons` (`rSR_cons`): consistency does
  not force a table-independent guess.
* **The predictors name few candidates**: `card_predIS_le`, `card_predCS_le` at `q₅ = 0`.
* **(PU) for the change token's commitment is computational**: the exhaustive predictor against
  `comCh` has advantage `1` (`PU.puAdv_bruteForce`), as for `comI`.

No `sorry`, no `axiom`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.MainRata

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Privacy.PU VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille

/-- `unlinkability_main_pu` for the Issuer with a constant guess. -/
example [HasPrg] (b₁ b₂ b₁' b₂' : Bool) :=
  unlinkability_main_pu Audit.rM Audit.rM_budget Audit.rM_cons (q5 := 0) (fun _ _ => le_rfl)
    (fun _ _ => le_rfl) (εhide := 0) (fun _ _ _ _ => (Audit.hidingAdvR_true _).le) b₁ b₂ b₁' b₂'

/-- The malicious Issuer on `main` with shared tables, `T_init = 1`, a constant guess and no table
reads. -/
def rS : AdversarySR :=
  ⟨default, default, 1, fun _ _ => default, fun _ => 0, fun _ _ => default, fun _ _ => 0,
    fun _ _ => True, fun _ _ => ∅⟩

lemma rdT_const {X : Sort*} (x : X) :
    RdT (p₁ := pIr) (p₂ := pIr) (p₃ := pSr) (p₄ := pSr) (fun _ => x) (fun _ => ∅) 0 0 :=
  ⟨fun _ _ _ => rfl, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩⟩

theorem rS_cons : rS.Cons 0 0 := ⟨fun _ => rdT_const True, fun _ => rdT_const ∅⟩

/-- `unlinkability_main_shared` for `rS`. -/
example [HasPrg] (b₁ b₂ b₁' b₂' : Bool) :=
  unlinkability_main_shared rS rS_cons (εhide := 0)
    (fun _ _ _ => (Audit.hidingAdvR_true _).le) b₁ b₂ b₁' b₂'

/-- The predictors of `rS` name at most `3747` and `1249` candidates. -/
example [HasPrg] (b₁ b₂ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ cf₃ : Credits → Commitment) (a : AuxSR) (c : Bool) :
    (predIS rS b₁ b₂ n t cf₂ cf₃ a c).card ≤ 3 * (0 + 1249) ∧
      (predCS rS b₁ b₂ n t cf₂ cf₃ a).card ≤ 0 + 1249 :=
  ⟨card_predIS_le rS b₁ b₂ n t cf₂ cf₃ a (q5 := 0) (fun _ _ => le_rfl) c,
    card_predCS_le rS b₁ b₂ n t cf₂ cf₃ a (q5 := 0) (fun _ _ => le_rfl)⟩

/-- An Issuer whose guess reads the shared `H₅` table at the key `k₀`. -/
def rSR (k₀ : ZK.Sim.Bytes 37) : AdversarySR :=
  ⟨default, default, 1, fun _ _ => default, fun _ => 0, fun _ _ => default, fun _ _ => 0,
    fun _ v => v.1.1 k₀ = fun _ => 0, fun _ _ => {k₀}⟩

/-- **`Cons` holds for a guess that reads `H₅`**: no slice or cipher reads, `H₅` at `{k₀}`. -/
theorem rSR_cons (k₀ : ZK.Sim.Bytes 37) : (rSR k₀).Cons 0 0 :=
  ⟨fun _ => ⟨fun t G5 h => by
      show (G5 k₀ = fun _ => 0) = (t.1.1 k₀ = fun _ => 0)
      rw [← h k₀ (mem_singleton_self _)],
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩⟩,
   fun _ => ⟨fun _ _ _ => rfl,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩⟩⟩

/-- `unlinkability_main_shared0` for the `H₅`-reading Issuer, for any bound `εhide` on its hiding
reductions (the hypothesis is satisfiable for an adversary that reads the shared table). -/
example [HasPrg] (k₀ : ZK.Sim.Bytes 37) (εhide : ℝ)
    (hh : ∀ b₁ b₂ a, hidingAdv (rSR k₀).ctx (redSR (rSR k₀) b₁ b₂ a) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :=
  unlinkability_main_shared (rSR k₀) (rSR_cons k₀) hh b₁ b₂ b₁' b₂'

/-- **(PU) for the change token's commitment is computational**: the exhaustive predictor has
advantage `1`. -/
example [HasPrg] (A : AdversaryRM) (b₁ : Bool) :
    puAdv (comCh A b₁) (bruteForce (Aux := Unit) (comCh A b₁)) = 1 :=
  puAdv_bruteForce _

end VoleMole.Audit.MainRata
