import VoleMole.Assumptions.PermLinks
import VoleMole.Audit.UnboundOMUF
import VoleMole.Audit.SimExtract

/-!
# Non-vacuity of the reductions to OMPR with `Com` a random permutation

`Assumptions/CTUFPerm.lean`, `Assumptions/PermLinks.lean`. A toy trapdoor in which every claim is
a preimage (`toyTrap` of `Audit/Nonvacuous.lean`), blocks `Bool × Bool`, one opening encoded
injectively, and a permutation-model forger that makes no query and claims `Com(())`: it is within
every budget and wins the permutation-model game with probability one (`toyFP_wins`). So the game
is winnable, the hypotheses of T4 in the permutation model (`advCTUFPermAt_le_ompr`) hold, and
the modelling hypothesis `hmodelP` of the Moussaka and unbound Moussaka corollaries
(`omuf_le_num_ompr_perm`, `omufU_le_num_ompr_perm`) holds for it.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Audit.PermOMPR

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Audit VoleMole.Assumptions.UOV
open VoleMole.Assumptions.UOV.Links VoleMole.Assumptions.UOV.CTUFPerm
open VoleMole.Assumptions.LazyPerm

/-- The opening's encoding into the blocks `Bool × Bool`. -/
def embU : Unit → Bool × Bool := fun _ => (false, false)

theorem embU_inj : Function.Injective embU := fun _ _ _ => rfl

/-- The permutation-model forger that claims `Com(())` under key `0`, with no query and no
opening. -/
def toyFP (K : ℕ) [NeZero K] :
    ProbComp (OracleComp (specCP (fun _ : Unit => Bool) K Bool Bool Unit) (CTOut K Unit Unit)) :=
  pure (pure (some (0, (), ()), []))

theorem toyFP_budget (K : ℕ) [NeZero K] : ∀ f ∈ support (toyFP K), CPBudget 0 0 0 f := by
  intro f hf
  simp only [toyFP, support_pure, Set.mem_singleton_iff] at hf
  subst hf
  exact ⟨isQueryBoundP_pure _ _ _, isQueryBoundP_pure _ _ _, isQueryBoundP_pure _ _ _, by simp⟩

/-- **The permutation-model game is winnable**: the toy forger wins with probability one. -/
theorem toyFP_wins (K : ℕ) [NeZero K] :
    advCTUFPermAt (fun _ _ _ => True) (fun _ => ()) embU (toyFP K) = 1 := by
  unfold advCTUFPermAt
  refine le_antisymm (prEvent_le_one _) ?_
  simp only [toyFP, pure_bind]
  rw [prEvent_eq_one_of_forall_mem_support _ _ fun r hr => ?_]
  simp only [cpRun, cpFinal, pure_bind, Option.map_some, Option.toList_some, List.append_nil,
    List.mapM_cons, List.mapM_nil, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff, fwdQ] at hr
  obtain ⟨x, ⟨y, hy, rfl⟩, rfl⟩ := hr
  erw [simulateQ_spec_query] at hy
  simp only [cpImpl, rpImpl, pmImpl] at hy
  erw [StateT.run_mk, support_map] at hy
  obtain ⟨b, hb, rfl⟩ := hy
  simp only [fwdS, fwdFind, List.find?_nil, Option.map_none] at hb
  erw [support_map] at hb
  obtain ⟨y, -, rfl⟩ := hb
  exact ⟨0, (), (), y.1, rfl, by simp [comP, fwdFind, embU], trivial, by simp, by simp⟩

/-- T4 in the permutation model applies to the toy forger. -/
example := advCTUFPermAt_le_ompr toyTrap (fun _ : Fin 1 => ((), ())) embU_inj (toyFP 1)
  (toyFP_budget 1)

/-- The toy forger meets the permutation-model modelling hypothesis against any advantage. -/
theorem toy_hmodelP (a : ℝ≥0∞) (ha : a ≤ 1) :
    a ≤ advCTUFPermAt (fun k => toyTrap.IsPre ((fun _ : Fin 2 => ((), ())) k).1)
      (signers toyTrap.D fun k => ((fun _ : Fin 2 => ((), ())) k).2) embU (toyFP 2) := by
  have := toyFP_wins 2
  simp only [toyTrap] at this ⊢
  rw [this]
  exact ha

/-- **Moussaka down to OMPR, `Com` a random permutation** (`omuf_le_num_ompr_perm`): every
hypothesis, the modelling one included, holds for the toy forger. -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omuf_le_num_ompr_perm lr pkU sk 1 toyTrap (fun _ => ((), ())) aU_budget pkU_digest pkU_inj
    embU_inj (toyFP 2) (toyFP_budget 2) (toy_hmodelP _ (prEvent_le_one _))

/-- **Unbound Moussaka down to OMPR, `Com ∪ UCom` a random permutation**
(`omufU_le_num_ompr_perm`). -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omufU_le_num_ompr_perm lr pkU sk 2 toyTrap (fun _ => ((), ())) UnboundOMUF.aUU_budget pkU_digest pkU_inj
    embU_inj (toyFP 2) (toyFP_budget 2) (toy_hmodelP _ (prEvent_le_one _))

end VoleMole.Audit.PermOMPR
