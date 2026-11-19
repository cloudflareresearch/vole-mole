import VoleMole.Assumptions.RatatouillePerm
import VoleMole.Audit.IdealTag
import VoleMole.Audit.PermOMPR

/-!
# Non-vacuity of det-FDH with `Tag` a random permutation (`Assumptions/FDHPerm.lean`,
`Assumptions/RatatouillePerm.lean`)

* A toy trapdoor in which every claim is a preimage (`toyTrap`), blocks `Bool × Bool`, one message
  encoded injectively, and a permutation-model forger that makes no query and claims `Tag(())`: it
  is within every budget and wins the permutation-model det-FDH game with probability one
  (`toyFDH_wins`). So the game is winnable and the hypotheses of `advFDHPerm_le_ompr_rate` hold.
* Ratatouille's balance under OMPR with `Tag` a random permutation (`balance_le_ompr_rate_perm`,
  `balance_le_ompr_rate_sim_perm`) for the adversary `balA0` of `Audit/Nonvacuous.lean`, any signer
  and completion, the encoding `(c, x) ↦ (0, (c, x))` of the pairs into `Target × (Commitment ×
  Credits)` and the forger without queries: every hypothesis is discharged except the modelling
  hypothesis `TagIdealP`, which stays an argument. It is a statement about the concrete KP800; it
  holds, for instance, whenever the forger's strict UF-Tag advantage is `0`
  (`tagIdealP_of_eq_zero`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Audit.PermFDH

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Spec.Ratatouille VoleMole.Assumptions.UOV
open VoleMole.Assumptions.IdealTag VoleMole.Assumptions.IdealTag.Rat VoleMole.Verifier
open VoleMole.ZK.Sim VoleMole.ROM.IC.RatBalance VoleMole.Audit VoleMole.Audit.PermOMPR
open VoleMole.Assumptions.UOV.FDHPerm VoleMole.Assumptions.LazyPerm

/-! ## The toy game -/

theorem mem_sList_iff {M B Z : Type} [Fintype M] [DecidableEq B] [DecidableEq Z]
    (emb : M → B × Z) (b : B × Z) : b ∈ sList emb ↔ ∃ m, emb m = b := by
  unfold sList
  rw [Finset.mem_toList, Finset.mem_image]
  simp

instance : Nonempty (Bc embU) := ⟨⟨(true, true), by simp [mem_sList_iff, embU]⟩⟩

noncomputable instance : SampleableType (Bc embU) := SampleableType.subtype _ _

/-- The permutation-model det-FDH forger that claims `Tag(())`, with no query. -/
def toyFDH : Unit → ProbComp (OracleComp (specFP (fun _ : Unit => Bool) Unit Bool Bool Unit)
    (Unit × Unit)) :=
  fun _ => pure (pure ((), ()))

theorem toyFDH_budget : ∀ pk, ∀ a ∈ support (toyFDH pk), FPBudget 0 0 0 a := by
  intro pk a ha
  simp only [toyFDH, support_pure, Set.mem_singleton_iff] at ha
  subst ha
  exact ⟨isQueryBoundP_pure _ _ _, isQueryBoundP_pure _ _ _, isQueryBoundP_pure _ _ _⟩

/-- **The permutation-model det-FDH game is winnable**: the toy forger wins with probability
one. -/
theorem toyFDH_wins : advFDHPerm toyTrap embU toyFDH = 1 := by
  unfold advFDHPerm
  refine le_antisymm (prEvent_le_one _) ?_
  simp only [toyFDH, toyTrap, pure_bind]
  rw [prEvent_eq_one_of_forall_mem_support _ _ fun r hr => ?_]
  simp only [fpRun, fpFinal, pure_bind, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff, fwdQF] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  erw [simulateQ_spec_query] at hx
  simp only [fpImpl, rpImpl, pmImpl] at hx
  erw [StateT.run_mk, support_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  simp only [fwdS, fwdFind, List.find?_nil, Option.map_none] at hb
  erw [support_map] at hb
  obtain ⟨y, -, rfl⟩ := hb
  exact ⟨by simp, y.1, by simp [CTUFPerm.comP, fwdFind, embU], trivial⟩

/-- **det-FDH with `Tag` a random permutation, down to OMPR**: the hypotheses hold for the toy
forger. -/
example := advFDHPerm_le_ompr_rate embU_inj toyTrap toyFDH toyFDH_budget

/-! ## Ratatouille -/

/-- The encoding of the pairs `(c, x)` into the blocks `Target × (Commitment × Credits)`. -/
def embR : Commitment × Credits → Target × (Commitment × Credits) := fun m => (default, m)

theorem embR_inj : Function.Injective embR := fun _ _ h => (Prod.ext_iff.1 h).2

/-- A target other than the default one. -/
def t1 : Target := Vector.replicate 45 1

theorem t1_ne : t1 ≠ default := by decide

instance : Nonempty (Bc embR) :=
  ⟨⟨(t1, default), by
    rw [mem_sList_iff]; rintro ⟨m, hm⟩; exact t1_ne (Prod.ext_iff.1 hm).1.symm⟩⟩

noncomputable instance : SampleableType (Bc embR) := SampleableType.subtype _ _

/-- A permutation-model forger that makes no query and outputs a failed signature. -/
def aP0 : FDHPermAdv (fun _ : Unit => Bool) (Commitment × Credits) :=
  fun _ => pure (pure (default, none))

theorem aP0_budget : ∀ pk, ∀ a ∈ support (aP0 pk), FPBudget 0 0 0 a := by
  intro pk a ha
  simp only [aP0, support_pure, Set.mem_singleton_iff] at ha
  subst ha
  exact ⟨isQueryBoundP_pure _ _ _, isQueryBoundP_pure _ _ _, isQueryBoundP_pure _ _ _⟩

/-- The modelling hypothesis holds whenever the forger's strict UF-Tag advantage is `0`. -/
theorem tagIdealP_of_eq_zero {DR : Type} [DecidableEq DR] {AR : DR → Type}
    [∀ d, SampleableType (AR d)] {Z : Type} [DecidableEq Z] [SampleableType Z] [Fintype Z]
    (pk : PublicKey) (σ : IC.RatBalance.Signer) (B : IC.RatBalance.TagForger)
    (emb : Commitment × Credits → Target × Z) (A' : FDHPermAdv AR Z)
    (h : ufTagStrictAdv pk σ B = 0) : TagIdealP pk σ B emb A' := by
  unfold TagIdealP; rw [h]; exact bot_le

/-- **Theorem 1 of Ratatouille under OMPR, `Tag` a random permutation**: for `balA0`, any signer
and completion, every hypothesis but the modelling hypothesis `TagIdealP` is discharged. -/
example (σ : IC.RatBalance.Signer) (τ : Target → Preimage) (N : ℕ) (lr : Bool)
    (hTag : TagIdealP IdealTag.pk0.map σ
      ((forger lr IdealTag.pk0 verQL balA0 N (verifierIC_verifyIC CrtGen.tables)).noProbe τ)
      embR aP0) :=
  balance_le_ompr_rate_perm lr IdealTag.pk0 balA0 N σ τ
    (by decide) (qA := 0) (nA := 0) (eA := 0) (fun _ => trivial)
    (fun _ => isQueryBoundP_pure _ _ _) (fun _ => isQueryBoundP_pure _ _ _) embR_inj aP0 aP0_budget
    hTag

/-- The same with simultaneous extraction (`balance_le_ompr_rate_sim_perm`). -/
example (σ : IC.RatBalance.Signer) (τ : Target → Preimage) (N : ℕ) (lr : Bool)
    (hTag : TagIdealP IdealTag.pk0.map σ
      ((forger lr IdealTag.pk0 verQL balA0 N (verifierIC_verifyIC CrtGen.tables)).noProbe τ)
      embR aP0) :=
  balance_le_ompr_rate_sim_perm lr IdealTag.pk0 balA0 N σ τ
    (by decide) (qA := 0) (nA := 0) (eA := 0) (fun _ => trivial)
    (fun _ => isQueryBoundP_pure _ _ _) (fun _ => isQueryBoundP_pure _ _ _) embR_inj aP0 aP0_budget
    hTag

end VoleMole.Audit.PermFDH
