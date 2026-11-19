import VoleMole.Audit.Nonvacuous
import VoleMole.Assumptions.RatatouilleOMPR

/-!
# Non-vacuity of the reductions to OMPR (`Assumptions/IdealTag.lean`, `RatatouilleOMPR.lean`)

* Theorem 1 (a) then (c) (`advFDH_le_ompr`) at the Issuer's trapdoor `ratTrap pk σ` (any key, any
  signer) for an adversary without queries: the query-bound hypothesis is discharged.
* Theorem 1 of Ratatouille under OMPR (`balance_le_ompr`, `balance_le_ompr_rate`) for the
  adversary `balA0` of `Audit/Nonvacuous.lean`, any signer and completion, and the trivial
  ideal-model forger: every hypothesis is discharged except the modelling hypothesis `TagIdeal`,
  which stays an argument. It is a statement about the concrete KP800, not provable; it holds,
  for instance, whenever the forger's strict UF-Tag advantage is `0` (`tagIdeal_of_eq_zero`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Audit.IdealTag

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Spec.Ratatouille VoleMole.Assumptions.UOV
open VoleMole.Assumptions.IdealTag VoleMole.Assumptions.IdealTag.Rat VoleMole.Verifier
open VoleMole.ZK.Sim VoleMole.ROM.IC.RatBalance VoleMole.Audit

/-- The key of the balance audit (a 32-byte digest). -/
def pk0 : UovPk := ⟨ByteArray.mk (Array.replicate 32 0), ByteArray.empty⟩

/-- An ideal-model forger that makes no query and outputs a failed signature. -/
def a0 : FDHAdv (fun _ : Unit => Bool) := fun _ => pure (pure (default, none))

theorem a0_bound : ∀ pk, ∀ a ∈ support (a0 pk), IsQueryBoundP a isHS 0 := by
  intro pk a ha
  simp only [a0, support_pure, Set.mem_singleton_iff] at ha
  subst ha
  exact isQueryBoundP_pure _ _ _

/-- **det-FDH ≤ OMPR at the Issuer's trapdoor**: the hypotheses hold. -/
example (pk : PublicKey) (σ : IC.RatBalance.Signer) (qH qS : ℕ) :=
  advFDH_le_ompr_rate (ratTrap pk σ) qH qS 0 a0 a0_bound

/-- The modelling hypothesis holds whenever the forger's strict UF-Tag advantage is `0`. -/
theorem tagIdeal_of_eq_zero {DR : Type} [DecidableEq DR] {AR : DR → Type}
    [∀ d, SampleableType (AR d)] (pk : PublicKey) (σ : IC.RatBalance.Signer)
    (B : IC.RatBalance.TagForger) (qH qS : ℕ) (A' : FDHAdv AR) (h : ufTagStrictAdv pk σ B = 0) :
    TagIdeal pk σ B qH qS A' := by
  unfold TagIdeal; rw [h]; exact bot_le

/-- **Theorem 1 of Ratatouille under OMPR**: for `balA0`, any signer and completion, every hypothesis
but the modelling hypothesis `TagIdeal` is discharged. -/
example (σ : IC.RatBalance.Signer) (τ : Target → Preimage) (N : ℕ) (lr : Bool) (qH : ℕ)
    (hTag : TagIdeal pk0.map σ
      ((forger lr pk0 verQL balA0 N (verifierIC_verifyIC CrtGen.tables)).noProbe τ) qH N a0) :=
  balance_le_ompr_rate lr pk0 balA0 N σ τ
    (by decide) (qA := 0) (nA := 0) (eA := 0) (fun _ => trivial)
    (fun _ => isQueryBoundP_pure _ _ _) (fun _ => isQueryBoundP_pure _ _ _) qH 0 a0 a0_bound hTag

end VoleMole.Audit.IdealTag
