import VoleMole.Assumptions.PermSimLinks
import VoleMole.Assumptions.RatatouillePermSim
import VoleMole.Assumptions.UnboundPermSimLinks
import VoleMole.Audit.UnboundOMUF
import VoleMole.Audit.PermOMPR
import VoleMole.Audit.PermFDH
import VoleMole.Audit.SimExtract

/-!
# Non-vacuity of Moussaka with AES and `Com` both random permutations
(`Assumptions/PermSimLinks.lean`)

`omuf_le_num_ompr_simP` (AES as random permutations with inverse queries, `Com` a random
permutation with inverse queries in the standalone CT-UF^open game) for the permutation-model
adversary `aUP` of `Audit/SimExtract.lean` (an inverse cipher query first), the toy trapdoor and
the toy permutation-model forger of `Audit/PermOMPR.lean`: every hypothesis, the modelling
hypothesis `hmodelP` for the forger `ctufForgerP` included, holds (`toy_hmodelP`).

Ratatouille with AES as random permutations (`Assumptions/RatatouillePermSim.lean`):
`balance_le_ompr_rate_simP` (`Tag` a random function) and `balance_le_ompr_rate_sim_permP` (`Tag`
a random permutation) for the permutation-model adversary `balA0P` of `Audit/SimExtract.lean`
(inverse cipher queries), any signer, completion and number of calls, and the trivial forgers
`a0`, `aP0`: every hypothesis is discharged except the modelling hypothesis (`TagIdeal`,
`TagIdealP` for `(forgerP …).noProbe τ`), which stays an argument, as in `Audit/IdealTag.lean`
and `Audit/PermFDH.lean`.

Unbound Moussaka with AES and `Com ∪ UCom` random permutations
(`Assumptions/UnboundPermSimLinks.lean`): `omufU_le_num_simP` and `omufU_le_num_ompr_simP` for the
permutation-model adversary `aUUP` (an inverse cipher query, then `aUU`'s bound and unbound Issue
queries and redemption, `Audit/UnboundOMUF.lean`): every hypothesis, the modelling hypothesis
`hmodelP` for `ctufForgerUP` included, holds.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Audit.PermSim

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Audit VoleMole.Assumptions.UOV
open VoleMole.Assumptions.UOV.Links VoleMole.Audit.PermOMPR VoleMole.Audit.SimExtract
open VoleMole.Assumptions.IdealTag VoleMole.Assumptions.IdealTag.Rat VoleMole.Audit.PermFDH
open VoleMole.Verifier VoleMole.ZK.Sim VoleMole.Spec.Ratatouille

/-- **Moussaka down to OMPR, AES and `Com` random permutations** (`omuf_le_num_ompr_simP`): every
hypothesis holds for `aUP` and the toy forger. -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omuf_le_num_ompr_simP lr pkU 1 aUP sk toyTrap (fun _ => ((), ())) aUP_budget pkU_digest pkU_inj
    embU_inj (toyFP 2) (toyFP_budget 2) (toy_hmodelP _ (prEvent_le_one _))

/-- **Ratatouille under OMPR, AES as random permutations, `Tag` a random function**
(`balance_le_ompr_rate_simP`): for `balA0P`, every hypothesis but `TagIdeal` is discharged. -/
example (σ : IC.RatBalance.Signer) (τ : Target → Preimage) (N : ℕ) (lr : Bool) (qH : ℕ)
    (hTag : TagIdeal IdealTag.pk0.map σ
      ((IC.RatBalance.forgerP lr IdealTag.pk0 IC.RatBalance.verQL balA0P N
        (verifierIC_verifyIC CrtGen.tables)).noProbe τ) qH N IdealTag.a0) :=
  balance_le_ompr_rate_simP lr IdealTag.pk0 balA0P N σ τ (by decide) balA0P_k balA0P_h balA0P_e
    qH 0 IdealTag.a0 IdealTag.a0_bound hTag

/-- **Ratatouille under OMPR, AES and `Tag` random permutations**
(`balance_le_ompr_rate_sim_permP`): for `balA0P`, every hypothesis but `TagIdealP` is
discharged. -/
example (σ : IC.RatBalance.Signer) (τ : Target → Preimage) (N : ℕ) (lr : Bool)
    (hTag : TagIdealP IdealTag.pk0.map σ
      ((IC.RatBalance.forgerP lr IdealTag.pk0 IC.RatBalance.verQL balA0P N
        (verifierIC_verifyIC CrtGen.tables)).noProbe τ) embR aP0) :=
  balance_le_ompr_rate_sim_permP lr IdealTag.pk0 balA0P N σ τ (by decide) balA0P_k balA0P_h
    balA0P_e embR_inj aP0 aP0_budget hTag

/-- An OMUF-U adversary of the permutation model: one inverse cipher query, then `aUU`'s moves (a
bound Issue query, an unbound one, one redemption). -/
def aUUP : ROM.IC.OMUFU.AdversaryP 2 1 where
  σ := Bool
  init := (fun _ => false) <$> invU
  query b := pure (true, if b then .inr ⟨0, ByteArray.empty, ByteArray.empty⟩
    else .inl ⟨0, ByteArray.empty, ByteArray.empty⟩)
  absorb b _ := b
  final _ := pure fun _ => ⟨[], ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩

theorem aUUP_budget : aUUP.Budget 0 1 0 :=
  ⟨isKindQueryBoundP_map _ invU_k, (isQueryBoundP_map_iff _ _ _).2 invU_e,
    (isQueryBoundP_map_iff _ _ _).2 invU_h, fun _ => trivial, fun _ => trivial,
    fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial⟩

/-- **Unbound Moussaka Theorem U1, AES as random permutations** (`omufU_le_num_simP`): its
hypotheses hold for `aUUP`. -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  ROM.IC.OMUFU.omufU_le_num_simP (lr := lr) (pk := pkU) (sk := sk) (qI := 2) aUUP_budget
    pkU_digest pkU_inj

/-- **Unbound Moussaka down to OMPR, AES and `Com ∪ UCom` random permutations**
(`omufU_le_num_ompr_simP`): every hypothesis, the modelling one included, holds for `aUUP` and
the toy forger. -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omufU_le_num_ompr_simP lr pkU 2 aUUP sk toyTrap (fun _ => ((), ())) aUUP_budget pkU_digest
    pkU_inj embU_inj (toyFP 2) (toyFP_budget 2) (toy_hmodelP _ (prEvent_le_one _))

end VoleMole.Audit.PermSim
