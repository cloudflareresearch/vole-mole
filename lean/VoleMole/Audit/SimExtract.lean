import VoleMole.Audit.IdealTag
import VoleMole.Assumptions.SimLinks
import VoleMole.ROM.MoussakaUnboundSim
import VoleMole.Audit.UnboundROM

/-!
# Non-vacuity of the protocol theorems with simultaneous extraction

The simultaneous-extraction corollaries (`ROM/MoussakaOMUFSim.lean`,
`ROM/RatatouilleBalanceSim.lean`, `Assumptions/SimLinks.lean`) instantiated with the objects of
`Audit/Nonvacuous.lean` and `Audit/IdealTag.lean`: the trivial OMUF adversary `aU` with two honest
Anchors of distinct 32-byte digests, the balance adversary `balA0` with any signer and any number
of calls, the toy ideal-`Com` forger, the trivial ideal-model forger. Every hypothesis is
discharged except, for the Ratatouille OMPR corollary, the modelling hypothesis `TagIdeal`, as
for the per-proof versions. The prefix structure of the outputs' runs (`PrefixRuns`) is not a
hypothesis of these corollaries: it is proved for Moussaka's projections (`prefixRuns_map`) and
for Ratatouille's `j`-th provers (`prefixRuns_I`, `prefixRuns_S`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Audit.SimExtract

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Verifier VoleMole.Audit VoleMole.Audit.IdealTag
open VoleMole.ROM.IC.OMUF VoleMole.Assumptions.UOV VoleMole.Assumptions.UOV.Links
open VoleMole.Assumptions.IdealTag VoleMole.Assumptions.IdealTag.Rat VoleMole.ZK.Sim
open VoleMole.Spec.Ratatouille

/-- Moussaka Theorem 1 with simultaneous extraction (`omuf_le_num_sim`): its hypotheses hold. -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omuf_le_num_sim (lr := lr) (sk := sk) (qI := 1) aU_budget pkU_digest pkU_inj

/-- The same with `Adv^{ct-uf-open}` (`omuf_le_num_open_sim`). -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omuf_le_num_open_sim lr pkU sk 1 aU_budget pkU_digest pkU_inj

/-- Moussaka down to OMPR with simultaneous extraction (`omuf_le_num_ompr_sim`): its hypotheses,
the modelling one included, hold for the toy ideal forger. -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omuf_le_num_ompr_sim lr pkU sk 1 toyTrap (fun _ => ((), ())) 0 0 aU_budget pkU_digest pkU_inj
    (toyF 2) (toyF_budget 2) (by
      have := toyF_wins 2
      simp only [toyTrap] at this ⊢
      rw [this]
      exact prEvent_le_one _)

/-- Ratatouille balance with simultaneous extraction (`balance_le_lean_sim`): its hypotheses hold
for `balA0`, any signer and any number of calls. -/
example (σ : RatBalance.Signer) (N : ℕ) (lr : Bool) :=
  RatBalance.balance_le_lean_sim lr IdealTag.pk0 balA0 N σ
    (by decide) (qA := 0) (nA := 0) (eA := 0) (fun _ => trivial)
    (fun _ => isQueryBoundP_pure _ _ _) (fun _ => isQueryBoundP_pure _ _ _)

/-- The same with the UF-Tag advantage of the forger (`balance_le_ufTag_sim`). -/
example (σ : RatBalance.Signer) (N : ℕ) (lr : Bool) :=
  RatBalance.balance_le_ufTag_sim lr IdealTag.pk0 balA0 N σ
    (by decide) (qA := 0) (nA := 0) (eA := 0) (fun _ => trivial)
    (fun _ => isQueryBoundP_pure _ _ _) (fun _ => isQueryBoundP_pure _ _ _)

/-- Ratatouille balance under OMPR with simultaneous extraction (`balance_le_ompr_rate_sim`):
every hypothesis but `TagIdeal` is discharged. -/
example (σ : RatBalance.Signer) (τ : Target → Preimage) (N : ℕ) (lr : Bool) (qH : ℕ)
    (hTag : TagIdeal IdealTag.pk0.map σ
      ((RatBalance.forger lr IdealTag.pk0 RatBalance.verQL balA0 N
        (verifierIC_verifyIC CrtGen.tables)).noProbe τ) qH N a0) :=
  balance_le_ompr_rate_sim lr IdealTag.pk0 balA0 N σ τ
    (by decide) (qA := 0) (nA := 0) (eA := 0) (fun _ => trivial)
    (fun _ => isQueryBoundP_pure _ _ _) (fun _ => isQueryBoundP_pure _ _ _) qH 0 a0 a0_bound hTag

/-- Unbound Moussaka, issuance and redemption together (`moussakaUnbound_sim_joint_spec`): its
hypotheses (statement properties, separated families, prefix runs, one hash log for the two
reference runs) hold at the executable statements, for one-instance families and the trivial
prover of each relation. -/
example (lr : Bool) (ci cr cd pf : ByteArray) :=
  moussakaUnbound_sim_joint_spec (ιI' := Unit) (ιR' := Unit) (βI := Unit) (βR := Unit)
    (α := Unit) (fun _ : Unit => moussakaUnboundIssue (toBA (List.replicate 45 0)) ci lr) lr
    (fun _ => (toBA (List.replicate 45 0), ci))
    (fun _ => Unbound.moussakaUnboundIssue_stmt _ _ _)
    (fun _ => by rw [Privacy.size_toBA, List.length_replicate]) (fun _ _ _ => rfl)
    (fun _ : Unit => moussakaUnboundRedeem [] UnboundROM.nf0 ci cr cd lr) (fun _ => [])
    (fun _ => by simp) (fun _ => UnboundROM.nf0) (fun _ => ci) (fun _ => cr) (fun _ => cd)
    (fun _ => Unbound.moussakaUnboundRedeem_stmt _ _ _ _ _ _) (fun _ => UnboundROM.nf0_size)
    (fun _ _ _ => rfl) (pure (pf, ((), ()))) (fun _ => pure (pf, ((), ())))
    (pure (pf, ((), ()))) (fun _ => pure (pf, ((), ()))) {()} {()} 0
    (fun _ _ => isQueryBoundP_pure _ _ _) (fun _ _ => isQueryBoundP_pure _ _ _) 0
    (fun _ _ => trivial) trivial (fun _ _ => trivial) 0 (fun _ _ => isQueryBoundP_pure _ _ _)
    (isQueryBoundP_pure _ _ _) (fun _ _ => isQueryBoundP_pure _ _ _)
    (fun _ _ _ _ => ⟨⟨[], (List.append_nil _).symm⟩, [], (List.append_nil _).symm⟩)
    (fun _ _ _ _ => ⟨⟨[], (List.append_nil _).symm⟩, [], (List.append_nil _).symm⟩)
    (fun _ _ => rfl) (fun _ => pure ()) (fun _ _ => False) fun _ _ h => h.elim

end VoleMole.Audit.SimExtract
