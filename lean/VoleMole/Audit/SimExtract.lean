import VoleMole.Audit.IdealTag
import VoleMole.Assumptions.SimLinks
import VoleMole.ROM.MoussakaUnboundSim
import VoleMole.ROM.MoussakaUnboundSimPerm
import VoleMole.ROM.MoussakaOMUFSimPerm
import VoleMole.ROM.RatatouilleBalanceSimPerm
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
for Ratatouille's `j`-th provers (`prefixRuns_I`, `prefixRuns_S`). The protocol corollaries carry
the joint bound (each query of the run charged once for both relations, `ROM/SimJoint.lean`);
their separation hypothesis is discharged inside (`decOf_sep`, the relations' DSTs). The unbound
Moussaka joint bound (`moussakaUnbound_sim_joint_spec`) is instantiated at the executable
statements with one-instance families and trivial provers.

The permutation-model joint bounds (`moussaka_sim_joint_specP`, `ratatouille_sim_joint_specP`,
`moussakaUnbound_sim_joint_specP`, `ROM/SimPermJointSpec.lean`) are instantiated at the
executable statements with one-instance families and a prover `invP` that makes one **inverse**
cipher query (one cipher query, no hash query): the joint normalization, the prefix runs and the
one hash log are discharged for it. Moussaka Theorem 1 in the permutation model
(`omuf_le_num_simP`) is instantiated with `aUP`, `aU` with an inverse cipher query first;
Ratatouille balance in the permutation model (`balance_le_lean_simP`) with `balA0P`, `balA0`
with an inverse cipher query before each request.

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

/-! ## The permutation model -/

/-- A prover of the permutation model making one inverse cipher query. -/
def invP (pf : ByteArray) : OracleComp specP (ByteArray × (Unit × Unit)) :=
  liftM (specP.query (.inr (false, (default, default)))) >>= fun _ => pure (pf, ((), ()))

lemma invP_e (pf : ByteArray) : IsQueryBoundP (invP pf) (fun t => t.isRight = true) 1 := by
  rw [invP, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr Nat.one_pos, fun _ => isQueryBoundP_pure _ _ _⟩

lemma invP_k (pf : ByteArray) : IsKindQueryBoundP (invP pf) 0 := by
  rw [invP, IsKindQueryBoundP, isQueryBound_query_bind_iff]
  exact ⟨trivial, fun _ => trivial⟩

lemma invP_h (pf : ByteArray) : IsQueryBoundP (invP pf) (fun t => t.isLeft = true) 0 := by
  rw [invP, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp), fun _ => isQueryBoundP_pure _ _ _⟩

/-- Moussaka issuance and redemption together in the permutation model
(`moussaka_sim_joint_specP`): its hypotheses hold at the executable statements for one-instance
families and the prover `invP` (an inverse cipher query) of each relation. -/
example (lr : Bool) (pf : ByteArray) :=
  moussaka_sim_joint_specP (ιI' := Unit) (ιR' := Unit) (α := Unit)
    (fun _ : Unit => (toBA (List.replicate 45 0), toBA (List.replicate 16 0)))
    (fun _ => by rw [Privacy.size_toBA, List.length_replicate])
    (fun _ => by rw [Privacy.size_toBA, List.length_replicate]) lr (fun _ _ _ => rfl)
    (fun _ : Unit => []) (fun _ => by simp) (fun _ => UnboundROM.nf0)
    (fun _ => toBA (List.replicate 16 0)) (fun _ => toBA (List.replicate 16 0))
    (fun _ => ByteArray.empty) (fun _ => UnboundROM.nf0_size)
    (fun _ => by rw [Privacy.size_toBA, List.length_replicate])
    (fun _ => by rw [Privacy.size_toBA, List.length_replicate]) (fun _ _ _ => rfl)
    (invP pf) (fun _ => invP pf) (invP pf) (fun _ => invP pf) {()} {()} 1
    (fun _ _ => invP_e pf) (fun _ _ => invP_e pf) 0 (fun _ _ => invP_k pf) (invP_k pf)
    (fun _ _ => invP_k pf) 0 (fun _ _ => invP_h pf) (invP_h pf) (fun _ _ => invP_h pf)
    (fun _ _ _ _ => ⟨⟨[], (List.append_nil _).symm⟩, [], (List.append_nil _).symm⟩)
    (fun _ _ _ _ => ⟨⟨[], (List.append_nil _).symm⟩, [], (List.append_nil _).symm⟩)
    (fun _ _ => rfl) (fun _ => pure ()) (fun _ _ => False) fun _ _ h => h.elim

/-- Ratatouille issuance and spend together in the permutation model
(`ratatouille_sim_joint_specP`): its hypotheses hold likewise. -/
example (lr : Bool) (pf : ByteArray) :=
  ratatouille_sim_joint_specP (ιI' := Unit) (ιR' := Unit) (α := Unit)
    (fun _ : Unit => (ByteArray.empty, 0, ByteArray.empty)) (fun _ => by norm_num) lr
    (fun _ _ _ => rfl) (fun _ : Unit => IdealTag.pk0) (fun _ => ByteArray.empty) (fun _ => 0)
    (fun _ => by norm_num) (fun _ => ByteArray.empty) (fun _ => ByteArray.empty)
    (fun _ _ _ => rfl)
    (invP pf) (fun _ => invP pf) (invP pf) (fun _ => invP pf) {()} {()} 1
    (fun _ _ => invP_e pf) (fun _ _ => invP_e pf) 0 (fun _ _ => invP_k pf) (invP_k pf)
    (fun _ _ => invP_k pf) 0 (fun _ _ => invP_h pf) (invP_h pf) (fun _ _ => invP_h pf)
    (fun _ _ _ _ => ⟨⟨[], (List.append_nil _).symm⟩, [], (List.append_nil _).symm⟩)
    (fun _ _ _ _ => ⟨⟨[], (List.append_nil _).symm⟩, [], (List.append_nil _).symm⟩)
    (fun _ _ => rfl) (fun _ => pure ()) (fun _ _ => False) fun _ _ h => h.elim

/-- Unbound Moussaka in the permutation model (`moussakaUnbound_sim_joint_specP`): its hypotheses
hold likewise. -/
example (lr : Bool) (ci cr cd pf : ByteArray) :=
  moussakaUnbound_sim_joint_specP (ιI' := Unit) (ιR' := Unit) (βI := Unit) (βR := Unit)
    (α := Unit) (fun _ : Unit => moussakaUnboundIssue (toBA (List.replicate 45 0)) ci lr) lr
    (fun _ => (toBA (List.replicate 45 0), ci))
    (fun _ => Unbound.moussakaUnboundIssue_stmt _ _ _)
    (fun _ => by rw [Privacy.size_toBA, List.length_replicate]) (fun _ _ _ => rfl)
    (fun _ : Unit => moussakaUnboundRedeem [] UnboundROM.nf0 ci cr cd lr) (fun _ => [])
    (fun _ => by simp) (fun _ => UnboundROM.nf0) (fun _ => ci) (fun _ => cr) (fun _ => cd)
    (fun _ => Unbound.moussakaUnboundRedeem_stmt _ _ _ _ _ _) (fun _ => UnboundROM.nf0_size)
    (fun _ _ _ => rfl) (invP pf) (fun _ => invP pf) (invP pf) (fun _ => invP pf) {()} {()} 1
    (fun _ _ => invP_e pf) (fun _ _ => invP_e pf) 0 (fun _ _ => invP_k pf) (invP_k pf)
    (fun _ _ => invP_k pf) 0 (fun _ _ => invP_h pf) (invP_h pf) (fun _ _ => invP_h pf)
    (fun _ _ _ _ => ⟨⟨[], (List.append_nil _).symm⟩, [], (List.append_nil _).symm⟩)
    (fun _ _ _ _ => ⟨⟨[], (List.append_nil _).symm⟩, [], (List.append_nil _).symm⟩)
    (fun _ _ => rfl) (fun _ => pure ()) (fun _ _ => False) fun _ _ h => h.elim

/-- One inverse cipher query. -/
def invU : OracleComp specP Unit :=
  liftM (specP.query (.inr (false, (default, default)))) >>= fun _ => pure ()

lemma invU_k : IsKindQueryBoundP invU 0 := by
  rw [invU, IsKindQueryBoundP, isQueryBound_query_bind_iff]
  exact ⟨trivial, fun _ => trivial⟩

lemma invU_e : IsQueryBoundP invU (fun t => t.isRight = true) 1 := by
  rw [invU, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr Nat.one_pos, fun _ => isQueryBoundP_pure _ _ _⟩

lemma invU_h : IsQueryBoundP invU (fun t => t.isLeft = true) 0 := by
  rw [invU, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp), fun _ => isQueryBoundP_pure _ _ _⟩

/-- An OMUF adversary of the permutation model: one inverse cipher query, then `aU`'s moves. -/
def aUP : AdversaryP 2 1 where
  σ := Unit
  init := invU
  query _ := pure ((), ⟨0, ByteArray.empty, ByteArray.empty⟩)
  absorb _ _ := ()
  final _ := pure fun _ => ⟨[], ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩

theorem aUP_budget : aUP.Budget 0 1 0 :=
  ⟨invU_k, invU_e, invU_h, fun _ => trivial, fun _ => trivial, fun _ => trivial,
    fun _ => trivial, fun _ => trivial, fun _ => trivial⟩

/-- Moussaka Theorem 1 with simultaneous extraction in the permutation model
(`omuf_le_num_simP`): its hypotheses hold for `aUP` (an inverse cipher query). -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omuf_le_num_simP (lr := lr) (pk := pkU) (sk := sk) (qI := 1) aUP_budget pkU_digest pkU_inj

/-- A balance adversary of the permutation model: `balA0` with an inverse cipher query before each
request. -/
def balA0P : RatBalance.RoundAdvP Unit (Spec.Ratatouille.Op Spec.Ratatouille.Sizes.labelRows)
    RatBalance.Resp :=
  ⟨(), fun s => invU >>= fun _ =>
    pure (.issue (Vector.replicate _ 0) 1 (Vector.replicate 16 0), s), fun s _ => s⟩

lemma balA0P_k (s : Unit) : IsKindQueryBoundP (balA0P.next s) 0 :=
  isKindQueryBoundP_bind (q₂ := 0) invU_k fun _ => isQueryBound_pure _ _ _ _

lemma balA0P_e (s : Unit) : IsQueryBoundP (balA0P.next s) (fun t => t.isRight = true) 1 :=
  isQueryBoundP_bind (m := 0) invU_e fun _ _ => isQueryBoundP_pure _ _ 0

lemma balA0P_h (s : Unit) : IsQueryBoundP (balA0P.next s) (fun t => t.isLeft = true) 0 :=
  isQueryBoundP_bind (m := 0) invU_h fun _ _ => isQueryBoundP_pure _ _ 0

/-- Ratatouille balance with simultaneous extraction in the permutation model
(`balance_le_lean_simP`): its hypotheses hold for `balA0P` (inverse cipher queries), any signer
and any number of calls. -/
example (σ : RatBalance.Signer) (N : ℕ) (lr : Bool) :=
  RatBalance.balance_le_lean_simP lr IdealTag.pk0 balA0P N σ (by decide) balA0P_k balA0P_h
    balA0P_e

end VoleMole.Audit.SimExtract
