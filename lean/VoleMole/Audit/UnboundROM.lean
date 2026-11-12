import VoleMole.ROM.MoussakaUnboundSpec

/-!
# Non-vacuity of the unbound Moussaka soundness bounds

As `Audit/Nonvacuous.lean` for `ROM/MoussakaUnbound*.lean`: every hypothesis of the headline
theorems is instantiated with a concrete choice. The statement hypotheses (`Unbound.IssueStmt`,
`Unbound.RedeemStmt`) hold for the reference statements `Unbound.refIssue`, `Unbound.refRedeem`
(C++ parameters, DSTs, instance encodings, the sharing evaluators of `Arith/MoussakaUnbound.lean`),
and `hinj` for families with more than one instance with the C++ encodings
(`EndToEnd/MoussakaUnboundSpec.lean`).

What is not exhibited here: that the executable verifier's own unbound statements (on the branch
that extends `Verifier/Relations.lean`) satisfy `IssueStmt` / `RedeemStmt`; that is one lemma per
relation once they exist (`rfl` for the parameters, `uIssueValues_eq` / `uRedeemValues_eq` for the
evaluator, as `refIssue_stmt`, `refRedeem_stmt`).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Audit.UnboundROM

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Verifier VoleMole.Unbound

/-- A 24-byte nullifier. -/
def nf0 : ByteArray := toBA (List.replicate 24 0)

theorem nf0_size : nf0.size = 24 := by
  rw [nf0, Privacy.size_toBA, List.length_replicate]

/-- Unbound issuance, spec relation, every term explicit, at well-formed byte arrays
(`|t| = 45`), for the trivial prover. -/
example (lr : Bool) (ci pf : ByteArray) :=
  moussakaUnboundIssue_accept_le_full_spec (β := Unit)
    (refIssue_stmt lr (toBA (List.replicate 45 0)) ci)
    (by rw [Privacy.size_toBA, List.length_replicate]) (pure (pf, ())) 0 trivial 0 trivial

/-- The same with the ideal cipher as random permutations. -/
example (lr : Bool) (ci pf : ByteArray) :=
  moussakaUnboundIssue_accept_le_perm_spec (β := Unit)
    (refIssue_stmt lr (toBA (List.replicate 45 0)) ci)
    (by rw [Privacy.size_toBA, List.length_replicate]) (pure (pf, ())) 0 trivial 0 trivial

/-- Unbound issuance with an adaptively chosen instance, for every injective family with 45-byte
`t`, the prover arbitrary. -/
example {ι β : Type} (inst : ι → ByteArray × ByteArray) (lr : Bool)
    (hlen : ∀ s, (inst s).1.size = 45) (hi : Function.Injective inst)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :=
  moussakaUnboundIssue_accept_le_adaptive_spec (fun s => refIssue lr (inst s).1 (inst s).2) lr
    inst (fun _ => refIssue_stmt _ _ _) hlen
    (EndToEnd.SpecRel.hinj_refIssue lr inst 45 hlen hi) P qE hqE q hq

/-- The same with the ideal cipher as random permutations. -/
example {ι β : Type} (inst : ι → ByteArray × ByteArray) (lr : Bool)
    (hlen : ∀ s, (inst s).1.size = 45) (hi : Function.Injective inst)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :=
  moussakaUnboundIssue_accept_le_adaptive_perm_spec (fun s => refIssue lr (inst s).1 (inst s).2)
    lr inst (fun _ => refIssue_stmt _ _ _) hlen
    (EndToEnd.SpecRel.hinj_refIssue lr inst 45 hlen hi) P qE hqE q hq

/-- Unbound redemption, spec relation, every term explicit, at a 24-byte `nf`, for the trivial
prover. -/
example (A : List UovPk) (hA : A.length ≤ 64) (ci cr cd pf : ByteArray) (lr : Bool) :=
  moussakaUnboundRedeem_accept_le_full_spec (β := Unit) hA
    (refRedeem_stmt lr A nf0 ci cr cd) nf0_size cd (pure (pf, ())) 0 trivial 0 trivial 0
    trivial

/-- The same with the ideal cipher as random permutations. -/
example (A : List UovPk) (hA : A.length ≤ 64) (ci cr cd pf : ByteArray) (lr : Bool) :=
  moussakaUnboundRedeem_accept_le_perm_spec (β := Unit) hA
    (refRedeem_stmt lr A nf0 ci cr cd) nf0_size cd (pure (pf, ())) 0 trivial 0 trivial 0
    trivial

/-- The prover's choice in the redemption examples: a 16-byte redemption context and a challenge
digest. -/
abbrev Idx := {c : ByteArray // c.size = 16} × ByteArray

theorem idx_inj (A : List UovPk) (nf ci : ByteArray) :
    Function.Injective fun s : Idx => (A.map UovPk.digest, nf, ci, s.1.1, s.2) := by
  intro s s' h
  simp only [Prod.mk.injEq, true_and] at h
  exact Prod.ext (Subtype.ext h.1) h.2

/-- `hinj` for unbound redemption with the redemption context and the challenge digest chosen by
the prover (fixed Anchors with 32-byte digests, `nf` and `ctx_iss`). -/
theorem hinj_idx (A : List UovPk) (hA : A.length ≤ 64) (hdig : ∀ pk ∈ A, pk.digest.size = 32)
    (nf ci : ByteArray) (hnf : nf.size = 24) (hci : ci.size = 16) (lr : Bool) :
    Function.Injective fun s : Idx => (refRedeem lr A nf ci s.1.1 s.2).instEnc ByteArray.empty :=
  EndToEnd.SpecRel.hinj_refRedeem (ι := Idx) lr (fun _ => A) (fun _ => nf) (fun _ => ci)
    (fun s => s.1.1) (fun s => s.2) (fun _ => hdig) (fun _ => by omega) 24 16 16 (fun _ => hnf)
    (fun _ => hci) (fun s => s.1.2) (idx_inj A nf ci)

/-- Unbound redemption with the redemption context and the challenge digest chosen by the
prover, the prover arbitrary. -/
example {β : Type} (A : List UovPk) (hA : A.length ≤ 64) (hdig : ∀ pk ∈ A, pk.digest.size = 32)
    (nf ci : ByteArray) (hnf : nf.size = 24) (hci : ci.size = 16) (lr : Bool)
    (P : OracleComp specIC (ByteArray × (Idx × β)))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :=
  moussakaUnboundRedeem_accept_le_adaptive_spec (fun s : Idx => refRedeem lr A nf ci s.1.1 s.2)
    lr (fun _ => A) (fun _ => hA) (fun _ => nf) (fun _ => ci) (fun s => s.1.1) (fun s => s.2)
    (fun _ => refRedeem_stmt _ _ _ _ _ _) (fun _ => hnf) (hinj_idx A hA hdig nf ci hnf hci lr)
    P qE hqE n hn q hq

/-- The same with the ideal cipher as random permutations. -/
example {β : Type} (A : List UovPk) (hA : A.length ≤ 64) (hdig : ∀ pk ∈ A, pk.digest.size = 32)
    (nf ci : ByteArray) (hnf : nf.size = 24) (hci : ci.size = 16) (lr : Bool)
    (P : OracleComp specP (ByteArray × (Idx × β)))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :=
  moussakaUnboundRedeem_accept_le_adaptive_perm_spec
    (fun s : Idx => refRedeem lr A nf ci s.1.1 s.2) lr (fun _ => A) (fun _ => hA) (fun _ => nf)
    (fun _ => ci) (fun s => s.1.1) (fun s => s.2) (fun _ => refRedeem_stmt _ _ _ _ _ _)
    (fun _ => hnf) (hinj_idx A hA hdig nf ci hnf hci lr) P qE hqE n hn q hq

end VoleMole.Audit.UnboundROM
