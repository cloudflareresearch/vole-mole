import VoleMole.ROM.MoussakaUnboundCor
import VoleMole.Theft.MoussakaUnbound
import VoleMole.Audit.UnboundOMUF

/-!
# Audit of unbound Moussaka Corollary U2, Proposition U3 and Theorem U4

* **Corollary U2** (`ROM/MoussakaUnboundCor.lean`): `corU2_le_num_sim` and
  `corU2_le_num_ompr_sim` are instantiated with the OMUF-U adversary `aUU` of
  `Audit/UnboundOMUF.lean` (two honest Anchors with distinct digests, the toy ideal forger for
  `hmodel`), so their hypotheses hold together. `honest_nf_distinct` has no hypotheses; it is
  stated at `U = 2`.
* **Proposition U3 and Theorem U4** (`Theft/MoussakaUnbound.lean`): `nmU`, `noSquat` and
  `noRedirectU` are instantiated for an adversary whose output every verifier rejects, with any
  provers, simulators and extractor: zero knowledge and weak simulation-extractability with error
  `1` (`zkRO_one`, `weakSE2_one`), the PRF hypothesis with `ε_prf = 1` (`prf1Adv_le_one`). This
  checks that the hypotheses are consistent with each other, not that they are small; their
  content is the errors (ZK: `lean/docs/zk.md`; SE: L8 on paper; PRF: a Keccak-p[800] assumption).
* **The events are the intended ones.** The honest redemption request replayed under its own
  statement is not fresh (`replay_not_freshU`); the same bytes under **another redemption
  context** are fresh (`redirect_ctx_freshU`), so redirecting a token to another Moderator is in
  the event. A redemption carrying the honest nullifier for its context is in `Squat`
  (`squat_of_nf`), whatever its witness.
* **Key recovery reduces to the PRF**: `owkAdv_le` holds for any adversary, here one that outputs
  the zero key (`owk_zero`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Audit.UnboundRest

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Verifier VoleMole.Audit
open VoleMole.ROM.IC.OMUF VoleMole.ROM.IC.OMUFU VoleMole.Assumptions.UOV
  VoleMole.Assumptions.UOV.Links VoleMole.Audit.UnboundOMUF

/-! ## Corollary U2 -/

/-- Corollary U2 with simultaneous extraction (`corU2_le_num_sim`): its hypotheses hold. -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  corU2_le_num_sim (lr := lr) (sk := sk) (qI := 2) aUU_budget pkU_digest pkU_inj

/-- Corollary U2 down to OMPR (`corU2_le_num_ompr_sim`), with the toy ideal forger. -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  corU2_le_num_ompr_sim (lr := lr) (pk := pkU) (sk := sk) (qI := 2) toyTrap (fun _ => ((), ())) 0 0
    aUU_budget pkU_digest pkU_inj (toyF 2) (toyF_budget 2) (toy_hmodel _ (prEvent_le_one _))

/-- Corollary U2, item 3, at two tokens. -/
example (c : Privacy.Coins Spec.Moussaka.ctxBytes) :=
  VoleMole.MoussakaUnbound.CorU2.honest_nf_distinct 2 c

/-! ## Proposition U3 and Theorem U4 -/

section NM

open VoleMole.Privacy VoleMole.Theft VoleMole.Theft.MoussakaUnbound VoleMole.Spec
  VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (AnchorSet Error ctxBytes proveSeedBytes nfBytes maxAnchors)

variable {G S : Type}

/-- Any prover and simulator are zero-knowledge with error `1` (a probability). -/
theorem zkRO_one {I W O ρ C G' S' : Type*} [Fintype ρ] [Fintype C] [Fintype G'] [Fintype S']
    (R : I → W → Prop) (prove : I → W → ρ → G' → S' → O) (sim : I → C → O)
    (prog : I → C → S' → S') (Adm : (O → G' → S' → Prop) → Prop) :
    ZeroKnowledgeRO R prove sim prog Adm 1 := fun x w _ D _ => by
  rw [abs_le]
  constructor <;> linarith [pr_nonneg (α := (ρ × G') × S') (fun a => D (prove x w a.1.1 a.1.2 a.2) a.1.2 a.2),
    pr_le_one (α := (ρ × G') × S') (fun a => D (prove x w a.1.1 a.1.2 a.2) a.1.2 a.2),
    pr_nonneg (α := (C × G') × S') (fun a => D (sim x a.1.1) a.1.2 (prog x a.1.1 a.2)),
    pr_le_one (α := (C × G') × S') (fun a => D (sim x a.1.1) a.1.2 (prog x a.1.1 a.2))]

/-- The PRF advantage is at most `1`. -/
theorem prf1Adv_le_one (ci : Bytes) (D : Bytes × (Privacy.Coins ctxBytes → Bytes) → Prop) :
    prf1Adv ci D ≤ 1 := by
  unfold prf1Adv
  rw [abs_le]
  constructor <;> linarith [pr_nonneg (α := Sec) (fun x => D (prf1Real ci x)),
    pr_le_one (α := Sec) (fun x => D (prf1Real ci x)),
    pr_nonneg (α := Sec × Tab1) (fun x => D (prf1Ideal ci x)),
    pr_le_one (α := Sec × Tab1) (fun x => D (prf1Ideal ci x))]

/-- A one-key Anchor Set. -/
def set0 : AnchorSet := ⟨[⟨[], fun _ => 0⟩], by simp, by simp [maxAnchors], by simp⟩

/-- **A trivial adversary**: constant choices, and an empty redemption request as its output. -/
def thiefU (G S : Type) : Thief G S :=
  ⟨fun _ => 0, ⟨[], fun _ => 0⟩, fun _ => 0, fun _ => (set0, fun _ => 0, []),
    fun _ _ _ _ _ => .redeem set0 [] [] [] []⟩

/-- A constant extractor. -/
def extU : MoussakaUnbound.Ext G S := fun _ _ _ _ _ _ => []

/-- `nmU`'s hypotheses hold together for the trivial adversary, with any provers and
simulators. -/
example [Fintype G] [Nonempty G] [Fintype S] [Nonempty S]
    (PI : Bytes → IssueInstance → Bytes → G → S → Bytes)
    (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)
    (simI : IssueInstance → Coins 1 → Bytes) (progI : IssueInstance → Coins 1 → S → S)
    (simR : RedeemInstance → Coins 1 → Bytes) (progR : RedeemInstance → Coins 1 → S → S) :=
  nmU (thiefU G S) PI PR (fun _ _ _ => false) (fun _ _ _ => false) extU simI progI simR progR
    (AdmI := fun _ => True) (AdmR := fun _ => True) (AdmE := fun _ => True)
    (zkRO_one _ _ _ _ _) zero_le_one (zkRO_one _ _ _ _ _) zero_le_one
    (fun _ _ _ => trivial) (fun _ _ _ => trivial) (weakSE2_one _ _ _ _ _ _ _ _ _)
    (fun _ _ => trivial) (fun _ => prf1Adv_le_one _ _)

/-- The same for Proposition U3 (`noSquat`) and Theorem U4 (`noRedirectU`). -/
example [Fintype G] [Nonempty G] [Fintype S] [Nonempty S]
    (PI : Bytes → IssueInstance → Bytes → G → S → Bytes)
    (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)
    (simI : IssueInstance → Coins 1 → Bytes) (progI : IssueInstance → Coins 1 → S → S)
    (simR : RedeemInstance → Coins 1 → Bytes) (progR : RedeemInstance → Coins 1 → S → S) :=
  And.intro (noSquat (thiefU G S) PI PR (fun _ _ _ => false) (fun _ _ _ => false) extU simI progI simR progR
    (AdmI := fun _ => True) (AdmR := fun _ => True) (AdmE := fun _ => True)
    (zkRO_one _ _ _ _ _) zero_le_one (zkRO_one _ _ _ _ _) zero_le_one
    (fun _ _ _ => trivial) (fun _ _ _ => trivial) (weakSE2_one _ _ _ _ _ _ _ _ _)
    (fun _ _ => trivial) (fun _ => prf1Adv_le_one _ _))
   (noRedirectU (thiefU G S) PI PR (fun _ _ _ => false) (fun _ _ _ => false) extU simI progI simR
    progR (AdmI := fun _ => True) (AdmR := fun _ => True) (AdmE := fun _ => True)
    (zkRO_one _ _ _ _ _) zero_le_one (zkRO_one _ _ _ _ _) zero_le_one
    (fun _ _ _ => trivial) (fun _ _ _ => trivial) (weakSE2_one _ _ _ _ _ _ _ _ _)
    (fun _ _ => trivial) (fun _ => prf1Adv_le_one _ _))

/-- **A replay is excluded**: the honest redemption request under its own Anchor Set, contexts
and digest is not fresh. -/
theorem replay_not_freshU (A : Thief G S) (o₁ b : Bytes) :
    ¬ MoussakaUnbound.FreshOp (MoussakaUnbound.stI A o₁) (MoussakaUnbound.stR A o₁ (.ok b))
      (.redeem (A.set o₁) b A.ci (A.cr o₁) (A.cd o₁)) :=
  fun h => h _ rfl rfl

/-- **A redirect to another redemption context is in scope**: the same request bytes under
another `ctx_red` are fresh. -/
theorem redirect_ctx_freshU (A : Thief G S) (o₁ b cr : Bytes) (hcr : cr ≠ A.cr o₁) :
    MoussakaUnbound.FreshOp (MoussakaUnbound.stI A o₁) (MoussakaUnbound.stR A o₁ (.ok b))
      (.redeem (A.set o₁) b A.ci cr (A.cd o₁)) := by
  rintro y hy heq
  cases hy
  exact hcr (RedeemInstance.mk.inj heq).2.2.2.1

/-- **Squatting needs no extraction**: an accepted fresh redemption carrying the honest nullifier
for its context is in `Squat`. -/
theorem squat_of_nf (A : Thief G S) (verI : IssueInstance → Bytes → S → Bool)
    (verR : RedeemInstance → Bytes → S → Bool) (ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes)
    (g₁ g₂ : G) (s : S) (S' : AnchorSet) (req ci cr cd : Bytes)
    (hq : A.out o₁ o₂ g₁ g₂ s = .redeem S' req ci cr cd)
    (ha : accE A verI verR ω o₁ o₂ g₁ g₂ s) (hf : freshE A ω o₁ o₂ g₁ g₂ s)
    (hn : req.take nfBytes = derive (List.ofFn ω.1) cr) :
    Squat A verI verR ω o₁ o₂ g₁ g₂ s := by
  refine ⟨ha, hf, ?_⟩
  rw [hq]
  exact hn

/-- **Key recovery reduces to the PRF**, for an adversary that outputs the zero key. -/
theorem owk_zero (ci : Bytes) :
    owkAdv ci (⟨fun _ _ => 0, fun _ _ _ => List.replicate 16 0⟩ : OAdv Unit Bytes) ≤ 1 + 1 / 2 ^ 192 :=
  owkAdv_le ci _ fun _ => prf1Adv_le_one _ _

end NM

end VoleMole.Audit.UnboundRest
