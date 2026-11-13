import VoleMole.Theft.MoussakaUnboundLean
import VoleMole.Audit.UnboundRest
import VoleMole.Audit.Theft

/-!
# Audit of unbound Moussaka's Proposition U3 and Theorem U4 with the Lean prover and many tokens

* **Zero knowledge of the Lean prover for the unbound relations**
  (`Privacy/MoussakaUnboundLean.lean`): `leanPI_zkRO` and `leanPR_zkRO` have no hypotheses; they
  are instantiated at function rows. The issuance relation they are stated for holds for every
  honest Client (`issueRelW_honest`), so the statement is not about an empty relation; the
  redemption relation holds for every honest redemption of the game (`xwN_relR`).
* **One token, Lean prover** (`Theft/MoussakaUnboundLean.lean`): `nmU_lean`, `noSquat_lean`,
  `noRedirectU_lean` are instantiated for the adversary of `Audit/UnboundRest.lean` whose output
  every verifier rejects: the hops' budgets are discharged (`budget_of_eq`), weak
  simulation-extractability and the PRF bound are taken with error `1`.
* **`U` tokens, `M` redemptions** (`Theft/MoussakaUnboundMany.lean`): `nmUN`, `noSquatN`,
  `noRedirectUN` and their Lean-prover forms are instantiated for a trivial adversary, for every
  `U ≥ 1` and `M`, with `WeakSEN` at error `1` (`weakSEN_one`) and any injective family of
  `M + 1` contexts; such a family exists for every `M < 2¹²⁸` (`exists_pts`). This checks that
  the hypotheses are consistent with each other, not that they are small.
* **The events are the intended ones.** An honest redemption request replayed under its own
  statement is not fresh (`replay_not_freshN`); the same statement under another redemption
  context is (`redirect_ctx_freshN`). The first hop has no collision term (`delta0_zero`).
* **Key recovery with many nullifiers reduces to the PRF** for any adversary with a read bound,
  here one that outputs the zero key and reads nothing (`owkN_zero`).

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.UnboundMany

open VoleMole.Privacy VoleMole.Theft VoleMole.Theft.MoussakaUnbound VoleMole.Spec
  VoleMole.Spec.MoussakaUnbound VoleMole.ZK.Sim VoleMole.Privacy.MoussakaUnbound
  VoleMole.Audit.UnboundRest
open VoleMole.Audit.Theft (budget_of_eq)
open VoleMole.Spec.Moussaka (AnchorSet Error ctxBytes proveSeedBytes nfBytes rBytes maxAnchors)
open VoleMole.Privacy.Moussaka (ShM leanSim)

/-! ## Zero knowledge of the Lean prover -/

/-- The Lean prover's zero knowledge for the two unbound relations, at function rows. -/
example (q3 q5 qE : ℕ) := leanPI_zkRO (R := Blk → Blk) q3 q5 qE
example (q3 q5 qE : ℕ) := leanPR_zkRO (R := Blk → Blk) q3 q5 qE

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

/-- **The issuance relation is inhabited**: every honest Client's statement and witness. -/
theorem issueRelW_honest (k : Coins nfKeyBytes) (r : Coins rBytes) (ci : Coins ctxBytes) :
    IssueRelW ⟨ucom (List.ofFn k) (List.ofFn ci) (List.ofFn r), List.ofFn ci⟩
      (encodeIssueWitness (List.ofFn k) (List.ofFn ci) (List.ofFn r)) :=
  ⟨⟨List.ofFn k, List.ofFn r, List.length_ofFn, List.length_ofFn, rfl, rfl⟩, List.length_ofFn⟩

/-! ## One token, with the Lean prover -/

section One

variable {G S : Type}

theorem distI_thiefU (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)
    (ω : MoussakaUnbound.Sec) (r₂ : Coins proveSeedBytes) (g₂ : G) :
    MoussakaUnbound.distI (thiefU G S) PR (fun _ _ _ => false) (fun _ _ _ => false) extU ω r₂ g₂ =
      fun _ _ _ => False := by
  funext p g u
  simp [MoussakaUnbound.distI, D₁, MoussakaUnbound.Bad, MoussakaUnbound.accE,
    MoussakaUnbound.AccOp, thiefU]

theorem distR_thiefU {CI : Type} (simI : IssueInstance → CI → Bytes)
    (progI : IssueInstance → CI → S → S) (ω : MoussakaUnbound.Sec) (c₁ : CI) (g₁ : G) :
    MoussakaUnbound.distR (thiefU G S) (fun _ _ _ => false) (fun _ _ _ => false) extU simI progI
      ω c₁ g₁ = fun _ _ _ => False := by
  funext p g u
  simp [MoussakaUnbound.distR, D₂, MoussakaUnbound.Bad, MoussakaUnbound.accE,
    MoussakaUnbound.AccOp, thiefU]

/-- `nmU_lean`'s hypotheses hold for the trivial adversary, with the Lean prover. -/
example (q3 q5 qE : ℕ) :=
  nmU_lean (R := Blk → Blk) (thiefU _ _) (fun _ _ _ => false) (fun _ _ _ => false) extU
    (q3 := q3) (q5 := q5) (qE := qE) (AdmE := fun _ => True)
    (fun ω r₂ g₂ => budget_of_eq (distI_thiefU _ ω r₂ g₂))
    (fun ω c₁ g₁ => budget_of_eq (distR_thiefU _ _ ω c₁ g₁))
    (weakSE2_one _ _ _ _ _ _ _ _ _) (fun _ _ => trivial) (fun _ => prf1Adv_le_one _ _)

/-- The same for `noSquat_lean` and `noRedirectU_lean`. -/
example (q3 q5 qE : ℕ) :=
  And.intro
    (noSquat_lean (R := Blk → Blk) (thiefU _ _) (fun _ _ _ => false) (fun _ _ _ => false) extU
      (q3 := q3) (q5 := q5) (qE := qE) (AdmE := fun _ => True)
      (fun ω r₂ g₂ => budget_of_eq (distI_thiefU _ ω r₂ g₂))
      (fun ω c₁ g₁ => budget_of_eq (distR_thiefU _ _ ω c₁ g₁))
      (weakSE2_one _ _ _ _ _ _ _ _ _) (fun _ _ => trivial) (fun _ => prf1Adv_le_one _ _))
    (noRedirectU_lean (R := Blk → Blk) (thiefU _ _) (fun _ _ _ => false) (fun _ _ _ => false) extU
      (q3 := q3) (q5 := q5) (qE := qE) (AdmE := fun _ => True)
      (fun ω r₂ g₂ => budget_of_eq (distI_thiefU _ ω r₂ g₂))
      (fun ω c₁ g₁ => budget_of_eq (distR_thiefU _ _ ω c₁ g₁))
      (weakSE2_one _ _ _ _ _ _ _ _ _) (fun _ _ => trivial) (fun _ => prf1Adv_le_one _ _))

end One

/-! ## `U` tokens and `M` redemptions -/

section Many

variable {G S : Type} {U M : ℕ}

/-- **A trivial adversary** against `U ≥ 1` tokens: constant choices, always token `0`, and an
empty redemption request as its output. -/
def thiefNU (U M : ℕ) [NeZero U] (G S : Type) : ThiefN U M G S :=
  ⟨fun _ _ => 0, fun _ => ⟨[], fun _ => 0⟩, fun _ _ _ => 0, fun _ _ => (0, set0, fun _ => 0, []),
    fun _ _ _ _ => .redeem set0 [] [] [] []⟩

/-- A constant extractor. -/
def extNU : ExtN U M G S := fun _ _ _ _ => []

/-- **`M + 1` distinct contexts exist** for every `M < 2¹²⁸`. -/
theorem exists_pts (hM : M + 1 ≤ 2 ^ 128) :
    ∃ pts : Fin (M + 1) → Coins ctxBytes, Function.Injective pts := by
  have hc : Fintype.card (Fin (M + 1)) ≤ Fintype.card (Coins ctxBytes) := by
    rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_fin, Prob.card_uint8]
    simp only [ctxBytes]
    norm_num
    exact hM
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hc
  exact ⟨f, f.injective⟩

theorem distPN_thiefNU [NeZero U] [Nonempty G] {CI CR : Type} [Nonempty CI] [Nonempty CR]
    (PI : Bytes → IssueInstance → Bytes → G → S → Bytes)
    (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)
    (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → S → S)
    (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → S → S)
    (i : Fin (U + M)) (ω : SecN U) (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (CI × CR) G) :
    distPN (thiefNU U M G S) PI PR simI progI simR progR (fun _ _ _ => false) (fun _ _ _ => false)
      extNU i ω τ = fun _ _ _ => False := by
  funext p g u
  simp [distPN, distN, contN, BadN, accN, MoussakaUnbound.AccOp, opN, thiefNU]

/-- `nmUN`'s hypotheses hold together for the trivial adversary, with any provers and
simulators, for every `U ≥ 1`, `M` and injective family of contexts. -/
example [NeZero U] [Fintype G] [Nonempty G] [Fintype S] [Nonempty S]
    (PI : Bytes → IssueInstance → Bytes → G → S → Bytes)
    (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)
    (simI : IssueInstance → Coins 1 → Bytes) (progI : IssueInstance → Coins 1 → S → S)
    (simR : RedeemInstance → Coins 1 → Bytes) (progR : RedeemInstance → Coins 1 → S → S)
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts) :=
  nmUN (thiefNU U M G S) PI PR simI progI simR progR (fun _ _ _ => false) (fun _ _ _ => false)
    extNU (AdmI := fun _ => True) (AdmR := fun _ => True) (AdmE := fun _ => True)
    (zkRO_one _ _ _ _ _) zero_le_one (zkRO_one _ _ _ _ _) zero_le_one
    (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (weakSEN_one _ _ _ _ _ _ _ _)
    (fun _ => trivial) pts hpts (fun _ _ => prf1Adv_le_one _ _)

/-- `nmUN_lean`, `noSquatN_lean` and `noRedirectUN_lean`: the hypotheses hold for the trivial
adversary with the Lean prover; the hops' budgets are discharged. -/
example [NeZero U] (q3 q5 qE : ℕ) (pts : Fin (M + 1) → Coins ctxBytes)
    (hpts : Function.Injective pts) :=
  And.intro
    (nmUN_lean (R := Blk → Blk) (thiefNU U M _ _) (fun _ _ _ => false) (fun _ _ _ => false) extNU
      (q3 := q3) (q5 := q5) (qE := qE) (AdmE := fun _ => True)
      (fun i _ ω τ => budget_of_eq (distPN_thiefNU _ _ _ _ _ _ i ω τ))
      (fun i _ ω τ => budget_of_eq (distPN_thiefNU _ _ _ _ _ _ i ω τ))
      (weakSEN_one _ _ _ _ _ _ _ _) (fun _ => trivial) pts hpts (fun _ _ => prf1Adv_le_one _ _))
    (And.intro
      (noSquatN_lean (R := Blk → Blk) (thiefNU U M _ _) (fun _ _ _ => false) (fun _ _ _ => false)
        extNU (q3 := q3) (q5 := q5) (qE := qE) (AdmE := fun _ => True)
        (fun i _ ω τ => budget_of_eq (distPN_thiefNU _ _ _ _ _ _ i ω τ))
        (fun i _ ω τ => budget_of_eq (distPN_thiefNU _ _ _ _ _ _ i ω τ))
        (weakSEN_one _ _ _ _ _ _ _ _) (fun _ => trivial) pts hpts (fun _ _ => prf1Adv_le_one _ _))
      (noRedirectUN_lean (R := Blk → Blk) (thiefNU U M _ _) (fun _ _ _ => false)
        (fun _ _ _ => false) extNU (q3 := q3) (q5 := q5) (qE := qE) (AdmE := fun _ => True)
        (fun i _ ω τ => budget_of_eq (distPN_thiefNU _ _ _ _ _ _ i ω τ))
        (fun i _ ω τ => budget_of_eq (distPN_thiefNU _ _ _ _ _ _ i ω τ))
        (weakSEN_one _ _ _ _ _ _ _ _) (fun _ => trivial) pts hpts
        (fun _ _ => prf1Adv_le_one _ _)))

/-- **A replay is excluded**: an operation whose statement is an honest redemption statement of
the log is not fresh. -/
theorem replay_not_freshN (l : Log) (S' : AnchorSet) (req ci cr cd π : Bytes)
    (h : some (Sum.inr (stOfR S' req ci cr cd), π) ∈ l) :
    ¬ FreshOpN l (.redeem S' req ci cr cd) :=
  fun hf => hf _ π h rfl

/-- **A redirect to another redemption context is in scope**: a redemption whose context differs
from the context of every honest redemption is fresh. -/
theorem redirect_ctx_freshN (l : Log) (S' : AnchorSet) (req ci cr cd : Bytes)
    (hcr : ∀ x π, some (Sum.inr x, π) ∈ l → x.ctxRed ≠ cr) :
    FreshOpN l (.redeem S' req ci cr cd) := by
  intro x π hx heq
  exact hcr x π hx (by rw [← heq]; rfl)

/-- **The first hop has no collision term.** -/
example [NeZero U] [Fintype G] [Nonempty G] [Fintype S] {CI CR : Type} [Fintype CI] [Nonempty CI]
    [Fintype CR] [Nonempty CR] (A : ThiefN U M G S)
    (PI : Bytes → IssueInstance → Bytes → G → S → Bytes)
    (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)
    (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → S → S)
    (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → S → S) :
    pr (TapeN U M CI CR G S) (deltaNU A PI PR simI progI simR progR
      ⟨0, Nat.add_pos_left (Nat.pos_of_ne_zero (NeZero.ne U)) M⟩) = 0 :=
  deltaN_zero _ _ _ _

/-- **Key recovery with many nullifiers reduces to the PRF**, for an adversary that outputs the
zero key and reads nothing. -/
theorem owkN_zero (ci : Bytes) (pts : Fin (M + 1) → Coins ctxBytes)
    (hpts : Function.Injective pts) :
    owkAdvN ci ((fun _ _ _ => List.replicate 16 0) : OAdvN Unit Bytes) ≤
      1 + ((M : ℝ) + 1) / 2 ^ 192 :=
  owkAdvN_le ci _ pts hpts (fun _ _ => ⟨fun _ => ∅, fun _ => by simp, fun _ _ _ => rfl⟩)
    fun _ => prf1Adv_le_one _ _

end Many

end VoleMole.Audit.UnboundMany
