import VoleMole.Theft.RatatouilleLean
import VoleMole.Theft.MoussakaLean

/-!
# Audit of the non-malleability theorems (`Theft/`)

* **The hypotheses can hold together with the Lean prover.** `noTheft_lean` and
  `noRedirect_lean` are instantiated with the executable Lean prover (function rows) for an
  adversary whose output the verifiers reject: the read budgets of the hops' distinguishers are
  discharged (`budget_const`), weak simulation-extractability is taken with error `1`
  (`weakSE2_one`; its content is the error, which L8 bounds on paper). This checks that the
  hypotheses are consistent, not that they are small.
* **F2 is excluded, a redirect is not.** A verbatim copy of the honest Client's spend request is
  not fresh (`copy_not_freshS`), so the no-theft event does not count the copying attack the note
  shows possible; a spend request with another amount is fresh (`changed_freshS`). For Moussaka,
  the honest redemption request replayed under the same Anchor Set, contexts and digest is not
  fresh (`replay_not_freshR`), and the same bytes under another challenge digest are
  (`redirect_freshR`): redirecting is what the theorem bounds.

No `sorry`, no `axiom`.
-/

namespace VoleMole.Audit.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Theft

/-- A distinguisher that does not read the tables has every budget. -/
lemma budget_const {R : Type} {O : Type*} {p : VoleMole.Verifier.Params} (P : Prop) (q3 q5 qE : ℕ) :
    Budget p q3 q5 qE (fun (_ : O) (_ : Tab3) (_ : ShG R p) => P) :=
  ⟨fun _ _ => (Rd3.const P).mono (Nat.zero_le _), fun _ _ => (Rd5.const P).mono (Nat.zero_le _),
    fun _ _ => (RdE.const P).mono (Nat.zero_le _)⟩

/-- The same, for a distinguisher equal to a constant. -/
lemma budget_of_eq {R : Type} {O : Type*} {p : VoleMole.Verifier.Params} {P : Prop} {q3 q5 qE : ℕ}
    {D : O → Tab3 → ShG R p → Prop} (h : D = fun _ _ _ => P) : Budget p q3 q5 qE D :=
  h ▸ budget_const P q3 q5 qE

section Rat

open VoleMole.Theft.Ratatouille VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille

variable {Z : Sizes} {G S : Type}

/-- A request of zeros. -/
def zeroSpend (Z : Sizes) : SpendRequest Z := Vector.replicate _ 0

/-- **A trivial thief**: constant choices, and a constant spend request as its output. -/
def thief0 (Z : Sizes) (G S : Type) : Thief Z G S :=
  ⟨fun _ => 0, Vector.replicate 16 0, 1, fun _ => Vector.replicate 119 0, fun _ => 1,
    fun _ _ _ _ _ => .spend (zeroSpend Z) (Vector.replicate 16 0) 0⟩

/-- A constant extractor. -/
def ext0 : Ext Z G S := fun _ _ _ _ _ _ =>
  (⟨Vector.replicate 24 0, Vector.replicate 16 0⟩,
    ⟨0, Vector.replicate 16 0, 0, Vector.replicate 119 0, Vector.replicate 24 0, 0,
      Vector.replicate 16 0⟩)

theorem distI_thief0 (PI : IssueInstance → IssueWitness → Rho → G → S → Option (IssueProof Z))
    (PS : SpendInstance → SpendWitness → Rho → G → S → Option (SpendProof Z)) (ω : Sec)
    (r₂ : Coins 16) (g₂ : G) :
    distI (thief0 Z G S) PI PS (fun _ _ _ => false) (fun _ _ _ => false) ext0 ω r₂ g₂ =
      fun _ _ _ => False := by
  funext p g u
  simp [distI, D₁, Bad, accE, AccOp, thief0]

theorem distS_thief0 {CI : Type} (simI : IssueInstance → CI → Option (IssueProof Z))
    (progI : IssueInstance → CI → S → S) (ω : Sec) (c₁ : CI) (g₁ : G) :
    distS (thief0 Z G S) (fun _ _ _ => false) (fun _ _ _ => false) ext0 simI progI ω c₁ g₁ =
      fun _ _ _ => False := by
  funext p g u
  simp [distS, D₂, Bad, accE, AccOp, thief0]

/-- `noTheft_lean`'s hypotheses hold for the trivial thief, with the Lean prover. -/
example (q3 q5 qE : ℕ) :=
  noTheft_lean (R := Blk → Blk) (thief0 _ _ _) (fun _ _ _ => false) (fun _ _ _ => false) ext0
    (q3 := q3) (q5 := q5) (qE := qE) (AdmE := fun _ => True)
    (fun ω r₂ g₂ => budget_of_eq (distI_thief0 _ _ ω r₂ g₂))
    (fun ω c₁ g₁ => budget_of_eq (distS_thief0 _ _ ω c₁ g₁))
    (weakSE2_one _ _ _ _ _ _ _ _ _) fun _ _ => trivial

/-- **F2 is excluded**: the honest spend request, copied verbatim under the Client's context, is
not fresh. -/
theorem copy_not_freshS (A : Thief Z G S) (o₁ : Except Error (IssueRequest Z)) (q : SpendRequest Z)
    (x : Credits) : ¬ FreshOp A (stI A o₁) (stS A (.ok q)) (.spend q A.ctx x) :=
  fun h => h _ rfl rfl

/-- A spend request with another amount is fresh. -/
theorem changed_freshS (A : Thief Z G S) (o₁ : Except Error (IssueRequest Z)) (q q' : SpendRequest Z)
    (c : Context) (x : Credits) (hd : (SpendReq.parse q').d ≠ (SpendReq.parse q).d) :
    FreshOp A (stI A o₁) (stS A (.ok q)) (.spend q' c x) := by
  rintro y hy heq
  cases hy
  exact hd (SpendInstance.mk.inj heq).2.2.1

end Rat

section Mous

open VoleMole.Theft.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka

variable {G S : Type}

/-- A one-key Anchor Set. -/
def set0 : AnchorSet := ⟨[⟨[], fun _ => 0⟩], by simp, by simp [maxAnchors], by simp⟩

/-- **A trivial adversary**: constant choices, and a constant redemption request as its output. -/
def thiefM (G S : Type) : Thief G S :=
  ⟨fun _ => 0, fun _ => 0, ⟨[], fun _ => 0⟩, fun _ _ => 0, fun _ => (set0, []),
    fun _ _ _ _ _ => .redeem set0 [] [] [] []⟩

/-- A constant extractor. -/
def extM : Moussaka.Ext G S := fun _ _ _ _ _ _ => []

theorem distI_thiefM (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes) (ω : Moussaka.Sec)
    (r₂ : Coins proveSeedBytes) (g₂ : G) :
    Moussaka.distI (thiefM G S) PR (fun _ _ _ => false) (fun _ _ _ => false) extM ω r₂ g₂ =
      fun _ _ _ => False := by
  funext p g u
  simp [Moussaka.distI, D₁, Moussaka.Bad, Moussaka.accE, Moussaka.AccOp, thiefM]

theorem distR_thiefM {CI : Type} (simI : IssueInstance → CI → Bytes)
    (progI : IssueInstance → CI → S → S) (ω : Moussaka.Sec) (c₁ : CI) (g₁ : G) :
    distR (thiefM G S) (fun _ _ _ => false) (fun _ _ _ => false) extM simI progI ω c₁ g₁ =
      fun _ _ _ => False := by
  funext p g u
  simp [distR, D₂, Moussaka.Bad, Moussaka.accE, Moussaka.AccOp, thiefM]

/-- `noRedirect_lean`'s hypotheses hold for the trivial adversary, with the Lean prover. -/
example (q3 q5 qE : ℕ) :=
  noRedirect_lean (R := Blk → Blk) (thiefM _ _) (fun _ _ _ => false) (fun _ _ _ => false) extM
    (q3 := q3) (q5 := q5) (qE := qE) (AdmE := fun _ => True)
    (fun ω r₂ g₂ => budget_of_eq (distI_thiefM _ ω r₂ g₂))
    (fun ω c₁ g₁ => budget_of_eq (distR_thiefM _ _ ω c₁ g₁))
    (weakSE2_one _ _ _ _ _ _ _ _ _) fun _ _ => trivial

/-- **A replay is excluded**: the honest redemption request under the honest Anchor Set, contexts
and digest is not fresh. -/
theorem replay_not_freshR (A : Moussaka.Thief G S) (o₁ b : Bytes) :
    ¬ Moussaka.FreshOp (Moussaka.stI A o₁) (stR A o₁ (.ok b))
      (.redeem (A.choose o₁).1 b A.ci A.cr (A.choose o₁).2) :=
  fun h => h _ rfl rfl

/-- **A redirect is in scope**: the same request bytes under another challenge digest are fresh. -/
theorem redirect_freshR (A : Moussaka.Thief G S) (o₁ b cd : Bytes) (hcd : cd ≠ (A.choose o₁).2) :
    Moussaka.FreshOp (Moussaka.stI A o₁) (stR A o₁ (.ok b)) (.redeem (A.choose o₁).1 b A.ci A.cr cd) := by
  rintro y hy heq
  cases hy
  exact hcd (RedeemInstance.mk.inj heq).2.2.2.2

end Mous

end VoleMole.Audit.Theft
