import VoleMole.Theft.RatatouilleLean
import VoleMole.Theft.MoussakaLean
import VoleMole.Theft.SimExtractLean
import VoleMole.Theft.Tables

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

* **The budget and plain-extraction versions can hold.** `noTheft_lean_reads`,
  `noRedirect_lean_reads` (`Theft/Reads.lean`: the hops' budgets proved) and
  `noTheft_lean_plain`, `noRedirect_lean_plain` (`Theft/SimExtractLean.lean`: `WeakSE2` replaced
  by plain extraction and programmed-point hits) are instantiated for the same adversaries, with
  a constant extractor (`StageBudget.const`, `plainSE_one`, `progEv_one`).
* **`Adv^ow` is not small in this model** (`owAdv_one_ratatouille`, `owAdv_one_moussaka`): `Com` is
  a fixed function here and the inverter any function, so an inverter that picks a preimage of the
  commitment it is given wins with probability `1`. The note's `q_K·2⁻¹²⁷` needs `KP800` as an
  ideal permutation (a random table) and an inverter with a bounded number of queries to it.

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

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

/-- `noTheft_lean_reads`'s hypotheses hold for the trivial thief: the budgets of a constant last
stage and a constant extractor. -/
example :=
  noTheft_lean_reads (R := Blk → Blk) (thief0 _ _ _) ext0 (AdmE := fun _ => True)
    (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudget.const _) (fun _ _ => StageBudget.const _)
    (weakSE2_one _ _ _ _ _ _ _ _ _) fun _ _ => trivial

/-- A constant witness. -/
def wit0 : Wit :=
  (⟨Vector.replicate 24 0, Vector.replicate 16 0⟩,
    ⟨0, Vector.replicate 16 0, 0, Vector.replicate 119 0, Vector.replicate 24 0, 0,
      Vector.replicate 16 0⟩)

/-- `noTheft_lean_plain`'s hypotheses hold for the trivial thief and a constant extractor. -/
example :=
  noTheft_lean_plain (R := Blk → Blk) (thief0 _ _ _) (e := fun _ _ _ _ _ _ => wit0)
    (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudget.const _) (fun _ _ => StageBudget.const _)
    (plainSE_one _ _ _ _ _) (progEv_one _ _ _ _ _ _ _)

/-- `noTheft_leanX_plain`'s hypotheses hold for the trivial thief and a constant extractor, with
`H₁`, `H₂⁰`, `H₂⁴`, `H₄`, `H₂¹`, `H₂²` and `H_comb` read off uniform tables (`hbX`, inputs of at
most `L` bytes). -/
example (L M : ℕ) :=
  noTheft_leanX_plain (R := Blk → Blk) (X := XTab L M) (Hb := hbX) (thief0 _ _ _) hbX_wf
    (e := fun _ _ _ _ _ _ => wit0) (Adm := fun _ => True) (Adm₀ := fun _ => True)
    (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ _ => StageBudget.const _) (fun _ _ _ => StageBudget.const _) (ε₀ := 1) (εh := 1)
    (plainSE_one _ _ _ _ _) (progEv_one _ _ _ _ _ _ _) (fun _ _ => trivial)
    fun _ _ _ _ _ _ => trivial

/-- **`Adv^ow` is `1` for some inverter** in this model: `Com` is a fixed function, and the
inverter that picks an opening of the first commitment at `t = 0` always succeeds. -/
theorem owAdv_one_ratatouille (ctx : Context) :
    ∃ B : Nullifier → (Credits → Commitment) → (Credits → Commitment) → Unit →
      Bool × Credits × Open4, owAdv ctx B = 1 := by
  refine ⟨fun nf L₁ _ _ => (false, 0, (nf, ctx, 0,
    Classical.epsilon fun r => com nf ctx 0 r = L₁ 0)), ?_⟩
  unfold owAdv
  rw [pr_congr (Q := fun _ => True) fun z => ⟨fun _ => trivial, fun _ => ?_⟩, pr_const]
  · simp
  · simp only [comOf, Bool.false_eq_true, ite_false]
    exact Classical.epsilon_spec (p := fun r => com (vec z.1.1.1) ctx 0 r = com (vec z.1.1.1) ctx 0
      (vec z.1.1.2)) ⟨_, rfl⟩

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

/-- `noRedirect_lean_reads`'s hypotheses hold for the trivial adversary. -/
example :=
  noRedirect_lean_reads (R := Blk → Blk) (thiefM _ _) extM (AdmE := fun _ => True)
    (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudget.const _) (fun _ _ => StageBudget.const _)
    (weakSE2_one _ _ _ _ _ _ _ _ _) fun _ _ => trivial

/-- `noRedirect_lean_plain`'s hypotheses hold for the trivial adversary and a constant
extractor. -/
example :=
  noRedirect_lean_plain (R := Blk → Blk) (thiefM _ _) (e := fun _ _ _ _ _ _ => [])
    (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudget.const _) (fun _ _ => StageBudget.const _)
    (plainSE_one _ _ _ _ _) (progEv_one _ _ _ _ _ _ _)

/-- `noRedirect_leanX_plain`'s hypotheses hold for the trivial adversary and a constant
extractor, with the other hashes read off uniform tables (`hbX`). -/
example (L M : ℕ) :=
  noRedirect_leanX_plain (R := Blk → Blk) (X := XTab L M) (Hb := hbX) (thiefM _ _) hbX_wf
    (e := fun _ _ _ _ _ _ => []) (Adm := fun _ => True) (Adm₀ := fun _ => True)
    (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ _ => StageBudget.const _) (fun _ _ _ => StageBudget.const _) (ε₀ := 1) (εh := 1)
    (plainSE_one _ _ _ _ _) (progEv_one _ _ _ _ _ _ _) (fun _ _ => trivial)
    fun _ _ _ _ _ _ => trivial

/-- **`Adv^ow` is `1` for some inverter** in this model (Moussaka): the inverter that picks an
opening of the commitment it is given always succeeds. -/
theorem owAdv_one_moussaka (ci cr : Bytes) :
    ∃ B : Bytes → Bytes → Unit → Moussaka.Open4, Moussaka.owAdv ci cr B = 1 := by
  refine ⟨fun nf t _ => (nf, ci, cr, Classical.epsilon fun r => com nf ci cr r = t), ?_⟩
  unfold Moussaka.owAdv
  rw [pr_congr (Q := fun _ => True) fun z => ⟨fun _ => trivial, fun _ => ?_⟩, pr_const]
  · simp
  · simp only [Moussaka.comOf]
    exact Classical.epsilon_spec (p := fun r => com (List.ofFn z.1.1) ci cr r =
      com (List.ofFn z.1.1) ci cr (List.ofFn z.1.2)) ⟨_, rfl⟩

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
