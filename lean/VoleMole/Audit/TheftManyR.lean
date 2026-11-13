import VoleMole.Theft.RatatouilleManyLean
import VoleMole.Theft.MoussakaManyReads
import VoleMole.Theft.MoussakaUnboundManyReads
import VoleMole.Theft.RatatouilleManyHit
import VoleMole.Audit.TheftMany
import VoleMole.Audit.UnboundMany

/-!
# Audit of Ratatouille no theft for `U` Clients and `M` spends, and of the many-proof bridges

* **The hypotheses can hold together.** `noTheftN` (`Theft/RatatouilleMany.lean`) is instantiated
  for a trivial adversary with any provers and simulators (zero knowledge and `WeakSEN` with
  error `1`), and `noTheftN_lean`, `noTheftN_lean_reads`, `noTheftN_lean_plain`
  (`Theft/RatatouilleManyLean.lean`) with the executable Lean prover (function rows), for every
  `U ≥ 1` and `M`. The same for `noRedirectN_lean_reads`, `noRedirectN_lean_plain`
  (`Theft/MoussakaManyReads.lean`) and `nmUN_lean_reads`, `nmUN_lean_plain`
  (`Theft/MoussakaUnboundManyReads.lean`). This checks that the hypotheses are consistent, not
  that they are small.
* **`ε_hit` is bounded with a satisfiable adversary class.** `noTheftN_leanX_hit`
  (`Theft/RatatouilleManyHit.lean`: the other hashes uniform tables, the programmed-point terms
  bounded) is instantiated at the trivial adversary, whose last stage reads no chain table
  (`AdmHitN 0 0 0`, `admHitN_const`), with `L = 14357`, for every `U ≥ 1` and `M`.
* **The game chains change tokens.** A spend whose request is sent and whose response the
  Client accepts leaves the Client with the change token made from the slot's coins
  (`change_chains`), and a later spend of that Client reveals the nullifier of the slot that made
  its current token and commits with the coins of its own slot (`next_spend`). So the nullifier
  of a change commitment becomes public when the change is spent.
* **The event is the intended one.** An honest spend statement of the log replayed is not fresh
  (`replay_not_freshNR`); a spend with an amount that differs from the amount of every honest
  spend is fresh (`changed_freshNR`).
* **`Adv^ow` is an assumption on the explicit inverter**: for some inverter `owAdvK` is `1`
  (`owAdvK_one`), as for `owAdv` of the one-Client theorem (`Audit/Theft.lean`,
  `owAdv_one_ratatouille`).
* **`WeakSEN` at `N = 2` and `WeakSE2`**: `weakSE2_of_weakSEN` is applied to `weakSEN_one`.

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.TheftManyR

open VoleMole.Privacy VoleMole.Theft VoleMole.ZK.Sim
open VoleMole.Audit.Theft (budget_of_eq zeroSpend wit0)
open VoleMole.Audit.UnboundRest (zkRO_one)

/-! ## Ratatouille -/

section Rat

open VoleMole.Theft.Ratatouille VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille

variable {Z : Sizes} {G S : Type} {U M : ℕ}

/-- **A trivial adversary** against `U ≥ 1` Clients: constant choices, always Client `0`, and a
constant spend request as its output. -/
def thiefNR (Z : Sizes) (U M : ℕ) [NeZero U] (G S : Type) : ThiefN Z U M G S :=
  ⟨fun _ => 0, fun _ => Vector.replicate 16 0, fun _ => 1, fun _ _ => Vector.replicate 119 0,
    fun _ _ => (0, 1), fun _ _ => Vector.replicate 127 0,
    fun _ _ _ _ => .spend (zeroSpend Z) (Vector.replicate 16 0) 0⟩

/-- A constant extractor. -/
def extNR : ExtN Z U M G S := fun _ _ _ _ => wit0

theorem distPI_thiefNR [NeZero U] [Nonempty G] {CI CS : Type} [Nonempty CI] [Nonempty CS]
    (PI : IssueInstance → IssueWitness → Rho → G → S → Option (IssueProof Z))
    (PS : SpendInstance → SpendWitness → Rho → G → S → Option (SpendProof Z))
    (simI : IssueInstance → CI → Option (IssueProof Z)) (progI : IssueInstance → CI → S → S)
    (simS : SpendInstance → CS → Option (SpendProof Z)) (progS : SpendInstance → CS → S → S)
    (i : Fin (U + M)) (ω : SecN U M) (τ : Fin (U + M) → Slot (Coins 16) (CI × CS) G) :
    distPI (thiefNR Z U M G S) PI PS simI progI simS progS (fun _ _ _ => false)
      (fun _ _ _ => false) extNR i ω τ = fun _ _ _ => False := by
  funext p g u
  simp [distPI, distN, contN, BadN, accN, AccOp, opN, thiefNR]

theorem distPS_thiefNR [NeZero U] [Nonempty G] {CI CS : Type} [Nonempty CI] [Nonempty CS]
    (PI : IssueInstance → IssueWitness → Rho → G → S → Option (IssueProof Z))
    (PS : SpendInstance → SpendWitness → Rho → G → S → Option (SpendProof Z))
    (simI : IssueInstance → CI → Option (IssueProof Z)) (progI : IssueInstance → CI → S → S)
    (simS : SpendInstance → CS → Option (SpendProof Z)) (progS : SpendInstance → CS → S → S)
    (i : Fin (U + M)) (ω : SecN U M) (τ : Fin (U + M) → Slot (Coins 16) (CI × CS) G) :
    distPS (thiefNR Z U M G S) PI PS simI progI simS progS (fun _ _ _ => false)
      (fun _ _ _ => false) extNR i ω τ = fun _ _ _ => False := by
  funext p g u
  simp [distPS, distN, contN, BadN, accN, AccOp, opN, thiefNR]

/-- `noTheftN`'s hypotheses hold together for the trivial adversary, with any provers and
simulators, for every `U ≥ 1` and `M`. -/
example [NeZero U] [Fintype G] [Nonempty G] [Fintype S] [Nonempty S]
    (PI : IssueInstance → IssueWitness → Rho → G → S → Option (IssueProof Z))
    (PS : SpendInstance → SpendWitness → Rho → G → S → Option (SpendProof Z))
    (simI : IssueInstance → Coins 1 → Option (IssueProof Z))
    (progI : IssueInstance → Coins 1 → S → S)
    (simS : SpendInstance → Coins 1 → Option (SpendProof Z))
    (progS : SpendInstance → Coins 1 → S → S) :=
  noTheftN (thiefNR Z U M G S) PI PS simI progI simS progS (fun _ _ _ => false)
    (fun _ _ _ => false) extNR (AdmI := fun _ => True) (AdmS := fun _ => True)
    (AdmE := fun _ => True) (zkRO_one _ _ _ _ _) zero_le_one (zkRO_one _ _ _ _ _) zero_le_one
    (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (weakSEN_one _ _ _ _ _ _ _ _)
    (fun _ _ => trivial)

/-- `noTheftN_lean`'s hypotheses hold for the trivial adversary with the Lean prover; the hops'
budgets are discharged. -/
example [NeZero U] (q3 q5 qE : ℕ) :=
  noTheftN_lean (R := Blk → Blk) (thiefNR _ U M _ _) (fun _ _ _ => false) (fun _ _ _ => false)
    extNR (q3 := q3) (q5 := q5) (qE := qE) (AdmE := fun _ => True)
    (fun i _ ω τ => budget_of_eq (distPI_thiefNR _ _ _ _ _ _ i ω τ))
    (fun i _ ω τ => budget_of_eq (distPS_thiefNR _ _ _ _ _ _ i ω τ))
    (weakSEN_one _ _ _ _ _ _ _ _) (fun _ _ => trivial)

/-- `noTheftN_lean_reads`'s hypotheses hold for the trivial adversary: the budgets of a constant
last stage and a constant extractor. -/
example [NeZero U] :=
  noTheftN_lean_reads (R := Blk → Blk) (thiefNR _ U M _ _) extNR (AdmE := fun _ => True)
    (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetN.const _) (fun _ _ => StageBudgetN.const _)
    (weakSEN_one _ _ _ _ _ _ _ _) fun _ _ => trivial

/-- `noTheftN_lean_plain`'s hypotheses hold for the trivial adversary and a constant extractor. -/
example [NeZero U] :=
  noTheftN_lean_plain (R := Blk → Blk) (thiefNR _ U M _ _) (e := fun _ _ _ _ => wit0)
    (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetN.const _) (fun _ _ => StageBudgetN.const _)
    (plainSEN_one _ _ _ _ _ _) (εh := fun _ => 1) (fun i => slotEvN_one _ i _ _ _ _ _)

/-- `noTheftN_leanX_hit`'s hypotheses hold for the trivial adversary (no chain-table queries)
and a constant extractor, with `L = Lmin`. -/
example [NeZero U] (M' : ℕ) :=
  noTheftN_leanX_hit (R := Blk → Blk) (L := Hit.Rata.Lmin) (M' := M') (thiefNR _ U M _ _) le_rfl
    (e := fun _ _ _ _ => wit0) (Adm := Hit.AdmHitN 0 0 0) (Adm₀ := fun _ => True) (ε₀ := 1)
    (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetNX.const _) (fun _ _ => StageBudgetNX.const _)
    (plainSEN_one _ _ _ _ _ _) (fun _ _ => Hit.admHitN_const _) (fun _ h => h)
    fun _ _ _ _ => trivial

/-- **Change tokens chain.** In a spend slot whose request is sent (`xtE` gives the statement
`x`, the entry carries a spend proof) and whose response the Client accepts, the spending
Client's token becomes the change token: made from this slot's coins (`src = n`), with the
change value `t'` and the adversary's refund and signature. -/
theorem change_chains (A : ThiefN Z U M G S) (p : Ratatouille.Pub) (σ : St Z U) (hn : ¬ σ.n < U)
    (x : SpendInstance) (t' : Credits) (hx : xtE A p σ = .ok (.inr x, t')) (π : SpendProof Z)
    (hresp : uovEval A.pk (respSig (A.respondS σ.iss
        (σ.sp ++ [.ok (SpendReq.toBytes ⟨x.nf, x.d, x.cNext, π⟩)]))) =
      tag x.cNext (respRefund (A.respondS σ.iss
        (σ.sp ++ [.ok (SpendReq.toBytes ⟨x.nf, x.d, x.cNext, π⟩)])))) :
    (step A p σ (some (.inr x, .inr π))).cur (A.who σ) =
      some ⟨σ.n, t', respRefund (A.respondS σ.iss
          (σ.sp ++ [.ok (SpendReq.toBytes ⟨x.nf, x.d, x.cNext, π⟩)])),
        respSig (A.respondS σ.iss
          (σ.sp ++ [.ok (SpendReq.toBytes ⟨x.nf, x.d, x.cNext, π⟩)]))⟩ := by
  unfold step
  simp only [hn, ↓reduceDIte, Function.update_self, curS, hx, entS, cOf, hresp, ↓reduceIte]

/-- **A spend reveals the nullifier of the slot that made the current token**, and its change
commitment is made with the coins of its own slot, at the Client's context and the change
value. -/
theorem next_spend (A : ThiefN Z U M G S) (p : Ratatouille.Pub) (σ : St Z U) (hn : ¬ σ.n < U)
    (x : SpendInstance) (t' : Credits) (hx : xtE A p σ = .ok (.inr x, t')) :
    ∃ τ, σ.cur (A.who σ) = some τ ∧ x.nf = (p τ.src).1 ∧ x.d = A.amt σ ∧
      clientCheck τ.t τ.x (A.amt σ) = some t' ∧ x.cNext = (p σ.n).2 (A.ctx (A.who σ)) t' := by
  unfold xtE at hx
  simp only [hn, ↓reduceDIte] at hx
  cases hc : σ.cur (A.who σ) with
  | none => rw [hc] at hx; cases hx
  | some τ =>
    rw [hc] at hx
    simp only at hx
    split_ifs at hx
    cases hk : clientCheck τ.t τ.x (A.amt σ) with
    | none => rw [hk] at hx; cases hx
    | some t'' =>
      rw [hk] at hx
      cases hx
      exact ⟨τ, rfl, rfl, rfl, hk, rfl⟩

/-- **A replay is excluded** (F2): a spend whose statement is an honest spend statement of the
log is not fresh. -/
theorem replay_not_freshNR (A : ThiefN Z U M G S) (l : LogR Z) (q : SpendRequest Z) (c : Context)
    (x : Credits) (π : RP Z) (h : some (Sum.inr (opXS A.base q c), π) ∈ l) :
    ¬ FreshOpN A l (.spend q c x) :=
  fun hf => hf _ π h rfl

/-- **A changed request is in scope**: a spend whose amount differs from the amount of every
honest spend of the log is fresh. -/
theorem changed_freshNR (A : ThiefN Z U M G S) (l : LogR Z) (q : SpendRequest Z) (c : Context)
    (x : Credits) (hd : ∀ y π, some (Sum.inr y, π) ∈ l → y.d ≠ (SpendReq.parse q).d) :
    FreshOpN A l (.spend q c x) := by
  intro y π hy heq
  exact hd y π hy (by rw [← heq]; rfl)

/-- **`Adv^ow` is `1` for some inverter** in this model: `Com` is a fixed function, and the
inverter that picks an opening of the commitment at the zero context and `t = 0` always
succeeds. So `owAdvK` is an assumption on the explicit inverter of `noTheftN`. -/
theorem owAdvK_one :
    ∃ B : Nullifier → (Context → Credits → Commitment) → Unit → Context × Credits × Open4,
      owAdvK B = 1 := by
  refine ⟨fun nf K _ => (Vector.replicate 16 0, 0, (nf, Vector.replicate 16 0, 0,
    Classical.epsilon fun r => com nf (Vector.replicate 16 0) 0 r = K (Vector.replicate 16 0) 0)),
    ?_⟩
  unfold owAdvK
  rw [pr_congr (Q := fun _ => True) fun z => ⟨fun _ => trivial, fun _ => ?_⟩, pr_const]
  · simp
  · simp only [comOf, pubC]
    exact Classical.epsilon_spec (p := fun r => com (vec z.1.1) (Vector.replicate 16 0) 0 r =
      com (vec z.1.1) (Vector.replicate 16 0) 0 (vec z.1.2)) ⟨_, rfl⟩

end Rat

/-! ## Moussaka -/

section Mous

open VoleMole.Theft.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka
open VoleMole.Audit.TheftMany (thiefNM extNM)

variable {U M : ℕ}

/-- `noRedirectN_lean_reads`'s hypotheses hold for the trivial adversary. -/
example [NeZero U] :=
  noRedirectN_lean_reads (R := Blk → Blk) (thiefNM U M _ _) extNM (AdmE := fun _ => True)
    (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetN.const _) (fun _ => StageBudgetN.const _)
    (weakSEN_one _ _ _ _ _ _ _ _) fun _ => trivial

/-- `noRedirectN_lean_plain`'s hypotheses hold for the trivial adversary and a constant
extractor. -/
example [NeZero U] :=
  noRedirectN_lean_plain (R := Blk → Blk) (thiefNM U M _ _) (e := fun _ _ _ _ => [])
    (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetN.const _) (fun _ => StageBudgetN.const _)
    (plainSEN_one _ _ _ _ _ _) (εh := fun _ => 1) (fun i => slotEvN_one _ i _ _ _ _ _)

end Mous

/-! ## Unbound Moussaka -/

section Unb

open VoleMole.Theft.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
  VoleMole.Privacy.MoussakaUnbound VoleMole.Audit.UnboundRest
open VoleMole.Audit.UnboundMany (thiefNU extNU)
open VoleMole.Spec.Moussaka (ctxBytes)

variable {U M : ℕ}

/-- `nmUN_lean_reads`'s hypotheses hold for the trivial adversary. -/
example [NeZero U] (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts) :=
  nmUN_lean_reads (R := Blk → Blk) (thiefNU U M _ _) extNU (AdmE := fun _ => True)
    (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetN.const _) (fun _ => StageBudgetN.const _)
    (weakSEN_one _ _ _ _ _ _ _ _) (fun _ => trivial) pts hpts (fun _ _ => prf1Adv_le_one _ _)

/-- `nmUN_lean_plain`'s hypotheses hold for the trivial adversary and a constant extractor. -/
example [NeZero U] (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts) :=
  nmUN_lean_plain (R := Blk → Blk) (thiefNU U M _ _) (e := fun _ _ _ _ => [])
    (a3 := 0) (a5 := 0) (aE := 0) (x3 := 0) (x5 := 0) (xE := 0)
    (fun _ _ => StageBudgetN.const _) (fun _ => StageBudgetN.const _)
    (plainSEN_one _ _ _ _ _ _) (εh := fun _ => 1) (fun i => slotEvN_one _ i _ _ _ _ _) pts hpts
    (fun _ _ => prf1Adv_le_one _ _)

end Unb

/-! ## `WeakSEN` at `N = 2` and `WeakSE2` -/

/-- `weakSE2_of_weakSEN` applies: its hypothesis holds with error `1`, for any two simulators. -/
example {I₁ I₂ P₁ P₂ C₁ C₂ G S Out W : Type} [Fintype C₁] [Nonempty C₁] [Fintype C₂] [Nonempty C₂]
    [Fintype G] [Fintype S] (sim₁ : I₁ → C₁ → Option P₁) (prog₁ : I₁ → C₁ → S → S)
    (sim₂ : I₂ → C₂ → Option P₂) (prog₂ : I₂ → C₂ → S → S) (Acc : Out → S → Prop)
    (Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop) (Rel : Out → W → Prop)
    (ext : Option (I₁ × P₁) → Option (I₂ × P₂) → (G → G → S → Out) → G → G → S → W)
    (Adm : (G → G → S → Out) → Prop) : WeakSE2 sim₁ prog₁ sim₂ prog₂ Acc Fresh Rel ext Adm 1 :=
  weakSE2_of_weakSEN (weakSEN_one _ _ _ _ _ _ _ _)

end VoleMole.Audit.TheftManyR
