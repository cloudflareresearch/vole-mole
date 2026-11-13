import VoleMole.Theft.MoussakaManyLean
import VoleMole.Audit.Theft
import VoleMole.Audit.UnboundRest

/-!
# Audit of Moussaka Theorem 3 for `U` tokens and `M` redemptions (`Theft/MoussakaMany.lean`)

* **The hypotheses can hold together.** `noRedirectN` is instantiated for a trivial adversary
  with any provers and simulators (zero knowledge and `WeakSEN` with error `1`), and
  `noRedirectN_lean` with the executable Lean prover (function rows), the hops' budgets
  discharged (`budget_of_eq`), for every `U ≥ 1` and `M`. This checks that the hypotheses are
  consistent, not that they are small.
* **The event is the intended one.** An honest redemption statement of the log replayed is not
  fresh (`replay_not_freshN`); a redemption whose digest differs from the digest of every honest
  redemption is fresh (`redirect_freshN`).

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.TheftMany

open VoleMole.Privacy VoleMole.Theft VoleMole.Theft.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka
  VoleMole.ZK.Sim VoleMole.Privacy.Moussaka
open VoleMole.Audit.Theft (budget_of_eq set0)
open VoleMole.Audit.UnboundRest (zkRO_one)

variable {G S : Type} {U M : ℕ}

/-- **A trivial adversary** against `U ≥ 1` tokens: constant choices, always token `0`, and an
empty redemption request as its output. -/
def thiefNM (U M : ℕ) [NeZero U] (G S : Type) : ThiefN U M G S :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ => ⟨[], fun _ => 0⟩, fun _ _ _ => 0, fun _ _ => (0, set0, []),
    fun _ _ _ _ => .redeem set0 [] [] [] []⟩

/-- A constant extractor. -/
def extNM : ExtN U M G S := fun _ _ _ _ => []

theorem distPN_thiefNM [NeZero U] [Nonempty G] {CI CR : Type} [Nonempty CI] [Nonempty CR]
    (PI : Bytes → IssueInstance → Bytes → G → S → Bytes)
    (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)
    (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → S → S)
    (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → S → S)
    (i : Fin (U + M)) (ω : SecN U) (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (CI × CR) G) :
    distPN (thiefNM U M G S) PI PR simI progI simR progR (fun _ _ _ => false) (fun _ _ _ => false)
      extNM i ω τ = fun _ _ _ => False := by
  funext p g u
  simp [distPN, distN, contN, BadN, accN, Moussaka.AccOp, opN, thiefNM]

/-- `noRedirectN`'s hypotheses hold together for the trivial adversary, with any provers and
simulators, for every `U ≥ 1` and `M`. -/
example [NeZero U] [Fintype G] [Nonempty G] [Fintype S] [Nonempty S]
    (PI : Bytes → IssueInstance → Bytes → G → S → Bytes)
    (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)
    (simI : IssueInstance → Coins 1 → Bytes) (progI : IssueInstance → Coins 1 → S → S)
    (simR : RedeemInstance → Coins 1 → Bytes) (progR : RedeemInstance → Coins 1 → S → S) :=
  noRedirectN (thiefNM U M G S) PI PR simI progI simR progR (fun _ _ _ => false)
    (fun _ _ _ => false) extNM (AdmI := fun _ => True) (AdmR := fun _ => True)
    (AdmE := fun _ => True) (zkRO_one _ _ _ _ _) zero_le_one (zkRO_one _ _ _ _ _) zero_le_one
    (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (weakSEN_one _ _ _ _ _ _ _ _)
    (fun _ => trivial)

/-- `noRedirectN_lean`'s hypotheses hold for the trivial adversary with the Lean prover; the
hops' budgets are discharged. -/
example [NeZero U] (q3 q5 qE : ℕ) :=
  noRedirectN_lean (R := Blk → Blk) (thiefNM U M _ _) (fun _ _ _ => false) (fun _ _ _ => false)
    extNM (q3 := q3) (q5 := q5) (qE := qE) (AdmE := fun _ => True)
    (fun i _ ω τ => budget_of_eq (distPN_thiefNM _ _ _ _ _ _ i ω τ))
    (fun i _ ω τ => budget_of_eq (distPN_thiefNM _ _ _ _ _ _ i ω τ))
    (weakSEN_one _ _ _ _ _ _ _ _) (fun _ => trivial)

/-- **A replay is excluded**: an operation whose statement is an honest redemption statement of
the log is not fresh. -/
theorem replay_not_freshN (l : Moussaka.Log) (S' : AnchorSet) (req ci cr cd π : Bytes)
    (h : some (Sum.inr (stOfR S' req ci cr cd), π) ∈ l) :
    ¬ Moussaka.FreshOpN l (.redeem S' req ci cr cd) :=
  fun hf => hf _ π h rfl

/-- **A redirect is in scope**: a redemption whose digest differs from the digest of every
honest redemption is fresh. -/
theorem redirect_freshN (l : Moussaka.Log) (S' : AnchorSet) (req ci cr cd : Bytes)
    (hcd : ∀ x π, some (Sum.inr x, π) ∈ l → x.challengeDigest ≠ cd) :
    Moussaka.FreshOpN l (.redeem S' req ci cr cd) := by
  intro x π hx heq
  exact hcd x π hx (by rw [← heq]; rfl)

end VoleMole.Audit.TheftMany
