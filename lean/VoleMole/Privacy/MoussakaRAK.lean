import VoleMole.Privacy.MoussakaRA
import VoleMole.Privacy.PermRA

/-!
# Moussaka with a key stage that reads the tables

In `Privacy/MoussakaRA.lean` the adversary's interaction reads the tables, but its contexts and
the challenge Clients' issuing keys (`AdversaryRA.ctxIss`, `ctxRed`, `pk`) are constants. Here
they are chosen by a **key stage** that reads the tables first (`AdversaryRAK`): `setup` reads the
four `H₃` slices and the shared tables (`H₂³`, `H₅`, the cipher) within a budget, consistently
(`KBudget`, per slice position as `IBudget`), and outputs a state `σ`; the rest of the adversary
(contexts, keys, interaction, guess) is the table-reading adversary `adv σ` of `MoussakaRA`.

## The game

`realGameRAK`: the setup on the slices and the original tables (nothing is programmed before
the challenge), then `realGameRA` of `adv σ`. Every hybrid is `gameRA` of `adv σ` with `σ` read
off the slices and the original tables (`gameRAK`).

## The hybrids

As in `anonymityRA`, but the **issuance statements are now adaptive** (the commitment and the
instance contain the contexts, which `σ` fixes): both issuance hops are `hop_roA` with
`ZeroKnowledgeROA` for the setup reader (`εAd` at the key stage's budget `(k₃, k₂, k₅, k_E)`).
Issuance `1`'s collision term (`deltaI1K`) is still `≤ noHitProb + 2⁻¹⁰²⁴`: issuance `0`'s
simulator coins are independent of the setup, of issuance `1`'s tape and of the tables
(`deltaI1K_le`). The redemption hops read the transcript through the setup and the two issuance
programmings (`SReads.bind`: `(k₃ + i₃, k₂ + i₂, k₅ + i₅ + 624, k_E + i_E + 9214)`); their
collision terms are `pr_collide_adaptive` at that budget. The setup's reads before the challenge
may meet the blocks the simulators program later: that is the `H₂³` term of `εAd`
(`2·k₂·2⁻¹⁰²⁴` for the simulated block plus a second zero-knowledge application for the real one),
in the issuance and the redemption hops. The simulated world is `simGameRA` of `adv σ`, a
function of the commitments, the nullifiers, the coins, the slices and the tables, and hiding
(for the reductions at `σ`) finishes as before.

**`anonymityRAK_lean_num`**:

    4·εAd(9; i₃ + q₃, q₅ + i₅ + 1872, q_E + i_E + 13821; k₃, k₂, k₅, k_E)
      + 4·εAd(9; q₃, q₅ + 1248, q_E + 13821; k₃ + i₃, k₂ + i₂, k₅ + i₅ + 624, k_E + i_E + 9214)
      + 4·((k₃ + i₃)·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607; k₅ + i₅ + 624, k_E + i_E + 9214))
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

With `k = 0` this is `anonymityRA_lean_num` up to `4·2⁻¹²⁸` (`εAd` at a zero budget is
`εRO + 2⁻¹²⁸`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [Inhabited R]

/-! ## The model -/

/-- **The colluding adversary with a key stage that reads the tables**: `setup` reads the four
`H₃` slices and the shared tables and outputs a state `σ`; the contexts, the challenge Clients'
keys, the interaction and the guess are those of the table-reading adversary `adv σ`. -/
structure AdversaryRAK (R : Type) (Sg : Type) where
  setup : Slices → ShM R → Sg
  adv : Sg → AdversaryRA R

namespace AdversaryRAK

variable {Sg : Type} (A : AdversaryRAK R Sg)

/-- **The key stage's budget**: as a function of each proof's slice and the shared tables (the
other slices fixed), the setup reads at most `k₃` slice keys, `k₂` `H₂³` keys, `k₅` `H₅` keys and
`k_E` cipher keys, consistently. -/
structure KBudget (k3 k2 k5 kE : ℕ) : Prop where
  s0 : ∀ (g₁ gL gR : Tab3), SReads pI (fun t : Tb R pI => A.setup ((t.1, g₁), (gL, gR)) t.2) k3 k2 k5 kE
  s1 : ∀ (g₀ gL gR : Tab3), SReads pI (fun t : Tb R pI => A.setup ((g₀, t.1), (gL, gR)) t.2) k3 k2 k5 kE
  sL : ∀ (g₀ g₁ gR : Tab3), SReads pR (fun t : Tb R pR => A.setup ((g₀, g₁), (t.1, gR)) t.2) k3 k2 k5 kE
  sR : ∀ (g₀ g₁ gL : Tab3), SReads pR (fun t : Tb R pR => A.setup ((g₀, g₁), (gL, t.1)) t.2) k3 k2 k5 kE

/-- **The interaction's budget**, at every state. -/
def IBudget (i3 i2 i5 iE : ℕ) : Prop := ∀ σ, (A.adv σ).IBudget i3 i2 i5 iE

/-- **The guess's budget**, at every state. -/
def GBudget (q3 q5 qE : ℕ) : Prop := ∀ σ, (A.adv σ).GBudget q3 q5 qE

end AdversaryRAK

variable {Sg : Type} (A : AdversaryRAK R Sg) (idx : AnchorSet → UOVKey → ℕ)

/-- The four slices of a game tape (every slot's slice is the last component of its tape). -/
def slK {C₀ C₁ D₂ D₃ : Type}
    (x : ((NR × (C₀ × Tab3)) × (NR × (C₁ × Tab3))) × ((D₂ × Tab3) × (D₃ × Tab3))) : Slices :=
  ((x.1.1.2.2, x.1.2.2.2), (x.2.1.2, x.2.2.2))

/-- **The game with a key stage**: the state read off the slices and the original tables, then
`gameRA` of `adv σ` with the slots drawn at `σ`. -/
def gameRAK {C₀ C₁ D₂ D₃ : Type} (b : Bool) (g₀ : Sg → NR × (C₀ × Tab3) → IssSlot R)
    (g₁ : Sg → NR × (C₁ × Tab3) → IssSlot R) (gL : Sg → D₂ × Tab3 → RedSlot R)
    (gR : Sg → D₃ × Tab3 → RedSlot R)
    (x : (((NR × (C₀ × Tab3)) × (NR × (C₁ × Tab3))) × ((D₂ × Tab3) × (D₃ × Tab3))) × ShM R) :
    Prop :=
  gameRA (A.adv (A.setup (slK x.1) x.2)) idx b (g₀ (A.setup (slK x.1) x.2))
    (g₁ (A.setup (slK x.1) x.2)) (gL (A.setup (slK x.1) x.2)) (gR (A.setup (slK x.1) x.2)) x

/-- **The real game with a key stage**: the setup reads the tables, then the spec's protocol with
every proof computed on the shared uniform tables, the adversary's interaction and guess reading
them. -/
def realGameRAK (PI : ProverRO R IssueInstance) (PR : ProverRO R RedeemInstance) (b : Bool) :
    ((TIr × TIr) × (TRr × TRr)) × ShM R → Prop :=
  gameRAK A idx b (fun σ => issRealRO (A.adv σ).ctxRO PI) (fun σ => issRealRO (A.adv σ).ctxRO PI)
    (fun σ => redRealRO (A.adv σ).ctxRO PR) (fun σ => redRealRO (A.adv σ).ctxRO PR)

/-- At every tape the real game is `realGameRA` of the adversary at the state read off it. -/
lemma realGameRAK_iff (PI : ProverRO R IssueInstance) (PR : ProverRO R RedeemInstance) (b : Bool)
    (x : ((TIr × TIr) × (TRr × TRr)) × ShM R) :
    realGameRAK A idx PI PR b x ↔ realGameRA (A.adv (A.setup (slK x.1) x.2)) idx PI PR b x :=
  Iff.rfl

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (simR : RedeemInstance → CR → Bytes)
  (progI : IssueInstance → CI → ShM R → ShM R) (progR : RedeemInstance → CR → ShM R → ShM R)

/-- The game with all four proofs simulated. -/
def simGameRAK (b : Bool) : ((TIs CI × TIs CI) × (TRs CR × TRs CR)) × ShM R → Prop :=
  gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
    (fun σ => issSimRO (A.adv σ).ctxRO simI progI) (fun σ => redSimRO (A.adv σ).ctxRO simR progR)
    (fun σ => redSimRO (A.adv σ).ctxRO simR progR)

/-- The state of the hiding tape: read off its slices and tables. -/
abbrev σOf (c : ((CI × CI) × (CR × CR)) × (Slices × ShM R)) : Sg := A.setup c.2.1 c.2.2

/-- The game after the hiding hop, at the state read off the slices and tables. -/
def idealGameRAK (b : Bool)
    (x : (HTape × (Coins nfBytes × Coins nfBytes)) × (((CI × CI) × (CR × CR)) × (Slices × ShM R))) :
    Prop :=
  idealGameRA (A.adv (σOf A x.2)) idx simI simR progI progR b x

theorem hiding_hopRAK [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (b : Bool) {εhide : ℝ}
    (hhide : ∀ c, hidingAdv (A.adv (σOf A c)).ctxRO.base.ci (A.adv (σOf A c)).ctxRO.base.cr
      (reductionRA (A.adv (σOf A c)) idx simI simR progI progR b c) ≤ εhide) :
    |pr _ (simGameRAK A idx simI simR progI progR b) -
      pr _ (idealGameRAK A idx simI simR progI progR b)| ≤ εhide := by
  rw [← pr_equiv regroupRO.symm (simGameRAK A idx simI simR progI progR b),
    pr_congr (P := fun y => simGameRAK A idx simI simR progI progR b (regroupRO.symm y))
      fun y => simGameRA_iff (A.adv (σOf A y.2)) idx simI simR progI progR b (regroupRO.symm y)]
  exact abs_pr_prod_sub_le' _ _ fun c => hhide c

/-- **After the hiding hop the worlds coincide**, tables included. -/
theorem idealGameRAK_eq [Fintype CI] [Fintype CR] :
    pr _ (idealGameRAK A idx simI simR progI progR false) =
      pr _ (idealGameRAK A idx simI simR progI progR true) := by
  rw [← pr_equiv swapNRO]
  exact pr_congr fun x => Iff.rfl

/-! ## The issuance hops: adaptive statements -/

section HopsI

variable {A idx}
variable (PI : ProverRO R IssueInstance) (PR : ProverRO R RedeemInstance)

/-- The state in hop 0, read off issuance `0`'s slice and the shared tables. -/
def Sx0 (γ : NR × (TIr × (TRr × TRr))) (t : Tab3 × ShM R) : Sg :=
  A.setup ((t.1, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2)) t.2

/-- The state in hop 1, read off issuance `1`'s slice and the shared tables. -/
def Sx1 (γ : TIs CI × (NR × (TRr × TRr))) (t : Tab3 × ShM R) : Sg :=
  A.setup ((γ.1.2.2, t.1), (γ.2.2.1.2, γ.2.2.2.2)) t.2

/-- The tape regrouped around issuance `0`'s proof, for `hop_roA`. -/
def eqv0K {N P G T₁ T₂ S : Type} :
    (N × (T₁ × T₂)) × (P × (G × S)) ≃ (((N × (P × G)) × T₁) × T₂) × S where
  toFun z := ((((z.1.1, (z.2.1, z.2.2.1)), z.1.2.1), z.1.2.2), z.2.2.2)
  invFun y := ((y.1.1.1.1, (y.1.1.2, y.1.2)), (y.1.1.1.2.1, (y.1.1.1.2.2, y.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The tape regrouped around issuance `1`'s proof, for `hop_roA`. -/
def eqv1K {T₀ N P G T₂ S : Type} :
    (T₀ × (N × T₂)) × (P × (G × S)) ≃ ((T₀ × (N × (P × G))) × T₂) × S where
  toFun z := (((z.1.1, (z.1.2.1, (z.2.1, z.2.2.1))), z.1.2.2), z.2.2.2)
  invFun y := ((y.1.1.1, (y.1.1.2.1, y.1.2)), (y.1.1.2.2.1, (y.1.1.2.2.2, y.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The collision term of hop 1**: issuance `1`'s real proof (of the statement at the state
read off the tables) on the tables programmed by issuance `0`'s simulation differs from the proof
on the original tables. -/
noncomputable def deltaI1K [Fintype CI] : ℝ :=
  pr ((TIs CI × (NR × (TRr × TRr))) × (Coins proveSeedBytes × (Tab3 × ShM R))) fun z =>
    PI (wIOf (A.adv (Sx1 (A := A) z.1 z.2.2)).ctxRO z.1.2.1)
        (xIOf (A.adv (Sx1 (A := A) z.1 z.2.2)).ctxRO z.1.2.1) (List.ofFn z.2.1) z.2.2.1
        (progI (xIOf (A.adv (Sx1 (A := A) z.1 z.2.2)).ctxRO z.1.1.1) z.1.1.2.1 z.2.2.2) ≠
      PI (wIOf (A.adv (Sx1 (A := A) z.1 z.2.2)).ctxRO z.1.2.1)
        (xIOf (A.adv (Sx1 (A := A) z.1 z.2.2)).ctxRO z.1.2.1) (List.ofFn z.2.1) z.2.2.1 z.2.2.2

variable {q3 q5 qE i3 i2 i5 iE k3 k2 k5 kE r5 rE m5 mE : ℕ}

theorem hop0RAK [Fintype CI] [Nonempty CI] (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    {AdmS : (X : Type) → (Tab3 × ShM R → X) → Prop}
    (hS : ∀ γ : NR × (TIr × (TRr × TRr)), AdmS Sg (Sx0 (A := A) γ))
    {ε : ℝ} (hIzk : ZeroKnowledgeROA IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI AdmS
      (Budget pI (i3 + q3) (r5 + (i5 + (r5 + r5 + q5))) (rE + (iE + (rE + rE + qE)))) ε)
    (b : Bool) :
    |pr _ (gameRAK A idx b (fun σ => issRealRO (A.adv σ).ctxRO PI)
        (fun σ => issRealRO (A.adv σ).ctxRO PI) (fun σ => redRealRO (A.adv σ).ctxRO PR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR)) -
      pr _ (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
        (fun σ => issRealRO (A.adv σ).ctxRO PI) (fun σ => redRealRO (A.adv σ).ctxRO PR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR))| ≤ ε := by
  have h := hop_roA (Γ := NR × (TIr × (TRr × TRr))) (ρ := Coins proveSeedBytes) (G := Tab3)
    (C := CI) (S := ShM R) (Sx0 (A := A))
    (fun γ σ ρ g s => PI (wIOf (A.adv σ).ctxRO γ.1) (xIOf (A.adv σ).ctxRO γ.1) (List.ofFn ρ) g s)
    (fun γ σ c => simI (xIOf (A.adv σ).ctxRO γ.1) c) (fun γ σ c => progI (xIOf (A.adv σ).ctxRO γ.1) c)
    (fun _ _ s => s) (fun γ σ => F0A (A := A.adv σ) (idx := idx) PI PR b γ) (ε := ε) fun γ => ?_
  · have hδ : pr ((NR × (TIr × (TRr × TRr))) × (Coins proveSeedBytes × (Tab3 × ShM R))) (fun z =>
        PI (wIOf (A.adv (Sx0 (A := A) z.1 z.2.2)).ctxRO z.1.1)
            (xIOf (A.adv (Sx0 (A := A) z.1 z.2.2)).ctxRO z.1.1) (List.ofFn z.2.1) z.2.2.1 z.2.2.2 ≠
          PI (wIOf (A.adv (Sx0 (A := A) z.1 z.2.2)).ctxRO z.1.1)
            (xIOf (A.adv (Sx0 (A := A) z.1 z.2.2)).ctxRO z.1.1) (List.ofFn z.2.1) z.2.2.1 z.2.2.2) =
        0 := by
      rw [pr_congr (Q := fun _ => False) fun z => by simp, pr_const]
      simp
    rw [hδ, add_zero] at h
    rw [← pr_equiv eqv0K (gameRAK A idx b (fun σ => issRealRO (A.adv σ).ctxRO PI)
        (fun σ => issRealRO (A.adv σ).ctxRO PI) (fun σ => redRealRO (A.adv σ).ctxRO PR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR)),
      ← pr_equiv eqv0K (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
        (fun σ => issRealRO (A.adv σ).ctxRO PI) (fun σ => redRealRO (A.adv σ).ctxRO PR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR))]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · have hz := hIzk Sg (Sx0 (A := A) γ)
      (fun σ => some (xIOf (A.adv σ).ctxRO γ.1, wIOf (A.adv σ).ctxRO γ.1)) (hS γ)
      (fun σ i w h => by
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact issueRelW_of _ γ.1) []
      (fun σ o g s => F0A (A := A.adv σ) (idx := idx) PI PR b γ o g s)
      fun σ => F0A_budget (A := A.adv σ) (PI := PI) (PR := PR) (hA σ) (hI σ) hPI5 hPIE hPR5 hPRE b γ
    exact hz

theorem hop1RAK [Fintype CI] [Nonempty CI] (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE)
    {AdmS : (X : Type) → (Tab3 × ShM R → X) → Prop}
    (hS : ∀ γ : TIs CI × (NR × (TRr × TRr)), AdmS Sg (Sx1 (A := A) γ))
    {ε : ℝ} (hIzk : ZeroKnowledgeROA IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI AdmS
      (Budget pI (i3 + q3) (i5 + (r5 + r5 + q5) + m5) (iE + (rE + rE + qE) + mE)) ε) (b : Bool) :
    |pr _ (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
        (fun σ => issRealRO (A.adv σ).ctxRO PI) (fun σ => redRealRO (A.adv σ).ctxRO PR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR)) -
      pr _ (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
        (fun σ => issSimRO (A.adv σ).ctxRO simI progI) (fun σ => redRealRO (A.adv σ).ctxRO PR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR))| ≤
      ε + deltaI1K (A := A) progI PI := by
  have h := hop_roA (Γ := TIs CI × (NR × (TRr × TRr))) (ρ := Coins proveSeedBytes) (G := Tab3)
    (C := CI) (S := ShM R) (Sx1 (A := A))
    (fun γ σ ρ g s => PI (wIOf (A.adv σ).ctxRO γ.2.1) (xIOf (A.adv σ).ctxRO γ.2.1) (List.ofFn ρ) g s)
    (fun γ σ c => simI (xIOf (A.adv σ).ctxRO γ.2.1) c)
    (fun γ σ c => progI (xIOf (A.adv σ).ctxRO γ.2.1) c)
    (fun γ σ s => progI (xIOf (A.adv σ).ctxRO γ.1.1) γ.1.2.1 s)
    (fun γ σ => F1A (A := A.adv σ) (idx := idx) simI PR b γ) (ε := ε) fun γ => ?_
  · rw [← pr_equiv eqv1K (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
        (fun σ => issRealRO (A.adv σ).ctxRO PI) (fun σ => redRealRO (A.adv σ).ctxRO PR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR)),
      ← pr_equiv eqv1K (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
        (fun σ => issSimRO (A.adv σ).ctxRO simI progI) (fun σ => redRealRO (A.adv σ).ctxRO PR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR))]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · exact hIzk Sg (Sx1 (A := A) γ)
      (fun σ => some (xIOf (A.adv σ).ctxRO γ.2.1, wIOf (A.adv σ).ctxRO γ.2.1)) (hS γ)
      (fun σ i w h => by
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact issueRelW_of _ γ.2.1) []
      (fun σ o g s => F1A (A := A.adv σ) (idx := idx) simI PR b γ o g
        (progI (xIOf (A.adv σ).ctxRO γ.1.1) γ.1.2.1 s))
      fun σ => F1A_budget (A := A.adv σ) (simI := simI) (PR := PR) (progI := progI) (hA σ) (hI σ)
        hPR5 hPRE hpI b γ

end HopsI

/-! ## The redemption hops: the transcript read through the setup -/

section HopsR

variable {A idx}
variable (PR : ProverRO R RedeemInstance)

/-- The state in a redemption hop, read off the hop's slice and the shared tables. -/
abbrev σL (γ : ΓL CI) (t : Tab3 × ShM R) : Sg := A.setup ((γ.1.1.2.2, γ.1.2.2.2), (t.1, γ.2.2)) t.2

/-- **The state and the transcript in hop L**, read off the left redemption's slice and the shared
tables: the setup on the original tables, the transcript through the issuance programmings. -/
def SxLK (γ : ΓL CI) (t : Tab3 × ShM R) : Sg × Trans :=
  (σL (A := A) γ t, SxL (A := A.adv (σL (A := A) γ t)) simI progI γ t)

/-- **The collision term of hop L**: the left redemption's real proof (of the statement read off
the tables through the setup) on the tables programmed by the issuance simulations differs from
the one on the original tables. -/
noncomputable def deltaLAK [Fintype CI] (b : Bool) : ℝ :=
  pr (ΓL CI × (Coins proveSeedBytes × (Tab3 × ShM R))) fun z =>
    PA (A := A.adv (SxLK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI PR b false z.1
        (SxLK (A := A) simI progI z.1 z.2.2).2 z.2.1 z.2.2.1
        (PIOf (A.adv (SxLK (A := A) simI progI z.1 z.2.2).1).ctxRO progI z.1 z.2.2.2) ≠
      PA (A := A.adv (SxLK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI PR b false z.1
        (SxLK (A := A) simI progI z.1 z.2.2).2 z.2.1 z.2.2.1 z.2.2.2

variable {q3 q5 qE i3 i2 i5 iE k3 k2 k5 kE r5 rE m5 mE : ℕ}

theorem hopLRAK [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (hA : A.GBudget q3 q5 qE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE)
    {AdmS : (X : Type) → (Tab3 × ShM R → X) → Prop}
    (hS : ∀ γ : ΓL CI, AdmS (Sg × Trans) (SxLK (A := A) simI progI γ))
    {ε : ℝ} (hR : ZeroKnowledgeROA RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmS
      (Budget pR q3 (0 + r5 + q5 + (m5 + m5)) (0 + rE + qE + (mE + mE))) ε) (b : Bool) :
    |pr _ (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
        (fun σ => issSimRO (A.adv σ).ctxRO simI progI) (fun σ => redRealRO (A.adv σ).ctxRO PR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR)) -
      pr _ (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
        (fun σ => issSimRO (A.adv σ).ctxRO simI progI) (fun σ => redSimRO (A.adv σ).ctxRO simR progR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR))| ≤
      ε + deltaLAK (A := A) (idx := idx) (simI := simI) (progI := progI) (PR := PR) b := by
  have h := hop_roA (Γ := ΓL CI) (ρ := Coins proveSeedBytes) (G := Tab3) (C := CR) (S := ShM R)
    (SxLK (A := A) simI progI) (fun γ x => PA (A := A.adv x.1) (idx := idx) simI PR b false γ x.2)
    (fun γ x => SmA (A := A.adv x.1) (idx := idx) simI simR b false γ x.2)
    (fun γ x => progA (A := A.adv x.1) (idx := idx) simI progR b false γ x.2)
    (fun γ x s => PIOf (A.adv x.1).ctxRO progI γ s)
    (fun γ x => FLA (A := A.adv x.1) (idx := idx) simI PR b γ x.2) (ε := ε) fun γ => ?_
  · -- From the hop to the games.
    let e : (((TIs CI × TIs CI) × ((Coins proveSeedBytes × Tab3) × TRr)) × ShM R) ≃
        (ΓL CI × (Coins proveSeedBytes × (Tab3 × ShM R))) :=
      { toFun := fun z => ((z.1.1, z.1.2.2), (z.1.2.1.1, (z.1.2.1.2, z.2)))
        invFun := fun z => ((z.1.1, ((z.2.1, z.2.2.1), z.1.2)), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let e' : (((TIs CI × TIs CI) × ((CR × Tab3) × TRr)) × ShM R) ≃
        (ΓL CI × (CR × (Tab3 × ShM R))) :=
      { toFun := fun z => ((z.1.1, z.1.2.2), (z.1.2.1.1, (z.1.2.1.2, z.2)))
        invFun := fun z => ((z.1.1, ((z.2.1, z.2.2.1), z.1.2)), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e1 : pr _ (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
        (fun σ => issSimRO (A.adv σ).ctxRO simI progI) (fun σ => redRealRO (A.adv σ).ctxRO PR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR)) =
        pr (ΓL CI × (Coins proveSeedBytes × (Tab3 × ShM R))) (fun z =>
          FLA (A := A.adv (SxLK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI PR b z.1
            (SxLK (A := A) simI progI z.1 z.2.2).2
            (PA (A := A.adv (SxLK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI PR b false z.1
              (SxLK (A := A) simI progI z.1 z.2.2).2 z.2.1 z.2.2.1
              (PIOf (A.adv (SxLK (A := A) simI progI z.1 z.2.2).1).ctxRO progI z.1 z.2.2.2)) z.2.2.1
            (PIOf (A.adv (SxLK (A := A) simI progI z.1 z.2.2).1).ctxRO progI z.1 z.2.2.2)) := by
      rw [← pr_equiv e.symm]
      refine pr_congr fun z => ?_
      show FLA (A := A.adv (σL (A := A) z.1 z.2.2)) (idx := idx) simI PR b z.1
          (SxL (A := A.adv (σL (A := A) z.1 z.2.2)) simI progI z.1 z.2.2)
          ((redRealRO (A.adv (σL (A := A) z.1 z.2.2)).ctxRO PR (z.2.1, z.2.2.1)).out
            (ptA (A := A.adv (σL (A := A) z.1 z.2.2)) (idx := idx) simI b z.1
              (SxL (A := A.adv (σL (A := A) z.1 z.2.2)) simI progI z.1 z.2.2) false)
            (PIOf (A.adv (σL (A := A) z.1 z.2.2)).ctxRO progI z.1 z.2.2.2)) z.2.2.1
          (PIOf (A.adv (σL (A := A) z.1 z.2.2)).ctxRO progI z.1 z.2.2.2) ↔ _
      unfold PA
      split_ifs with hok
      · exact Iff.rfl
      · exact postRO_not_ok (Bool.of_not_eq_true hok) _ _ _ _ _ _
    have e2 : pr _ (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
        (fun σ => issSimRO (A.adv σ).ctxRO simI progI) (fun σ => redSimRO (A.adv σ).ctxRO simR progR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR)) =
        pr (ΓL CI × (CR × (Tab3 × ShM R))) (fun z =>
          FLA (A := A.adv (SxLK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI PR b z.1
            (SxLK (A := A) simI progI z.1 z.2.2).2
            (SmA (A := A.adv (SxLK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI simR b false z.1
              (SxLK (A := A) simI progI z.1 z.2.2).2 z.2.1)
            z.2.2.1 (PIOf (A.adv (SxLK (A := A) simI progI z.1 z.2.2).1).ctxRO progI z.1
              (progA (A := A.adv (SxLK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI progR b false
                z.1 (SxLK (A := A) simI progI z.1 z.2.2).2 z.2.1 z.2.2.2))) := by
      rw [← pr_equiv e'.symm]
      exact pr_congr fun z => Iff.rfl
    rw [e1, e2]
    exact h
  · -- The zero-knowledge step, from `ZeroKnowledgeROA`.
    have hz := hR (Sg × Trans) (SxLK (A := A) simI progI γ)
      (fun x => stwA (A := A.adv x.1) (idx := idx) simI b false γ x.2)
      (hS γ) (fun x => stwA_rel (A := A.adv x.1) (idx := idx) simI b false γ x.2) []
      (fun x o g s => FLA (A := A.adv x.1) (idx := idx) simI PR b γ x.2
        (.ok ((ptA (A := A.adv x.1) (idx := idx) simI b γ x.2 false).tok.nf ++ o)) g
        (PIOf (A.adv x.1).ctxRO progI γ s))
      fun x => ⟨fun o s => (hA x.1 x.2).h3L _ _ _ _ _ _ _,
        fun o g => (rd5_postRO (A := (A.adv x.1).fixT x.2) (idx := idx) (hA x.1 x.2) _ _ (Rd5.const _)
          (rd5_redReal hPR5 _ _) _).comp_prog ((hpI _ _).comp (hpI _ _)),
        fun o g => (rdE_postRO (A := (A.adv x.1).fixT x.2) (idx := idx) (hA x.1 x.2) _ _ (RdE.const _)
          (rdE_redReal hPRE _ _) _).comp_prog ((hpI _ _).comp (hpI _ _))⟩
    refine le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun a => ?_)
      (pr_congr fun a => ?_)) hz
    · show FLA (A := A.adv (SxLK (A := A) simI progI γ a.2).1) (idx := idx) simI PR b γ
          (SxLK (A := A) simI progI γ a.2).2
          (PA (A := A.adv (SxLK (A := A) simI progI γ a.2).1) (idx := idx) simI PR b false γ
            (SxLK (A := A) simI progI γ a.2).2 a.1 a.2.1 a.2.2) a.2.1
          (PIOf (A.adv (SxLK (A := A) simI progI γ a.2).1).ctxRO progI γ a.2.2) ↔ _
      unfold PA outReal
      split_ifs with hok
      · simp only [stwA, hok, ↓reduceIte, Option.elim]
        rw [(redeem_factsA (A := A.adv (SxLK (A := A) simI progI γ a.2).1) (idx := idx) simI simR PR b
          false γ _ hok).2.1]
      · simp only [stwA, Bool.of_not_eq_true hok, Bool.false_eq_true, ↓reduceIte, Option.elim]
        exact postRO_not_ok (Bool.of_not_eq_true hok) _ _ _ _ _ _
    · show FLA (A := A.adv (SxLK (A := A) simI progI γ a.2).1) (idx := idx) simI PR b γ
          (SxLK (A := A) simI progI γ a.2).2
          (SmA (A := A.adv (SxLK (A := A) simI progI γ a.2).1) (idx := idx) simI simR b false γ
            (SxLK (A := A) simI progI γ a.2).2 a.1) a.2.1
          (PIOf (A.adv (SxLK (A := A) simI progI γ a.2).1).ctxRO progI γ
            (progA (A := A.adv (SxLK (A := A) simI progI γ a.2).1) (idx := idx) simI progR b false γ
              (SxLK (A := A) simI progI γ a.2).2 a.1 a.2.2)) ↔ _
      unfold SmA progA outSim progSim
      split_ifs with hok
      · simp only [stwA, hok, ↓reduceIte, Option.elim]
        rw [(redeem_factsA (A := A.adv (SxLK (A := A) simI progI γ a.2).1) (idx := idx) simI simR PR b
          false γ _ hok).2.2]
      · simp only [stwA, Bool.of_not_eq_true hok, Bool.false_eq_true, ↓reduceIte, Option.elim]
        exact postRO_not_ok (Bool.of_not_eq_true hok) _ _ _ _ _ _

/-- The state in hop R. -/
abbrev σR (γ : ΓR CI CR) (t : Tab3 × ShM R) : Sg := A.setup ((γ.1.1.2.2, γ.1.2.2.2), (γ.2.2, t.1)) t.2

/-- **The state and the transcript in hop R.** -/
def SxRK (γ : ΓR CI CR) (t : Tab3 × ShM R) : Sg × Trans :=
  (σR (A := A) γ t, SxR (A := A.adv (σR (A := A) γ t)) simI progI γ t)

/-- **The collision term of hop R**: the right redemption's real proof on the tables programmed by
the other three simulations differs from the one on the original tables. -/
noncomputable def deltaRAK [Fintype CI] [Fintype CR] (b : Bool) : ℝ :=
  pr (ΓR CI CR × (Coins proveSeedBytes × (Tab3 × ShM R))) fun z =>
    PA (A := A.adv (SxRK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI PR b true z.1
        (SxRK (A := A) simI progI z.1 z.2.2).2 z.2.1 z.2.2.1
        (LRA (A := A.adv (SxRK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI progI progR b z.1
          (SxRK (A := A) simI progI z.1 z.2.2).2 z.2.2.2) ≠
      PA (A := A.adv (SxRK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI PR b true z.1
        (SxRK (A := A) simI progI z.1 z.2.2).2 z.2.1 z.2.2.1 z.2.2.2

theorem hopRRAK [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (hA : A.GBudget q3 q5 qE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpR : ∀ x c, IsProg (progR x c) m5 mE)
    {AdmS : (X : Type) → (Tab3 × ShM R → X) → Prop}
    (hS : ∀ γ : ΓR CI CR, AdmS (Sg × Trans) (SxRK (A := A) simI progI γ))
    {ε : ℝ} (hR : ZeroKnowledgeROA RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmS
      (Budget pR q3 (0 + 0 + q5 + (m5 + (m5 + m5))) (0 + 0 + qE + (mE + (mE + mE)))) ε)
    (b : Bool) :
    |pr _ (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
        (fun σ => issSimRO (A.adv σ).ctxRO simI progI) (fun σ => redSimRO (A.adv σ).ctxRO simR progR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR)) -
      pr _ (simGameRAK A idx simI simR progI progR b)| ≤
      ε + deltaRAK (A := A) (idx := idx) (simI := simI) (progI := progI) (progR := progR) (PR := PR)
        b := by
  have h := hop_roA (Γ := ΓR CI CR) (ρ := Coins proveSeedBytes) (G := Tab3) (C := CR) (S := ShM R)
    (SxRK (A := A) simI progI) (fun γ x => PA (A := A.adv x.1) (idx := idx) simI PR b true γ x.2)
    (fun γ x => SmA (A := A.adv x.1) (idx := idx) simI simR b true γ x.2)
    (fun γ x => progA (A := A.adv x.1) (idx := idx) simI progR b true γ x.2)
    (fun γ x => LRA (A := A.adv x.1) (idx := idx) simI progI progR b γ x.2)
    (fun γ x => FRA (A := A.adv x.1) (idx := idx) simI simR b γ x.2) (ε := ε) fun γ => ?_
  · let e : (((TIs CI × TIs CI) × (TRs CR × (Coins proveSeedBytes × Tab3))) × ShM R) ≃
        (ΓR CI CR × (Coins proveSeedBytes × (Tab3 × ShM R))) :=
      { toFun := fun z => ((z.1.1, z.1.2.1), (z.1.2.2.1, (z.1.2.2.2, z.2)))
        invFun := fun z => ((z.1.1, (z.1.2, (z.2.1, z.2.2.1))), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let e' : (((TIs CI × TIs CI) × (TRs CR × (CR × Tab3))) × ShM R) ≃
        (ΓR CI CR × (CR × (Tab3 × ShM R))) :=
      { toFun := fun z => ((z.1.1, z.1.2.1), (z.1.2.2.1, (z.1.2.2.2, z.2)))
        invFun := fun z => ((z.1.1, (z.1.2, (z.2.1, z.2.2.1))), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e1 : pr _ (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
        (fun σ => issSimRO (A.adv σ).ctxRO simI progI) (fun σ => redSimRO (A.adv σ).ctxRO simR progR)
        (fun σ => redRealRO (A.adv σ).ctxRO PR)) =
        pr (ΓR CI CR × (Coins proveSeedBytes × (Tab3 × ShM R))) (fun z =>
          FRA (A := A.adv (SxRK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI simR b z.1
            (SxRK (A := A) simI progI z.1 z.2.2).2
            (PA (A := A.adv (SxRK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI PR b true z.1
              (SxRK (A := A) simI progI z.1 z.2.2).2 z.2.1 z.2.2.1
              (LRA (A := A.adv (SxRK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI progI progR b
                z.1 (SxRK (A := A) simI progI z.1 z.2.2).2 z.2.2.2)) z.2.2.1
            (LRA (A := A.adv (SxRK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI progI progR b z.1
              (SxRK (A := A) simI progI z.1 z.2.2).2 z.2.2.2)) := by
      rw [← pr_equiv e.symm]
      refine pr_congr fun z => ?_
      show FRA (A := A.adv (σR (A := A) z.1 z.2.2)) (idx := idx) simI simR b z.1
          (SxR (A := A.adv (σR (A := A) z.1 z.2.2)) simI progI z.1 z.2.2)
          ((redRealRO (A.adv (σR (A := A) z.1 z.2.2)).ctxRO PR (z.2.1, z.2.2.1)).out
            (ptA (A := A.adv (σR (A := A) z.1 z.2.2)) (idx := idx) simI b z.1
              (SxR (A := A.adv (σR (A := A) z.1 z.2.2)) simI progI z.1 z.2.2) true)
            (LRA (A := A.adv (σR (A := A) z.1 z.2.2)) (idx := idx) simI progI progR b z.1
              (SxR (A := A.adv (σR (A := A) z.1 z.2.2)) simI progI z.1 z.2.2) z.2.2.2)) z.2.2.1
          (LRA (A := A.adv (σR (A := A) z.1 z.2.2)) (idx := idx) simI progI progR b z.1
            (SxR (A := A.adv (σR (A := A) z.1 z.2.2)) simI progI z.1 z.2.2) z.2.2.2) ↔ _
      unfold PA
      split_ifs with hok
      · exact Iff.rfl
      · exact postRO_not_ok (Bool.of_not_eq_true hok) _ _ _ _ _ _
    have e2 : pr _ (simGameRAK A idx simI simR progI progR b) =
        pr (ΓR CI CR × (CR × (Tab3 × ShM R))) (fun z =>
          FRA (A := A.adv (SxRK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI simR b z.1
            (SxRK (A := A) simI progI z.1 z.2.2).2
            (SmA (A := A.adv (SxRK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI simR b true z.1
              (SxRK (A := A) simI progI z.1 z.2.2).2 z.2.1)
            z.2.2.1 (LRA (A := A.adv (SxRK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI progI
              progR b z.1 (SxRK (A := A) simI progI z.1 z.2.2).2
              (progA (A := A.adv (SxRK (A := A) simI progI z.1 z.2.2).1) (idx := idx) simI progR b true
                z.1 (SxRK (A := A) simI progI z.1 z.2.2).2 z.2.1 z.2.2.2))) := by
      rw [← pr_equiv e'.symm]
      exact pr_congr fun z => Iff.rfl
    rw [e1, e2]
    exact h
  · have hL : ∀ x : Sg × Trans, IsProg (LRA (A := A.adv x.1) (idx := idx) simI progI progR b γ x.2)
        (m5 + (m5 + m5)) (mE + (mE + mE)) := fun x =>
      (hpI _ _).comp ((hpI _ _).comp (IsProg.ite _ (hpR _ _) (IsProg.id.mono (Nat.zero_le _)
        (Nat.zero_le _))))
    have hz := hR (Sg × Trans) (SxRK (A := A) simI progI γ)
      (fun x => stwA (A := A.adv x.1) (idx := idx) simI b true γ x.2)
      (hS γ) (fun x => stwA_rel (A := A.adv x.1) (idx := idx) simI b true γ x.2) []
      (fun x o g s => FRA (A := A.adv x.1) (idx := idx) simI simR b γ x.2
        (.ok ((ptA (A := A.adv x.1) (idx := idx) simI b γ x.2 true).tok.nf ++ o)) g
        (LRA (A := A.adv x.1) (idx := idx) simI progI progR b γ x.2 s))
      fun x => ⟨fun o s => (hA x.1 x.2).h3R _ _ _ _ _ _ _,
        fun o g => (rd5_postRO (A := (A.adv x.1).fixT x.2) (idx := idx) (hA x.1 x.2) _ _ (Rd5.const _)
          (Rd5.const _) _).comp_prog (hL x),
        fun o g => (rdE_postRO (A := (A.adv x.1).fixT x.2) (idx := idx) (hA x.1 x.2) _ _ (RdE.const _)
          (RdE.const _) _).comp_prog (hL x)⟩
    refine le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun a => ?_)
      (pr_congr fun a => ?_)) hz
    · show FRA (A := A.adv (SxRK (A := A) simI progI γ a.2).1) (idx := idx) simI simR b γ
          (SxRK (A := A) simI progI γ a.2).2
          (PA (A := A.adv (SxRK (A := A) simI progI γ a.2).1) (idx := idx) simI PR b true γ
            (SxRK (A := A) simI progI γ a.2).2 a.1 a.2.1 a.2.2) a.2.1
          (LRA (A := A.adv (SxRK (A := A) simI progI γ a.2).1) (idx := idx) simI progI progR b γ
            (SxRK (A := A) simI progI γ a.2).2 a.2.2) ↔ _
      unfold PA outReal
      split_ifs with hok
      · simp only [stwA, hok, ↓reduceIte, Option.elim]
        rw [(redeem_factsA (A := A.adv (SxRK (A := A) simI progI γ a.2).1) (idx := idx) simI simR PR b
          true γ _ hok).2.1]
      · simp only [stwA, Bool.of_not_eq_true hok, Bool.false_eq_true, ↓reduceIte, Option.elim]
        exact postRO_not_ok (Bool.of_not_eq_true hok) _ _ _ _ _ _
    · show FRA (A := A.adv (SxRK (A := A) simI progI γ a.2).1) (idx := idx) simI simR b γ
          (SxRK (A := A) simI progI γ a.2).2
          (SmA (A := A.adv (SxRK (A := A) simI progI γ a.2).1) (idx := idx) simI simR b true γ
            (SxRK (A := A) simI progI γ a.2).2 a.1) a.2.1
          (LRA (A := A.adv (SxRK (A := A) simI progI γ a.2).1) (idx := idx) simI progI progR b γ
            (SxRK (A := A) simI progI γ a.2).2
            (progA (A := A.adv (SxRK (A := A) simI progI γ a.2).1) (idx := idx) simI progR b true γ
              (SxRK (A := A) simI progI γ a.2).2 a.1 a.2.2)) ↔ _
      unfold SmA progA outSim progSim
      split_ifs with hok
      · simp only [stwA, hok, ↓reduceIte, Option.elim]
        rw [(redeem_factsA (A := A.adv (SxRK (A := A) simI progI γ a.2).1) (idx := idx) simI simR PR b
          true γ _ hok).2.2]
      · simp only [stwA, Bool.of_not_eq_true hok, Bool.false_eq_true, ↓reduceIte, Option.elim]
        exact postRO_not_ok (Bool.of_not_eq_true hok) _ _ _ _ _ _

end HopsR

/-! ## Issuer hiding and unlinkability with a table-reading key stage -/

variable {A idx} {PI : ProverRO R IssueInstance} {PR : ProverRO R RedeemInstance} in
/-- **Theorem 4(a) in the random-oracle and ideal-cipher model, the key stage and the interaction
reading the tables, for any proof systems.** As `anonymityRA`, with the issuance proofs
`ZeroKnowledgeROA` for the readers `AdmSI` (which contain the setup read off each issuance slice
and the shared tables) and the redemption proofs for `AdmS` (which contain the state and the
transcript read through the setup and the issuance simulations' programming). -/
theorem anonymityRAK [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR]
    {q3 q5 qE i3 i2 i5 iE r5 rE m5 mE : ℕ} {εI εR : ℕ → ℕ → ℝ} {εhide : ℝ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpR : ∀ x c, IsProg (progR x c) m5 mE)
    {AdmSI AdmS : (X : Type) → (Tab3 × ShM R → X) → Prop}
    (hS0 : ∀ γ : NR × (TIr × (TRr × TRr)), AdmSI Sg (Sx0 (A := A) γ))
    (hS1 : ∀ γ : TIs CI × (NR × (TRr × TRr)), AdmSI Sg (Sx1 (A := A) γ))
    (hSL : ∀ γ : ΓL CI, AdmS (Sg × Trans) (SxLK (A := A) simI progI γ))
    (hSR : ∀ γ : ΓR CI CR, AdmS (Sg × Trans) (SxRK (A := A) simI progI γ))
    (hIzk : ∀ a c, ZeroKnowledgeROA IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI AdmSI
      (Budget pI (i3 + q3) a c) (εI a c))
    (hRzk : ∀ a c, ZeroKnowledgeROA RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmS
      (Budget pR q3 a c) (εR a c))
    (hhide : ∀ b c, hidingAdv (A.adv (σOf A c)).ctxRO.base.ci (A.adv (σOf A c)).ctxRO.base.cr
      (reductionRA (A.adv (σOf A c)) idx simI simR progI progR b c) ≤ εhide) :
    |pr _ (realGameRAK A idx PI PR false) - pr _ (realGameRAK A idx PI PR true)| ≤
      2 * (εI (r5 + (i5 + (r5 + r5 + q5))) (rE + (iE + (rE + rE + qE))) +
          εI (i5 + (r5 + r5 + q5) + m5) (iE + (rE + rE + qE) + mE) +
          εR (0 + r5 + q5 + (m5 + m5)) (0 + rE + qE + (mE + mE)) +
          εR (0 + 0 + q5 + (m5 + (m5 + m5))) (0 + 0 + qE + (mE + (mE + mE)))) +
        2 * deltaI1K (A := A) progI PI +
        (deltaLAK (A := A) (idx := idx) (simI := simI) (progI := progI) (PR := PR) false +
          deltaLAK (A := A) (idx := idx) (simI := simI) (progI := progI) (PR := PR) true) +
        (deltaRAK (A := A) (idx := idx) (simI := simI) (progI := progI) (progR := progR) (PR := PR)
            false +
          deltaRAK (A := A) (idx := idx) (simI := simI) (progI := progI) (progR := progR) (PR := PR)
            true) +
        2 * εhide := by
  have hw (b : Bool) : |pr _ (realGameRAK A idx PI PR b) -
      pr _ (idealGameRAK A idx simI simR progI progR b)| ≤
      εI (r5 + (i5 + (r5 + r5 + q5))) (rE + (iE + (rE + rE + qE))) +
        (εI (i5 + (r5 + r5 + q5) + m5) (iE + (rE + rE + qE) + mE) + deltaI1K (A := A) progI PI) +
        (εR (0 + r5 + q5 + (m5 + m5)) (0 + rE + qE + (mE + mE)) +
          deltaLAK (A := A) (idx := idx) (simI := simI) (progI := progI) (PR := PR) b) +
        (εR (0 + 0 + q5 + (m5 + (m5 + m5))) (0 + 0 + qE + (mE + (mE + mE))) +
          deltaRAK (A := A) (idx := idx) (simI := simI) (progI := progI) (progR := progR) (PR := PR)
            b) + εhide := by
    have h1 := hop0RAK (idx := idx) (simI := simI) (progI := progI) PI PR hA hI hPI5
      hPIE hPR5 hPRE hS0 (hIzk _ _) b
    have h2 := hop1RAK (idx := idx) (simI := simI) (progI := progI) PI PR hA hI hPR5
      hPRE hpI hS1 (hIzk _ _) b
    have h3 := hopLRAK (idx := idx) (simI := simI) (progI := progI) (simR := simR) (progR := progR)
      PR hA hPR5 hPRE hpI hSL (hRzk _ _) b
    have h4 := hopRRAK (idx := idx) (simI := simI) (progI := progI) (simR := simR) (progR := progR)
      PR hA hpI hpR hSR (hRzk _ _) b
    have h5 := hiding_hopRAK A idx simI simR progI progR b (hhide b)
    unfold realGameRAK
    set p0 := pr _ (gameRAK A idx b (fun σ => issRealRO (A.adv σ).ctxRO PI)
      (fun σ => issRealRO (A.adv σ).ctxRO PI) (fun σ => redRealRO (A.adv σ).ctxRO PR)
      (fun σ => redRealRO (A.adv σ).ctxRO PR))
    set p1 := pr _ (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
      (fun σ => issRealRO (A.adv σ).ctxRO PI) (fun σ => redRealRO (A.adv σ).ctxRO PR)
      (fun σ => redRealRO (A.adv σ).ctxRO PR))
    set p2 := pr _ (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
      (fun σ => issSimRO (A.adv σ).ctxRO simI progI) (fun σ => redRealRO (A.adv σ).ctxRO PR)
      (fun σ => redRealRO (A.adv σ).ctxRO PR))
    set p3 := pr _ (gameRAK A idx b (fun σ => issSimRO (A.adv σ).ctxRO simI progI)
      (fun σ => issSimRO (A.adv σ).ctxRO simI progI) (fun σ => redSimRO (A.adv σ).ctxRO simR progR)
      (fun σ => redRealRO (A.adv σ).ctxRO PR))
    set p4 := pr _ (simGameRAK A idx simI simR progI progR b)
    set p5 := pr _ (idealGameRAK A idx simI simR progI progR b)
    have := abs_sub_le p0 p1 p5
    have := abs_sub_le p1 p2 p5
    have := abs_sub_le p2 p3 p5
    have := abs_sub_le p3 p4 p5
    linarith
  have h0 := hw false
  have h1 := hw true
  rw [idealGameRAK_eq] at h0
  rw [abs_sub_comm] at h1
  have := abs_sub_le (pr _ (realGameRAK A idx PI PR false))
    (pr _ (idealGameRAK A idx simI simR progI progR true)) (pr _ (realGameRAK A idx PI PR true))
  linarith

/-! ## With the Lean prover -/

section Lean

open VoleMole.Verifier VoleMole.Verifier.Bridge

variable [CipherRow R]

lemma smallParams_pI : SmallParams pI := smallParams_of_le (by decide) (by decide)

/-- **Adaptive zero knowledge of the Lean issuance prover** (`ZK.Sim.lean_zeroKnowledgeROA`). -/
theorem leanPI_zkROA [ZKPRow R] (q3 q5 qE s3 s2 s5 sE : ℕ) : ZeroKnowledgeROA IssueRelW
    (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPI w x (List.ofFn ρ) g s) (leanSim pI)
    leanProgI (fun _ Sx => SReads pI Sx s3 s2 s5 sE) (Budget pI q3 q5 qE)
    (εAdG R pI pI.qsDegree q3 q5 qE s3 s2 s5 sE) := by
  have h := lean_zeroKnowledgeROA (R := R) Hashes.shake pI stI (fun _ => rfl) rfl (fun _ w => toBA w)
    IssueRelW csI zkHypI hashesWF_shake smallParams_pI q3 q5 qE s3 s2 s5 sE
    (fun o => toL (o.toOption.getD .empty))
  have e : (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPI w x (List.ofFn ρ) g s) =
      fun x w r g s => toL ((realRO pI Hashes.shake (stI x) (toBA w) r g s).toOption.getD .empty) := by
    funext x w ρ g s
    exact leanPI_ofFn w x ρ g s
  rw [e]
  exact h

variable (A : AdversaryRAK R Sg) (idx : AnchorSet → UOVKey → ℕ)

/-- **The collision term of hop 1** is still `≤ noHitProb + 2⁻¹⁰²⁴`: issuance `0`'s simulator
coins are independent of the state, of issuance `1`'s tape and of the tables. -/
theorem deltaI1K_le : deltaI1K (A := A) (leanProgI (R := R)) leanPI ≤ noHitProb + 1 / 2 ^ 1024 := by
  unfold deltaI1K
  refine (pr_mono (Q := fun z => preTail (blk (preLen pI) (preRO Hashes.shake
      (stI (xIOf (A.adv (Sx1 (A := A) z.1 z.2.2)).ctxRO z.1.2.1))
      (toBA (wIOf (A.adv (Sx1 (A := A) z.1 z.2.2)).ctxRO z.1.2.1)) z.2.1 z.2.2.1 z.2.2.2)) ∈
      ({simTail z.1.1.2.1} : Finset ByteArray)) fun z hz => ?_).trans ?_
  · rw [leanPI_ofFn, leanPI_ofFn] at hz
    have h1 := toL_getD_ne hz
    have hL := progRO_progAt (R := R) Hashes.shake
      (stI (xIOf (A.adv (Sx1 (A := A) z.1 z.2.2)).ctxRO z.1.1.1)) z.1.1.2.1
    have hz' := zkHypI _ _ (issueRelW_of (A.adv (Sx1 (A := A) z.1 z.2.2)).ctxRO z.1.2.1)
    have hT : ∀ s : ShM R, ∀ b ∈ ({simBlk Hashes.shake
        (stI (xIOf (A.adv (Sx1 (A := A) z.1 z.2.2)).ctxRO z.1.1.1)) z.1.1.2.1 s} :
        Finset (Bytes (preLen pI))), preTail b ∈ ({simTail z.1.1.2.1} : Finset ByteArray) := by
      intro s b hb
      rw [Finset.mem_singleton] at hb ⊢
      rw [hb]
      exact preTail_simBlk hashesWF_shake rfl _ _
    exact realRO_ne_tail hz' hashesWF_shake hlab_pI hL hT _ _ _ h1
  · refine pr_le_of_snd fun y => pr_le_of_snd fun r => pr_le_of_fst fun n =>
      pr_le_of_snd fun g => ?_
    have h := pr_simTail_eq_le (p := pI) (preTail (blk (preLen pI) (preRO Hashes.shake
      (stI (xIOf (A.adv (A.setup ((g, y.2.1), (r.2.1.2, r.2.2.2)) y.2.2)).ctxRO r.1))
      (toBA (wIOf (A.adv (A.setup ((g, y.2.1), (r.2.1.2, r.2.2.2)) y.2.2)).ctxRO r.1)) y.1 y.2.1 y.2.2)))
    rw [tail_pI] at h
    refine le_trans (le_of_eq (pr_congr fun c => ?_)) h
    exact Finset.mem_singleton

variable {A}

/-- **The state and transcript of hop L read** `(k₃ + i₃, k₂ + i₂, k₅ + i₅ + 624, k_E + i_E + 9214)`. -/
lemma sReads_SxLK {k3 k2 k5 kE i3 i2 i5 iE : ℕ} (hK : A.KBudget k3 k2 k5 kE)
    (hI : A.IBudget i3 i2 i5 iE) (γ : ΓL (SimCoins pI)) :
    SReads pR (SxLK (A := A) (leanSim pI) (leanProgI (R := R)) γ) (k3 + i3) (k2 + i2)
      (k5 + (i5 + 312 + 312)) (kE + (iE + 4607 + 4607)) :=
  (hK.sL _ _ _).bind (g := fun σ t => (σ, SxL (A := A.adv σ) (leanSim pI) leanProgI γ t))
    fun σ => (sReads_SxL (A.adv σ) (hI σ) γ).map fun x => (σ, x)

/-- **The state and transcript of hop R read** `(k₃ + i₃, k₂ + i₂, k₅ + i₅ + 624, k_E + i_E + 9214)`. -/
lemma sReads_SxRK {k3 k2 k5 kE i3 i2 i5 iE : ℕ} (hK : A.KBudget k3 k2 k5 kE)
    (hI : A.IBudget i3 i2 i5 iE) (γ : ΓR (SimCoins pI) (SimCoins pR)) :
    SReads pR (SxRK (A := A) (leanSim pI) (leanProgI (R := R)) γ) (k3 + i3) (k2 + i2)
      (k5 + (i5 + 312 + 312)) (kE + (iE + 4607 + 4607)) :=
  (hK.sR _ _ _).bind (g := fun σ t => (σ, SxR (A := A.adv σ) (leanSim pI) leanProgI γ t))
    fun σ => (sReads_SxR (A.adv σ) (hI σ) γ).map fun x => (σ, x)

variable (A)

/-- **The collision term of hop L**, with the statement read off the tables through the setup:
`δL b ≤ (k₃ + i₃)·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607; k₅ + i₅ + 624, k_E + i_E + 9214) + noHitProb
+ 2·2⁻¹⁰²⁴`. -/
theorem deltaLAK_le [ZKPRow R] {k3 k2 k5 kE i3 i2 i5 iE : ℕ} (hK : A.KBudget k3 k2 k5 kE)
    (hI : A.IBudget i3 i2 i5 iE) (b : Bool) :
    deltaLAK (A := A) (idx := idx) (simI := leanSim pI) (progI := leanProgI) (PR := leanPR) b ≤
      (k3 + i3 : ℕ) / 2 ^ 128 + (1 / 2 ^ 113 +
        ZKPRow.εP R pR 0 312 4607 (k5 + (i5 + 312 + 312)) (kE + (iE + 4607 + 4607)) +
        (noHitProb + 2 / 2 ^ 1024)) := by
  unfold deltaLAK
  refine pr_le_of_fst fun γ => ?_
  refine (pr_mono fun z hz => PA_ne (A.adv (SxLK (A := A) (leanSim pI) leanProgI γ z.2).1) idx b false
    γ _ z.1 z.2.1 _ _ hz).trans ?_
  refine (pr_collide_adaptive Hashes.shake pR rfl smallParams_pR hashesWF_shake
    (fun x : Sg × Trans => stwL (A.adv x.1) idx b false γ x.2)
    (fun x => csR (xROf (A.adv x.1).ctxRO (ptA (A := A.adv x.1) (idx := idx) (leanSim pI) b γ x.2 false)))
    (fun x => stwL_hyp (A.adv x.1) idx b false γ x.2) (SxLK (A := A) (leanSim pI) leanProgI γ)
    (sReads_SxLK hK hI γ)
    (fun x => PIOf (A.adv x.1).ctxRO leanProgI γ) _ (fun x => progAt_PIOf (A.adv x.1).ctxRO γ) _
    (fun x => tails_PIOf (A.adv x.1).ctxRO γ)).trans ?_
  have hc : (({simTail γ.1.1.2.1, simTail γ.1.2.2.1} : Finset ByteArray).card : ℝ) ≤ 2 := by
    exact_mod_cast Finset.card_le_two
  rw [tail_pR]
  gcongr

/-- **The collision term of hop R**: `δR b ≤ (k₃ + i₃)·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607;
k₅ + i₅ + 624, k_E + i_E + 9214) + noHitProb + 3·2⁻¹⁰²⁴`. -/
theorem deltaRAK_le [ZKPRow R] {k3 k2 k5 kE i3 i2 i5 iE : ℕ} (hK : A.KBudget k3 k2 k5 kE)
    (hI : A.IBudget i3 i2 i5 iE) (b : Bool) :
    deltaRAK (A := A) (idx := idx) (simI := leanSim pI) (progI := leanProgI) (progR := leanProgR)
        (PR := leanPR) b ≤
      (k3 + i3 : ℕ) / 2 ^ 128 + (1 / 2 ^ 113 +
        ZKPRow.εP R pR 0 312 4607 (k5 + (i5 + 312 + 312)) (kE + (iE + 4607 + 4607)) +
        (noHitProb + 3 / 2 ^ 1024)) := by
  unfold deltaRAK
  refine pr_le_of_fst fun γ => ?_
  refine (pr_mono fun z hz => PA_ne (A.adv (SxRK (A := A) (leanSim pI) leanProgI γ z.2).1) idx b true
    γ _ z.1 z.2.1 _ _ hz).trans ?_
  -- The programming before the right redemption's, at three blocks.
  let Bx : Sg × Trans → ShM R → Finset (Bytes (preLen pI)) := fun x s =>
    {simBlk Hashes.shake (stI (xIOf (A.adv x.1).ctxRO γ.1.1.1)) γ.1.1.2.1
        (progRO pI Hashes.shake (stI (xIOf (A.adv x.1).ctxRO γ.1.2.1)) γ.1.2.2.1
          (progA (A := A.adv x.1) (idx := idx) (leanSim pI) leanProgR b false γ x.2 γ.2.1 s))} ∪
      {simBlk Hashes.shake (stI (xIOf (A.adv x.1).ctxRO γ.1.2.1)) γ.1.2.2.1
        (progA (A := A.adv x.1) (idx := idx) (leanSim pI) leanProgR b false γ x.2 γ.2.1 s)} ∪
      (if okA (A := A.adv x.1) (idx := idx) (leanSim pI) γ x.2 = true then
        {simBlk Hashes.shake (stR (xROf (A.adv x.1).ctxRO (ptA (A := A.adv x.1) (idx := idx)
          (leanSim pI) b γ x.2 false))) γ.2.1 s} else ∅)
  have hL : ∀ x : Sg × Trans, ProgAt (LRA (A := A.adv x.1) (idx := idx) (leanSim pI) leanProgI
      leanProgR b γ x.2) (Bx x) :=
    fun x => (progAt_PIOf (A.adv x.1).ctxRO γ).comp (ProgAt.ite (okA (A := A.adv x.1) (idx := idx)
      (leanSim pI) γ x.2 = true) (progRO_progAt (R := R) Hashes.shake _ γ.2.1))
  have hT : ∀ x s, ∀ b' ∈ Bx x s, preTail b' ∈
      ({simTail γ.2.1, simTail γ.1.1.2.1, simTail γ.1.2.2.1} : Finset ByteArray) := by
    intro x s b' hb
    rcases Finset.mem_union.1 hb with hb | hb
    · exact Finset.mem_insert.2 (Or.inr (tails_PIOf (A.adv x.1).ctxRO γ _ b' hb))
    · by_cases hc : okA (A := A.adv x.1) (idx := idx) (leanSim pI) γ x.2 = true
      · simp only [hc, ↓reduceIte] at hb
        rw [Finset.mem_singleton.1 hb]
        exact Finset.mem_insert.2 (Or.inl (preTail_simBlk hashesWF_shake rfl _ _))
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hb
        exact absurd hb (Finset.notMem_empty _)
  refine (pr_collide_adaptive Hashes.shake pR rfl smallParams_pR hashesWF_shake
    (fun x : Sg × Trans => stwL (A.adv x.1) idx b true γ x.2)
    (fun x => csR (xROf (A.adv x.1).ctxRO (ptA (A := A.adv x.1) (idx := idx) (leanSim pI) b γ x.2 true)))
    (fun x => stwL_hyp (A.adv x.1) idx b true γ x.2) (SxRK (A := A) (leanSim pI) leanProgI γ)
    (sReads_SxRK hK hI γ)
    (fun x => LRA (A := A.adv x.1) (idx := idx) (leanSim pI) leanProgI leanProgR b γ x.2) Bx hL _
    hT).trans ?_
  have hc : (({simTail γ.2.1, simTail γ.1.1.2.1, simTail γ.1.2.2.1} :
      Finset ByteArray).card : ℝ) ≤ 3 := by
    exact_mod_cast Finset.card_le_three
  rw [tail_pR]
  gcongr

/-- **Theorem 4(a) with the Lean prover, the key stage and the interaction reading the tables, for
every type of cipher rows** (`ZKRow R`, `ZKPRow R`; `anonymityRAK_lean_num` at function rows). The
guess reads each `H₃` slice at `q₃` keys, `H₅` at `q₅`, the cipher at `q_E` and `H₂³` freely; the
interaction at every state reads `(i₃, i₂, i₅, i_E)` (`IBudget`); the key stage reads
`(k₃, k₂, k₅, k_E)` (`KBudget`), consistently. Then the two worlds differ by at most

    4·εAd(9; i₃ + q₃, q₅ + i₅ + 1872, q_E + i_E + 13821; k₃, k₂, k₅, k_E)
      + 4·εAd(9; q₃, q₅ + 1248, q_E + 13821; k₃ + i₃, k₂ + i₂, k₅ + i₅ + 624, k_E + i_E + 9214)
      + 4·((k₃ + i₃)·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607; k₅ + i₅ + 624, k_E + i_E + 9214))
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

The issuance hops are the adaptive theorem at the key stage's budget (the interaction's reads paid
as the distinguisher's); the redemption hops the adaptive theorem at the composed reader's budget
(the setup, then the transcript through the two issuance programmings); issuance `1`'s collision
term is `noHitProb + 2⁻¹⁰²⁴` (`deltaI1K_le`), the redemptions' the adaptive collision bound. -/
theorem anonymityRAK_lean_numG [ZKRow R] [ZKPRow R] {q3 q5 qE i3 i2 i5 iE k3 k2 k5 kE : ℕ}
    {εhide : ℝ} (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE) (hK : A.KBudget k3 k2 k5 kE)
    (hhide : ∀ b c, hidingAdv (A.adv (σOf A c)).ctxRO.base.ci (A.adv (σOf A c)).ctxRO.base.cr
      (reductionRA (A.adv (σOf A c)) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRAK A idx leanPI leanPR false) - pr _ (realGameRAK A idx leanPI leanPR true)| ≤
      4 * εAdG R pI 9 (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) k3 k2 k5 kE +
        4 * εAdG R pR 9 q3 (q5 + 1248) (qE + 13821) (k3 + i3) (k2 + i2) (k5 + i5 + 624)
          (kE + iE + 9214) +
        4 * ((k3 + i3 : ℕ) / 2 ^ 128 + 1 / 2 ^ 113 +
          ZKPRow.εP R pR 0 312 4607 (k5 + i5 + 624) (kE + iE + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  have hPI5 : ∀ w x rho g, Rd5 (leanPI (R := R) w x rho g) 624 := fun w x rho g =>
    (realROb_rd5 (p := pI) (Hb := Hashes.shake) (st := stI x) (w := toBA w) (toBA rho) g).map
      fun o => toL (o.toOption.getD .empty)
  have hPIE : ∀ w x rho g, RdE (leanPI (R := R) w x rho g) 4607 := fun w x rho g =>
    (realROb_rdE (p := pI) (st := stI x) (w := toBA w) hashesWF_shake (toBA rho) g).map
      fun o => toL (o.toOption.getD .empty)
  have hPR5 : ∀ w x rho g, Rd5 (leanPR (R := R) w x rho g) 624 := fun w x rho g =>
    (realROb_rd5 (p := pR) (Hb := Hashes.shake) (st := stR x) (w := toBA w) (toBA rho) g).map
      fun o => toL (o.toOption.getD .empty)
  have hPRE : ∀ w x rho g, RdE (leanPR (R := R) w x rho g) 4607 := fun w x rho g =>
    (realROb_rdE (p := pR) (st := stR x) (w := toBA w) hashesWF_shake (toBA rho) g).map
      fun o => toL (o.toOption.getD .empty)
  have h := anonymityRAK (A := A) (idx := idx) (PI := leanPI) (PR := leanPR) (simI := leanSim pI)
    (simR := leanSim pR) (progI := leanProgI) (progR := leanProgR)
    (εI := fun a c => εAdG R pI pI.qsDegree (i3 + q3) a c k3 k2 k5 kE)
    (εR := fun a c => εAdG R pR pR.qsDegree q3 a c (k3 + i3) (k2 + i2) (k5 + (i5 + 312 + 312))
      (kE + (iE + 4607 + 4607)))
    (AdmSI := fun _ Sx => SReads pI Sx k3 k2 k5 kE)
    (AdmS := fun _ Sx => SReads pR Sx (k3 + i3) (k2 + i2) (k5 + (i5 + 312 + 312))
      (kE + (iE + 4607 + 4607)))
    hA hI hPI5 hPIE hPR5 hPRE (fun x c => progRO_isProg c) (fun x c => progRO_isProg c)
    (fun γ => hK.s0 _ _ _) (fun γ => hK.s1 _ _ _) (sReads_SxLK hK hI) (sReads_SxRK hK hI)
    (fun a c => leanPI_zkROA (i3 + q3) a c k3 k2 k5 kE)
    (fun a c => leanPR_zkROA q3 a c (k3 + i3) (k2 + i2) (k5 + (i5 + 312 + 312))
      (kE + (iE + 4607 + 4607))) hhide
  have mI : ∀ a c, a ≤ q5 + i5 + 1872 → c ≤ qE + iE + 13821 →
      εAdG R pI pI.qsDegree (i3 + q3) a c k3 k2 k5 kE ≤
        εAdG R pI 9 (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) k3 k2 k5 kE :=
    fun a c ha hc => εAdG_mono pI le_rfl ha hc le_rfl le_rfl le_rfl le_rfl
  have mR : ∀ a c, a ≤ q5 + 1248 → c ≤ qE + 13821 →
      εAdG R pR pR.qsDegree q3 a c (k3 + i3) (k2 + i2) (k5 + (i5 + 312 + 312))
        (kE + (iE + 4607 + 4607)) ≤
        εAdG R pR 9 q3 (q5 + 1248) (qE + 13821) (k3 + i3) (k2 + i2) (k5 + i5 + 624)
          (kE + iE + 9214) :=
    fun a c ha hc => εAdG_mono pR le_rfl ha hc le_rfl le_rfl (by omega) (by omega)
  have m1 := mI (624 + (i5 + (624 + 624 + q5))) (4607 + (iE + (4607 + 4607 + qE))) (by omega)
    (by omega)
  have m2 := mI (i5 + (624 + 624 + q5) + 312) (iE + (4607 + 4607 + qE) + 4607) (by omega) (by omega)
  have m3 := mR (0 + 624 + q5 + (312 + 312)) (0 + 4607 + qE + (4607 + 4607)) (by omega) (by omega)
  have m4 := mR (0 + 0 + q5 + (312 + (312 + 312))) (0 + 0 + qE + (4607 + (4607 + 4607))) (by omega)
    (by omega)
  have d1 := deltaI1K_le (R := R) A
  have dL0 := deltaLAK_le A idx hK hI false
  have dL1 := deltaLAK_le A idx hK hI true
  have dR0 := deltaRAK_le A idx hK hI false
  have dR1 := deltaRAK_le A idx hK hI true
  have e1 : ZKPRow.εP R pR 0 312 4607 (k5 + (i5 + 312 + 312)) (kE + (iE + 4607 + 4607)) =
      ZKPRow.εP R pR 0 312 4607 (k5 + i5 + 624) (kE + iE + 9214) := by
    rw [show k5 + (i5 + 312 + 312) = k5 + i5 + 624 by omega,
      show kE + (iE + 4607 + 4607) = kE + iE + 9214 by omega]
  rw [e1] at dL0 dL1 dR0 dR1
  refine h.trans ?_
  rw [div_eq_mul_one_div (2 : ℝ) ((2 : ℝ) ^ 1024)] at dL0 dL1
  rw [div_eq_mul_one_div (3 : ℝ) ((2 : ℝ) ^ 1024)] at dR0 dR1
  rw [div_eq_mul_one_div (12 : ℝ) ((2 : ℝ) ^ 1024)]
  generalize (1 : ℝ) / 2 ^ 1024 = κ at d1 dL0 dL1 dR0 dR1 ⊢
  linarith

/-- **Theorem 4(a) with the Lean prover, in the random-oracle and ideal-cipher model, the key stage
and the interaction reading the tables, with every term explicit** (`anonymityRAK_lean_numG` at
function rows). -/
theorem anonymityRAK_lean_num (A : AdversaryRAK (Blk → Blk) Sg) {q3 q5 qE i3 i2 i5 iE k3 k2 k5 kE : ℕ}
    {εhide : ℝ} (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE) (hK : A.KBudget k3 k2 k5 kE)
    (hhide : ∀ b c, hidingAdv (A.adv (σOf A c)).ctxRO.base.ci (A.adv (σOf A c)).ctxRO.base.cr
      (reductionRA (A.adv (σOf A c)) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRAK A idx leanPI leanPR false) - pr _ (realGameRAK A idx leanPI leanPR true)| ≤
      4 * εAd 9 (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) k3 k2 k5 kE +
        4 * εAd 9 q3 (q5 + 1248) (qE + 13821) (k3 + i3) (k2 + i2) (k5 + i5 + 624) (kE + iE + 9214) +
        4 * ((k3 + i3 : ℕ) / 2 ^ 128 + 1 / 2 ^ 113 + εROP 0 312 4607 (k5 + i5 + 624) (kE + iE + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityRAK_lean_numG A idx hA hI hK hhide

/-- **Theorem 4(a) with a table-reading key stage and AES as uniformly random permutations**
(`anonymityRAK_lean_numG` at permutation rows). -/
theorem anonymityRAK_lean_num_perm (A : AdversaryRAK (Equiv.Perm Blk) Sg)
    {q3 q5 qE i3 i2 i5 iE k3 k2 k5 kE : ℕ} {εhide : ℝ} (hA : A.GBudget q3 q5 qE)
    (hI : A.IBudget i3 i2 i5 iE) (hK : A.KBudget k3 k2 k5 kE)
    (hhide : ∀ b c, hidingAdv (A.adv (σOf A c)).ctxRO.base.ci (A.adv (σOf A c)).ctxRO.base.cr
      (reductionRA (A.adv (σOf A c)) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRAK A idx leanPI leanPR false) - pr _ (realGameRAK A idx leanPI leanPR true)| ≤
      4 * εAdPm pI 9 (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) k3 k2 k5 kE +
        4 * εAdPm pR 9 q3 (q5 + 1248) (qE + 13821) (k3 + i3) (k2 + i2) (k5 + i5 + 624)
          (kE + iE + 9214) +
        4 * ((k3 + i3 : ℕ) / 2 ^ 128 + 1 / 2 ^ 113 +
          εROPmP pR 0 312 4607 (k5 + i5 + 624) (kE + iE + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityRAK_lean_numG A idx hA hI hK hhide

end Lean

end VoleMole.Privacy.Moussaka
