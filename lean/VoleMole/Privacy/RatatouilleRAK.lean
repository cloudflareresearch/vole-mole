import VoleMole.Privacy.RatatouilleRA
import VoleMole.Privacy.PermRA

/-!
# Ratatouille with a key stage that reads the tables

In `Privacy/RatatouilleRA.lean` the Issuer's two message stages read the tables, but its key,
context and initial balance (`AdversaryRA.pk`, `ctx`, `tInit`) are constants. Here they are chosen
by a **key stage** that reads the tables first (`AdversaryRAK`): `setup` reads the four `H₃` slices
and the shared tables (`H₂³`, `H₅`, the cipher) within a budget, consistently (`KBudget`, per
slice position as `IBudget`), and outputs a state `σ`; the rest of the Issuer (key, context,
balance, both stages, the guess) is the table-reading Issuer `adv σ` of `RatatouilleRA`.

## The game

`realGameRAK`: the setup on the slices and the original tables (nothing is programmed before the
challenge), then `realGameRA` of `adv σ`. Every hybrid is `gameRA` of `adv σ` with `σ` read off
the slices and the original tables (`gameRAK`).

## The hybrids

As in `unlinkabilityRA`, but the **issuance statements are now adaptive** (the commitment, the
balance and the context are fixed by `σ`; if `σ`'s balance is `0` nothing is proved): both
issuance hops are `hop_roA` with `ZeroKnowledgeROA` for the setup reader (`εAd` at the key stage's
budget `(k₃, k₂, k₅, k_E)`). Issuance `1`'s collision term (`deltaI1RK`) is still
`≤ noHitProb + 2⁻¹⁰²⁴` (`deltaI1RK_le`: issuance `0`'s simulator coins are independent of the
setup). The spend hops read the stage-1 messages (round 1) and the transcript (round 2) through
the setup (`SReads.bind`: `+ (k₃, k₂, k₅, k_E)`), and their collision terms are
`pr_collide_adaptive` at those budgets. The setup's reads before the challenge may meet blocks the
simulators program later: that is the `H₂³` term of `εAd` in each hop. The simulated world is
`simGameRA` of `adv σ`, a function of the commitments, the nullifiers, the coins, the slices and
the tables, and hiding (for the reductions at `σ`) finishes as before.

**`unlinkabilityRAK_lean_num`**: any two worlds differ by at most

    4·εAd(9; 2i₃ + q₃, q₅ + 2i₅ + 1872, q_E + 2i_E + 13821; k₃, k₂, k₅, k_E)
      + 2·εAd(9; i₃ + q₃, q₅ + i₅ + 1248, q_E + i_E + 13821;
              k₃ + i₃, k₂ + i₂, k₅ + i₅ + 624, k_E + i_E + 9214)
      + 2·εAd(9; q₃, q₅ + 936, q_E + 13821; k₃ + 2i₃, k₂ + 2i₂, k₅ + 2i₅ + 1560, k_E + 2i_E + 23035)
      + 2·(k₃ + i₃)·2⁻¹²⁸ + 2·(k₃ + 2i₃)·2⁻¹²⁸
      + 4·(2⁻¹¹³ + εROP(0, 312, 4607; k₅ + 2i₅ + 1560, k_E + 2i_E + 23035))
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim

variable {Z : Sizes} {R : Type} [Fintype R] [Nonempty R]

/-! ## The model -/

/-- **The malicious Issuer with a key stage that reads the tables**: `setup` reads the four `H₃`
slices and the shared tables and outputs a state `σ`; the key, context, balance, both message
stages and the guess are those of the table-reading Issuer `adv σ`. -/
structure AdversaryRAK (R : Type) (Z : Sizes) (Sg : Type) where
  setup : SlicesR → ShR R → Sg
  adv : Sg → AdversaryRA R Z

namespace AdversaryRAK

variable {Sg : Type} (A : AdversaryRAK R Z Sg)

/-- **The key stage's budget**: as a function of each proof's slice and the shared tables (the
other slices fixed), the setup reads at most `k₃` slice keys, `k₂` `H₂³` keys, `k₅` `H₅` keys and
`k_E` cipher keys, consistently. -/
structure KBudget (k3 k2 k5 kE : ℕ) : Prop where
  s0 : ∀ (g₁ g₂ g₃ : Tab3), SReads pI (fun t : Tb R pI => A.setup ((t.1, g₁), (g₂, g₃)) t.2) k3 k2 k5 kE
  s1 : ∀ (g₀ g₂ g₃ : Tab3), SReads pI (fun t : Tb R pI => A.setup ((g₀, t.1), (g₂, g₃)) t.2) k3 k2 k5 kE
  s2 : ∀ (g₀ g₁ g₃ : Tab3), SReads pS (fun t : Tb R pS => A.setup ((g₀, g₁), (t.1, g₃)) t.2) k3 k2 k5 kE
  s3 : ∀ (g₀ g₁ g₂ : Tab3), SReads pS (fun t : Tb R pS => A.setup ((g₀, g₁), (g₂, t.1)) t.2) k3 k2 k5 kE

/-- **The interaction's budget**, at every state. -/
def IBudget (i3 i2 i5 iE : ℕ) : Prop := ∀ σ, (A.adv σ).IBudget i3 i2 i5 iE

/-- **The guess's budget**, at every state. -/
def GBudget (q3 q5 qE : ℕ) : Prop := ∀ σ, (A.adv σ).GBudget q3 q5 qE

end AdversaryRAK

variable {Sg : Type} (A : AdversaryRAK R Z Sg)

/-- The four slices of a game tape (every slot's slice is the last component of its tape). -/
def slRK {C₀ C₁ C₂ C₃ : Type}
    (x : ((NRR × (C₀ × Tab3)) × (NRR × (C₁ × Tab3))) × ((NRR × (C₂ × Tab3)) × (NRR × (C₃ × Tab3)))) :
    SlicesR :=
  ((x.1.1.2.2, x.1.2.2.2), (x.2.1.2.2, x.2.2.2.2))

/-- **The game with a key stage**: the state read off the slices and the original tables, then
`gameRA` of `adv σ` with the slots drawn at `σ`. -/
def gameRAK {C₀ C₁ C₂ C₃ : Type} (b₁ b₂ : Bool) (g₀ : Sg → NRR × (C₀ × Tab3) → IssSlotR R Z)
    (g₁ : Sg → NRR × (C₁ × Tab3) → IssSlotR R Z) (k₁ : Sg → NRR × (C₂ × Tab3) → SpSlotR R Z)
    (k₂ : Sg → NRR × (C₃ × Tab3) → SpSlotR R Z)
    (x : (((NRR × (C₀ × Tab3)) × (NRR × (C₁ × Tab3))) × ((NRR × (C₂ × Tab3)) × (NRR × (C₃ × Tab3)))) ×
      ShR R) : Prop :=
  gameRA (A.adv (A.setup (slRK x.1) x.2)) b₁ b₂ (g₀ (A.setup (slRK x.1) x.2))
    (g₁ (A.setup (slRK x.1) x.2)) (k₁ (A.setup (slRK x.1) x.2)) (k₂ (A.setup (slRK x.1) x.2)) x

/-- **The real game with a key stage**: the setup reads the tables, then the spec's protocol with
every proof computed on the shared uniform tables, the Issuer's interaction and guess reading
them. -/
def realGameRAK (PI : ProverI R Z) (PS : ProverS R Z) (b₁ b₂ : Bool) :
    ((TRe × TRe) × (TRe × TRe)) × ShR R → Prop :=
  gameRAK A b₁ b₂ (fun σ => issRealR (A.adv σ).toRO PI) (fun σ => issRealR (A.adv σ).toRO PI)
    (fun σ => spRealR (A.adv σ).toRO PS) (fun σ => spRealR (A.adv σ).toRO PS)

/-- At every tape the real game is `realGameRA` of the Issuer at the state read off it. -/
lemma realGameRAK_iff (PI : ProverI R Z) (PS : ProverS R Z) (b₁ b₂ : Bool)
    (x : ((TRe × TRe) × (TRe × TRe)) × ShR R) :
    realGameRAK A PI PS b₁ b₂ x ↔ realGameRA (A.adv (A.setup (slRK x.1) x.2)) PI PS b₁ b₂ x :=
  Iff.rfl

section Ideal

variable {CI CS : Type} (simI : IssueInstance → CI → Option (IssueProof Z))
  (simS : SpendInstance → CS → Option (SpendProof Z))
  (progI : IssueInstance → CI → ShR R → ShR R) (progS : SpendInstance → CS → ShR R → ShR R)

/-- The game with all four proofs simulated. -/
def simGameRAK (b₁ b₂ : Bool) : ((TIsR CI × TIsR CI) × (TSsR CS × TSsR CS)) × ShR R → Prop :=
  gameRAK A b₁ b₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
    (fun σ => issSimR (A.adv σ).toRO simI progI) (fun σ => spSimR (A.adv σ).toRO simS progS)
    (fun σ => spSimR (A.adv σ).toRO simS progS)

/-- The state of a hiding tape: read off its slices and tables. -/
abbrev σOfR (K : KR R CI CS) : Sg := A.setup K.2.1 K.2.2

/-- The ideal world at the state read off the slices and tables. -/
def idealGameRAK (b₁ b₂ : Bool) (y : UTape × KR R CI CS) : Prop :=
  idealGameRA (A.adv (σOfR A y.2)) simI simS progI progS b₁ b₂ y

theorem hiding_hopRAK [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS]
    (hprogI : ∀ x x' c, simI x c = none → progI x c = progI x' c)
    (hprogS : ∀ x x' c, simS x c = none → progS x c = progS x' c) (b₁ b₂ : Bool) {εhide : ℝ}
    (hhide : ∀ K, hidingAdv (A.adv (σOfR A K)).ctx
      (reductionRA (A.adv (σOfR A K)) simI simS progI progS b₁ b₂ K) ≤ εhide) :
    |pr _ (simGameRAK A simI simS progI progS b₁ b₂) -
      pr _ (idealGameRAK A simI simS progI progS b₁ b₂)| ≤ εhide := by
  rw [← pr_equiv regroupR.symm (simGameRAK A simI simS progI progS b₁ b₂),
    pr_congr (P := fun y => simGameRAK A simI simS progI progS b₁ b₂ (regroupR.symm y))
      fun y => (simGameRA_iff (A.adv (σOfR A y.2)) simI simS progI progS hprogI hprogS b₁ b₂
      (regroupR.symm y)).trans (simGame_iff _ simI simS b₁ b₂ _)]
  exact abs_pr_prod_sub_le' _ _ fun K => hhide K

/-- **In the ideal world the four worlds coincide**, for every simulator coins, slices and
tables (at the state they fix). -/
theorem idealGameRAK_eq [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS] (b₁ b₂ : Bool) :
    pr _ (idealGameRAK A simI simS progI progS b₁ b₂) =
      pr _ (idealGameRAK A simI simS progI progS false false) := by
  have key : ∀ K : KR R CI CS, pr UTape (fun u => idealGameRAK A simI simS progI progS b₁ b₂ (u, K)) =
      pr UTape (fun u => idealGameRAK A simI simS progI progS false false (u, K)) := by
    intro K
    set A' := atRA (A.adv (σOfR A K)) progI progS K.1 K.2.2 K.2.1
    have e (c₁ c₂ : Bool) (u : UTape) : idealGameRAK A simI simS progI progS c₁ c₂ (u, K) ↔
        idealW A' simI simS (bif c₁ then vec u.1.2.1 else vec u.1.1.1)
          (bif c₂ == c₁ then vec u.2.1.1 else bif c₁ then vec u.1.1.1 else vec u.1.2.1)
          (vec u.1.1.2) (vec u.1.2.2) (vec u.2.1.2) (vec u.2.2.2) K.1 :=
      idealGame_iff A' simI simS c₁ c₂ (u, K.1)
    rw [pr_congr (e b₁ b₂), pr_congr (e false false)]
    cases b₁ <;> cases b₂ <;>
      simp only [Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.not_false, Bool.cond_true,
        Bool.cond_false]
    · rw [← pr_equiv (permU (⟨fun z => (z.1, z.2.2, z.2.1), fun z => (z.1, z.2.2, z.2.1),
        fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
        (fun u => idealW A' simI simS (vec u.1.1.1) (vec u.2.1.1) (vec u.1.1.2) (vec u.1.2.2)
          (vec u.2.1.2) (vec u.2.2.2) K.1)]
      exact pr_congr fun _ => Iff.rfl
    · rw [← pr_equiv (permU (⟨fun z => (z.2.1, z.2.2, z.1), fun z => (z.2.2, z.1, z.2.1),
        fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
        (fun u => idealW A' simI simS (vec u.1.1.1) (vec u.2.1.1) (vec u.1.1.2) (vec u.1.2.2)
          (vec u.2.1.2) (vec u.2.2.2) K.1)]
      exact pr_congr fun _ => Iff.rfl
    · rw [← pr_equiv (permU (⟨fun z => (z.2.1, z.1, z.2.2), fun z => (z.2.1, z.1, z.2.2),
        fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
        (fun u => idealW A' simI simS (vec u.1.1.1) (vec u.2.1.1) (vec u.1.1.2) (vec u.1.2.2)
          (vec u.2.1.2) (vec u.2.2.2) K.1)]
      exact pr_congr fun _ => Iff.rfl
  have h := abs_pr_prod_sub_le' (fun y : UTape × KR R CI CS => idealGameRAK A simI simS progI progS b₁ b₂ y)
    (fun y : UTape × KR R CI CS => idealGameRAK A simI simS progI progS false false y) (ε := 0)
    fun K => by rw [key K, sub_self, abs_zero]
  rw [abs_nonpos_iff, sub_eq_zero] at h
  exact h

end Ideal

/-! ## The issuance hops: adaptive statements -/

section HopsI

variable {A} {CI : Type} {simI : IssueInstance → CI → Option (IssueProof Z)}
  {progI : IssueInstance → CI → ShR R → ShR R} {PI : ProverI R Z} {PS : ProverS R Z}
  {q3 q5 qE i3 i2 i5 iE r5 rE m5 mE : ℕ}

/-- The state in hop 0, read off issuance `0`'s slice and the shared tables. -/
def SxI0 (γ : NRR × (TRe × (TRe × TRe))) (t : Tab3 × ShR R) : Sg :=
  A.setup ((t.1, γ.2.1.2.2), (γ.2.2.1.2.2, γ.2.2.2.2.2)) t.2

/-- The state in hop 1, read off issuance `1`'s slice and the shared tables. -/
def SxI1 (γ : TIsR CI × (NRR × (TRe × TRe))) (t : Tab3 × ShR R) : Sg :=
  A.setup ((γ.1.2.2, t.1), (γ.2.2.1.2.2, γ.2.2.2.2.2)) t.2

/-- The issuance statement and witness at the state `σ`, unless its balance is `0` (then nothing
is proved). -/
def stwI (n : NRR) (σ : Sg) : Option (IssueInstance × IssueWitness) :=
  if (A.adv σ).toRO.tInit = 0 then none else some (xIOf (A.adv σ).toRO n, ⟨vec n.1, vec n.2⟩)

lemma stwI_rel (n : NRR) : ∀ σ i w, stwI (A := A) n σ = some (i, w) → IssueRel i w := by
  intro σ i w h
  unfold stwI at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- An issuance output at the state `σ` from the prover's proof (or none if nothing is proved). -/
def outI (n : NRR) (σ : Sg) (o : Option (IssueProof Z)) : IssOut Z TokenS :=
  if (A.adv σ).toRO.tInit = 0 then issOutOf (A.adv σ).toRO.base (.error .invalidArgument)
  else ΦI (A.adv σ).toRO n o

lemma issRealR_outI (n : NRR) (σ : Sg) (y : Coins 16 × Tab3) (s : ShR R) :
    (issRealR (A.adv σ).toRO PI (n, y)).out s =
      outI (A := A) n σ (outReal (stwI (A := A) n) (fun x w (ρ : Coins 16) g s => PI x w (vec ρ) g s)
        none σ y.1 y.2 s) := by
  unfold outI outReal stwI
  by_cases hT : (A.adv σ).toRO.tInit = 0
  · simp only [hT, ↓reduceIte]
    exact issRealR_out_zero hT _ _
  · simp only [hT, ↓reduceIte, Option.elim]
    exact issRealR_out_ne hT _ _

lemma issSim_outI (n : NRR) (σ : Sg) (c : CI) :
    issSim (A.adv σ).toRO.base simI (n.1, n.2, c) = outI (A := A) n σ (outSim (stwI (A := A) n) simI none σ c) := by
  unfold outI outSim stwI
  by_cases hT : (A.adv σ).toRO.tInit = 0
  · simp only [hT, ↓reduceIte]
    exact issSim_zero hT _ _
  · simp only [hT, ↓reduceIte, Option.elim]
    exact issSim_ne hT _ _

lemma PIR_progSim (n : NRR) (σ : Sg) (c : CI) (s : ShR R) :
    PIR (A.adv σ).toRO progI n c s = progSim (stwI (A := A) n) progI σ c s := by
  unfold progSim stwI PIR
  by_cases hT : (A.adv σ).toRO.tInit = 0
  · simp only [hT, ↓reduceIte, Option.elim]
  · simp only [hT, ↓reduceIte, Option.elim]

/-- The tape regrouped around issuance `0`'s proof, for `hop_roA`. -/
def eqv0RK {N P G T₁ T₂ S : Type} :
    (N × (T₁ × T₂)) × (P × (G × S)) ≃ (((N × (P × G)) × T₁) × T₂) × S where
  toFun z := ((((z.1.1, (z.2.1, z.2.2.1)), z.1.2.1), z.1.2.2), z.2.2.2)
  invFun y := ((y.1.1.1.1, (y.1.1.2, y.1.2)), (y.1.1.1.2.1, (y.1.1.1.2.2, y.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The tape regrouped around issuance `1`'s proof, for `hop_roA`. -/
def eqv1RK {T₀ N P G T₂ S : Type} :
    (T₀ × (N × T₂)) × (P × (G × S)) ≃ ((T₀ × (N × (P × G))) × T₂) × S where
  toFun z := (((z.1.1, (z.1.2.1, (z.2.1, z.2.2.1))), z.1.2.2), z.2.2.2)
  invFun y := ((y.1.1.1, (y.1.1.2.1, y.1.2)), (y.1.1.2.2.1, (y.1.1.2.2.2, y.2)))
  left_inv _ := rfl
  right_inv _ := rfl

theorem hopI0RAK [Fintype CI] [Nonempty CI] (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPI5 : ∀ x w ρ g, Rd5 (PI x w ρ g) r5) (hPIE : ∀ x w ρ g, RdE (PI x w ρ g) rE)
    (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) r5) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) rE)
    {AdmS : (X : Type) → (Tab3 × ShR R → X) → Prop}
    (hS : ∀ γ : NRR × (TRe × (TRe × TRe)), AdmS Sg (SxI0 (A := A) γ))
    {ε : ℝ} (hIzk : ZeroKnowledgeROA IssueRel
      (fun x w (ρ : Coins 16) g s => PI x w (vec ρ) g s) simI progI AdmS
      (Budget pI (i3 + i3 + q3) (0 + (r5 + (i5 + (r5 + (i5 + (r5 + q5))))))
        (0 + (rE + (iE + (rE + (iE + (rE + qE))))))) ε) (b₁ b₂ : Bool) :
    |pr _ (gameRAK A b₁ b₂ (fun σ => issRealR (A.adv σ).toRO PI) (fun σ => issRealR (A.adv σ).toRO PI)
        (fun σ => spRealR (A.adv σ).toRO PS) (fun σ => spRealR (A.adv σ).toRO PS)) -
      pr _ (gameRAK A b₁ b₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
        (fun σ => issRealR (A.adv σ).toRO PI) (fun σ => spRealR (A.adv σ).toRO PS)
        (fun σ => spRealR (A.adv σ).toRO PS))| ≤ ε := by
  have h := hop_roA (Γ := NRR × (TRe × (TRe × TRe))) (ρ := Coins 16) (G := Tab3) (C := CI)
    (S := ShR R) (SxI0 (A := A))
    (fun γ σ ρ g s => (issRealR (A.adv σ).toRO PI (γ.1, (ρ, g))).out s)
    (fun γ σ c => issSim (A.adv σ).toRO.base simI (γ.1.1, γ.1.2, c))
    (fun γ σ c s => PIR (A.adv σ).toRO progI γ.1 c s)
    (fun _ _ s => s) (fun γ σ => F0A (A.adv σ) PI PS b₁ b₂ γ) (ε := ε) fun γ => ?_
  · have hδ : pr ((NRR × (TRe × (TRe × TRe))) × (Coins 16 × (Tab3 × ShR R))) (fun z =>
        (issRealR (A.adv (SxI0 (A := A) z.1 z.2.2)).toRO PI (z.1.1, (z.2.1, z.2.2.1))).out z.2.2.2 ≠
          (issRealR (A.adv (SxI0 (A := A) z.1 z.2.2)).toRO PI (z.1.1, (z.2.1, z.2.2.1))).out
            z.2.2.2) = 0 := by
      rw [pr_congr (Q := fun _ => False) fun z => by simp, pr_const]
      simp
    rw [hδ, add_zero] at h
    rw [← pr_equiv eqv0RK (gameRAK A b₁ b₂ (fun σ => issRealR (A.adv σ).toRO PI)
        (fun σ => issRealR (A.adv σ).toRO PI) (fun σ => spRealR (A.adv σ).toRO PS)
        (fun σ => spRealR (A.adv σ).toRO PS)),
      ← pr_equiv eqv0RK (gameRAK A b₁ b₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
        (fun σ => issRealR (A.adv σ).toRO PI) (fun σ => spRealR (A.adv σ).toRO PS)
        (fun σ => spRealR (A.adv σ).toRO PS))]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · have hz := hIzk Sg (SxI0 (A := A) γ) (stwI (A := A) γ.1) (hS γ) (stwI_rel γ.1) none
      (fun σ o g s => F0A (A.adv σ) PI PS b₁ b₂ γ (outI (A := A) γ.1 σ o) g s)
      fun σ => ⟨fun o s => rd3_viewRA0 (hA σ) (hI σ) b₁ b₂ _ _ _ _ _ _,
        fun o g => rd5_viewRA (hA σ) (hI σ) b₁ b₂ (fun _ => outI (A := A) γ.1 σ o)
          (issRealR (A.adv σ).toRO PI γ.2.1).out g γ.2.1.2.2 γ.2.2.1.2.2 γ.2.2.2.2.2
          (spRealR (A.adv σ).toRO PS γ.2.2.1).out (spRealR (A.adv σ).toRO PS γ.2.2.2).out (Rd5.const _)
          (rd5_issRealR hPI5 _) (rd5_spRealR hPS5 _) (rd5_spRealR hPS5 _),
        fun o g => rdE_viewRA (hA σ) (hI σ) b₁ b₂ (fun _ => outI (A := A) γ.1 σ o)
          (issRealR (A.adv σ).toRO PI γ.2.1).out g γ.2.1.2.2 γ.2.2.1.2.2 γ.2.2.2.2.2
          (spRealR (A.adv σ).toRO PS γ.2.2.1).out (spRealR (A.adv σ).toRO PS γ.2.2.2).out (RdE.const _)
          (rdE_issRealR hPIE _) (rdE_spRealR hPSE _) (rdE_spRealR hPSE _)⟩
    refine le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun a => ?_)
      (pr_congr fun a => ?_)) hz
    · rw [issRealR_outI (A := A) (PI := PI) γ.1 _ (a.1, a.2.1) a.2.2]
    · rw [issSim_outI (A := A) (simI := simI) γ.1 _ a.1, PIR_progSim (A := A) (progI := progI)]

/-- **The collision term of hop 1**: issuance `1`'s real proof (of the statement at the state read
off the tables) on the tables programmed by issuance `0`'s simulation differs from the proof on
the original tables. -/
noncomputable def deltaI1RK [Fintype CI] : ℝ :=
  pr ((TIsR CI × (NRR × (TRe × TRe))) × (Coins 16 × (Tab3 × ShR R))) fun z =>
    (issRealR (A.adv (SxI1 (A := A) z.1 z.2.2)).toRO PI (z.1.2.1, (z.2.1, z.2.2.1))).out
        (PIR (A.adv (SxI1 (A := A) z.1 z.2.2)).toRO progI z.1.1.1 z.1.1.2.1 z.2.2.2) ≠
      (issRealR (A.adv (SxI1 (A := A) z.1 z.2.2)).toRO PI (z.1.2.1, (z.2.1, z.2.2.1))).out z.2.2.2

theorem hopI1RAK [Fintype CI] [Nonempty CI] (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) r5) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE)
    {AdmS : (X : Type) → (Tab3 × ShR R → X) → Prop}
    (hS : ∀ γ : TIsR CI × (NRR × (TRe × TRe)), AdmS Sg (SxI1 (A := A) γ))
    {ε : ℝ} (hIzk : ZeroKnowledgeROA IssueRel
      (fun x w (ρ : Coins 16) g s => PI x w (vec ρ) g s) simI progI AdmS
      (Budget pI (i3 + i3 + q3) (0 + (0 + (i5 + (r5 + (i5 + (r5 + q5))))) + m5)
        (0 + (0 + (iE + (rE + (iE + (rE + qE))))) + mE)) ε)
    (b₁ b₂ : Bool) :
    |pr _ (gameRAK A b₁ b₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
        (fun σ => issRealR (A.adv σ).toRO PI) (fun σ => spRealR (A.adv σ).toRO PS)
        (fun σ => spRealR (A.adv σ).toRO PS)) -
      pr _ (gameRAK A b₁ b₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
        (fun σ => issSimR (A.adv σ).toRO simI progI) (fun σ => spRealR (A.adv σ).toRO PS)
        (fun σ => spRealR (A.adv σ).toRO PS))| ≤ ε + deltaI1RK (A := A) (progI := progI) (PI := PI) := by
  have h := hop_roA (Γ := TIsR CI × (NRR × (TRe × TRe))) (ρ := Coins 16) (G := Tab3) (C := CI)
    (S := ShR R) (SxI1 (A := A))
    (fun γ σ ρ g s => (issRealR (A.adv σ).toRO PI (γ.2.1, (ρ, g))).out s)
    (fun γ σ c => issSim (A.adv σ).toRO.base simI (γ.2.1.1, γ.2.1.2, c))
    (fun γ σ c s => PIR (A.adv σ).toRO progI γ.2.1 c s)
    (fun γ σ s => PIR (A.adv σ).toRO progI γ.1.1 γ.1.2.1 s)
    (fun γ σ => F1A (A.adv σ) simI PS b₁ b₂ γ) (ε := ε) fun γ => ?_
  · rw [← pr_equiv eqv1RK (gameRAK A b₁ b₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
        (fun σ => issRealR (A.adv σ).toRO PI) (fun σ => spRealR (A.adv σ).toRO PS)
        (fun σ => spRealR (A.adv σ).toRO PS)),
      ← pr_equiv eqv1RK (gameRAK A b₁ b₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
        (fun σ => issSimR (A.adv σ).toRO simI progI) (fun σ => spRealR (A.adv σ).toRO PS)
        (fun σ => spRealR (A.adv σ).toRO PS))]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · have hz := hIzk Sg (SxI1 (A := A) γ) (stwI (A := A) γ.2.1) (hS γ) (stwI_rel γ.2.1) none
      (fun σ o g s => F1A (A.adv σ) simI PS b₁ b₂ γ (outI (A := A) γ.2.1 σ o) g
        (PIR (A.adv σ).toRO progI γ.1.1 γ.1.2.1 s))
      fun σ => ⟨fun o s => rd3_viewRA1 (hA σ) (hI σ) b₁ b₂ _ _ _ _ _ _,
        fun o g => (rd5_viewRA (hA σ) (hI σ) b₁ b₂ (noProgI (A.adv σ).toRO simI γ.1).out
          (fun _ => outI (A := A) γ.2.1 σ o) γ.1.2.2 g γ.2.2.1.2.2 γ.2.2.2.2.2
          (spRealR (A.adv σ).toRO PS γ.2.2.1).out (spRealR (A.adv σ).toRO PS γ.2.2.2).out
          (Rd5.const _) (Rd5.const _) (rd5_spRealR hPS5 _) (rd5_spRealR hPS5 _)).comp_prog
            (isProg_PIR (A := (A.adv σ).toRO) hpI _ _),
        fun o g => (rdE_viewRA (hA σ) (hI σ) b₁ b₂ (noProgI (A.adv σ).toRO simI γ.1).out
          (fun _ => outI (A := A) γ.2.1 σ o) γ.1.2.2 g γ.2.2.1.2.2 γ.2.2.2.2.2
          (spRealR (A.adv σ).toRO PS γ.2.2.1).out (spRealR (A.adv σ).toRO PS γ.2.2.2).out
          (RdE.const _) (RdE.const _) (rdE_spRealR hPSE _) (rdE_spRealR hPSE _)).comp_prog
            (isProg_PIR (A := (A.adv σ).toRO) hpI _ _)⟩
    refine le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun a => ?_)
      (pr_congr fun a => ?_)) hz
    · rw [issRealR_outI (A := A) (PI := PI) γ.2.1 _ (a.1, a.2.1) a.2.2]
    · rw [issSim_outI (A := A) (simI := simI) γ.2.1 _ a.1,
        PIR_progSim (A := A) (progI := progI) γ.2.1]

end HopsI

/-! ## The spend hops: the messages read through the setup -/

section HopS1

variable {A} {CI CS : Type} {simI : IssueInstance → CI → Option (IssueProof Z)}
  {simS : SpendInstance → CS → Option (SpendProof Z)}
  {progI : IssueInstance → CI → ShR R → ShR R} {progS : SpendInstance → CS → ShR R → ShR R}
  {PS : ProverS R Z} {q3 q5 qE i3 i2 i5 iE r5 rE m5 mE : ℕ}

/-- The state in hop S1, read off round 1's slice and the shared tables. -/
abbrev σS1 (γ : ΓS1 CI) (t : Tab3 × ShR R) : Sg :=
  A.setup ((γ.1.1.1.2.2, γ.1.1.2.2.2), (t.1, γ.2.2.2)) t.2

variable (A simI progI) in
/-- **The state and the stage-1 messages in hop S1**: the setup on the original tables, stage 1
through the issuance simulations' programming. -/
def Sx1K (γ : ΓS1 CI) (t : Tab3 × ShR R) : Sg × M₁ :=
  (σS1 (A := A) γ t, Sx1 (A.adv (σS1 (A := A) γ t)) simI progI γ t)

variable (A simI progI PS) in
/-- **The collision term of hop S1**: round 1's real proof (of the statement read off the tables
through the setup) on the tables programmed by the issuance simulations differs from the one on
the original tables. -/
noncomputable def deltaS1AK [Fintype CI] (b₁ : Bool) : ℝ :=
  pr (ΓS1 CI × (Coins 16 × (Tab3 × ShR R))) fun z =>
    PS1 (A.adv (Sx1K A simI progI z.1 z.2.2).1) simI PS b₁ z.1 (Sx1K A simI progI z.1 z.2.2).2 z.2.1
        z.2.2.1 (PI2R (A.adv (Sx1K A simI progI z.1 z.2.2).1).toRO progI z.1.1 z.2.2.2) ≠
      PS1 (A.adv (Sx1K A simI progI z.1 z.2.2).1) simI PS b₁ z.1 (Sx1K A simI progI z.1 z.2.2).2 z.2.1
        z.2.2.1 z.2.2.2

set_option maxHeartbeats 600000 in
theorem hopS1RAK [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS] (hA : A.GBudget q3 q5 qE)
    (hI : A.IBudget i3 i2 i5 iE)
    (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) r5) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE)
    {AdmS : (X : Type) → (Tab3 × ShR R → X) → Prop}
    (hS : ∀ γ : ΓS1 CI, AdmS (Sg × M₁) (Sx1K A simI progI γ))
    {ε : ℝ} (hR : ZeroKnowledgeROA SpendRel
      (fun x w (ρ : Coins 16) g s => PS x w (vec ρ) g s) simS progS AdmS
      (Budget pS (i3 + q3) (i5 + (0 + (0 + (0 + (r5 + q5)))) + (m5 + m5))
        (iE + (0 + (0 + (0 + (rE + qE)))) + (mE + mE))) ε)
    (b₁ b₂ : Bool) :
    |pr _ (gameRAK A b₁ b₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
        (fun σ => issSimR (A.adv σ).toRO simI progI) (fun σ => spRealR (A.adv σ).toRO PS)
        (fun σ => spRealR (A.adv σ).toRO PS)) -
      pr _ (gameRAK A b₁ b₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
        (fun σ => issSimR (A.adv σ).toRO simI progI) (fun σ => spSimR (A.adv σ).toRO simS progS)
        (fun σ => spRealR (A.adv σ).toRO PS))| ≤
      ε + deltaS1AK A simI progI PS b₁ := by
  have h := hop_roA (Γ := ΓS1 CI) (ρ := Coins 16) (G := Tab3) (C := CS) (S := ShR R)
    (Sx1K A simI progI) (fun γ x => PS1 (A.adv x.1) simI PS b₁ γ x.2)
    (fun γ x => SmS1 (A.adv x.1) simI simS b₁ γ x.2) (fun γ x => progS1 (A.adv x.1) simI progS b₁ γ x.2)
    (fun γ x s => PI2R (A.adv x.1).toRO progI γ.1 s)
    (fun γ x => FS1A (A.adv x.1) simI PS b₁ b₂ γ x.2) (ε := ε) fun γ => ?_
  · -- From the hop to the games.
    let e : (((TIsR CI × TIsR CI) × ((NRR × (Coins 16 × Tab3)) × TRe)) × ShR R) ≃
        (ΓS1 CI × (Coins 16 × (Tab3 × ShR R))) :=
      { toFun := fun z => (((z.1.1, z.1.2.1.1), z.1.2.2), (z.1.2.1.2.1, (z.1.2.1.2.2, z.2)))
        invFun := fun z => ((z.1.1.1, ((z.1.1.2, (z.2.1, z.2.2.1)), z.1.2)), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let e' : (((TIsR CI × TIsR CI) × ((NRR × (CS × Tab3)) × TRe)) × ShR R) ≃
        (ΓS1 CI × (CS × (Tab3 × ShR R))) :=
      { toFun := fun z => (((z.1.1, z.1.2.1.1), z.1.2.2), (z.1.2.1.2.1, (z.1.2.1.2.2, z.2)))
        invFun := fun z => ((z.1.1.1, ((z.1.1.2, (z.2.1, z.2.2.1)), z.1.2)), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e1 : pr _ (gameRAK A b₁ b₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
        (fun σ => issSimR (A.adv σ).toRO simI progI) (fun σ => spRealR (A.adv σ).toRO PS)
        (fun σ => spRealR (A.adv σ).toRO PS)) =
        pr (ΓS1 CI × (Coins 16 × (Tab3 × ShR R))) (fun z =>
          FS1A (A.adv (Sx1K A simI progI z.1 z.2.2).1) simI PS b₁ b₂ z.1 (Sx1K A simI progI z.1 z.2.2).2
            (PS1 (A.adv (Sx1K A simI progI z.1 z.2.2).1) simI PS b₁ z.1 (Sx1K A simI progI z.1 z.2.2).2
              z.2.1 z.2.2.1 (PI2R (A.adv (Sx1K A simI progI z.1 z.2.2).1).toRO progI z.1.1 z.2.2.2))
            z.2.2.1 (PI2R (A.adv (Sx1K A simI progI z.1 z.2.2).1).toRO progI z.1.1 z.2.2.2)) := by
      rw [← pr_equiv e.symm]
      exact pr_congr fun z => Iff.rfl
    have e2 : pr _ (gameRAK A b₁ b₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
        (fun σ => issSimR (A.adv σ).toRO simI progI) (fun σ => spSimR (A.adv σ).toRO simS progS)
        (fun σ => spRealR (A.adv σ).toRO PS)) =
        pr (ΓS1 CI × (CS × (Tab3 × ShR R))) (fun z =>
          FS1A (A.adv (Sx1K A simI progI z.1 z.2.2).1) simI PS b₁ b₂ z.1 (Sx1K A simI progI z.1 z.2.2).2
            (SmS1 (A.adv (Sx1K A simI progI z.1 z.2.2).1) simI simS b₁ z.1
              (Sx1K A simI progI z.1 z.2.2).2 z.2.1) z.2.2.1
            (PI2R (A.adv (Sx1K A simI progI z.1 z.2.2).1).toRO progI z.1.1
              (progS1 (A.adv (Sx1K A simI progI z.1 z.2.2).1) simI progS b₁ z.1
                (Sx1K A simI progI z.1 z.2.2).2 z.2.1 z.2.2.2))) := by
      rw [← pr_equiv e'.symm]
      exact pr_congr fun z => Iff.rfl
    rw [e1, e2]
    exact h
  · -- The zero-knowledge step, from `ZeroKnowledgeROA`.
    have hz := hR (Sg × M₁) (Sx1K A simI progI γ) (fun x => stwS1 (A.adv x.1) simI b₁ γ x.2) (hS γ)
      (fun x => stwS1_rel (A := A.adv x.1) (simI := simI) b₁ γ x.2) none
      (fun x o g s => FS1A (A.adv x.1) simI PS b₁ b₂ γ x.2
        (spOfProof (A.adv x.1).toRO γ.1.2 (τ1A (A.adv x.1) simI b₁ γ.1 x.2) x.2.2
          ((clientCheck (τ1A (A.adv x.1) simI b₁ γ.1 x.2).t (τ1A (A.adv x.1) simI b₁ γ.1 x.2).x
            x.2.2).getD 0) o) g
        (PI2R (A.adv x.1).toRO progI γ.1 s))
      fun x => by
        have hL : IsProg (PI2R (A.adv x.1).toRO progI γ.1) (m5 + m5) (mE + mE) :=
          (isProg_PIR hpI _ _).comp (isProg_PIR hpI _ _)
        exact ⟨fun o s => Rd3.bind
          (m := fun g => trans₂ (A.adv x.1) b₁ ((γ.1.1.1.2.2, γ.1.1.2.2.2), (g, γ.2.2.2)) x.2
            (noProgI (A.adv x.1).toRO simI γ.1.1.1).out (fun t => t)
            (noProgI (A.adv x.1).toRO simI γ.1.1.2).out
            (fun t => t) (fun _ _ _ => spOfProof (A.adv x.1).toRO γ.1.2 (τ1A (A.adv x.1) simI b₁ γ.1 x.2)
              x.2.2 ((clientCheck (τ1A (A.adv x.1) simI b₁ γ.1 x.2).t
                (τ1A (A.adv x.1) simI b₁ γ.1 x.2).x x.2.2).getD 0) o)
            (fun _ _ _ t => t) (PI2R (A.adv x.1).toRO progI γ.1 s))
          (f := fun m₂ g => viewR ((A.adv x.1).fixR (x.2, m₂)) b₁ b₂
            (noProgI (A.adv x.1).toRO simI γ.1.1.1)
            (noProgI (A.adv x.1).toRO simI γ.1.1.2) (fakeS (spOfProof (A.adv x.1).toRO γ.1.2
              (τ1A (A.adv x.1) simI b₁ γ.1 x.2) x.2.2
              ((clientCheck (τ1A (A.adv x.1) simI b₁ γ.1 x.2).t
                (τ1A (A.adv x.1) simI b₁ γ.1 x.2).x x.2.2).getD 0) o) g)
            (spRealR (A.adv x.1).toRO PS γ.2) (PI2R (A.adv x.1).toRO progI γ.1 s))
          (rd3_trans₂ (σ := fun g => ((γ.1.1.1.2.2, γ.1.1.2.2.2), (g, γ.2.2.2)))
            (fun _ _ u => SReads.rd3 ((hI x.1).b2 _ _ _ _ _) u) _ _ _ _ _ _ _ _ _)
          fun m₂ => rd3_viewR2 (hA x.1 _) b₁ b₂ _ _ _ _ _ _,
        fun o g => (Rd5.bind
          (m := fun u => trans₂ (A.adv x.1) b₁ ((γ.1.1.1.2.2, γ.1.1.2.2.2), (g, γ.2.2.2)) x.2
            (noProgI (A.adv x.1).toRO simI γ.1.1.1).out (fun t => t)
            (noProgI (A.adv x.1).toRO simI γ.1.1.2).out
            (fun t => t) (fun _ _ _ => spOfProof (A.adv x.1).toRO γ.1.2 (τ1A (A.adv x.1) simI b₁ γ.1 x.2)
              x.2.2 ((clientCheck (τ1A (A.adv x.1) simI b₁ γ.1 x.2).t
                (τ1A (A.adv x.1) simI b₁ γ.1 x.2).x x.2.2).getD 0) o)
            (fun _ _ _ t => t) u)
          (f := fun m₂ u => viewR ((A.adv x.1).fixR (x.2, m₂)) b₁ b₂
            (noProgI (A.adv x.1).toRO simI γ.1.1.1)
            (noProgI (A.adv x.1).toRO simI γ.1.1.2) (fakeS (spOfProof (A.adv x.1).toRO γ.1.2
              (τ1A (A.adv x.1) simI b₁ γ.1 x.2) x.2.2
              ((clientCheck (τ1A (A.adv x.1) simI b₁ γ.1 x.2).t
                (τ1A (A.adv x.1) simI b₁ γ.1 x.2).x x.2.2).getD 0) o) g)
            (spRealR (A.adv x.1).toRO PS γ.2) u)
          (SReads.rd5 ((hI x.1).b0 ((i₀R (A.adv x.1).toRO simI γ.1).req, (i₁R (A.adv x.1).toRO simI γ.1).req)
            (spOfProof (A.adv x.1).toRO γ.1.2 (τ1A (A.adv x.1) simI b₁ γ.1 x.2) x.2.2
              ((clientCheck (τ1A (A.adv x.1) simI b₁ γ.1 x.2).t
                (τ1A (A.adv x.1) simI b₁ γ.1 x.2).x x.2.2).getD 0) o).req
            γ.1.1.2.2.2 g γ.2.2.2) γ.1.1.1.2.2) fun m₂ =>
            rd5_viewR (hA x.1 _) b₁ b₂ _ _ _ _ _ _ _ _ (Rd5.const _) (Rd5.const _)
              (fun _ _ => Rd5.const _) (rd5_spRealR hPS5 _)).comp_prog hL,
        fun o g => (RdE.bind
          (m := fun u => trans₂ (A.adv x.1) b₁ ((γ.1.1.1.2.2, γ.1.1.2.2.2), (g, γ.2.2.2)) x.2
            (noProgI (A.adv x.1).toRO simI γ.1.1.1).out (fun t => t)
            (noProgI (A.adv x.1).toRO simI γ.1.1.2).out
            (fun t => t) (fun _ _ _ => spOfProof (A.adv x.1).toRO γ.1.2 (τ1A (A.adv x.1) simI b₁ γ.1 x.2)
              x.2.2 ((clientCheck (τ1A (A.adv x.1) simI b₁ γ.1 x.2).t
                (τ1A (A.adv x.1) simI b₁ γ.1 x.2).x x.2.2).getD 0) o)
            (fun _ _ _ t => t) u)
          (f := fun m₂ u => viewR ((A.adv x.1).fixR (x.2, m₂)) b₁ b₂
            (noProgI (A.adv x.1).toRO simI γ.1.1.1)
            (noProgI (A.adv x.1).toRO simI γ.1.1.2) (fakeS (spOfProof (A.adv x.1).toRO γ.1.2
              (τ1A (A.adv x.1) simI b₁ γ.1 x.2) x.2.2
              ((clientCheck (τ1A (A.adv x.1) simI b₁ γ.1 x.2).t
                (τ1A (A.adv x.1) simI b₁ γ.1 x.2).x x.2.2).getD 0) o) g)
            (spRealR (A.adv x.1).toRO PS γ.2) u)
          (SReads.rdE ((hI x.1).b0 ((i₀R (A.adv x.1).toRO simI γ.1).req, (i₁R (A.adv x.1).toRO simI γ.1).req)
            (spOfProof (A.adv x.1).toRO γ.1.2 (τ1A (A.adv x.1) simI b₁ γ.1 x.2) x.2.2
              ((clientCheck (τ1A (A.adv x.1) simI b₁ γ.1 x.2).t
                (τ1A (A.adv x.1) simI b₁ γ.1 x.2).x x.2.2).getD 0) o).req
            γ.1.1.2.2.2 g γ.2.2.2) γ.1.1.1.2.2) fun m₂ =>
            rdE_viewR (hA x.1 _) b₁ b₂ _ _ _ _ _ _ _ _ (RdE.const _) (RdE.const _)
              (fun _ _ => RdE.const _) (rdE_spRealR hPSE _)).comp_prog hL⟩
    refine le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun a => ?_)
      (pr_congr fun a => ?_)) hz
    · unfold outReal stwS1
      beta_reduce
      split_ifs with hok
      · obtain ⟨hv, t', hc⟩ := ok1A_valid b₁ γ.1 (Sx1K A simI progI γ a.2).2 hok
        simp only [Option.elim, hc, Option.getD_some]
        unfold PS1
        rw [spRealR_out_ok _ hv hc]
      · exact FS1A_not_ok b₁ b₂ _ _ (Bool.of_not_eq_true hok) _ _ _ _
    · unfold outSim progSim stwS1 progS1
      beta_reduce
      split_ifs with hok
      · obtain ⟨hv, t', hc⟩ := ok1A_valid b₁ γ.1 (Sx1K A simI progI γ a.2).2 hok
        simp only [Option.elim, hc, Option.getD_some]
        unfold SmS1
        rw [spSim_ok _ _ hv hc]
      · exact FS1A_not_ok b₁ b₂ _ _ (Bool.of_not_eq_true hok) _ _ _ _

end HopS1

section HopS2

variable {A} {CI CS : Type} {simI : IssueInstance → CI → Option (IssueProof Z)}
  {simS : SpendInstance → CS → Option (SpendProof Z)}
  {progI : IssueInstance → CI → ShR R → ShR R} {progS : SpendInstance → CS → ShR R → ShR R}
  {PS : ProverS R Z} {q3 q5 qE i3 i2 i5 iE r5 rE m5 mE : ℕ}

/-- The state in hop S2, read off round 2's slice and the shared tables. -/
abbrev σS2 (γ : ΓS2 CI CS) (t : Tab3 × ShR R) : Sg :=
  A.setup ((γ.1.1.1.2.2, γ.1.1.2.2.2), (γ.1.2.2.2, t.1)) t.2

variable (A simI simS progI progS) in
/-- **The state and the transcript in hop S2.** -/
def Sx2K (b₁ : Bool) (γ : ΓS2 CI CS) (t : Tab3 × ShR R) : Sg × MsgR :=
  (σS2 (A := A) γ t, Sx2 (A.adv (σS2 (A := A) γ t)) simI simS progI progS b₁ γ t)

variable (A simI simS progI progS PS) in
/-- **The collision term of hop S2**: round 2's real proof on the tables programmed by the other
three simulations differs from the one on the original tables. -/
noncomputable def deltaS2AK [Fintype CI] [Fintype CS] (b₁ b₂ : Bool) : ℝ :=
  pr (ΓS2 CI CS × (Coins 16 × (Tab3 × ShR R))) fun z =>
    PS2 (A.adv (Sx2K A simI simS progI progS b₁ z.1 z.2.2).1) simI simS PS b₁ b₂ z.1
        (Sx2K A simI simS progI progS b₁ z.1 z.2.2).2 z.2.1 z.2.2.1
        (LS2R ((A.adv (Sx2K A simI simS progI progS b₁ z.1 z.2.2).1).fixR
          (Sx2K A simI simS progI progS b₁ z.1 z.2.2).2) simI progI progS b₁ z.1 z.2.2.2) ≠
      PS2 (A.adv (Sx2K A simI simS progI progS b₁ z.1 z.2.2).1) simI simS PS b₁ b₂ z.1
        (Sx2K A simI simS progI progS b₁ z.1 z.2.2).2 z.2.1 z.2.2.1 z.2.2.2

set_option maxHeartbeats 600000 in
theorem hopS2RAK [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS] (hA : A.GBudget q3 q5 qE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpS : ∀ x c, IsProg (progS x c) m5 mE) (b₁ : Bool)
    {AdmS : (X : Type) → (Tab3 × ShR R → X) → Prop}
    (hS : ∀ γ : ΓS2 CI CS, AdmS (Sg × MsgR) (Sx2K A simI simS progI progS b₁ γ))
    {ε : ℝ} (hR : ZeroKnowledgeROA SpendRel
      (fun x w (ρ : Coins 16) g s => PS x w (vec ρ) g s) simS progS AdmS
      (Budget pS q3 (0 + (0 + (0 + (0 + q5))) + (m5 + (m5 + m5)))
        (0 + (0 + (0 + (0 + qE))) + (mE + (mE + mE)))) ε)
    (b₂ : Bool) :
    |pr _ (gameRAK A b₁ b₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
        (fun σ => issSimR (A.adv σ).toRO simI progI) (fun σ => spSimR (A.adv σ).toRO simS progS)
        (fun σ => spRealR (A.adv σ).toRO PS)) -
      pr _ (simGameRAK A simI simS progI progS b₁ b₂)| ≤
      ε + deltaS2AK A simI simS progI progS PS b₁ b₂ := by
  have h := hop_roA (Γ := ΓS2 CI CS) (ρ := Coins 16) (G := Tab3) (C := CS) (S := ShR R)
    (Sx2K A simI simS progI progS b₁) (fun γ x => PS2 (A.adv x.1) simI simS PS b₁ b₂ γ x.2)
    (fun γ x => SmS2 (A.adv x.1) simI simS b₁ b₂ γ x.2)
    (fun γ x => progS2 (A.adv x.1) simI simS progS b₁ b₂ γ x.2)
    (fun γ x s => LS2R ((A.adv x.1).fixR x.2) simI progI progS b₁ γ s)
    (fun γ x => FS2R ((A.adv x.1).fixR x.2) simI simS b₁ b₂ γ) (ε := ε) fun γ => ?_
  · -- From the hop to the games.
    let e : (((TIsR CI × TIsR CI) × (TSsR CS × (NRR × (Coins 16 × Tab3)))) × ShR R) ≃
        (ΓS2 CI CS × (Coins 16 × (Tab3 × ShR R))) :=
      { toFun := fun z => (((z.1.1, z.1.2.1), z.1.2.2.1), (z.1.2.2.2.1, (z.1.2.2.2.2, z.2)))
        invFun := fun z => ((z.1.1.1, (z.1.1.2, (z.1.2, (z.2.1, z.2.2.1)))), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let e' : (((TIsR CI × TIsR CI) × (TSsR CS × (NRR × (CS × Tab3)))) × ShR R) ≃
        (ΓS2 CI CS × (CS × (Tab3 × ShR R))) :=
      { toFun := fun z => (((z.1.1, z.1.2.1), z.1.2.2.1), (z.1.2.2.2.1, (z.1.2.2.2.2, z.2)))
        invFun := fun z => ((z.1.1.1, (z.1.1.2, (z.1.2, (z.2.1, z.2.2.1)))), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e1 : pr _ (gameRAK A b₁ b₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
        (fun σ => issSimR (A.adv σ).toRO simI progI) (fun σ => spSimR (A.adv σ).toRO simS progS)
        (fun σ => spRealR (A.adv σ).toRO PS)) =
        pr (ΓS2 CI CS × (Coins 16 × (Tab3 × ShR R))) (fun z =>
          FS2R ((A.adv (Sx2K A simI simS progI progS b₁ z.1 z.2.2).1).fixR
              (Sx2K A simI simS progI progS b₁ z.1 z.2.2).2) simI simS b₁ b₂ z.1
            (PS2 (A.adv (Sx2K A simI simS progI progS b₁ z.1 z.2.2).1) simI simS PS b₁ b₂ z.1
              (Sx2K A simI simS progI progS b₁ z.1 z.2.2).2 z.2.1 z.2.2.1
              (LS2R ((A.adv (Sx2K A simI simS progI progS b₁ z.1 z.2.2).1).fixR
                (Sx2K A simI simS progI progS b₁ z.1 z.2.2).2) simI progI progS b₁ z.1 z.2.2.2))
            z.2.2.1
            (LS2R ((A.adv (Sx2K A simI simS progI progS b₁ z.1 z.2.2).1).fixR
              (Sx2K A simI simS progI progS b₁ z.1 z.2.2).2) simI progI progS b₁ z.1 z.2.2.2)) := by
      rw [← pr_equiv e.symm]
      exact pr_congr fun z => Iff.rfl
    have e2 : pr _ (simGameRAK A simI simS progI progS b₁ b₂) =
        pr (ΓS2 CI CS × (CS × (Tab3 × ShR R))) (fun z =>
          FS2R ((A.adv (Sx2K A simI simS progI progS b₁ z.1 z.2.2).1).fixR
              (Sx2K A simI simS progI progS b₁ z.1 z.2.2).2) simI simS b₁ b₂ z.1
            (SmS2 (A.adv (Sx2K A simI simS progI progS b₁ z.1 z.2.2).1) simI simS b₁ b₂ z.1
              (Sx2K A simI simS progI progS b₁ z.1 z.2.2).2 z.2.1) z.2.2.1
            (LS2R ((A.adv (Sx2K A simI simS progI progS b₁ z.1 z.2.2).1).fixR
                (Sx2K A simI simS progI progS b₁ z.1 z.2.2).2) simI progI progS b₁ z.1
              (progS2 (A.adv (Sx2K A simI simS progI progS b₁ z.1 z.2.2).1) simI simS progS b₁ b₂ z.1
                (Sx2K A simI simS progI progS b₁ z.1 z.2.2).2 z.2.1 z.2.2.2))) := by
      rw [← pr_equiv e'.symm]
      exact pr_congr fun z => Iff.rfl
    rw [e1, e2]
    exact h
  · -- The zero-knowledge step, from `ZeroKnowledgeROA`.
    have hz := hR (Sg × MsgR) (Sx2K A simI simS progI progS b₁ γ)
      (fun x => stwS2 (A.adv x.1) simI simS b₁ b₂ γ x.2) (hS γ)
      (fun x => stwS2_rel (A := A.adv x.1) (simI := simI) (simS := simS) b₁ b₂ γ x.2) none
      (fun x o g s => FS2R ((A.adv x.1).fixR x.2) simI simS b₁ b₂ γ
        (spOfProof (A.adv x.1).toRO γ.2 (τ₂R ((A.adv x.1).fixR x.2) simI simS b₁ b₂ γ)
          (d₂R ((A.adv x.1).fixR x.2) simI simS b₁ γ)
          ((clientCheck (τ₂R ((A.adv x.1).fixR x.2) simI simS b₁ b₂ γ).t
            (τ₂R ((A.adv x.1).fixR x.2) simI simS b₁ b₂ γ).x
            (d₂R ((A.adv x.1).fixR x.2) simI simS b₁ γ)).getD 0) o) g
        (LS2R ((A.adv x.1).fixR x.2) simI progI progS b₁ γ s))
      fun x => by
        have hL : IsProg (LS2R ((A.adv x.1).fixR x.2) simI progI progS b₁ γ) (m5 + (m5 + m5))
            (mE + (mE + mE)) :=
          (isProg_PIR hpI _ _).comp ((isProg_PIR hpI _ _).comp (IsProg.ite _ (hpS _ _)
            (IsProg.id.mono (Nat.zero_le _) (Nat.zero_le _))))
        exact ⟨fun o s => rd3_viewR3 (hA x.1 x.2) b₁ b₂ _ _ _ _ _ _,
          fun o g => (rd5_viewR (hA x.1 x.2) b₁ b₂ (noProgI ((A.adv x.1).fixR x.2) simI γ.1.1.1).out
            (noProgI ((A.adv x.1).fixR x.2) simI γ.1.1.2).out γ.1.1.1.2.2 γ.1.1.2.2.2 γ.1.2.2.2 g
            (noProgS ((A.adv x.1).fixR x.2) simS γ.1.2).out _ (Rd5.const _) (Rd5.const _)
            (fun _ _ => Rd5.const _) (fun _ _ => Rd5.const _)).comp_prog hL,
          fun o g => (rdE_viewR (hA x.1 x.2) b₁ b₂ (noProgI ((A.adv x.1).fixR x.2) simI γ.1.1.1).out
            (noProgI ((A.adv x.1).fixR x.2) simI γ.1.1.2).out γ.1.1.1.2.2 γ.1.1.2.2.2 γ.1.2.2.2 g
            (noProgS ((A.adv x.1).fixR x.2) simS γ.1.2).out _ (RdE.const _) (RdE.const _)
            (fun _ _ => RdE.const _) (fun _ _ => RdE.const _)).comp_prog hL⟩
    refine le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun a => ?_)
      (pr_congr fun a => ?_)) hz
    · unfold outReal stwS2
      beta_reduce
      split_ifs with hok
      · obtain ⟨hv, t', hc⟩ := ok2A_valid b₁ b₂ γ (Sx2K A simI simS progI progS b₁ γ a.2).2 hok
        simp only [Option.elim, hc, Option.getD_some]
        unfold PS2
        rw [spRealR_out_ok _ hv hc]
      · exact FS2R_not_ok b₁ b₂ _ _ (Bool.of_not_eq_true hok) _ _ _ _
    · unfold outSim progSim stwS2 progS2
      beta_reduce
      split_ifs with hok
      · obtain ⟨hv, t', hc⟩ := ok2A_valid b₁ b₂ γ (Sx2K A simI simS progI progS b₁ γ a.2).2 hok
        simp only [Option.elim, hc, Option.getD_some]
        unfold SmS2
        rw [spSim_ok _ _ hv hc]
      · exact FS2R_not_ok b₁ b₂ _ _ (Bool.of_not_eq_true hok) _ _ _ _

end HopS2

/-! ## Unlinkability with a table-reading key stage -/

variable {A} {CI CS : Type} {simI : IssueInstance → CI → Option (IssueProof Z)}
  {simS : SpendInstance → CS → Option (SpendProof Z)}
  {progI : IssueInstance → CI → ShR R → ShR R} {progS : SpendInstance → CS → ShR R → ShR R}
  {PI : ProverI R Z} {PS : ProverS R Z} in
/-- **Theorem 2 in the random-oracle and ideal-cipher model, the key stage and the Issuer's
interaction reading the tables, for any proof systems.** As `unlinkabilityRA`, with the issuance
proofs `ZeroKnowledgeROA` for the readers `AdmSI` (which contain the setup read off each issuance
slice and the shared tables) and the spend proofs for `AdmS₁`, `AdmS₂` (which contain the state and
the messages read through the setup and the simulations' programming). -/
theorem unlinkabilityRAK [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS]
    {q3 q5 qE i3 i2 i5 iE r5 rE m5 mE : ℕ} {εI εS₁ εS₂ : ℕ → ℕ → ℕ → ℝ} {εhide : ℝ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPI5 : ∀ x w ρ g, Rd5 (PI x w ρ g) r5) (hPIE : ∀ x w ρ g, RdE (PI x w ρ g) rE)
    (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) r5) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpS : ∀ x c, IsProg (progS x c) m5 mE)
    (hprogI : ∀ x x' c, simI x c = none → progI x c = progI x' c)
    (hprogS : ∀ x x' c, simS x c = none → progS x c = progS x' c)
    {AdmSI AdmS₁ AdmS₂ : (X : Type) → (Tab3 × ShR R → X) → Prop}
    (hSI0 : ∀ γ : NRR × (TRe × (TRe × TRe)), AdmSI Sg (SxI0 (A := A) γ))
    (hSI1 : ∀ γ : TIsR CI × (NRR × (TRe × TRe)), AdmSI Sg (SxI1 (A := A) γ))
    (hS1 : ∀ γ : ΓS1 CI, AdmS₁ (Sg × M₁) (Sx1K A simI progI γ))
    (hS2 : ∀ b₁ (γ : ΓS2 CI CS), AdmS₂ (Sg × MsgR) (Sx2K A simI simS progI progS b₁ γ))
    (hIzk : ∀ a b c, ZeroKnowledgeROA IssueRel (fun x w (ρ : Coins 16) g s => PI x w (vec ρ) g s)
      simI progI AdmSI (Budget pI a b c) (εI a b c))
    (hSzk₁ : ∀ a b c, ZeroKnowledgeROA SpendRel (fun x w (ρ : Coins 16) g s => PS x w (vec ρ) g s)
      simS progS AdmS₁ (Budget pS a b c) (εS₁ a b c))
    (hSzk₂ : ∀ a b c, ZeroKnowledgeROA SpendRel (fun x w (ρ : Coins 16) g s => PS x w (vec ρ) g s)
      simS progS AdmS₂ (Budget pS a b c) (εS₂ a b c))
    (hhide : ∀ b₁ b₂ K, hidingAdv (A.adv (σOfR A K)).ctx
      (reductionRA (A.adv (σOfR A K)) simI simS progI progS b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRAK A PI PS b₁ b₂) - pr _ (realGameRAK A PI PS b₁' b₂')| ≤
      2 * (εI (i3 + i3 + q3) (0 + (r5 + (i5 + (r5 + (i5 + (r5 + q5))))))
            (0 + (rE + (iE + (rE + (iE + (rE + qE)))))) +
          εI (i3 + i3 + q3) (0 + (0 + (i5 + (r5 + (i5 + (r5 + q5))))) + m5)
            (0 + (0 + (iE + (rE + (iE + (rE + qE))))) + mE) +
          εS₁ (i3 + q3) (i5 + (0 + (0 + (0 + (r5 + q5)))) + (m5 + m5))
            (iE + (0 + (0 + (0 + (rE + qE)))) + (mE + mE)) +
          εS₂ q3 (0 + (0 + (0 + (0 + q5))) + (m5 + (m5 + m5)))
            (0 + (0 + (0 + (0 + qE))) + (mE + (mE + mE)))) +
        2 * deltaI1RK (A := A) (progI := progI) (PI := PI) +
        (deltaS1AK A simI progI PS b₁ + deltaS1AK A simI progI PS b₁') +
        (deltaS2AK A simI simS progI progS PS b₁ b₂ + deltaS2AK A simI simS progI progS PS b₁' b₂') +
        2 * εhide := by
  have hw (c₁ c₂ : Bool) : |pr _ (realGameRAK A PI PS c₁ c₂) -
      pr _ (idealGameRAK A simI simS progI progS c₁ c₂)| ≤
      εI (i3 + i3 + q3) (0 + (r5 + (i5 + (r5 + (i5 + (r5 + q5))))))
          (0 + (rE + (iE + (rE + (iE + (rE + qE)))))) +
        (εI (i3 + i3 + q3) (0 + (0 + (i5 + (r5 + (i5 + (r5 + q5))))) + m5)
            (0 + (0 + (iE + (rE + (iE + (rE + qE))))) + mE) +
          deltaI1RK (A := A) (progI := progI) (PI := PI)) +
        (εS₁ (i3 + q3) (i5 + (0 + (0 + (0 + (r5 + q5)))) + (m5 + m5))
            (iE + (0 + (0 + (0 + (rE + qE)))) + (mE + mE)) + deltaS1AK A simI progI PS c₁) +
        (εS₂ q3 (0 + (0 + (0 + (0 + q5))) + (m5 + (m5 + m5)))
            (0 + (0 + (0 + (0 + qE))) + (mE + (mE + mE))) +
          deltaS2AK A simI simS progI progS PS c₁ c₂) + εhide := by
    have h1 := hopI0RAK (A := A) (PI := PI) (PS := PS) (simI := simI) (progI := progI) hA hI hPI5
      hPIE hPS5 hPSE hSI0 (hIzk _ _ _) c₁ c₂
    have h2 := hopI1RAK (A := A) (PI := PI) (PS := PS) (simI := simI) (progI := progI) hA hI hPS5
      hPSE hpI hSI1 (hIzk _ _ _) c₁ c₂
    have h3 := hopS1RAK (A := A) (PS := PS) (simI := simI) (simS := simS) (progI := progI)
      (progS := progS) hA hI hPS5 hPSE hpI hS1 (hSzk₁ _ _ _) c₁ c₂
    have h4 := hopS2RAK (A := A) (PS := PS) (simI := simI) (simS := simS) (progI := progI)
      (progS := progS) hA hpI hpS c₁ (hS2 c₁) (hSzk₂ _ _ _) c₂
    have h5 := hiding_hopRAK A simI simS progI progS hprogI hprogS c₁ c₂ (hhide c₁ c₂)
    unfold realGameRAK
    unfold simGameRAK at h5 h4
    set p0 := pr _ (gameRAK A c₁ c₂ (fun σ => issRealR (A.adv σ).toRO PI)
      (fun σ => issRealR (A.adv σ).toRO PI) (fun σ => spRealR (A.adv σ).toRO PS)
      (fun σ => spRealR (A.adv σ).toRO PS))
    set p1 := pr _ (gameRAK A c₁ c₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
      (fun σ => issRealR (A.adv σ).toRO PI) (fun σ => spRealR (A.adv σ).toRO PS)
      (fun σ => spRealR (A.adv σ).toRO PS))
    set p2 := pr _ (gameRAK A c₁ c₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
      (fun σ => issSimR (A.adv σ).toRO simI progI) (fun σ => spRealR (A.adv σ).toRO PS)
      (fun σ => spRealR (A.adv σ).toRO PS))
    set p3 := pr _ (gameRAK A c₁ c₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
      (fun σ => issSimR (A.adv σ).toRO simI progI) (fun σ => spSimR (A.adv σ).toRO simS progS)
      (fun σ => spRealR (A.adv σ).toRO PS))
    set p4 := pr _ (gameRAK A c₁ c₂ (fun σ => issSimR (A.adv σ).toRO simI progI)
      (fun σ => issSimR (A.adv σ).toRO simI progI) (fun σ => spSimR (A.adv σ).toRO simS progS)
      (fun σ => spSimR (A.adv σ).toRO simS progS))
    set p5 := pr _ (idealGameRAK A simI simS progI progS c₁ c₂)
    have := abs_sub_le p0 p1 p5
    have := abs_sub_le p1 p2 p5
    have := abs_sub_le p2 p3 p5
    have := abs_sub_le p3 p4 p5
    linarith
  have h := hw b₁ b₂
  have h' := hw b₁' b₂'
  rw [idealGameRAK_eq] at h h'
  rw [abs_sub_comm] at h'
  have := abs_sub_le (pr _ (realGameRAK A PI PS b₁ b₂))
    (pr _ (idealGameRAK A simI simS progI progS false false)) (pr _ (realGameRAK A PI PS b₁' b₂'))
  linarith

/-! ## With the Lean prover -/

section Lean

open VoleMole.Verifier VoleMole.Verifier.Bridge

variable [CipherRow R] (A : AdversaryRAK R Sizes.labelRows Sg)

/-- **Adaptive zero knowledge of the Lean issuance prover** (`ZK.Sim.lean_zeroKnowledgeROA`). -/
theorem leanPIR_zkROA [ZKPRow R] (q3 q5 qE s3 s2 s5 sE : ℕ) : ZeroKnowledgeROA IssueRel
    (fun x w (ρ : Coins 16) g (s : ShR R) => leanPIR x w (vec ρ) g s) leanSimIR leanProgIR
    (fun _ Sx => SReads pI Sx s3 s2 s5 sE) (Budget pI q3 q5 qE)
    (εAdG R pI pI.qsDegree q3 q5 qE s3 s2 s5 sE) := by
  have h := lean_zeroKnowledgeROA (R := R) Hashes.shake pI stI (fun _ => rfl) rfl encI IssueRel csI
    zkHypI hashesWF_shake (smallParams_of_le (by decide) (by decide)) q3 q5 qE s3 s2 s5 sE
    (vecOf Sizes.labelRows.issue)
  have e : (fun x w (ρ : Coins 16) g (s : ShR R) => leanPIR x w (vec ρ) g s) =
      fun x w r g s => vecOf _ (realRO pI Hashes.shake (stI x) (encI x w) r g s) := by
    funext x w ρ g s
    exact leanPIR_vec x w ρ g s
  rw [e]
  exact h

/-- **The collision term of hop 1** is still `≤ noHitProb + 2⁻¹⁰²⁴`: issuance `0`'s simulator
coins are independent of the state, of issuance `1`'s tape and of the tables. -/
theorem deltaI1RK_le : deltaI1RK (A := A) (progI := leanProgIR (R := R)) (PI := leanPIR) ≤
    noHitProb + 1 / 2 ^ 1024 := by
  unfold deltaI1RK
  refine (pr_mono (Q := fun z => (A.adv (SxI1 (A := A) z.1 z.2.2)).toRO.tInit ≠ 0 ∧
      preTail (blk (preLen pI) (preRO Hashes.shake
      (stI (xIOf (A.adv (SxI1 (A := A) z.1 z.2.2)).toRO z.1.2.1))
      (encI (xIOf (A.adv (SxI1 (A := A) z.1 z.2.2)).toRO z.1.2.1) ⟨vec z.1.2.1.1, vec z.1.2.1.2⟩)
        z.2.1 z.2.2.1 z.2.2.2)) ∈ ({simTail z.1.1.2.1} : Finset ByteArray)) fun z hz => ?_).trans ?_
  · by_cases hT : (A.adv (SxI1 (A := A) z.1 z.2.2)).toRO.tInit = 0
    · exact absurd (by rw [issRealR_out_zero hT, issRealR_out_zero hT]) hz
    refine ⟨hT, ?_⟩
    rw [issRealR_out_ne hT, issRealR_out_ne hT] at hz
    simp only [PIR, hT, ↓reduceIte, leanPIR_vec] at hz
    have h1 := vecOf_ne fun e => hz (by rw [e])
    have hL := progRO_progAt (R := R) Hashes.shake
      (stI (xIOf (A.adv (SxI1 (A := A) z.1 z.2.2)).toRO z.1.1.1)) z.1.1.2.1
    have hz' := zkHypI (xIOf (A.adv (SxI1 (A := A) z.1 z.2.2)).toRO z.1.2.1)
      ⟨vec z.1.2.1.1, vec z.1.2.1.2⟩ rfl
    have hT' : ∀ s : ShR R, ∀ b ∈ ({simBlk Hashes.shake
        (stI (xIOf (A.adv (SxI1 (A := A) z.1 z.2.2)).toRO z.1.1.1)) z.1.1.2.1 s} :
        Finset (ZK.Sim.Bytes (preLen pI))), preTail b ∈ ({simTail z.1.1.2.1} : Finset ByteArray) := by
      intro s b hb
      rw [Finset.mem_singleton] at hb ⊢
      rw [hb]
      exact preTail_simBlk hashesWF_shake rfl _ _
    exact realRO_ne_tail hz' hashesWF_shake hlab_pI hL hT' _ _ _ h1
  · refine pr_le_of_snd fun y => pr_le_of_snd fun r => pr_le_of_fst fun n =>
      pr_le_of_snd fun g => ?_
    have h := pr_simTail_eq_le (p := pI) (preTail (blk (preLen pI) (preRO Hashes.shake
      (stI (xIOf (A.adv (A.setup ((g, y.2.1), (r.2.1.2.2, r.2.2.2.2)) y.2.2)).toRO r.1))
      (encI (xIOf (A.adv (A.setup ((g, y.2.1), (r.2.1.2.2, r.2.2.2.2)) y.2.2)).toRO r.1)
        ⟨vec r.1.1, vec r.1.2⟩) y.1 y.2.1 y.2.2)))
    rw [tail_pI] at h
    refine le_trans (pr_mono fun c hc => ?_) h
    exact Finset.mem_singleton.1 hc.2

variable {A}

/-- **The state and the stage-1 messages of hop S1 read** `(k₃ + i₃, k₂ + i₂, k₅ + i₅ + 624,
k_E + i_E + 9214)`. -/
lemma sReads_Sx1K {k3 k2 k5 kE i3 i2 i5 iE : ℕ} (hK : A.KBudget k3 k2 k5 kE)
    (hI : A.IBudget i3 i2 i5 iE) (γ : ΓS1 (SimCoins pI)) :
    SReads pS (Sx1K A leanSimIR (leanProgIR (R := R)) γ) (k3 + i3) (k2 + i2)
      (k5 + (i5 + 312 + 312)) (kE + (iE + 4607 + 4607)) :=
  (hK.s2 _ _ _).bind (g := fun σ t => (σ, Sx1 (A.adv σ) leanSimIR leanProgIR γ t))
    fun σ => (sReads_Sx1 (A.adv σ) (hI σ) γ).map fun x => (σ, x)

/-- **The state and the transcript of hop S2 read** `(k₃ + 2i₃, k₂ + 2i₂, k₅ + 2i₅ + 1560,
k_E + 2i_E + 23035)`. -/
lemma sReads_Sx2K {k3 k2 k5 kE i3 i2 i5 iE : ℕ} (hK : A.KBudget k3 k2 k5 kE)
    (hI : A.IBudget i3 i2 i5 iE) (b₁ : Bool) (γ : ΓS2 (SimCoins pI) (SimCoins pS)) :
    SReads pS (Sx2K A leanSimIR leanSimSR (leanProgIR (R := R)) leanProgSR b₁ γ) (k3 + 2 * i3)
      (k2 + 2 * i2) (k5 + (2 * i5 + 1560)) (kE + (2 * iE + 23035)) :=
  (hK.s3 _ _ _).bind
    (g := fun σ t => (σ, Sx2 (A.adv σ) leanSimIR leanSimSR leanProgIR leanProgSR b₁ γ t))
    fun σ => (sReads_Sx2 (A.adv σ) (hI σ) b₁ γ).map fun x => (σ, x)

variable (A)

/-- **The collision term of hop S1**, with the statement read off the tables through the setup:
`δS₁ ≤ (k₃ + i₃)·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607; k₅ + i₅ + 624, k_E + i_E + 9214) + noHitProb
+ 2·2⁻¹⁰²⁴`. -/
theorem deltaS1AK_le [ZKPRow R] {k3 k2 k5 kE i3 i2 i5 iE : ℕ} (hK : A.KBudget k3 k2 k5 kE)
    (hI : A.IBudget i3 i2 i5 iE) (b₁ : Bool) :
    deltaS1AK A leanSimIR leanProgIR leanPSR b₁ ≤
      (k3 + i3 : ℕ) / 2 ^ 128 + (1 / 2 ^ 113 +
        ZKPRow.εP R pS 0 312 4607 (k5 + (i5 + 312 + 312)) (kE + (iE + 4607 + 4607)) +
        (noHitProb + 2 / 2 ^ 1024)) := by
  unfold deltaS1AK
  refine pr_le_of_fst fun γ => ?_
  refine (pr_mono fun z hz => PS1_ne (A.adv (Sx1K A leanSimIR leanProgIR γ z.2).1) b₁ γ _ z.1 z.2.1
    _ _ hz).trans ?_
  refine (pr_collide_adaptive Hashes.shake pS rfl smallParams_pS hashesWF_shake
    (fun x : Sg × M₁ => stwC1 (A.adv x.1) b₁ γ x.2)
    (fun x => csS (xSOf (A.adv x.1).toRO γ.1.2 (τ1A (A.adv x.1) leanSimIR b₁ γ.1 x.2) x.2.2))
    (fun x => stwC1_hyp (A.adv x.1) b₁ γ x.2)
    (Sx1K A leanSimIR leanProgIR γ) (sReads_Sx1K hK hI γ)
    (fun x => PI2R (A.adv x.1).toRO leanProgIR γ.1) _
    (fun x => progAt_PI2R (A.adv x.1).toRO γ.1) _ (fun x => tails_PI2R (A.adv x.1).toRO γ.1)).trans ?_
  have hc : (({simTail γ.1.1.1.2.1, simTail γ.1.1.2.2.1} : Finset ByteArray).card : ℝ) ≤ 2 := by
    exact_mod_cast Finset.card_le_two
  rw [show (8 * (16 * (pS.qsDegree - 1)) : ℕ) = 1024 from rfl]
  gcongr

/-- **The collision term of hop S2**: `δS₂ ≤ (k₃ + 2i₃)·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607;
k₅ + 2i₅ + 1560, k_E + 2i_E + 23035) + noHitProb + 3·2⁻¹⁰²⁴`. -/
theorem deltaS2AK_le [ZKPRow R] {k3 k2 k5 kE i3 i2 i5 iE : ℕ} (hK : A.KBudget k3 k2 k5 kE)
    (hI : A.IBudget i3 i2 i5 iE) (b₁ b₂ : Bool) :
    deltaS2AK A leanSimIR leanSimSR leanProgIR leanProgSR leanPSR b₁ b₂ ≤
      (k3 + 2 * i3 : ℕ) / 2 ^ 128 + (1 / 2 ^ 113 +
        ZKPRow.εP R pS 0 312 4607 (k5 + (2 * i5 + 1560)) (kE + (2 * iE + 23035)) +
        (noHitProb + 3 / 2 ^ 1024)) := by
  unfold deltaS2AK
  refine pr_le_of_fst fun γ => ?_
  refine (pr_mono fun z hz => PS2_ne (A.adv (Sx2K A leanSimIR leanSimSR leanProgIR leanProgSR b₁ γ
    z.2).1) b₁ b₂ γ _ z.1 z.2.1 _ _ hz).trans ?_
  choose Bx hBx using fun x : Sg × MsgR => progAt_LS2R ((A.adv x.1).fixR x.2) b₁ γ
  refine (pr_collide_adaptive Hashes.shake pS rfl smallParams_pS hashesWF_shake
    (fun x : Sg × MsgR => stwC2 (A.adv x.1) b₁ b₂ γ x.2)
    (fun x => csS (xSOf (A.adv x.1).toRO γ.2 (τ₂R ((A.adv x.1).fixR x.2) leanSimIR leanSimSR b₁ b₂ γ)
      (d₂R ((A.adv x.1).fixR x.2) leanSimIR leanSimSR b₁ γ))) (fun x => stwC2_hyp (A.adv x.1) b₁ b₂ γ x.2)
    (Sx2K A leanSimIR leanSimSR leanProgIR leanProgSR b₁ γ) (sReads_Sx2K hK hI b₁ γ)
    (fun x => LS2R ((A.adv x.1).fixR x.2) leanSimIR leanProgIR leanProgSR b₁ γ) Bx
    (fun x => (hBx x).1) _ (fun x => (hBx x).2)).trans ?_
  have hc : (({simTail γ.1.2.2.1, simTail γ.1.1.1.2.1, simTail γ.1.1.2.2.1} :
      Finset ByteArray).card : ℝ) ≤ 3 := by
    exact_mod_cast Finset.card_le_three
  rw [show (8 * (16 * (pS.qsDegree - 1)) : ℕ) = 1024 from rfl]
  gcongr

/-- **Theorem 2 with the Lean prover, the key stage and the Issuer's interaction reading the
tables, for every type of cipher rows** (`ZKRow R`, `ZKPRow R`; `unlinkabilityRAK_lean_num` at
function rows). The guess reads each `H₃` slice at `q₃` keys, `H₅` at `q₅`, the cipher at `q_E` and
`H₂³` freely; each stage of the interaction at every state reads `(i₃, i₂, i₅, i_E)` (`IBudget`);
the key stage reads `(k₃, k₂, k₅, k_E)` (`KBudget`), consistently. Then any two worlds differ by at
most

    4·εAd(9; 2i₃ + q₃, q₅ + 2i₅ + 1872, q_E + 2i_E + 13821; k₃, k₂, k₅, k_E)
      + 2·εAd(9; i₃ + q₃, q₅ + i₅ + 1248, q_E + i_E + 13821;
              k₃ + i₃, k₂ + i₂, k₅ + i₅ + 624, k_E + i_E + 9214)
      + 2·εAd(9; q₃, q₅ + 936, q_E + 13821; k₃ + 2i₃, k₂ + 2i₂, k₅ + 2i₅ + 1560, k_E + 2i_E + 23035)
      + 2·(k₃ + i₃)·2⁻¹²⁸ + 2·(k₃ + 2i₃)·2⁻¹²⁸
      + 4·(2⁻¹¹³ + εROP(0, 312, 4607; k₅ + 2i₅ + 1560, k_E + 2i_E + 23035))
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide. -/
theorem unlinkabilityRAK_lean_numG [ZKRow R] [ZKPRow R] {q3 q5 qE i3 i2 i5 iE k3 k2 k5 kE : ℕ}
    {εhide : ℝ} (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE) (hK : A.KBudget k3 k2 k5 kE)
    (hhide : ∀ b₁ b₂ K, hidingAdv (A.adv (σOfR A K)).ctx
      (reductionRA (A.adv (σOfR A K)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRAK A leanPIR leanPSR b₁ b₂) - pr _ (realGameRAK A leanPIR leanPSR b₁' b₂')| ≤
      4 * εAdG R pI 9 (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) k3 k2 k5 kE +
        2 * εAdG R pS 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) (k3 + i3) (k2 + i2)
          (k5 + i5 + 624) (kE + iE + 9214) +
        2 * εAdG R pS 9 q3 (q5 + 936) (qE + 13821) (k3 + 2 * i3) (k2 + 2 * i2) (k5 + 2 * i5 + 1560)
          (kE + 2 * iE + 23035) +
        2 * ((k3 + i3 : ℕ) / 2 ^ 128) + 2 * ((k3 + 2 * i3 : ℕ) / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + ZKPRow.εP R pS 0 312 4607 (k5 + 2 * i5 + 1560) (kE + 2 * iE + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  have hPI5 : ∀ x w ρ g, Rd5 (leanPIR (R := R) x w ρ g) 624 := fun x w ρ g =>
    (realROb_rd5 (p := pI) (Hb := Hashes.shake) (st := stI x) (w := encI x w) (bOf ρ) g).map
      (vecOf Sizes.labelRows.issue)
  have hPIE : ∀ x w ρ g, RdE (leanPIR (R := R) x w ρ g) 4607 := fun x w ρ g =>
    (realROb_rdE (p := pI) (st := stI x) (w := encI x w) hashesWF_shake (bOf ρ) g).map
      (vecOf Sizes.labelRows.issue)
  have hPS5 : ∀ x w ρ g, Rd5 (leanPSR (R := R) x w ρ g) 624 := fun x w ρ g =>
    (realROb_rd5 (p := pS) (Hb := Hashes.shake) (st := stS x) (w := encS x w) (bOf ρ) g).map
      (vecOf Sizes.labelRows.spend)
  have hPSE : ∀ x w ρ g, RdE (leanPSR (R := R) x w ρ g) 4607 := fun x w ρ g =>
    (realROb_rdE (p := pS) (st := stS x) (w := encS x w) hashesWF_shake (bOf ρ) g).map
      (vecOf Sizes.labelRows.spend)
  have h := unlinkabilityRAK (A := A) (PI := leanPIR) (PS := leanPSR) (simI := leanSimIR)
    (simS := leanSimSR) (progI := leanProgIR) (progS := leanProgSR)
    (εI := fun a b c => εAdG R pI pI.qsDegree a b c k3 k2 k5 kE)
    (εS₁ := fun a b c => εAdG R pS pS.qsDegree a b c (k3 + i3) (k2 + i2) (k5 + (i5 + 312 + 312))
      (kE + (iE + 4607 + 4607)))
    (εS₂ := fun a b c => εAdG R pS pS.qsDegree a b c (k3 + 2 * i3) (k2 + 2 * i2)
      (k5 + (2 * i5 + 1560)) (kE + (2 * iE + 23035)))
    (AdmSI := fun _ Sx => SReads pI Sx k3 k2 k5 kE)
    (AdmS₁ := fun _ Sx => SReads pS Sx (k3 + i3) (k2 + i2) (k5 + (i5 + 312 + 312))
      (kE + (iE + 4607 + 4607)))
    (AdmS₂ := fun _ Sx => SReads pS Sx (k3 + 2 * i3) (k2 + 2 * i2) (k5 + (2 * i5 + 1560))
      (kE + (2 * iE + 23035)))
    hA hI hPI5 hPIE hPS5 hPSE (fun x c => progRO_isProg c) (fun x c => progRO_isProg c)
    leanProgIR_none leanProgSR_none (fun γ => hK.s0 _ _ _) (fun γ => hK.s1 _ _ _)
    (sReads_Sx1K hK hI) (fun b₁ => sReads_Sx2K hK hI b₁)
    (fun a b c => leanPIR_zkROA a b c _ _ _ _) (fun a b c => leanPSR_zkROA a b c _ _ _ _)
    (fun a b c => leanPSR_zkROA a b c _ _ _ _) hhide b₁ b₂ b₁' b₂'
  have mI : ∀ a b c, a ≤ 2 * i3 + q3 → b ≤ q5 + 2 * i5 + 1872 → c ≤ qE + 2 * iE + 13821 →
      εAdG R pI pI.qsDegree a b c k3 k2 k5 kE ≤
        εAdG R pI 9 (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) k3 k2 k5 kE :=
    fun a b c ha hb hc => εAdG_mono pI ha hb hc le_rfl le_rfl le_rfl le_rfl
  have m1 := mI (i3 + i3 + q3) (0 + (624 + (i5 + (624 + (i5 + (624 + q5))))))
    (0 + (4607 + (iE + (4607 + (iE + (4607 + qE)))))) (by omega) (by omega) (by omega)
  have m2 := mI (i3 + i3 + q3) (0 + (0 + (i5 + (624 + (i5 + (624 + q5))))) + 312)
    (0 + (0 + (iE + (4607 + (iE + (4607 + qE))))) + 4607) (by omega) (by omega) (by omega)
  have m3 : εAdG R pS pS.qsDegree (i3 + q3) (i5 + (0 + (0 + (0 + (624 + q5)))) + (312 + 312))
      (iE + (0 + (0 + (0 + (4607 + qE)))) + (4607 + 4607)) (k3 + i3) (k2 + i2)
      (k5 + (i5 + 312 + 312)) (kE + (iE + 4607 + 4607)) ≤
      εAdG R pS 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) (k3 + i3) (k2 + i2) (k5 + i5 + 624)
        (kE + iE + 9214) :=
    εAdG_mono pS le_rfl (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
  have m4 : εAdG R pS pS.qsDegree q3 (0 + (0 + (0 + (0 + q5))) + (312 + (312 + 312)))
      (0 + (0 + (0 + (0 + qE))) + (4607 + (4607 + 4607))) (k3 + 2 * i3) (k2 + 2 * i2)
      (k5 + (2 * i5 + 1560)) (kE + (2 * iE + 23035)) ≤
      εAdG R pS 9 q3 (q5 + 936) (qE + 13821) (k3 + 2 * i3) (k2 + 2 * i2) (k5 + 2 * i5 + 1560)
        (kE + 2 * iE + 23035) :=
    εAdG_mono pS le_rfl (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
  have d1 := deltaI1RK_le A
  have dS1 := deltaS1AK_le A hK hI b₁
  have dS1' := deltaS1AK_le A hK hI b₁'
  have dS2 := deltaS2AK_le A hK hI b₁ b₂
  have dS2' := deltaS2AK_le A hK hI b₁' b₂'
  have eP : ZKPRow.εP R pS 0 312 4607 (k5 + (i5 + 312 + 312)) (kE + (iE + 4607 + 4607)) ≤
      ZKPRow.εP R pS 0 312 4607 (k5 + 2 * i5 + 1560) (kE + 2 * iE + 23035) :=
    ZKPRow.εP_mono pS le_rfl le_rfl le_rfl (by omega) (by omega)
  have eP2 : ZKPRow.εP R pS 0 312 4607 (k5 + (2 * i5 + 1560)) (kE + (2 * iE + 23035)) =
      ZKPRow.εP R pS 0 312 4607 (k5 + 2 * i5 + 1560) (kE + 2 * iE + 23035) := by
    rw [show k5 + (2 * i5 + 1560) = k5 + 2 * i5 + 1560 by omega,
      show kE + (2 * iE + 23035) = kE + 2 * iE + 23035 by omega]
  rw [eP2] at dS2 dS2'
  refine h.trans ?_
  rw [div_eq_mul_one_div (2 : ℝ) ((2 : ℝ) ^ 1024)] at dS1 dS1'
  rw [div_eq_mul_one_div (3 : ℝ) ((2 : ℝ) ^ 1024)] at dS2 dS2'
  rw [div_eq_mul_one_div (12 : ℝ) ((2 : ℝ) ^ 1024)]
  generalize (1 : ℝ) / 2 ^ 1024 = κ at d1 dS1 dS1' dS2 dS2' ⊢
  linarith

/-- **Theorem 2 with the Lean prover, in the random-oracle and ideal-cipher model, the key stage
and the Issuer's interaction reading the tables, with every term explicit**
(`unlinkabilityRAK_lean_numG` at function rows). -/
theorem unlinkabilityRAK_lean_num (A : AdversaryRAK (Blk → Blk) Sizes.labelRows Sg)
    {q3 q5 qE i3 i2 i5 iE k3 k2 k5 kE : ℕ} {εhide : ℝ} (hA : A.GBudget q3 q5 qE)
    (hI : A.IBudget i3 i2 i5 iE) (hK : A.KBudget k3 k2 k5 kE)
    (hhide : ∀ b₁ b₂ K, hidingAdv (A.adv (σOfR A K)).ctx
      (reductionRA (A.adv (σOfR A K)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRAK A leanPIR leanPSR b₁ b₂) - pr _ (realGameRAK A leanPIR leanPSR b₁' b₂')| ≤
      4 * εAd 9 (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) k3 k2 k5 kE +
        2 * εAd 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) (k3 + i3) (k2 + i2)
          (k5 + i5 + 624) (kE + iE + 9214) +
        2 * εAd 9 q3 (q5 + 936) (qE + 13821) (k3 + 2 * i3) (k2 + 2 * i2) (k5 + 2 * i5 + 1560)
          (kE + 2 * iE + 23035) +
        2 * ((k3 + i3 : ℕ) / 2 ^ 128) + 2 * ((k3 + 2 * i3 : ℕ) / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + εROP 0 312 4607 (k5 + 2 * i5 + 1560) (kE + 2 * iE + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityRAK_lean_numG A hA hI hK hhide b₁ b₂ b₁' b₂'

/-- **Theorem 2 with a table-reading key stage and AES as uniformly random permutations**
(`unlinkabilityRAK_lean_numG` at permutation rows). -/
theorem unlinkabilityRAK_lean_num_perm (A : AdversaryRAK (Equiv.Perm Blk) Sizes.labelRows Sg)
    {q3 q5 qE i3 i2 i5 iE k3 k2 k5 kE : ℕ} {εhide : ℝ} (hA : A.GBudget q3 q5 qE)
    (hI : A.IBudget i3 i2 i5 iE) (hK : A.KBudget k3 k2 k5 kE)
    (hhide : ∀ b₁ b₂ K, hidingAdv (A.adv (σOfR A K)).ctx
      (reductionRA (A.adv (σOfR A K)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRAK A leanPIR leanPSR b₁ b₂) - pr _ (realGameRAK A leanPIR leanPSR b₁' b₂')| ≤
      4 * εAdPm pI 9 (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) k3 k2 k5 kE +
        2 * εAdPm pS 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) (k3 + i3) (k2 + i2)
          (k5 + i5 + 624) (kE + iE + 9214) +
        2 * εAdPm pS 9 q3 (q5 + 936) (qE + 13821) (k3 + 2 * i3) (k2 + 2 * i2) (k5 + 2 * i5 + 1560)
          (kE + 2 * iE + 23035) +
        2 * ((k3 + i3 : ℕ) / 2 ^ 128) + 2 * ((k3 + 2 * i3 : ℕ) / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + εROPmP pS 0 312 4607 (k5 + 2 * i5 + 1560) (kE + 2 * iE + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityRAK_lean_numG A hA hI hK hhide b₁ b₂ b₁' b₂'

end Lean

end VoleMole.Privacy.Ratatouille
