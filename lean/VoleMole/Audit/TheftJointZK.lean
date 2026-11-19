import VoleMole.Theft.NumLin
import VoleMole.Theft.JointZK
import VoleMole.Audit.TheftNum

/-!
# Audit of the linear many-token theft theorems and of the joint composition step

* The six linear numeric theorems (`Theft/NumLin.lean`) are instantiated at the trivial
  adversaries of the earlier audits, at every per-kind hash budget and the cipher budget `2⁶⁴` and
  any `U, M ≤ 2³⁰`: `noTheftN_lean_numL`, `noTheftN_lean_numLP`, `noRedirectN_lean_numL`,
  `noRedirectN_lean_numLP`, `nmUN_lean_numL`, `nmUN_lean_numLP`. At `U = M = 1` the bound is
  `2⁻⁵⁴ + 2⁻⁵⁹`.
* The joint step (`Theft/JointZK.lean`): with the charges `Y ≡ 0`, the hypothesis of
  `real_sim_leN_jointZK` is the hypothesis of `real_sim_leN` and its bound is `real_sim_leN`'s, so
  the step is a generalization; `joint_le` is instantiated with nonzero charges on a two-point
  tape.

No `sorry`, no `axiom`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.TheftJointZK

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Theft VoleMole.ROM VoleMole.ROM.IC
open VoleMole.ROM.Reads VoleMole.Verifier
open OracleComp OracleSpec

/-! ## The linear bound at one Client -/

set_option exponentiation.threshold 300 in
example : ((1 + 1 : ℕ) : ℝ) / 2 ^ 55 + 1 / 2 ^ 59 = 1 / 2 ^ 54 + 1 / 2 ^ 59 := by norm_num

section Many

open VoleMole.Theft.Ratatouille VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille
open VoleMole.Audit.TheftManyR (thiefNR)
open VoleMole.Audit.Theft (zeroSpend)

variable {U M : ℕ}

/-- `noTheftN_lean_numL` at the trivial adversary, every budget `2⁶⁴`, any `U, M ≤ 2³⁰`. -/
example [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) :=
  noTheftN_lean_numL (L := Hit.Rata.Lmin) (thiefNR _ U M _ _) le_rfl (q := fun _ => 2 ^ 64)
    (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0), ⟨trivial, trivial⟩, rfl⟩

/-- `noTheftN_lean_numLP` at the trivial adversary with permutation rows. -/
example [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) :=
  noTheftN_lean_numLP (L := Hit.Rata.Lmin) (thiefNR _ U M _ _) le_rfl (q := fun _ => 2 ^ 64)
    (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    fun _ _ => ⟨pure (.spend (zeroSpend _) (Vector.replicate 16 0) 0), ⟨trivial, trivial⟩, rfl⟩

end Many

section Mous

open VoleMole.Theft.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka
open VoleMole.Audit.Theft (setW)
open VoleMole.Audit.TheftManyHit (thiefNMW hitWfN_thiefNMW)
open VoleMole.Audit.TheftPlainMany (keysOutN_thiefNMW)

variable {U M : ℕ}

/-- `noRedirectN_lean_numL` at the well-formed trivial adversary. -/
example [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) :=
  noRedirectN_lean_numL (L := Lrom) (thiefNMW U M _ _) hitWfN_thiefNMW keysOutN_thiefNMW le_rfl
    (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩)

/-- `noRedirectN_lean_numLP` at the well-formed trivial adversary with permutation rows. -/
example [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) :=
  noRedirectN_lean_numLP (L := Lrom) (thiefNMW U M _ _) hitWfN_thiefNMW keysOutN_thiefNMW le_rfl
    (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩)

end Mous

section Unbound

open VoleMole.Theft.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
  VoleMole.Privacy.MoussakaUnbound
open VoleMole.Spec.Moussaka (ctxBytes cdBytes)
open VoleMole.Audit.TheftManyHit (thiefNUW hitWfN_thiefNUW)
open VoleMole.Audit.Theft (setW)
open VoleMole.Audit.UnboundRest (prf1Adv_le_one)
open VoleMole.Audit.TheftPlainUnbound (keysOutNU_thiefNUW)

variable {U M : ℕ}

/-- `nmUN_lean_numL` at the well-formed trivial adversary. -/
example [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) (pts : Fin (M + 1) → Coins ctxBytes)
    (hpts : Function.Injective pts) :=
  nmUN_lean_numL (L := LminU) (thiefNUW U M _ _) hitWfN_thiefNUW keysOutNU_thiefNUW le_rfl
    (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩) pts hpts
    (fun _ _ => prf1Adv_le_one _ _)

/-- `nmUN_lean_numLP` at the well-formed trivial adversary with permutation rows. -/
example [NeZero U] (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) (pts : Fin (M + 1) → Coins ctxBytes)
    (hpts : Function.Injective pts) :=
  nmUN_lean_numLP (L := LminU) (thiefNUW U M _ _) hitWfN_thiefNUW keysOutNU_thiefNUW le_rfl
    (q := fun _ => 2 ^ 64) (qE := 2 ^ 64) (fun _ => le_rfl) le_rfl hU hM
    (fun _ _ => ⟨pure (.redeem setW [] (List.replicate ctxBytes 0) (List.replicate ctxBytes 0)
      (List.replicate cdBytes 0)), ⟨trivial, trivial⟩, rfl⟩) pts hpts
    (fun _ _ => prf1Adv_le_one _ _)

end Unbound

/-! ## The joint step -/

section Joint

open Finset

variable {Ω O ρ C G S : Type*}
  (P : Ω → List O → ρ → G → S → O) (Sm : Ω → List O → C → O) (pg : Ω → List O → C → S → S)
  {N : ℕ} [Nonempty ρ] [Nonempty C] [Nonempty G]
  [Fintype Ω] [Nonempty Ω] [Fintype ρ] [Fintype C] [Fintype G] [Fintype S] [Nonempty S]

lemma exU_zero {Z : Type*} [Fintype Z] : exU Z (fun _ => (0 : ℝ)) = 0 := by simp [exU]

/-- **With no charges the joint step is `real_sim_leN`**: its hypothesis is `real_sim_leN`'s, and
its bound is `Σ_i (ε i + Pr[deltaN i])`. -/
example (ε : ℕ → ℝ)
    (h : ∀ (i : Fin N) (Ev : Ω → List O → (Fin N → G) → S → Prop) ω τ,
      |pr ((ρ × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) a.1.2 a.2) -
        pr ((C × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (Sm ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1) a.1.2
          (pg ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.2))| ≤ ε i)
    (Ev : Ω → List O → (Fin N → G) → S → Prop) :
    |pr _ (realGN (C := C) P Ev) - pr _ (simGN (ρ := ρ) Sm pg Ev)| ≤
      ∑ i : Fin N, (ε i + pr _ (deltaN P Sm pg i)) := by
  have hj := real_sim_leN_jointZK P Sm pg ε (fun _ _ => 0) (B := 0) (J := 0)
    (fun _ _ => le_rfl) (fun _ _ _ => le_rfl)
    (fun i Ev ω τ => by rw [exU_zero, add_zero]; exact h i Ev ω τ)
    (by simp [exU_zero]) (by simp) Ev
  simpa using hj

/-- `joint_le` at two equal worlds with a nonzero charge `Y = 1/4`, `B = 1/4`, `J = 1/2`. -/
example (F : Bool → Prop) :
    |pr Bool (fun z => F z) - pr Bool (fun z => F z)| ≤
      (∑ i ∈ range 2, (fun _ => (0 : ℝ)) i + 1 / 2) / (1 - (2 : ℕ) * (1 / 4)) := by
  have h := joint_le (Z := Bool) (V := Bool) (N := 2) (fun _ z => z) (fun _ => 0)
    (fun _ _ => 1 / 4) (B := 1 / 4) (J := 1 / 2) (fun _ _ => by norm_num)
    (fun _ _ _ => le_rfl)
    (fun _ _ F => by
      simp only [sub_self, abs_zero, zero_add]
      exact exU_nonneg fun _ => by norm_num)
    (by simp [exU]; norm_num) (by norm_num) F
  exact h

end Joint

end VoleMole.Audit.TheftJointZK
