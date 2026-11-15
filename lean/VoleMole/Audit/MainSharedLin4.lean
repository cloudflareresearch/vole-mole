import VoleMole.Audit.MainFind
import VoleMole.Audit.MainNCLean
import VoleMole.Privacy.MoussakaMainSharedLin
import VoleMole.Privacy.RatatouilleMainSharedLin

/-!
# Audit of the four-proof theorems on `main` on the linear joint hop (`ZK/MainSharedLin4.lean`)

* **`anonymity_main_sharedLin` (+ `_find`) and `unlinkability_main_sharedLin` apply**: for the
  adversaries `mH`, `rH` of `Audit/MainSharedAll.lean` (constant guess, no table reads; joint
  reads at budgets `0`, `ConsH.consJ`) with `εhide = 0`, and for the `H₃`-reading `mH3 k ρ`,
  `rH3 k ρ` (one `H₃` point, `ConsJ 2 0`).
* **`anonymityNC_main_lin` (+ `_find`, `anonymityNC_main_lean_lin`) applies with the trapdoor
  signers** (`φ = 0`): every hypothesis holds, and the whole bound at budgets `0` is at most
  `2⁻¹⁰⁰` (`ncm_lin_le`, `ncm_lean_lin_le`). With `main_sharedAll_le` it was about `2⁻⁹⁹·⁴`.
* **The numbers at budgets `0`** (`lin4_zero_le`, `linNC_zero_le`): the hop and failure and
  collision terms of 4(a) and Ratatouille, and the whole statistical bound of 4(b'), are at most
  `2⁻¹⁰⁰`.
* `main_sharedAll_le4LinJ`, `main_sharedAll_leLinJ`, `rdN_or_bstarN`, `bstarN_imp`,
  `realAll_eq_hybN`, `simAll_eq_hybN` are instantiated through these at the games of `main`'s
  issuance, redemption and spend layouts: their hypotheses are met.

No `sorry`, no `axiom`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.MainSharedLin4

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Privacy.PU VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Audit.MainSharedAll VoleMole.Audit.MainFind VoleMole.Audit.Live

/-! ## The numbers at budgets `0` -/

set_option exponentiation.threshold 1100 in
/-- **The hop, failure and collision terms of 4(a) and Ratatouille at budgets `0`** (written
`0 + 0`, as `ConsH.consJ` gives them from `ConsH 0 0`) are below `2⁻¹⁰⁰` (about `2⁻¹⁰⁰·³³`). -/
theorem lin4_zero_le :
    16 * (εS (0 + 0 + 4) (0 + 0 + 8 * 4607) + Δ23N 9 4) + 8 * noHitProb + 3750 / 2 ^ 128 ≤
      1 / 2 ^ 100 := by
  have h := noHitProb_le_128
  unfold Δ23N εS
  norm_num at h ⊢
  linarith

set_option exponentiation.threshold 1100 in
/-- **The whole statistical bound of 4(b') at budgets `0`**, with `main`'s Lean issuance prover
(`+ 4·2⁻¹¹³`) and without the abort term, is below `2⁻¹⁰⁰`. -/
theorem linNC_zero_le :
    16 * (εS (0 + 0 + 4) (0 + 0 + 8 * 4607) + Δ23N 9 4) +
      (8 * noHitProb + (4 * ((0 : ℕ) + 625) + 626) / 2 ^ 128) + 4 / 2 ^ 113 ≤ 1 / 2 ^ 100 := by
  have h := noHitProb_le_128
  unfold Δ23N εS
  norm_num at h ⊢
  linarith

section Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka

/-- `anonymity_main_sharedLin` for `mH`. -/
example (idx : Rule) :=
  anonymity_main_sharedLin mH idx mH_cons.consJ (εhide := 0)
    (fun _ _ _ => (Audit.hidingAdv_true _ _).le)

/-- `anonymity_main_sharedLin` for the `H₃`-reading adversary `mH3 k ρ`. -/
example (k : Pre) (ρ : ZK.Sim.Bytes 16) (idx : Rule) :=
  anonymity_main_sharedLin (mH3 k ρ) idx (mH3_cons k ρ).consJ (εhide := 1)
    (fun _ _ _ => Audit.hidingAdv_le_one _ _ _)

/-- `anonymity_main_sharedLin_find` for `mH`. -/
example :=
  anonymity_main_sharedLin_find mH mH_cons.consJ (εhide := 0)
    (fun _ _ _ => (Audit.hidingAdv_true _ _).le)

/-- **`anonymityNC_main_lin` for `ncm d` with the trapdoor signers: the bound is a number, at most
`2⁻¹⁰⁰`.** -/
theorem ncm_lin_le (d : Spec.Bytes) (PI : NIZK IssueInstance) :
    |realNCM (ncm d) (Rule.ofIdx Audit.idxEval) PI (fun _ => skI d) false -
        realNCM (ncm d) (Rule.ofIdx Audit.idxEval) PI (fun _ => skI d) true| ≤ 1 / 2 ^ 100 := by
  have h := anonymityNC_main_lin (ncm d) (Rule.ofIdx Audit.idxEval) PI (fun _ => skI d)
    (fun _ => skI_correct d) (ruleNC_ofIdx _ _ Audit.idxEval_sound) (ncm_cons d).consJ (q5 := 0)
    (fun _ _ _ => le_rfl)
  rw [MainSharedAll.phi_skI, MainSharedAll.phi_skI] at h
  have hz := linNC_zero_le
  have : (0 : ℝ) ≤ 4 / 2 ^ 113 := by positivity
  linarith

/-- **`anonymityNC_main_lean_lin` for `ncm d`**, `main`'s Lean issuance prover: at most `2⁻¹⁰⁰`. -/
theorem ncm_lean_lin_le [HasPrg] (d : Spec.Bytes) :
    |realNCML (ncm d) (Rule.ofIdx Audit.idxEval) (fun _ => skI d) false -
        realNCML (ncm d) (Rule.ofIdx Audit.idxEval) (fun _ => skI d) true| ≤ 1 / 2 ^ 100 := by
  have h := anonymityNC_main_lean_lin (ncm d) (Rule.ofIdx Audit.idxEval) (fun _ => skI d)
    (fun _ => skI_correct d) (ruleNC_ofIdx _ _ Audit.idxEval_sound) (ncm_cons d).consJ (q5 := 0)
    (fun _ _ _ => le_rfl)
  rw [MainSharedAll.phi_skI, MainSharedAll.phi_skI] at h
  have hz := linNC_zero_le
  linarith

/-- `anonymityNC_main_lin_find` for `ncmF` (sets with both issuers, trapdoor signers). -/
example (PI : NIZK IssueInstance) :
    |realNCM ncmF findIdx PI (fun c => skI (digL c)) false -
        realNCM ncmF findIdx PI (fun c => skI (digL c)) true| ≤ 1 / 2 ^ 100 := by
  have h := anonymityNC_main_lin_find ncmF PI (fun c => skI (digL c)) (fun c => skI_correct _)
    ncmF_contains ncmF_cons.consJ (q5 := 0) (fun _ _ _ => le_rfl)
  rw [MainFind.phi_skL, MainFind.phi_skL] at h
  have hz := linNC_zero_le
  have : (0 : ℝ) ≤ 4 / 2 ^ 113 := by positivity
  linarith

/-- `unlinkabilityNC_main_lin_find` for `ncm d` (one key, any sets). -/
example (d : Spec.Bytes) (PI : NIZK IssueInstance) :=
  unlinkabilityNC_main_lin_find (ncm d) PI (fun _ => skI d) (fun _ => skI_correct d) rfl rfl
    (ncm_cons d).consJ (q5 := 0) (fun _ _ _ => le_rfl)

end Moussaka

section Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille

/-- `unlinkability_main_sharedLin` for `rH`. -/
example [HasPrg] (b₁ b₂ b₁' b₂' : Bool) :=
  unlinkability_main_sharedLin rH rH_cons.consJ (εhide := 0)
    (fun _ _ _ _ => (Audit.hidingAdvR_true _).le) b₁ b₂ b₁' b₂'

/-- `unlinkability_main_sharedLin` for the `H₃`-reading Issuer `rH3 k ρ`, for any bound on its
hiding reductions. -/
example [HasPrg] (k : Pre) (ρ : ZK.Sim.Bytes 16) (εhide : ℝ)
    (hh : ∀ T b₁ b₂ a, hidingAdv (rH3 k ρ).ctx (redSR23 ((rH3 k ρ).withH T) b₁ b₂ a) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :=
  unlinkability_main_sharedLin (rH3 k ρ) (rH3_cons k ρ).consJ hh b₁ b₂ b₁' b₂'

end Ratatouille

end VoleMole.Audit.MainSharedLin4
