import VoleMole.Audit.MainRata
import VoleMole.Privacy.MoussakaMainShared23
import VoleMole.Privacy.RatatouilleMainShared23

/-!
# Audit of the results on `main` with one shared `H₂³` table (`lean/docs/zk.md` §4.2)

* **`anonymity_main_shared23` and `unlinkability_main_shared23` apply**: for the adversaries `mS`
  (Moussaka) and `rS` (Ratatouille) of `Audit/MainShared.lean`, `Audit/MainRata.lean` (constant
  guess, no table reads) every hypothesis holds, with `εhide = 0`. For the adversaries `mR k₀`,
  `rSR k₀` whose guess reads the shared `H₅` table, `Cons` holds and the theorems apply for any
  bound on their hiding reductions.
* **The programming-collision term is a number**: `Δ23 9 ≤ 2⁻¹⁰⁶` (`Δ23_le`), so the shared `H₂³`
  table adds at most `30·2⁻¹⁰⁶ < 2⁻¹⁰¹` to the bound of each protocol.
* **The predictors name few candidates**: `card_predS23_le`, `card_predIS23_le`,
  `card_predCS23_le` at `q₅ = 0`.

No `sorry`, no `axiom`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.MainShared23

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Privacy.PU VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Audit.MainShared VoleMole.Audit.MainRata

set_option exponentiation.threshold 1100 in
/-- **The programming-collision term of a hop is below `2⁻¹⁰⁶`** for QuickSilver degree `9`. -/
theorem Δ23_le : Δ23 9 ≤ 1 / 2 ^ 106 := by
  have h := noHitProb_le
  have h2 : ((1 : ℝ) / 2) ^ (2 ^ 15) ≤ 1 / 2 ^ 120 := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have h3 : noHitProb ≤ 1 / 2 ^ 120 := h.trans h2
  have h4 : (0 : ℝ) ≤ noHitProb := pr_nonneg _
  unfold Δ23 εS
  have h5 : (3 : ℝ) / 2 ^ 1024 ≤ 1 / 2 ^ 120 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    norm_num
  norm_num at h3 ⊢
  linarith

section Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka

/-- `anonymity_main_shared23` for `mS`. -/
example (idx : Rule) :=
  anonymity_main_shared23 mS idx mS_cons (εhide := 0) (fun _ _ => (Audit.hidingAdv_true _ _).le)

/-- `anonymity_main_shared23` for the `H₅`-reading adversary `mR k₀`. -/
example (k₀ : ZK.Sim.Bytes 37) (idx : Rule) :=
  anonymity_main_shared23 (mR k₀) idx (mR_cons k₀) (εhide := 1)
    (fun _ _ => Audit.hidingAdv_le_one _ _ _)

/-- The predictors of `mS` on the shared table name at most `2498` candidates. -/
example (idx : Rule) (b : Bool) (t₀ t₁ n₀ n₁ : Spec.Bytes) (a : AuxS) (c : Bool) :
    (predS23 mS idx b t₀ t₁ n₀ n₁ a c).card ≤ 2 * (0 + 1249) :=
  card_predS23_le mS idx (q5 := 0) (fun _ _ _ _ => le_rfl) b t₀ t₁ n₀ n₁ a c

end Moussaka

section Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille

/-- `unlinkability_main_shared23` for `rS`. -/
example [HasPrg] (b₁ b₂ b₁' b₂' : Bool) :=
  unlinkability_main_shared23 rS rS_cons (εhide := 0)
    (fun _ _ _ => (Audit.hidingAdvR_true _).le) b₁ b₂ b₁' b₂'

/-- `unlinkability_main_shared23` for the `H₅`-reading Issuer `rSR k₀`. -/
example [HasPrg] (k₀ : ZK.Sim.Bytes 37) (εhide : ℝ)
    (hh : ∀ b₁ b₂ a, hidingAdv (rSR k₀).ctx (redSR23 (rSR k₀) b₁ b₂ a) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :=
  unlinkability_main_shared23 (rSR k₀) (rSR_cons k₀) hh b₁ b₂ b₁' b₂'

/-- The predictors of `rS` on the shared table name at most `3747` and `1249` candidates. -/
example [HasPrg] (b₁ b₂ : Bool) (n : Quad Nullifier) (t : Commitment × Commitment)
    (cf₂ cf₃ : Credits → Commitment) (a : AuxSR) (c : Bool) :
    (predIS23 rS b₁ b₂ n t cf₂ cf₃ a c).card ≤ 3 * (0 + 1249) ∧
      (predCS23 rS b₁ b₂ n t cf₂ cf₃ a).card ≤ 0 + 1249 :=
  ⟨card_predIS23_le rS b₁ b₂ n t cf₂ cf₃ a (q5 := 0) (fun _ _ => le_rfl) c,
    card_predCS23_le rS b₁ b₂ n t cf₂ cf₃ a (q5 := 0) (fun _ _ => le_rfl)⟩

end Ratatouille

end VoleMole.Audit.MainShared23
