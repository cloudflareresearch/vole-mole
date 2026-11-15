import VoleMole.Theft.JointUnbIv
import VoleMole.Theft.JointNumJ

/-!
# Unbound non-malleability for `U` tokens and `M` redemptions with the joint step at points

The many-token unbound bound of `Theft/NumLin.lean` (`nmUN_lean_numL`) is linear in `U + M`:
`(U + M)·2⁻⁵⁵ + 2⁻⁵⁹`. Here the hops are replaced by the joint step at points, as
`Theft/JointNumJ.lean` does for Ratatouille:

* **`nmU_sim_le`**: in the simulated game,
  `Pr[BadN] ≤ ε_SE + Σ_h (ε_prf + (M+1)·2⁻¹⁹² + Adv^bind(B₁ h) + Adv^spr-k(B₂ h))`, with `ε_SE`
  `ROM/`'s simultaneous extraction for the reduction's budget (as in `nmUN_lean_rom`);
* **`nmUN_lean_numJ`**: numerically, with every per-kind hash budget and the cipher budget at
  most `2⁶⁴` and `U, M ≤ 2³⁰`, the hypotheses of `nmUN_lean_numL`, and the refused slots' `iv`s
  `ivRX`,

      Pr[BadN] ≤ 2⁻⁵⁴ + Σ_h (ε_prf + Adv^bind(B₁ h) + Adv^spr-k(B₂ h)).
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads VoleMole.ZK.IC

namespace MoussakaUnbound

open VoleMole.Privacy.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (AnchorSet ctxBytes proveSeedBytes nfBytes)
open VoleMole.Privacy.Moussaka (ShM leanSim)
open VoleMole.Theft.Ratatouille (qPre pFail pFail_le failG_nonneg jexpr_mono)

-- `UCom`, `Derive` and `Com` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

section Sim

variable {U M L : ℕ} (A : ThiefN U M Tab3 (TabU L))

set_option maxHeartbeats 4000000 in
/-- **The simulated game's event**: `ROM/`'s simultaneous extraction for the reduction's budget,
and the hit of an honest token (key recovery, binding, key second preimages). -/
theorem nmU_sim_le (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutNU A kt)
    (hL : LminU ≤ L) {q : Kind → ℕ} {qE nG : ℕ}
    (hA : ∀ reqs reds, AdmLN (QBudT q qE nG) ansPN (A.out reqs reds)) {εprf : ℝ}
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
      (leanProgRUX hbX) (extRomUN q qE nG) h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabU L))
        (nmSimN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG))) ≤
      ((epsRomU (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
          (nG + (U + M) * 338)).toReal +
        (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
      ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
        bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
          (extRomUN q qE nG) h) +
        sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
          (leanProgRUX hbX) (extRomUN q qE nG) h)) := by
  have hAH : ∀ F : (Fin (U + M) → Tab3) → TabU L → UOp,
      AdmLN (QBudT q qE nG) ansPN F →
      Hit.AdmHitN (R := Blk → Blk) (p := Privacy.Moussaka.pI) (L := L) (M := Arith.Moussaka.M)
        (N := U + M) (G := Tab3) (q .mu) (q .h21) (q .h22) F := by
    rintro F ⟨oa, hb, rfl⟩
    exact admHitN_runTN hb.1
  have hmv := ((progMovesN_hitU (U := U) (M := M) (R := Blk → Blk) hL (q .mu) (q .h21)
    (q .h22)).mono hAH).fresh_mono (Fresh' := FreshKNU kt) fun _ _ h => h.1
  have hse := sim_se_leN_okKU A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
    (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG) hw hk
    (weakSEN_of_plainL progQUm (patch2 Privacy.Moussaka.pI) logQUm
      (plainSENL_romU kt hL _ _ _ _) hmv progU_sndX hpatchUm hlogUm logQUm_none
      fun oa ys hl h => hl ▸ qBudT_redQNu h ys)
    fun _ => hA _ _
  have hhit := sim_hit_leN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
    (extRomUN q qE nG)
  have hkey : ∀ hh : Fin U, owkAdvN (A.ci hh) (keyBN A (leanSim pI) (leanProgIUX hbX)
      (leanSim pR) (leanProgRUX hbX) (extRomUN q qE nG) hh) ≤ εprf + (M + 1) / 2 ^ 192 :=
    fun hh => owkAdvN_le (A.ci hh) _ pts hpts (fun t b => by
      obtain ⟨Q, hQ, hf⟩ := viewN_reads A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
        (leanProgRUX hbX) (extRomUN q qE nG) hh t b
      exact ⟨Q, hQ, fun F F' hag => by simp only [keyBN, hf F F' hag]⟩) (hprf hh)
  have hsum : ∑ hh : Fin U, (owkAdvN (A.ci hh) (keyBN A (leanSim pI) (leanProgIUX hbX)
        (leanSim pR) (leanProgRUX hbX) (extRomUN q qE nG) hh) +
        bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
          (extRomUN q qE nG) hh) +
        sprAdvN (A.ci hh) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
          (leanProgRUX hbX) (extRomUN q qE nG) hh)) ≤
      ∑ hh : Fin U, (εprf + (M + 1) / 2 ^ 192 +
        bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
          (extRomUN q qE nG) hh) +
        sprAdvN (A.ci hh) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
          (leanProgRUX hbX) (extRomUN q qE nG) hh)) :=
    Finset.sum_le_sum fun hh _ => by linarith [hkey hh]
  have hor : pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabU L))
      (nmSimN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
        (BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG))) ≤
      pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabU L))
        (nmSimN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
          (seEvN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE nG))) +
      pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabU L))
        (nmSimN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
          (hitN A (extRomUN q qE nG))) := by
    refine (Privacy.pr_mono fun z hz => ?_).trans (pr_or_le _ _)
    obtain ⟨h1, h2, h3 | h3⟩ := hz
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr h3
  linarith

end Sim

/-! ## Numbers -/

section Num

/-- **The joint bound's arithmetic** (as `numJ_final`, with room for the `U·(M+1)·2⁻¹⁹²` term).
With `n ≤ 2³¹` slots, the per-slot terms summing to at most `2⁻⁷⁰`, `B ≤ 2⁻⁵⁵`,
`J ≤ 300·2⁻⁶³` and the simulated game's error `≤ 15·2⁻⁶³`, the total is at most `2⁻⁵⁴`. -/
lemma numJ_finalU {n a B J r : ℝ} (hn : n ≤ 2 ^ 31) (ha : a ≤ 1 / 2 ^ 70)
    (hB0 : 0 ≤ B) (hB : B ≤ 1 / 2 ^ 55) (hJ : J ≤ 300 / 2 ^ 63) (hr : r ≤ 15 / 2 ^ 63) :
    n * B < 1 ∧ (a + J) / (1 - n * B) + r ≤ 1 / 2 ^ 54 := by
  have hnB : n * B ≤ 1 / 2 ^ 24 := by
    calc n * B ≤ 2 ^ 31 * (1 / 2 ^ 55) := mul_le_mul hn hB hB0 (by positivity)
      _ = 1 / 2 ^ 24 := by norm_num
  have hden : (1 : ℝ) - 1 / 2 ^ 24 ≤ 1 - n * B := by linarith
  have hden0 : (0 : ℝ) < 1 - 1 / 2 ^ 24 := by norm_num
  refine ⟨by linarith, ?_⟩
  have h1 : (a + J) / (1 - n * B) ≤ (1 / 2 ^ 70 + 300 / 2 ^ 63) / (1 - n * B) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have h2 : (1 / 2 ^ 70 + 300 / 2 ^ 63) / (1 - n * B) ≤
      (1 / 2 ^ 70 + 300 / 2 ^ 63) / (1 - 1 / 2 ^ 24) :=
    div_le_div_of_nonneg_left (by positivity) hden0 hden
  have h3 : (1 / 2 ^ 70 + 300 / 2 ^ 63 : ℝ) / (1 - 1 / 2 ^ 24) + 15 / 2 ^ 63 ≤ 1 / 2 ^ 54 := by
    norm_num
  linarith

lemma final_combineU {p s X r S c : ℝ} (hj : |p - s| ≤ X) (hsim : s ≤ r + S)
    (hfin : X + r ≤ c) : p ≤ c + S := by
  have := (abs_sub_le_iff.1 hj).1
  linarith

variable {U M L : ℕ}

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1100 in
/-- **Unbound non-malleability for `U` tokens and `M` redemptions with the joint step at
points** (function rows, `L ≥ LminU`): with every per-kind hash budget and the cipher budget at
most `2⁶⁴` and `U, M ≤ 2³⁰`, under the hypotheses of `nmUN_lean_numL`,

    Pr[BadN] ≤ 2⁻⁵⁴ + Σ_h (ε_prf + Adv^bind(B₁ h) + Adv^spr-k(B₂ h)).

(`nmUN_lean_numL` gives `(U + M)·2⁻⁵⁵ + 2⁻⁵⁹` in place of `2⁻⁵⁴`, about `2⁻²⁴` at
`U + M = 2³¹`.) -/
theorem nmUN_lean_numJ (A : ThiefN U M Tab3 (TabU L))
    (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutNU A kt) (hL : LminU ≤ L)
    {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64) (hqE : qE ≤ 2 ^ 64) (hU : U ≤ 2 ^ 30)
    (hM : M ≤ 2 ^ 30) (hA : ∀ reqs reds, AdmLN (QBud q qE) ansPN (A.out reqs reds)) {εprf : ℝ}
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
      (leanProgRUX hbX) (extRomUN q qE (totK Arith.Moussaka.M q)) h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabU L))
        (nmRealNE A (leanPIUX hbX) (leanPRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE (totK Arith.Moussaka.M q)))) ≤
      1 / 2 ^ 54 + ∑ h : Fin U, (εprf +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
            (extRomUN q qE (totK Arith.Moussaka.M q)) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) (extRomUN q qE (totK Arith.Moussaka.M q)) h)) := by
  have hA' := fun reqs reds => admLN_qBudT (hA reqs reds)
  have hL49 : 49 ≤ L := le_trans (by norm_num [LminU]) hL
  have hN32 : U + M ≤ 2 ^ 32 := by omega
  have hN31 : U + M ≤ 2 ^ 31 := by omega
  have hsim := nmU_sim_le A hw hk hL hA' pts hpts hprf
  rw [sum_split, ← add_assoc] at hsim
  set N := U + M with hNdef
  have hn : (N : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hN31
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have ht3 : (q .h3 : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hq .h3
  have ht5 : (q .h5 : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hq .h5
  have he : (qE : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hqE
  -- the budgets as reals
  have cQE : ((aEU N qE + N * max 4607 4607 : ℕ) : ℝ) =
      2 * ((N : ℝ) * 101372 + qE) + 9215 + N * 4607 := by
    simp only [aEU, verifyCellBound_pRU, max_self]; push_cast; ring
  have cQ5 : ((a5U N q + N * max 312 624 : ℕ) : ℝ) = (N : ℝ) * 312 + q .h5 + 312 + N * 624 := by
    simp only [a5U, show max 312 624 = 624 from rfl]; push_cast; ring
  set QE := aEU N qE + N * max 4607 4607 with hQE
  set Q5 := a5U N q + N * max 312 624 with hQ5
  have hQEm : (QE : ℝ) ≤ 2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 := by
    rw [cQE]; nlinarith
  have hQ5m : (Q5 : ℝ) ≤ 2 ^ 31 * 312 + 2 ^ 64 + 312 + 2 ^ 31 * 624 := by
    rw [cQ5]; nlinarith
  have hQE0 : (0 : ℝ) ≤ QE := Nat.cast_nonneg _
  have hQ50 : (0 : ℝ) ≤ Q5 := Nat.cast_nonneg _
  -- the cipher denominator
  have hdE : (2 : ℝ) ^ 128 - 221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 + 4607) ≤
      dEZK QE := by
    unfold dEZK; push_cast; linarith
  have hdEm : (0 : ℝ) < 2 ^ 128 -
      221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 + 4607) := by
    norm_num
  have hdE0 : 0 < dEZK QE := lt_of_lt_of_le hdEm hdE
  have hE : 221 * ((QE + 4607 : ℕ) : ℝ) < 2 ^ 128 := by
    have := hdE0; unfold dEZK at this; linarith
  have h3 : (q .h3 : ℝ) < 2 ^ 128 := by linarith
  -- the budget factor
  have hβm : βZK Q5 QE ≤ 1 / 2 ^ 55 := by
    unfold βZK
    have h1 : 221 / dEZK QE * QE ≤
        221 / (2 ^ 128 - 221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 + 4607)) *
          (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607) :=
      mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hdEm hdE) hQEm hQE0
        (div_nonneg (by norm_num) hdEm.le)
    have h2 : 1 / 2 ^ 128 * (Q5 : ℝ) ≤
        1 / 2 ^ 128 * (2 ^ 31 * 312 + 2 ^ 64 + 312 + 2 ^ 31 * 624) :=
      mul_le_mul_of_nonneg_left hQ5m (by positivity)
    have h3' : (221 : ℝ) /
          (2 ^ 128 - 221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 + 4607)) *
          (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607) +
        1 / 2 ^ 128 * (2 ^ 31 * 312 + 2 ^ 64 + 312 + 2 ^ 31 * 624) ≤ 1 / 2 ^ 55 := by norm_num
    linarith
  have hβ : βZK Q5 QE < 1 := by linarith
  have hD : (1 : ℝ) - 1 / 2 ^ 55 ≤ 1 - βZK Q5 QE := by linarith
  have hD0 : (0 : ℝ) < 1 - 1 / 2 ^ 55 := by norm_num
  have hDβ : 0 < 1 - βZK Q5 QE := by linarith
  -- the weights
  set w := wZK (q .h3) Q5 QE with hwdef
  have hw0 : w 0 ≤ 1 / (2 ^ 128 - 2 ^ 64) / (1 - 1 / 2 ^ 55) := by
    show 1 / (2 ^ 128 - (q .h3 : ℝ)) / (1 - βZK Q5 QE) ≤ _
    have : (0 : ℝ) < 2 ^ 128 - 2 ^ 64 := by norm_num
    exact div_le_div₀ (by positivity) (div_le_div_of_nonneg_left (by norm_num) this (by linarith))
      hD0 hD
  have hw1 : w 1 ≤ 221 / (2 ^ 128 - 221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 +
      2 ^ 31 * 4607 + 4607)) / (1 - 1 / 2 ^ 55) := by
    show 221 / dEZK QE / (1 - βZK Q5 QE) ≤ _
    exact div_le_div₀ (div_nonneg (by norm_num) hdEm.le)
      (div_le_div_of_nonneg_left (by norm_num) hdEm hdE) hD0 hD
  have hw2 : w 2 ≤ 1 / 2 ^ 128 / (1 - 1 / 2 ^ 55) := by
    show 1 / 2 ^ 128 / (1 - βZK Q5 QE) ≤ _
    exact div_le_div_of_nonneg_left (by positivity) hD0 hD
  have hwnn : ∀ k, 0 ≤ w k := by
    intro k
    fin_cases k
    · exact div_nonneg (div_nonneg zero_le_one (by linarith)) hDβ.le
    · exact div_nonneg (div_nonneg (by norm_num) hdE0.le) hDβ.le
    · exact div_nonneg (by positivity) hDβ.le
  have hw0' : 0 ≤ w 0 := hwnn 0
  have hw1' : 0 ≤ w 1 := hwnn 1
  have hw2' : 0 ≤ w 2 := hwnn 2
  -- the largest per-hop charge
  set B := ∑ k, w k * MZK N (q .h3) (a5U N q) (aEU N qE) (max 312 624) (max 4607 4607) k
    with hBdef
  have hBe : B = w 0 * q .h3 + w 1 * QE + w 2 * Q5 := by
    rw [hBdef, Fin.sum_univ_three]
    simp only [MZK, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hQE, hQ5]
  have hB0 : 0 ≤ B := by rw [hBe]; positivity
  have hB : B ≤ 1 / 2 ^ 55 := by
    rw [hBe]
    have e1 := mul_le_mul hw0 ht3 (Nat.cast_nonneg _) (by norm_num)
    have e2 := mul_le_mul hw1 hQEm hQE0 (div_nonneg (div_nonneg (by norm_num) hdEm.le) hD0.le)
    have e3 := mul_le_mul hw2 hQ5m hQ50 (by positivity)
    have : 1 / (2 ^ 128 - 2 ^ 64) / (1 - 1 / 2 ^ 55) * (2 : ℝ) ^ 64 +
        221 / (2 ^ 128 - 221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 + 4607)) /
          (1 - 1 / 2 ^ 55) * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607) +
        1 / 2 ^ 128 / (1 - 1 / 2 ^ 55) * (2 ^ 31 * 312 + 2 ^ 64 + 312 + 2 ^ 31 * 624) ≤
        1 / 2 ^ 55 := by norm_num
    linarith
  -- the summed charges
  have hJ := nmU_J_le A hA' hL49 hN32 w hwnn
  have caE : ((aEU N qE : ℕ) : ℝ) ≤ 2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 := by
    simp only [aEU, verifyCellBound_pRU]; push_cast; nlinarith
  have ca5 : ((a5U N q : ℕ) : ℝ) ≤ 2 ^ 31 * 312 + 2 ^ 64 + 312 := by
    simp only [a5U]; push_cast; nlinarith
  have cm1 : ((max 4607 4607 : ℕ) : ℝ) = 4607 := by norm_num
  have cm2 : ((max 312 624 : ℕ) : ℝ) = 624 := by norm_num
  have hpF := pFail_le
  have hpF0 : 0 ≤ pFail := exP_nonneg fun g => failG_nonneg g
  rw [cm1, cm2] at hJ
  have hJm := jexpr_mono hw0' hw1' hw2' (Nat.cast_nonneg (q .h3)) (Nat.cast_nonneg (aEU N qE))
    (Nat.cast_nonneg (a5U N q)) hn0 hpF0 hw0 hw1 hw2 ht3 caE ca5 hn hpF
  have hJn : (1 : ℝ) / (2 ^ 128 - 2 ^ 64) / (1 - 1 / 2 ^ 55) * 2 ^ 64 +
        221 / (2 ^ 128 - 221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 + 4607)) /
          (1 - 1 / 2 ^ 55) * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215) +
        1 / 2 ^ 128 / (1 - 1 / 2 ^ 55) * (2 ^ 31 * 312 + 2 ^ 64 + 312) +
      (221 / (2 ^ 128 - 221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 + 4607)) /
          (1 - 1 / 2 ^ 55) * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 * 4607) +
        1 / 2 ^ 128 / (1 - 1 / 2 ^ 55) * (2 ^ 31 * 312 + 2 ^ 64 + 312 + 2 * 624)) *
        ((2 ^ 31 : ℝ) ^ 2 / 2 ^ 64 + 4 * (2 ^ 31 : ℝ) ^ 2 / 2 ^ 128) +
      (221 / (2 ^ 128 - 221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 + 4607)) /
          (1 - 1 / 2 ^ 55) * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215) +
        1 / 2 ^ 128 / (1 - 1 / 2 ^ 55) * (2 ^ 31 * 312 + 2 ^ 64 + 312)) *
          (2 * 2 ^ 31 * (1 / 2 ^ 113)) +
      2 * 2 ^ 31 * (221 / (2 ^ 128 - 221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 +
          4607)) / (1 - 1 / 2 ^ 55) * 4607 + 1 / 2 ^ 128 / (1 - 1 / 2 ^ 55) * 624) *
        (2 * 2 ^ 31 * (1 / 2 ^ 113)) ≤ 300 / 2 ^ 63 := by
    norm_num
  -- the per-slot terms
  have hεZ : εZK QE / (1 - βZK Q5 QE) ≤ (1 / 2 ^ 113 + 221 * 9214 /
      (2 ^ 128 - 221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 + 4607)) +
        1 / 2 ^ 128) / (1 - 1 / 2 ^ 55) := by
    unfold εZK
    have e1 := grindBad_le_113
    have e2 : 221 * 9214 / dEZK QE ≤ 221 * 9214 /
        (2 ^ 128 - 221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 + 4607)) :=
      div_le_div_of_nonneg_left (by norm_num) hdEm hdE
    exact div_le_div₀ (by norm_num) (by linarith) hD0 hD
  have hδ : ∀ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabU L))
      (deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
        (leanProgRUX hbX) i) ≤
      1 / 2 ^ 113 + (zkB 0 312 4607 + zkB 0 312 4607) +
        (1 / 2 ^ 128 + (2 ^ 32 : ℝ) / 2 ^ 1024) := by
    intro i
    refine ((deltaNU_le (R := Blk → Blk) hbX_wf A i).trans
      (deltaBoundN_le (εz_fn_le _ _ _ _) (εz_fn_le _ _ _ _))).trans ?_
    have h2N : (((2 * N : ℕ)) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast (by omega : 2 * N ≤ 2 ^ 32)
    exact add_le_add le_rfl (add_le_add le_rfl (div_le_div_of_nonneg_right h2N (by positivity)))
  have hδ0 : ∀ i, 0 ≤ pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabU L))
      (deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
        (leanProgRUX hbX) i) := fun i => pr_nonneg _
  have ha : ∑ i : Fin N, (εZK QE / (1 - βZK Q5 QE) + (1 + B) *
      pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabU L))
        (deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
          (leanProgRUX hbX) i)) ≤ 1 / 2 ^ 70 := by
    have hpt : ∀ i : Fin N, εZK QE / (1 - βZK Q5 QE) + (1 + B) *
        pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (TabU L))
          (deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) i) ≤
        (1 / 2 ^ 113 + 221 * 9214 /
          (2 ^ 128 - 221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 + 4607)) +
            1 / 2 ^ 128) / (1 - 1 / 2 ^ 55) +
        (1 + 1 / 2 ^ 55) * (1 / 2 ^ 113 + (zkB 0 312 4607 + zkB 0 312 4607) +
          (1 / 2 ^ 128 + (2 ^ 32 : ℝ) / 2 ^ 1024)) := fun i =>
      add_le_add hεZ (mul_le_mul (by linarith) (hδ i) (hδ0 i) (by norm_num))
    refine (Finset.sum_le_sum fun i _ => hpt i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hP0 : (0 : ℝ) ≤ (1 / 2 ^ 113 + 221 * 9214 /
          (2 ^ 128 - 221 * (2 * (2 ^ 31 * 101372 + 2 ^ 64) + 9215 + 2 ^ 31 * 4607 + 4607)) +
            1 / 2 ^ 128) / (1 - 1 / 2 ^ 55) +
        (1 + 1 / 2 ^ 55) * (1 / 2 ^ 113 + (zkB 0 312 4607 + zkB 0 312 4607) +
          (1 / 2 ^ 128 + (2 ^ 32 : ℝ) / 2 ^ 1024)) := by norm_num [zkB]
    refine (mul_le_mul_of_nonneg_right hn hP0).trans ?_
    norm_num [zkB]
  -- the simulated game's error
  obtain ⟨rq, rE⟩ := romBudgets (c := 101372) hU hM (by norm_num) hq hqE
  have hr : (epsRomU (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
      (totK Arith.Moussaka.M q + (U + M) * 338)).toReal ≤ 13 / 2 ^ 63 := by
    rw [epsRomU_eq]
    refine toReal_epsRomG_le _ _ (by norm_num) rq ?_ ?_
    · rw [verifyCellBound_pRU]; exact rE
    · have := totK_le Arith.Moussaka.M hq
      have : (U + M) * 338 ≤ 2 ^ 31 * 338 := Nat.mul_le_mul (by omega) le_rfl
      omega
  have hh : ((U + M : ℕ) : ℝ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22) ≤ 1 / 2 ^ 63 := by
    have e1 := epsHitN_mono (N' := 2 ^ 31) (a' := 2 ^ 64) (b' := 2 ^ 64) (c' := 2 ^ 64)
      (N := U + M) (by omega) (hq .mu) (hq .h21) (hq .h22)
    have e0 : 0 ≤ Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22) := by
      unfold Hit.epsHitN; positivity
    have e2 : (2 ^ 31 : ℝ) * Hit.epsHitN (2 ^ 31) (2 ^ 64) (2 ^ 64) (2 ^ 64) ≤ 1 / 2 ^ 63 := by
      norm_num [Hit.epsHitN]
    have hn' : ((U + M : ℕ) : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hN31
    exact (mul_le_mul hn' e1 e0 (by norm_num)).trans e2
  have hx := extra_le hU hM
  have hr' : (epsRomU (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
      (totK Arith.Moussaka.M q + (U + M) * 338)).toReal +
      ((U + M : ℕ) : ℝ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22) +
      (U : ℝ) * (((M : ℝ) + 1) / 2 ^ 192) ≤ 15 / 2 ^ 63 := by
    have : (1 : ℝ) / 2 ^ 100 ≤ 1 / 2 ^ 63 := by norm_num
    linarith
  -- the joint step
  have hNB : (N : ℝ) * B < 1 :=
    (numJ_finalU hn (a := 0) (J := 0) (r := 0) (by norm_num) hB0 hB (by norm_num)
      (by norm_num)).1
  have hj := nmU_joint_le A hA' ivRX h3 hE hβ hJ hNB
  have hfin := (numJ_finalU hn ha hB0 hB (hJm.trans hJn) hr').2
  refine final_combineU hj ?_ hfin
  linarith

end Num

end MoussakaUnbound

end VoleMole.Theft
