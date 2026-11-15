import VoleMole.Theft.DeltaBound
import VoleMole.ZK.ReadsMany
import VoleMole.Theft.PlainTotalRom
import VoleMole.Theft.PlainRataPermReads
import VoleMole.Theft.PlainMousPermReads
import VoleMole.Theft.PlainRataManyPerm
import VoleMole.Theft.PlainMousManyPerm
import VoleMole.Theft.PlainUnboundManyPerm

/-!
# The terms of the theft theorems, numerically

The theft and non-malleability theorems with `ROM/`'s plain extraction (`*_lean_romK`,
`*_lean_romP'`) bound `Pr[Bad]` by sums of symbolic terms. Here each is bounded by an explicit
number for adversaries with every per-kind hash budget and the cipher budget at most `2⁶⁴`, and
`U, M ≤ 2³⁰`:

* **Zero knowledge** (`εz_fn_le`, `εz_perm_le`): `ZKRow.εz R p q₃ q₅ q_E ≤ zkB q₃ q₅ q_E` for
  function rows (`εRO`) and for permutation rows (`εROPm p`, at the six parameter sets of the
  theft games: `nHi p = 1`, `switchEps p ≤ 28102·2⁻¹²⁸`), with

      zkB q₃ q₅ q_E = q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(q_E + 9214)/(2¹²⁸ − 2) + 28102·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸.

  At the hops' budgets of one Client (`q₃ ≤ 2⁶⁵`, `q₅, q_E ≤ 2⁶⁵ + 2¹⁸`) this is about
  `223·2⁻⁶³ ≈ 2⁻⁵⁵·²`; the cipher term `221·q_E·2⁻¹²⁸` dominates.
* **`ROM/`'s extraction error** (`toReal_epsRomG_le`, `toReal_epsRomPG_le`): `epsRom`, `epsRomM`,
  `epsRomU` (one generic `epsRomG`) and the permutation versions (`epsRomPG`) are at most
  `13·2⁻⁶³` for per-kind budgets `≤ 2⁶⁵`, `q_E ≤ 2⁶⁵` and `n_G ≤ 2⁷⁰` (the `H₂³` and `H₂²` terms,
  `9·q₂₃·2⁻¹²⁸` and `3·q₂₂·2⁻¹²⁸`, dominate).
* **The programmed-point terms** (`epsHit_le`, `epsHitN_le`) are monotone; at `2⁶⁴` they are below
  `2⁻¹⁹⁰`.
* `qPre_le`, `totK_le`: the extractor's and the reduction's per-kind queries, `≤ 313` per kind,
  and the total over the ten kinds of the tables.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset
open scoped ENNReal

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC

/-! ## Zero knowledge -/

section ZK

/-- **A numeric bound for the zero-knowledge error** of both row types. -/
noncomputable def zkB (q3 q5 qE : ℕ) : ℝ :=
  q3 / 2 ^ 128 + 1 / 2 ^ 113 + 221 * (qE + 9214) / (2 ^ 128 - 2) + 28102 / 2 ^ 128 +
    (q5 + 1) / 2 ^ 128

lemma zkB_mono {q3 q5 qE q3' q5' qE' : ℕ} (h3 : q3 ≤ q3') (h5 : q5 ≤ q5') (hE : qE ≤ qE') :
    zkB q3 q5 qE ≤ zkB q3' q5' qE' := by
  unfold zkB
  have h3' : (q3 : ℝ) ≤ q3' := by exact_mod_cast h3
  have h5' : (q5 : ℝ) ≤ q5' := by exact_mod_cast h5
  have hE' : (qE : ℝ) ≤ qE' := by exact_mod_cast hE
  have hd : (0 : ℝ) < 2 ^ 128 - 2 := by norm_num
  gcongr

lemma zkB_nonneg (q3 q5 qE : ℕ) : 0 ≤ zkB q3 q5 qE := by
  unfold zkB
  have hd : (0 : ℝ) < 2 ^ 128 - 2 := by norm_num
  positivity

/-- **Function rows**: `εRO ≤ zkB`. -/
lemma εz_fn_le (p : Params) (q3 q5 qE : ℕ) : ZKRow.εz (Blk → Blk) p q3 q5 qE ≤ zkB q3 q5 qE := by
  rw [ZKRow.εz_fn]
  unfold εRO zkB
  have hE : (221 * (4607 + (qE + 4607)) / 2 ^ 128 : ℝ) ≤ 221 * (qE + 9214) / (2 ^ 128 - 2) := by
    rw [show (4607 + (qE + 4607) : ℝ) = qE + 9214 by ring]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) ≤ 28102 / 2 ^ 128 := by positivity
  linarith

/-- The parameter sets whose permutation-row error `zkB` bounds: one hidden-row block and at most
`56` VOLE column blocks. -/
def PermOk (p : Params) : Prop := nHi p = 1 ∧ p.voleColBlocks ≤ 56

lemma switchEps_le {p : Params} (hp : PermOk p) : switchEps p ≤ 28102 / 2 ^ 128 := by
  unfold switchEps
  rw [hp.1]
  have h : (BAVC.tau * (2 + p.voleColBlocks).choose 2 + (1 + 1).choose 2 : ℕ) ≤ 28102 := by
    have hc : (2 + p.voleColBlocks).choose 2 ≤ (2 + 56).choose 2 :=
      Nat.choose_le_choose 2 (by have := hp.2; omega)
    have ht : BAVC.tau = 17 := rfl
    rw [ht]
    have : (2 + 56).choose 2 = 1653 := by decide
    have : (1 + 1).choose 2 = 1 := by decide
    omega
  have h' : ((BAVC.tau * (2 + p.voleColBlocks).choose 2 + (1 + 1).choose 2 : ℕ) : ℝ) ≤ 28102 := by
    exact_mod_cast h
  exact div_le_div_of_nonneg_right h' (by positivity)

/-- **Permutation rows**: `εROPm p ≤ zkB` for the parameter sets with `PermOk`. -/
lemma εz_perm_le {p : Params} (hp : PermOk p) (q3 q5 qE : ℕ) :
    ZKRow.εz (Equiv.Perm Blk) p q3 q5 qE ≤ zkB q3 q5 qE := by
  show εROPm p q3 q5 qE ≤ zkB q3 q5 qE
  unfold εROPm zkB
  rw [hp.1]
  have hs := switchEps_le hp
  have e : ((2 ^ 128 - (1 + 1) : ℕ) : ℝ) = 2 ^ 128 - 2 := by norm_num
  rw [e, show (4607 + (qE + 4607) : ℝ) = qE + 9214 by ring]
  linarith

lemma permOk_pIR : PermOk Privacy.Ratatouille.pI := by
  unfold PermOk; exact ⟨rfl, by decide⟩
lemma permOk_pSR : PermOk Privacy.Ratatouille.pS := by
  unfold PermOk; exact ⟨rfl, by decide⟩
lemma permOk_pIM : PermOk Privacy.Moussaka.pI := by
  unfold PermOk; exact ⟨rfl, by decide⟩
lemma permOk_pRM : PermOk Privacy.Moussaka.pR := by
  unfold PermOk; exact ⟨rfl, by decide⟩
lemma permOk_pIU : PermOk Privacy.MoussakaUnbound.pI := by
  unfold PermOk; exact ⟨rfl, by decide⟩
lemma permOk_pRU : PermOk Privacy.MoussakaUnbound.pR := by
  unfold PermOk; exact ⟨rfl, by decide⟩

/-- **A collision term**, numerically: the bound of `Theft/DeltaBound.lean` with `zkB` and
`noHitProb ≤ 2⁻¹²⁸`. -/
lemma deltaBound_le {a : ℝ} (ha : a ≤ zkB 0 312 4607) (c : ℝ) :
    1 / 2 ^ 113 + a + (noHitProb + c / 2 ^ 1024) ≤
      1 / 2 ^ 113 + zkB 0 312 4607 + (1 / 2 ^ 128 + c / 2 ^ 1024) :=
  add_le_add (add_le_add le_rfl ha) (add_le_add noHitProb_le_128 le_rfl)

end ZK

/-! ## `ROM/`'s extraction error -/

section Rom

/-- **The error of `ROM/`'s simultaneous extraction for two outputs**, function rows, with the
quicksilver parameter `n` and the combination's `M` (`epsRom`, `epsRomM`, `epsRomU`). -/
noncomputable def epsRomG (n M : ℕ) (q : Kind → ℕ) (qE nG : ℕ) : ℝ≥0∞ :=
  (q .h21 + 2) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 2) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 2) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    chainHitEpsCombSim q M 2 + stmtBindEpsSim q 2 + 2 * failEps q qE

/-- **The same in the permutation model** (`epsRomP`, `epsRomMP`, `epsRomUP`). -/
noncomputable def epsRomPG (n M : ℕ) (q : Kind → ℕ) (qE nG : ℕ) : ℝ≥0∞ :=
  (q .h21 + 2) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 2) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((nG + 2 * q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 2) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    chainHitEpsCombSim q M 2 + stmtBindEpsSim q 2 + 2 * failEpsP q qE

lemma epsRom_eq (q : Kind → ℕ) (qE nG : ℕ) :
    epsRom q qE nG = epsRomG 12282 Arith.Ratatouille.uovM q qE nG := rfl
lemma epsRomM_eq (q : Kind → ℕ) (qE nG : ℕ) :
    Moussaka.epsRomM q qE nG = epsRomG 4409 Arith.Moussaka.M q qE nG := rfl
lemma epsRomU_eq (q : Kind → ℕ) (qE nG : ℕ) :
    MoussakaUnbound.epsRomU q qE nG = epsRomG 7929 Arith.Moussaka.M q qE nG := rfl
lemma epsRomP_eq (q : Kind → ℕ) (qE nG : ℕ) :
    epsRomP q qE nG = epsRomPG 12282 Arith.Ratatouille.uovM q qE nG := rfl
lemma epsRomMP_eq (q : Kind → ℕ) (qE nG : ℕ) :
    Moussaka.epsRomMP q qE nG = epsRomPG 4409 Arith.Moussaka.M q qE nG := rfl
lemma epsRomUP_eq (q : Kind → ℕ) (qE nG : ℕ) :
    MoussakaUnbound.epsRomUP q qE nG = epsRomPG 7929 Arith.Moussaka.M q qE nG := rfl

lemma epsRomG_mono (n M : ℕ) {q q' : Kind → ℕ} {qE qE' nG nG' : ℕ} (hq : ∀ k, q k ≤ q' k)
    (hE : qE ≤ qE') (hG : nG ≤ nG') : epsRomG n M q qE nG ≤ epsRomG n M q' qE' nG' := by
  simp only [epsRomG, chainHitEpsCombSim, chainHitEpsSim, stmtBindEpsSim, failEps, openHashEps,
    ladderEps]
  gcongr <;> exact hq _

lemma epsRomPG_mono (n M : ℕ) {q q' : Kind → ℕ} {qE qE' nG nG' : ℕ} (hq : ∀ k, q k ≤ q' k)
    (hE : qE ≤ qE') (hG : nG ≤ nG') : epsRomPG n M q qE nG ≤ epsRomPG n M q' qE' nG' := by
  simp only [epsRomPG, chainHitEpsCombSim, chainHitEpsSim, stmtBindEpsSim, failEpsP, openHashEps,
    ladderEps]
  gcongr <;> first | exact hq _ | exact pE_mono hE | exact pE_mono (by omega)

lemma epsQS_nonneg' (n : ℕ) : 0 ≤ Seed.epsQS (2 ^ 128) (2 ^ 64) n := by
  unfold Seed.epsQS; positivity

set_option exponentiation.threshold 1100 in
/-- **`epsRomG` at the largest budgets**: `≤ 13·2⁻⁶³`. -/
lemma toReal_epsRomG_top (n M : ℕ) (hn : n ≤ 2 ^ 32) :
    (epsRomG n M (fun _ => 2 ^ 65) (2 ^ 65) (2 ^ 70)).toReal ≤ 13 / 2 ^ 63 := by
  have hQS := VoleMole.Prob.epsQS_le hn
  simp only [epsRomG, chainHitEpsCombSim, chainHitEpsSim, stmtBindEpsSim, failEps, openHashEps,
    ladderEps, ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ne_eq, ENNReal.add_eq_top,
    ENNReal.mul_eq_top, ENNReal.div_eq_top, ENNReal.natCast_ne_top, ENNReal.ofNat_ne_top,
    ENNReal.inv_eq_top, ENNReal.pow_eq_top_iff, ENNReal.ofReal_ne_top, not_false_eq_true, and_true,
    false_and, and_false, pow_eq_zero_iff, OfNat.ofNat_ne_zero, ENNReal.inv_eq_zero, or_self,
    ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_ofReal (epsQS_nonneg' n)]
  norm_num [verifierTotal] at hQS ⊢
  linarith

set_option exponentiation.threshold 1100 in
/-- **`epsRomPG` at the largest budgets**: `≤ 13·2⁻⁶³`. -/
lemma toReal_epsRomPG_top (n M : ℕ) (hn : n ≤ 2 ^ 32) :
    (epsRomPG n M (fun _ => 2 ^ 65) (2 ^ 65) (2 ^ 70)).toReal ≤ 13 / 2 ^ 63 := by
  have h1 : ¬ ((2 : ℕ) ^ 128 - 2 ^ 65 = 0) := by norm_num
  have h2 : ¬ ((2 : ℕ) ^ 128 - (2 ^ 65 + 4607) = 0) := by norm_num
  have hQS := VoleMole.Prob.epsQS_le hn
  simp only [epsRomPG, chainHitEpsCombSim, chainHitEpsSim, stmtBindEpsSim, failEpsP, openHashEps,
    ladderEps, pE, ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ne_eq, ENNReal.add_eq_top,
    ENNReal.mul_eq_top, ENNReal.div_eq_top, ENNReal.natCast_ne_top, ENNReal.ofNat_ne_top,
    ENNReal.inv_eq_top, ENNReal.pow_eq_top_iff, ENNReal.ofReal_ne_top, not_false_eq_true, and_true,
    false_and, and_false, pow_eq_zero_iff, OfNat.ofNat_ne_zero, ENNReal.inv_eq_zero, or_self,
    ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_ofReal (epsQS_nonneg' n),
    Nat.cast_eq_zero, h1, h2]
  norm_num [verifierTotal] at hQS ⊢
  linarith

/-- **`ROM/`'s extraction error, numerically** (function rows): `≤ 13·2⁻⁶³` for per-kind budgets
`≤ 2⁶⁵`, `q_E ≤ 2⁶⁵`, `n_G ≤ 2⁷⁰`. -/
lemma toReal_epsRomG_le (n M : ℕ) (hn : n ≤ 2 ^ 32) {q : Kind → ℕ} {qE nG : ℕ}
    (hq : ∀ k, q k ≤ 2 ^ 65) (hE : qE ≤ 2 ^ 65) (hG : nG ≤ 2 ^ 70) :
    (epsRomG n M q qE nG).toReal ≤ 13 / 2 ^ 63 := by
  have htop : epsRomG n M (fun _ => 2 ^ 65) (2 ^ 65) (2 ^ 70) ≠ ⊤ := by
    simp [epsRomG, chainHitEpsCombSim, chainHitEpsSim, stmtBindEpsSim, failEps, openHashEps,
      ladderEps, ENNReal.mul_eq_top, ENNReal.div_eq_top]
  exact (ENNReal.toReal_mono htop (epsRomG_mono n M hq hE hG)).trans (toReal_epsRomG_top n M hn)

lemma epsRomPG_ne_top (n M : ℕ) (q : Kind → ℕ) {qE : ℕ} (nG : ℕ) (hqE : qE + 4607 < 2 ^ 128) :
    epsRomPG n M q qE nG ≠ ⊤ := by
  have h1 : pE qE ≠ ⊤ := pE_ne_top (by omega)
  have h2 : pE (qE + 4607) ≠ ⊤ := pE_ne_top hqE
  simp [epsRomPG, chainHitEpsCombSim, chainHitEpsSim, stmtBindEpsSim, failEpsP, openHashEps,
    ladderEps, ENNReal.mul_eq_top, ENNReal.div_eq_top, h1, h2]

/-- **`ROM/`'s extraction error, numerically** (permutation rows): `≤ 13·2⁻⁶³` for per-kind
budgets `≤ 2⁶⁵`, `q_E ≤ 2⁶⁵`, `n_G ≤ 2⁷⁰`. -/
lemma toReal_epsRomPG_le (n M : ℕ) (hn : n ≤ 2 ^ 32) {q : Kind → ℕ} {qE nG : ℕ}
    (hq : ∀ k, q k ≤ 2 ^ 65) (hE : qE ≤ 2 ^ 65) (hG : nG ≤ 2 ^ 70) :
    (epsRomPG n M q qE nG).toReal ≤ 13 / 2 ^ 63 := by
  have htop := epsRomPG_ne_top n M (fun _ => 2 ^ 65) (qE := 2 ^ 65) (2 ^ 70) (by norm_num)
  exact (ENNReal.toReal_mono htop (epsRomPG_mono n M hq hE hG)).trans (toReal_epsRomPG_top n M hn)

end Rom

/-! ## The programmed-point terms and the budgets -/

section Hit

lemma epsHit_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    Hit.epsHit a b c ≤ Hit.epsHit a' b' c' := by
  unfold Hit.epsHit
  have ha' : ((a + 3 : ℕ) : ℝ) ≤ (a' + 3 : ℕ) := by exact_mod_cast Nat.add_le_add_right ha 3
  have hb' : ((b + 3 : ℕ) : ℝ) ≤ (b' + 3 : ℕ) := by exact_mod_cast Nat.add_le_add_right hb 3
  have hc' : ((c + 3 : ℕ) : ℝ) ≤ (c' + 3 : ℕ) := by exact_mod_cast Nat.add_le_add_right hc 3
  gcongr

lemma epsHitN_mono {N a b c N' a' b' c' : ℕ} (hN : N ≤ N') (ha : a ≤ a') (hb : b ≤ b')
    (hc : c ≤ c') : Hit.epsHitN N a b c ≤ Hit.epsHitN N' a' b' c' := by
  unfold Hit.epsHitN
  have ha' : ((a + N + 1 : ℕ) : ℝ) ≤ (a' + N' + 1 : ℕ) := by exact_mod_cast (by omega)
  have hb' : ((b + N + 1 : ℕ) : ℝ) ≤ (b' + N' + 1 : ℕ) := by exact_mod_cast (by omega)
  have hc' : ((c + N + 1 : ℕ) : ℝ) ≤ (c' + N' + 1 : ℕ) := by exact_mod_cast (by omega)
  gcongr

/-- The extractor's and the prefix reduction's queries, per kind. -/
lemma qPre_le (k : Kind) : Ratatouille.qPre k ≤ 313 := by
  cases k <;> simp [Ratatouille.qPre, extractorQueries, vPreQueries]

/-- The total over the ten kinds of the tables. -/
lemma totK_le (M : ℕ) {q : Kind → ℕ} {B : ℕ} (hq : ∀ k, q k ≤ B) : totK M q ≤ 10 * B := by
  unfold totK
  refine (Finset.sum_le_card_nsmul _ _ B fun k _ => hq k).trans ?_
  rw [smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  unfold kindsT
  refine (Finset.card_insert_le _ _).trans ?_
  refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
  refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
  simp

end Hit

end VoleMole.Theft
