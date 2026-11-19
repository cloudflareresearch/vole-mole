import VoleMole.Theft.NumTerms

/-!
# The theft and non-malleability theorems with explicit numbers

The headline theorems of `Theft/PlainTotalRom.lean` (function rows, per-kind budgets) and of
`Theft/Plain*Perm*.lean` (permutation rows, forward and inverse cipher queries) with every
non-computational term bounded by an explicit number (`Theft/NumTerms.lean`, `Theft/DeltaBound.lean`),
for adversaries with **every per-kind hash budget and the cipher budget at most `2⁶⁴`** and, in the
games with many tokens, **`U, M ≤ 2³⁰`**:

| game | theorem (function rows / permutation rows) | `X` |
|---|---|---|
| Ratatouille no theft, one Client | `noTheft_lean_num` / `noTheft_lean_numP` | `2⁻⁵⁴` |
| Ratatouille no theft, `U` Clients, `M` spends | `noTheftN_lean_num` / `noTheftN_lean_numP` | `2⁻²⁴` |
| Moussaka non-malleability, one token | `noRedirect_lean_num` / `noRedirect_lean_numP` | `2⁻⁵⁴` |
| Moussaka non-malleability, `U` tokens, `M` redemptions | `noRedirectN_lean_num` / `noRedirectN_lean_numP` | `2⁻²⁴` |
| unbound Moussaka, `U` tokens, `M` redemptions | `nmUN_lean_num` / `nmUN_lean_numP` | `2⁻²⁴` |

Each states `Pr[Bad] ≤ X + (computational terms)`: the one-wayness advantage of the explicit
inverters (`owAdv`, `owAdvK`, a computational assumption on Keccak-p[800,12]) and, for unbound
Moussaka, the PRF, binding and second-preimage advantages (`εprf`, `bindAdv`, `sprAdvN`).

**Where the numbers come from.** `X` is the sum of the zero-knowledge errors of the hops
(`zkB ≈ 223·2⁻⁶³` per hop at these budgets, dominated by the cipher term `221·q_E'·2⁻¹²⁸` with
`q_E' ≈ 2·q_E`), the collision terms (`≈ 2⁻¹⁰⁶` each), `ROM/`'s extraction error (`≤ 13·2⁻⁶³`)
and the programmed-point terms (`< 2⁻¹⁹⁰`). One Client: two hops, `≈ 2⁻⁵⁴·²`. Many tokens: one hop
per honest proof, `U + M ≤ 2³¹` hops, `≈ 223·2⁻³² ≈ 2⁻²⁴·²`: the hybrid argument loses the factor
`U + M` on the zero-knowledge error, whose cipher term is linear in the adversary's cipher budget.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## The numeric sums -/

section Sums

set_option exponentiation.threshold 1100 in
/-- **One Client or token**: the two hops, the collision term, `ROM/`'s error and the
programmed-point term are at most `2⁻⁵⁴`. -/
lemma one_le {zI zS d r e : ℝ} (hzI : zI ≤ zkB (2 ^ 65) (2 ^ 65 + 1560) (2 ^ 65 + 2 ^ 18))
    (hzS : zS ≤ zkB (2 ^ 65) (2 ^ 65 + 1560) (2 ^ 65 + 2 ^ 18))
    (hd : d ≤ 1 / 2 ^ 113 + zkB 0 312 4607 + (1 / 2 ^ 128 + 1 / 2 ^ 1024)) (hr : r ≤ 13 / 2 ^ 63)
    (he : e ≤ Hit.epsHit (2 ^ 64) (2 ^ 64) (2 ^ 64)) :
    zI + zS + d + (r + e) ≤ 1 / 2 ^ 54 := by
  have hnum : zkB (2 ^ 65) (2 ^ 65 + 1560) (2 ^ 65 + 2 ^ 18) +
      zkB (2 ^ 65) (2 ^ 65 + 1560) (2 ^ 65 + 2 ^ 18) +
      (1 / 2 ^ 113 + zkB 0 312 4607 + (1 / 2 ^ 128 + 1 / 2 ^ 1024)) +
      (13 / 2 ^ 63 + Hit.epsHit (2 ^ 64) (2 ^ 64) (2 ^ 64)) ≤ 1 / 2 ^ 54 := by
    norm_num [zkB, Hit.epsHit]
  exact (add_le_add (add_le_add (add_le_add hzI hzS) hd) (add_le_add hr he)).trans hnum

/-- The bound of `U` or `M` hops. -/
lemma mul_zk_le {n : ℕ} (hn : n ≤ 2 ^ 30) {z : ℝ} (hz0 : 0 ≤ z)
    (hz : z ≤ zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50)) :
    (n : ℝ) * z ≤ 2 ^ 30 * zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50) := by
  have hn' : (n : ℝ) ≤ 2 ^ 30 := by exact_mod_cast hn
  exact mul_le_mul hn' hz hz0 (by positivity)

set_option exponentiation.threshold 1100 in
/-- **`U` tokens and `M` proofs**: the `U + M` hops, the `U + M` collision terms, `ROM/`'s error,
the programmed-point terms and a term `≤ 2⁻¹⁰⁰` are at most `2⁻²⁴`. -/
lemma many_le' {U M : ℕ} (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) {zI zS r e x : ℝ}
    (hzI0 : 0 ≤ zI) (hzS0 : 0 ≤ zS)
    (hzI : zI ≤ zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50))
    (hzS : zS ≤ zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50)) {D : Fin (U + M) → ℝ}
    (hD : ∀ i, D i ≤ 1 / 2 ^ 113 + (zkB 0 312 4607 + zkB 0 312 4607) +
      (1 / 2 ^ 128 + ((2 * (U + M) : ℕ) : ℝ) / 2 ^ 1024))
    (hr : r ≤ 13 / 2 ^ 63) (he : e ≤ Hit.epsHitN (2 ^ 31) (2 ^ 64) (2 ^ 64) (2 ^ 64))
    (hx : x ≤ 1 / 2 ^ 100) :
    U * zI + M * zS + ∑ i, D i + (r + ((U + M : ℕ) : ℝ) * e) + x ≤ 1 / 2 ^ 24 := by
  have hN : ((U + M : ℕ) : ℝ) ≤ 2 ^ 31 := by exact_mod_cast (by omega : U + M ≤ 2 ^ 31)
  have hN2 : (((2 * (U + M) : ℕ)) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast (by omega : 2 * (U + M) ≤ 2 ^ 32)
  have hz0 : 0 ≤ zkB 0 312 4607 := zkB_nonneg _ _ _
  have hB0 : 0 ≤ 1 / 2 ^ 113 + (zkB 0 312 4607 + zkB 0 312 4607) +
      (1 / 2 ^ 128 + (2 ^ 32 : ℝ) / 2 ^ 1024) := by positivity
  have hsum : ∑ i, D i ≤ 2 ^ 31 * (1 / 2 ^ 113 + (zkB 0 312 4607 + zkB 0 312 4607) +
      (1 / 2 ^ 128 + (2 ^ 32 : ℝ) / 2 ^ 1024)) := by
    refine (Finset.sum_le_sum fun i _ => (hD i).trans (add_le_add le_rfl (add_le_add le_rfl
      (div_le_div_of_nonneg_right hN2 (by positivity))))).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hN hB0
  have hE0 : 0 ≤ Hit.epsHitN (2 ^ 31) (2 ^ 64) (2 ^ 64) (2 ^ 64) := Hit.epsHitN_nonneg _ _ _ _
  have he' : ((U + M : ℕ) : ℝ) * e ≤ 2 ^ 31 * Hit.epsHitN (2 ^ 31) (2 ^ 64) (2 ^ 64) (2 ^ 64) :=
    (mul_le_mul_of_nonneg_left he (by positivity)).trans (mul_le_mul_of_nonneg_right hN hE0)
  have hnum : 2 ^ 30 * zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50) +
      2 ^ 30 * zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50) +
      2 ^ 31 * (1 / 2 ^ 113 + (zkB 0 312 4607 + zkB 0 312 4607) +
        (1 / 2 ^ 128 + (2 ^ 32 : ℝ) / 2 ^ 1024)) +
      (13 / 2 ^ 63 + 2 ^ 31 * Hit.epsHitN (2 ^ 31) (2 ^ 64) (2 ^ 64) (2 ^ 64)) + 1 / 2 ^ 100 ≤
      1 / 2 ^ 24 := by
    norm_num [zkB, Hit.epsHitN]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (mul_zk_le hU hzI0 hzI)
    (mul_zk_le hM hzS0 hzS)) hsum) (add_le_add hr he')) hx).trans hnum

/-- `many_le'` without the extra term. -/
lemma many_le {U M : ℕ} (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) {zI zS r e : ℝ}
    (hzI0 : 0 ≤ zI) (hzS0 : 0 ≤ zS)
    (hzI : zI ≤ zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50))
    (hzS : zS ≤ zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50)) {D : Fin (U + M) → ℝ}
    (hD : ∀ i, D i ≤ 1 / 2 ^ 113 + (zkB 0 312 4607 + zkB 0 312 4607) +
      (1 / 2 ^ 128 + ((2 * (U + M) : ℕ) : ℝ) / 2 ^ 1024))
    (hr : r ≤ 13 / 2 ^ 63) (he : e ≤ Hit.epsHitN (2 ^ 31) (2 ^ 64) (2 ^ 64) (2 ^ 64)) :
    U * zI + M * zS + ∑ i, D i + (r + ((U + M : ℕ) : ℝ) * e) ≤ 1 / 2 ^ 24 := by
  have h := many_le' hU hM hzI0 hzS0 hzI hzS hD hr he (x := 0) (by positivity)
  rwa [add_zero] at h

/-- A collision term of `U` tokens, numerically. -/
lemma deltaBoundN_le {U M : ℕ} {a b : ℝ} (ha : a ≤ zkB 0 312 4607) (hb : b ≤ zkB 0 312 4607) :
    1 / 2 ^ 113 + (a + b) + (noHitProb + ((2 * (U + M) : ℕ) : ℝ) / 2 ^ 1024) ≤
      1 / 2 ^ 113 + (zkB 0 312 4607 + zkB 0 312 4607) +
        (1 / 2 ^ 128 + ((2 * (U + M) : ℕ) : ℝ) / 2 ^ 1024) :=
  add_le_add (add_le_add le_rfl (add_le_add ha hb)) (add_le_add noHitProb_le_128 le_rfl)

/-- The budgets of the hops of `U` tokens. -/
lemma hopBudgets {U M c : ℕ} (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) (hc : c ≤ 2 ^ 18) {q3 q5 qE : ℕ}
    (h3 : q3 ≤ 2 ^ 64) (h5 : q5 ≤ 2 ^ 64) (hE : qE ≤ 2 ^ 64) :
    2 * q3 ≤ 2 ^ 65 ∧ 2 * q5 + (U + M) * 312 + 312 + (U + M - 1) * 624 ≤ 2 ^ 65 + 2 ^ 41 ∧
      2 * qE + (U + M) * c + 4608 ≤ 2 ^ 65 + 2 ^ 50 := by
  have hc' : (U + M) * c ≤ 2 ^ 31 * 2 ^ 18 :=
    Nat.mul_le_mul (by omega) hc
  refine ⟨by omega, by omega, by omega⟩

/-- `ROM/`'s budgets of `U` tokens. -/
lemma romBudgets {U M c : ℕ} (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) (hc : c ≤ 2 ^ 18)
    {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64) (hE : qE ≤ 2 ^ 64) :
    (∀ k, (q + (U + M) • Ratatouille.qPre) k ≤ 2 ^ 65) ∧ qE + (U + M) * c ≤ 2 ^ 65 := by
  have hc' : (U + M) * c ≤ 2 ^ 31 * 2 ^ 18 := Nat.mul_le_mul (by omega) hc
  refine ⟨fun k => ?_, by omega⟩
  have h1 := hq k
  have h2 : (U + M) * Ratatouille.qPre k ≤ 2 ^ 31 * 313 := Nat.mul_le_mul (by omega) (qPre_le k)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  omega

end Sums

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

variable {L : ℕ}

/-- **No theft, one Client, function rows, numerically**: with every per-kind hash budget and the
cipher budget at most `2⁶⁴`, `Pr[Bad] ≤ 2⁻⁵⁴ + Adv^ow(inverter)` (`noTheft_lean_romK`). -/
theorem noTheft_lean_num
    (A : Thief Sizes.labelRows Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64)
    (hqE : qE ≤ 2 ^ 64) (hA : ∀ o₁ o₂, AdmL (QBud q qE) ansP (A.out o₁ o₂)) :
    pr _ (theftReal A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
        (extRom A q qE (totK Arith.Ratatouille.uovM q))) ≤
      1 / 2 ^ 54 +
        owAdv A.ctx (inverter A (extRom A q qE (totK Arith.Ratatouille.uovM q)) leanSimIR
          (leanProgIRX hbX) leanSimSR (leanProgSRX hbX)) := by
  have h3 := hq .h3
  have h5 := hq .h5
  have hr : (epsRom (q + qPre + qPre) (qE + verifyCellBound pS + verifyCellBound pI)
      (totK Arith.Ratatouille.uovM q + 338 + 338)).toReal ≤ 13 / 2 ^ 63 := by
    rw [epsRom_eq]
    refine toReal_epsRomG_le _ _ (by norm_num) (fun k => ?_) ?_ ?_
    · have := hq k; have := qPre_le k; simp only [Pi.add_apply]; omega
    · rw [verifyCellBound_pS, verifyCellBound_pI]; omega
    · have := totK_le Arith.Ratatouille.uovM hq; omega
  refine (noTheft_lean_romK A hL hA).trans (add_le_add (one_le ?_ ?_ ?_ hr
    (epsHit_mono (hq _) (hq _) (hq _))) le_rfl)
  · exact (εz_fn_le _ _ _ _).trans (zkB_mono (by omega) (by omega) (by omega))
  · exact (εz_fn_le _ _ _ _).trans (zkB_mono (by omega) (by omega) (by omega))
  · exact (deltaS_le (R := Blk → Blk) hbX_wf A).trans (deltaBound_le (εz_fn_le _ _ _ _) 1)

/-- **No theft, one Client, permutation rows and inverse queries, numerically**: with every
per-kind hash budget and the cipher budget (forward and inverse) at most `2⁶⁴`,
`Pr[Bad] ≤ 2⁻⁵⁴ + Adv^ow(inverter)` (`noTheft_lean_romP'`). -/
theorem noTheft_lean_numP
    (A : Thief Sizes.labelRows Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64)
    (hqE : qE ≤ 2 ^ 64) (hA : ∀ o₁ o₂, AdmL (QBudP q qE) ansQ (A.out o₁ o₂)) :
    pr _ (theftReal A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
        (extRomP A q qE)) ≤
      1 / 2 ^ 54 +
        owAdv A.ctx (inverter A (extRomP A q qE) leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX)) := by
  have h3 := hq .h3
  have h5 := hq .h5
  have hq0 : ∀ k, (q + qPre + qPre) k ≤ 2 ^ 65 := fun k => by
    have := hq k; have := qPre_le k; simp only [Pi.add_apply]; omega
  have hr : (epsRomP (q + qPre + qPre) (qE + verifyCellBound pS + verifyCellBound pI)
      (totK Arith.Ratatouille.uovM (q + qPre + qPre))).toReal ≤ 13 / 2 ^ 63 := by
    rw [epsRomP_eq]
    refine toReal_epsRomPG_le _ _ (by norm_num) hq0 ?_ ?_
    · rw [verifyCellBound_pS, verifyCellBound_pI]; omega
    · have := totK_le Arith.Ratatouille.uovM hq0; omega
  refine (noTheft_lean_romP' A hL (by omega) hA).trans (add_le_add (one_le ?_ ?_ ?_ hr
    (epsHit_mono (hq _) (hq _) (hq _))) le_rfl)
  · exact (εz_perm_le permOk_pIR _ _ _).trans (zkB_mono (by omega) (by omega) (by omega))
  · exact (εz_perm_le permOk_pSR _ _ _).trans (zkB_mono (by omega) (by omega) (by omega))
  · exact (deltaS_le (R := Equiv.Perm Blk) hbX_wf A).trans
      (deltaBound_le (εz_perm_le permOk_pSR _ _ _) 1)

variable {U M : ℕ}

set_option maxHeartbeats 4000000 in
/-- **No theft for `U` Clients and `M` spends, function rows, numerically**: with every per-kind
hash budget and the cipher budget at most `2⁶⁴` and `U, M ≤ 2³⁰`,
`Pr[Bad] ≤ 2⁻²⁴ + Σ_j Adv^ow(inverter_j)` (`noTheftN_lean_romK`). -/
theorem noTheftN_lean_num
    (A : ThiefN Sizes.labelRows U M Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64)
    (hqE : qE ≤ 2 ^ 64) (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30)
    (hA : ∀ iss sp, AdmLN (QBud q qE) ansPN (A.out iss sp)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
        (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
        (theftRealN A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
          (extRomN A q qE (totK Arith.Ratatouille.uovM q))) ≤
      1 / 2 ^ 24 +
        ∑ j : Fin (U + M), owAdvK (inverterN A leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX) (extRomN A q qE (totK Arith.Ratatouille.uovM q)) j) := by
  obtain ⟨b3, b5, bE⟩ := hopBudgets (c := 147451) hU hM (by norm_num) (hq .h3) (hq .h5) hqE
  obtain ⟨rq, rE⟩ := romBudgets (c := 142844) hU hM (by norm_num) hq hqE
  have hr : (epsRom (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pS)
      (totK Arith.Ratatouille.uovM q + (U + M) * 338)).toReal ≤ 13 / 2 ^ 63 := by
    rw [epsRom_eq]
    refine toReal_epsRomG_le _ _ (by norm_num) rq ?_ ?_
    · rw [verifyCellBound_pS]; exact rE
    · have := totK_le Arith.Ratatouille.uovM hq
      have : (U + M) * 338 ≤ 2 ^ 31 * 338 := Nat.mul_le_mul (by omega) le_rfl
      omega
  refine (noTheftN_lean_romK A hL hA).trans (add_le_add (many_le hU hM
    (ZKRow.εz_nonneg _ _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    ((εz_fn_le _ _ _ _).trans (zkB_mono b3 b5 bE)) ((εz_fn_le _ _ _ _).trans (zkB_mono b3 b5 bE))
    (fun i => (deltaNR_le (R := Blk → Blk) hbX_wf A i).trans
      (deltaBoundN_le (εz_fn_le _ _ _ _) (εz_fn_le _ _ _ _))) hr
    (epsHitN_mono (by omega) (hq _) (hq _) (hq _))) le_rfl)

set_option maxHeartbeats 4000000 in
/-- **No theft for `U` Clients and `M` spends, permutation rows, numerically**: as
`noTheftN_lean_num`, with AES as random permutations and inverse queries
(`noTheftN_lean_romP'`). -/
theorem noTheftN_lean_numP
    (A : ThiefN Sizes.labelRows U M Tab3
      (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64)
    (hqE : qE ≤ 2 ^ 64) (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30)
    (hA : ∀ iss sp, AdmLN (QBudP q qE) ansPNQ (A.out iss sp)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
        (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
        (theftRealN A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
          (extRomNP A q qE)) ≤
      1 / 2 ^ 24 +
        ∑ j : Fin (U + M), owAdvK (inverterN A leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX) (extRomNP A q qE) j) := by
  obtain ⟨b3, b5, bE⟩ := hopBudgets (c := 147451) hU hM (by norm_num) (hq .h3) (hq .h5) hqE
  obtain ⟨rq, rE⟩ := romBudgets (c := 142844) hU hM (by norm_num) hq hqE
  have hr : (epsRomP (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pS)
      (totK Arith.Ratatouille.uovM (q + (U + M) • qPre))).toReal ≤ 13 / 2 ^ 63 := by
    rw [epsRomP_eq]
    refine toReal_epsRomPG_le _ _ (by norm_num) rq ?_ ?_
    · rw [verifyCellBound_pS]; exact rE
    · have := totK_le Arith.Ratatouille.uovM rq; omega
  refine (noTheftN_lean_romP' A hL (by omega) hA).trans (add_le_add (many_le hU hM
    (ZKRow.εz_nonneg _ _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    ((εz_perm_le permOk_pIR _ _ _).trans (zkB_mono b3 b5 bE))
    ((εz_perm_le permOk_pSR _ _ _).trans (zkB_mono b3 b5 bE))
    (fun i => (deltaNR_le (R := Equiv.Perm Blk) hbX_wf A i).trans
      (deltaBoundN_le (εz_perm_le permOk_pIR _ _ _) (εz_perm_le permOk_pSR _ _ _))) hr
    (epsHitN_mono (by omega) (hq _) (hq _) (hq _))) le_rfl)

end Ratatouille

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka
open VoleMole.Theft.Ratatouille (qPre)

variable {L : ℕ}

/-- **Redemption non-malleability, one token, function rows, numerically**: with every per-kind
hash budget and the cipher budget at most `2⁶⁴`, `Pr[Bad] ≤ 2⁻⁵⁴ + Adv^ow(inverter)`
(`noRedirect_lean_romK`). -/
theorem noRedirect_lean_num (A : Thief Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
    (hw : Hit.Mous.HitWf A) {kt : Bytes → UOVKey} (hk : KeysOut A kt) (hL : Lrom ≤ L)
    {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64) (hqE : qE ≤ 2 ^ 64)
    (hA : ∀ o₁ o₂, AdmL (QBud q qE) ansP (A.out o₁ o₂)) :
    pr _ (nmReal A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX)
        (extRomM q qE (totK Arith.Moussaka.M q))) ≤
      1 / 2 ^ 54 +
        owAdv A.ci A.cr (inverter A (extRomM q qE (totK Arith.Moussaka.M q)) (leanSim pI)
          (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)) := by
  have h3 := hq .h3
  have h5 := hq .h5
  have hr : (epsRomM (q + qPre + qPre) (qE + verifyCellBound pR + verifyCellBound pI)
      (totK Arith.Moussaka.M q + 338 + 338)).toReal ≤ 13 / 2 ^ 63 := by
    rw [epsRomM_eq]
    refine toReal_epsRomG_le _ _ (by norm_num) (fun k => ?_) ?_ ?_
    · have := hq k; have := qPre_le k; simp only [Pi.add_apply]; omega
    · rw [verifyCellBound_pR, verifyCellBound_pIm]; omega
    · have := totK_le Arith.Moussaka.M hq; omega
  refine (noRedirect_lean_romK A hw hk hL hA).trans (add_le_add (one_le ?_ ?_ ?_ hr
    (epsHit_mono (hq _) (hq _) (hq _))) le_rfl)
  · exact (εz_fn_le _ _ _ _).trans (zkB_mono (by omega) (by omega) (by omega))
  · exact (εz_fn_le _ _ _ _).trans (zkB_mono (by omega) (by omega) (by omega))
  · exact (deltaR_le (R := Blk → Blk) hbX_wf A).trans (deltaBound_le (εz_fn_le _ _ _ _) 1)

/-- **Redemption non-malleability, one token, permutation rows and inverse queries,
numerically**: `Pr[Bad] ≤ 2⁻⁵⁴ + Adv^ow(inverter)` (`noRedirect_lean_romP'`). -/
theorem noRedirect_lean_numP
    (A : Thief Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
    (hw : Hit.Mous.HitWf A) {kt : Bytes → UOVKey} (hk : KeysOut A kt) (hL : Lrom ≤ L)
    {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64) (hqE : qE ≤ 2 ^ 64)
    (hA : ∀ o₁ o₂, AdmL (QBudP q qE) ansQ (A.out o₁ o₂)) :
    pr _ (nmReal A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extRomMP q qE)) ≤
      1 / 2 ^ 54 +
        owAdv A.ci A.cr (inverter A (extRomMP q qE) (leanSim pI) (leanProgIX hbX) (leanSim pR)
          (leanProgRX hbX)) := by
  have h3 := hq .h3
  have h5 := hq .h5
  have hq0 : ∀ k, (q + qPre + qPre) k ≤ 2 ^ 65 := fun k => by
    have := hq k; have := qPre_le k; simp only [Pi.add_apply]; omega
  have hr : (epsRomMP (q + qPre + qPre) (qE + verifyCellBound pR + verifyCellBound pI)
      (totK Arith.Moussaka.M (q + qPre + qPre))).toReal ≤ 13 / 2 ^ 63 := by
    rw [epsRomMP_eq]
    refine toReal_epsRomPG_le _ _ (by norm_num) hq0 ?_ ?_
    · rw [verifyCellBound_pR, verifyCellBound_pIm]; omega
    · have := totK_le Arith.Moussaka.M hq0; omega
  refine (noRedirect_lean_romP' A hw hk hL (by omega) hA).trans (add_le_add (one_le ?_ ?_ ?_ hr
    (epsHit_mono (hq _) (hq _) (hq _))) le_rfl)
  · exact (εz_perm_le permOk_pIM _ _ _).trans (zkB_mono (by omega) (by omega) (by omega))
  · exact (εz_perm_le permOk_pRM _ _ _).trans (zkB_mono (by omega) (by omega) (by omega))
  · exact (deltaR_le (R := Equiv.Perm Blk) hbX_wf A).trans
      (deltaBound_le (εz_perm_le permOk_pRM _ _ _) 1)

variable {U M : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Redemption non-malleability for `U` tokens and `M` redemptions, function rows,
numerically**: with every per-kind hash budget and the cipher budget at most `2⁶⁴` and
`U, M ≤ 2³⁰`, `Pr[Bad] ≤ 2⁻²⁴ + Σ_h Adv^ow(inverter_h)` (`noRedirectN_lean_romK`). -/
theorem noRedirectN_lean_num
    (A : ThiefN U M Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
    (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutN A kt) (hL : Lrom ≤ L)
    {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64) (hqE : qE ≤ 2 ^ 64) (hU : U ≤ 2 ^ 30)
    (hM : M ≤ 2 ^ 30) (hA : ∀ reqs reds, AdmLN (QBud q qE) ansPN (A.out reqs reds)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
        (nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX)
          (extRomMN q qE (totK Arith.Moussaka.M q))) ≤
      1 / 2 ^ 24 +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)
            (extRomMN q qE (totK Arith.Moussaka.M q)) h) := by
  obtain ⟨b3, b5, bE⟩ := hopBudgets (c := 73723) hU hM (by norm_num) (hq .h3) (hq .h5) hqE
  obtain ⟨rq, rE⟩ := romBudgets (c := 69116) hU hM (by norm_num) hq hqE
  have hr : (epsRomM (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
      (totK Arith.Moussaka.M q + (U + M) * 338)).toReal ≤ 13 / 2 ^ 63 := by
    rw [epsRomM_eq]
    refine toReal_epsRomG_le _ _ (by norm_num) rq ?_ ?_
    · rw [verifyCellBound_pR]; exact rE
    · have := totK_le Arith.Moussaka.M hq
      have : (U + M) * 338 ≤ 2 ^ 31 * 338 := Nat.mul_le_mul (by omega) le_rfl
      omega
  refine (noRedirectN_lean_romK A hw hk hL hA).trans (add_le_add (many_le hU hM
    (ZKRow.εz_nonneg _ _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    ((εz_fn_le _ _ _ _).trans (zkB_mono b3 b5 bE)) ((εz_fn_le _ _ _ _).trans (zkB_mono b3 b5 bE))
    (fun i => (deltaNM_le (R := Blk → Blk) hbX_wf A i).trans
      (deltaBoundN_le (εz_fn_le _ _ _ _) (εz_fn_le _ _ _ _))) hr
    (epsHitN_mono (by omega) (hq _) (hq _) (hq _))) le_rfl)

set_option maxHeartbeats 4000000 in
/-- **Redemption non-malleability for `U` tokens and `M` redemptions, permutation rows,
numerically**: as `noRedirectN_lean_num`, with AES as random permutations and inverse queries
(`noRedirectN_lean_romP'`). -/
theorem noRedirectN_lean_numP
    (A : ThiefN U M Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
    (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutN A kt) (hL : Lrom ≤ L)
    {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64) (hqE : qE ≤ 2 ^ 64) (hU : U ≤ 2 ^ 30)
    (hM : M ≤ 2 ^ 30) (hA : ∀ reqs reds, AdmLN (QBudP q qE) ansPNQ (A.out reqs reds)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
        (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
        (nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extRomMNP q qE)) ≤
      1 / 2 ^ 24 +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)
            (extRomMNP q qE) h) := by
  obtain ⟨b3, b5, bE⟩ := hopBudgets (c := 73723) hU hM (by norm_num) (hq .h3) (hq .h5) hqE
  obtain ⟨rq, rE⟩ := romBudgets (c := 69116) hU hM (by norm_num) hq hqE
  have hr : (epsRomMP (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
      (totK Arith.Moussaka.M (q + (U + M) • qPre))).toReal ≤ 13 / 2 ^ 63 := by
    rw [epsRomMP_eq]
    refine toReal_epsRomPG_le _ _ (by norm_num) rq ?_ ?_
    · rw [verifyCellBound_pR]; exact rE
    · have := totK_le Arith.Moussaka.M rq; omega
  refine (noRedirectN_lean_romP' A hw hk hL (by omega) hA).trans (add_le_add (many_le hU hM
    (ZKRow.εz_nonneg _ _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    ((εz_perm_le permOk_pIM _ _ _).trans (zkB_mono b3 b5 bE))
    ((εz_perm_le permOk_pRM _ _ _).trans (zkB_mono b3 b5 bE))
    (fun i => (deltaNM_le (R := Equiv.Perm Blk) hbX_wf A i).trans
      (deltaBoundN_le (εz_perm_le permOk_pIM _ _ _) (εz_perm_le permOk_pRM _ _ _))) hr
    (epsHitN_mono (by omega) (hq _) (hq _) (hq _))) le_rfl)

end Moussaka

namespace MoussakaUnbound

open VoleMole.Privacy.MoussakaUnbound
open VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (AnchorSet ctxBytes proveSeedBytes nfBytes)
open VoleMole.Privacy.Moussaka (ShM leanSim)
open VoleMole.Theft.Ratatouille (qPre)

variable {U M L : ℕ}

/-- The extra term of unbound Moussaka: `U·(M + 1)·2⁻¹⁹²` (the honest keys' uniqueness), split off
the per-token computational terms. -/
lemma sum_split (U M : ℕ) (a : ℝ) (b s : Fin U → ℝ) :
    ∑ h : Fin U, (a + ((M : ℝ) + 1) / 2 ^ 192 + b h + s h) =
      ∑ h : Fin U, (a + b h + s h) + U * (((M : ℝ) + 1) / 2 ^ 192) := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

lemma extra_le (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) :
    (U : ℝ) * (((M : ℝ) + 1) / 2 ^ 192) ≤ 1 / 2 ^ 100 := by
  have hU' : (U : ℝ) ≤ 2 ^ 30 := by exact_mod_cast hU
  have hM' : (M : ℝ) ≤ 2 ^ 30 := by exact_mod_cast hM
  calc (U : ℝ) * (((M : ℝ) + 1) / 2 ^ 192) ≤ 2 ^ 30 * ((2 ^ 30 + 1) / 2 ^ 192) := by gcongr
    _ ≤ 1 / 2 ^ 100 := by norm_num

set_option maxHeartbeats 4000000 in
/-- **Unbound non-malleability for `U` tokens and `M` redemptions, function rows, numerically**:
with every per-kind hash budget and the cipher budget at most `2⁶⁴` and `U, M ≤ 2³⁰`,

    Pr[Bad] ≤ 2⁻²⁴ + Σ_h (ε_prf + Adv^bind(B₁ h) + Adv^spr-k(B₂ h))

(`nmUN_lean_romK`; its `U·(M + 1)·2⁻¹⁹²` is in `2⁻²⁴`). -/
theorem nmUN_lean_num
    (A : ThiefN U M Tab3 (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
    (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutNU A kt) (hL : LminU ≤ L)
    {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64) (hqE : qE ≤ 2 ^ 64) (hU : U ≤ 2 ^ 30)
    (hM : M ≤ 2 ^ 30) (hA : ∀ reqs reds, AdmLN (QBud q qE) ansPN (A.out reqs reds)) {εprf : ℝ}
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
      (leanProgRUX hbX) (extRomUN q qE (totK Arith.Moussaka.M q)) h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
        (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
        (nmRealNE A (leanPIUX hbX) (leanPRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE (totK Arith.Moussaka.M q)))) ≤
      1 / 2 ^ 24 +
        ∑ h : Fin U, (εprf +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
            (extRomUN q qE (totK Arith.Moussaka.M q)) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) (extRomUN q qE (totK Arith.Moussaka.M q)) h)) := by
  obtain ⟨b3, b5, bE⟩ := hopBudgets (c := 105979) hU hM (by norm_num) (hq .h3) (hq .h5) hqE
  obtain ⟨rq, rE⟩ := romBudgets (c := 101372) hU hM (by norm_num) hq hqE
  have hr : (epsRomU (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
      (totK Arith.Moussaka.M q + (U + M) * 338)).toReal ≤ 13 / 2 ^ 63 := by
    rw [epsRomU_eq]
    refine toReal_epsRomG_le _ _ (by norm_num) rq ?_ ?_
    · rw [verifyCellBound_pRU]; exact rE
    · have := totK_le Arith.Moussaka.M hq
      have : (U + M) * 338 ≤ 2 ^ 31 * 338 := Nat.mul_le_mul (by omega) le_rfl
      omega
  refine (nmUN_lean_romK A hw hk hL hA pts hpts hprf).trans ?_
  rw [sum_split, ← add_assoc, add_right_comm]
  exact add_le_add (many_le' hU hM (ZKRow.εz_nonneg _ _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    ((εz_fn_le _ _ _ _).trans (zkB_mono b3 b5 bE)) ((εz_fn_le _ _ _ _).trans (zkB_mono b3 b5 bE))
    (fun i => (deltaNU_le (R := Blk → Blk) hbX_wf A i).trans
      (deltaBoundN_le (εz_fn_le _ _ _ _) (εz_fn_le _ _ _ _))) hr
    (epsHitN_mono (by omega) (hq _) (hq _) (hq _)) (extra_le hU hM)) le_rfl

set_option maxHeartbeats 4000000 in
/-- **Unbound non-malleability for `U` tokens and `M` redemptions, permutation rows,
numerically**: as `nmUN_lean_num`, with AES as random permutations and inverse queries
(`nmUN_lean_romP'`). -/
theorem nmUN_lean_numP
    (A : ThiefN U M Tab3 (ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
    (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutNU A kt) (hL : LminU ≤ L)
    {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64) (hqE : qE ≤ 2 ^ 64) (hU : U ≤ 2 ^ 30)
    (hM : M ≤ 2 ^ 30) (hA : ∀ reqs reds, AdmLN (QBudP q qE) ansPNQ (A.out reqs reds)) {εprf : ℝ}
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
      (leanProgRUX hbX) (extRomUNP q qE) h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
        (ShX (Equiv.Perm Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
        (nmRealNE A (leanPIUX hbX) (leanPRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extRomUNP q qE))) ≤
      1 / 2 ^ 24 +
        ∑ h : Fin U, (εprf +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
            (extRomUNP q qE) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) (extRomUNP q qE) h)) := by
  obtain ⟨b3, b5, bE⟩ := hopBudgets (c := 105979) hU hM (by norm_num) (hq .h3) (hq .h5) hqE
  obtain ⟨rq, rE⟩ := romBudgets (c := 101372) hU hM (by norm_num) hq hqE
  have hr : (epsRomUP (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
      (totK Arith.Moussaka.M (q + (U + M) • qPre))).toReal ≤ 13 / 2 ^ 63 := by
    rw [epsRomUP_eq]
    refine toReal_epsRomPG_le _ _ (by norm_num) rq ?_ ?_
    · rw [verifyCellBound_pRU]; exact rE
    · have := totK_le Arith.Moussaka.M rq; omega
  refine (nmUN_lean_romP' A hw hk hL (by omega) hA pts hpts hprf).trans ?_
  rw [sum_split, ← add_assoc, add_right_comm]
  exact add_le_add (many_le' hU hM (ZKRow.εz_nonneg _ _ _ _) (ZKRow.εz_nonneg _ _ _ _)
    ((εz_perm_le permOk_pIU _ _ _).trans (zkB_mono b3 b5 bE))
    ((εz_perm_le permOk_pRU _ _ _).trans (zkB_mono b3 b5 bE))
    (fun i => (deltaNU_le (R := Equiv.Perm Blk) hbX_wf A i).trans
      (deltaBoundN_le (εz_perm_le permOk_pIU _ _ _) (εz_perm_le permOk_pRU _ _ _))) hr
    (epsHitN_mono (by omega) (hq _) (hq _) (hq _)) (extra_le hU hM)) le_rfl

end MoussakaUnbound

end VoleMole.Theft
