import VoleMole.Theft.Num

/-!
# The many-token theft theorems, numerically, linear in the number of honest proofs

`Theft/Num.lean` states the many-token theorems at the largest numbers of proofs they allow,
`U, M ≤ 2³⁰`, with the bound `2⁻²⁴`. The bound is linear in `U + M`: each honest proof pays one
zero-knowledge hop (`zkB ≈ 223·2⁻⁶³` at the hops' budgets), one collision term (`≈ 2⁻¹⁰⁵`) and one
programmed-point term (`< 2⁻¹⁹⁰`), and the game pays `ROM/`'s extraction error (`≤ 13·2⁻⁶³`) once.
Here the same theorems state that bound for every `U, M ≤ 2³⁰`, with every per-kind hash budget
and the cipher budget at most `2⁶⁴`:

    Pr[Bad] ≤ (U + M)·2⁻⁵⁵ + 2⁻⁵⁹ + (computational terms)

| game | theorem (function rows / permutation rows) |
|---|---|
| Ratatouille no theft, `U` Clients, `M` spends | `noTheftN_lean_numL` / `noTheftN_lean_numLP` |
| Moussaka non-malleability, `U` tokens, `M` redemptions | `noRedirectN_lean_numL` / `noRedirectN_lean_numLP` |
| unbound Moussaka, `U` tokens, `M` redemptions | `nmUN_lean_numL` / `nmUN_lean_numLP` |

So `≤ 2⁻⁵⁴ + 2⁻⁵⁹` for `U = M = 1`, `≈ 2⁻³⁵` for `U + M = 2²⁰` and `≈ 2⁻²⁴` for `U + M = 2³¹`.
The factor `U + M` stays: every hop charges the adversary's whole cipher budget (`221·q_E·2⁻¹²⁸`,
key-level) again. `Theft/JointZK.lean` states the composition step that would charge it once, and
`lean/docs/security/ratatouille.md` §5 explains why the hybrid of `Theft/Many.lean`, which uses the
one-proof zero-knowledge theorem as a black box, cannot.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## The numeric sum -/

section Sums

set_option exponentiation.threshold 1100 in
/-- **One honest proof's terms**: a hop's zero-knowledge error at the hops' budgets of
`U, M ≤ 2³⁰`, its collision term and its programmed-point term are below `2⁻⁵⁵`. -/
lemma perProof_le :
    zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50) +
      (1 / 2 ^ 113 + (zkB 0 312 4607 + zkB 0 312 4607) + (1 / 2 ^ 128 + (2 ^ 32 : ℝ) / 2 ^ 1024)) +
      Hit.epsHitN (2 ^ 31) (2 ^ 64) (2 ^ 64) (2 ^ 64) ≤ 1 / 2 ^ 55 := by
  norm_num [zkB, Hit.epsHitN]

set_option exponentiation.threshold 1100 in
/-- **`U` tokens and `M` proofs, linearly**: the `U + M` hops, the `U + M` collision terms,
`ROM/`'s error, the programmed-point terms and a term `≤ 2⁻¹⁰⁰` are at most
`(U + M)·2⁻⁵⁵ + 2⁻⁵⁹`. -/
lemma many_lin_le' {U M : ℕ} (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) {zI zS r e x : ℝ}
    (hzI : zI ≤ zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50))
    (hzS : zS ≤ zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50)) {D : Fin (U + M) → ℝ}
    (hD : ∀ i, D i ≤ 1 / 2 ^ 113 + (zkB 0 312 4607 + zkB 0 312 4607) +
      (1 / 2 ^ 128 + ((2 * (U + M) : ℕ) : ℝ) / 2 ^ 1024))
    (hr : r ≤ 13 / 2 ^ 63) (he : e ≤ Hit.epsHitN (2 ^ 31) (2 ^ 64) (2 ^ 64) (2 ^ 64))
    (hx : x ≤ 1 / 2 ^ 100) :
    U * zI + M * zS + ∑ i, D i + (r + ((U + M : ℕ) : ℝ) * e) + x ≤
      ((U + M : ℕ) : ℝ) / 2 ^ 55 + 1 / 2 ^ 59 := by
  set Z := zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50)
  set B := 1 / 2 ^ 113 + (zkB 0 312 4607 + zkB 0 312 4607) +
    (1 / 2 ^ 128 + (2 ^ 32 : ℝ) / 2 ^ 1024)
  set E := Hit.epsHitN (2 ^ 31) (2 ^ 64) (2 ^ 64) (2 ^ 64)
  have hN2 : (((2 * (U + M) : ℕ)) : ℝ) ≤ 2 ^ 32 := by
    exact_mod_cast (by omega : 2 * (U + M) ≤ 2 ^ 32)
  have hD' : ∀ i, D i ≤ B := fun i => (hD i).trans (add_le_add le_rfl (add_le_add le_rfl
    (div_le_div_of_nonneg_right hN2 (by positivity))))
  have hN0 : (0 : ℝ) ≤ ((U + M : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsum : ∑ i, D i ≤ ((U + M : ℕ) : ℝ) * B := by
    refine (Finset.sum_le_sum fun i _ => hD' i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hz : (U : ℝ) * zI + M * zS ≤ ((U + M : ℕ) : ℝ) * Z := by
    have h1 : (U : ℝ) * zI ≤ U * Z := mul_le_mul_of_nonneg_left hzI (Nat.cast_nonneg _)
    have h2 : (M : ℝ) * zS ≤ M * Z := mul_le_mul_of_nonneg_left hzS (Nat.cast_nonneg _)
    push_cast
    linarith
  have he' : ((U + M : ℕ) : ℝ) * e ≤ ((U + M : ℕ) : ℝ) * E := mul_le_mul_of_nonneg_left he hN0
  have hper : ((U + M : ℕ) : ℝ) * (Z + B + E) ≤ ((U + M : ℕ) : ℝ) / 2 ^ 55 := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left perProof_le hN0
  have hrx : r + x ≤ 1 / 2 ^ 59 := by
    have : (13 : ℝ) / 2 ^ 63 + 1 / 2 ^ 100 ≤ 1 / 2 ^ 59 := by norm_num
    linarith
  nlinarith

set_option exponentiation.threshold 1100 in
/-- `many_lin_le'` without the extra term. -/
lemma many_lin_le {U M : ℕ} (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30) {zI zS r e : ℝ}
    (hzI : zI ≤ zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50))
    (hzS : zS ≤ zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50)) {D : Fin (U + M) → ℝ}
    (hD : ∀ i, D i ≤ 1 / 2 ^ 113 + (zkB 0 312 4607 + zkB 0 312 4607) +
      (1 / 2 ^ 128 + ((2 * (U + M) : ℕ) : ℝ) / 2 ^ 1024))
    (hr : r ≤ 13 / 2 ^ 63) (he : e ≤ Hit.epsHitN (2 ^ 31) (2 ^ 64) (2 ^ 64) (2 ^ 64)) :
    U * zI + M * zS + ∑ i, D i + (r + ((U + M : ℕ) : ℝ) * e) ≤
      ((U + M : ℕ) : ℝ) / 2 ^ 55 + 1 / 2 ^ 59 := by
  have h := many_lin_le' hU hM hzI hzS hD hr he (x := 0) (by positivity)
  rwa [add_zero] at h

end Sums

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

variable {L U M : ℕ}

set_option maxHeartbeats 4000000 in
/-- **No theft for `U` Clients and `M` spends, function rows, linearly**: with every per-kind
hash budget and the cipher budget at most `2⁶⁴` and `U, M ≤ 2³⁰`,
`Pr[Bad] ≤ (U + M)·2⁻⁵⁵ + 2⁻⁵⁹ + Σ_j Adv^ow(inverter_j)` (`noTheftN_lean_romK`). -/
theorem noTheftN_lean_numL
    (A : ThiefN Sizes.labelRows U M Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64)
    (hqE : qE ≤ 2 ^ 64) (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30)
    (hA : ∀ iss sp, AdmLN (QBud q qE) ansPN (A.out iss sp)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
        (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
        (theftRealN A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
          (extRomN A q qE (totK Arith.Ratatouille.uovM q))) ≤
      ((U + M : ℕ) : ℝ) / 2 ^ 55 + 1 / 2 ^ 59 +
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
  exact (noTheftN_lean_romK A hL hA).trans (add_le_add (many_lin_le hU hM
    ((εz_fn_le _ _ _ _).trans (zkB_mono b3 b5 bE)) ((εz_fn_le _ _ _ _).trans (zkB_mono b3 b5 bE))
    (fun i => (deltaNR_le (R := Blk → Blk) hbX_wf A i).trans
      (deltaBoundN_le (εz_fn_le _ _ _ _) (εz_fn_le _ _ _ _))) hr
    (epsHitN_mono (by omega) (hq _) (hq _) (hq _))) le_rfl)

set_option maxHeartbeats 4000000 in
/-- **No theft for `U` Clients and `M` spends, permutation rows, linearly**: as
`noTheftN_lean_numL`, with AES as random permutations and inverse queries
(`noTheftN_lean_romP'`). -/
theorem noTheftN_lean_numLP
    (A : ThiefN Sizes.labelRows U M Tab3
      (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64)
    (hqE : qE ≤ 2 ^ 64) (hU : U ≤ 2 ^ 30) (hM : M ≤ 2 ^ 30)
    (hA : ∀ iss sp, AdmLN (QBudP q qE) ansPNQ (A.out iss sp)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
        (ShX (Equiv.Perm Blk) pI (XTab L Arith.Ratatouille.uovM)))
        (theftRealN A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
          (extRomNP A q qE)) ≤
      ((U + M : ℕ) : ℝ) / 2 ^ 55 + 1 / 2 ^ 59 +
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
  exact (noTheftN_lean_romP' A hL (by omega) hA).trans (add_le_add (many_lin_le hU hM
    ((εz_perm_le permOk_pIR _ _ _).trans (zkB_mono b3 b5 bE))
    ((εz_perm_le permOk_pSR _ _ _).trans (zkB_mono b3 b5 bE))
    (fun i => (deltaNR_le (R := Equiv.Perm Blk) hbX_wf A i).trans
      (deltaBoundN_le (εz_perm_le permOk_pIR _ _ _) (εz_perm_le permOk_pSR _ _ _))) hr
    (epsHitN_mono (by omega) (hq _) (hq _) (hq _))) le_rfl)

end Ratatouille

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka
open VoleMole.Theft.Ratatouille (qPre)

variable {L U M : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Redemption non-malleability for `U` tokens and `M` redemptions, function rows,
linearly**: with every per-kind hash budget and the cipher budget at most `2⁶⁴` and
`U, M ≤ 2³⁰`, `Pr[Bad] ≤ (U + M)·2⁻⁵⁵ + 2⁻⁵⁹ + Σ_h Adv^ow(inverter_h)`
(`noRedirectN_lean_romK`). -/
theorem noRedirectN_lean_numL
    (A : ThiefN U M Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
    (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutN A kt) (hL : Lrom ≤ L)
    {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64) (hqE : qE ≤ 2 ^ 64) (hU : U ≤ 2 ^ 30)
    (hM : M ≤ 2 ^ 30) (hA : ∀ reqs reds, AdmLN (QBud q qE) ansPN (A.out reqs reds)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
        (nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX)
          (extRomMN q qE (totK Arith.Moussaka.M q))) ≤
      ((U + M : ℕ) : ℝ) / 2 ^ 55 + 1 / 2 ^ 59 +
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
  exact (noRedirectN_lean_romK A hw hk hL hA).trans (add_le_add (many_lin_le hU hM
    ((εz_fn_le _ _ _ _).trans (zkB_mono b3 b5 bE)) ((εz_fn_le _ _ _ _).trans (zkB_mono b3 b5 bE))
    (fun i => (deltaNM_le (R := Blk → Blk) hbX_wf A i).trans
      (deltaBoundN_le (εz_fn_le _ _ _ _) (εz_fn_le _ _ _ _))) hr
    (epsHitN_mono (by omega) (hq _) (hq _) (hq _))) le_rfl)

set_option maxHeartbeats 4000000 in
/-- **Redemption non-malleability for `U` tokens and `M` redemptions, permutation rows,
linearly**: as `noRedirectN_lean_numL`, with AES as random permutations and inverse queries
(`noRedirectN_lean_romP'`). -/
theorem noRedirectN_lean_numLP
    (A : ThiefN U M Tab3 (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
    (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutN A kt) (hL : Lrom ≤ L)
    {q : Kind → ℕ} {qE : ℕ} (hq : ∀ k, q k ≤ 2 ^ 64) (hqE : qE ≤ 2 ^ 64) (hU : U ≤ 2 ^ 30)
    (hM : M ≤ 2 ^ 30) (hA : ∀ reqs reds, AdmLN (QBudP q qE) ansPNQ (A.out reqs reds)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
        (ShX (Equiv.Perm Blk) pI (XTab L Arith.Moussaka.M)))
        (nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX) (extRomMNP q qE)) ≤
      ((U + M : ℕ) : ℝ) / 2 ^ 55 + 1 / 2 ^ 59 +
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
  exact (noRedirectN_lean_romP' A hw hk hL (by omega) hA).trans (add_le_add (many_lin_le hU hM
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

set_option maxHeartbeats 4000000 in
/-- **Unbound non-malleability for `U` tokens and `M` redemptions, function rows, linearly**:
with every per-kind hash budget and the cipher budget at most `2⁶⁴` and `U, M ≤ 2³⁰`,

    Pr[Bad] ≤ (U + M)·2⁻⁵⁵ + 2⁻⁵⁹ + Σ_h (ε_prf + Adv^bind(B₁ h) + Adv^spr-k(B₂ h))

(`nmUN_lean_romK`; its `U·(M + 1)·2⁻¹⁹²` is in `2⁻⁵⁹`). -/
theorem nmUN_lean_numL
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
      ((U + M : ℕ) : ℝ) / 2 ^ 55 + 1 / 2 ^ 59 +
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
  exact add_le_add (many_lin_le' hU hM
    ((εz_fn_le _ _ _ _).trans (zkB_mono b3 b5 bE)) ((εz_fn_le _ _ _ _).trans (zkB_mono b3 b5 bE))
    (fun i => (deltaNU_le (R := Blk → Blk) hbX_wf A i).trans
      (deltaBoundN_le (εz_fn_le _ _ _ _) (εz_fn_le _ _ _ _))) hr
    (epsHitN_mono (by omega) (hq _) (hq _) (hq _)) (extra_le hU hM)) le_rfl

set_option maxHeartbeats 4000000 in
/-- **Unbound non-malleability for `U` tokens and `M` redemptions, permutation rows,
linearly**: as `nmUN_lean_numL`, with AES as random permutations and inverse queries
(`nmUN_lean_romP'`). -/
theorem nmUN_lean_numLP
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
      ((U + M : ℕ) : ℝ) / 2 ^ 55 + 1 / 2 ^ 59 +
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
  exact add_le_add (many_lin_le' hU hM
    ((εz_perm_le permOk_pIU _ _ _).trans (zkB_mono b3 b5 bE))
    ((εz_perm_le permOk_pRU _ _ _).trans (zkB_mono b3 b5 bE))
    (fun i => (deltaNU_le (R := Equiv.Perm Blk) hbX_wf A i).trans
      (deltaBoundN_le (εz_perm_le permOk_pIU _ _ _) (εz_perm_le permOk_pRU _ _ _))) hr
    (epsHitN_mono (by omega) (hq _) (hq _) (hq _)) (extra_le hU hM)) le_rfl

end MoussakaUnbound

end VoleMole.Theft
