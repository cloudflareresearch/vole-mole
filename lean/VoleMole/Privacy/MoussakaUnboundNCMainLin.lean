import VoleMole.ZK.MainSharedLin
import VoleMole.Privacy.MoussakaUnboundNCMainLeanN

/-!
# Unbound Moussaka U5(b) on `main` with `n` adaptive queries, the joint hop linear in `n`

`anonymityNC_main_U_sharedAllN` and `anonymityNC_main_U_leanN`
(`Privacy/MoussakaUnboundNCMain{N,LeanN}.lean`) use the joint hop `main_sharedAll_leN`, whose
factor is `2ⁿ − 1`. The same games with the linear joint hop `main_sharedAll_leLin`
(`ZK/MainSharedLin.lean`): every other step (the simulated side, the statistical (PU) bound
`bstarNN_le`, the abort, PRF and swap hops, the Lean issuance hop) is reused unchanged.

    anonymityNC_main_U_sharedAllLin:
      |Pr[W₀] − Pr[W₁]| ≤ 4n·(εS(2q₃ + n, 2q_E + 2n·4607) + Δ23N(9, n))
          + 2·(n·noHitProb + 2n·(q₅ + 312n + 1)·2⁻¹²⁸ + n²·313·2⁻¹²⁸)
          + 2·(ψ false + ψ true) + 2·εprf
    anonymityNC_main_U_leanLin: the same with `φ` for `ψ`, plus `4·2⁻¹¹³`.

The guess's reads are counted twice (`2q₃`, `2q_E`): once for the event, once for the bad event,
whose read set is the guess's `H₅` read set.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.MoussakaUnbound

open VoleMole.Spec VoleMole.Spec.MoussakaUnbound VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval
attribute [local irreducible] simulate realRO progRO

section Lin

variable (A : AdversaryUNCH) (PI : NIZK IssueInstance) (sk : Bool → Signer) (n : ℕ)

/-- **The joint hop in each world, linear in `n`.** -/
theorem real_sim_NLin (hsk : ∀ c, (sk c).Correct (A.pk c)) {q3 qE : ℕ} (hC : A.ConsH q3 qE)
    (b : Bool) :
    |realNN A PI sk n b - simNN A PI sk n b| ≤
      2 * n * (εS (2 * q3 + n) (2 * qE + 2 * n * 4607) + Δ23N 9 n) + bstarNN A PI sk n b :=
  main_sharedAll_leLin hashesWF_shake (nvalidNN A PI sk n hsk b) (evNN A PI sk n b)
    (r5NN A PI sk n b)
    (rdN_ofNN A PI sk n (f := fun y u G2 T => A.guess y u G2 T)
      (R := fun y u G2 T => A.R5 y u G2 T) hC.g b)
    (rdN_ofNN A PI sk n (f := fun y u G2 T => A.R5 y u G2 T)
      (R := fun y u G2 T => A.R5 y u G2 T) hC.r b)

/-- **Unbound Moussaka U5(b) on `main` with `n` adaptive redemption queries, all tables shared,
the joint hop linear in `n`**: the hypotheses of `anonymityNC_main_U_sharedAllN`, and

    |Pr[W₀] − Pr[W₁]| ≤ 4n·(εS(2q₃ + n, 2q_E + 2n·4607) + Δ23N(9, n))
        + 2·(n·noHitProb + 2n·(q₅ + 312n + 1)·2⁻¹²⁸ + n²·313·2⁻¹²⁸)
        + 2·(ψ false + ψ true) + 2·εprf. -/
theorem anonymityNC_main_U_sharedAllLin (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hK : Contains A.unc.nc) {q3 qE q5 : ℕ} (hC : A.ConsH q3 qE)
    (h5 : ∀ y u G2 T, (A.R5 y u G2 T).card ≤ q5) {εprf : ℝ}
    (hprf : ∀ b z, prfAdvNC (redNN A n b z) ≤ εprf) :
    |realNN A PI sk n false - realNN A PI sk n true| ≤
      4 * n * (εS (2 * q3 + n) (2 * qE + 2 * n * 4607) + Δ23N 9 n) +
        2 * (n * noHitProb + n * (2 * (((q5 + n * 312 : ℕ) + 1) / 2 ^ 128)) +
          n * n * (((312 : ℕ) + 1) / 2 ^ 128)) +
        2 * (psi A.unc.nc PI sk false + psi A.unc.nc PI sk true) + 2 * εprf := by
  have r0 := real_sim_NLin A PI sk n hsk hC false
  have r1 := real_sim_NLin A PI sk n hsk hC true
  have b0 := bstarNN_le (PI := PI) (n := n) hsk hK h5 false
  have b1 := bstarNN_le (PI := PI) (n := n) hsk hK h5 true
  have s0 := sim_hyb_NN A PI sk n hsk hK false
  have s1 := sim_hyb_NN A PI sk n hsk hK true
  have p0 := prf_hop_NN A n false (hprf false)
  have p1 := prf_hop_NN A n true (hprf true)
  have ie := idealNN_eq A n
  rw [abs_sub_le_iff] at r0 r1 s0 s1 p0 p1 ⊢
  constructor <;> linarith

/-- **U5(b) on `main` with the Lean issuance prover, `n` adaptive queries, the joint hop linear
in `n`**: the hypotheses of `anonymityNC_main_U_leanN`, and

    |Pr[W₀] − Pr[W₁]| ≤ 4n·(εS(2q₃ + n, 2q_E + 2n·4607) + Δ23N(9, n))
        + 2·(n·noHitProb + 2n·(q₅ + 312n + 1)·2⁻¹²⁸ + n²·313·2⁻¹²⁸)
        + 2·(φ false + φ true) + 2·εprf + 4·2⁻¹¹³. -/
theorem anonymityNC_main_U_leanLin [HasPrg] (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hK : Contains A.unc.nc) {q3 qE q5 : ℕ} (hC : A.ConsH q3 qE)
    (h5 : ∀ y u G2 T, (A.R5 y u G2 T).card ≤ q5) {εprf : ℝ}
    (hprf : ∀ b z, prfAdvNC (redNN A n b z) ≤ εprf) :
    |realNNL A sk n false - realNNL A sk n true| ≤
      4 * n * (εS (2 * q3 + n) (2 * qE + 2 * n * 4607) + Δ23N 9 n) +
        2 * (n * noHitProb + n * (2 * (((q5 + n * 312 : ℕ) + 1) / 2 ^ 128)) +
          n * n * (((312 : ℕ) + 1) / 2 ^ 128)) +
        2 * (phiU A.unc.nc sk false + phiU A.unc.nc sk true) + 2 * εprf + 4 / 2 ^ 113 := by
  have h := anonymityNC_main_U_sharedAllLin A PIaccU sk n hsk hK hC h5 hprf
  have k0 := kappa_eq_zero A.unc.nc PIaccU PIaccU_correct
  have p0 := psi_le A.unc.nc PIaccU sk false
  have p1 := psi_le A.unc.nc PIaccU sk true
  have c0 := realNNL_close A sk n false
  have c1 := realNNL_close A sk n true
  rw [k0] at p0 p1
  rw [abs_sub_le_iff] at h c0 c1 ⊢
  constructor <;> linarith

end Lin

end VoleMole.Privacy.MoussakaUnbound
