import VoleMole.Privacy.MoussakaDelta
import VoleMole.Privacy.RatatouilleDelta
import VoleMole.Privacy.PomFRITDelta
import VoleMole.ZK.TwoPhasePerm

/-!
# Moussaka, Ratatouille and PomFRIT privacy with AES as uniformly random permutations

The games of `Privacy/MoussakaRO.lean`, `Privacy/RatatouilleRO.lean` and `Privacy/PomFRITRO.lean`
(and their collision bounds, `Privacy/MoussakaDelta.lean`, `Privacy/RatatouilleDelta.lean`,
`Privacy/PomFRITDelta.lean`) are stated for every type of cipher rows `R` with zero knowledge
(`ZK.Sim.ZKRow R`; for PomFRIT's two-phase proofs also `ZK.Sim.ZK2Row R`): the shared tables are
`ShG R p = Tab2G p × Tab5F × (Blk → R)`, the prover, the verifier and the simulator's
recomputation run with the CTR PRG of the rows, and the adversary's guess reads the cipher table
at `q_E` keys (whole rows). With **permutation rows** (`R = Equiv.Perm Blk`, `ZK.Sim.ZKRow.perm`)
the adversary reads whole permutations, so forward and inverse AES queries, and the
zero-knowledge error is `εROPm` (`ZK/ReadsROPerm.lean`):

    εROPm p q₃ q₅ q_E = q₃·2⁻¹²⁸ + 2⁻¹¹⁰ + 221·(4607 + q_E + 4607)/(2¹²⁸ − (nHi p + 1))
                          + switchEps p + (q₅ + 1)·2⁻¹²⁸.

* **`anonymityRO_lean_num_perm`** (Moussaka, Theorem 4(a)):

      4·εROPm(pI; q₃, q₅ + 1872, q_E + 13821) + 4·εROPm(pR; q₃, q₅ + 1872, q_E + 13821)
        + 4·(2⁻¹¹⁰ + εROPm(pR; 0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

* **`unlinkabilityRO_lean_num_perm`** (Ratatouille, Theorem 2): the same with `pS` for `pR`.

* **`blindnessRO_lean_num_perm`** (PomFRIT blindness; two-phase zero knowledge with permutation
  rows, `ZK.Sim.ZK2Row.perm` from `ZK/TwoPhasePerm.lean`):

      4·εROPm(pP; q₃, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸.

They are `anonymityRO_lean_numG`, `unlinkabilityRO_lean_numG`, `blindnessRO_lean_numG` at
`Equiv.Perm Blk`: nothing in the games uses that the rows are functions.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy

open VoleMole.ZK.Sim

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka

/-- **Theorem 4(a) (Moussaka issuer hiding and unlinkability) with AES as uniformly random
permutations, every term explicit.** The real game runs the spec with the Lean prover on the
shared tables, the cipher a table of independent uniform permutations of the blocks; the
adversary's guess reads each `H₃` slice at `q₃` keys, `H₅` at `q₅`, the permutation table at `q_E`
keys (whole permutations: forward and inverse queries) and `H₂³` freely. Then the two worlds
differ by at most

    4·εROPm(pI; q₃, q₅ + 1872, q_E + 13821) + 4·εROPm(pR; q₃, q₅ + 1872, q_E + 13821)
      + 4·(2⁻¹¹⁰ + εROPm(pR; 0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide. -/
theorem anonymityRO_lean_num_perm (A : AdversaryRO (Equiv.Perm Blk))
    (idx : AnchorSet → UOVKey → ℕ) {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b c, hidingAdv A.base.ci A.base.cr
      (reductionRO A idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRO A idx leanPI leanPR false) - pr _ (realGameRO A idx leanPI leanPR true)| ≤
      4 * εROPm pI q3 (q5 + 1872) (qE + 13821) + 4 * εROPm pR q3 (q5 + 1872) (qE + 13821) +
        4 * (1 / 2 ^ 110 + εROPm pR 0 312 4607) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityRO_lean_numG A idx hA hhide

end Moussaka

namespace Ratatouille

open VoleMole.Spec.Ratatouille

/-- **Theorem 2 (Ratatouille unlinkability) with AES as uniformly random permutations, every term
explicit.** As `unlinkabilityRO_lean_num`, the cipher a table of independent uniform permutations
read by the Issuer's guess at `q_E` keys (whole permutations); any two worlds differ by at most

    4·εROPm(pI; q₃, q₅ + 1872, q_E + 13821) + 4·εROPm(pS; q₃, q₅ + 1872, q_E + 13821)
      + 4·(2⁻¹¹⁰ + εROPm(pS; 0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide. -/
theorem unlinkabilityRO_lean_num_perm (A : AdversaryRO (Equiv.Perm Blk) Sizes.labelRows)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionR A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameR A leanPIR leanPSR b₁ b₂) - pr _ (realGameR A leanPIR leanPSR b₁' b₂')| ≤
      4 * εROPm pI q3 (q5 + 1872) (qE + 13821) + 4 * εROPm pS q3 (q5 + 1872) (qE + 13821) +
        4 * (1 / 2 ^ 110 + εROPm pS 0 312 4607) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityRO_lean_numG A hA hhide b₁ b₂ b₁' b₂'

end Ratatouille

namespace PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge

/-- **PomFRIT blindness with AES as uniformly random permutations, every term explicit.** The
real game runs the spec with the Lean two-phase prover on the shared tables, the cipher a table of
independent uniform permutations; the Issuer's guess reads each `H₃` slice at `q₃` keys, `H₅` at
`q₅`, the permutation table at `q_E` keys (whole permutations) and `H₂³` freely. Then

    |Pr[W₀] − Pr[W₁]| ≤ 4·εROPm(pP; q₃, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸. -/
theorem blindnessRO_lean_num_perm (A : AdversaryRO (Equiv.Perm Blk)) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr ((XR × XR) × ShP (Equiv.Perm Blk)) (realGameRO Hashes.shake A false) -
        pr ((XR × XR) × ShP (Equiv.Perm Blk)) (realGameRO Hashes.shake A true)| ≤
      4 * εROPm pP q3 (q5 + 1248) (qE + 18428) + 2 * noHitProb + 2 / 2 ^ 128 :=
  blindnessRO_lean_numG A hA

end PomFRIT

end VoleMole.Privacy
