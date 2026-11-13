import VoleMole.Privacy.MoussakaRA
import VoleMole.Privacy.RatatouilleRA
import VoleMole.Privacy.PomFRITRAGame
import VoleMole.Privacy.PomFRITRAH
import VoleMole.ZK.HopsPatchPerm
import VoleMole.ZK.TwoPhasePerm

/-!
# Privacy with a table-reading adversary and AES as uniformly random permutations

The games of `Privacy/MoussakaRA.lean`, `Privacy/RatatouilleRA.lean` and
`Privacy/PomFRITRAGame.lean` (the adversary's interaction reads the tables, with consistent
budgets `SReads`) are stated for every type of cipher rows with zero knowledge for fixed
statements (`ZK.Sim.ZKRow`), for statements read off the tables (`ZK.Sim.ZKPRow`: the cipher
table patched on the reader's keys) and, for PomFRIT, two-phase zero knowledge with a continuation
that reads the tables after step 1 (`ZK.Sim.ZK2ARow`). With **permutation rows** the instances are
`ZKRow.perm` (`ZK/ReadsROPerm.lean`), `ZKPRow.perm` (`ZK/HopsPatchPerm.lean`) and `ZK2ARow.perm`
(`ZK/TwoPhasePerm.lean`), and the errors are `εROPm`, `εROPmP` and `εAdPm`.

* **`anonymityRA_lean_num_perm`** (Moussaka):

      4·εROPm(pI; i₃ + q₃, q₅ + i₅ + 1872, q_E + i_E + 13821)
        + 4·εAdPm(pR; 9; q₃, q₅ + 1248, q_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214)
        + 4·(i₃·2⁻¹²⁸ + 2⁻¹¹³ + εROPmP(pR; 0, 312, 4607; i₅ + 624, i_E + 9214))
        + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

* **`unlinkabilityRA_lean_num_perm`** (Ratatouille):

      4·εROPm(pI; 2i₃ + q₃, q₅ + 2i₅ + 1872, q_E + 2i_E + 13821)
        + 2·εAdPm(pS; 9; i₃ + q₃, q₅ + i₅ + 1248, q_E + i_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214)
        + 2·εAdPm(pS; 9; q₃, q₅ + 936, q_E + 13821; 2i₃, 2i₂, 2i₅ + 1560, 2i_E + 23035)
        + 6·i₃·2⁻¹²⁸ + 4·(2⁻¹¹³ + εROPmP(pS; 0, 312, 4607; 2i₅ + 1560, 2i_E + 23035))
        + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

* **`blindnessRA_lean_num_perm`** (PomFRIT, no `H₂³` reads by the interaction):

      4·εROPm(pP; q₃ + 4i₃, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸.

* **`blindnessRAH_lean_num_perm`** (PomFRIT, the interaction reading `H₂³` too, joint budget
  `IBudgetH`, `Privacy/PomFRITRAH.lean`):

      4·εROPm(pP; q₃ + 6i₃, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035) + 2·noHitProb + 2·2⁻¹²⁸
        + [i₂ > 0]·4·(2⁻¹¹³ + εROPm(pP; 6i₃, 6i₅ + 2184, 6i_E + 18428) + 2i₂·2⁻¹²⁸).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy

open VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka

/-- **Theorem 4(a) (Moussaka) with a table-reading interaction and AES as uniformly random
permutations, every term explicit** (`anonymityRA_lean_numG` at permutation rows): the guess
reads each `H₃` slice at `q₃` keys, `H₅` at `q₅`, the permutation table at `q_E` keys (whole
permutations) and `H₂³` freely; the interaction reads, as a function of each slice and the shared
tables, at most `i₃` slice keys, `i₂` `H₂³` keys, `i₅` `H₅` keys and `i_E` permutation-table keys,
consistently. -/
theorem anonymityRA_lean_num_perm (A : AdversaryRA (Equiv.Perm Blk))
    (idx : AnchorSet → UOVKey → ℕ) {q3 q5 qE i3 i2 i5 iE : ℕ} {εhide : ℝ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hhide : ∀ b c, hidingAdv A.ctxRO.base.ci A.ctxRO.base.cr
      (reductionRA A idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRA A idx leanPI leanPR false) - pr _ (realGameRA A idx leanPI leanPR true)| ≤
      4 * εROPm pI (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) +
        4 * εAdPm pR 9 q3 (q5 + 1248) (qE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        4 * (i3 / 2 ^ 128 + 1 / 2 ^ 113 + εROPmP pR 0 312 4607 (i5 + 624) (iE + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityRA_lean_numG A idx hA hI hhide

end Moussaka

namespace Ratatouille

open VoleMole.Spec.Ratatouille

/-- **Theorem 2 (Ratatouille) with a table-reading Issuer and AES as uniformly random
permutations, every term explicit** (`unlinkabilityRA_lean_numG` at permutation rows). -/
theorem unlinkabilityRA_lean_num_perm (A : AdversaryRA (Equiv.Perm Blk) Sizes.labelRows)
    {q3 q5 qE i3 i2 i5 iE : ℕ} {εhide : ℝ} (hA : A.GBudget q3 q5 qE)
    (hI : A.IBudget i3 i2 i5 iE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionRA A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRA A leanPIR leanPSR b₁ b₂) - pr _ (realGameRA A leanPIR leanPSR b₁' b₂')| ≤
      4 * εROPm pI (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) +
        2 * εAdPm pS 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        2 * εAdPm pS 9 q3 (q5 + 936) (qE + 13821) (2 * i3) (2 * i2) (2 * i5 + 1560)
          (2 * iE + 23035) +
        6 * (i3 / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + εROPmP pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityRA_lean_numG A hA hI hhide b₁ b₂ b₁' b₂'

end Ratatouille

namespace PomFRIT

/-- **PomFRIT blindness with a table-reading Issuer and AES as uniformly random permutations,
every term explicit** (`blindnessRA_lean_numG` at permutation rows; SHAKE as the base record):

    |Pr[W₀] − Pr[W₁]| ≤ 4·εROPm(pP; q₃ + 4i₃, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸. -/
theorem blindnessRA_lean_num_perm (A : AdversaryRA (Equiv.Perm Blk)) {q3 q5 qE i3 i5 iE : ℕ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i5 iE) :
    |pr ((XR × XR) × ShP (Equiv.Perm Blk)) (realGameRA Hashes.shake A false) -
        pr ((XR × XR) × ShP (Equiv.Perm Blk)) (realGameRA Hashes.shake A true)| ≤
      4 * εROPm pP (q3 + 4 * i3) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 :=
  blindnessRA_lean_numG A hA hI

/-- **PomFRIT blindness with an Issuer whose interaction reads every table, `H₂³` included, and
AES as uniformly random permutations, every term explicit** (`blindnessRAH_lean_numG` at
permutation rows; SHAKE as the base record). -/
theorem blindnessRAH_lean_num_perm (A : AdversaryRA (Equiv.Perm Blk)) {q3 q5 qE i3 i2 i5 iE : ℕ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudgetH i3 i2 i5 iE) :
    |pr ((XR × XR) × ShP (Equiv.Perm Blk)) (realGameRA Hashes.shake A false) -
        pr ((XR × XR) × ShP (Equiv.Perm Blk)) (realGameRA Hashes.shake A true)| ≤
      4 * εROPm pP (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 +
        (if i2 = 0 then 0 else
          4 * (1 / 2 ^ 113 + εROPm pP (6 * i3) (6 * i5 + 2184) (6 * iE + 18428) +
            (i2 + i2 : ℕ) / 2 ^ 128)) :=
  blindnessRAH_lean_numG A hA hI

end PomFRIT

end VoleMole.Privacy
