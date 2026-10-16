import VoleMole.ROM.SharedH3Reads
import VoleMole.Privacy.SeedXOFGames

/-!
# The privacy games with the seed XOF, the interaction an oracle computation over the tables

`Privacy/SeedXOFGames.lean` for the adversaries of `ROM/PrivacyReads.lean` and
`ROM/SharedH3Reads.lean` (`AdversaryOC`: the interaction a VCVio oracle computation over the
tables, its budget the syntactic query bound `QBudget`). The adversary at XOF table `g` is `A g`;
each theorem is the `*_seed` theorem for the table-reading adversary `fun g => (A g).toRA`, with
`IBudget` from `QBudget` (`AdversaryOC.iBudget`), the bound unchanged.
-/

set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy

open VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ROM.Reads

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka

variable (idx : AnchorSet → UOVKey → ℕ)

/-- **`anonymityOC_lean_num` with the seed XOF.** -/
theorem anonymityOC_lean_num_seed (A : XofM → AdversaryOC (Blk → Blk))
    {q3 q5 qE i3 i2 i5 iE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).toRA.GBudget q3 q5 qE)
    (hI : ∀ g q₀ q₁, QBudget ((A g).trans q₀ q₁) i3 i2 i5 iE)
    (hhide : ∀ g b c, hidingAdv (A g).toRA.ctxRO.base.ci (A g).toRA.ctxRO.base.cr
      (reductionRA (A g).toRA idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide)
    (hg : ∀ b z, RdX (fun g => realGameRA (A g).toRA idx leanPI leanPR b z) qg) :
    |pr _ (seedGameRA idx (fun g => (A g).toRA) false) -
        pr _ (seedGameRA idx (fun g => (A g).toRA) true)| ≤
      4 * εRO (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) +
        4 * εAd 9 q3 (q5 + 1248) (qE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        4 * (i3 / 2 ^ 128 + 1 / 2 ^ 113 + εROP 0 312 4607 (i5 + 624) (iE + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  anonymityRA_lean_num_seed idx (fun g => (A g).toRA) hA (fun g => AdversaryOC.iBudget (hI g))
    hhide hg

/-- **`anonymityOC_lean_num_perm` with the seed XOF.** -/
theorem anonymityOC_lean_num_perm_seed (A : XofM → AdversaryOC (Equiv.Perm Blk))
    {q3 q5 qE i3 i2 i5 iE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).toRA.GBudget q3 q5 qE)
    (hI : ∀ g q₀ q₁, QBudget ((A g).trans q₀ q₁) i3 i2 i5 iE)
    (hhide : ∀ g b c, hidingAdv (A g).toRA.ctxRO.base.ci (A g).toRA.ctxRO.base.cr
      (reductionRA (A g).toRA idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide)
    (hg : ∀ b z, RdX (fun g => realGameRA (A g).toRA idx leanPI leanPR b z) qg) :
    |pr _ (seedGameRA idx (fun g => (A g).toRA) false) -
        pr _ (seedGameRA idx (fun g => (A g).toRA) true)| ≤
      4 * εROPm pI (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) +
        4 * εAdPm pR 9 q3 (q5 + 1248) (qE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        4 * (i3 / 2 ^ 128 + 1 / 2 ^ 113 + εROPmP pR 0 312 4607 (i5 + 624) (iE + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  anonymityRA_lean_num_perm_seed idx (fun g => (A g).toRA) hA
    (fun g => AdversaryOC.iBudget (hI g)) hhide hg

/-- **`anonymityOCSh_num` (one shared `H₃`) with the seed XOF.** -/
theorem anonymityOCSh_num_seed (A : XofM → AdversaryOC (RowH (Blk → Blk)))
    {q5 qE i2 i5 iE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).toRA.GBudget 0 q5 qE)
    (hI : ∀ g q₀ q₁, QBudget ((A g).trans q₀ q₁) 0 i2 i5 iE)
    (hhide : ∀ g b c, hidingAdv (A g).toRA.ctxRO.base.ci (A g).toRA.ctxRO.base.cr
      (reductionRA (A g).toRA idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide)
    (hg : ∀ b z, RdX (fun g => realGameRASh (A g).toRA idx b z) qg) :
    |pr _ (seedGameRASh idx (fun g => (A g).toRA) false) -
        pr _ (seedGameRASh idx (fun g => (A g).toRA) true)| ≤
      4 * εRO (qE + iE + 13824) (q5 + i5 + 1872) (qE + iE + 13824) +
        4 * εAd 9 (qE + 13822) (q5 + 1248) (qE + 13822) 0 i2 (i5 + 624) (iE + 9214) +
        4 * (1 / 2 ^ 113 + εROP 0 312 4607 (i5 + 624) (iE + 9214)) +
        8 * ((iE + 9214 : ℕ) / 2 ^ 128) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  anonymityRASh_num_seed idx (fun g => (A g).toRA) hA (fun g => AdversaryOC.iBudget (hI g))
    hhide hg

/-- **`anonymityOCSh_num_perm` with the seed XOF.** -/
theorem anonymityOCSh_num_perm_seed (A : XofM → AdversaryOC (RowH (Equiv.Perm Blk)))
    {q5 qE i2 i5 iE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).toRA.GBudget 0 q5 qE)
    (hI : ∀ g q₀ q₁, QBudget ((A g).trans q₀ q₁) 0 i2 i5 iE)
    (hhide : ∀ g b c, hidingAdv (A g).toRA.ctxRO.base.ci (A g).toRA.ctxRO.base.cr
      (reductionRA (A g).toRA idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide)
    (hg : ∀ b z, RdX (fun g => realGameRASh (A g).toRA idx b z) qg) :
    |pr _ (seedGameRASh idx (fun g => (A g).toRA) false) -
        pr _ (seedGameRASh idx (fun g => (A g).toRA) true)| ≤
      4 * εROPm pI (qE + iE + 13824) (q5 + i5 + 1872) (qE + iE + 13824) +
        4 * εAdPm pR 9 (qE + 13822) (q5 + 1248) (qE + 13822) 0 i2 (i5 + 624) (iE + 9214) +
        4 * (1 / 2 ^ 113 + εROPmP pR 0 312 4607 (i5 + 624) (iE + 9214)) +
        8 * ((iE + 9214 : ℕ) / 2 ^ 128) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  anonymityRASh_num_perm_seed idx (fun g => (A g).toRA) hA (fun g => AdversaryOC.iBudget (hI g))
    hhide hg

end Moussaka

namespace Ratatouille

open VoleMole.Spec.Ratatouille

/-- **`unlinkabilityOC_lean_num` with the seed XOF.** -/
theorem unlinkabilityOC_lean_num_seed (A : XofR → AdversaryOC (Blk → Blk) Sizes.labelRows)
    {q3 q5 qE i3 i2 i5 iE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).toRA.GBudget q3 q5 qE)
    (h1 : ∀ g tr, QBudget ((A g).msg₁ tr) i3 i2 i5 iE)
    (h2 : ∀ g tr rq, QBudget ((A g).msg₂ tr rq) i3 i2 i5 iE)
    (hhide : ∀ g b₁ b₂ K, hidingAdv (A g).toRA.ctx
      (reductionRA (A g).toRA leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hg : ∀ b₁ b₂ z, RdX (fun g => realGameRA (A g).toRA leanPIR leanPSR b₁ b₂ z) qg)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (seedGameRA (fun g => (A g).toRA) b₁ b₂) -
        pr _ (seedGameRA (fun g => (A g).toRA) b₁' b₂')| ≤
      4 * εRO (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) +
        2 * εAd 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        2 * εAd 9 q3 (q5 + 936) (qE + 13821) (2 * i3) (2 * i2) (2 * i5 + 1560) (2 * iE + 23035) +
        6 * (i3 / 2 ^ 128) + 4 * (1 / 2 ^ 113 + εROP 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  unlinkabilityRA_lean_num_seed (fun g => (A g).toRA) hA
    (fun g => AdversaryOC.iBudget (h1 g) (h2 g)) hhide hg b₁ b₂ b₁' b₂'

/-- **`unlinkabilityOC_lean_num_perm` with the seed XOF.** -/
theorem unlinkabilityOC_lean_num_perm_seed
    (A : XofR → AdversaryOC (Equiv.Perm Blk) Sizes.labelRows) {q3 q5 qE i3 i2 i5 iE qg : ℕ}
    {εhide : ℝ} (hA : ∀ g, (A g).toRA.GBudget q3 q5 qE)
    (h1 : ∀ g tr, QBudget ((A g).msg₁ tr) i3 i2 i5 iE)
    (h2 : ∀ g tr rq, QBudget ((A g).msg₂ tr rq) i3 i2 i5 iE)
    (hhide : ∀ g b₁ b₂ K, hidingAdv (A g).toRA.ctx
      (reductionRA (A g).toRA leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hg : ∀ b₁ b₂ z, RdX (fun g => realGameRA (A g).toRA leanPIR leanPSR b₁ b₂ z) qg)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (seedGameRA (fun g => (A g).toRA) b₁ b₂) -
        pr _ (seedGameRA (fun g => (A g).toRA) b₁' b₂')| ≤
      4 * εROPm pI (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) +
        2 * εAdPm pS 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        2 * εAdPm pS 9 q3 (q5 + 936) (qE + 13821) (2 * i3) (2 * i2) (2 * i5 + 1560)
          (2 * iE + 23035) +
        6 * (i3 / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + εROPmP pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  unlinkabilityRA_lean_num_perm_seed (fun g => (A g).toRA) hA
    (fun g => AdversaryOC.iBudget (h1 g) (h2 g)) hhide hg b₁ b₂ b₁' b₂'

/-- **`unlinkabilityOCSh_num` (one shared `H₃`) with the seed XOF.** -/
theorem unlinkabilityOCSh_num_seed (A : XofR → AdversaryOC (RowH (Blk → Blk)) Sizes.labelRows)
    {q5 qE i2 i5 iE qg : ℕ} {εhide : ℝ} (hA : ∀ g, (A g).toRA.GBudget 0 q5 qE)
    (h1 : ∀ g tr, QBudget ((A g).msg₁ tr) 0 i2 i5 iE)
    (h2 : ∀ g tr rq, QBudget ((A g).msg₂ tr rq) 0 i2 i5 iE)
    (hhide : ∀ g b₁ b₂ K, hidingAdv (A g).toRA.ctx
      (reductionRA (A g).toRA leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hg : ∀ b₁ b₂ z, RdX (fun g => realGameRASh (A g).toRA b₁ b₂ z) qg) (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (seedGameRASh (fun g => (A g).toRA) b₁ b₂) -
        pr _ (seedGameRASh (fun g => (A g).toRA) b₁' b₂')| ≤
      4 * εRO (qE + 2 * iE + 13824) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13824) +
        2 * εAd 9 (qE + iE + 13822) (q5 + i5 + 1248) (qE + iE + 13822) 0 i2 (i5 + 624) (iE + 9214) +
        2 * εAd 9 (qE + 13821) (q5 + 936) (qE + 13821) 0 (2 * i2) (2 * i5 + 1560) (2 * iE + 23035) +
        4 * (1 / 2 ^ 113 + εROP 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        4 * ((iE + 9214 : ℕ) / 2 ^ 128) + 4 * ((2 * iE + 23035 : ℕ) / 2 ^ 128) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  unlinkabilityRASh_num_seed (fun g => (A g).toRA) hA
    (fun g => AdversaryOC.iBudget (h1 g) (h2 g)) hhide hg b₁ b₂ b₁' b₂'

/-- **`unlinkabilityOCSh_num_perm` with the seed XOF.** -/
theorem unlinkabilityOCSh_num_perm_seed
    (A : XofR → AdversaryOC (RowH (Equiv.Perm Blk)) Sizes.labelRows) {q5 qE i2 i5 iE qg : ℕ}
    {εhide : ℝ} (hA : ∀ g, (A g).toRA.GBudget 0 q5 qE)
    (h1 : ∀ g tr, QBudget ((A g).msg₁ tr) 0 i2 i5 iE)
    (h2 : ∀ g tr rq, QBudget ((A g).msg₂ tr rq) 0 i2 i5 iE)
    (hhide : ∀ g b₁ b₂ K, hidingAdv (A g).toRA.ctx
      (reductionRA (A g).toRA leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hg : ∀ b₁ b₂ z, RdX (fun g => realGameRASh (A g).toRA b₁ b₂ z) qg) (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (seedGameRASh (fun g => (A g).toRA) b₁ b₂) -
        pr _ (seedGameRASh (fun g => (A g).toRA) b₁' b₂')| ≤
      4 * εROPm pI (qE + 2 * iE + 13824) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13824) +
        2 * εAdPm pS 9 (qE + iE + 13822) (q5 + i5 + 1248) (qE + iE + 13822) 0 i2 (i5 + 624)
          (iE + 9214) +
        2 * εAdPm pS 9 (qE + 13821) (q5 + 936) (qE + 13821) 0 (2 * i2) (2 * i5 + 1560)
          (2 * iE + 23035) +
        4 * (1 / 2 ^ 113 + εROPmP pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        4 * ((iE + 9214 : ℕ) / 2 ^ 128) + 4 * ((2 * iE + 23035 : ℕ) / 2 ^ 128) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  unlinkabilityRASh_num_perm_seed (fun g => (A g).toRA) hA
    (fun g => AdversaryOC.iBudget (h1 g) (h2 g)) hhide hg b₁ b₂ b₁' b₂'

end Ratatouille

namespace PomFRIT

open VoleMole.Spec VoleMole.Spec.PomFRIT

variable {Ctx : Type} [Fintype Ctx] [DecidableEq Ctx] (enc : Bytes → Ctx)

/-- **`blindnessOC_lean_num` with the seed XOF**: the key-and-messages stage at the tables reads
at most `q_k` cells. -/
theorem blindnessOC_lean_num_seed (A : XofP Ctx → AdversaryOC (Blk → Blk))
    {q3 q5 qE i3 i5 iE qk qg : ℕ} (hA : ∀ g, (A g).toRA.GBudget q3 q5 qE)
    (hk : ∀ g, QBudget (A g).keyOf i3 0 i5 iE)
    (hr : ∀ g t₀ t₁, QBudget ((A g).respOf t₀ t₁) i3 0 i5 iE)
    (hkx : ∀ sl s, RdX (fun g => (A g).toRA.keyOf sl s) qk)
    (hg : ∀ b z, RdX (fun g => realGameRA Hashes.shake (A g).toRA b z) qg) :
    |pr _ (seedGameRA enc (fun g => (A g).toRA) false) -
        pr _ (seedGameRA enc (fun g => (A g).toRA) true)| ≤
      4 * εRO (q3 + 4 * i3) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 + 2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  blindnessRA_lean_num_seed enc (fun g => (A g).toRA) hA
    (fun g => AdversaryOC.iBudget (hk g) (hr g)) hkx hg

/-- **`blindnessOC_lean_num_perm` with the seed XOF.** -/
theorem blindnessOC_lean_num_perm_seed (A : XofP Ctx → AdversaryOC (Equiv.Perm Blk))
    {q3 q5 qE i3 i5 iE qk qg : ℕ} (hA : ∀ g, (A g).toRA.GBudget q3 q5 qE)
    (hk : ∀ g, QBudget (A g).keyOf i3 0 i5 iE)
    (hr : ∀ g t₀ t₁, QBudget ((A g).respOf t₀ t₁) i3 0 i5 iE)
    (hkx : ∀ sl s, RdX (fun g => (A g).toRA.keyOf sl s) qk)
    (hg : ∀ b z, RdX (fun g => realGameRA Hashes.shake (A g).toRA b z) qg) :
    |pr _ (seedGameRA enc (fun g => (A g).toRA) false) -
        pr _ (seedGameRA enc (fun g => (A g).toRA) true)| ≤
      4 * εROPm pP (q3 + 4 * i3) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 + 2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  blindnessRA_lean_num_perm_seed enc (fun g => (A g).toRA) hA
    (fun g => AdversaryOC.iBudget (hk g) (hr g)) hkx hg

/-- **`blindnessOCH_lean_num` (queries to `H₂³`) with the seed XOF.** -/
theorem blindnessOCH_lean_num_seed (A : XofP Ctx → AdversaryOC (Blk → Blk))
    {q3 q5 qE i3 i2 i5 iE qk qg : ℕ} (hA : ∀ g, (A g).toRA.GBudget q3 q5 qE)
    (hk : ∀ g, QBudget (A g).keyOf i3 i2 i5 iE)
    (hr : ∀ g t₀ t₁, QBudget ((A g).respOf t₀ t₁) i3 i2 i5 iE)
    (hkx : ∀ sl s, RdX (fun g => (A g).toRA.keyOf sl s) qk)
    (hg : ∀ b z, RdX (fun g => realGameRA Hashes.shake (A g).toRA b z) qg) :
    |pr _ (seedGameRA enc (fun g => (A g).toRA) false) -
        pr _ (seedGameRA enc (fun g => (A g).toRA) true)| ≤
      4 * εRO (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 +
        (if i2 = 0 then 0 else
          4 * (1 / 2 ^ 113 + εRO (6 * i3) (6 * i5 + 2184) (6 * iE + 18428) +
            (i2 + i2 : ℕ) / 2 ^ 128)) + 2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  blindnessRAH_lean_num_seed enc (fun g => (A g).toRA) hA
    (fun g => AdversaryOC.iBudgetH (hk g) (hr g)) hkx hg

/-- **`blindnessOCH_lean_num_perm` with the seed XOF.** -/
theorem blindnessOCH_lean_num_perm_seed (A : XofP Ctx → AdversaryOC (Equiv.Perm Blk))
    {q3 q5 qE i3 i2 i5 iE qk qg : ℕ} (hA : ∀ g, (A g).toRA.GBudget q3 q5 qE)
    (hk : ∀ g, QBudget (A g).keyOf i3 i2 i5 iE)
    (hr : ∀ g t₀ t₁, QBudget ((A g).respOf t₀ t₁) i3 i2 i5 iE)
    (hkx : ∀ sl s, RdX (fun g => (A g).toRA.keyOf sl s) qk)
    (hg : ∀ b z, RdX (fun g => realGameRA Hashes.shake (A g).toRA b z) qg) :
    |pr _ (seedGameRA enc (fun g => (A g).toRA) false) -
        pr _ (seedGameRA enc (fun g => (A g).toRA) true)| ≤
      4 * εROPm pP (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 +
        (if i2 = 0 then 0 else
          4 * (1 / 2 ^ 113 + εROPm pP (6 * i3) (6 * i5 + 2184) (6 * iE + 18428) +
            (i2 + i2 : ℕ) / 2 ^ 128)) + 2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  blindnessRAH_lean_num_perm_seed enc (fun g => (A g).toRA) hA
    (fun g => AdversaryOC.iBudgetH (hk g) (hr g)) hkx hg

/-- **`blindnessOCSh_num` (one shared `H₃`) with the seed XOF.** -/
theorem blindnessOCSh_num_seed (A : XofP Ctx → AdversaryOC (RowH (Blk → Blk)))
    {q5 qE i5 iE qk qg : ℕ} (hA : ∀ g, (A g).toRA.GBudget 0 q5 qE)
    (hk : ∀ g, QBudget (A g).keyOf 0 0 i5 iE)
    (hr : ∀ g t₀ t₁, QBudget ((A g).respOf t₀ t₁) 0 0 i5 iE)
    (hkx : ∀ sl s, RdX (fun g => (A g).toRA.keyOf sl s) qk)
    (hg : ∀ b z, RdX (fun g => realGameRASh Hashes.shake (A g).toRA b z) qg) :
    |pr _ (seedGameRASh enc (fun g => (A g).toRA) false) -
        pr _ (seedGameRASh enc (fun g => (A g).toRA) true)| ≤
      4 * εRO (qE + 4 * iE + 23035) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 + 2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  blindnessRASh_num_seed enc (fun g => (A g).toRA) hA
    (fun g => AdversaryOC.iBudget (hk g) (hr g)) hkx hg

/-- **`blindnessOCSh_num_perm` with the seed XOF.** -/
theorem blindnessOCSh_num_perm_seed (A : XofP Ctx → AdversaryOC (RowH (Equiv.Perm Blk)))
    {q5 qE i5 iE qk qg : ℕ} (hA : ∀ g, (A g).toRA.GBudget 0 q5 qE)
    (hk : ∀ g, QBudget (A g).keyOf 0 0 i5 iE)
    (hr : ∀ g t₀ t₁, QBudget ((A g).respOf t₀ t₁) 0 0 i5 iE)
    (hkx : ∀ sl s, RdX (fun g => (A g).toRA.keyOf sl s) qk)
    (hg : ∀ b z, RdX (fun g => realGameRASh Hashes.shake (A g).toRA b z) qg) :
    |pr _ (seedGameRASh enc (fun g => (A g).toRA) false) -
        pr _ (seedGameRASh enc (fun g => (A g).toRA) true)| ≤
      4 * εROPm pP (qE + 4 * iE + 23035) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 + 2 * ((2 * (qk + qg) + 1 : ℕ) / 2 ^ 256) :=
  blindnessRASh_num_perm_seed enc (fun g => (A g).toRA) hA
    (fun g => AdversaryOC.iBudget (hk g) (hr g)) hkx hg

end PomFRIT

end VoleMole.Privacy
