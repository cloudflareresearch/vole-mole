import VoleMole.ROM.PrivacyReads
import VoleMole.Privacy.SharedH3RA
import VoleMole.Privacy.SharedH3PomFRITRA

/-!
# One shared `H₃`, the interaction an oracle computation over the tables

`Privacy/SharedH3RA.lean` for adversaries written as VCVio oracle computations
(`ROM/PrivacyReads.lean`): the interaction queries the shared tables, whose rows carry `H₃`'s
columns (`ZK.Sim.RowH`), and no slot slice (`QBudget … 0 i₂ i₅ i_E`: zero slice queries). Its
consistency is a theorem (`AdversaryOC.iBudget`); the bounds are those of
`anonymityRASh_num`, `unlinkabilityRASh_num`, `blindnessRASh_num` and their `_perm` versions.
-/

set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy

open VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ROM.Reads

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka

/-- **Theorem 4(a) with one shared `H₃` and an interaction that is an oracle computation over the
tables** (function rows; `anonymityRASh_num` for `A.toRA`). -/
theorem anonymityOCSh_num (A : AdversaryOC (RowH (Blk → Blk))) (idx : AnchorSet → UOVKey → ℕ)
    {q5 qE i2 i5 iE : ℕ} {εhide : ℝ}
    (hA : A.toRA.GBudget 0 q5 qE) (hI : ∀ q₀ q₁, QBudget (A.trans q₀ q₁) 0 i2 i5 iE)
    (hhide : ∀ b c, hidingAdv A.toRA.ctxRO.base.ci A.toRA.ctxRO.base.cr
      (reductionRA A.toRA idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRASh A.toRA idx false) - pr _ (realGameRASh A.toRA idx true)| ≤
      4 * εRO (qE + iE + 13824) (q5 + i5 + 1872) (qE + iE + 13824) +
        4 * εAd 9 (qE + 13822) (q5 + 1248) (qE + 13822) 0 i2 (i5 + 624) (iE + 9214) +
        4 * (1 / 2 ^ 110 + εROP 0 312 4607 (i5 + 624) (iE + 9214)) +
        8 * ((iE + 9214 : ℕ) / 2 ^ 128) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityRASh_num A.toRA idx hA (AdversaryOC.iBudget hI) hhide

/-- **`anonymityOCSh_num` with AES as uniformly random permutations.** -/
theorem anonymityOCSh_num_perm (A : AdversaryOC (RowH (Equiv.Perm Blk)))
    (idx : AnchorSet → UOVKey → ℕ) {q5 qE i2 i5 iE : ℕ} {εhide : ℝ}
    (hA : A.toRA.GBudget 0 q5 qE) (hI : ∀ q₀ q₁, QBudget (A.trans q₀ q₁) 0 i2 i5 iE)
    (hhide : ∀ b c, hidingAdv A.toRA.ctxRO.base.ci A.toRA.ctxRO.base.cr
      (reductionRA A.toRA idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRASh A.toRA idx false) - pr _ (realGameRASh A.toRA idx true)| ≤
      4 * εROPm pI (qE + iE + 13824) (q5 + i5 + 1872) (qE + iE + 13824) +
        4 * εAdPm pR 9 (qE + 13822) (q5 + 1248) (qE + 13822) 0 i2 (i5 + 624) (iE + 9214) +
        4 * (1 / 2 ^ 110 + εROPmP pR 0 312 4607 (i5 + 624) (iE + 9214)) +
        8 * ((iE + 9214 : ℕ) / 2 ^ 128) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityRASh_num_perm A.toRA idx hA (AdversaryOC.iBudget hI) hhide

end Moussaka

namespace Ratatouille

open VoleMole.Spec.Ratatouille

/-- **Theorem 2 with one shared `H₃` and an Issuer whose interaction is an oracle computation over
the tables** (function rows; `unlinkabilityRASh_num` for `A.toRA`). -/
theorem unlinkabilityOCSh_num (A : AdversaryOC (RowH (Blk → Blk)) Sizes.labelRows)
    {q5 qE i2 i5 iE : ℕ} {εhide : ℝ} (hA : A.toRA.GBudget 0 q5 qE)
    (h1 : ∀ tr, QBudget (A.msg₁ tr) 0 i2 i5 iE) (h2 : ∀ tr rq, QBudget (A.msg₂ tr rq) 0 i2 i5 iE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.toRA.ctx
      (reductionRA A.toRA leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRASh A.toRA b₁ b₂) - pr _ (realGameRASh A.toRA b₁' b₂')| ≤
      4 * εRO (qE + 2 * iE + 13824) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13824) +
        2 * εAd 9 (qE + iE + 13822) (q5 + i5 + 1248) (qE + iE + 13822) 0 i2 (i5 + 624) (iE + 9214) +
        2 * εAd 9 (qE + 13821) (q5 + 936) (qE + 13821) 0 (2 * i2) (2 * i5 + 1560) (2 * iE + 23035) +
        4 * (1 / 2 ^ 110 + εROP 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        4 * ((iE + 9214 : ℕ) / 2 ^ 128) + 4 * ((2 * iE + 23035 : ℕ) / 2 ^ 128) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityRASh_num A.toRA hA (AdversaryOC.iBudget h1 h2) hhide b₁ b₂ b₁' b₂'

/-- **`unlinkabilityOCSh_num` with AES as uniformly random permutations.** -/
theorem unlinkabilityOCSh_num_perm (A : AdversaryOC (RowH (Equiv.Perm Blk)) Sizes.labelRows)
    {q5 qE i2 i5 iE : ℕ} {εhide : ℝ} (hA : A.toRA.GBudget 0 q5 qE)
    (h1 : ∀ tr, QBudget (A.msg₁ tr) 0 i2 i5 iE) (h2 : ∀ tr rq, QBudget (A.msg₂ tr rq) 0 i2 i5 iE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.toRA.ctx
      (reductionRA A.toRA leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRASh A.toRA b₁ b₂) - pr _ (realGameRASh A.toRA b₁' b₂')| ≤
      4 * εROPm pI (qE + 2 * iE + 13824) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13824) +
        2 * εAdPm pS 9 (qE + iE + 13822) (q5 + i5 + 1248) (qE + iE + 13822) 0 i2 (i5 + 624)
          (iE + 9214) +
        2 * εAdPm pS 9 (qE + 13821) (q5 + 936) (qE + 13821) 0 (2 * i2) (2 * i5 + 1560)
          (2 * iE + 23035) +
        4 * (1 / 2 ^ 110 + εROPmP pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        4 * ((iE + 9214 : ℕ) / 2 ^ 128) + 4 * ((2 * iE + 23035 : ℕ) / 2 ^ 128) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityRASh_num_perm A.toRA hA (AdversaryOC.iBudget h1 h2) hhide b₁ b₂ b₁' b₂'

end Ratatouille

namespace PomFRIT

open VoleMole.Spec VoleMole.Spec.PomFRIT

/-- **PomFRIT blindness with one shared `H₃` and an Issuer whose interaction is an oracle
computation over the tables** (no slice and no `H₂³` query; function rows;
`blindnessRASh_num` for `A.toRA`). -/
theorem blindnessOCSh_num (A : AdversaryOC (RowH (Blk → Blk))) {q5 qE i5 iE : ℕ}
    (hA : A.toRA.GBudget 0 q5 qE) (hk : QBudget A.keyOf 0 0 i5 iE)
    (hr : ∀ t₀ t₁, QBudget (A.respOf t₀ t₁) 0 0 i5 iE) :
    |pr ((XR × XR) × ShP (RowH (Blk → Blk))) (realGameRASh Hashes.shake A.toRA false) -
        pr ((XR × XR) × ShP (RowH (Blk → Blk))) (realGameRASh Hashes.shake A.toRA true)| ≤
      4 * εRO (qE + 4 * iE + 23035) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 :=
  blindnessRASh_num A.toRA hA (AdversaryOC.iBudget hk hr)

/-- **`blindnessOCSh_num` with AES as uniformly random permutations.** -/
theorem blindnessOCSh_num_perm (A : AdversaryOC (RowH (Equiv.Perm Blk))) {q5 qE i5 iE : ℕ}
    (hA : A.toRA.GBudget 0 q5 qE) (hk : QBudget A.keyOf 0 0 i5 iE)
    (hr : ∀ t₀ t₁, QBudget (A.respOf t₀ t₁) 0 0 i5 iE) :
    |pr ((XR × XR) × ShP (RowH (Equiv.Perm Blk))) (realGameRASh Hashes.shake A.toRA false) -
        pr ((XR × XR) × ShP (RowH (Equiv.Perm Blk))) (realGameRASh Hashes.shake A.toRA true)| ≤
      4 * εROPm pP (qE + 4 * iE + 23035) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 :=
  blindnessRASh_num_perm A.toRA hA (AdversaryOC.iBudget hk hr)

end PomFRIT

end VoleMole.Privacy
