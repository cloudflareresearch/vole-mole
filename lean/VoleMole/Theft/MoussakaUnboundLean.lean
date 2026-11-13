import VoleMole.Theft.MoussakaUnbound
import VoleMole.Privacy.MoussakaUnboundLean

/-!
# Unbound Moussaka Proposition U3 and Theorem U4 with the Lean prover (zero knowledge discharged)

`nmU`, `noSquat` and `noRedirectU` (`Theft/MoussakaUnbound.lean`) at the executable Lean prover
in the random-oracle and ideal-cipher model (`Privacy/MoussakaUnboundLean.lean`: provers `leanPI`,
`leanPR`, simulator `Moussaka.leanSim`, programming `leanProgI`, `leanProgR`; tables `Tab3` and
`Moussaka.ShM R`). Both zero-knowledge hypotheses are theorems (`leanPI_zkRO`, `leanPR_zkRO`),
with error `ZKRow.εz R p q₃ q₅ q_E` at the unbound parameters `pI` (232 witness bytes) and `pR`
(559). What remains as hypotheses is as for the bound theorem (`Theft/MoussakaLean.lean`): the
read budgets of the hops' distinguishers (`hAI`, `hAR`), weak simulation-extractability (`hse`, L8
on paper), the PRF bound for the key-recovery distinguishers (`hprf`), and the explicit terms
`δ_R`, `Adv^bind` and `Adv^spr-k`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.MoussakaUnbound

open VoleMole.Privacy VoleMole.Privacy.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
  VoleMole.ZK.Sim
open VoleMole.Privacy.Moussaka (ShM leanSim)

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R] [ZKRow R]

/-- **Unbound non-malleability and no squatting with the Lean prover** (`nmU`):

    Pr[Bad] ≤ εz(pI; q₃, q₅, q_E) + εz(pR; q₃, q₅, q_E) + δ_R + ε_SE + (ε_prf + 2⁻¹⁹²)
                + Adv^bind(B₁) + Adv^spr-k(B₂). -/
theorem nmU_lean (A : Thief Tab3 (ShM R)) (verI : IssueInstance → Bytes → ShM R → Bool)
    (verR : RedeemInstance → Bytes → ShM R → Bool) (ext : Ext Tab3 (ShM R)) {q3 q5 qE : ℕ}
    {AdmE : (Tab3 → Tab3 → ShM R → UOp) → Prop} {εSE εprf : ℝ}
    (hAI : ∀ ω r₂ g₂, Budget pI q3 q5 qE (distI A leanPR verI verR ext ω r₂ g₂))
    (hAR : ∀ ω c₁ g₁, Budget pR q3 q5 qE (distR A verI verR ext (leanSim pI) leanProgI ω c₁ g₁))
    (hse : WeakSE2 (simI' (leanSim pI)) leanProgI (simR' (leanSim pR)) leanProgR
      (AccOp verI verR) FreshOp RelOp ext AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂))
    (hprf : ∀ b, prf1Adv A.ci
      (owkD (keyB A ext (leanSim pI) leanProgI (leanSim pR) leanProgR) b) ≤ εprf) :
    pr _ (nmReal A leanPI leanPR verI verR ext) ≤
      ZKRow.εz R pI q3 q5 qE + ZKRow.εz R pR q3 q5 qE +
        pr _ (deltaR A leanPR (leanSim pI) leanProgI) + εSE + (εprf + 1 / 2 ^ 192) +
        bindAdv (bindB A ext (leanSim pI) leanProgI (leanSim pR) leanProgR) +
        sprAdv A.ci (sprB A ext (leanSim pI) leanProgI (leanSim pR) leanProgR) :=
  nmU (CI := SimCoins pI) (CR := SimCoins pR) A leanPI leanPR verI verR ext
    (leanSim pI) leanProgI (leanSim pR) leanProgR (leanPI_zkRO (R := R) q3 q5 qE)
    (ZKRow.εz_nonneg _ _ _ _) (leanPR_zkRO (R := R) q3 q5 qE) (ZKRow.εz_nonneg _ _ _ _) hAI hAR
    hse hAE hprf

/-- **Proposition U3 (no nullifier squatting) with the Lean prover.** -/
theorem noSquat_lean (A : Thief Tab3 (ShM R)) (verI : IssueInstance → Bytes → ShM R → Bool)
    (verR : RedeemInstance → Bytes → ShM R → Bool) (ext : Ext Tab3 (ShM R)) {q3 q5 qE : ℕ}
    {AdmE : (Tab3 → Tab3 → ShM R → UOp) → Prop} {εSE εprf : ℝ}
    (hAI : ∀ ω r₂ g₂, Budget pI q3 q5 qE (distI A leanPR verI verR ext ω r₂ g₂))
    (hAR : ∀ ω c₁ g₁, Budget pR q3 q5 qE (distR A verI verR ext (leanSim pI) leanProgI ω c₁ g₁))
    (hse : WeakSE2 (simI' (leanSim pI)) leanProgI (simR' (leanSim pR)) leanProgR
      (AccOp verI verR) FreshOp RelOp ext AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂))
    (hprf : ∀ b, prf1Adv A.ci
      (owkD (keyB A ext (leanSim pI) leanProgI (leanSim pR) leanProgR) b) ≤ εprf) :
    pr _ (nmRealE A leanPI leanPR (Squat A verI verR)) ≤
      ZKRow.εz R pI q3 q5 qE + ZKRow.εz R pR q3 q5 qE +
        pr _ (deltaR A leanPR (leanSim pI) leanProgI) + εSE + (εprf + 1 / 2 ^ 192) +
        bindAdv (bindB A ext (leanSim pI) leanProgI (leanSim pR) leanProgR) +
        sprAdv A.ci (sprB A ext (leanSim pI) leanProgI (leanSim pR) leanProgR) :=
  noSquat (CI := SimCoins pI) (CR := SimCoins pR) A leanPI leanPR verI verR ext
    (leanSim pI) leanProgI (leanSim pR) leanProgR (leanPI_zkRO (R := R) q3 q5 qE)
    (ZKRow.εz_nonneg _ _ _ _) (leanPR_zkRO (R := R) q3 q5 qE) (ZKRow.εz_nonneg _ _ _ _) hAI hAR
    hse hAE hprf

/-- **Theorem U4 (no redirect to another digest, Anchor Set or redemption context) with the Lean
prover.** -/
theorem noRedirectU_lean (A : Thief Tab3 (ShM R)) (verI : IssueInstance → Bytes → ShM R → Bool)
    (verR : RedeemInstance → Bytes → ShM R → Bool) (ext : Ext Tab3 (ShM R)) {q3 q5 qE : ℕ}
    {AdmE : (Tab3 → Tab3 → ShM R → UOp) → Prop} {εSE εprf : ℝ}
    (hAI : ∀ ω r₂ g₂, Budget pI q3 q5 qE (distI A leanPR verI verR ext ω r₂ g₂))
    (hAR : ∀ ω c₁ g₁, Budget pR q3 q5 qE (distR A verI verR ext (leanSim pI) leanProgI ω c₁ g₁))
    (hse : WeakSE2 (simI' (leanSim pI)) leanProgI (simR' (leanSim pR)) leanProgR
      (AccOp verI verR) FreshOp RelOp ext AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂))
    (hprf : ∀ b, prf1Adv A.ci
      (owkD (keyB A ext (leanSim pI) leanProgI (leanSim pR) leanProgR) b) ≤ εprf) :
    pr _ (nmRealE A leanPI leanPR (Redirect A verI verR ext)) ≤
      ZKRow.εz R pI q3 q5 qE + ZKRow.εz R pR q3 q5 qE +
        pr _ (deltaR A leanPR (leanSim pI) leanProgI) + εSE + (εprf + 1 / 2 ^ 192) +
        bindAdv (bindB A ext (leanSim pI) leanProgI (leanSim pR) leanProgR) +
        sprAdv A.ci (sprB A ext (leanSim pI) leanProgI (leanSim pR) leanProgR) :=
  noRedirectU (CI := SimCoins pI) (CR := SimCoins pR) A leanPI leanPR verI verR ext
    (leanSim pI) leanProgI (leanSim pR) leanProgR (leanPI_zkRO (R := R) q3 q5 qE)
    (ZKRow.εz_nonneg _ _ _ _) (leanPR_zkRO (R := R) q3 q5 qE) (ZKRow.εz_nonneg _ _ _ _) hAI hAR
    hse hAE hprf

end VoleMole.Theft.MoussakaUnbound
