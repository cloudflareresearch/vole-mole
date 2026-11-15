import VoleMole.Theft.PlainTotal
import VoleMole.Theft.PlainRataReads
import VoleMole.Theft.PlainMousReads
import VoleMole.Theft.PlainRataManyRom
import VoleMole.Theft.PlainMousManyRom
import VoleMole.Theft.PlainUnboundManyRom

/-!
# The theft and non-malleability theorems without a total hash budget

The `*_lean_rom'` theorems ask the adversary for a total hash budget `n_G` (`QBudT q q_E n_G`).
By `admL_qBudT` and `admLN_qBudT` (`Theft/PlainTotal.lean`) a last stage within the per-kind
budget `QBud q q_E` is within `QBudT q q_E (totK M q)`, `totK M q = Σ_{k ∈ kindsT M} q k` the
sum over the ten kinds the tables answer (`H_comb` at the game's `M` only: a query off the table
points is answered by SHAKE, which the adversary computes itself). So each theorem holds for
adversaries with per-kind bounds only, with `n_G := totK M q`:

* **`noTheft_lean_romK`** (Ratatouille, one Client), **`noTheftN_lean_romK`** (`U` Clients,
  `M` spends), **`noRedirect_lean_romK`** (Moussaka, one token), **`noRedirectN_lean_romK`**
  (`U` tokens, `M` redemptions), **`nmUN_lean_romK`** (unbound Moussaka).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

variable {L : ℕ}

/-- **No theft with `ROM/`'s plain extraction, per-kind budgets only** (Ratatouille, one Client):
`noTheft_lean_rom'` with `n_G = totK uovM q`. -/
theorem noTheft_lean_romK
    (A : Thief Sizes.labelRows Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE : ℕ}
    (hA : ∀ o₁ o₂, AdmL (QBud q qE) ansP (A.out o₁ o₂)) :
    pr _ (theftReal A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
        (extRom A q qE (totK Arith.Ratatouille.uovM q))) ≤
      ZKRow.εz (Blk → Blk) pI (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 211958) +
        ZKRow.εz (Blk → Blk) pS (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 211958) +
        pr _ (deltaS A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX)) +
        ((epsRom (q + qPre + qPre) (qE + verifyCellBound pS + verifyCellBound pI)
          (totK Arith.Ratatouille.uovM q + 338 + 338)).toReal +
          Hit.epsHit (q .mu) (q .h21) (q .h22)) +
        owAdv A.ctx (inverter A (extRom A q qE (totK Arith.Ratatouille.uovM q)) leanSimIR
          (leanProgIRX hbX) leanSimSR (leanProgSRX hbX)) :=
  noTheft_lean_rom' A hL fun o₁ o₂ => admL_qBudT (hA o₁ o₂)

variable {U M : ℕ}

set_option maxHeartbeats 4000000 in
/-- **No theft for `U` Clients and `M` spends, per-kind budgets only**: `noTheftN_lean_rom'`
with `n_G = totK uovM q`. -/
theorem noTheftN_lean_romK
    (A : ThiefN Sizes.labelRows U M Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
    (hL : Hit.Rata.Lmin ≤ L) {q : Kind → ℕ} {qE : ℕ}
    (hA : ∀ iss sp, AdmLN (QBud q qE) ansPN (A.out iss sp)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
        (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
        (theftRealN A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX)
          (extRomN A q qE (totK Arith.Ratatouille.uovM q))) ≤
      U * ZKRow.εz (Blk → Blk) pI (2 * q .h3) (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 147451 + 4608) +
        M * ZKRow.εz (Blk → Blk) pS (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624) (2 * qE + (U + M) * 147451 + 4608) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3
            (ShX (Blk → Blk) pI (XTab L Arith.Ratatouille.uovM)))
          (deltaNR A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX) leanSimSR
            (leanProgSRX hbX) i) +
        ((epsRom (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pS)
            (totK Arith.Ratatouille.uovM q + (U + M) * 338)).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ j : Fin (U + M), owAdvK (inverterN A leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX) (extRomN A q qE (totK Arith.Ratatouille.uovM q)) j) :=
  noTheftN_lean_rom' A hL fun iss sp => admLN_qBudT (hA iss sp)

end Ratatouille

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka
open VoleMole.Theft.Ratatouille (qPre)

variable {L : ℕ}

/-- **Redemption non-malleability with `ROM/`'s plain extraction, per-kind budgets only**
(Moussaka, one token): `noRedirect_lean_rom'` with `n_G = totK Moussaka.M q`. -/
theorem noRedirect_lean_romK (A : Thief Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
    (hw : Hit.Mous.HitWf A) {kt : Bytes → UOVKey} (hk : KeysOut A kt) (hL : Lrom ≤ L)
    {q : Kind → ℕ} {qE : ℕ} (hA : ∀ o₁ o₂, AdmL (QBud q qE) ansP (A.out o₁ o₂)) :
    pr _ (nmReal A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX)
        (extRomM q qE (totK Arith.Moussaka.M q))) ≤
      ZKRow.εz (Blk → Blk) pI (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 138230) +
        ZKRow.εz (Blk → Blk) pR (2 * q .h3) (2 * q .h5 + 1560) (2 * qE + 138230) +
        pr _ (deltaR A (leanPRX hbX) (leanSim pI) (leanProgIX hbX)) +
        ((epsRomM (q + Ratatouille.qPre + Ratatouille.qPre)
          (qE + verifyCellBound pR + verifyCellBound pI)
          (totK Arith.Moussaka.M q + 338 + 338)).toReal +
          Hit.epsHit (q .mu) (q .h21) (q .h22)) +
        owAdv A.ci A.cr (inverter A (extRomM q qE (totK Arith.Moussaka.M q)) (leanSim pI)
          (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)) :=
  noRedirect_lean_rom' A hw hk hL fun o₁ o₂ => admL_qBudT (hA o₁ o₂)

variable {U M : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Redemption non-malleability for `U` tokens and `M` redemptions, per-kind budgets only**:
`noRedirectN_lean_rom'` with `n_G = totK Moussaka.M q`. -/
theorem noRedirectN_lean_romK (A : ThiefN U M Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
    (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutN A kt)
    (hL : Lrom ≤ L) {q : Kind → ℕ} {qE : ℕ}
    (hA : ∀ reqs reds, AdmLN (QBud q qE) ansPN (A.out reqs reds)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
        (nmRealN A (leanPIX hbX) (leanPRX hbX) (verILX hbX) (verRLX hbX)
          (extRomMN q qE (totK Arith.Moussaka.M q))) ≤
      U * ZKRow.εz (Blk → Blk) pI (2 * q .h3) (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 73723 + 4608) +
        M * ZKRow.εz (Blk → Blk) pR (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624) (2 * qE + (U + M) * 73723 + 4608) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
            (ShX (Blk → Blk) pI (XTab L Arith.Moussaka.M)))
          (deltaNM A (leanPIX hbX) (leanPRX hbX) (leanSim pI) (leanProgIX hbX) (leanSim pR)
            (leanProgRX hbX) i) +
        ((epsRomM (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
            (totK Arith.Moussaka.M q + (U + M) * 338)).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) (leanProgIX hbX) (leanSim pR) (leanProgRX hbX)
            (extRomMN q qE (totK Arith.Moussaka.M q)) h) :=
  noRedirectN_lean_rom' A hw hk hL fun reqs reds => admLN_qBudT (hA reqs reds)

end Moussaka

namespace MoussakaUnbound

open VoleMole.Privacy.MoussakaUnbound
open VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (AnchorSet ctxBytes proveSeedBytes nfBytes)
open VoleMole.Privacy.Moussaka (ShM leanSim)
open VoleMole.Theft.Ratatouille (qPre)

variable {U M L : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Unbound non-malleability for `U` tokens and `M` redemptions, per-kind budgets only**:
`nmUN_lean_rom'` with `n_G = totK Moussaka.M q`. -/
theorem nmUN_lean_romK
    (A : ThiefN U M Tab3 (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
    (hw : HitWfN A) {kt : Bytes → UOVKey} (hk : KeysOutNU A kt)
    (hL : LminU ≤ L) {q : Kind → ℕ} {qE : ℕ}
    (hA : ∀ reqs reds, AdmLN (QBud q qE) ansPN (A.out reqs reds)) {εprf : ℝ}
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
      (leanProgRUX hbX) (extRomUN q qE (totK Arith.Moussaka.M q)) h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
        (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
        (nmRealNE A (leanPIUX hbX) (leanPRUX hbX)
          (BadN A (verILUX hbX) (verRLUX hbX) (extRomUN q qE (totK Arith.Moussaka.M q)))) ≤
      U * ZKRow.εz (Blk → Blk) pI (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 105979 + 4608) +
        M * ZKRow.εz (Blk → Blk) pR (2 * q .h3)
          (2 * q .h5 + (U + M) * 312 + 312 + (U + M - 1) * 624)
          (2 * qE + (U + M) * 105979 + 4608) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3
            (ShX (Blk → Blk) Privacy.Moussaka.pI (XTab L Arith.Moussaka.M)))
          (deltaNU A (leanPIUX hbX) (leanPRUX hbX) (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) i) +
        ((epsRomU (q + (U + M) • qPre) (qE + (U + M) * verifyCellBound pR)
            (totK Arith.Moussaka.M q + (U + M) * 338)).toReal +
          (U + M : ℕ) * Hit.epsHitN (U + M) (q .mu) (q .h21) (q .h22)) +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR) (leanProgRUX hbX)
            (extRomUN q qE (totK Arith.Moussaka.M q)) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX hbX) (leanSim pR)
            (leanProgRUX hbX) (extRomUN q qE (totK Arith.Moussaka.M q)) h)) :=
  nmUN_lean_rom' A hw hk hL (fun reqs reds => admLN_qBudT (hA reqs reds)) pts hpts hprf

end MoussakaUnbound

end VoleMole.Theft
