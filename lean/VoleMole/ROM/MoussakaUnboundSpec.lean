import VoleMole.ROM.MoussakaUnboundAdapt
import VoleMole.ROM.SpecSound
import VoleMole.EndToEnd.MoussakaUnboundSpec

/-!
# Soundness of the unbound Moussaka relations for the spec relations

`ROM/SpecSound.lean` for the unbound relations: each of the eight headline bounds of
`ROM/MoussakaUnbound.lean` and `ROM/MoussakaUnboundAdapt.lean` (`_full`, `_perm`, `_adaptive`,
`_adaptive_perm`, for issuance and redemption) holds with the same bound for "the decoded witness
of no known tree is in the spec relation" (`EndToEnd/MoussakaUnboundSpec.lean`):

| relation | spec relation (decoded witness) | extra hypotheses |
| --- | --- | --- |
| unbound issue | `Spec.MoussakaUnbound.IssueRel ⟨t, ctx_iss⟩` (`SpecRel.uIssueWitOf`) | `|t| = 45` |
| unbound redeem | `Spec.MoussakaUnbound.RedeemRel ⟨anchors, nf, ctx_iss, ctx_red, cd⟩` (`SpecRel.uRedeemWitOf`) | `|nf| = 24` (`|anchors| ≤ 64` is already assumed) |

`cd` (the challenge digest) is any byte string: the relation does not read it. The adaptive
versions keep `hinj` (`SpecRel.hinj_unboundIssue`, `SpecRel.hinj_unboundRedeem` discharge it for
the C++ encodings).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

variable {ι β : Type}

/-- `moussakaUnboundIssue_accept_le_full` for the spec relation (`IssueRel`, the decoded witness
`uIssueWitOf`), for `t` of 45 bytes. -/
theorem moussakaUnboundIssue_accept_le_full_spec {st : Statement} {lr : Bool}
    {t ctxIss : ByteArray} (hst : Unbound.IssueStmt st lr t ctxIss) (ht : t.size = 45)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables st P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ st
          (fun _ w => Spec.MoussakaUnbound.IssueRel ⟨toL t, toL ctxIss⟩
            (SpecRel.uIssueWitOf (toL ctxIss) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEps q :=
  le_trans (prEvent_bind_mono _ _ _ _ fun _ _ h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun _ w hw =>
      SpecRel.uIssueRel_of_wit t ctxIss ht w hw) he)⟩)
    (moussakaUnboundIssue_accept_le_full hst P qE hqE q hq)

/-- `moussakaUnboundIssue_accept_le_perm` for the spec relation, for `t` of 45 bytes. -/
theorem moussakaUnboundIssue_accept_le_perm_spec {st : Statement} {lr : Bool}
    {t ctxIss : ByteArray} (hst : Unbound.IssueStmt st lr t ctxIss) (ht : t.size = 45)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameP CrtGen.tables st P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ st
          (fun _ w => Spec.MoussakaUnbound.IssueRel ⟨toL t, toL ctxIss⟩
            (SpecRel.uIssueWitOf (toL ctxIss) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEps q :=
  le_trans (prEvent_bind_mono _ _ _ _ fun _ _ h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun _ w hw =>
      SpecRel.uIssueRel_of_wit t ctxIss ht w hw) he)⟩)
    (moussakaUnboundIssue_accept_le_perm hst P qE hqE q hq)

/-- `moussakaUnboundIssue_accept_le_adaptive` for the spec relation of the chosen instance, for
families with `t` of 45 bytes (`hinj`: `SpecRel.hinj_unboundIssue`). -/
theorem moussakaUnboundIssue_accept_le_adaptive_spec (stF : ι → Statement) (lr : Bool)
    (inst : ι → ByteArray × ByteArray)
    (hst : ∀ s, Unbound.IssueStmt (stF s) lr (inst s).1 (inst s).2)
    (ht : ∀ s, (inst s).1.size = 45)
    (hinj : Function.Injective fun s => (stF s).instEnc ByteArray.empty)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables stF P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r))
          (fun _ w => Spec.MoussakaUnbound.IssueRel
            ⟨toL (inst (stOut r)).1, toL (inst (stOut r)).2⟩
            (SpecRel.uIssueWitOf (toL (inst (stOut r)).2) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEps q + stmtBindEps q :=
  le_trans (prEvent_bind_mono _ _ _ _ fun _ _ h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun _ w hw =>
      SpecRel.uIssueRel_of_wit _ _ (ht _) w hw) he)⟩)
    (moussakaUnboundIssue_accept_le_adaptive stF lr inst hst hinj P qE hqE q hq)

/-- `moussakaUnboundIssue_accept_le_adaptive_perm` for the spec relation of the chosen instance,
for families with `t` of 45 bytes. -/
theorem moussakaUnboundIssue_accept_le_adaptive_perm_spec (stF : ι → Statement) (lr : Bool)
    (inst : ι → ByteArray × ByteArray)
    (hst : ∀ s, Unbound.IssueStmt (stF s) lr (inst s).1 (inst s).2)
    (ht : ∀ s, (inst s).1.size = 45)
    (hinj : Function.Injective fun s => (stF s).instEnc ByteArray.empty)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables stF
      (normP (Unbound.issueParams lr) π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (stF (stOut r))
          (fun _ w => Spec.MoussakaUnbound.IssueRel
            ⟨toL (inst (stOut r)).1, toL (inst (stOut r)).2⟩
            (SpecRel.uIssueWitOf (toL (inst (stOut r)).2) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEps q + stmtBindEps q :=
  le_trans (prEvent_bind_mono _ _ _ _ fun _ _ h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun _ w hw =>
      SpecRel.uIssueRel_of_wit _ _ (ht _) w hw) he)⟩)
    (moussakaUnboundIssue_accept_le_adaptive_perm stF lr inst hst hinj P qE hqE q hq)

/-- `moussakaUnboundRedeem_accept_le_full` for the spec relation (`RedeemRel`, the decoded
witness `uRedeemWitOf`), for `nf` of 24 bytes and any `challenge_digest` `cd`. -/
theorem moussakaUnboundRedeem_accept_le_full_spec {st : Statement} {lr : Bool}
    {anchors : List UovPk} (hn64 : anchors.length ≤ 64) {nf ctxIss ctxRed : ByteArray}
    (hst : Unbound.RedeemStmt st lr anchors nf ctxIss ctxRed) (hnf : nf.size = 24)
    (cd : ByteArray)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables st P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ st
          (fun _ w => Spec.MoussakaUnbound.RedeemRel
            ⟨anchors.map UovPk.toSpec, toL nf, toL ctxIss, toL ctxRed, toL cd⟩
            (SpecRel.uRedeemWitOf (toL ctxIss) (toL ctxRed) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q Moussaka.M :=
  le_trans (prEvent_bind_mono _ _ _ _ fun _ _ h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun _ w hw =>
      SpecRel.uRedeemRel_of_wit anchors hn64 nf ctxIss ctxRed cd hnf w hw) he)⟩)
    (moussakaUnboundRedeem_accept_le_full hn64 hst P qE hqE n hn q hq)

/-- `moussakaUnboundRedeem_accept_le_perm` for the spec relation, for `nf` of 24 bytes. -/
theorem moussakaUnboundRedeem_accept_le_perm_spec {st : Statement} {lr : Bool}
    {anchors : List UovPk} (hn64 : anchors.length ≤ 64) {nf ctxIss ctxRed : ByteArray}
    (hst : Unbound.RedeemStmt st lr anchors nf ctxIss ctxRed) (hnf : nf.size = 24)
    (cd : ByteArray)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameP CrtGen.tables st P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ st
          (fun _ w => Spec.MoussakaUnbound.RedeemRel
            ⟨anchors.map UovPk.toSpec, toL nf, toL ctxIss, toL ctxRed, toL cd⟩
            (SpecRel.uRedeemWitOf (toL ctxIss) (toL ctxRed) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q Moussaka.M :=
  le_trans (prEvent_bind_mono _ _ _ _ fun _ _ h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun _ w hw =>
      SpecRel.uRedeemRel_of_wit anchors hn64 nf ctxIss ctxRed cd hnf w hw) he)⟩)
    (moussakaUnboundRedeem_accept_le_perm hn64 hst P qE hqE n hn q hq)

/-- `moussakaUnboundRedeem_accept_le_adaptive` for the spec relation of the chosen instance, for
families with `nf` of 24 bytes (`hinj`: `SpecRel.hinj_unboundRedeem`). -/
theorem moussakaUnboundRedeem_accept_le_adaptive_spec (stF : ι → Statement) (lr : Bool)
    (anc : ι → List UovPk) (hn64 : ∀ s, (anc s).length ≤ 64) (nf ctxIss ctxRed cd : ι → ByteArray)
    (hst : ∀ s, Unbound.RedeemStmt (stF s) lr (anc s) (nf s) (ctxIss s) (ctxRed s))
    (hnf : ∀ s, (nf s).size = 24)
    (hinj : Function.Injective fun s => (stF s).instEnc ByteArray.empty)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables stF P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r))
          (fun _ w => Spec.MoussakaUnbound.RedeemRel
            ⟨(anc (stOut r)).map UovPk.toSpec, toL (nf (stOut r)), toL (ctxIss (stOut r)),
              toL (ctxRed (stOut r)), toL (cd (stOut r))⟩
            (SpecRel.uRedeemWitOf (toL (ctxIss (stOut r))) (toL (ctxRed (stOut r))) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q Moussaka.M + stmtBindEps q :=
  le_trans (prEvent_bind_mono _ _ _ _ fun _ _ h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun _ w hw =>
      SpecRel.uRedeemRel_of_wit _ (hn64 _) _ _ _ _ (hnf _) w hw) he)⟩)
    (moussakaUnboundRedeem_accept_le_adaptive stF lr anc hn64 nf ctxIss ctxRed hst hinj P qE hqE
      n hn q hq)

/-- `moussakaUnboundRedeem_accept_le_adaptive_perm` for the spec relation of the chosen
instance, for families with `nf` of 24 bytes. -/
theorem moussakaUnboundRedeem_accept_le_adaptive_perm_spec (stF : ι → Statement) (lr : Bool)
    (anc : ι → List UovPk) (hn64 : ∀ s, (anc s).length ≤ 64) (nf ctxIss ctxRed cd : ι → ByteArray)
    (hst : ∀ s, Unbound.RedeemStmt (stF s) lr (anc s) (nf s) (ctxIss s) (ctxRed s))
    (hnf : ∀ s, (nf s).size = 24)
    (hinj : Function.Injective fun s => (stF s).instEnc ByteArray.empty)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables stF
      (normP (Unbound.redeemParams lr) π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (stF (stOut r))
          (fun _ w => Spec.MoussakaUnbound.RedeemRel
            ⟨(anc (stOut r)).map UovPk.toSpec, toL (nf (stOut r)), toL (ctxIss (stOut r)),
              toL (ctxRed (stOut r)), toL (cd (stOut r))⟩
            (SpecRel.uRedeemWitOf (toL (ctxIss (stOut r))) (toL (ctxRed (stOut r))) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q Moussaka.M +
        stmtBindEps q :=
  le_trans (prEvent_bind_mono _ _ _ _ fun _ _ h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun _ w hw =>
      SpecRel.uRedeemRel_of_wit _ (hn64 _) _ _ _ _ (hnf _) w hw) he)⟩)
    (moussakaUnboundRedeem_accept_le_adaptive_perm stF lr anc hn64 nf ctxIss ctxRed hst hinj P qE
      hqE n hn q hq)

end VoleMole.ROM.IC
