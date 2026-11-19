import VoleMole.EndToEnd.SpecRelations
import VoleMole.ROM.CipherFull
import VoleMole.ROM.PermFull
import VoleMole.ROM.AdaptFull
import VoleMole.ROM.AdaptComb
import VoleMole.ROM.AdaptPomfrit
import VoleMole.ROM.PermAdapt

/-!
# Soundness for the spec relations

The headline soundness theorems of the random-oracle and ideal-cipher layer bound
`Pr[accept ∧ ¬Extracted]` where "extracted" means that a known tree's candidate satisfies the
*arithmetized* relation (`EndToEnd/Relations.lean`). `EndToEnd/SpecRelations.lean` proves that an
arithmetized witness decodes to a witness of the *spec* relation (for well-formed instances), so
each bound also holds with the spec relation and the decoded witness in place of the arithmetized
one: `Pr[accept ∧ the decoded witness of no known tree is in the spec relation] ≤ the same bound`.

For each of the 20 headline theorems `X` (`*_accept_le_full`, `*_accept_le_perm`,
`*_accept_le_adaptive`, `*_accept_le_adaptive_perm`, for the five relations) there is `X_spec`, with
the same bound and, besides `X`'s hypotheses, only well-formedness of the instance:

| relation | spec relation (decoded witness) | extra hypotheses |
| --- | --- | --- |
| Moussaka issue | `Privacy.Moussaka.IssueRelW ⟨t, ctx_iss⟩` (`SpecRel.issueWitOf`) | `|t| = 45`, `|ctx_iss| = 16` |
| Moussaka redeem | `Privacy.Moussaka.RedeemRelW ⟨anchors, nf, ctx_iss, ctx_red, cd⟩` (`SpecRel.redeemWitOf`) | `|nf| = 24`, `|ctx_iss| = |ctx_red| = 16` |
| Ratatouille issue | `Spec.Ratatouille.IssueRel (SpecRel.issueInstOf c t_init ctx)` (`SpecRel.issueWitOfR`) | `t_init < 2⁶⁴` |
| Ratatouille spend | `Spec.Ratatouille.SpendRel (SpecRel.spendInstOf pk nf d c' ctx)` (`SpecRel.spendWitOf`) | none (`d < 2⁶⁴` is already assumed) |
| PomFRIT redeem | `SpecRel.PomRel pk h(chal1) r s` (`r`, `s` the candidate's bytes) | none |

(`issueInstOf`, `spendInstOf` read the byte arrays as fixed-length vectors; they are the verifier's
fields when those have the C++ lengths, `SpecRel.bOf_bytesVec`.) The adaptive versions keep `hinj`
as a hypothesis; `SpecRel.hinj_*` discharge it for fixed-length families.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-- Monotonicity of a two-stage experiment in its event. -/
theorem prEvent_bind_mono {T X : Type} (mT : ProbComp T) (m : T → ProbComp X)
    (p p' : T → X → Prop) (h : ∀ E r, p E r → p' E r) :
    Pr{let E ← mT; let r ← m E}[p E r] ≤ Pr{let E ← mT; let r ← m E}[p' E r] := by
  let : MeasurableSpace T := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  exact MeasureTheory.lintegral_mono fun E => prEvent_mono _ _ _ (h E)

/-- `Extracted` is monotone in the witness predicate. -/
theorem extracted_mono {hp : HasPrg} {β : Type} {st : Statement}
    {W W' : ByteArray → (ℕ → GF128) → Prop} (h : ∀ c w, W c w → W' c w) {r : Out β}
    (he : @Extracted hp β st W r) : @Extracted hp β st W' r := by
  obtain ⟨i, hi, hw⟩ := he
  exact ⟨i, hi, h _ _ hw⟩

variable {ι β : Type}

/-- `moussakaIssue_accept_le_full` for the spec relation (`IssueRelW`, the decoded witness
`issueWitOf`), for `t` of 45 bytes and `ctx_iss` of 16. -/
theorem moussakaIssue_accept_le_full_spec (t ctxIss : ByteArray) (ht : t.size = 45)
    (hci : ctxIss.size = 16) (labelRows : Bool)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaIssue t ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (moussakaIssue t ctxIss labelRows)
          (fun _ w => Privacy.Moussaka.IssueRelW ⟨toL t, toL ctxIss⟩
            (SpecRel.issueWitOf (toL ctxIss) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEps q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.issueRelW_of_wit t ctxIss ht hci w hw)
        he)⟩)
    (moussakaIssue_accept_le_full t ctxIss labelRows P qE hqE q hq)

/-- `moussakaIssue_accept_le_perm` for the spec relation (`IssueRelW`, the decoded witness
`issueWitOf`), for `t` of 45 bytes and `ctx_iss` of 16. -/
theorem moussakaIssue_accept_le_perm_spec (t ctxIss : ByteArray) (ht : t.size = 45)
    (hci : ctxIss.size = 16) (labelRows : Bool)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameP CrtGen.tables (moussakaIssue t ctxIss labelRows) P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (moussakaIssue t ctxIss labelRows)
          (fun _ w => Privacy.Moussaka.IssueRelW ⟨toL t, toL ctxIss⟩
            (SpecRel.issueWitOf (toL ctxIss) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEps q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.issueRelW_of_wit t ctxIss ht hci w hw)
        he)⟩)
    (moussakaIssue_accept_le_perm t ctxIss labelRows P qE hqE q hq)

/-- `moussakaIssue_accept_le_adaptive` for the spec relation of the chosen instance (`IssueRelW`,
`issueWitOf`), for families with `t` of 45 bytes and `ctx_iss` of 16 (`hinj`:
`SpecRel.hinj_moussakaIssue_of`). -/
theorem moussakaIssue_accept_le_adaptive_spec (inst : ι → ByteArray × ByteArray)
    (ht : ∀ s, (inst s).1.size = 45) (hci : ∀ s, (inst s).2.size = 16) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (moussakaIssue (inst s).1 (inst s).2 labelRows).instEnc ByteArray.empty)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => moussakaIssue (inst s).1 (inst s).2 labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (moussakaIssue (inst (stOut r)).1 (inst (stOut r)).2 labelRows)
          (fun _ w => Privacy.Moussaka.IssueRelW
            ⟨toL (inst (stOut r)).1, toL (inst (stOut r)).2⟩
            (SpecRel.issueWitOf (toL (inst (stOut r)).2) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEps q + stmtBindEps q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.issueRelW_of_wit _ _ (ht _) (hci _) w hw)
        he)⟩)
    (moussakaIssue_accept_le_adaptive inst labelRows hinj P qE hqE q hq)

/-- `moussakaIssue_accept_le_adaptive_perm` for the spec relation of the chosen instance
(`IssueRelW`, `issueWitOf`), for families with `t` of 45 bytes and `ctx_iss` of 16 (`hinj`:
`SpecRel.hinj_moussakaIssue_of`). -/
theorem moussakaIssue_accept_le_adaptive_perm_spec (inst : ι → ByteArray × ByteArray)
    (ht : ∀ s, (inst s).1.size = 45) (hci : ∀ s, (inst s).2.size = 16) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (moussakaIssue (inst s).1 (inst s).2 labelRows).instEnc ByteArray.empty)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => moussakaIssue (inst s).1 (inst s).2 labelRows)
      (normP (moussakaIssue ByteArray.empty ByteArray.empty labelRows).params π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (moussakaIssue (inst (stOut r)).1 (inst (stOut r)).2 labelRows)
          (fun _ w => Privacy.Moussaka.IssueRelW
            ⟨toL (inst (stOut r)).1, toL (inst (stOut r)).2⟩
            (SpecRel.issueWitOf (toL (inst (stOut r)).2) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEps q + stmtBindEps q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.issueRelW_of_wit _ _ (ht _) (hci _) w hw)
        he)⟩)
    (moussakaIssue_accept_le_adaptive_perm inst labelRows hinj P qE hqE q hq)

/-- `moussakaRedeem_accept_le_full` for the spec relation (`RedeemRelW`, the decoded witness
`redeemWitOf`), for `nf` of 24 bytes and contexts of 16. -/
theorem moussakaRedeem_accept_le_full_spec (anchors : List UovPk) (hn64 : anchors.length ≤ 64)
    (nf ctxIss ctxRed challengeDigest : ByteArray)
    (hnf : nf.size = 24) (hci : ctxIss.size = 16) (hcr : ctxRed.size = 16) (labelRows : Bool)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
          (fun _ w => Privacy.Moussaka.RedeemRelW
            ⟨anchors.map UovPk.toSpec, toL nf, toL ctxIss, toL ctxRed, toL challengeDigest⟩
            (SpecRel.redeemWitOf (toL nf) (toL ctxIss) (toL ctxRed) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q Moussaka.M := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.redeemRelW_of_wit anchors hn64 nf ctxIss ctxRed challengeDigest hnf hci hcr w hw)
        he)⟩)
    (moussakaRedeem_accept_le_full anchors hn64 nf ctxIss ctxRed challengeDigest labelRows P qE hqE
      n hn q hq)

/-- `moussakaRedeem_accept_le_perm` for the spec relation (`RedeemRelW`, the decoded witness
`redeemWitOf`), for `nf` of 24 bytes and contexts of 16. -/
theorem moussakaRedeem_accept_le_perm_spec (anchors : List UovPk) (hn64 : anchors.length ≤ 64)
    (nf ctxIss ctxRed challengeDigest : ByteArray)
    (hnf : nf.size = 24) (hci : ctxIss.size = 16) (hcr : ctxRed.size = 16) (labelRows : Bool)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameP CrtGen.tables
      (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
          (fun _ w => Privacy.Moussaka.RedeemRelW
            ⟨anchors.map UovPk.toSpec, toL nf, toL ctxIss, toL ctxRed, toL challengeDigest⟩
            (SpecRel.redeemWitOf (toL nf) (toL ctxIss) (toL ctxRed) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q Moussaka.M := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.redeemRelW_of_wit anchors hn64 nf ctxIss ctxRed challengeDigest hnf hci hcr w hw)
        he)⟩)
    (moussakaRedeem_accept_le_perm anchors hn64 nf ctxIss ctxRed challengeDigest labelRows P qE hqE
      n hn q hq)

/-- `moussakaRedeem_accept_le_adaptive` for the spec relation of the chosen instance (`RedeemRelW`,
`redeemWitOf`), for families with `nf` of 24 bytes and contexts of 16 (`hinj`:
`SpecRel.hinj_moussakaRedeem`). -/
theorem moussakaRedeem_accept_le_adaptive_spec (anc : ι → List UovPk)
    (hn64 : ∀ s, (anc s).length ≤ 64) (nf ctxIss ctxRed cd : ι → ByteArray)
    (hnf : ∀ s, (nf s).size = 24) (hci : ∀ s, (ctxIss s).size = 16)
    (hcr : ∀ s, (ctxRed s).size = 16) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows).instEnc
        ByteArray.empty)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (moussakaRedeem (anc (stOut r)) (nf (stOut r)) (ctxIss (stOut r)) (ctxRed (stOut r))
            (cd (stOut r)) labelRows)
          (fun _ w => Privacy.Moussaka.RedeemRelW
            ⟨(anc (stOut r)).map UovPk.toSpec, toL (nf (stOut r)), toL (ctxIss (stOut r)),
              toL (ctxRed (stOut r)), toL (cd (stOut r))⟩
            (SpecRel.redeemWitOf (toL (nf (stOut r))) (toL (ctxIss (stOut r)))
              (toL (ctxRed (stOut r))) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q Moussaka.M + stmtBindEps q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.redeemRelW_of_wit _ (hn64 _) _ _ _ _ (hnf _) (hci _) (hcr _) w hw)
        he)⟩)
    (moussakaRedeem_accept_le_adaptive anc hn64 nf ctxIss ctxRed cd labelRows hinj P qE hqE n hn q
      hq)

/-- `moussakaRedeem_accept_le_adaptive_perm` for the spec relation of the chosen instance
(`RedeemRelW`, `redeemWitOf`), for families with `nf` of 24 bytes and contexts of 16 (`hinj`:
`SpecRel.hinj_moussakaRedeem`). -/
theorem moussakaRedeem_accept_le_adaptive_perm_spec (anc : ι → List UovPk)
    (hn64 : ∀ s, (anc s).length ≤ 64) (nf ctxIss ctxRed cd : ι → ByteArray)
    (hnf : ∀ s, (nf s).size = 24) (hci : ∀ s, (ctxIss s).size = 16)
    (hcr : ∀ s, (ctxRed s).size = 16) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows).instEnc
        ByteArray.empty)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows)
      (normP (moussakaRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty ByteArray.empty
        labelRows).params π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (moussakaRedeem (anc (stOut r)) (nf (stOut r)) (ctxIss (stOut r)) (ctxRed (stOut r))
            (cd (stOut r)) labelRows)
          (fun _ w => Privacy.Moussaka.RedeemRelW
            ⟨(anc (stOut r)).map UovPk.toSpec, toL (nf (stOut r)), toL (ctxIss (stOut r)),
              toL (ctxRed (stOut r)), toL (cd (stOut r))⟩
            (SpecRel.redeemWitOf (toL (nf (stOut r))) (toL (ctxIss (stOut r)))
              (toL (ctxRed (stOut r))) w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q Moussaka.M +
        stmtBindEps q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.redeemRelW_of_wit _ (hn64 _) _ _ _ _ (hnf _) (hci _) (hcr _) w hw)
        he)⟩)
    (moussakaRedeem_accept_le_adaptive_perm anc hn64 nf ctxIss ctxRed cd labelRows hinj P qE hqE n
      hn q hq)

/-- `ratatouilleIssue_accept_le_full` for the spec relation (`Spec.Ratatouille.IssueRel` at
`issueInstOf`, the decoded witness `issueWitOfR`), for `t_init < 2⁶⁴`. -/
theorem ratatouilleIssue_accept_le_full_spec (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray)
    (ht : tInit < 2 ^ 64)
    (labelRows : Bool) (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (ratatouilleIssue c tInit ctxIss labelRows)
          (fun _ w => Spec.Ratatouille.IssueRel (SpecRel.issueInstOf c tInit ctxIss)
            (SpecRel.issueWitOfR w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEps q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.issueRel_of_witB c tInit ctxIss ht w hw)
        he)⟩)
    (ratatouilleIssue_accept_le_full c tInit ctxIss labelRows P qE hqE q hq)

/-- `ratatouilleIssue_accept_le_perm` for the spec relation (`Spec.Ratatouille.IssueRel` at
`issueInstOf`, the decoded witness `issueWitOfR`), for `t_init < 2⁶⁴`. -/
theorem ratatouilleIssue_accept_le_perm_spec (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray)
    (ht : tInit < 2 ^ 64)
    (labelRows : Bool) (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameP CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (ratatouilleIssue c tInit ctxIss labelRows)
          (fun _ w => Spec.Ratatouille.IssueRel (SpecRel.issueInstOf c tInit ctxIss)
            (SpecRel.issueWitOfR w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEps q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.issueRel_of_witB c tInit ctxIss ht w hw)
        he)⟩)
    (ratatouilleIssue_accept_le_perm c tInit ctxIss labelRows P qE hqE q hq)

/-- `ratatouilleIssue_accept_le_adaptive` for the spec relation of the chosen instance (`IssueRel`
at `issueInstOf`, `issueWitOfR`), for families with `t_init < 2⁶⁴` (`hinj`:
`SpecRel.hinj_ratatouilleIssue`). -/
theorem ratatouilleIssue_accept_le_adaptive_spec (inst : ι → ByteArray × ℕ × ByteArray) (ht : ∀ s,
    (inst s).2.1 < 2 ^ 64)
    (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows).instEnc ByteArray.empty)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (ratatouilleIssue (inst (stOut r)).1 (inst (stOut r)).2.1 (inst (stOut r)).2.2 labelRows)
          (fun _ w => Spec.Ratatouille.IssueRel
            (SpecRel.issueInstOf (inst (stOut r)).1 (inst (stOut r)).2.1 (inst (stOut r)).2.2)
            (SpecRel.issueWitOfR w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEps q + stmtBindEps q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.issueRel_of_witB _ _ _ (ht _) w hw)
        he)⟩)
    (ratatouilleIssue_accept_le_adaptive inst labelRows hinj P qE hqE q hq)

/-- `ratatouilleIssue_accept_le_adaptive_perm` for the spec relation of the chosen instance
(`IssueRel` at `issueInstOf`, `issueWitOfR`), for families with `t_init < 2⁶⁴` (`hinj`:
`SpecRel.hinj_ratatouilleIssue`). -/
theorem ratatouilleIssue_accept_le_adaptive_perm_spec (inst : ι → ByteArray × ℕ × ByteArray)
    (ht : ∀ s, (inst s).2.1 < 2 ^ 64)
    (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows).instEnc ByteArray.empty)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows)
      (normP (ratatouilleIssue .empty 0 .empty labelRows).params π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (ratatouilleIssue (inst (stOut r)).1 (inst (stOut r)).2.1 (inst (stOut r)).2.2 labelRows)
          (fun _ w => Spec.Ratatouille.IssueRel
            (SpecRel.issueInstOf (inst (stOut r)).1 (inst (stOut r)).2.1 (inst (stOut r)).2.2)
            (SpecRel.issueWitOfR w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEps q + stmtBindEps q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.issueRel_of_witB _ _ _ (ht _) w hw)
        he)⟩)
    (ratatouilleIssue_accept_le_adaptive_perm inst labelRows hinj P qE hqE q hq)

/-- `ratatouilleSpend_accept_le_full` for the spec relation (`Spec.Ratatouille.SpendRel` at
`spendInstOf`, the decoded witness `spendWitOf`). -/
theorem ratatouilleSpend_accept_le_full_spec (pk : UovPk) (nf : ByteArray) (d : ℕ) (hd : d < 2 ^ 64)
    (cNext ctxIss : ByteArray) (labelRows : Bool)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (ratatouilleSpend pk nf d cNext ctxIss labelRows)
          (fun _ w => Spec.Ratatouille.SpendRel (SpecRel.spendInstOf pk nf d cNext ctxIss)
            (SpecRel.spendWitOf w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q Ratatouille.uovM := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.spendRel_of_witB pk nf d hd cNext ctxIss w hw)
        he)⟩)
    (ratatouilleSpend_accept_le_full pk nf d hd cNext ctxIss labelRows P qE hqE n hn q hq)

/-- `ratatouilleSpend_accept_le_perm` for the spec relation (`Spec.Ratatouille.SpendRel` at
`spendInstOf`, the decoded witness `spendWitOf`). -/
theorem ratatouilleSpend_accept_le_perm_spec (pk : UovPk) (nf : ByteArray) (d : ℕ) (hd : d < 2 ^ 64)
    (cNext ctxIss : ByteArray) (labelRows : Bool)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameP CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (ratatouilleSpend pk nf d cNext ctxIss labelRows)
          (fun _ w => Spec.Ratatouille.SpendRel (SpecRel.spendInstOf pk nf d cNext ctxIss)
            (SpecRel.spendWitOf w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q Ratatouille.uovM := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.spendRel_of_witB pk nf d hd cNext ctxIss w hw)
        he)⟩)
    (ratatouilleSpend_accept_le_perm pk nf d hd cNext ctxIss labelRows P qE hqE n hn q hq)

/-- `ratatouilleSpend_accept_le_adaptive` for the spec relation of the chosen instance (`SpendRel`
at `spendInstOf`, `spendWitOf`; `hinj`: `SpecRel.hinj_ratatouilleSpend`). -/
theorem ratatouilleSpend_accept_le_adaptive_spec (pk : ι → UovPk) (nf : ι → ByteArray) (d : ι → ℕ)
    (hd : ∀ s, d s < 2 ^ 64) (cNext ctxIss : ι → ByteArray) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows).instEnc
        ByteArray.empty)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (ratatouilleSpend (pk (stOut r)) (nf (stOut r)) (d (stOut r)) (cNext (stOut r))
            (ctxIss (stOut r)) labelRows)
          (fun _ w => Spec.Ratatouille.SpendRel
            (SpecRel.spendInstOf (pk (stOut r)) (nf (stOut r)) (d (stOut r)) (cNext (stOut r))
              (ctxIss (stOut r)))
            (SpecRel.spendWitOf w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q Ratatouille.uovM + stmtBindEps q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.spendRel_of_witB _ _ _ (hd _) _ _ w hw)
        he)⟩)
    (ratatouilleSpend_accept_le_adaptive pk nf d hd cNext ctxIss labelRows hinj P qE hqE n hn q hq)

/-- `ratatouilleSpend_accept_le_adaptive_perm` for the spec relation of the chosen instance
(`SpendRel` at `spendInstOf`, `spendWitOf`; `hinj`: `SpecRel.hinj_ratatouilleSpend`). -/
theorem ratatouilleSpend_accept_le_adaptive_perm_spec (pk : ι → UovPk) (nf : ι → ByteArray)
    (d : ι → ℕ) (hd : ∀ s, d s < 2 ^ 64) (cNext ctxIss : ι → ByteArray) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows).instEnc
        ByteArray.empty)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows)
      (normP (ratatouilleSpend ⟨ByteArray.empty, ByteArray.empty⟩ ByteArray.empty 0
        ByteArray.empty ByteArray.empty labelRows).params π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (ratatouilleSpend (pk (stOut r)) (nf (stOut r)) (d (stOut r)) (cNext (stOut r))
            (ctxIss (stOut r)) labelRows)
          (fun _ w => Spec.Ratatouille.SpendRel
            (SpecRel.spendInstOf (pk (stOut r)) (nf (stOut r)) (d (stOut r)) (cNext (stOut r))
              (ctxIss (stOut r)))
            (SpecRel.spendWitOf w)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q Ratatouille.uovM +
        stmtBindEps q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.spendRel_of_witB _ _ _ (hd _) _ _ w hw)
        he)⟩)
    (ratatouilleSpend_accept_le_adaptive_perm pk nf d hd cNext ctxIss labelRows hinj P qE hqE n hn
      q hq)

/-- `pomfritRedeem_accept_le_full` for the spec relation (`PomRel`: `P(s) = h ⊕ r` on bytes for the
target `h` at the verifier's `chal1`, `(r, s)` the candidate's bytes `[0, 45)`, `[45, 164)`). -/
theorem pomfritRedeem_accept_le_full_spec (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (pomfritRedeem pk sig msg labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (pomfritRedeem pk sig msg labelRows)
          (fun c1 w => SpecRel.PomRel pk.toSpec
            (toL (pomfritTarget (pomfritParams labelRows) pk.digest c1 sig msg))
            (SpecRel.bytesOf (SpecRel.bitsOf w) 0 45)
            (SpecRel.bytesOf (SpecRel.bitsOf w) 45 119)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q 45 := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.pomRel_of_wit pk _ (SpecRel.size_pomfritTarget _ _ _ _ _) w hw)
        he)⟩)
    (pomfritRedeem_accept_le_full pk sig msg labelRows P qE hqE n hn q hq)

/-- `pomfritRedeem_accept_le_perm` for the spec relation (`PomRel`: `P(s) = h ⊕ r` on bytes for the
target `h` at the verifier's `chal1`, `(r, s)` the candidate's bytes `[0, 45)`, `[45, 164)`). -/
theorem pomfritRedeem_accept_le_perm_spec (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameP CrtGen.tables (pomfritRedeem pk sig msg labelRows) P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (pomfritRedeem pk sig msg labelRows)
          (fun c1 w => SpecRel.PomRel pk.toSpec
            (toL (pomfritTarget (pomfritParams labelRows) pk.digest c1 sig msg))
            (SpecRel.bytesOf (SpecRel.bitsOf w) 0 45)
            (SpecRel.bytesOf (SpecRel.bitsOf w) 45 119))
          r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q 45 := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.pomRel_of_wit pk _ (SpecRel.size_pomfritTarget _ _ _ _ _) w hw)
        he)⟩)
    (pomfritRedeem_accept_le_perm pk sig msg labelRows P qE hqE n hn q hq)

/-- `pomfritRedeem_accept_le_adaptive` for the spec relation (`PomRel` for the chosen signature and
message). -/
theorem pomfritRedeem_accept_le_adaptive_spec (pk : UovPk) (sigF msgF : ι → ByteArray)
    (labelRows : Bool)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => pomfritRedeem pk (sigF s) (msgF s) labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (pomfritRedeem pk (sigF (stOut r)) (msgF (stOut r)) labelRows)
          (fun c1 w => SpecRel.PomRel pk.toSpec
            (toL (pomfritTarget (pomfritParams labelRows) pk.digest c1 (sigF (stOut r))
              (msgF (stOut r))))
            (SpecRel.bytesOf (SpecRel.bitsOf w) 0 45)
            (SpecRel.bytesOf (SpecRel.bitsOf w) 45 119)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q 45 + stmtBindEpsD q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.pomRel_of_wit pk _ (SpecRel.size_pomfritTarget _ _ _ _ _) w hw)
        he)⟩)
    (pomfritRedeem_accept_le_adaptive pk sigF msgF labelRows P qE hqE n hn q hq)

/-- `pomfritRedeem_accept_le_adaptive_perm` for the spec relation (`PomRel` for the chosen signature
and message). -/
theorem pomfritRedeem_accept_le_adaptive_perm_spec (pk : UovPk) (sigF msgF : ι → ByteArray)
    (labelRows : Bool)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => pomfritRedeem pk (sigF s) (msgF s) labelRows)
      (normP (pomfritParams labelRows) π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (pomfritRedeem pk (sigF (stOut r)) (msgF (stOut r)) labelRows)
          (fun c1 w => SpecRel.PomRel pk.toSpec
            (toL (pomfritTarget (pomfritParams labelRows) pk.digest c1 (sigF (stOut r))
              (msgF (stOut r))))
            (SpecRel.bytesOf (SpecRel.bitsOf w) 0 45)
            (SpecRel.bytesOf (SpecRel.bitsOf w) 45 119)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q 45 +
        stmtBindEpsD q := by
  refine le_trans (prEvent_bind_mono _ _ _ _ fun E r h =>
    ⟨h.1, fun he => h.2 (extracted_mono (fun c1 w hw =>
      SpecRel.pomRel_of_wit pk _ (SpecRel.size_pomfritTarget _ _ _ _ _) w hw)
        he)⟩)
    (pomfritRedeem_accept_le_adaptive_perm pk sigF msgF labelRows P qE hqE n hn q hq)


end VoleMole.ROM.IC
