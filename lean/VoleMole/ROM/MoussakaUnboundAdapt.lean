import VoleMole.ROM.MoussakaUnbound
import VoleMole.ROM.PermAdapt

/-!
# The unbound Moussaka relations with adaptively chosen statements

`ROM/AdaptFull.lean`, `ROM/AdaptComb.lean` and `ROM/PermAdapt.lean` for the two unbound
relations: the prover outputs a proof and the index `s` of the statement `stF s` it proves, from a
family of statements with the properties of `Unbound.IssueStmt` / `Unbound.RedeemStmt` (one
label-row choice, so common parameters, DST and combination) and injective instance encodings
(`hinj`). The bound is the fixed-statement one (`ROM/MoussakaUnbound.lean`) plus the
statement-binding term `stmtBindEps q = (q₀+3)·(q₂₁+q₀+4)·2⁻²⁵⁶`:

* `moussakaUnboundIssue_accept_le_adaptive`, `moussakaUnboundRedeem_accept_le_adaptive` (PRF view);
* `moussakaUnboundIssue_accept_le_adaptive_perm`, `moussakaUnboundRedeem_accept_le_adaptive_perm`
  (random permutations, inverse queries).

`hinj` is discharged for the C++ encodings in `EndToEnd/MoussakaUnboundSpec.lean`
(`hinj_unboundIssue`: `t` of fixed length; `hinj_unboundRedeem`: as `hinj_moussakaRedeem`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

variable {ι β : Type}

/-- **Unbound issuance with an adaptively chosen statement** (as
`moussakaIssue_accept_le_adaptive`): for a family `stF` of unbound issuance statements at
`inst s = (t, ctx_iss)` with injective instance encodings,

    ≤ (the bound of `moussakaUnboundIssue_accept_le_full`) + (q₀+3)·(q₂₁+q₀+4)·2⁻²⁵⁶. -/
theorem moussakaUnboundIssue_accept_le_adaptive (stF : ι → Statement) (lr : Bool)
    (inst : ι → ByteArray × ByteArray)
    (hst : ∀ s, Unbound.IssueStmt (stF s) lr (inst s).1 (inst s).2)
    (hinj : Function.Injective fun s => (stF s).instEnc ByteArray.empty)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables stF P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r))
          (fun _ => moussakaUnboundIssueWit (fun k => fnOf (inst (stOut r)).1 k.val)
            (fnOf (inst (stOut r)).2)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEps q + stmtBindEps q := by
  classical
  set st₀ := Unbound.refIssue lr ByteArray.empty ByteArray.empty
  have hmu := muIn_injective (stF := stF) (dst := Unbound.issueDst) (fun s => (hst s).dst) hinj
  have h := prEvent_accept_le_adaptive CrtGen.tables stF (decOf fun s => muIn (stF s))
    (fun s => Unbound.issueSys (inst s).1 (inst s).2) P liftInvOk_tables st₀
    (fun s => (hst s).params) (fun s => (hst s).delayed) none (fun s => (hst s).comb)
    (fun s => decOf_apply hmu s) (fun s => MoussakaUnbound.uIssueSystem_length _ _) 9
    (fun s _ => moussakaUnboundIssueWit (fun k => fnOf (inst s).1 k.val) (fnOf (inst s).2))
    (fun s c1 lb w => (hst s).values c1 lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        Unbound.issue_extract_chain (hst s) ch hv hA hAS hkos hP.1 hQS admissible deltaBlocks
          deltaBlocks_injOn acc hP.2)
    qE hqE q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps, stmtEps_game]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (Unbound.refIssue_stmt _ _ _).witnessBytes_le
      (Unbound.refIssue_stmt _ _ _).qsDegree_le
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
          ((q .h23 : ℝ≥0∞) + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEps q + stmtBindEps q +
          (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
          (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
          ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
        gcongr
    _ = _ := by ring

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Unbound redemption with an adaptively chosen statement** (as
`moussakaRedeem_accept_le_adaptive`; at most 64 Anchors per statement):

    ≤ (the bound of `moussakaUnboundRedeem_accept_le_full`) + (q₀+3)·(q₂₁+q₀+4)·2⁻²⁵⁶. -/
theorem moussakaUnboundRedeem_accept_le_adaptive (stF : ι → Statement) (lr : Bool)
    (anc : ι → List UovPk) (hn64 : ∀ s, (anc s).length ≤ 64) (nf ctxIss ctxRed : ι → ByteArray)
    (hst : ∀ s, Unbound.RedeemStmt (stF s) lr (anc s) (nf s) (ctxIss s) (ctxRed s))
    (hinj : Function.Injective fun s => (stF s).instEnc ByteArray.empty)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables stF P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r))
          (fun _ => moussakaUnboundRedeemWit GF256.ofBits ((anc (stOut r)).map UovPk.map)
            (fnOf (nf (stOut r))) (fnOf (ctxIss (stOut r))) (fnOf (ctxRed (stOut r)))) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q Moussaka.M + stmtBindEps q := by
  classical
  set st₀ := Unbound.refRedeem lr [] ByteArray.empty ByteArray.empty ByteArray.empty
    ByteArray.empty
  have hmu := muIn_injective (stF := stF) (dst := Unbound.redeemDst) (fun s => (hst s).dst) hinj
  have h := prEvent_accept_le_adaptive_comb CrtGen.tables stF (decOf fun s => muIn (stF s)) P
    (fun s => Unbound.redeemSysL (anc s) (nf s) (ctxIss s) (ctxRed s))
    (fun s => moussakaUnboundRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    Unbound.combDst liftInvOk_tables st₀ (fun s => (hst s).params) (fun s => (hst s).delayed)
    (fun s => (hst s).comb) (fun s => decOf_apply hmu s)
    (fun s _ => MoussakaUnbound.uRedeemSystem_length _ _ _ _ _ _ _)
    (fun s w => prU_comb_bad_le _ _ w fun hW =>
      Unbound.redeem_comb_bad_gf128 _ (by simpa using hn64 s) _ _ _ w hW) 9
    (fun s _ => moussakaUnboundRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    (fun s c1 v w => by
      rw [(hst s).values]; simp only [Unbound.redeemSys, ofArr_combinationOf_ba])
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc l hv A hA hAS hkos hQS hcb hP =>
        Unbound.redeem_extract_chain (hst s) ch l hv hA hAS hkos hP.1 hQS hcb admissible
          deltaBlocks deltaBlocks_injOn acc hP.2)
    qE hqE n hn q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb q Moussaka.M rfl, stmtEps_game]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (Unbound.refRedeem_stmt _ _ _ _ _ _).witnessBytes_le
      (Unbound.refRedeem_stmt _ _ _ _ _ _).qsDegree_le
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n : ℝ≥0∞) + 2 + (verifierTotal : ℝ≥0∞)) / 2 ^ 448) +
          ((q .h23 : ℝ≥0∞) + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q Moussaka.M +
          stmtBindEps q +
          (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
          (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
          ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
        gcongr
    _ = _ := by push_cast; ring

/-- **Unbound issuance with an adaptively chosen statement and the ideal cipher as random
permutations** (as `moussakaIssue_accept_le_adaptive_perm`; the normalized prover uses the
family's common parameters `Unbound.issueParams lr`):

    ≤ (the bound of `moussakaUnboundIssue_accept_le_perm`) + stmtBindEps q. -/
theorem moussakaUnboundIssue_accept_le_adaptive_perm (stF : ι → Statement) (lr : Bool)
    (inst : ι → ByteArray × ByteArray)
    (hst : ∀ s, Unbound.IssueStmt (stF s) lr (inst s).1 (inst s).2)
    (hinj : Function.Injective fun s => (stF s).instEnc ByteArray.empty)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables stF
      (normP (Unbound.issueParams lr) π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (stF (stOut r))
          (fun _ => moussakaUnboundIssueWit (fun k => fnOf (inst (stOut r)).1 k.val)
            (fnOf (inst (stOut r)).2)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEps q + stmtBindEps q := by
  classical
  set st₀ := Unbound.refIssue lr ByteArray.empty ByteArray.empty
  have hmu := muIn_injective (stF := stF) (dst := Unbound.issueDst) (fun s => (hst s).dst) hinj
  have h := prEvent_accept_le_adaptiveP CrtGen.tables stF (decOf fun s => muIn (stF s))
    (fun s => Unbound.issueSys (inst s).1 (inst s).2) P liftInvOk_tables st₀
    (fun s => (hst s).params) (fun s => (hst s).delayed) none (fun s => (hst s).comb)
    (fun s => decOf_apply hmu s) (fun s => MoussakaUnbound.uIssueSystem_length _ _) 9
    (fun s _ => moussakaUnboundIssueWit (fun k => fnOf (inst s).1 k.val) (fnOf (inst s).2))
    (fun s c1 lb w => (hst s).values c1 lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        Unbound.issue_extract_chain (hst s) ch hv hA hAS hkos hP.1 hQS admissible deltaBlocks
          deltaBlocks_injOn acc hP.2)
    qE hqE q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps_perm q rfl, stmtEps_game, stmtBindEps_addH4]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (Unbound.refIssue_stmt _ _ _).witnessBytes_le
      (Unbound.refIssue_stmt _ _ _).qsDegree_le
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
          ((q .h23 : ℝ≥0∞) + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEps q + stmtBindEps q +
          (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
          (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
          qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
        gcongr
    _ = _ := by ring

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Unbound redemption with an adaptively chosen statement and the ideal cipher as random
permutations** (as `moussakaRedeem_accept_le_adaptive_perm`):

    ≤ (the bound of `moussakaUnboundRedeem_accept_le_perm`) + stmtBindEps q. -/
theorem moussakaUnboundRedeem_accept_le_adaptive_perm (stF : ι → Statement) (lr : Bool)
    (anc : ι → List UovPk) (hn64 : ∀ s, (anc s).length ≤ 64) (nf ctxIss ctxRed : ι → ByteArray)
    (hst : ∀ s, Unbound.RedeemStmt (stF s) lr (anc s) (nf s) (ctxIss s) (ctxRed s))
    (hinj : Function.Injective fun s => (stF s).instEnc ByteArray.empty)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables stF
      (normP (Unbound.redeemParams lr) π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (stF (stOut r))
          (fun _ => moussakaUnboundRedeemWit GF256.ofBits ((anc (stOut r)).map UovPk.map)
            (fnOf (nf (stOut r))) (fnOf (ctxIss (stOut r))) (fnOf (ctxRed (stOut r)))) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q Moussaka.M +
        stmtBindEps q := by
  classical
  set st₀ := Unbound.refRedeem lr [] ByteArray.empty ByteArray.empty ByteArray.empty
    ByteArray.empty
  have hmu := muIn_injective (stF := stF) (dst := Unbound.redeemDst) (fun s => (hst s).dst) hinj
  have h := prEvent_accept_le_adaptive_combP CrtGen.tables stF (decOf fun s => muIn (stF s)) P
    (fun s => Unbound.redeemSysL (anc s) (nf s) (ctxIss s) (ctxRed s))
    (fun s => moussakaUnboundRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    Unbound.combDst liftInvOk_tables st₀ (fun s => (hst s).params) (fun s => (hst s).delayed)
    (fun s => (hst s).comb) (fun s => decOf_apply hmu s)
    (fun s _ => MoussakaUnbound.uRedeemSystem_length _ _ _ _ _ _ _)
    (fun s w => prU_comb_bad_le _ _ w fun hW =>
      Unbound.redeem_comb_bad_gf128 _ (by simpa using hn64 s) _ _ _ w hW) 9
    (fun s _ => moussakaUnboundRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    (fun s c1 v w => by
      rw [(hst s).values]; simp only [Unbound.redeemSys, ofArr_combinationOf_ba])
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc l hv A hA hAS hkos hQS hcb hP =>
        Unbound.redeem_extract_chain (hst s) ch l hv hA hAS hkos hP.1 hQS hcb admissible
          deltaBlocks deltaBlocks_injOn acc hP.2)
    qE hqE n hn q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb_perm q Moussaka.M rfl, stmtEps_game,
    stmtBindEps_addH4]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (Unbound.refRedeem_stmt _ _ _ _ _ _).witnessBytes_le
      (Unbound.refRedeem_stmt _ _ _ _ _ _).qsDegree_le
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ +
            ((n : ℝ≥0∞) + (q .h21 : ℝ≥0∞) + 2 + (verifierTotal : ℝ≥0∞)) / 2 ^ 448) +
          ((q .h23 : ℝ≥0∞) + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q Moussaka.M +
          stmtBindEps q +
          (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
          (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
          qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
        gcongr
    _ = _ := by push_cast; ring

end VoleMole.ROM.IC
