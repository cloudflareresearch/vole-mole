import VoleMole.Prob.MoussakaUnbound
import VoleMole.ROM.CipherRelations
import VoleMole.ROM.PermFull

/-!
# The unbound Moussaka relations in the random-oracle and ideal-cipher model (fixed statement)

The bounds of `ROM/Accept.lean`, `ROM/CipherRelations.lean`, `ROM/CipherFull.lean` and
`ROM/PermFull.lean` for the two unbound relations of PR #63 (`security/moussaka-unbound.md` §2),
for **any verifier statement with the properties of `Unbound.IssueStmt` / `Unbound.RedeemStmt`**
(`Prob/MoussakaUnbound.lean`: the C++ parameters, DSTs and combination, the evaluator the
`Arith/MoussakaUnbound.lean` system). The proofs are those of the base relations with
`Unbound.issue_extract_chain`, `Unbound.redeem_extract_chain` as the per-chain step; nothing about
the random oracle, the ideal cipher or the identification of the chain depends on the relation.

With `n'` the number of constraints (`3816` for issuance, `7929` for redemption, at most 64
Anchors for redemption), and the terms of `ROM/CipherFull.lean` (`openHashEps`, `chainHitEps`,
`chainHitEpsComb`):

* `ROM.moussakaUnboundIssue_accept_le`, `ROM.moussakaUnboundRedeem_accept_le`: against the random
  oracle with any CTR PRG, `ε_bind`, `ε_dead`, `ε_chain` and the identification as hypotheses (as
  `moussakaIssue_accept_le`).
* `moussakaUnboundIssue_accept_le_ic`, `moussakaUnboundRedeem_accept_le_ic`: the joint hash and
  ideal-cipher experiment, binding explicit.
* **`moussakaUnboundIssue_accept_le_full`, `moussakaUnboundRedeem_accept_le_full`**: every term
  explicit (PRF view, forward cipher queries), no hypothesis beyond the query bounds:

      Pr[accept ∧ ¬Extracted] ≤ (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε₂ + (q₂₃+1)·9·2⁻¹²⁸ + 2·q_E²·2⁻²⁵⁶
        + 2·(openHashEps q + q₁·2⁻²⁵⁶) + 1024·q_E·q₁·2⁻²⁵⁶ + chainHitEps q [+ comb],

  `ε₂ = ε_QS(3816)` (issuance), `ε_QS(7929) + 2⁻¹²⁸ + (n+339)·2⁻⁴⁴⁸` (redemption, `n` the prover's
  hash queries).
* **`moussakaUnboundIssue_accept_le_perm`, `moussakaUnboundRedeem_accept_le_perm`**: the cipher as
  random permutations with inverse queries (`ROM/PermFull.lean`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM

variable [VoleMole.Verifier.HasPrg]

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.EndToEnd VoleMole.SeedExtraction

variable {β : Type}

/-- **Unbound issuance against the random oracle** (as `moussakaIssue_accept_le`):
`≤ (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·ε_QS(3816) + (Q+1)·9·2⁻¹²⁸ + ε_bind + ε_dead + ε_chain + hits`. -/
theorem moussakaUnboundIssue_accept_le {st : Statement} {lr : Bool} {t ctxIss : ByteArray}
    (hst : Unbound.IssueStmt st lr t ctxIss)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hC : (ChainData.ofSys (st := st) preOf midOf (Unbound.issueSys t ctxIss) accOf).Committed)
    (oa : OracleComp spec (ByteArray × ExtData β)) (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (chainFail deadFail : Out β → Prop) {εb εd εs : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables st oa)).run' ∅}[
      bindFail st r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables st oa)).run' ∅}[
      deadFail r] ≤ εd)
    (hchain : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables st oa)).run' ∅}[
      chainFail r] ≤ εs)
    (deadOf : Table → Fin BAVC.tau → Finset ℕ) (hit : Dom → Table → Prop) (εh : Kind → ℝ≥0∞)
    (hεh : ∀ k ∉ hitKinds, εh k = 0)
    (hhit : ∀ t g, Pr{let u ← $ᵗ (Ans t)}[hit t (Function.update g t u)] ≤ εh t.1)
    (hsame : SameChainHyp CrtGen.tables st oa preOf midOf accOf deadOf hit chainFail)
    (hL2 : DeadHiddenHyp CrtGen.tables st oa deadOf hit chainFail deadFail) :
    Pr{let r ← (simulateQ randomOracle (game CrtGen.tables st oa)).run' ∅}[
        r.2.2.accept = true ∧ ¬Extracted st
          (fun _ => moussakaUnboundIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + εb + εd + εs +
        hitSum (q + verifierQueries) εh := by
  classical
  refine (prEvent_accept_le_chain_terms liftInvOk_tables _ hC
    (fun _ _ => MoussakaUnbound.uIssueSystem_length _ _) 9 _
    (fun _ _ c1 lb w => hst.values c1 lb w)
    (fun y g ch known acc hv A hA hAS hkos hQS hP =>
      Unbound.issue_extract_chain hst ch hv hA hAS hkos hP.1 hQS admissible deltaBlocks
        deltaBlocks_injOn acc hP.2)
    oa q hq chainFail deadFail hbind hdead hchain deadOf hit εh hεh hhit hsame hL2).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ hst.witnessBytes_le hst.qsDegree_le
  · norm_num

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Unbound redemption against the random oracle** (at most 64 Anchors; as
`moussakaRedeem_accept_le`): `≤ (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·(ε_QS(7929) + 2⁻¹²⁸ + (n+337)·2⁻⁴⁴⁸) +
(Q+1)·9·2⁻¹²⁸ + ε_bind + ε_dead + ε_chain + hits`. -/
theorem moussakaUnboundRedeem_accept_le {st : Statement} {lr : Bool} {anchors : List UovPk}
    (hn64 : anchors.length ≤ 64) {nf ctxIss ctxRed : ByteArray}
    (hst : Unbound.RedeemStmt st lr anchors nf ctxIss ctxRed)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    (pre : ByteArray → Table → List Dom)
    (hC : (CombData.ofSys (st := st) preOf midOf (Unbound.redeemSysL anchors nf ctxIss ctxRed)
      (moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed)) accOf Unbound.combDst pre).Committed)
    (oa : OracleComp spec (ByteArray × ExtData β)) (n : ℕ) (hn : IsTotalQueryBound oa n)
    (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (chainFail deadFail : Out β → Prop) {εb εd εs : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables st oa)).run' ∅}[
      bindFail st r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables st oa)).run' ∅}[
      deadFail r] ≤ εd)
    (hchain : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables st oa)).run' ∅}[
      chainFail r] ≤ εs)
    (deadOf : Table → Fin BAVC.tau → Finset ℕ) (hit : Dom → Table → Prop) (εh : Kind → ℝ≥0∞)
    (hεh : ∀ k ∉ hitKinds, εh k = 0)
    (hhit : ∀ t g, Pr{let u ← $ᵗ (Ans t)}[hit t (Function.update g t u)] ≤ εh t.1)
    (hsame : SameChainHyp CrtGen.tables st oa preOf midOf accOf deadOf hit chainFail)
    (hL2 : DeadHiddenHyp CrtGen.tables st oa deadOf hit chainFail deadFail)
    (hcombFresh : CombFreshHyp CrtGen.tables _ (CombData.ofSys (st := st) preOf midOf
      (Unbound.redeemSysL anchors nf ctxIss ctxRed)
      (moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed)) accOf Unbound.combDst pre) oa hit chainFail) :
    Pr{let r ← (simulateQ randomOracle (game CrtGen.tables st oa)).run' ∅}[
        r.2.2.accept = true ∧ ¬Extracted st
          (fun _ => moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
            (fnOf ctxIss) (fnOf ctxRed)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + εb + εd + εs +
        hitSum (q + verifierQueries) εh := by
  classical
  refine (prEvent_accept_le_comb_terms liftInvOk_tables _ hC
    (fun _ _ _ => MoussakaUnbound.uRedeemSystem_length _ _ _ _ _ _ _)
    (fun _ _ w => prU_comb_bad_le _ _ w fun hW =>
      Unbound.redeem_comb_bad_gf128 _ (by simpa using hn64) _ _ _ w hW) 9 _ hst.comb
    (fun _ _ v w => by
      rw [hst.values]; simp only [Unbound.redeemSys, ofArr_combinationOf_ba]; rfl)
    (fun y g ch known acc l _ hv A hA hAS hkos hQS hcb hP =>
      Unbound.redeem_extract_chain hst ch l hv hA hAS hkos hP.1 hQS hcb admissible deltaBlocks
        deltaBlocks_injOn acc hP.2)
    oa n hn q hq chainFail deadFail hbind hdead hchain deadOf hit εh hεh hhit hsame hL2
    hcombFresh).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ hst.witnessBytes_le hst.qsDegree_le
  · norm_num

end VoleMole.ROM

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

variable {β : Type}

/-! ## The joint hash and ideal-cipher experiment, binding explicit -/

/-- **Unbound issuance in the random-oracle and ideal-cipher model, binding explicit** (as
`ratatouilleIssue_accept_le_ic`). -/
theorem moussakaUnboundIssue_accept_le_ic {st : Statement} {lr : Bool} {t ctxIss : ByteArray}
    (hst : Unbound.IssueStmt st lr t ctxIss)
    (preOf midOf : CTable → ByteArray → Table → Chain)
    (accOf : CTable → ByteArray → Table → Prob.Bytes 16 → Prop)
    (hC : ∀ E, (ChainData.ofSys (st := st) (preOf E) (midOf E) (Unbound.issueSys t ctxIss)
      (accOf E)).Committed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q)
    (chainFail deadFail : CTable → Out (β × QueryLog specIC) → Prop) {εd εs : ℝ≥0∞}
    (hdead : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables st P E)).run' ∅}[deadFail E r] ≤ εd)
    (hchain : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables st P E)).run' ∅}[chainFail E r] ≤ εs)
    (deadOf : CTable → Table → Fin BAVC.tau → Finset ℕ) (hit : CTable → Dom → Table → Prop)
    (εh : Kind → ℝ≥0∞) (hεh : ∀ k ∉ hitKinds, εh k = 0)
    (hhit : ∀ E t g, Pr{let u ← $ᵗ (Ans t)}[hit E t (Function.update g t u)] ≤ εh t.1)
    (hsame : ∀ E : CTable, @SameChainHyp (icPrg E.cipher) _ CrtGen.tables st (proverIC st E P)
      (preOf E) (midOf E) (accOf E) (deadOf E) (hit E) (chainFail E))
    (hL2 : ∀ E : CTable, @DeadHiddenHyp (icPrg E.cipher) _ CrtGen.tables st (proverIC st E P)
      (deadOf E) (hit E) (chainFail E) (deadFail E)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables st P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ st
          (fun _ => moussakaUnboundIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) + εd + εs +
        hitSum (q + verifierQueries) εh := by
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    hitSum (q + verifierQueries) εh
  refine (prEvent_joint_le_explicit CrtGen.tables _ P qE hqE q hq _ deadFail chainFail A
    fun E => ?_).trans ((add_le_add (add_le_add le_rfl hdead) hchain).trans
      (le_of_eq (by simp only [A]; ring)))
  have h := @moussakaUnboundIssue_accept_le (icPrg E.cipher) _ st lr t ctxIss hst (preOf E)
    (midOf E) (accOf E) (hC E) (proverIC st E P)
    (q + extractorQueries) (isKindQueryBound_proverIC _ E hq) (chainFail E) (deadFail E) _ _ _
    le_rfl le_rfl le_rfl (deadOf E) (hit E) εh hεh (hhit E) (hsame E) (hL2 E)
  simp only [gameIC]
  refine h.trans (le_of_eq ?_)
  rw [hitSum_add_extractorQueries]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero]
  ring

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Unbound redemption in the random-oracle and ideal-cipher model, binding explicit** (as
`moussakaRedeem_accept_le_ic`; the total count `n` of `P`'s hash queries raised by the extractor's
two). -/
theorem moussakaUnboundRedeem_accept_le_ic {st : Statement} {lr : Bool} {anchors : List UovPk}
    (hn64 : anchors.length ≤ 64) {nf ctxIss ctxRed : ByteArray}
    (hst : Unbound.RedeemStmt st lr anchors nf ctxIss ctxRed)
    (preOf midOf : CTable → ByteArray → Table → Chain)
    (accOf : CTable → ByteArray → Table → Prob.Bytes 16 → Prop)
    (pre : CTable → ByteArray → Table → List Dom)
    (hC : ∀ E, (CombData.ofSys (st := st) (preOf E) (midOf E)
      (Unbound.redeemSysL anchors nf ctxIss ctxRed)
      (moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed)) (accOf E) Unbound.combDst (pre E)).Committed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q)
    (chainFail deadFail : CTable → Out (β × QueryLog specIC) → Prop) {εd εs : ℝ≥0∞}
    (hdead : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables st P E)).run' ∅}[deadFail E r] ≤ εd)
    (hchain : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables st P E)).run' ∅}[chainFail E r] ≤ εs)
    (deadOf : CTable → Table → Fin BAVC.tau → Finset ℕ) (hit : CTable → Dom → Table → Prop)
    (εh : Kind → ℝ≥0∞) (hεh : ∀ k ∉ hitKinds, εh k = 0)
    (hhit : ∀ E t g, Pr{let u ← $ᵗ (Ans t)}[hit E t (Function.update g t u)] ≤ εh t.1)
    (hsame : ∀ E : CTable, @SameChainHyp (icPrg E.cipher) _ CrtGen.tables st (proverIC st E P)
      (preOf E) (midOf E) (accOf E) (deadOf E) (hit E) (chainFail E))
    (hL2 : ∀ E : CTable, @DeadHiddenHyp (icPrg E.cipher) _ CrtGen.tables st (proverIC st E P)
      (deadOf E) (hit E) (chainFail E) (deadFail E))
    (hcombFresh : ∀ E : CTable, @CombFreshHyp (icPrg E.cipher) _ _ CrtGen.tables st
      (CombData.ofSys (st := st) (preOf E) (midOf E) (Unbound.redeemSysL anchors nf ctxIss ctxRed)
        (moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
          (fnOf ctxRed)) (accOf E) Unbound.combDst (pre E))
      (proverIC st E P) (hit E) (chainFail E)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables st P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ st
          (fun _ => moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
            (fnOf ctxIss) (fnOf ctxRed)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) + εd + εs +
        hitSum (q + verifierQueries) εh := by
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    hitSum (q + verifierQueries) εh
  refine (prEvent_joint_le_explicit CrtGen.tables _ P qE hqE q hq _ deadFail chainFail A
    fun E => ?_).trans ((add_le_add (add_le_add le_rfl hdead) hchain).trans
      (le_of_eq (by simp only [A]; ring)))
  have h := @moussakaUnboundRedeem_accept_le (icPrg E.cipher) _ st lr anchors hn64 nf ctxIss
    ctxRed hst (preOf E) (midOf E) (accOf E) (pre E) (hC E) (proverIC st E P) (n + 2)
    (isTotalQueryBound_proverIC _ E hn)
    (q + extractorQueries) (isKindQueryBound_proverIC _ E hq) (chainFail E) (deadFail E) _ _ _
    le_rfl le_rfl le_rfl (deadOf E) (hit E) εh hεh (hhit E) (hsame E) (hL2 E) (hcombFresh E)
  simp only [gameIC]
  refine h.trans (le_of_eq ?_)
  rw [hitSum_add_extractorQueries]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero]
  ring

/-! ## Every term explicit (PRF view) -/

/-- **Unbound issuance in the random-oracle and ideal-cipher model, every term explicit** (as
`moussakaIssue_accept_le_full`):

    ≤ (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε_QS(3816) + (q₂₃+1)·9·2⁻¹²⁸ + 2·q_E²·2⁻²⁵⁶
      + 2·(openHashEps q + q₁·2⁻²⁵⁶) + 1024·q_E·q₁·2⁻²⁵⁶ + chainHitEps q. -/
theorem moussakaUnboundIssue_accept_le_full {st : Statement} {lr : Bool} {t ctxIss : ByteArray}
    (hst : Unbound.IssueStmt st lr t ctxIss)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables st P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ st
          (fun _ => moussakaUnboundIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEps q := by
  rw [← hitSum_hitEps]
  exact moussakaUnboundIssue_accept_le_ic hst (preOf CrtGen.tables st P)
    (midOf CrtGen.tables st P) (accOf CrtGen.tables st P)
    (fun E => chainData_committed CrtGen.tables st P E _) P qE hqE q hq (fun E r => PostOut E r)
    (fun E r => DeadOpenOut st E r) (prEvent_joint_deadOpen_le CrtGen.tables st P q hq)
    (prEvent_joint_postOut_le P CrtGen.tables st qE hqE q hq) (deadOf CrtGen.tables st P)
    (chainHit CrtGen.tables st P) _ (hitEps_eq_zero _ _)
    (fun E => by
      have h := prEvent_chainHit_le CrtGen.tables st P E _ (isKindQueryBound_gameIC _ st P E hq)
      rwa [hst.comb] at h)
    (sameChainHyp_ic CrtGen.tables st P) (deadHiddenHyp_ic CrtGen.tables st P)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Unbound redemption in the random-oracle and ideal-cipher model, every term explicit** (as
`moussakaRedeem_accept_le_full`; at most 64 Anchors, `n` the prover's total hash queries). -/
theorem moussakaUnboundRedeem_accept_le_full {st : Statement} {lr : Bool} {anchors : List UovPk}
    (hn64 : anchors.length ≤ 64) {nf ctxIss ctxRed : ByteArray}
    (hst : Unbound.RedeemStmt st lr anchors nf ctxIss ctxRed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables st P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ st
          (fun _ => moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
            (fnOf ctxIss) (fnOf ctxRed)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q Moussaka.M := by
  rw [← hitSum_hitEps_comb q Moussaka.M (cb := st.comb) hst.comb]
  exact moussakaUnboundRedeem_accept_le_ic hn64 hst (preOf CrtGen.tables _ P)
    (midOf CrtGen.tables _ P) (accOf CrtGen.tables _ P) (preCells CrtGen.tables _ P)
    (fun E => CombData.ofSys_committed _ _ _ _ _ _ _ (preOf_committed CrtGen.tables _ P E)
      (accOf_committed CrtGen.tables _ P E) (midOf_committed CrtGen.tables _ P E)
      (fun y g x v hx => midOf_comb CrtGen.tables _ P E Moussaka.M y g x v hx)
      (preCells_mid CrtGen.tables _ P E)
      (fun y g x v h => preCells_comb CrtGen.tables _ P E Moussaka.M y g x v h)) P qE hqE n hn q
    hq (fun E r => PostOut E r)
    (fun E r => DeadOpenOut _ E r) (prEvent_joint_deadOpen_le CrtGen.tables _ P q hq)
    (prEvent_joint_postOut_le P CrtGen.tables _ qE hqE q hq) (deadOf CrtGen.tables _ P)
    (chainHit CrtGen.tables _ P) _ (hitEps_eq_zero _ _)
    (fun E => prEvent_chainHit_le CrtGen.tables _ P E _ (isKindQueryBound_gameIC _ _ P E hq))
    (sameChainHyp_ic CrtGen.tables _ P) (deadHiddenHyp_ic CrtGen.tables _ P)
    (fun E => combFreshHyp_ic CrtGen.tables _ P E hst.comb _ rfl rfl)

/-! ## The ideal cipher as random permutations, with inverse queries -/

/-- **Unbound issuance with the ideal cipher as random permutations (forward and inverse
queries)** (as `moussakaIssue_accept_le_perm`), `p = 1/(2¹²⁸ − q_E)`, `p' = 1/(2¹²⁸ − q_E − 4607)`:

    ≤ (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε_QS(3816) + (q₂₃+1)·9·2⁻¹²⁸ + 2·q_E²·p²
      + 2·(openHashEps q + q₁·p'²) + q_E·4608·q₂₁·p² + chainHitEps q. -/
theorem moussakaUnboundIssue_accept_le_perm {st : Statement} {lr : Bool} {t ctxIss : ByteArray}
    (hst : Unbound.IssueStmt st lr t ctxIss)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameP CrtGen.tables st P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ st
          (fun _ => moussakaUnboundIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEps q := by
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEps q
  refine (prEvent_jointP_le_explicit CrtGen.tables st P qE hqE q hq _ A fun π => ?_).trans
    (le_of_eq (by simp only [A]; ring))
  have hqW := isKindQueryBound_normP st.params π hq
  have h := @moussakaUnboundIssue_accept_le (icPrg π.fwd.cipher) _ st lr t ctxIss hst
    (preOf CrtGen.tables st (Wn st P π) π.fwd) (midOf CrtGen.tables st (Wn st P π) π.fwd)
    (accOf CrtGen.tables st (Wn st P π) π.fwd)
    (chainData_committed CrtGen.tables st (Wn st P π) π.fwd _) (proverIC st π.fwd (Wn st P π))
    (addH4 q + extractorQueries) (isKindQueryBound_proverIC _ π.fwd hqW)
    (PostPOut st.params π.fwd) (DeadOpenOut st π.fwd) _ _ _ le_rfl le_rfl le_rfl
    (deadOf CrtGen.tables st (Wn st P π) π.fwd) (chainHit CrtGen.tables st (Wn st P π) π.fwd) _
    (hitEps_eq_zero _ _)
    (prEvent_chainHit_le CrtGen.tables st (Wn st P π) π.fwd _
      (isKindQueryBound_gameIC _ st _ π.fwd hqW))
    (sameChainHyp_icP CrtGen.tables st P π) (deadHiddenHyp_icP CrtGen.tables st P π)
  simp only [gameP, gameIC]
  refine h.trans (le_of_eq ?_)
  rw [hitSum_add_extractorQueries, hitSum_hitEps_perm q (cb := st.comb) hst.comb]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  ring

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Unbound redemption with the ideal cipher as random permutations** (as
`moussakaRedeem_accept_le_perm`; `n` is `P`'s total hash-query count, which the normalized prover
raises by one `H₄` query per `H₂¹` query). -/
theorem moussakaUnboundRedeem_accept_le_perm {st : Statement} {lr : Bool} {anchors : List UovPk}
    (hn64 : anchors.length ≤ 64) {nf ctxIss ctxRed : ByteArray}
    (hst : Unbound.RedeemStmt st lr anchors nf ctxIss ctxRed)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameP CrtGen.tables st P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ st
          (fun _ => moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
            (fnOf ctxIss) (fnOf ctxRed)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q Moussaka.M := by
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q Moussaka.M
  refine (prEvent_jointP_le_explicit CrtGen.tables st P qE hqE q hq _ A fun π => ?_).trans
    (le_of_eq (by simp only [A]; ring))
  have hqW := isKindQueryBound_normP st.params π hq
  have hnW := isQueryBoundP_left_normP st.params π hn hq
  have h := @moussakaUnboundRedeem_accept_le (icPrg π.fwd.cipher) _ st lr anchors hn64 nf ctxIss
    ctxRed hst
    (preOf CrtGen.tables st (Wn st P π) π.fwd) (midOf CrtGen.tables st (Wn st P π) π.fwd)
    (accOf CrtGen.tables st (Wn st P π) π.fwd) (preCells CrtGen.tables st (Wn st P π) π.fwd)
    (CombData.ofSys_committed _ _ _ _ _ _ _ (preOf_committed CrtGen.tables _ _ π.fwd)
      (accOf_committed CrtGen.tables _ _ π.fwd) (midOf_committed CrtGen.tables _ _ π.fwd)
      (fun y g x v hx => midOf_comb CrtGen.tables _ _ π.fwd Moussaka.M y g x v hx)
      (preCells_mid CrtGen.tables _ _ π.fwd)
      (fun y g x v h => preCells_comb CrtGen.tables _ _ π.fwd Moussaka.M y g x v h))
    (proverIC st π.fwd (Wn st P π)) (n + q .h21 + 2) (isTotalQueryBound_proverIC _ π.fwd hnW)
    (addH4 q + extractorQueries) (isKindQueryBound_proverIC _ π.fwd hqW)
    (PostPOut st.params π.fwd) (DeadOpenOut st π.fwd) _ _ _ le_rfl le_rfl le_rfl
    (deadOf CrtGen.tables st (Wn st P π) π.fwd) (chainHit CrtGen.tables st (Wn st P π) π.fwd) _
    (hitEps_eq_zero _ _)
    (prEvent_chainHit_le CrtGen.tables st (Wn st P π) π.fwd _
      (isKindQueryBound_gameIC _ st _ π.fwd hqW))
    (sameChainHyp_icP CrtGen.tables st P π) (deadHiddenHyp_icP CrtGen.tables st P π)
    (combFreshHyp_icP CrtGen.tables st P π hst.comb _ rfl rfl)
  simp only [gameP, gameIC]
  refine h.trans (le_of_eq ?_)
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb_perm q Moussaka.M (cb := st.comb) hst.comb]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  ring

end VoleMole.ROM.IC
