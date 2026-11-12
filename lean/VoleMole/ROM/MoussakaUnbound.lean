import VoleMole.ROM.CipherFull
import VoleMole.ROM.SingleOracle

/-!
# The random-oracle and ideal-cipher bounds for the unbound Moussaka relations

`ROM/Accept.lean`, `ROM/CipherRelations.lean` and `ROM/CipherFull.lean` for unbound Moussaka's two
relations (`Verifier/Relations.lean`: `moussakaUnboundIssue`, `moussakaUnboundRedeem`), from the
same generic theorems as the base relations (`prEvent_accept_le_chain_terms`,
`prEvent_accept_le_comb_terms`, `prEvent_joint_le_explicit` and the chain data, hits and failure
events of `ROM/CipherChain.lean`, `ROM/CipherSame.lean`), with the per-chain extraction of
`Verifier/Bridge/ChainRelations.lean` (`moussakaUnbound*_extract_chain`), the system lengths
`3816` and `7929` (`uIssueSystem_length`, `uRedeemSystem_length`) and, for redemption, the
combination term `moussaka_unbound_redeem_comb_bad_gf128` (at most 64 Anchors). The issuance proof
follows Ratatouille issuance's, the redemption proof Moussaka redemption's.

* `combOk_moussakaUnboundIssue`, `combOk_moussakaUnboundRedeem`: the single-oracle side condition
  (`ROM/SingleOracle.lean`; the combination DST `make_dst("mous", 1, 'l', '0')` ends in `'0'`).
* `moussakaUnboundIssue_accept_le`, `moussakaUnboundRedeem_accept_le`: against the random oracle,
  with `ε_bind`, `ε_dead`, `ε_chain` and the hits as hypotheses.
* `IC.moussakaUnboundIssue_accept_le_ic`, `IC.moussakaUnboundRedeem_accept_le_ic`: in the joint
  random-oracle and ideal-cipher experiment, binding explicit.
* **`IC.moussakaUnboundIssue_accept_le_full`, `IC.moussakaUnboundRedeem_accept_le_full`**: every
  term explicit, no hypothesis beyond the query bounds (and `|anchors| ≤ 64`):

      Pr[accept ∧ ¬Extracted] ≤ (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε_QS(3816) + (q₂₃+1)·9·2⁻¹²⁸ + (binding,
        dead-leaf and chain terms of `moussakaIssue_accept_le_full`)

  for issuance, and for redemption `(q₂₂+1)·(ε_QS(7929) + 2⁻¹²⁸ + (n+2+337)·2⁻⁴⁴⁸)` in the second
  term and `chainHitEpsComb q 45` for the hits, as `moussakaRedeem_accept_le_full`.

Not extended here: the variants with AES as random permutations (`ROM/PermFull.lean`), adaptively
chosen statements (`ROM/AdaptFull.lean`, `ROM/AdaptComb.lean`, `ROM/PermAdapt.lean`) and the spec
relations (`ROM/SpecSound.lean`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM

-- The statements hold for any CTR PRG (`HasPrg`, `Verifier/Prg.lean`), AES included.
variable [VoleMole.Verifier.HasPrg]

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.EndToEnd VoleMole.SeedExtraction

omit [VoleMole.Verifier.HasPrg] in
theorem combOk_moussakaUnboundIssue (t ctxIss : ByteArray) (labelRows : Bool) :
    CombOk (moussakaUnboundIssue t ctxIss labelRows) := fun _ _ h => by cases h

omit [VoleMole.Verifier.HasPrg] in
theorem combOk_moussakaUnboundRedeem (anchors : List UovPk)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool) :
    CombOk (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) :=
  combOk_dst rfl (by decide) (by decide) rfl

variable {β : Type}

/-- **Unbound Moussaka issuance against the random oracle**:
`≤ (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·ε_QS(3816) + (Q+1)·9·2⁻¹²⁸ + ε_bind + ε_dead + ε_chain`
(as `moussakaIssue_accept_le`). -/
theorem moussakaUnboundIssue_accept_le (t ctxIss : ByteArray) (labelRows : Bool) (preOf midOf : ByteArray → Table → Chain)
    (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hC : (ChainData.ofSys (st := moussakaUnboundIssue t ctxIss labelRows) preOf midOf
      (moussakaUnboundIssueSys t ctxIss) accOf).Committed)
    (oa : OracleComp spec (ByteArray × ExtData β)) (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (chainFail deadFail : Out β → Prop) {εb εd εs : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle
      (game CrtGen.tables (moussakaUnboundIssue t ctxIss labelRows) oa)).run' ∅}[
        bindFail (moussakaUnboundIssue t ctxIss labelRows) r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle
      (game CrtGen.tables (moussakaUnboundIssue t ctxIss labelRows) oa)).run' ∅}[deadFail r] ≤
        εd)
    (hchain : Pr{let r ← (simulateQ randomOracle
      (game CrtGen.tables (moussakaUnboundIssue t ctxIss labelRows) oa)).run' ∅}[chainFail r] ≤
        εs)
    (deadOf : Table → Fin BAVC.tau → Finset ℕ) (hit : Dom → Table → Prop) (εh : Kind → ℝ≥0∞)
    (hεh : ∀ k ∉ hitKinds, εh k = 0)
    (hhit : ∀ t g, Pr{let u ← $ᵗ (Ans t)}[hit t (Function.update g t u)] ≤ εh t.1)
    (hsame : SameChainHyp CrtGen.tables (moussakaUnboundIssue t ctxIss labelRows) oa preOf midOf accOf
      deadOf hit chainFail)
    (hL2 : DeadHiddenHyp CrtGen.tables (moussakaUnboundIssue t ctxIss labelRows) oa deadOf hit chainFail
      deadFail) :
    Pr{let r ← (simulateQ randomOracle
      (game CrtGen.tables (moussakaUnboundIssue t ctxIss labelRows) oa)).run' ∅}[
        r.2.2.accept = true ∧ ¬Extracted (moussakaUnboundIssue t ctxIss labelRows)
          (fun _ => moussakaUnboundIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + εb + εd + εs +
        hitSum (q + verifierQueries) εh := by
  classical
  refine (prEvent_accept_le_chain_terms liftInvOk_tables _ hC
    (fun _ _ => MoussakaUnbound.uIssueSystem_length _ _) 9 _
    (fun _ _ c1 lb w => moussakaUnboundIssue_values t ctxIss labelRows c1 lb w)
    (fun y g ch known acc hv A hA hAS hkos hQS hP =>
      moussakaUnboundIssue_extract_chain t ctxIss labelRows ch hv hA hAS hkos hP.1 hQS
        admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    oa q hq chainFail deadFail hbind hdead hchain deadOf hit εh hεh hhit hsame hL2).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ (by norm_num [moussakaUnboundIssue])
      (by norm_num [moussakaUnboundIssue])
  · norm_num

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Unbound Moussaka redemption against the random oracle** (at most 64 anchors):
`≤ (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·(ε_QS(7929) + 2⁻¹²⁸ + (n+337)·2⁻⁴⁴⁸) + (Q+1)·9·2⁻¹²⁸ + ε_bind + ε_dead +
ε_chain` (as `moussakaRedeem_accept_le`). -/
theorem moussakaUnboundRedeem_accept_le (anchors : List UovPk) (hn64 : anchors.length ≤ 64)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    (pre : ByteArray → Table → List Dom)
    (hC : (CombData.ofSys (st := moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      preOf midOf (moussakaUnboundRedeemSysL anchors nf ctxIss ctxRed)
      (moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed)) accOf (toBA (VoleMole.Spec.makeDst "mous" 1 'l' '0')) pre).Committed)
    (oa : OracleComp spec (ByteArray × ExtData β)) (n : ℕ) (hn : IsTotalQueryBound oa n)
    (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (chainFail deadFail : Out β → Prop) {εb εd εs : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) oa)).run' ∅}[
      bindFail (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) oa)).run' ∅}[
      deadFail r] ≤ εd)
    (hchain : Pr{let r ← (simulateQ randomOracle (game CrtGen.tables (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) oa)).run' ∅}[
      chainFail r] ≤ εs)
    (deadOf : Table → Fin BAVC.tau → Finset ℕ) (hit : Dom → Table → Prop) (εh : Kind → ℝ≥0∞)
    (hεh : ∀ k ∉ hitKinds, εh k = 0)
    (hhit : ∀ t g, Pr{let u ← $ᵗ (Ans t)}[hit t (Function.update g t u)] ≤ εh t.1)
    (hsame : SameChainHyp CrtGen.tables (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) oa preOf midOf accOf
      deadOf hit chainFail)
    (hL2 : DeadHiddenHyp CrtGen.tables (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) oa deadOf hit chainFail
      deadFail)
    (hcombFresh : CombFreshHyp CrtGen.tables _ (CombData.ofSys (st := moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      preOf midOf (moussakaUnboundRedeemSysL anchors nf ctxIss ctxRed)
      (moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed)) accOf (toBA (VoleMole.Spec.makeDst "mous" 1 'l' '0')) pre) oa hit chainFail) :
    Pr{let r ← (simulateQ randomOracle (game CrtGen.tables
      (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) oa)).run' ∅}[
        r.2.2.accept = true ∧ ¬Extracted
          (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
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
      moussaka_unbound_redeem_comb_bad_gf128 _ (by simpa using hn64) _ _ _ w hW) 9 _ rfl
    (fun _ _ v w => by
      rw [moussakaUnboundRedeem_values]; simp only [moussakaUnboundRedeemSys, ofArr_combinationOf_ba]; rfl)
    (fun y g ch known acc l _ hv A hA hAS hkos hQS hcb hP =>
      moussakaUnboundRedeem_extract_chain anchors nf ctxIss ctxRed challengeDigest labelRows ch l hv hA
        hAS hkos hP.1 hQS hcb admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    oa n hn q hq chainFail deadFail hbind hdead hchain deadOf hit εh hεh hhit hsame hL2 hcombFresh).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ (by norm_num [moussakaUnboundRedeem]) (by norm_num [moussakaUnboundRedeem])
  · norm_num

end VoleMole.ROM

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

variable {β : Type}

/-- **Unbound Moussaka issuance in the random-oracle and ideal-cipher model, binding explicit**
(as `ratatouilleIssue_accept_le_ic`, with `ε_QS(3816)`). -/
theorem moussakaUnboundIssue_accept_le_ic (t ctxIss : ByteArray) (labelRows : Bool) (preOf midOf : CTable → ByteArray → Table → Chain)
    (accOf : CTable → ByteArray → Table → Prob.Bytes 16 → Prop)
    (hC : ∀ E, (ChainData.ofSys (st := moussakaUnboundIssue t ctxIss labelRows) (preOf E)
      (midOf E) (moussakaUnboundIssueSys t ctxIss) (accOf E)).Committed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q)
    (chainFail deadFail : CTable → Out (β × QueryLog specIC) → Prop) {εd εs : ℝ≥0∞}
    (hdead : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaUnboundIssue t ctxIss labelRows) P E)).run' ∅}[
        deadFail E r] ≤ εd)
    (hchain : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaUnboundIssue t ctxIss labelRows) P E)).run' ∅}[
        chainFail E r] ≤ εs)
    (deadOf : CTable → Table → Fin BAVC.tau → Finset ℕ) (hit : CTable → Dom → Table → Prop)
    (εh : Kind → ℝ≥0∞) (hεh : ∀ k ∉ hitKinds, εh k = 0)
    (hhit : ∀ E t g, Pr{let u ← $ᵗ (Ans t)}[hit E t (Function.update g t u)] ≤ εh t.1)
    (hsame : ∀ E : CTable, @SameChainHyp (icPrg E.cipher) _ CrtGen.tables
      (moussakaUnboundIssue t ctxIss labelRows) (proverIC (moussakaUnboundIssue t ctxIss labelRows) E P)
      (preOf E) (midOf E) (accOf E) (deadOf E) (hit E) (chainFail E))
    (hL2 : ∀ E : CTable, @DeadHiddenHyp (icPrg E.cipher) _ CrtGen.tables
      (moussakaUnboundIssue t ctxIss labelRows) (proverIC (moussakaUnboundIssue t ctxIss labelRows) E P)
      (deadOf E) (hit E) (chainFail E) (deadFail E)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaUnboundIssue t ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (moussakaUnboundIssue t ctxIss labelRows)
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
  have h := @moussakaUnboundIssue_accept_le (icPrg E.cipher) _ t ctxIss labelRows (preOf E)
    (midOf E) (accOf E) (hC E) (proverIC (moussakaUnboundIssue t ctxIss labelRows) E P)
    (q + extractorQueries) (isKindQueryBound_proverIC _ E hq) (chainFail E) (deadFail E) _ _ _
    le_rfl le_rfl le_rfl (deadOf E) (hit E) εh hεh (hhit E) (hsame E) (hL2 E)
  simp only [gameIC]
  refine h.trans (le_of_eq ?_)
  rw [hitSum_add_extractorQueries]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero]
  ring

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Unbound Moussaka redemption in the random-oracle and ideal-cipher model, binding explicit**
(as `moussakaRedeem_accept_le_ic`, with `ε_QS(7929)`). -/
theorem moussakaUnboundRedeem_accept_le_ic (anchors : List UovPk) (hn64 : anchors.length ≤ 64)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool)
    (preOf midOf : CTable → ByteArray → Table → Chain)
    (accOf : CTable → ByteArray → Table → Prob.Bytes 16 → Prop)
    (pre : CTable → ByteArray → Table → List Dom)
    (hC : ∀ E, (CombData.ofSys (st := moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      (preOf E) (midOf E) (moussakaUnboundRedeemSysL anchors nf ctxIss ctxRed)
      (moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed)) (accOf E) (toBA (VoleMole.Spec.makeDst "mous" 1 'l' '0')) (pre E)).Committed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q)
    (chainFail deadFail : CTable → Out (β × QueryLog specIC) → Prop) {εd εs : ℝ≥0∞}
    (hdead : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P E)).run' ∅}[deadFail E r] ≤ εd)
    (hchain : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P E)).run' ∅}[chainFail E r] ≤ εs)
    (deadOf : CTable → Table → Fin BAVC.tau → Finset ℕ) (hit : CTable → Dom → Table → Prop)
    (εh : Kind → ℝ≥0∞) (hεh : ∀ k ∉ hitKinds, εh k = 0)
    (hhit : ∀ E t g, Pr{let u ← $ᵗ (Ans t)}[hit E t (Function.update g t u)] ≤ εh t.1)
    (hsame : ∀ E : CTable, @SameChainHyp (icPrg E.cipher) _ CrtGen.tables
      (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) (proverIC (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) E P)
      (preOf E) (midOf E) (accOf E) (deadOf E) (hit E) (chainFail E))
    (hL2 : ∀ E : CTable, @DeadHiddenHyp (icPrg E.cipher) _ CrtGen.tables
      (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) (proverIC (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) E P)
      (deadOf E) (hit E) (chainFail E) (deadFail E))
    (hcombFresh : ∀ E : CTable, @CombFreshHyp (icPrg E.cipher) _ _ CrtGen.tables
      (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) (CombData.ofSys (st := moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      (preOf E) (midOf E) (moussakaUnboundRedeemSysL anchors nf ctxIss ctxRed)
      (moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed)) (accOf E) (toBA (VoleMole.Spec.makeDst "mous" 1 'l' '0')) (pre E))
      (proverIC (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) E P) (hit E) (chainFail E)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
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
  have h := @moussakaUnboundRedeem_accept_le (icPrg E.cipher) _ anchors hn64 nf ctxIss ctxRed challengeDigest labelRows (preOf E)
    (midOf E) (accOf E) (pre E) (hC E) (proverIC (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) E P) (n + 2)
    (isTotalQueryBound_proverIC _ E hn)
    (q + extractorQueries) (isKindQueryBound_proverIC _ E hq) (chainFail E) (deadFail E) _ _ _
    le_rfl le_rfl le_rfl (deadOf E) (hit E) εh hεh (hhit E) (hsame E) (hL2 E) (hcombFresh E)
  simp only [gameIC]
  refine h.trans (le_of_eq ?_)
  rw [hitSum_add_extractorQueries]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero]
  ring

/-- **Unbound Moussaka issuance in the random-oracle and ideal-cipher model, every term
explicit** (as `moussakaIssue_accept_le_full`, with `ε_QS(3816)`). No assumption is left. -/
theorem moussakaUnboundIssue_accept_le_full (t ctxIss : ByteArray) (labelRows : Bool) (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaUnboundIssue t ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (moussakaUnboundIssue t ctxIss labelRows)
          (fun _ => moussakaUnboundIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEps q := by
  set st := moussakaUnboundIssue t ctxIss labelRows
  rw [← hitSum_hitEps]
  exact moussakaUnboundIssue_accept_le_ic t ctxIss labelRows (preOf CrtGen.tables st P)
    (midOf CrtGen.tables st P) (accOf CrtGen.tables st P)
    (fun E => chainData_committed CrtGen.tables st P E _) P qE hqE q hq (fun E r => PostOut E r)
    (fun E r => DeadOpenOut st E r) (prEvent_joint_deadOpen_le CrtGen.tables st P q hq)
    (prEvent_joint_postOut_le P CrtGen.tables st qE hqE q hq) (deadOf CrtGen.tables st P)
    (chainHit CrtGen.tables st P) _ (hitEps_eq_zero _ _)
    (fun E => prEvent_chainHit_le CrtGen.tables st P E _ (isKindQueryBound_gameIC _ st P E hq))
    (sameChainHyp_ic CrtGen.tables st P) (deadHiddenHyp_ic CrtGen.tables st P)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Unbound Moussaka redemption in the random-oracle and ideal-cipher model, every term
explicit** (as `moussakaRedeem_accept_le_full`, with `ε_QS(7929)`; `n` is `P`'s total hash-query
count). No assumption is left beyond `|anchors| ≤ 64`. -/
theorem moussakaUnboundRedeem_accept_le_full (anchors : List UovPk) (hn64 : anchors.length ≤ 64)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
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
  rw [← hitSum_hitEps_comb q Moussaka.M
    (cb := (moussakaUnboundRedeem anchors nf ctxIss ctxRed challengeDigest labelRows).comb) rfl]
  exact moussakaUnboundRedeem_accept_le_ic anchors hn64 nf ctxIss ctxRed challengeDigest labelRows (preOf CrtGen.tables _ P)
    (midOf CrtGen.tables _ P) (accOf CrtGen.tables _ P) (preCells CrtGen.tables _ P)
    (fun E => CombData.ofSys_committed _ _ _ _ _ _ _ (preOf_committed CrtGen.tables _ P E)
      (accOf_committed CrtGen.tables _ P E) (midOf_committed CrtGen.tables _ P E)
      (fun y g x v hx => midOf_comb CrtGen.tables _ P E Moussaka.M y g x v hx)
      (preCells_mid CrtGen.tables _ P E)
      (fun y g x v h => preCells_comb CrtGen.tables _ P E Moussaka.M y g x v h)) P qE hqE n hn q hq (fun E r => PostOut E r)
    (fun E r => DeadOpenOut _ E r) (prEvent_joint_deadOpen_le CrtGen.tables _ P q hq)
    (prEvent_joint_postOut_le P CrtGen.tables _ qE hqE q hq) (deadOf CrtGen.tables _ P)
    (chainHit CrtGen.tables _ P) _ (hitEps_eq_zero _ _)
    (fun E => prEvent_chainHit_le CrtGen.tables _ P E _ (isKindQueryBound_gameIC _ _ P E hq))
    (sameChainHyp_ic CrtGen.tables _ P) (deadHiddenHyp_ic CrtGen.tables _ P)
    (fun E => combFreshHyp_ic CrtGen.tables _ P E rfl _ rfl rfl)

end VoleMole.ROM.IC
