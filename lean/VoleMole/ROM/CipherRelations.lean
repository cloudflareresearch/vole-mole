import VoleMole.ROM.CipherOpen

/-!
# The other four relations in the ideal-cipher model, binding explicit (plan M6)

`ROM/CipherOpen.lean`'s `moussakaIssue_accept_le_ic'` for Ratatouille issuance, Moussaka
redemption, Ratatouille spend and PomFRIT redemption: the bounds of `ROM/Accept.lean` in the
joint hash and ideal-cipher experiment, with `ε_bind` replaced by

    2·q_E²·2⁻²⁵⁶ + openHashEps q + q₁·2⁻²⁵⁶

(`prEvent_joint_le_of_bindFail`, `prEvent_joint_deadOpen_le`). For the combined relations the
total hash-query count of the game's prover `proverIC` is `P`'s plus the extractor's two
(`isTotalQueryBound_proverIC`), so `n` becomes `n + 2`. `hsame`, `hL2`, the hits and, for the
combined relations, `hcombFresh` stay assumptions here (for every cipher table, with `ε_dead`,
`ε_chain` bounds on joint probabilities); `ROM/CipherFull.lean` discharges them.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

variable {α β : Type}

/-! ## Total hash-query counts -/

/-- The hash queries of `runE E P` are `P`'s. -/
theorem isTotalQueryBound_runE (E : CTable) {P : OracleComp specIC α} {n : ℕ}
    (hP : IsQueryBoundP P (fun t => t.isLeft = true) n) : IsTotalQueryBound (runE E P) n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hP
    cases t with
    | inl d =>
      rw [runE_inl]
      simp only [Sum.isLeft_inl, not_true_eq_false, false_or, ite_true] at hP
      exact isTotalQueryBound_query_bind_iff.2 ⟨hP.1, fun u =>
        (isQueryBound_map_iff _ _ _ _ _).2 (ih u (hP.2 u))⟩
    | inr x =>
      rw [runE_inr]
      exact (isQueryBound_map_iff _ _ _ _ _).2 (ih (E x) (by simpa using hP.2 (E x)))

/-- **The total hash queries of `proverIC`**: `P`'s and the extractor's two. -/
theorem isTotalQueryBound_proverIC (st : Statement) (E : CTable)
    {P : OracleComp specIC (ByteArray × β)} {n : ℕ}
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) :
    IsTotalQueryBound (proverIC st E P) (n + 2) := by
  unfold proverIC
  refine isTotalQueryBound_bind (isTotalQueryBound_runE E hn) fun r => ?_
  unfold mu1Q
  split <;>
  · refine isTotalQueryBound_hashQ_bind_iff.2 ⟨by norm_num, fun u => ?_⟩
    exact isTotalQueryBound_hashQ_bind_iff.2 ⟨by norm_num, fun _ => trivial⟩

/-! ## The joint bound from per-table bounds -/

/-- **From per-cipher-table bounds with `ε_bind`, `ε_dead`, `ε_chain` the game's own failure
probabilities to the joint experiment with binding explicit.** -/
theorem prEvent_joint_le_explicit (T : CrtTables) (st : Statement)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) (ev deadFail chainFail : CTable → Out (β × QueryLog specIC) → Prop)
    (c : ℝ≥0∞)
    (h : ∀ E, Pr{let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[ev E r] ≤
      c + Pr{let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[
          @bindFail (icPrg E.cipher) _ st r] +
        Pr{let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[deadFail E r] +
        Pr{let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[chainFail E r]) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[ev E r] ≤
      c + (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[
          deadFail E r] +
        Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[
          chainFail E r] :=
  (prEvent_joint_le_of_fails T st P qE hqE ev deadFail chainFail c h).trans
    (add_le_add (add_le_add (add_le_add le_rfl
      (add_le_add le_rfl (prEvent_joint_deadOpen_le T st P q hq))) le_rfl) le_rfl)

/-! ## The four relations -/

/-- **Ratatouille issuance in the random-oracle and ideal-cipher model, binding explicit**:

    Pr[accept ∧ ¬Extracted] ≤ (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε_QS(3776) + (q₂₃+1)·9·2⁻¹²⁸
      + (2·q_E²·2⁻²⁵⁶ + openHashEps q + q₁·2⁻²⁵⁶) + ε_dead + ε_chain. -/
theorem ratatouilleIssue_accept_le_ic (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray)
    (labelRows : Bool) (preOf midOf : CTable → ByteArray → Table → Chain)
    (accOf : CTable → ByteArray → Table → Prob.Bytes 16 → Prop)
    (hC : ∀ E, (ChainData.ofSys (st := ratatouilleIssue c tInit ctxIss labelRows) (preOf E)
      (midOf E) (ratatouilleIssueSys c tInit ctxIss) (accOf E)).Committed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q)
    (chainFail deadFail : CTable → Out (β × QueryLog specIC) → Prop) {εd εs : ℝ≥0∞}
    (hdead : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) P E)).run' ∅}[
        deadFail E r] ≤ εd)
    (hchain : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) P E)).run' ∅}[
        chainFail E r] ≤ εs)
    (deadOf : CTable → Table → Fin BAVC.tau → Finset ℕ) (hit : CTable → Dom → Table → Prop)
    (εh : Kind → ℝ≥0∞) (hεh : ∀ k ∉ hitKinds, εh k = 0)
    (hhit : ∀ E t g, Pr{let u ← $ᵗ (Ans t)}[hit E t (Function.update g t u)] ≤ εh t.1)
    (hsame : ∀ E : CTable, @SameChainHyp (icPrg E.cipher) _ CrtGen.tables
      (ratatouilleIssue c tInit ctxIss labelRows) (proverIC (ratatouilleIssue c tInit ctxIss labelRows) E P)
      (preOf E) (midOf E) (accOf E) (deadOf E) (hit E) (chainFail E))
    (hL2 : ∀ E : CTable, @DeadHiddenHyp (icPrg E.cipher) _ CrtGen.tables
      (ratatouilleIssue c tInit ctxIss labelRows) (proverIC (ratatouilleIssue c tInit ctxIss labelRows) E P)
      (deadOf E) (hit E) (chainFail E) (deadFail E)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (ratatouilleIssue c tInit ctxIss labelRows)
          (fun _ => ratatouilleIssueWit (fnOf c) tInit (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) + εd + εs +
        hitSum (q + verifierQueries) εh := by
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    hitSum (q + verifierQueries) εh
  refine (prEvent_joint_le_explicit CrtGen.tables _ P qE hqE q hq _ deadFail chainFail A
    fun E => ?_).trans ((add_le_add (add_le_add le_rfl hdead) hchain).trans
      (le_of_eq (by simp only [A]; ring)))
  have h := @ratatouilleIssue_accept_le (icPrg E.cipher) _ c tInit ctxIss labelRows (preOf E)
    (midOf E) (accOf E) (hC E) (proverIC (ratatouilleIssue c tInit ctxIss labelRows) E P)
    (q + extractorQueries) (isKindQueryBound_proverIC _ E hq) (chainFail E) (deadFail E) _ _ _
    le_rfl le_rfl le_rfl (deadOf E) (hit E) εh hεh (hhit E) (hsame E) (hL2 E)
  simp only [gameIC]
  refine h.trans (le_of_eq ?_)
  rw [hitSum_add_extractorQueries]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero]
  ring

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Moussaka redemption in the random-oracle and ideal-cipher model, binding explicit**: as
`moussakaRedeem_accept_le` in the joint experiment, with `ε_bind` replaced by
`2·q_E²·2⁻²⁵⁶ + openHashEps q + q₁·2⁻²⁵⁶` and the total count `n` of `P`'s hash queries raised
by the extractor's two. -/
theorem moussakaRedeem_accept_le_ic (anchors : List UovPk) (hn64 : anchors.length ≤ 64)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool)
    (preOf midOf : CTable → ByteArray → Table → Chain)
    (accOf : CTable → ByteArray → Table → Prob.Bytes 16 → Prop)
    (pre : CTable → ByteArray → Table → List Dom)
    (hC : ∀ E, (CombData.ofSys (st := moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      (preOf E) (midOf E) (moussakaRedeemSysL anchors nf ctxIss ctxRed)
      (moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed)) (accOf E) (toBA (VoleMole.Spec.makeDst "mous" 0 'l' '0')) (pre E)).Committed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q)
    (chainFail deadFail : CTable → Out (β × QueryLog specIC) → Prop) {εd εs : ℝ≥0∞}
    (hdead : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P E)).run' ∅}[deadFail E r] ≤ εd)
    (hchain : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P E)).run' ∅}[chainFail E r] ≤ εs)
    (deadOf : CTable → Table → Fin BAVC.tau → Finset ℕ) (hit : CTable → Dom → Table → Prop)
    (εh : Kind → ℝ≥0∞) (hεh : ∀ k ∉ hitKinds, εh k = 0)
    (hhit : ∀ E t g, Pr{let u ← $ᵗ (Ans t)}[hit E t (Function.update g t u)] ≤ εh t.1)
    (hsame : ∀ E : CTable, @SameChainHyp (icPrg E.cipher) _ CrtGen.tables
      (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) (proverIC (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) E P)
      (preOf E) (midOf E) (accOf E) (deadOf E) (hit E) (chainFail E))
    (hL2 : ∀ E : CTable, @DeadHiddenHyp (icPrg E.cipher) _ CrtGen.tables
      (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) (proverIC (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) E P)
      (deadOf E) (hit E) (chainFail E) (deadFail E))
    (hcombFresh : ∀ E : CTable, @CombFreshHyp (icPrg E.cipher) _ _ CrtGen.tables
      (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) (CombData.ofSys (st := moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      (preOf E) (midOf E) (moussakaRedeemSysL anchors nf ctxIss ctxRed)
      (moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed)) (accOf E) (toBA (VoleMole.Spec.makeDst "mous" 0 'l' '0')) (pre E))
      (proverIC (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) E P) (hit E) (chainFail E)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
          (fun _ => moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
            (fnOf ctxIss) (fnOf ctxRed)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) + εd + εs +
        hitSum (q + verifierQueries) εh := by
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    hitSum (q + verifierQueries) εh
  refine (prEvent_joint_le_explicit CrtGen.tables _ P qE hqE q hq _ deadFail chainFail A
    fun E => ?_).trans ((add_le_add (add_le_add le_rfl hdead) hchain).trans
      (le_of_eq (by simp only [A]; ring)))
  have h := @moussakaRedeem_accept_le (icPrg E.cipher) _ anchors hn64 nf ctxIss ctxRed challengeDigest labelRows (preOf E)
    (midOf E) (accOf E) (pre E) (hC E) (proverIC (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) E P) (n + 2)
    (isTotalQueryBound_proverIC _ E hn)
    (q + extractorQueries) (isKindQueryBound_proverIC _ E hq) (chainFail E) (deadFail E) _ _ _
    le_rfl le_rfl le_rfl (deadOf E) (hit E) εh hεh (hhit E) (hsame E) (hL2 E) (hcombFresh E)
  simp only [gameIC]
  refine h.trans (le_of_eq ?_)
  rw [hitSum_add_extractorQueries]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero]
  ring

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Ratatouille spend in the random-oracle and ideal-cipher model, binding explicit**: as
`ratatouilleSpend_accept_le` in the joint experiment, with `ε_bind` replaced by
`2·q_E²·2⁻²⁵⁶ + openHashEps q + q₁·2⁻²⁵⁶` and the total count `n` of `P`'s hash queries raised
by the extractor's two. -/
theorem ratatouilleSpend_accept_le_ic (pk : UovPk) (nf : ByteArray) (d : ℕ) (hd : d < 2 ^ 64)
    (cNext ctxIss : ByteArray) (labelRows : Bool)
    (preOf midOf : CTable → ByteArray → Table → Chain)
    (accOf : CTable → ByteArray → Table → Prob.Bytes 16 → Prop)
    (pre : CTable → ByteArray → Table → List Dom)
    (hC : ∀ E, (CombData.ofSys (st := ratatouilleSpend pk nf d cNext ctxIss labelRows)
      (preOf E) (midOf E) (ratatouilleSpendSysL pk nf d cNext ctxIss)
      (ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss)) (accOf E)
      (toBA (VoleMole.Spec.makeDst "rata" 0 'l' '0')) (pre E)).Committed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q)
    (chainFail deadFail : CTable → Out (β × QueryLog specIC) → Prop) {εd εs : ℝ≥0∞}
    (hdead : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) P E)).run' ∅}[deadFail E r] ≤ εd)
    (hchain : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) P E)).run' ∅}[chainFail E r] ≤ εs)
    (deadOf : CTable → Table → Fin BAVC.tau → Finset ℕ) (hit : CTable → Dom → Table → Prop)
    (εh : Kind → ℝ≥0∞) (hεh : ∀ k ∉ hitKinds, εh k = 0)
    (hhit : ∀ E t g, Pr{let u ← $ᵗ (Ans t)}[hit E t (Function.update g t u)] ≤ εh t.1)
    (hsame : ∀ E : CTable, @SameChainHyp (icPrg E.cipher) _ CrtGen.tables
      (ratatouilleSpend pk nf d cNext ctxIss labelRows) (proverIC (ratatouilleSpend pk nf d cNext ctxIss labelRows) E P)
      (preOf E) (midOf E) (accOf E) (deadOf E) (hit E) (chainFail E))
    (hL2 : ∀ E : CTable, @DeadHiddenHyp (icPrg E.cipher) _ CrtGen.tables
      (ratatouilleSpend pk nf d cNext ctxIss labelRows) (proverIC (ratatouilleSpend pk nf d cNext ctxIss labelRows) E P)
      (deadOf E) (hit E) (chainFail E) (deadFail E))
    (hcombFresh : ∀ E : CTable, @CombFreshHyp (icPrg E.cipher) _ _ CrtGen.tables
      (ratatouilleSpend pk nf d cNext ctxIss labelRows) (CombData.ofSys (st := ratatouilleSpend pk nf d cNext ctxIss labelRows)
      (preOf E) (midOf E) (ratatouilleSpendSysL pk nf d cNext ctxIss)
      (ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss)) (accOf E)
      (toBA (VoleMole.Spec.makeDst "rata" 0 'l' '0')) (pre E))
      (proverIC (ratatouilleSpend pk nf d cNext ctxIss labelRows) E P) (hit E) (chainFail E)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (ratatouilleSpend pk nf d cNext ctxIss labelRows)
          (fun _ => ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext)
            (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) + εd + εs +
        hitSum (q + verifierQueries) εh := by
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    hitSum (q + verifierQueries) εh
  refine (prEvent_joint_le_explicit CrtGen.tables _ P qE hqE q hq _ deadFail chainFail A
    fun E => ?_).trans ((add_le_add (add_le_add le_rfl hdead) hchain).trans
      (le_of_eq (by simp only [A]; ring)))
  have h := @ratatouilleSpend_accept_le (icPrg E.cipher) _ pk nf d hd cNext ctxIss labelRows (preOf E)
    (midOf E) (accOf E) (pre E) (hC E) (proverIC (ratatouilleSpend pk nf d cNext ctxIss labelRows) E P) (n + 2)
    (isTotalQueryBound_proverIC _ E hn)
    (q + extractorQueries) (isKindQueryBound_proverIC _ E hq) (chainFail E) (deadFail E) _ _ _
    le_rfl le_rfl le_rfl (deadOf E) (hit E) εh hεh (hhit E) (hsame E) (hL2 E) (hcombFresh E)
  simp only [gameIC]
  refine h.trans (le_of_eq ?_)
  rw [hitSum_add_extractorQueries]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero]
  ring

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **PomFRIT redemption in the random-oracle and ideal-cipher model, binding explicit**: as
`pomfritRedeem_accept_le` in the joint experiment, with `ε_bind` replaced by
`2·q_E²·2⁻²⁵⁶ + openHashEps q + q₁·2⁻²⁵⁶` and the total count `n` of `P`'s hash queries raised
by the extractor's two. -/
theorem pomfritRedeem_accept_le_ic (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool)
    (preOf midOf : CTable → ByteArray → Table → Chain)
    (accOf : CTable → ByteArray → Table → Prob.Bytes 16 → Prop)
    (pre : CTable → ByteArray → Table → List Dom)
    (hC : ∀ E, (pomfritData pk sig msg labelRows (preOf E) (midOf E) (accOf E) (pre E)).Committed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q)
    (chainFail deadFail : CTable → Out (β × QueryLog specIC) → Prop) {εd εs : ℝ≥0∞}
    (hdead : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (pomfritRedeem pk sig msg labelRows) P E)).run' ∅}[deadFail E r] ≤ εd)
    (hchain : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (pomfritRedeem pk sig msg labelRows) P E)).run' ∅}[chainFail E r] ≤ εs)
    (deadOf : CTable → Table → Fin BAVC.tau → Finset ℕ) (hit : CTable → Dom → Table → Prop)
    (εh : Kind → ℝ≥0∞) (hεh : ∀ k ∉ hitKinds, εh k = 0)
    (hhit : ∀ E t g, Pr{let u ← $ᵗ (Ans t)}[hit E t (Function.update g t u)] ≤ εh t.1)
    (hsame : ∀ E : CTable, @SameChainHyp (icPrg E.cipher) _ CrtGen.tables
      (pomfritRedeem pk sig msg labelRows) (proverIC (pomfritRedeem pk sig msg labelRows) E P)
      (preOf E) (midOf E) (accOf E) (deadOf E) (hit E) (chainFail E))
    (hL2 : ∀ E : CTable, @DeadHiddenHyp (icPrg E.cipher) _ CrtGen.tables
      (pomfritRedeem pk sig msg labelRows) (proverIC (pomfritRedeem pk sig msg labelRows) E P)
      (deadOf E) (hit E) (chainFail E) (deadFail E))
    (hcombFresh : ∀ E : CTable, @CombFreshHyp (icPrg E.cipher) _ _ CrtGen.tables
      (pomfritRedeem pk sig msg labelRows) (pomfritData pk sig msg labelRows (preOf E) (midOf E) (accOf E) (pre E))
      (proverIC (pomfritRedeem pk sig msg labelRows) E P) (hit E) (chainFail E)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (pomfritRedeem pk sig msg labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (pomfritRedeem pk sig msg labelRows)
          (fun c1 => pomfritWit GF256.ofBits 119 45 pk.map
            (fun k => ⟨fnOf (pomfritTarget (pomfritParams labelRows) pk.digest c1 sig msg) k.val⟩)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) + εd + εs +
        hitSum (q + verifierQueries) εh := by
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) +
    hitSum (q + verifierQueries) εh
  refine (prEvent_joint_le_explicit CrtGen.tables _ P qE hqE q hq _ deadFail chainFail A
    fun E => ?_).trans ((add_le_add (add_le_add le_rfl hdead) hchain).trans
      (le_of_eq (by simp only [A]; ring)))
  have h := @pomfritRedeem_accept_le (icPrg E.cipher) _ pk sig msg labelRows (preOf E)
    (midOf E) (accOf E) (pre E) (hC E) (proverIC (pomfritRedeem pk sig msg labelRows) E P) (n + 2)
    (isTotalQueryBound_proverIC _ E hn)
    (q + extractorQueries) (isKindQueryBound_proverIC _ E hq) (chainFail E) (deadFail E) _ _ _
    le_rfl le_rfl le_rfl (deadOf E) (hit E) εh hεh (hhit E) (hsame E) (hL2 E) (hcombFresh E)
  simp only [gameIC]
  refine h.trans (le_of_eq ?_)
  rw [hitSum_add_extractorQueries]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero]
  ring

end VoleMole.ROM.IC
