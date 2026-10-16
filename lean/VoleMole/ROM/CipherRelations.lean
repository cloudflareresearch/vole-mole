import VoleMole.ROM.CipherOpen

/-!
# The other four relations in the ideal-cipher model, binding explicit (plan M6)

`ROM/CipherOpen.lean`'s `moussakaIssue_accept_le_ic'` for Ratatouille issuance, Moussaka
redemption, Ratatouille spend and PomFRIT redemption: the bounds of `ROM/Accept.lean` in the
joint hash and ideal-cipher experiment, with `ε_bind` replaced by

    2·q_E²·2⁻²⁵⁶ + openHashEps q + q₁·2⁻²⁵⁶

(`prEvent_joint_le_of_bindFail`, `prEvent_joint_deadOpen_le`). For the combined relations the
total hash-query count of the game's prover `proverIC` is `P`'s plus the extractor's two
(`isTotalQueryBound_proverIC`), so `n` becomes `n + 2`. `hsame` (`ε_chain`) and `hL2` (`ε_dead`)
stay assumptions, for every cipher table.
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

/-- **From per-cipher-table bounds with `ε_bind = Pr[bindFail]` to the joint experiment with
binding explicit.** -/
theorem prEvent_joint_le_explicit (T : CrtTables) (st : Statement)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) (ev : CTable → Out (β × QueryLog specIC) → Prop) (c : ℝ≥0∞)
    (h : ∀ E, Pr{let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[ev E r] ≤
      c + Pr{let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[
        @bindFail (icPrg E.cipher) _ st r]) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[ev E r] ≤
      c + (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) :=
  (prEvent_joint_le_of_bindFail T st P qE hqE ev c h).trans
    (add_le_add le_rfl (add_le_add le_rfl (prEvent_joint_deadOpen_le T st P q hq)))

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
    (hdead : ∀ E, Pr{let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) P E)).run' ∅}[
        deadFail E r] ≤ εd)
    (hchain : ∀ E, Pr{let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) P E)).run' ∅}[
        chainFail E r] ≤ εs)
    (hsame : ∀ (E : CTable) (g : Table), let _ : HasPrg := icPrg E.cipher
      let st := ratatouilleIssue c tInit ctxIss labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC CrtGen.tables st P E)
      r.2.2.accept = true → ¬chainFail E r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      let ch := runChain (Hashes.ofTable g) CrtGen.tables st r.1 leaves r.2.1.keys
      SameChain st CrtGen.tables (preOf E) (midOf E) (accOf E) g ch
        (runX (Hashes.ofTable g) st r.1 leaves) (runY (Hashes.ofTable g) st ch) (runZ st ch))
    (hL2 : ∀ (E : CTable) (g : Table), let _ : HasPrg := icPrg E.cipher
      let st := ratatouilleIssue c tInit ctxIss labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC CrtGen.tables st P E)
      r.2.2.accept = true → ¬chainFail E r → ¬deadFail E r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      ∀ i ∉ r.2.1.known, IsFixed ((onSet st CrtGen.tables (runChain (Hashes.ofTable g)
        CrtGen.tables st r.1 leaves r.2.1.keys) chal3Blocks : Finset Blocks) : Set Blocks) i) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (ratatouilleIssue c tInit ctxIss labelRows)
          (fun _ => ratatouilleIssueWit (fnOf c) tInit (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) + εd + εs := by
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128)
  refine (prEvent_joint_le_explicit CrtGen.tables _ P qE hqE q hq _ (A + εd + εs) fun E => ?_).trans
    (le_of_eq (by ring))
  have h := @ratatouilleIssue_accept_le (icPrg E.cipher) _ c tInit ctxIss labelRows (preOf E)
    (midOf E) (accOf E) (hC E) (proverIC (ratatouilleIssue c tInit ctxIss labelRows) E P)
    (q + extractorQueries) (isKindQueryBound_proverIC _ E hq) (chainFail E) (deadFail E) _ _ _
    le_rfl (hdead E) (hchain E) (hsame E) (hL2 E)
  simp only [gameIC]
  refine h.trans (le_of_eq ?_)
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
    (hC : ∀ E, (CombData.ofSys (st := moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      (preOf E) (midOf E) (moussakaRedeemSysL anchors nf ctxIss ctxRed)
      (moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed)) (accOf E) (toBA (VoleMole.Spec.makeDst "mous" 0 'l' '0'))).Committed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q)
    (chainFail deadFail : CTable → Out (β × QueryLog specIC) → Prop) {εd εs : ℝ≥0∞}
    (hdead : ∀ E, Pr{let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P E)).run' ∅}[deadFail E r] ≤ εd)
    (hchain : ∀ E, Pr{let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P E)).run' ∅}[chainFail E r] ≤ εs)
    (hsame : ∀ (E : CTable) (g : Table), let _ : HasPrg := icPrg E.cipher
      let st := moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC CrtGen.tables st P E)
      r.2.2.accept = true → ¬chainFail E r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      let ch := runChain (Hashes.ofTable g) CrtGen.tables st r.1 leaves r.2.1.keys
      SameChain st CrtGen.tables (preOf E) (midOf E) (accOf E) g ch
        (runX (Hashes.ofTable g) st r.1 leaves) (runY (Hashes.ofTable g) st ch) (runZ st ch))
    (hL2 : ∀ (E : CTable) (g : Table), let _ : HasPrg := icPrg E.cipher
      let st := moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC CrtGen.tables st P E)
      r.2.2.accept = true → ¬chainFail E r → ¬deadFail E r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      ∀ i ∉ r.2.1.known, IsFixed ((onSet st CrtGen.tables (runChain (Hashes.ofTable g)
        CrtGen.tables st r.1 leaves r.2.1.keys) chal3Blocks : Finset Blocks) : Set Blocks) i) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
          (fun _ => moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
            (fnOf ctxIss) (fnOf ctxRed)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) + εd + εs := by
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128)
  refine (prEvent_joint_le_explicit CrtGen.tables _ P qE hqE q hq _ (A + εd + εs) fun E => ?_).trans
    (le_of_eq (by ring))
  have h := @moussakaRedeem_accept_le (icPrg E.cipher) _ anchors hn64 nf ctxIss ctxRed challengeDigest labelRows (preOf E)
    (midOf E) (accOf E) (hC E) (proverIC (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) E P) (n + 2)
    (isTotalQueryBound_proverIC _ E hn)
    (q + extractorQueries) (isKindQueryBound_proverIC _ E hq) (chainFail E) (deadFail E) _ _ _
    le_rfl (hdead E) (hchain E) (hsame E) (hL2 E)
  simp only [gameIC]
  refine h.trans (le_of_eq ?_)
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
    (hC : ∀ E, (CombData.ofSys (st := ratatouilleSpend pk nf d cNext ctxIss labelRows)
      (preOf E) (midOf E) (ratatouilleSpendSysL pk nf d cNext ctxIss)
      (ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss)) (accOf E)
      (toBA (VoleMole.Spec.makeDst "rata" 0 'l' '0'))).Committed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q)
    (chainFail deadFail : CTable → Out (β × QueryLog specIC) → Prop) {εd εs : ℝ≥0∞}
    (hdead : ∀ E, Pr{let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) P E)).run' ∅}[deadFail E r] ≤ εd)
    (hchain : ∀ E, Pr{let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) P E)).run' ∅}[chainFail E r] ≤ εs)
    (hsame : ∀ (E : CTable) (g : Table), let _ : HasPrg := icPrg E.cipher
      let st := ratatouilleSpend pk nf d cNext ctxIss labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC CrtGen.tables st P E)
      r.2.2.accept = true → ¬chainFail E r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      let ch := runChain (Hashes.ofTable g) CrtGen.tables st r.1 leaves r.2.1.keys
      SameChain st CrtGen.tables (preOf E) (midOf E) (accOf E) g ch
        (runX (Hashes.ofTable g) st r.1 leaves) (runY (Hashes.ofTable g) st ch) (runZ st ch))
    (hL2 : ∀ (E : CTable) (g : Table), let _ : HasPrg := icPrg E.cipher
      let st := ratatouilleSpend pk nf d cNext ctxIss labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC CrtGen.tables st P E)
      r.2.2.accept = true → ¬chainFail E r → ¬deadFail E r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      ∀ i ∉ r.2.1.known, IsFixed ((onSet st CrtGen.tables (runChain (Hashes.ofTable g)
        CrtGen.tables st r.1 leaves r.2.1.keys) chal3Blocks : Finset Blocks) : Set Blocks) i) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (ratatouilleSpend pk nf d cNext ctxIss labelRows)
          (fun _ => ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext)
            (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) + εd + εs := by
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128)
  refine (prEvent_joint_le_explicit CrtGen.tables _ P qE hqE q hq _ (A + εd + εs) fun E => ?_).trans
    (le_of_eq (by ring))
  have h := @ratatouilleSpend_accept_le (icPrg E.cipher) _ pk nf d hd cNext ctxIss labelRows (preOf E)
    (midOf E) (accOf E) (hC E) (proverIC (ratatouilleSpend pk nf d cNext ctxIss labelRows) E P) (n + 2)
    (isTotalQueryBound_proverIC _ E hn)
    (q + extractorQueries) (isKindQueryBound_proverIC _ E hq) (chainFail E) (deadFail E) _ _ _
    le_rfl (hdead E) (hchain E) (hsame E) (hL2 E)
  simp only [gameIC]
  refine h.trans (le_of_eq ?_)
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
    (hC : ∀ E, (pomfritData pk sig msg labelRows (preOf E) (midOf E) (accOf E)).Committed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q)
    (chainFail deadFail : CTable → Out (β × QueryLog specIC) → Prop) {εd εs : ℝ≥0∞}
    (hdead : ∀ E, Pr{let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (pomfritRedeem pk sig msg labelRows) P E)).run' ∅}[deadFail E r] ≤ εd)
    (hchain : ∀ E, Pr{let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (pomfritRedeem pk sig msg labelRows) P E)).run' ∅}[chainFail E r] ≤ εs)
    (hsame : ∀ (E : CTable) (g : Table), let _ : HasPrg := icPrg E.cipher
      let st := pomfritRedeem pk sig msg labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC CrtGen.tables st P E)
      r.2.2.accept = true → ¬chainFail E r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      let ch := runChain (Hashes.ofTable g) CrtGen.tables st r.1 leaves r.2.1.keys
      SameChain st CrtGen.tables (preOf E) (midOf E) (accOf E) g ch
        (runX (Hashes.ofTable g) st r.1 leaves) (runY (Hashes.ofTable g) st ch) (runZ st ch))
    (hL2 : ∀ (E : CTable) (g : Table), let _ : HasPrg := icPrg E.cipher
      let st := pomfritRedeem pk sig msg labelRows
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC CrtGen.tables st P E)
      r.2.2.accept = true → ¬chainFail E r → ¬deadFail E r → ∀ leaves, BAVC.reconstruct r.2.2.iv
        (Proof.opening ⟨st.params, r.1⟩) (Proof.delta ⟨st.params, r.1⟩) = some leaves →
      ∀ i ∉ r.2.1.known, IsFixed ((onSet st CrtGen.tables (runChain (Hashes.ofTable g)
        CrtGen.tables st r.1 leaves r.2.1.keys) chal3Blocks : Finset Blocks) : Set Blocks) i) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (pomfritRedeem pk sig msg labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (pomfritRedeem pk sig msg labelRows)
          (fun c1 => pomfritWit GF256.ofBits 119 45 pk.map
            (fun k => ⟨fnOf (pomfritTarget (pomfritParams labelRows) pk.digest c1 sig msg) k.val⟩)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) + εd + εs := by
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128)
  refine (prEvent_joint_le_explicit CrtGen.tables _ P qE hqE q hq _ (A + εd + εs) fun E => ?_).trans
    (le_of_eq (by ring))
  have h := @pomfritRedeem_accept_le (icPrg E.cipher) _ pk sig msg labelRows (preOf E)
    (midOf E) (accOf E) (hC E) (proverIC (pomfritRedeem pk sig msg labelRows) E P) (n + 2)
    (isTotalQueryBound_proverIC _ E hn)
    (q + extractorQueries) (isKindQueryBound_proverIC _ E hq) (chainFail E) (deadFail E) _ _ _
    le_rfl (hdead E) (hchain E) (hsame E) (hL2 E)
  simp only [gameIC]
  refine h.trans (le_of_eq ?_)
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero]
  ring

end VoleMole.ROM.IC
