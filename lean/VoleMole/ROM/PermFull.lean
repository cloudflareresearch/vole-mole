import VoleMole.ROM.PermPost
import VoleMole.ROM.CipherFull

/-!
# Soundness of the five relations with the ideal cipher as random permutations (plan M6)

The bounds of `ROM/CipherFull.lean` (`*_accept_le_full`, PRF view, forward queries) in the model
of `L0-L2-commitments.md` §3.1: the cipher is a uniformly random permutation per key (`PTable`),
the prover makes **forward and inverse** queries (`specP`), and the straight-line extractor reads
the forward-and-inverse records `(k, z, π_k(z))` of its queries (`normP`, `gameP`). For a prover
`P` with at most `q_E` cipher queries (forward or inverse), `q k` hash queries of kind `k` (total
`n` for the combined relations), and `p = 1/(2¹²⁸ − q_E)`, `p' = 1/(2¹²⁸ − q_E − 4607)`:

    Pr[accept ∧ ¬Extracted] ≤ (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε₂ + (q₂₃+1)·N·2⁻¹²⁸
      + 2·q_E²·p² + 2·(openHashEps q + q₁·p'²) + q_E·4608·q₂₁·p² + chainHitEps q [+ comb],

with `ε₂`, `N`, `openHashEps`, `chainHitEps` as in `ROM/CipherFull.lean`, except that for the
combined relations the total hash count in `ε₂` is `n + q₂₁` (the normalized prover's `H₄` query
per `H₂¹` query, `L0-L2` N1). Compared with the PRF view: `2⁻¹²⁸` per fresh cipher value becomes
`p` (or `p'`, where the verifier's `2·2303` GGM points must keep their values), and Post
(`1024·q_E·q₁·2⁻²⁵⁶`) becomes the point-tied `q_E·4608·q₂₁·p²` (`ROM/PermPost.lean`; the
unrestricted Post fails against inverse queries). No PRP/PRF switching term enters.

* `prEvent_jointP_le_explicit`: from a per-permutation-table bound with the game's own failure
  probabilities (binding, opened dead leaf, Post) to the joint experiment.
* `sameChainHyp_icP`, `deadHiddenHyp_icP`, `combFreshHyp_icP`: the identification hypotheses of
  `ROM/Accept.lean` for the normalized prover, with `chainFail := PostPOut`.
* **`moussakaIssue_accept_le_perm`, `ratatouilleIssue_accept_le_perm`,
  `moussakaRedeem_accept_le_perm`, `ratatouilleSpend_accept_le_perm`,
  `pomfritRedeem_accept_le_perm`** (fixed statement).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

variable {β : Type}

/-! ## The joint failure probabilities -/

/-- **Post (point-tied) in the joint experiment**: `≤ q_E·4608·q₂₁·p²`. -/
theorem prEvent_jointP_postP_le (T : CrtTables) (st : Statement)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameP T st P π)).run' ∅}[
        PostPOut st.params π.fwd r] ≤ qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
  have h := prEvent_jointP_le_add (gameP T st P) (fun π r => PostPOut st.params π.fwd r)
    (fun _ _ => False) (qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2) fun g => by
      refine le_trans ?_ le_self_add
      simp only [PostPOut, gameP, gameIC_aux]
      exact prEvent_perm_postP_le st.params g P qE hqE q hq
  rwa [prEvent_jointP_false, add_zero] at h

/-- **From per-permutation-table bounds to the joint experiment, every cipher term explicit.** -/
theorem prEvent_jointP_le_explicit (T : CrtTables) (st : Statement)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) (ev : PTable → Out (β × QueryLog specIC) → Prop) (c : ℝ≥0∞)
    (h : ∀ π, Pr{let r ← (simulateQ randomOracle (gameP T st P π)).run' ∅}[ev π r] ≤
      c + Pr{let r ← (simulateQ randomOracle (gameP T st P π)).run' ∅}[
          @bindFail (icPrg π.fwd.cipher) _ st r] +
        Pr{let r ← (simulateQ randomOracle (gameP T st P π)).run' ∅}[DeadOpenOut st π.fwd r] +
        Pr{let r ← (simulateQ randomOracle (gameP T st P π)).run' ∅}[
          PostPOut st.params π.fwd r]) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameP T st P π)).run' ∅}[ev π r] ≤
      c + (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 :=
  (prEvent_avgP_le_add3 _ _ _ _ _ c h).trans
    (add_le_add (add_le_add (add_le_add le_rfl ((prEvent_jointP_bindFail_le T st P qE hqE).trans
      (add_le_add le_rfl (prEvent_jointP_deadOpen_le st P T qE hqE q hq))))
      (prEvent_jointP_deadOpen_le st P T qE hqE q hq)) (prEvent_jointP_postP_le T st P qE hqE q hq))

/-! ## The identification hypotheses for the normalized prover -/

section Hyp

variable (T : CrtTables) (st : Statement) (P : OracleComp specP (ByteArray × β)) (π : PTable)

lemma not_postP_of_out (g : Table)
    (h : ¬PostPOut st.params π.fwd
      (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st (Wn st P π) π.fwd))) :
    ¬PostP st.params π.fwd (jOf g (Wn st P π) π.fwd) := by
  unfold PostPOut at h
  rwa [gameIC_aux] at h

/-- `hsame` for the normalized prover, outside the point-tied Post. -/
theorem sameChainHyp_icP : @SameChainHyp (icPrg π.fwd.cipher) (β × QueryLog specIC) T st
    (proverIC st π.fwd (Wn st P π)) (preOf T st (Wn st P π) π.fwd)
    (midOf T st (Wn st P π) π.fwd) (accOf T st (Wn st P π) π.fwd)
    (deadOf T st (Wn st P π) π.fwd) (chainHit T st (Wn st P π) π.fwd)
    (PostPOut st.params π.fwd) :=
  sameChainHyp_ic_of T st _ π.fwd _ fun g h =>
    keysPre_of_not_postP T st P π g (not_postP_of_out T st P π g h)

/-- `hL2` for the normalized prover, outside the point-tied Post and an opened dead leaf. -/
theorem deadHiddenHyp_icP : @DeadHiddenHyp (icPrg π.fwd.cipher) (β × QueryLog specIC) T st
    (proverIC st π.fwd (Wn st P π)) (deadOf T st (Wn st P π) π.fwd)
    (chainHit T st (Wn st P π) π.fwd) (PostPOut st.params π.fwd) (DeadOpenOut st π.fwd) :=
  deadHiddenHyp_ic_of T st _ π.fwd _ fun g h =>
    keysPre_of_not_postP T st P π g (not_postP_of_out T st P π g h)

end Hyp

/-- The hit terms read no `H₄` count. -/
lemma hitSum_hitEps_congr (q q' : Kind → ℕ) (h : ∀ k, k ≠ .h4 → q' k = q k)
    (cb : Option (ℕ × ByteArray)) :
    hitSum (q' + verifierQueries) (hitEps (q' + extractorQueries + verifierQueries)
      (combCount cb (q' + extractorQueries + verifierQueries))) =
    hitSum (q + verifierQueries) (hitEps (q + extractorQueries + verifierQueries)
      (combCount cb (q + extractorQueries + verifierQueries))) := by
  have hc : combCount cb (q' + extractorQueries + verifierQueries) =
      combCount cb (q + extractorQueries + verifierQueries) := by
    rcases cb with _ | ⟨M, d⟩
    · rfl
    · simp only [combCount, Pi.add_apply, h (.comb M) (by simp)]
  rw [hc]
  simp only [hitSum, hitEps, Pi.add_apply, h .h1 (by decide), h .h21 (by decide),
    h .h22 (by decide), h .h23 (by decide)]

lemma hitSum_hitEps_perm (q : Kind → ℕ) {cb : Option (ℕ × ByteArray)} (hcb : cb = none) :
    hitSum (addH4 q + verifierQueries) (hitEps (addH4 q + extractorQueries + verifierQueries)
      (combCount cb (addH4 q + extractorQueries + verifierQueries))) = chainHitEps q := by
  subst hcb
  exact (hitSum_hitEps_congr q (addH4 q) (fun _ hk => addH4_of_ne q hk) none).trans
    (hitSum_hitEps q)

lemma hitSum_hitEps_comb_perm (q : Kind → ℕ) (M : ℕ) {cb : Option (ℕ × ByteArray)}
    {dst : ByteArray} (hcb : cb = some (M, dst)) :
    hitSum (addH4 q + verifierQueries) (hitEps (addH4 q + extractorQueries + verifierQueries)
      (combCount cb (addH4 q + extractorQueries + verifierQueries))) = chainHitEpsComb q M :=
  (hitSum_hitEps_congr q (addH4 q) (fun _ hk => addH4_of_ne q hk) cb).trans
    (hitSum_hitEps_comb q M hcb)

/-! ## The issue relations -/

/-- **Moussaka issuance with the ideal cipher as random permutations (forward and inverse
queries)**: the permutation table drawn uniformly, the prover `P` (at most `q_E` cipher queries,
forward or inverse, and `q k` hash queries of each kind `k`), the normalized prover and the
straight-line extractor reading its records, the executable verifier with the ideal cipher; the
verifier accepts and the extractor's candidate is not an issuance witness with probability

    ≤ (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε_QS(4008) + (q₂₃+1)·9·2⁻¹²⁸ + 2·q_E²·p²
      + 2·(openHashEps q + q₁·p'²) + q_E·4608·q₂₁·p² + chainHitEps q,

`p = 1/(2¹²⁸ − q_E)`, `p' = 1/(2¹²⁸ − q_E − 4607)`. -/
theorem moussakaIssue_accept_le_perm (t ctxIss : ByteArray) (labelRows : Bool)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameP CrtGen.tables (moussakaIssue t ctxIss labelRows) P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (moussakaIssue t ctxIss labelRows)
          (fun _ => moussakaIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEps q := by
  set st := moussakaIssue t ctxIss labelRows
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEps q
  refine (prEvent_jointP_le_explicit CrtGen.tables st P qE hqE q hq _ A fun π => ?_).trans
    (le_of_eq (by simp only [A]; ring))
  have hqW := isKindQueryBound_normP st.params π hq
  have h := @moussakaIssue_accept_le (icPrg π.fwd.cipher) _ t ctxIss labelRows
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
  rw [hitSum_add_extractorQueries, hitSum_hitEps_perm q (cb := st.comb) rfl]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  ring

/-- **Ratatouille issuance with the ideal cipher as random permutations** (as
`moussakaIssue_accept_le_perm`, with `ε_QS(3776)`). -/
theorem ratatouilleIssue_accept_le_perm (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray)
    (labelRows : Bool) (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameP CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (ratatouilleIssue c tInit ctxIss labelRows)
          (fun _ => ratatouilleIssueWit (fnOf c) tInit (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEps q := by
  set st := ratatouilleIssue c tInit ctxIss labelRows
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEps q
  refine (prEvent_jointP_le_explicit CrtGen.tables st P qE hqE q hq _ A fun π => ?_).trans
    (le_of_eq (by simp only [A]; ring))
  have hqW := isKindQueryBound_normP st.params π hq
  have h := @ratatouilleIssue_accept_le (icPrg π.fwd.cipher) _ c tInit ctxIss labelRows
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
  rw [hitSum_add_extractorQueries, hitSum_hitEps_perm q (cb := st.comb) rfl]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  ring

/-! ## The combined relations -/

/-- `hcombFresh` for the normalized prover (it does not use the failure event). -/
theorem combFreshHyp_icP (T : CrtTables) (st : Statement) (P : OracleComp specP (ByteArray × β))
    (π : PTable) {M : ℕ} {dst : ByteArray} (hcomb : st.comb = some (M, dst)) (C : CombData st M)
    (hpre : C.pre = preCells T st (Wn st P π) π.fwd) (hdst : C.dst = dst) :
    @CombFreshHyp (icPrg π.fwd.cipher) (β × QueryLog specIC) M T st C
      (proverIC st π.fwd (Wn st P π)) (chainHit T st (Wn st P π) π.fwd)
      (PostPOut st.params π.fwd) :=
  combFreshHyp_ic_of T st _ π.fwd hcomb C hpre hdst _

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Moussaka redemption with the ideal cipher as random permutations** (as
`moussakaIssue_accept_le_perm`, with the combination terms; `n` is `P`'s total hash-query count,
which the normalized prover raises by one `H₄` query per `H₂¹` query). -/
theorem moussakaRedeem_accept_le_perm (anchors : List UovPk) (hn64 : anchors.length ≤ 64)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameP CrtGen.tables
      (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
          (fun _ => moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
            (fnOf ctxIss) (fnOf ctxRed)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q Moussaka.M := by
  set st := moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q Moussaka.M
  refine (prEvent_jointP_le_explicit CrtGen.tables st P qE hqE q hq _ A fun π => ?_).trans
    (le_of_eq (by simp only [A]; ring))
  have hqW := isKindQueryBound_normP st.params π hq
  have hnW := isQueryBoundP_left_normP st.params π hn hq
  have h := @moussakaRedeem_accept_le (icPrg π.fwd.cipher) _ anchors hn64 nf ctxIss ctxRed
    challengeDigest labelRows
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
    (combFreshHyp_icP CrtGen.tables st P π rfl _ rfl rfl)
  simp only [gameP, gameIC]
  refine h.trans (le_of_eq ?_)
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb_perm q Moussaka.M (cb := st.comb) rfl]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  ring

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Ratatouille spend with the ideal cipher as random permutations** (as
`moussakaRedeem_accept_le_perm`). -/
theorem ratatouilleSpend_accept_le_perm (pk : UovPk) (nf : ByteArray) (d : ℕ) (hd : d < 2 ^ 64)
    (cNext ctxIss : ByteArray) (labelRows : Bool)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameP CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (ratatouilleSpend pk nf d cNext ctxIss labelRows)
          (fun _ => ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext)
            (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q Ratatouille.uovM := by
  set st := ratatouilleSpend pk nf d cNext ctxIss labelRows
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q Ratatouille.uovM
  refine (prEvent_jointP_le_explicit CrtGen.tables st P qE hqE q hq _ A fun π => ?_).trans
    (le_of_eq (by simp only [A]; ring))
  have hqW := isKindQueryBound_normP st.params π hq
  have hnW := isQueryBoundP_left_normP st.params π hn hq
  have h := @ratatouilleSpend_accept_le (icPrg π.fwd.cipher) _ pk nf d hd cNext ctxIss labelRows
    (preOf CrtGen.tables st (Wn st P π) π.fwd) (midOf CrtGen.tables st (Wn st P π) π.fwd)
    (accOf CrtGen.tables st (Wn st P π) π.fwd) (preCells CrtGen.tables st (Wn st P π) π.fwd)
    (CombData.ofSys_committed _ _ _ _ _ _ _ (preOf_committed CrtGen.tables _ _ π.fwd)
      (accOf_committed CrtGen.tables _ _ π.fwd) (midOf_committed CrtGen.tables _ _ π.fwd)
      (fun y g x v hx => midOf_comb CrtGen.tables _ _ π.fwd Ratatouille.uovM y g x v hx)
      (preCells_mid CrtGen.tables _ _ π.fwd)
      (fun y g x v h => preCells_comb CrtGen.tables _ _ π.fwd Ratatouille.uovM y g x v h))
    (proverIC st π.fwd (Wn st P π)) (n + q .h21 + 2) (isTotalQueryBound_proverIC _ π.fwd hnW)
    (addH4 q + extractorQueries) (isKindQueryBound_proverIC _ π.fwd hqW)
    (PostPOut st.params π.fwd) (DeadOpenOut st π.fwd) _ _ _ le_rfl le_rfl le_rfl
    (deadOf CrtGen.tables st (Wn st P π) π.fwd) (chainHit CrtGen.tables st (Wn st P π) π.fwd) _
    (hitEps_eq_zero _ _)
    (prEvent_chainHit_le CrtGen.tables st (Wn st P π) π.fwd _
      (isKindQueryBound_gameIC _ st _ π.fwd hqW))
    (sameChainHyp_icP CrtGen.tables st P π) (deadHiddenHyp_icP CrtGen.tables st P π)
    (combFreshHyp_icP CrtGen.tables st P π rfl _ rfl rfl)
  simp only [gameP, gameIC]
  refine h.trans (le_of_eq ?_)
  rw [hitSum_add_extractorQueries,
    hitSum_hitEps_comb_perm q Ratatouille.uovM (cb := st.comb) rfl]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  ring

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **PomFRIT redemption with the ideal cipher as random permutations** (as
`moussakaRedeem_accept_le_perm`, with `N = 2`). -/
theorem pomfritRedeem_accept_le_perm (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool)
    (P : OracleComp specP (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameP CrtGen.tables (pomfritRedeem pk sig msg labelRows) P π)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (pomfritRedeem pk sig msg labelRows)
          (fun c1 => pomfritWit GF256.ofBits 119 45 pk.map
            (fun k => ⟨fnOf (pomfritTarget (pomfritParams labelRows) pk.digest c1 sig msg) k.val⟩))
          r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q 45 := by
  set st := pomfritRedeem pk sig msg labelRows
  set A : ℝ≥0∞ := (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q 45
  refine (prEvent_jointP_le_explicit CrtGen.tables st P qE hqE q hq _ A fun π => ?_).trans
    (le_of_eq (by simp only [A]; ring))
  have hqW := isKindQueryBound_normP st.params π hq
  have hnW := isQueryBoundP_left_normP st.params π hn hq
  have h := @pomfritRedeem_accept_le (icPrg π.fwd.cipher) _ pk sig msg labelRows
    (preOf CrtGen.tables st (Wn st P π) π.fwd) (midOf CrtGen.tables st (Wn st P π) π.fwd)
    (accOf CrtGen.tables st (Wn st P π) π.fwd) (preCells CrtGen.tables st (Wn st P π) π.fwd)
    (pomfritData_committed _ _ _ _ _ _ _ _ (preOf_committed CrtGen.tables _ _ π.fwd)
      (accOf_committed CrtGen.tables _ _ π.fwd) (midOf_committed CrtGen.tables _ _ π.fwd)
      (fun y g x v hx => midOf_comb CrtGen.tables _ _ π.fwd 45 y g x v hx)
      (preCells_mid CrtGen.tables _ _ π.fwd)
      (fun y g x v h => preCells_comb CrtGen.tables _ _ π.fwd 45 y g x v h))
    (proverIC st π.fwd (Wn st P π)) (n + q .h21 + 2) (isTotalQueryBound_proverIC _ π.fwd hnW)
    (addH4 q + extractorQueries) (isKindQueryBound_proverIC _ π.fwd hqW)
    (PostPOut st.params π.fwd) (DeadOpenOut st π.fwd) _ _ _ le_rfl le_rfl le_rfl
    (deadOf CrtGen.tables st (Wn st P π) π.fwd) (chainHit CrtGen.tables st (Wn st P π) π.fwd) _
    (hitEps_eq_zero _ _)
    (prEvent_chainHit_le CrtGen.tables st (Wn st P π) π.fwd _
      (isKindQueryBound_gameIC _ st _ π.fwd hqW))
    (sameChainHyp_icP CrtGen.tables st P π) (deadHiddenHyp_icP CrtGen.tables st P π)
    (combFreshHyp_icP CrtGen.tables st P π rfl _ rfl rfl)
  simp only [gameP, gameIC]
  refine h.trans (le_of_eq ?_)
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb_perm q 45 (cb := st.comb) rfl]
  simp only [Pi.add_apply, extractorQueries, A, reduceCtorEq, or_self, ite_false, add_zero,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  ring

end VoleMole.ROM.IC
