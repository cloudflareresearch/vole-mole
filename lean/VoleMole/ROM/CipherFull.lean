import VoleMole.ROM.CipherSame

/-!
# The issue relations in the random-oracle and ideal-cipher model, every term explicit (plan M6)

`ROM/CipherOpen.lean` (`moussakaIssue_accept_le_ic'`) and `ROM/CipherRelations.lean` bound
`Pr[accept ∧ ¬Extracted]` in the joint hash and ideal-cipher experiment with binding explicit and
the "same chain" step and L2 as hypotheses (`hsame`, `hL2`, with their failure events `chainFail`,
`deadFail` and hits). `ROM/CipherChain.lean` and `ROM/CipherSame.lean` discharge those hypotheses:

* chain data `preOf`, `midOf`, `accOf`, `deadOf` read off the logs (committed:
  `chainData_committed`);
* hits `chainHit`, each `≤ hitEps n` when its cell is resampled (`prEvent_chainHit_le`);
* `chainFail := PostOut` (`Pr ≤ 1024·q_E·q₁·2⁻²⁵⁶`, `prEvent_joint_postOut_le`) and
  `deadFail := DeadOpenOut` (`≤ openHashEps q + q₁·2⁻²⁵⁶`, `prEvent_joint_deadOpen_le`);
* `hsame` (`sameChainHyp_ic`) and `hL2` (`deadHiddenHyp_ic`).

So for every relation the extraction failure is bounded by an explicit function of the prover's
query counts (`q_E` cipher queries, `q k` hash queries of kind `k`, and for the combined relations
the total `n` of hash queries) alone. For the issue relations (`moussakaIssue_accept_le_full`,
`ratatouilleIssue_accept_le_full`):

    Pr[accept ∧ ¬Extracted] ≤ (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε_QS(n') + (q₂₃+1)·9·2⁻¹²⁸
      + 2·q_E²·2⁻²⁵⁶ + 2·(openHashEps q + q₁·2⁻²⁵⁶) + 1024·q_E·q₁·2⁻²⁵⁶ + chainHitEps q,

with `chainHitEps q = (q₁+18)·(18q₁+q₂₁+325)·2⁻²⁵⁶ + (q₂₁+1)·(q₂₁+q₂₂+2)·2⁻¹⁰⁸⁸
+ (q₂₂+1)·(q₂₂+q₂₃+2)·2⁻⁴⁴⁸` (the hits of the identification, `L0-L2` L1.4 ordering, `Coll₁`
and the `H₂¹`, `H₂²` collisions). For `q ≤ 2⁶⁴` every term but `ε_QS` and the `2⁻¹²⁸`, `2⁻¹⁵⁰`
ones is `O(2⁻¹²⁰)`.

For the combined relations (`moussakaRedeem_accept_le_full`, `ratatouilleSpend_accept_le_full`,
`pomfritRedeem_accept_le_full`) the bound of `ROM/CipherRelations.lean` with the same explicit
terms, and `chainHitEpsComb q M = chainHitEps q + (q₂₂+1)·(q_comb+1)·2⁻⁴⁴⁸`: a combination input
`chal2 ‖ dst` queried before the `H₂²` input whose answer is `chal2` is also a hit, which makes the
verifier's combination cell fresh for the chain data (`combFreshHyp_ic`), whose dependence on the
combination cells is confined to the log before `y` (`CombData.pre := preCells`, `midOf_comb`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-- The probability of the identification's hits, for a prover with `q k` hash queries of kind `k`
(the game adds the verifier's queries). -/
noncomputable def chainHitEps (q : Kind → ℕ) : ℝ≥0∞ :=
  (q .h1 + 18) * (((18 * (q .h1 + 18) + (q .h21 + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    (q .h21 + 1) * (((q .h22 + 1 + (q .h21 + 1) : ℕ) : ℝ≥0∞) / 2 ^ 1088) +
    (q .h22 + 1) * (((q .h23 + 1 + (q .h22 + 1) : ℕ) : ℝ≥0∞) / 2 ^ 448)

lemma hitSum_hitEps (q : Kind → ℕ) :
    hitSum (q + verifierQueries) (hitEps (q + extractorQueries + verifierQueries)
      (combCount none (q + extractorQueries + verifierQueries))) = chainHitEps q := by
  simp [hitSum, hitEps, chainHitEps, extractorQueries, verifierQueries, combCount]

variable {β : Type}

/-- The game's hash queries per kind. -/
lemma isKindQueryBound_gameIC (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β))
    (E : CTable) {q : Kind → ℕ} (hq : IsKindQueryBoundIC P q) :
    IsKindQueryBound (gameIC T st P E) (q + extractorQueries + verifierQueries) :=
  @isKindQueryBound_game (icPrg E.cipher) _ T st _ _ (isKindQueryBound_proverIC st E hq)

/-- **Moussaka issuance in the random-oracle and ideal-cipher model, every term explicit**: the
cipher table drawn uniformly, the prover `P` (at most `q_E` cipher queries and `q k` hash queries
of each kind `k`) with the straight-line extractor of `proverIC`, the executable verifier with the
ideal cipher; the verifier accepts and the extractor's candidate is not an issuance witness with
probability

    ≤ (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε_QS(4008) + (q₂₃+1)·9·2⁻¹²⁸ + 2·q_E²·2⁻²⁵⁶
      + 2·(openHashEps q + q₁·2⁻²⁵⁶) + 1024·q_E·q₁·2⁻²⁵⁶ + chainHitEps q.

No assumption is left: `moussakaIssue_accept_le_ic'` with the chain data, hits and failure events of
`ROM/CipherChain.lean`, `ROM/CipherSame.lean`. -/
theorem moussakaIssue_accept_le_full (t ctxIss : ByteArray) (labelRows : Bool)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaIssue t ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (moussakaIssue t ctxIss labelRows)
          (fun _ => moussakaIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEps q := by
  set st := moussakaIssue t ctxIss labelRows
  rw [← hitSum_hitEps]
  exact moussakaIssue_accept_le_ic' t ctxIss labelRows (preOf CrtGen.tables st P)
    (midOf CrtGen.tables st P) (accOf CrtGen.tables st P)
    (fun E => chainData_committed CrtGen.tables st P E _) P qE hqE q hq (fun E r => PostOut E r)
    (fun E r => DeadOpenOut st E r) (prEvent_joint_deadOpen_le CrtGen.tables st P q hq)
    (prEvent_joint_postOut_le P CrtGen.tables st qE hqE q hq) (deadOf CrtGen.tables st P)
    (chainHit CrtGen.tables st P) _ (hitEps_eq_zero _ _)
    (fun E => prEvent_chainHit_le CrtGen.tables st P E _ (isKindQueryBound_gameIC _ st P E hq))
    (sameChainHyp_ic CrtGen.tables st P) (deadHiddenHyp_ic CrtGen.tables st P)

/-- **Ratatouille issuance in the random-oracle and ideal-cipher model, every term explicit**
(as `moussakaIssue_accept_le_full`, with `ε_QS(3776)`). -/
theorem ratatouilleIssue_accept_le_full (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray)
    (labelRows : Bool) (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleIssue c tInit ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (ratatouilleIssue c tInit ctxIss labelRows)
          (fun _ => ratatouilleIssueWit (fnOf c) tInit (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEps q := by
  set st := ratatouilleIssue c tInit ctxIss labelRows
  rw [← hitSum_hitEps]
  exact ratatouilleIssue_accept_le_ic c tInit ctxIss labelRows (preOf CrtGen.tables st P)
    (midOf CrtGen.tables st P) (accOf CrtGen.tables st P)
    (fun E => chainData_committed CrtGen.tables st P E _) P qE hqE q hq (fun E r => PostOut E r)
    (fun E r => DeadOpenOut st E r) (prEvent_joint_deadOpen_le CrtGen.tables st P q hq)
    (prEvent_joint_postOut_le P CrtGen.tables st qE hqE q hq) (deadOf CrtGen.tables st P)
    (chainHit CrtGen.tables st P) _ (hitEps_eq_zero _ _)
    (fun E => prEvent_chainHit_le CrtGen.tables st P E _ (isKindQueryBound_gameIC _ st P E hq))
    (sameChainHyp_ic CrtGen.tables st P) (deadHiddenHyp_ic CrtGen.tables st P)

/-! ## The combined relations -/

section Comb

variable (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β)) (E : CTable)

/-- **The cells the data at an `H₂²` input `y` read**: the game's log before `y`. -/
def preCells (y : ByteArray) (g : Table) : List Dom :=
  (logBefore (.h22, y) (gLog T st P E g)).map Sigma.fst

lemma takeWhile_append_of_forall {γ : Type} {p : γ → Bool} {A : List γ} (B : List γ)
    (h : ∀ a ∈ A, p a = true) : (A ++ B).takeWhile p = A ++ B.takeWhile p := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    rw [List.cons_append, List.takeWhile_cons, ite_eq_left (h a List.mem_cons_self),
      ih fun a' ha' => h a' (List.mem_cons_of_mem _ ha'), List.cons_append]

/-- A cell outside the game's log before `b` is outside `P`'s joint log before `b`. -/
lemma not_mem_jPre (g : Table) {b d : Dom}
    (hd : d ∉ (logBefore b (gLog T st P E g)).map Sigma.fst) :
    (.inl d : DomIC) ∉ (logBefore (.inl b) (jOf g P E)).map Sigma.fst := by
  intro hmem
  by_cases hb : (.inl b : DomIC) ∈ (jOf g P E).map Sigma.fst
  · rw [map_fst_logBefore_gLog_of_mem T st P E g hb] at hd
    exact hd (mem_hashLog.2 hmem)
  · rw [logBefore_eq_of_not_mem hb] at hmem
    obtain ⟨R, hR⟩ := map_fst_gLog T st P E g
    apply hd
    rw [map_fst_logBefore, hR, takeWhile_append_of_forall _ fun a ha => ?_]
    · exact List.mem_append_left _ (mem_hashLog.2 hmem)
    · have : a ≠ b := fun h => hb (h ▸ mem_hashLog.1 ha)
      simp [this]

/-- **The data at `y` do not read the combination cells outside the log before `y`.** -/
theorem midOf_comb (M : ℕ) (y : ByteArray) (g : Table) (x : ByteArray) (v : Ans (.comb M, x))
    (hx : ((.comb M, x) : Dom) ∉ preCells T st P E y g) :
    midOf T st P E y (Function.update g (.comb M, x) v) = midOf T st P E y g := by
  unfold midOf
  have h1 : logBefore (.h22, y) (gLog T st P E (Function.update g (.comb M, x) v)) =
      logBefore (.h22, y) (gLog T st P E g) :=
    logBefore_tableQueryLog_congr_of_not_mem _ g _ (fun t ht => Function.update_of_ne ht _ _) hx
  have h2 : logBefore (.inl (.h22, y)) (jOf (Function.update g (.comb M, x) v) P E) =
      logBefore (.inl (.h22, y)) (jOf g P E) :=
    logBefore_tableQueryLog_congr_of_not_mem P (join g E) _
      (fun t ht => join_update_inl_of_ne g E _ v ht) (not_mem_jPre T st P E g hx)
  rw [h1, h2]
  exact midCore_update st E _ _ _ g _ v (midKind_comb M)

lemma preCells_mid (y : ByteArray) (g : Table) (u : Ans (.h22, y)) :
    preCells T st P E y (Function.update g (.h22, y) u) = preCells T st P E y g := by
  unfold preCells; rw [logBefore_gLog_update]

lemma preCells_comb (M : ℕ) (y : ByteArray) (g : Table) (x : ByteArray) (v : Ans (.comb M, x))
    (h : ((.comb M, x) : Dom) ∈ preCells T st P E y g) :
    ((.comb M, x) : Dom) ∈ preCells T st P E y (Function.update g (.comb M, x) v) :=
  mem_logBefore_tableQueryLog_update _ g v h

/-- **The combination cell of the accepted chain is fresh, without hits** (`CombFreshHyp` for the
joint game): a combination input `chal2 ‖ dst` queried before the verifier's `H₂²` input `y` would
make the `H₂²` answer at `y` a hit. -/
theorem combFreshHyp_ic {M : ℕ} {dst : ByteArray} (hcomb : st.comb = some (M, dst))
    (C : CombData st M) (hpre : C.pre = preCells T st P E) (hdst : C.dst = dst) :
    @CombFreshHyp (icPrg E.cipher) (β × QueryLog specIC) M T st C (proverIC st E P)
      (chainHit T st P E) (PostOut E) := by
  let _ : HasPrg := icPrg E.cipher
  intro g
  dsimp only
  have e1 := gameIC_fst T st P g E
  have etr := gameIC_tr T st P g E
  simp only [gameIC] at e1 etr
  rw [etr, e1, hpre, hdst]
  intro hacc _ hh leaves hr
  obtain ⟨-, leaves', hr0, -⟩ := (accept_iff _ T st (πOf g P E)).1 hacc
  have hiv := (verify_iv_chal1 _ T st _ hacc hr0).1
  rw [hiv] at hr
  set y := runY (Hashes.ofTable g) st (runChain (Hashes.ofTable g) T st (πOf g P E) leaves
    (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))).2.1.keys)
  have hyG : ((.h22, y) : Dom) ∈ (gLog T st P E g).map Sigma.fst :=
    inLog_gLog T st P E g (inLog_verifyQ g T st _ hacc hr _).2.1
  intro hmem
  apply noHit_cell T st P E hh hyG
  simp only [hitTargets, List.mem_append, combTargets, hcomb]
  refine Or.inr (List.mem_map.2 ⟨(g (.h22, y)).ba ++ dst, mem_kindIns hmem, ?_⟩)
  exact ByteArray.extract_append_eq_left (Prob.Bytes.size_ba _).symm

/-- The hits of a combined relation: the issue relations' plus the earlier combination inputs. -/
noncomputable def chainHitEpsComb (q : Kind → ℕ) (M : ℕ) : ℝ≥0∞ :=
  chainHitEps q + (q .h22 + 1) * (((q (.comb M) + 1 : ℕ) : ℝ≥0∞) / 2 ^ 448)

lemma hitSum_hitEps_comb (q : Kind → ℕ) (M : ℕ) {cb : Option (ℕ × ByteArray)} {dst : ByteArray}
    (hcb : cb = some (M, dst)) :
    hitSum (q + verifierQueries) (hitEps (q + extractorQueries + verifierQueries)
      (combCount cb (q + extractorQueries + verifierQueries))) =
      chainHitEpsComb q M := by
  subst hcb
  simp only [hitSum, hitEps, chainHitEpsComb, chainHitEps, combCount, Pi.add_apply,
    extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false, add_zero,
    Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, ENNReal.add_div, mul_add,
    mul_zero]
  ring

end Comb

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **moussakaRedeem_accept_le_full Moussaka redemption** in the random-oracle and ideal-cipher model, every term explicit (as
`moussakaIssue_accept_le_full`, with the combination freshness and the earlier combination
inputs among the hits; `n` is `P`'s total hash-query count). -/
theorem moussakaRedeem_accept_le_full (anchors : List UovPk) (hn64 : anchors.length ≤ 64)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
          (fun _ => moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
            (fnOf ctxIss) (fnOf ctxRed)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q Moussaka.M := by
  rw [← hitSum_hitEps_comb q Moussaka.M
    (cb := (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows).comb) rfl]
  exact moussakaRedeem_accept_le_ic anchors hn64 nf ctxIss ctxRed challengeDigest labelRows (preOf CrtGen.tables _ P)
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

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **ratatouilleSpend_accept_le_full Ratatouille spend** in the random-oracle and ideal-cipher model, every term explicit (as
`moussakaIssue_accept_le_full`, with the combination freshness and the earlier combination
inputs among the hits; `n` is `P`'s total hash-query count). -/
theorem ratatouilleSpend_accept_le_full (pk : UovPk) (nf : ByteArray) (d : ℕ) (hd : d < 2 ^ 64)
    (cNext ctxIss : ByteArray) (labelRows : Bool)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (ratatouilleSpend pk nf d cNext ctxIss labelRows)
          (fun _ => ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext)
            (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q Ratatouille.uovM := by
  rw [← hitSum_hitEps_comb q Ratatouille.uovM
    (cb := (ratatouilleSpend pk nf d cNext ctxIss labelRows).comb) rfl]
  exact ratatouilleSpend_accept_le_ic pk nf d hd cNext ctxIss labelRows (preOf CrtGen.tables _ P)
    (midOf CrtGen.tables _ P) (accOf CrtGen.tables _ P) (preCells CrtGen.tables _ P)
    (fun E => CombData.ofSys_committed _ _ _ _ _ _ _ (preOf_committed CrtGen.tables _ P E)
      (accOf_committed CrtGen.tables _ P E) (midOf_committed CrtGen.tables _ P E)
      (fun y g x v hx => midOf_comb CrtGen.tables _ P E Ratatouille.uovM y g x v hx)
      (preCells_mid CrtGen.tables _ P E)
      (fun y g x v h => preCells_comb CrtGen.tables _ P E Ratatouille.uovM y g x v h)) P qE hqE n hn q hq (fun E r => PostOut E r)
    (fun E r => DeadOpenOut _ E r) (prEvent_joint_deadOpen_le CrtGen.tables _ P q hq)
    (prEvent_joint_postOut_le P CrtGen.tables _ qE hqE q hq) (deadOf CrtGen.tables _ P)
    (chainHit CrtGen.tables _ P) _ (hitEps_eq_zero _ _)
    (fun E => prEvent_chainHit_le CrtGen.tables _ P E _ (isKindQueryBound_gameIC _ _ P E hq))
    (sameChainHyp_ic CrtGen.tables _ P) (deadHiddenHyp_ic CrtGen.tables _ P)
    (fun E => combFreshHyp_ic CrtGen.tables _ P E rfl _ rfl rfl)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **pomfritRedeem_accept_le_full PomFRIT redemption** in the random-oracle and ideal-cipher model, every term explicit (as
`moussakaIssue_accept_le_full`, with the combination freshness and the earlier combination
inputs among the hits; `n` is `P`'s total hash-query count). -/
theorem pomfritRedeem_accept_le_full (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (pomfritRedeem pk sig msg labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (pomfritRedeem pk sig msg labelRows)
          (fun c1 => pomfritWit GF256.ofBits 119 45 pk.map
            (fun k => ⟨fnOf (pomfritTarget (pomfritParams labelRows) pk.digest c1 sig msg) k.val⟩)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q 45 := by
  rw [← hitSum_hitEps_comb q 45
    (cb := (pomfritRedeem pk sig msg labelRows).comb) rfl]
  exact pomfritRedeem_accept_le_ic pk sig msg labelRows (preOf CrtGen.tables _ P)
    (midOf CrtGen.tables _ P) (accOf CrtGen.tables _ P) (preCells CrtGen.tables _ P)
    (fun E => pomfritData_committed _ _ _ _ _ _ _ _ (preOf_committed CrtGen.tables _ P E)
      (accOf_committed CrtGen.tables _ P E) (midOf_committed CrtGen.tables _ P E)
      (fun y g x v hx => midOf_comb CrtGen.tables _ P E 45 y g x v hx)
      (preCells_mid CrtGen.tables _ P E)
      (fun y g x v h => preCells_comb CrtGen.tables _ P E 45 y g x v h)) P qE hqE n hn q hq (fun E r => PostOut E r)
    (fun E r => DeadOpenOut _ E r) (prEvent_joint_deadOpen_le CrtGen.tables _ P q hq)
    (prEvent_joint_postOut_le P CrtGen.tables _ qE hqE q hq) (deadOf CrtGen.tables _ P)
    (chainHit CrtGen.tables _ P) _ (hitEps_eq_zero _ _)
    (fun E => prEvent_chainHit_le CrtGen.tables _ P E _ (isKindQueryBound_gameIC _ _ P E hq))
    (sameChainHyp_ic CrtGen.tables _ P) (deadHiddenHyp_ic CrtGen.tables _ P)
    (fun E => combFreshHyp_ic CrtGen.tables _ P E rfl _ rfl rfl)

end VoleMole.ROM.IC
