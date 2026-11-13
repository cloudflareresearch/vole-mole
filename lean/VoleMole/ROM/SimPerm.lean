import VoleMole.ROM.SimJoint
import VoleMole.ROM.PermAdapt

/-!
# Simultaneous extraction with the ideal cipher as random permutations (inverse queries)

`ROM/SimExtract.lean`'s simultaneous bounds in the permutation model of `ROM/PermModel.lean`
(plan §2h, §2i): the provers `P j` make forward and inverse cipher queries; at each permutation
table `π` the normalized provers `normP p π (P j)` (one `H₄` query added per `H₂¹` query, inverse
queries recorded as forward ones) are provers of the PRF view at the cipher table `π.fwd`, so
`prEvent_sim_le_E` / `prEvent_sim_comb_le_E` apply per table. Averaged over `π`, with the failure
events bounded per output in the permutation model (`ROM/PermAdapt.lean`'s
`prEvent_jointP_bindFail_le_A`, `prEvent_jointP_deadOpen_le_A`, `prEvent_jointP_postP_le_A`):

    Pr[event] ≤ Σ_k q'_k·ε_k + |J|·Σ_k r_k·ε_k + |J|·failEpsP q q_E,

`q' = addH4 q` the normalized budget (the extra `H₄` queries are not charged: `ε_{H₄} = 0`).

* `normP_map`, `prefixRuns_normP_map`: normalization commutes with projections, so projections of
  one run stay prefix runs after normalization.
* `failEpsP`, `sum_fail_leP`: the per-output failure terms in the permutation model.
* **`prEvent_sim_leP`**, **`prEvent_sim_comb_leP`**.

The two relations of a protocol together: `ROM/SimPermJoint.lean`. The normalization depends on
the relation's parameters (`ivIn p`), which differ between issuance and redemption (spend); there
one normalization adds the `iv` queries of both parameter sets (`normJ`, `ROM/PermJoint.lean`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## Normalization and projections -/

/-- **Normalization commutes with a projection of the output.** -/
theorem normP_map {γ α : Type} (p : Params) (π : PTable) (f : γ → α) (G : OracleComp specP γ) :
    normP p π (f <$> G) = f <$> normP p π G := by
  induction G using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with d | ⟨b, c⟩
    · rw [map_bind, normP_inl, normP_inl]
      split_ifs
      · simp only [map_bind]
        exact congrArg _ (funext fun _ => congrArg _ (funext fun u => ih u))
      · simp only [map_bind]
        exact congrArg _ (funext fun u => ih u)
    · cases b
      · rw [map_bind, normP_inv, normP_inv]
        simp only [map_bind]
        exact congrArg _ (funext fun _ => ih _)
      · rw [map_bind, normP_fwd, normP_fwd]
        simp only [map_bind]
        exact congrArg _ (funext fun u => ih u)

/-- **Projections of one run stay prefix runs after normalization.** -/
theorem prefixRuns_normP_map {ι' ι β γ : Type} (p : Params) (π : PTable) (G : OracleComp specP γ)
    (proj : ι' → γ → ByteArray × (ι × β)) (j₀ : ι') (J : Finset ι') :
    PrefixRuns π.fwd (normP p π (proj j₀ <$> G)) (fun j => normP p π (proj j <$> G)) J := by
  have h := prefixRuns_map π.fwd (normP p π G) proj j₀ J
  simpa only [normP_map] using h

/-! ## The failure terms -/

/-- The failure terms of one output in the permutation model (binding, an opened dead leaf,
point-tied Post), as in `prEvent_accept_le_adaptiveP`. -/
noncomputable def failEpsP (q : Kind → ℕ) (qE : ℕ) : ℝ≥0∞ :=
  (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
    (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) + qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2

/-- The per-output failure terms of the provers `P j` in the permutation model. -/
theorem sum_fail_leP {ι' ι β : Type} (T : CrtTables) (stF : ι → Statement) (p : Params)
    (hparams : ∀ s, (stF s).params = p) (P : ι' → OracleComp specP (ByteArray × (ι × β)))
    (J : Finset ι') (qE : ℕ) (hqE : ∀ j ∈ J, IsQueryBoundP (P j) (fun t => t.isRight = true) qE)
    (q : Kind → ℕ) (hq : ∀ j ∈ J, IsKindQueryBoundP (P j) q) :
    ∑ j ∈ J, (Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
        (gameA T stF (normP p π (P j)) π.fwd)).run' ∅}[bindFailA stF π.fwd r] +
      Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
        (gameA T stF (normP p π (P j)) π.fwd)).run' ∅}[deadOpenA stF π.fwd r] +
      Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
        (gameA T stF (normP p π (P j)) π.fwd)).run' ∅}[PostPOut p π.fwd r]) ≤
      J.card * failEpsP q qE := by
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun j hj => ?_
  have hdo := prEvent_jointP_deadOpen_le_A T stF p (P j) hparams qE (hqE j hj) q (hq j hj)
  unfold failEpsP
  gcongr
  · exact (prEvent_jointP_bindFail_le_A T stF p (P j) qE (hqE j hj)).trans (add_le_add le_rfl hdo)
  · exact prEvent_jointP_postP_le_A T stF p (P j) qE (hqE j hj) q (hq j hj)

/-! ## The simultaneous bounds in the permutation model -/

variable {ι' α ι β : Type}

/-- **Simultaneous extraction for the issue relations in the permutation model**: provers `P j`
(forward and inverse cipher queries) whose normalized runs are prefixes of `P₀`'s at every
permutation table (`prefixRuns_normP_map` for projections of one run), all within `q_E` cipher
queries, `q k` hash queries of kind `k` and `n_G` in all. -/
theorem prEvent_sim_leP (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
    (sys : ι → System GF128) (hT : liftInvOk T = true) (st₀ : Statement)
    (hparams : ∀ s, (stF s).params = st₀.params) (hdel : ∀ s, (stF s).delayed = false)
    (cb : Option (ℕ × ByteArray)) (hcomb : ∀ s, (stF s).comb = cb)
    (hdec : ∀ s, dec (muIn (stF s)) = some s) {n : ℕ} (hn : ∀ s, (sys s).length = n) (N : ℕ)
    (Wit : ι → ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ s c1 lb w, (stF s).values c1 lb w = (sys s).values w)
    (hdet : ∀ (E : CTable) s, @ChainDet (icPrg E.cipher) T (stF s) (sys s) N (Wit s))
    (P₀ : OracleComp specP (ByteArray × (ι × β))) (P : ι' → OracleComp specP (ByteArray × (ι × β)))
    (J : Finset ι') (qE : ℕ) (hqE : ∀ j ∈ J, IsQueryBoundP (P j) (fun t => t.isRight = true) qE)
    (q : Kind → ℕ) (hq₀ : IsKindQueryBoundP P₀ q) (hq : ∀ j ∈ J, IsKindQueryBoundP (P j) q)
    (nG : ℕ) (hnG₀ : IsQueryBoundP P₀ (fun t => t.isLeft = true) nG)
    (hnG : ∀ j ∈ J, IsQueryBoundP (P j) (fun t => t.isLeft = true) nG)
    (hpre : ∀ π : PTable, PrefixRuns π.fwd (normP st₀.params π P₀)
      (fun j => normP st₀.params π (P j)) J)
    (oa : PTable → OracleComp spec α) (event : PTable → α → Prop)
    (htr : ∀ π g, event π (evalWithAnswerFn (QueryImpl.ofFn g) (oa π)) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA T stF (normP st₀.params π (P j)) π.fwd)
      r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (stF (stOut r)) (Wit (stOut r)) r) :
    let n' := addH4 q + extractorQueries + verifierQueries
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (oa π)).run' ∅}[event π r] ≤
      ∑ k ∈ adaptKinds, (addH4 q k : ℝ≥0∞) * adaptEps st₀ n N cb n' k +
      ∑ _j ∈ J, ∑ k ∈ adaptKinds,
        ((extractorQueries + verifierQueries) k : ℝ≥0∞) * adaptEps st₀ n N cb n' k +
      J.card * failEpsP q qE := by
  intro n'
  have h := prEvent_avg_le_sum3₂ ($ᵗ PTable) _ _ (∑ k ∈ adaptKinds, (addH4 q k : ℝ≥0∞) *
      adaptEps st₀ n N cb n' k + ∑ _j ∈ J, ∑ k ∈ adaptKinds,
        ((extractorQueries + verifierQueries) k : ℝ≥0∞) * adaptEps st₀ n N cb n' k) J
    (fun j π => (simulateQ randomOracle (gameA T stF (normP st₀.params π (P j)) π.fwd)).run' ∅)
    (fun π r => bindFailA stF π.fwd r) (fun π r => deadOpenA stF π.fwd r)
    (fun π r => PostPOut st₀.params π.fwd r) (∅ : Finset ι')
    (fun j π => (simulateQ randomOracle (gameA T stF (normP st₀.params π (P j)) π.fwd)).run' ∅)
    (fun π r => bindFailA stF π.fwd r) (fun π r => deadOpenA stF π.fwd r)
    (fun π r => PostPOut st₀.params π.fwd r) fun π => by
      simpa only [Finset.sum_empty, add_zero] using
        prEvent_sim_le_E T stF dec π.fwd (normP st₀.params π P₀)
          (fun j => normP st₀.params π (P j)) sys hT st₀ hparams hdel cb hcomb hdec hn N Wit hvals
          (hdet π.fwd) (fun r => PostPOut st₀.params π.fwd r)
          (fun j s g h => keysPre_A T stF st₀.params (P j) (hparams s) π g h) J (addH4 q)
          (isKindQueryBound_normP st₀.params π hq₀)
          (fun j hj => isKindQueryBound_normP st₀.params π (hq j hj)) (nG + q .h21)
          (isQueryBoundP_left_normP st₀.params π hnG₀ hq₀)
          (fun j hj => isQueryBoundP_left_normP st₀.params π (hnG j hj) (hq j hj))
          (hpre π) (oa π) (event π) (htr π)
  rw [Finset.sum_empty, add_zero] at h
  exact h.trans (add_le_add le_rfl (sum_fail_leP T stF st₀.params hparams P J qE hqE q hq))

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Simultaneous extraction for the combined relations in the permutation model** (the
normalized provers' total hash count is `n_G + q₂₁`). -/
theorem prEvent_sim_comb_leP (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
    {M : ℕ} (sysL : ι → (Fin M → GF128) → System GF128)
    (witL : ι → (ℕ → GF128) → Prop) (dst : ByteArray) (hT : liftInvOk T = true)
    (st₀ : Statement) (hparams : ∀ s, (stF s).params = st₀.params)
    (hdel : ∀ s, (stF s).delayed = false) (hcomb : ∀ s, (stF s).comb = some (M, dst))
    (hdec : ∀ s, dec (muIn (stF s)) = some s) {n' : ℕ} (hn' : ∀ s l, (sysL s l).length = n')
    {εc : ℝ≥0∞} (hεc : ∀ s w, prU (Fin M → GF128) (fun l => (sysL s l).Holds w ∧ ¬witL s w) ≤ εc)
    (N : ℕ) (Wit : ι → ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ s c1 (v : Prob.Bytes (16 * M)) w,
      (stF s).values c1 v.ba w = (sysL s (combDec v)).values w)
    (hdet : ∀ (E : CTable) s, @CombDet (icPrg E.cipher) M T (stF s) (sysL s) (witL s) N (Wit s))
    (P₀ : OracleComp specP (ByteArray × (ι × β))) (P : ι' → OracleComp specP (ByteArray × (ι × β)))
    (J : Finset ι') (qE : ℕ) (hqE : ∀ j ∈ J, IsQueryBoundP (P j) (fun t => t.isRight = true) qE)
    (q : Kind → ℕ) (hq₀ : IsKindQueryBoundP P₀ q) (hq : ∀ j ∈ J, IsKindQueryBoundP (P j) q)
    (nG : ℕ) (hnG₀ : IsQueryBoundP P₀ (fun t => t.isLeft = true) nG)
    (hnG : ∀ j ∈ J, IsQueryBoundP (P j) (fun t => t.isLeft = true) nG)
    (hpre : ∀ π : PTable, PrefixRuns π.fwd (normP st₀.params π P₀)
      (fun j => normP st₀.params π (P j)) J)
    (oa : PTable → OracleComp spec α) (event : PTable → α → Prop)
    (htr : ∀ π g, event π (evalWithAnswerFn (QueryImpl.ofFn g) (oa π)) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA T stF (normP st₀.params π (P j)) π.fwd)
      r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (stF (stOut r)) (Wit (stOut r)) r) :
    let nn := addH4 q + extractorQueries + verifierQueries
    let ntot := nG + q .h21 + 2 + verifierTotal
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (oa π)).run' ∅}[event π r] ≤
      ∑ k ∈ adaptKinds, (addH4 q k : ℝ≥0∞) * combAdaptEps (M := M) dst st₀ n' εc ntot N nn k +
      ∑ _j ∈ J, ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) *
        combAdaptEps (M := M) dst st₀ n' εc ntot N nn k +
      J.card * failEpsP q qE := by
  intro nn ntot
  have h := prEvent_avg_le_sum3₂ ($ᵗ PTable) _ _ (∑ k ∈ adaptKinds, (addH4 q k : ℝ≥0∞) *
      combAdaptEps (M := M) dst st₀ n' εc ntot N nn k + ∑ _j ∈ J, ∑ k ∈ adaptKinds,
        ((extractorQueries + verifierQueries) k : ℝ≥0∞) *
          combAdaptEps (M := M) dst st₀ n' εc ntot N nn k) J
    (fun j π => (simulateQ randomOracle (gameA T stF (normP st₀.params π (P j)) π.fwd)).run' ∅)
    (fun π r => bindFailA stF π.fwd r) (fun π r => deadOpenA stF π.fwd r)
    (fun π r => PostPOut st₀.params π.fwd r) (∅ : Finset ι')
    (fun j π => (simulateQ randomOracle (gameA T stF (normP st₀.params π (P j)) π.fwd)).run' ∅)
    (fun π r => bindFailA stF π.fwd r) (fun π r => deadOpenA stF π.fwd r)
    (fun π r => PostPOut st₀.params π.fwd r) fun π => by
      simpa only [Finset.sum_empty, add_zero] using
        prEvent_sim_comb_le_E T stF dec π.fwd (normP st₀.params π P₀)
          (fun j => normP st₀.params π (P j)) sysL witL dst hT st₀ hparams hdel hcomb hdec hn' hεc
          N Wit hvals (hdet π.fwd) (fun r => PostPOut st₀.params π.fwd r)
          (fun j s g h => keysPre_A T stF st₀.params (P j) (hparams s) π g h) J (addH4 q)
          (isKindQueryBound_normP st₀.params π hq₀)
          (fun j hj => isKindQueryBound_normP st₀.params π (hq j hj)) (nG + q .h21)
          (isQueryBoundP_left_normP st₀.params π hnG₀ hq₀)
          (fun j hj => isQueryBoundP_left_normP st₀.params π (hnG j hj) (hq j hj))
          (hpre π) (oa π) (event π) (htr π)
  rw [Finset.sum_empty, add_zero] at h
  exact h.trans (add_le_add le_rfl (sum_fail_leP T stF st₀.params hparams P J qE hqE q hq))

end VoleMole.ROM.IC
