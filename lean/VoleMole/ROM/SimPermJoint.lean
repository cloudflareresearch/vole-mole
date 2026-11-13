import VoleMole.ROM.PermJoint

/-!
# Simultaneous extraction across two relations in the permutation model

`ROM/SimJoint.lean`'s joint charging (each query of a protocol run charged once for both
relations) with the ideal cipher as random permutations and inverse queries (`ROM/PermModel.lean`).

**The obstacle.** The per-relation bounds of `ROM/SimPerm.lean` run each relation's provers
through its own normalization `normP p π`, which adds the `H₄` query of the `iv` *at the
relation's parameters* (`ivIn p`) before every `H₂¹` query. Issuance and redemption (spend) have
different parameters, so their normalized reference runs have different hash logs, and the joint
bound, which charges the queries of **one** shared run, needs one hash log (`hsame`).

**The resolution.** Both relations' provers go through one normalization `normP p_N π`, of provers
that make the `iv` queries of the other parameter set themselves (`ROM/PermJoint.lean`:
`normJ p_I p_R π P = normP p_I π (addIV p_R P)`). The shared run then has one hash log. The
permutation-model bounds used `p_N` in two roles, which are now separate:
- the *records* of the normalized prover (binding, an opened dead leaf, the averaging over `π`):
  any `p_N`, unchanged;
- *N1* (the chain's `iv` is in the log before the chain), used by Post and `KeysPre`: at the
  statement's parameters `p`, a hypothesis `IvBefore p` on the normalized log, which `normJ`
  satisfies for both `p_I` (`ivBefore_normP`) and `p_R` (`ivBefore_normP_addIV`).
Per permutation table the normalized provers are provers of the PRF view at `π.fwd`, so
`prEvent_sim_joint_le_E` applies with `cf = PostPOut p` (`keysPre_iv`); averaged over `π`, the
failure terms are `failEpsP` per output (`sum_fail_leP_iv`).

* **`prEvent_sim_joint_leP`**: for any normalization parameters `p_N` and provers with N1 at both
  relations' parameters,

      Pr[event] ≤ Σ_k q'_k·jointEps_k + |J_I|·Σ_k r_k·ε_I,k + |J_R|·Σ_k r_k·ε_R,k
        + (|J_I| + |J_R|)·failEpsP q q_E,

  `q' = addH4 q` (the `H₄` queries are not charged, `ε_{H₄} = 0`), the total hash count `n_G + q₂₁`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

variable {ιI' ιR' α ιI βI ιR βR : Type}

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Simultaneous extraction for an issue-type and a combined relation together, in the
permutation model**: provers `PI j`, `PR j` with forward and inverse cipher queries, normalized at
one parameter set `pN`, with N1 at both relations' parameters (`hN1I`, `hN1R`), the two
normalized reference runs having one hash log (`hsame`). Each query of the shared run is charged
once (`jointEps`), each output's continuation at its relation's charge, each output's failure
terms by `failEpsP`. -/
theorem prEvent_sim_joint_leP (T : CrtTables) (hT : liftInvOk T = true)
    (stI : ιI → Statement) (decI : ByteArray → Option ιI)
    (sysI : ιI → System GF128) (stI₀ : Statement) (hparamsI : ∀ s, (stI s).params = stI₀.params)
    (hdelI : ∀ s, (stI s).delayed = false) (hcombI : ∀ s, (stI s).comb = none)
    (hdecI : ∀ s, decI (muIn (stI s)) = some s) {n : ℕ} (hn : ∀ s, (sysI s).length = n)
    (stR : ιR → Statement) (decR : ByteArray → Option ιR)
    {M : ℕ} (sysL : ιR → (Fin M → GF128) → System GF128) (witL : ιR → (ℕ → GF128) → Prop)
    (dst : ByteArray) (stR₀ : Statement) (hparamsR : ∀ s, (stR s).params = stR₀.params)
    (hdelR : ∀ s, (stR s).delayed = false) (hcombR : ∀ s, (stR s).comb = some (M, dst))
    (hdecR : ∀ s, decR (muIn (stR s)) = some s) {n' : ℕ} (hn' : ∀ s l, (sysL s l).length = n')
    {εc : ℝ≥0∞} (hεc : ∀ s w, prU (Fin M → GF128) (fun l => (sysL s l).Holds w ∧ ¬witL s w) ≤ εc)
    (hsep : ∀ x, (decI x).isSome → (decR x).isSome → False) (N : ℕ)
    (WitI : ιI → ByteArray → (ℕ → GF128) → Prop)
    (hvalsI : ∀ s c1 lb w, (stI s).values c1 lb w = (sysI s).values w)
    (hdetI : ∀ (E : CTable) s, @ChainDet (icPrg E.cipher) T (stI s) (sysI s) N (WitI s))
    (WitR : ιR → ByteArray → (ℕ → GF128) → Prop)
    (hvalsR : ∀ s c1 (v : Prob.Bytes (16 * M)) w,
      (stR s).values c1 v.ba w = (sysL s (combDec v)).values w)
    (hdetR : ∀ (E : CTable) s, @CombDet (icPrg E.cipher) M T (stR s) (sysL s) (witL s) N (WitR s))
    (pN : Params)
    (PI₀ : OracleComp specP (ByteArray × (ιI × βI)))
    (PI : ιI' → OracleComp specP (ByteArray × (ιI × βI)))
    (PR₀ : OracleComp specP (ByteArray × (ιR × βR)))
    (PR : ιR' → OracleComp specP (ByteArray × (ιR × βR)))
    (hN1I : ∀ j (π : PTable) g, IvBefore stI₀.params (jP pN g π (PI j)))
    (hN1R : ∀ j (π : PTable) g, IvBefore stR₀.params (jP pN g π (PR j)))
    (JI : Finset ιI') (JR : Finset ιR') (qE : ℕ)
    (hqEI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isRight = true) qE)
    (hqER : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hqI : ∀ j ∈ JI, IsKindQueryBoundP (PI j) q) (hqR₀ : IsKindQueryBoundP PR₀ q)
    (hqR : ∀ j ∈ JR, IsKindQueryBoundP (PR j) q) (nG : ℕ)
    (hnGI : ∀ j ∈ JI, IsQueryBoundP (PI j) (fun t => t.isLeft = true) nG)
    (hnGR₀ : IsQueryBoundP PR₀ (fun t => t.isLeft = true) nG)
    (hnGR : ∀ j ∈ JR, IsQueryBoundP (PR j) (fun t => t.isLeft = true) nG)
    (hpreI : ∀ π : PTable, PrefixRuns π.fwd (normP pN π PI₀) (fun j => normP pN π (PI j)) JI)
    (hpreR : ∀ π : PTable, PrefixRuns π.fwd (normP pN π PR₀) (fun j => normP pN π (PR j)) JR)
    (hsame : ∀ (π : PTable) g, tableQueryLog (runE π.fwd (normP pN π PI₀)) g =
      tableQueryLog (runE π.fwd (normP pN π PR₀)) g)
    (oa : PTable → OracleComp spec α) (event : PTable → α → Prop)
    (htr : ∀ π g, event π (evalWithAnswerFn (QueryImpl.ofFn g) (oa π)) →
      (∃ j ∈ JI,
        let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stI (normP pN π (PI j)) π.fwd)
        r.2.2.accept = true ∧
          ¬@Extracted (icPrg π.fwd.cipher) _ (stI (stOut r)) (WitI (stOut r)) r) ∨
      (∃ j ∈ JR,
        let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stR (normP pN π (PR j)) π.fwd)
        r.2.2.accept = true ∧
          ¬@Extracted (icPrg π.fwd.cipher) _ (stR (stOut r)) (WitR (stOut r)) r)) :
    let nn := addH4 q + extractorQueries + verifierQueries
    let ntot := nG + q .h21 + 2 + verifierTotal
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (oa π)).run' ∅}[event π r] ≤
      ∑ k ∈ adaptKinds, (addH4 q k : ℝ≥0∞) *
        jointEps (M := M) dst stI₀ stR₀ n n' εc ntot N nn k +
      ∑ _j ∈ JI, ∑ k ∈ adaptKinds,
        ((extractorQueries + verifierQueries) k : ℝ≥0∞) * adaptEps stI₀ n N none nn k +
      ∑ _j ∈ JR, ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) *
        combAdaptEps (M := M) dst stR₀ n' εc ntot N nn k +
      JI.card * failEpsP q qE + JR.card * failEpsP q qE := by
  intro nn ntot
  refine (prEvent_avg_le_sum3₂ ($ᵗ PTable) _ _ (∑ k ∈ adaptKinds, (addH4 q k : ℝ≥0∞) *
      jointEps (M := M) dst stI₀ stR₀ n n' εc ntot N nn k +
    ∑ _j ∈ JI, ∑ k ∈ adaptKinds,
      ((extractorQueries + verifierQueries) k : ℝ≥0∞) * adaptEps stI₀ n N none nn k +
    ∑ _j ∈ JR, ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) *
      combAdaptEps (M := M) dst stR₀ n' εc ntot N nn k) JI
    (fun j π => (simulateQ randomOracle (gameA T stI (normP pN π (PI j)) π.fwd)).run' ∅)
    (fun π r => bindFailA stI π.fwd r) (fun π r => deadOpenA stI π.fwd r)
    (fun π r => PostPOut stI₀.params π.fwd r) JR
    (fun j π => (simulateQ randomOracle (gameA T stR (normP pN π (PR j)) π.fwd)).run' ∅)
    (fun π r => bindFailA stR π.fwd r) (fun π r => deadOpenA stR π.fwd r)
    (fun π r => PostPOut stR₀.params π.fwd r) fun π =>
      prEvent_sim_joint_le_E T stI decI stR decR π.fwd hT sysI stI₀ hparamsI hdelI hcombI hdecI
      hn sysL witL dst stR₀ hparamsR hdelR hcombR hdecR hn' hεc hsep N WitI hvalsI (hdetI π.fwd)
      WitR hvalsR (hdetR π.fwd) (normP pN π PI₀) (fun j => normP pN π (PI j)) (normP pN π PR₀)
      (fun j => normP pN π (PR j)) (fun r => PostPOut stI₀.params π.fwd r)
      (fun j s g h => keysPre_iv T stI pN stI₀.params (PI j) (hparamsI s) π g (hN1I j π g) h)
      (fun r => PostPOut stR₀.params π.fwd r)
      (fun j s g h => keysPre_iv T stR pN stR₀.params (PR j) (hparamsR s) π g (hN1R j π g) h)
      JI JR (addH4 q) (fun j hj => isKindQueryBound_normP pN π (hqI j hj))
      (isKindQueryBound_normP pN π hqR₀) (fun j hj => isKindQueryBound_normP pN π (hqR j hj))
      (nG + q .h21) (fun j hj => isQueryBoundP_left_normP pN π (hnGI j hj) (hqI j hj))
      (isQueryBoundP_left_normP pN π hnGR₀ hqR₀)
      (fun j hj => isQueryBoundP_left_normP pN π (hnGR j hj) (hqR j hj)) (hpreI π) (hpreR π)
      (hsame π) (oa π) (event π) (htr π)).trans ?_
  rw [add_assoc _ (∑ j ∈ JI, _) (∑ j ∈ JR, _), add_assoc _ ((JI.card : ℝ≥0∞) * _)]
  exact add_le_add le_rfl (add_le_add
    (sum_fail_leP_iv T stI pN stI₀.params hparamsI PI JI qE hqEI q hqI)
    (sum_fail_leP_iv T stR pN stR₀.params hparamsR PR JR qE hqER q hqR))

end VoleMole.ROM.IC
