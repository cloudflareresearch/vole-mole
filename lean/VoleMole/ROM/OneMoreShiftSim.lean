import VoleMole.ROM.OneMoreLemmaPSim
import VoleMole.ROM.OneMoreShiftBound

/-!
# U2's term with simultaneous extraction (gap G8)

`lean/docs/security/pomfrit.md` §6.2, §6.4; `lean/docs/probabilistic-plan.md` §2m, §2n.
`ROM/OneMoreShiftBound.lean` bounds `Pr[∃ i ≤ ℓ, ShiftFail i]` by a union over the `ℓ + 1`
forgeries. Here each query of the forger's run is charged once, as for U1
(`ROM/OneMoreLemmaPSim.lean`, whose proofs this file follows with `N = 2` for `2⁵⁷`).

* **The per-query bad event** (`simBadS`): `pomBad` with `N = 2` (Lemma P without `Shift`) or an
  order hit; it reads the logs before the query only (`simBadS_prefix_congr`); per query
  `≤ simEpsS` (`prEvent_simBadS_le`: `2⁻¹⁵⁰` at `H₂¹`, `ε_QS + 2⁻¹²⁸ + ntot·2⁻⁴⁴⁸` at `H₂²`,
  `2·2⁻¹²⁸` at `H₂³`, the hits, statement hits and order hits).
* **The prefix runs** (`prefix_of_shiftFail`): a failed forgery of U2 passed the game's
  verification (`ver_tableG`), so its derived prover's logs are prefixes of the last one's.
* **The trace**: `shiftFail_events`, then `pomBad_traceG` with U2's goal (`GoalS`).
* **The bounds**: per cipher table (`prEvent_shiftFailZ_sim_le_E`), joint
  (`prEvent_shiftFailZ_sim_le`), in the game (`prEvent_shiftFail_sim_le`), and Theorem U2
  (`pomfrit_U2_sim`): `Pr[PomWin] ≤ Adv^{ompr⊕17} + sfailSimEps`, with the chain charges
  `(q'₂₁ + ℓ + 1)·2⁻¹⁵⁰ + (q'₂₂ + ℓ + 1)·(ε_QS + 2⁻¹²⁸ + …) + (q'₂₃ + ℓ + 1)·2·2⁻¹²⁸`
  (`sfailSimEps_eq`); never worse than the union bound (`sfailSimEps_le`).

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.ZK.Sim VoleMole.Verifier.Bridge

/-! ## The per-query bad event and its bound -/

section Bad

variable (lr : Bool) (pk : UovPk) (E : CTable)

/-- **Lemma P's per-query bad event in the derived game of `P`, with the order hit**: `pomBad`
(the statement committed at the query, chain hits, statement hits) or an order hit. -/
def simBadS {β : Type} (P : OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × β)))
    (t : Dom) (g : Table) : Prop :=
  pomBad pk hG (fun s => s.2.1) (fun s => s.2.2) lr CrtGen.tables P E 2 t g ∨
    orderHitL (tableQueryLog (gameA CrtGen.tables (stG lr pk) P E)) t g

set_option maxRecDepth 4000 in
/-- **At a query of the shorter run, the bad events agree** for two provers whose logs extend one
another. -/
theorem simBadS_prefix_congr {β : Type}
    (P P' : OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × β))) (g : Table)
    (t : Dom) (ht : t ∈ (tableQueryLog (runE E P) g).map Sigma.fst)
    (hH : ∃ Y, tableQueryLog (runE E P') g = tableQueryLog (runE E P) g ++ Y)
    (hJ : ∃ Y, jOf g P' E = jOf g P E ++ Y) :
    simBadS lr pk E P t g ↔ simBadS lr pk E P' t g := by
  let _ : HasPrg := icPrg E.cipher
  set stF := stT pk hG (fun s : TG × ByteArray × ByteArray => s.2.1) (fun s => s.2.2) lr
  obtain ⟨hA, -, hJ'⟩ := logBefore_prefix CrtGen.tables stF E P P' g ht hH hJ
  have hA' : logBefore t (gLogA CrtGen.tables stF P E g) =
      logBefore t (gLogA CrtGen.tables stF P' E g) := hA
  unfold simBadS pomBad combBadF chainHitL stmtHitD orderHitL
  rw [stG_eq_stT, stmtAtD_congr _ _ hA', hA]
  refine or_congr (or_congr (exists_congr fun o => and_congr_right fun _ => ?_) Iff.rfl) Iff.rfl
  obtain ⟨k, x⟩ := t
  by_cases hk : k = .h22
  · subst hk
    have hmid : midOfA CrtGen.tables stF P E (stKT pk hG (fun s => s.2.1) (fun s => s.2.2) lr o)
        x g = midOfA CrtGen.tables stF P' E (stKT pk hG (fun s => s.2.1) (fun s => s.2.2) lr o)
        x g := by
      unfold midOfA; rw [hA', hJ']
    have hpre : preCellsA CrtGen.tables stF P E x g = preCellsA CrtGen.tables stF P' E x g := by
      unfold preCellsA; rw [hA']
    simp only [combBad, ite_true, CombData.qsComb, CombData.wC, combDataD]
    rw [hmid, hpre]
  · simp only [combBad, hk, ite_false]
    refine chainBad_congr_at _ _ CrtGen.tables chal3Blocks _ g k x (fun hk' => ?_)
      (fun hk' => absurd hk' hk) (fun hk' => ?_)
    · subst hk'
      show preOfA CrtGen.tables stF P E _ x g = preOfA CrtGen.tables stF P' E _ x g
      unfold preOfA
      rw [hA', hJ']
    · subst hk'
      show accOfA CrtGen.tables stF P E _ x g = accOfA CrtGen.tables stF P' E _ x g
      unfold accOfA
      rw [hA', hJ']

/-- The chain charges of Lemma P per kind, with PomFRIT's parameters: KOS at `H₂¹`, the
combined `H₂²` bound (`ntot` bounds the cached cells), `2` accepted `chal3` at `H₂³` (no `Shift`). -/
noncomputable def cellEpsS (ntot : ℕ) : Kind → ℝ≥0∞
  | .h21 => (2 ^ 150 : ℝ≥0∞)⁻¹
  | .h22 => ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) + (2 ^ 128 : ℝ≥0∞)⁻¹ +
      (ntot : ℝ≥0∞) / 2 ^ 448
  | .h23 => (2 : ℝ≥0∞) / 2 ^ 128
  | _ => 0

/-- **The per-query charge of `simBadS`** in a game with `n k` queries of kind `k`: the chain
charge, the hits, the statement hits and the order hits. -/
noncomputable def simEpsS (ntot : ℕ) (n : Kind → ℕ) (k : Kind) : ℝ≥0∞ :=
  cellEpsS ntot k + (hitEps n (combCount (some (45, dstP)) n) k + stmtEpsD n k) + orderEps n k

lemma simEpsS_eq_zero (ntot : ℕ) (n : Kind → ℕ) (k : Kind) (hk : k ∉ adaptKinds) :
    simEpsS ntot n k = 0 := by
  cases k <;> simp_all [adaptKinds, simEpsS, cellEpsS, hitEps, stmtEpsD, orderEps]

lemma pomEps_le_cellEpsS (ntot : ℕ) (n : Kind → ℕ) (k : Kind) :
    pomEps pk hG (fun s : TG × ByteArray × ByteArray => s.2.1) (fun s => s.2.2) lr 1313
        (2 ^ 128 : ℝ≥0∞)⁻¹ ntot 2 n k ≤
      cellEpsS ntot k + (hitEps n (combCount (some (45, dstP)) n) k + stmtEpsD n k) := by
  unfold pomEps
  refine add_le_add ?_ le_rfl
  cases k <;> simp only [cellEpsS, chainEps, reduceCtorEq, ite_true, ite_false, le_refl,
    Nat.cast_ofNat]
  exact epsKOS_chal3Blocks_le _ (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])
    (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **The per-query bound of `simBadS`** (cache form), for a prover with `q k` hash queries of
kind `k`. -/
theorem prEvent_simBadS_le {β : Type}
    (P : OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × β))) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) (K : Finset Dom) [SampleableType ((d : K) → Ans d.val)]
    (hK : ∀ u, combKey 45 dstP u ∈ K) (ntot : ℕ)
    (c : (ofFn fun d : K => Ans d.val).QueryCache) (t : K) (hc : c t = none)
    (hcard : (cachedKeys c).card < ntot) :
    Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[
      simBadS lr pk E P t.val (extendTable K (completeTable c g))] ≤
      simEpsS ntot (q + extractorQueries + verifierQueries) t.val.1 := by
  classical
  unfold simBadS simEpsS
  refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
  · refine (prEvent_pomBad_le pk hG (fun s => s.2.1) (fun s => s.2.2) lr CrtGen.tables P E
      liftInvOk_tables 2 (n' := 1313)
      (fun o c1 l => (PomFRIT.pomfritRedeemSystem_length _ _ _ _ _ _ _).trans (by norm_num))
      (εc := (2 ^ 128 : ℝ≥0∞)⁻¹)
      (fun o c1 w => prU_comb_bad_le _ _ w fun hW => pomfrit_comb_bad_gf128 _ _ _ _ w hW)
      q hq K hK ntot c t hc hcard).trans ?_
    exact pomEps_le_cellEpsS lr pk ntot _ _
  · refine prEvent_completeTable_cell_le c _ hc
      (fun t G => orderHitL (tableQueryLog (gameA CrtGen.tables (stG lr pk) P E)) t.val
        (extendTable K G)) _ fun G => ?_
    simp only [extendTable_update]
    exact prEvent_orderHitL_le _ _ (isKindQueryBound_gameA CrtGen.tables (stG lr pk) P E hq) _ _

end Bad

/-! ## The prefix runs of a failed forgery of U2 -/

section PrefixS

variable (g : Table) (lr : Bool) (E : CTable) (pk : UovPk) (pre : TG → SIss) (A : Forger)
  (Lst : List TG) (ℓ : ℕ)

/-- **The derived provers of a failed forgery `i ≤ ℓ` of U2 and of the last forgery**: the former's
joint and hash logs are prefixes of the latter's, at the same tables (`prefix_of_pfail` for U2). -/
theorem prefix_of_shiftFail {i : ℕ} (hiℓ : i ≤ ℓ)
    (h : ShiftFailZ pk i (runG g CrtGen.tables lr E noHint (hintS lr E) tgts2 pk pre A Lst ℓ)) :
    (∃ Y, tableQueryLog (runE E (proverP lr pk pre A Lst ℓ)) g =
      tableQueryLog (runE E (proverP lr pk pre A Lst i)) g ++ Y) ∧
    ∃ Y, jOf g (proverP lr pk pre A Lst ℓ) E = jOf g (proverP lr pk pre A Lst i) E ++ Y := by
  obtain ⟨hacc, x, σ, hcl, -⟩ := h
  obtain ⟨hi, -, hrf, -⟩ :=
    ver_tableG g CrtGen.tables lr E noHint (hintS lr E) tgts2 pk pre A Lst ℓ i hacc hcl
  have hJ := jOf_proverP_prefix g lr E pk pre A Lst hiℓ hi hrf
  exact ⟨runE_proverP_prefix g lr E pk pre A Lst hJ, hJ⟩

end PrefixS

/-! ## The simultaneous bound, per cipher table -/

section SimE

variable (lr : Bool) (pk : UovPk) (pre : TG → SIss) (A : Forger) (Lst : List TG) (ℓ : ℕ)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **U2's term with simultaneous extraction, for fixed key, target stream and cipher table**:
the queries of the last derived prover's run (which extends every derived prover's run where a
forgery fails) are charged once, each forgery's extraction and verification queries once per
forgery, and each forgery's failure events. -/
theorem prEvent_shiftFailZ_sim_le_E (hd : pk.digest.size = 32) {qA : Kind → ℕ} {nA qE QT : ℕ}
    (hA : ForgerBound A qA nA qE QT) (E : CTable) :
    let q := qP qA QT ℓ
    let ε := simEpsS (nP nA QT ℓ + (2 + verifierTotal)) (q + extractorQueries + verifierQueries)
    Pr{let z ← (simulateQ randomOracle ((simulateQ (htW (AR := Ans) noHint pre)
        (Acomp CrtGen.tables lr E (hintS lr E) tgts2 pk ℓ A)).run (hs0G Lst))).run' ∅}[
        ∃ i : Fin (ℓ + 1), ShiftFailZ pk i.val z] ≤
      ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * ε k +
      ∑ _j : Fin (ℓ + 1), ∑ k ∈ adaptKinds,
        ((extractorQueries + verifierQueries) k : ℝ≥0∞) * ε k +
      ∑ j : Fin (ℓ + 1), Pr{let r ← (simulateQ randomOracle
        (gameDP lr E pk pre A Lst j.val)).run' ∅}[failP lr pk E r] := by
  classical
  intro q ε
  set n := nP nA QT ℓ
  set P : ℕ → OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × AuxP)) :=
    fun i => proverP lr pk pre A Lst i with hPdef
  set P₀ := P ℓ
  set oa := (simulateQ (htW (AR := Ans) noHint pre)
    (Acomp CrtGen.tables lr E (hintS lr E) tgts2 pk ℓ A)).run (hs0G Lst)
  set stF := stG lr pk
  have hb : ∀ j : Fin (ℓ + 1), IsKindQueryBoundIC (P j.val) q ∧
      IsQueryBoundP (P j.val) (fun t => t.isLeft = true) n ∧
      IsQueryBoundP (P j.val) (fun t => t.isRight = true) (eP lr qE ℓ) := fun j =>
    proverP_bounds lr pre pk hA Lst (Nat.lt_succ_iff.1 j.isLt)
  have hb₀ := proverP_bounds lr pre pk hA Lst (le_refl ℓ)
  have hK : ∀ k ∉ adaptKinds, ε k = 0 := simEpsS_eq_zero _ _
  let S : Finset Dom := possibleQueryKeys oa ∪ possibleQueryKeys (runE E P₀) ∪
    (Finset.univ : Finset (Fin (ℓ + 1))).biUnion
      (fun j => possibleQueryKeys (gameA CrtGen.tables stF (P j.val) E)) ∪
    Finset.univ.image (combKey 45 dstP)
  have hKS : ∀ u, combKey 45 dstP u ∈ S := fun u =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  have hSo : AllQueriesSatisfy oa (· ∈ S) :=
    (allQueriesSatisfy_possibleQueryKeys oa).mono fun _ h =>
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hSA : AllQueriesSatisfy (runE E P₀) (· ∈ S) :=
    (allQueriesSatisfy_possibleQueryKeys _).mono fun _ h =>
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hSG : ∀ j : Fin (ℓ + 1), AllQueriesSatisfy (gameA CrtGen.tables stF (P j.val) E) (· ∈ S) :=
    fun j => (allQueriesSatisfy_possibleQueryKeys _).mono fun _ h =>
      Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, h⟩))
  let : SampleableType ((d : S) → Ans d.val) := SampleableType.piOfFintype _
  have hcA := worstCaseCostBound_of_kindQueryBound (runE E P₀) adaptKinds ε hK q
    (isKindQueryBound_runE E hb₀.1)
  have htr : ∀ g, (∃ i : Fin (ℓ + 1), ShiftFailZ pk i.val (evalWithAnswerFn (QueryImpl.ofFn g) oa)) →
      (∃ e ∈ tableQueryLog (runE E P₀) g, simBadS lr pk E P₀ e.1 g) ∨
      (∃ j ∈ (Finset.univ : Finset (Fin (ℓ + 1))), ∃ e ∈ tableQueryLog (gameK CrtGen.tables stF E id
          (evalWithAnswerFn (QueryImpl.ofFn g) (runE E (P j.val)))) g,
        e.1 ∉ (tableQueryLog (runE E (P j.val)) g).map Sigma.fst ∧ simBadS lr pk E (P j.val) e.1 g) ∨
      (∃ j ∈ (Finset.univ : Finset (Fin (ℓ + 1))),
        failP lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (gameDP lr E pk pre A Lst j.val))) := by
    intro g hev
    obtain ⟨i, hi⟩ := hev
    have hiℓ : i.val ≤ ℓ := Nat.lt_succ_iff.1 i.isLt
    have hev4 := shiftFail_events g E pk lr pre A Lst ℓ i.val hd hi
    obtain ⟨hH, hJ⟩ := prefix_of_shiftFail g lr E pk pre A Lst ℓ hiℓ hi
    -- a failure of the `i`-th derived game, or a bad query of its log
    have key : failP lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (gameDP lr E pk pre A Lst i.val)) ∨
        ∃ e ∈ tableQueryLog (gameDP lr E pk pre A Lst i.val) g, simBadS lr pk E (P i.val) e.1 g := by
      rcases hev4 with h0 | h1 | h2 | ⟨e, he, hb'⟩
      · by_cases hf : bindFailA stF E (evalWithAnswerFn (QueryImpl.ofFn g)
            (gameDP lr E pk pre A Lst i.val)) ∨ deadOpenA stF E (evalWithAnswerFn (QueryImpl.ofFn g)
            (gameDP lr E pk pre A Lst i.val)) ∨ PostOut E (evalWithAnswerFn (QueryImpl.ofFn g)
            (gameDP lr E pk pre A Lst i.val))
        · left
          rcases hf with hf | hf | hf
          · exact Or.inl hf
          · exact Or.inr (Or.inl hf)
          · exact Or.inr (Or.inr (Or.inl hf))
        · right
          simp only [not_or] at hf
          obtain ⟨e, he, hbad⟩ := pomBad_traceG pk hG (fun s => s.2.1) (fun s => s.2.2) lr
            CrtGen.tables (P i.val) E GoalS liftInvOk_tables 2
            (fun s => combDetG_pomfritT_some pk hG (fun s => s.2.1) (fun s => s.2.2) lr E s)
            (fun r => PostOut E r)
            (fun s g' h => keysPre_of_not_postOut CrtGen.tables _ (P i.val) E g' h) g
            ⟨h0, hf.1, hf.2.1, hf.2.2⟩
          exact ⟨e, he, Or.inl hbad⟩
      · exact Or.inl (Or.inr (Or.inr (Or.inl h1)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h2)))
      · right
        refine ⟨e, he, ?_⟩
        rcases hb' with hb' | hb'
        · exact Or.inl (Or.inr (Or.inl hb'))
        · exact Or.inr hb'
    rcases key with hf | ⟨e, he, hbad⟩
    · exact Or.inr (Or.inr ⟨i, Finset.mem_univ _, hf⟩)
    rw [tableQueryLog_gameA_eq] at he
    by_cases hm : e.1 ∈ (tableQueryLog (runE E (P i.val)) g).map Sigma.fst
    · have hm₀ : e.1 ∈ (tableQueryLog (runE E P₀) g).map Sigma.fst := by
        obtain ⟨Y, hY⟩ := hH
        rw [hY, List.map_append]
        exact List.mem_append_left _ hm
      obtain ⟨e', he', heq⟩ := List.mem_map.1 hm₀
      refine Or.inl ⟨e', he', ?_⟩
      rw [heq]
      exact (simBadS_prefix_congr lr pk E (P i.val) P₀ g e.1 hm hH hJ).1 hbad
    · exact Or.inr (Or.inl ⟨i, Finset.mem_univ _, e,
        (List.mem_append.1 he).resolve_left fun h => hm (List.mem_map_of_mem h), hm, hbad⟩)
  have key := prEvent_le_shared_suffix (D := Dom) (R := Ans) S oa
    (fun z => ∃ i : Fin (ℓ + 1), ShiftFailZ pk i.val z) hSo (runE E P₀) hSA (fun t => ε t.1) _ hcA n
    (isTotalQueryBound_runE E hb₀.2.1) (simBadS lr pk E P₀) Finset.univ
    (fun j : Fin (ℓ + 1) => runE E (P j.val)) (fun _ => gameK CrtGen.tables stF E id)
    (fun j _ => by rw [← gameA_eq_bind]; exact hSG j)
    (∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) * ε k)
    (fun _ a => worstCaseCostBound_of_kindQueryBound _ adaptKinds ε hK _
      (isKindQueryBound_gameK CrtGen.tables stF E id a)) n (2 + verifierTotal)
    (fun j _ => isTotalQueryBound_runE E (hb j).2.1)
    (fun _ a => isTotalQueryBound_gameK CrtGen.tables stF E id a)
    (fun j => simBadS lr pk E (P j.val)) Finset.univ
    (fun j : Fin (ℓ + 1) => gameDP lr E pk pre A Lst j.val) (fun _ r => failP lr pk E r)
    (fun j _ => hSG j) (n + (2 + verifierTotal)) (by omega) le_rfl
    (fun c t hc hcard => prEvent_simBadS_le lr pk E P₀ q hb₀.1 S hKS _ c t hc hcard)
    (fun j _ c t hc hcard => prEvent_simBadS_le lr pk E (P j.val) q (hb j).1 S hKS _ c t hc hcard)
    htr
  exact key

end SimE

/-! ## The joint experiment and the game -/

section Joint

/-- **U2's term with simultaneous extraction, every term explicit**: the shared run's queries
`q k` and each forgery's extraction and verification queries `r k` at the per-query charge
`simEpsS`, and each forgery's failure terms (`failEps`: binding, an opened dead leaf, Post; and
`2⁻¹²⁸` for the verifier's `H₂³` input unqueried). `q`, `qE`, `n` the derived provers' budgets. -/
noncomputable def sfailSimEps (q : Kind → ℕ) (qE n ℓ : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ adaptKinds, ((q k : ℝ≥0∞) + (ℓ + 1) * ((extractorQueries + verifierQueries) k : ℝ≥0∞)) *
      simEpsS (n + (2 + verifierTotal)) (q + extractorQueries + verifierQueries) k +
    (ℓ + 1) * (failEps q qE + (2 ^ 128 : ℝ≥0∞)⁻¹)

set_option exponentiation.threshold 1100 in
/-- **`sfailSimEps` with the chain charges written out**: `2·2⁻¹²⁸` per `H₂³` query of the run
and per forgery, `(q₂₃ + ℓ + 1)·2·2⁻¹²⁸` (U1 has `(q₂₃ + ℓ + 1)·2⁻⁷¹` here); KOS and the combined
`H₂²` bound as for U1; the hits, statement hits and order hits; and the failure terms per forgery. -/
theorem sfailSimEps_eq (q : Kind → ℕ) (qE n ℓ : ℕ) :
    sfailSimEps q qE n ℓ =
      ((q .h21 : ℝ≥0∞) + (ℓ + 1)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
      ((q .h22 : ℝ≥0∞) + (ℓ + 1)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
        (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + (2 + verifierTotal) : ℕ) : ℝ≥0∞) / 2 ^ 448) +
      ((q .h23 : ℝ≥0∞) + (ℓ + 1)) * ((2 : ℝ≥0∞) / 2 ^ 128) +
      ∑ k ∈ adaptKinds, ((q k : ℝ≥0∞) + (ℓ + 1) * ((extractorQueries + verifierQueries) k : ℝ≥0∞)) *
        (hitEps (q + extractorQueries + verifierQueries)
          (combCount (some (45, dstP)) (q + extractorQueries + verifierQueries)) k +
          stmtEpsD (q + extractorQueries + verifierQueries) k +
          orderEps (q + extractorQueries + verifierQueries) k) +
      (ℓ + 1) * (failEps q qE + (2 ^ 128 : ℝ≥0∞)⁻¹) := by
  unfold sfailSimEps
  congr 1
  have hsplit : ∀ k, simEpsS (n + (2 + verifierTotal)) (q + extractorQueries + verifierQueries) k =
      cellEpsS (n + (2 + verifierTotal)) k +
        (hitEps (q + extractorQueries + verifierQueries)
          (combCount (some (45, dstP)) (q + extractorQueries + verifierQueries)) k +
          stmtEpsD (q + extractorQueries + verifierQueries) k +
          orderEps (q + extractorQueries + verifierQueries) k) := fun k => by
    simp only [simEpsS, add_assoc]
  simp only [hsplit, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [adaptKinds]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [cellEpsS, Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self,
    ↓reduceIte, add_zero, mul_zero, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
  ring

set_option exponentiation.threshold 1100 in
/-- **One derived game's charges, summed**: the per-query charges over all its queries, with the
failure terms, are `someEps` (`pomfritT_accept_le_some`'s bound) plus the order hits at `H₂¹`. -/
theorem sum_simEpsS_eq (q : Kind → ℕ) (qE n : ℕ) :
    ∑ k ∈ adaptKinds, ((q + extractorQueries + verifierQueries) k : ℝ≥0∞) *
        simEpsS (n + (2 + verifierTotal)) (q + extractorQueries + verifierQueries) k +
      failEps q qE =
      someEps q qE n + ((q + extractorQueries + verifierQueries) .h21 : ℝ≥0∞) *
        orderEps (q + extractorQueries + verifierQueries) .h21 := by
  simp only [adaptKinds]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [simEpsS, cellEpsS, hitEps, stmtEpsD, orderEps, combCount, someEps, failEps,
    chainHitEpsComb, chainHitEps, stmtBindEpsD, Pi.add_apply, extractorQueries, verifierQueries,
    reduceCtorEq, or_self, false_or, or_false, ↓reduceIte, add_zero, zero_add, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv]
  ring

/-- **The simultaneous bound is never worse than the union bound**:
`sfailSimEps ≤ (ℓ + 1)·sfailEps` (`prEvent_shiftFail_le`'s bound). The shared queries `q k` are
charged once instead of `ℓ + 1` times; Post and the chain hits are no longer charged twice. -/
theorem sfailSimEps_le (q : Kind → ℕ) (qE n ℓ : ℕ) :
    sfailSimEps q qE n ℓ ≤ (ℓ + 1) * sfailEps q qE n := by
  set n'' := q + extractorQueries + verifierQueries
  set ε := simEpsS (n + (2 + verifierTotal)) n''
  have h1 : ∑ k ∈ adaptKinds, ((q k : ℝ≥0∞) + (ℓ + 1) *
      ((extractorQueries + verifierQueries) k : ℝ≥0∞)) * ε k ≤
      (ℓ + 1) * ∑ k ∈ adaptKinds, (n'' k : ℝ≥0∞) * ε k := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    have hn : (n'' k : ℝ≥0∞) = q k + ((extractorQueries + verifierQueries) k : ℝ≥0∞) := by
      simp only [n'', Pi.add_apply, Nat.cast_add, add_assoc]
    rw [hn, mul_add]
    exact add_le_add (le_mul_of_one_le_left zero_le le_add_self) le_rfl
  have h2 : ((n'' .h21 : ℝ≥0∞)) * orderEps n'' .h21 ≤
      ∑ k ∈ hitKinds, (n'' k : ℝ≥0∞) * (hitEps n'' (combCount cbP n'') k + orderEps n'' k) :=
    (mul_le_mul_of_nonneg_left le_add_self zero_le).trans
      (Finset.single_le_sum (f := fun k => (n'' k : ℝ≥0∞) *
        (hitEps n'' (combCount cbP n'') k + orderEps n'' k)) (fun _ _ => zero_le)
        (by decide : Kind.h21 ∈ hitKinds))
  calc sfailSimEps q qE n ℓ
      ≤ (ℓ + 1) * ∑ k ∈ adaptKinds, (n'' k : ℝ≥0∞) * ε k +
          (ℓ + 1) * (failEps q qE + (2 ^ 128 : ℝ≥0∞)⁻¹) := add_le_add h1 le_rfl
    _ = (ℓ + 1) * ((∑ k ∈ adaptKinds, (n'' k : ℝ≥0∞) * ε k + failEps q qE) +
          (2 ^ 128 : ℝ≥0∞)⁻¹) := by rw [← mul_add, add_assoc]
    _ = (ℓ + 1) * ((someEps q qE n + (n'' .h21 : ℝ≥0∞) * orderEps n'' .h21) +
          (2 ^ 128 : ℝ≥0∞)⁻¹) := by rw [sum_simEpsS_eq]
    _ ≤ (ℓ + 1) * sfailEps q qE n := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        have h3 : someEps q qE n + (2 ^ 128 : ℝ≥0∞)⁻¹ ≤
            someEps q qE n + ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) *
              (2 ^ 256 : ℝ≥0∞)⁻¹) + (2 ^ 128 : ℝ≥0∞)⁻¹ :=
          add_le_add le_self_add le_rfl
        calc someEps q qE n + (n'' .h21 : ℝ≥0∞) * orderEps n'' .h21 + (2 ^ 128 : ℝ≥0∞)⁻¹
            = (someEps q qE n + (2 ^ 128 : ℝ≥0∞)⁻¹) + (n'' .h21 : ℝ≥0∞) * orderEps n'' .h21 := by
              ring
          _ ≤ sfailEps q qE n := add_le_add h3 h2

variable (lr : Bool) (pk : UovPk) (pre : TG → SIss) (A : Forger) (Lst : List TG) (ℓ : ℕ)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **U2's term with simultaneous extraction, for a fixed key and target stream**: over the
cipher table and the hash table, some forgery fails with probability at most `sfailSimEps`. -/
theorem prEvent_shiftFailZ_sim_le (hd : pk.digest.size = 32) {qA : Kind → ℕ} {nA qE QT : ℕ}
    (hA : ForgerBound A qA nA qE QT) :
    Pr{let E ← $ᵗ CTable; let z ← (simulateQ randomOracle ((simulateQ (htW (AR := Ans) noHint pre)
        (Acomp CrtGen.tables lr E (hintS lr E) tgts2 pk ℓ A)).run (hs0G Lst))).run' ∅}[
        ∃ i : Fin (ℓ + 1), ShiftFailZ pk i.val z] ≤
      sfailSimEps (qP qA QT ℓ) (eP lr qE ℓ) (nP nA QT ℓ) ℓ := by
  classical
  set q := qP qA QT ℓ
  set e := eP lr qE ℓ
  set ε := simEpsS (nP nA QT ℓ + (2 + verifierTotal)) (q + extractorQueries + verifierQueries)
  set c := ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * ε k +
      ∑ _j : Fin (ℓ + 1), ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) * ε k
  have hb : ∀ j : Fin (ℓ + 1), IsKindQueryBoundIC (proverP lr pk pre A Lst j.val) q ∧
      IsQueryBoundP (proverP lr pk pre A Lst j.val) (fun t => t.isLeft = true) (nP nA QT ℓ) ∧
      IsQueryBoundP (proverP lr pk pre A Lst j.val) (fun t => t.isRight = true) e := fun j =>
    proverP_bounds lr pre pk hA Lst (Nat.lt_succ_iff.1 j.isLt)
  have havg := prEvent_avg_le_sum4 _ (fun E z => ∃ i : Fin (ℓ + 1), ShiftFailZ pk i.val z) c
    (Finset.univ : Finset (Fin (ℓ + 1)))
    (fun j E => (simulateQ randomOracle (gameDP lr E pk pre A Lst j.val)).run' ∅)
    (fun E r => bindFailA (stG lr pk) E r) (fun E r => deadOpenA (stG lr pk) E r)
    (fun E r => PostOut E r)
    (fun E r => r.2.2.accept = true ∧
      ((.h23, zOut (stG lr pk (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2)
    (fun E => prEvent_shiftFailZ_sim_le_E lr pk pre A Lst ℓ hd hA E)
  refine havg.trans ?_
  have h3 := sum_fail_le CrtGen.tables (stG lr pk) (pomfritParams lr) (fun _ => rfl)
    (fun j : Fin (ℓ + 1) => proverP lr pk pre A Lst j.val) Finset.univ e (fun j _ => (hb j).2.2) q
    (fun j _ => (hb j).1)
  rw [Finset.sum_add_distrib]
  refine (add_le_add le_rfl (add_le_add h3
    (Finset.sum_le_card_nsmul _ _ (2 ^ 128 : ℝ≥0∞)⁻¹ fun j _ => ?_))).trans_eq ?_
  · exact prEvent_joint_le_of_forall _ _ fun E =>
      prEvent_zUnqueried_le_A CrtGen.tables (stG lr pk) (proverP lr pk pre A Lst j.val) E
  simp only [c, sfailSimEps, Finset.card_univ, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  simp only [add_mul, mul_assoc, mul_add]
  ring

end Joint

section Game

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (lr : Bool) (A : Forger)

/-- **U2's term with simultaneous extraction** (`pomfrit.md` §6.2, §6.4, G8): in PomFRIT's
one-more game with U2's shift rule (`hintS`), for a key generation whose public keys have 32-byte
digests and a forger with budget `qA`, `nA`, `qE`, `Q_T`, some forgery `i ≤ ℓ` is accepted with a
claim that is a preimage of none of its shifted targets with probability at most `sfailSimEps`, for
any number `n` of targets. Each query of the forger's run is charged once (`prEvent_shiftFail_le`
charges it once per forgery). -/
theorem prEvent_shiftFail_sim_le (n ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) :
    Pr{let r ← game KG pre n ℓ CrtGen.tables lr A noHint (hintS lr) tgts2}[
        ∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val r] ≤
      sfailSimEps (qP qA QT ℓ) (eP lr qE ℓ) (nP nA QT ℓ) ℓ := by
  unfold game omuf advC
  simp only [bind_assoc, pure_bind]
  apply prEvent_bind_le_of_forall_le_of_support KG _ (fun r => ∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val r)
  intro kp hkp
  rw [eqd_swap ($ᵗ CTable) (unifList TG n) (fun E L => (do
    let r ← (simulateQ (realImpl noHint (pre kp.2))
      (Acomp CrtGen.tables lr E (hintS lr E) tgts2 kp.1 ℓ A)).run (fun _ => none, ch0 L)
    pure (kp.1, r.1, r.2))) (fun r => ∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val r)]
  apply prEvent_bind_le_of_forall_le _ _ (fun r => ∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val r)
  intro L
  refine le_trans (le_of_eq ?_) (prEvent_shiftFailZ_sim_le lr kp.1 (pre kp.2) A L ℓ (hdig kp hkp) hA)
  have key : ∀ E : CTable, (simulateQ (realImpl noHint (pre kp.2))
      (Acomp CrtGen.tables lr E (hintS lr E) tgts2 kp.1 ℓ A)).run (fun _ => none, ch0 L) =
      (fun z => (z.1.1, (z.1.2.1, chOf z.1.2.2 z.2))) <$>
        (simulateQ randomOracle ((simulateQ (htW (AR := Ans) noHint (pre kp.2))
          (Acomp CrtGen.tables lr E (hintS lr E) tgts2 kp.1 ℓ A)).run (hs0G L))).run ∅ := fun E =>
    realImpl_run_eq noHint (pre kp.2) _ (fun _ => none) (ch0 L)
  simp only [key, StateT.run'_eq, map_bind, Functor.map_map, bind_pure_comp]
  have hev : ∀ a : ((List (ByteArray × SIss) × Bool) × HTSG (List TG)) × (specR Ans).QueryCache,
      (∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val (kp.1, a.1.1, a.1.2.1, chOf a.1.2.2 a.2)) =
        (∃ i : Fin (ℓ + 1), ShiftFailZ kp.1 i.val a.1) := fun a => rfl
  simp only [hev]

/-- **Theorem U2 with simultaneous extraction** (`pomfrit.md` §6.2, §6.4; G8): for a key
generation with 32-byte key digests, any Issuer and a forger with budget `qA`, `nA`, `qE`, `Q_T`,
with U2's shift rule (`hintS`, at most `17` shifts per request),

    Pr[PomWin] ≤ Adv^{ompr⊕17}(red …; Q_T + ℓ + 1, ℓ) + sfailSimEps(q', q_E', n', ℓ),

the forger's run charged once, each forgery's extraction, verification and failure terms once per
forgery (`pomfrit_U2_explicit` has `(ℓ + 1)·sfailEps` instead). No `2⁻⁷¹` term. -/
theorem pomfrit_U2_sim (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A noHint (hintS lr) tgts2}[PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre (QT + (ℓ + 1))
          (red noHint (advC ℓ CrtGen.tables lr A (hintS lr) tgts2))}[
        Wins ℓ (goodShift BAVC.tau relP) r.1 r.2.1 r.2.2] +
      sfailSimEps (qP qA QT ℓ) (eP lr qE ℓ) (nP nA QT ℓ) ℓ :=
  (pomfrit_U2_bound KG pre ℓ QT CrtGen.tables lr A BAVC.tau (shP lr) hA.ht).trans
    (add_le_add le_rfl (prEvent_shiftFail_sim_le KG pre lr A _ ℓ hdig hA))

end Game


end VoleMole.ROM.OneMore.Pomfrit
