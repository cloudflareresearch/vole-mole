import VoleMole.ROM.OneMoreClsGame

/-!
# U1^cls's term with simultaneous extraction (gap G8-cls)

`lean/docs/security/pomfrit.md` §6.4. `ROM/OneMoreLemmaPSim.lean` with the class extractor: the
per-query bad event is Lemma P^cls's (`pomBadC`, with the parallelism event at `H₂¹` and `2⁵⁰`
accepted `chal3` at `H₂³`) or an order hit (`simBadC`); a failed forgery of the game with the
wrapped forger and `E₁^cls` traces to a bad query of the last derived prover's run (charged once),
of its own extraction and verification, or to its failure events (`clsFail_events`,
`pomBadC_trace`). The failure events of the wrapped forger's derived games (binding, an opened dead
leaf, Post) are those of the forger's (`events_wrapE`).

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

/-- **Lemma P^cls's per-query bad event in the derived game of `P`, with the order hit**:
`pomBadC` (the statement committed at the query, the parallelism event at `H₂¹`, chain hits,
statement hits) or an order hit. -/
def simBadC {β : Type} (P : OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × β)))
    (t : Dom) (g : Table) : Prop :=
  pomBadC pk hG (fun s => s.2.1) (fun s => s.2.2) lr CrtGen.tables P E (2 ^ 50) t g ∨
    orderHitL (tableQueryLog (gameA CrtGen.tables (stG lr pk) P E)) t g

set_option maxRecDepth 4000 in
/-- **At a query of the shorter run, the bad events agree** for two provers whose logs extend one
another. -/
theorem simBadC_prefix_congr {β : Type}
    (P P' : OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × β))) (g : Table)
    (t : Dom) (ht : t ∈ (tableQueryLog (runE E P) g).map Sigma.fst)
    (hH : ∃ Y, tableQueryLog (runE E P') g = tableQueryLog (runE E P) g ++ Y)
    (hJ : ∃ Y, jOf g P' E = jOf g P E ++ Y) :
    simBadC lr pk E P t g ↔ simBadC lr pk E P' t g := by
  let _ : HasPrg := icPrg E.cipher
  set stF := stT pk hG (fun s : TG × ByteArray × ByteArray => s.2.1) (fun s => s.2.2) lr
  obtain ⟨hA, -, hJ'⟩ := logBefore_prefix CrtGen.tables stF E P P' g ht hH hJ
  have hA' : logBefore t (gLogA CrtGen.tables stF P E g) =
      logBefore t (gLogA CrtGen.tables stF P' E g) := hA
  have hpar : parBadA pk hG (fun s : TG × ByteArray × ByteArray => s.2.1) (fun s => s.2.2) lr
      CrtGen.tables P E t g ↔ parBadA pk hG (fun s : TG × ByteArray × ByteArray => s.2.1)
        (fun s => s.2.2) lr CrtGen.tables P' E t g := by
    clear ht hH hJ
    obtain ⟨k, x⟩ := t
    cases k
    case h21 =>
      unfold parBadA
      simp only [parBad]
      have hp : preOfA CrtGen.tables stF P E (stKT pk hG (fun s => s.2.1) (fun s => s.2.2) lr none)
          x g = preOfA CrtGen.tables stF P' E (stKT pk hG (fun s => s.2.1) (fun s => s.2.2) lr none)
          x g := by
        unfold preOfA; rw [hA', hJ']
      rw [hp]
    all_goals simp [parBadA, parBad]
  unfold simBadC pomBadC
  rw [hpar]
  refine or_congr (or_congr ?_ Iff.rfl) ?_
  swap
  · unfold orderHitL; rw [stG_eq_stT, hA]
  unfold pomBad combBadF chainHitL stmtHitD
  rw [stmtAtD_congr _ _ hA', hA]
  refine or_congr (exists_congr fun o => and_congr_right fun _ => ?_) Iff.rfl
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

/-- The chain charges of Lemma P^cls per kind: KOS and parallelism at `H₂¹`, the combined `H₂²`
bound, `2⁵⁰` accepted `chal3` at `H₂³`. -/
noncomputable def cellEpsC (ntot : ℕ) : Kind → ℝ≥0∞
  | .h21 => (2 ^ 150 : ℝ≥0∞)⁻¹ + (2 ^ 134 : ℝ≥0∞)⁻¹
  | .h22 => ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) + (2 ^ 128 : ℝ≥0∞)⁻¹ +
      (ntot : ℝ≥0∞) / 2 ^ 448
  | .h23 => (2 ^ 50 : ℝ≥0∞) / 2 ^ 128
  | _ => 0

/-- **The per-query charge of `simBadC`**. -/
noncomputable def simEpsC (ntot : ℕ) (n : Kind → ℕ) (k : Kind) : ℝ≥0∞ :=
  cellEpsC ntot k + (hitEps n (combCount (some (45, dstP)) n) k + stmtEpsD n k) + orderEps n k

lemma simEpsC_eq_zero (ntot : ℕ) (n : Kind → ℕ) (k : Kind) (hk : k ∉ adaptKinds) :
    simEpsC ntot n k = 0 := by
  cases k <;> simp_all [adaptKinds, simEpsC, cellEpsC, hitEps, stmtEpsD, orderEps]

lemma pomEpsC_le_cellEpsC (ntot : ℕ) (n : Kind → ℕ) (k : Kind) :
    pomEpsC pk hG (fun s : TG × ByteArray × ByteArray => s.2.1) (fun s => s.2.2) lr 1313
        (2 ^ 128 : ℝ≥0∞)⁻¹ ntot (2 ^ 50) n k ≤
      cellEpsC ntot k + (hitEps n (combCount (some (45, dstP)) n) k + stmtEpsD n k) := by
  unfold pomEpsC pomEps
  cases k
  case h21 =>
    simp only [cellEpsC, chainEps, parEpsK, reduceCtorEq, ite_false]
    have hkos : epsKOS #chal3Blocks (Chain.kosL (stKT pk hG (fun s : TG × ByteArray × ByteArray =>
        s.2.1) (fun s => s.2.2) lr none)) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
      epsKOS_chal3Blocks_le _ (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])
        (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])
    have hpar : parEps (Chain.kosL (stKT pk hG (fun s : TG × ByteArray × ByteArray => s.2.1)
        (fun s => s.2.2) lr none)) ≤ (2 ^ 134 : ℝ≥0∞)⁻¹ :=
      parEps_le (by
        cases lr <;>
          norm_num [Chain.kosL, stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams,
            Params.correctionRows, Params.witnessBits])
    calc _ = epsKOS #chal3Blocks (Chain.kosL (stKT pk hG (fun s : TG × ByteArray × ByteArray =>
          s.2.1) (fun s => s.2.2) lr none)) + parEps (Chain.kosL (stKT pk hG
            (fun s : TG × ByteArray × ByteArray => s.2.1) (fun s => s.2.2) lr none)) +
          (hitEps n (combCount (some (45, dstP)) n) .h21 + stmtEpsD n .h21) := by ring
      _ ≤ _ := by gcongr
  all_goals norm_num [cellEpsC, chainEps, parEpsK]

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **The per-query bound of `simBadC`** (cache form), for a prover with `q k` hash queries of
kind `k`. -/
theorem prEvent_simBadC_le {β : Type}
    (P : OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × β))) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) (K : Finset Dom) [SampleableType ((d : K) → Ans d.val)]
    (hK : ∀ u, combKey 45 dstP u ∈ K) (ntot : ℕ)
    (c : (ofFn fun d : K => Ans d.val).QueryCache) (t : K) (hc : c t = none)
    (hcard : (cachedKeys c).card < ntot) :
    Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[
      simBadC lr pk E P t.val (extendTable K (completeTable c g))] ≤
      simEpsC ntot (q + extractorQueries + verifierQueries) t.val.1 := by
  classical
  unfold simBadC simEpsC
  refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
  · refine (prEvent_pomBadC_le pk hG (fun s => s.2.1) (fun s => s.2.2) lr CrtGen.tables P E
      liftInvOk_tables (2 ^ 50) (n' := 1313)
      (fun o c1 l => (PomFRIT.pomfritRedeemSystem_length _ _ _ _ _ _ _).trans (by norm_num))
      (εc := (2 ^ 128 : ℝ≥0∞)⁻¹)
      (fun o c1 w => prU_comb_bad_le _ _ w fun hW => pomfrit_comb_bad_gf128 _ _ _ _ w hW)
      q hq K hK ntot c t hc hcard).trans ?_
    exact pomEpsC_le_cellEpsC lr pk ntot _ _
  · refine prEvent_completeTable_cell_le c _ hc
      (fun t G => orderHitL (tableQueryLog (gameA CrtGen.tables (stG lr pk) P E)) t.val
        (extendTable K G)) _ fun G => ?_
    simp only [extendTable_update]
    exact prEvent_orderHitL_le _ _ (isKindQueryBound_gameA CrtGen.tables (stG lr pk) P E hq) _ _

end Bad

/-! ## Prefix runs -/

section Refresh

variable (g : Table) (lr : Bool) (E : CTable) (pk : UovPk) (pre : TG → SIss) (A : Forger)
  (Lst : List TG) (ℓ : ℕ)

/-- `prefix_of_pfail` for the hint `E₁^cls`. -/
theorem prefix_of_clsFail {i : ℕ} (hiℓ : i ≤ ℓ)
    (h : PFailZ pk i (evalWithAnswerFn (QueryImpl.ofFn g)
      ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
        (Acomp CrtGen.tables lr E (e1C lr E) tgts1 pk ℓ A)).run (hs0 Lst)))) :
    (∃ Y, tableQueryLog (runE E (proverP lr pk pre A Lst ℓ)) g =
      tableQueryLog (runE E (proverP lr pk pre A Lst i)) g ++ Y) ∧
    ∃ Y, jOf g (proverP lr pk pre A Lst ℓ) E = jOf g (proverP lr pk pre A Lst i) E ++ Y := by
  obtain ⟨hi, -, hrf⟩ := pfail_refresh g CrtGen.tables lr E (e1C lr E) pk pre A Lst ℓ i h
  have hinv0 : InvH (e1C lr E) (hs0 Lst) (hs0 Lst) (fun _ => none) :=
    ⟨SameT.refl _, fun x a e hx => by simp [hs0] at hx⟩
  obtain ⟨e1, -, -, -⟩ := eval_wrapIC_hint g E lr (e1C lr E) pre (A pk) [] _ _ _ hinv0
  rw [e1] at hi hrf
  have hJ := jOf_proverP_prefix g lr E pk pre A Lst hiℓ hi hrf
  exact ⟨runE_proverP_prefix g lr E pk pre A Lst hJ, hJ⟩

end Refresh

/-! ## The simultaneous bound, per cipher table -/

section SimE

variable (lr : Bool) (pk : UovPk) (pre : TG → SIss) (A : Forger) (Lst : List TG) (ℓ : ℕ)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **U1^cls's term with simultaneous extraction, for fixed key, target stream and cipher table**,
for a forger whose log covers the decoder (`prEvent_pfailZ_sim_le_Ec` with `E₁^cls`), with a
failure event `cf` guarding `KeysPre` in place of Post (`prEvent_clsFailZ_sim_le_E` is
`cf = PostOut E`): the queries of the last derived prover's run (which extends every derived
prover's run where a forgery fails) are charged once, each forgery's extraction and verification
queries once per forgery, and each forgery's failure events. -/
theorem prEvent_clsFailZ_sim_le_Ec (hd : pk.digest.size = 32) {qA : Kind → ℕ} {nA qE QT : ℕ}
    (hA : ForgerBound A qA nA qE QT) (E : CTable)
    (cf : Out (((TG × ByteArray × ByteArray) × AuxP) × QueryLog specIC) → Prop)
    (hcf : ∀ j : Fin (ℓ + 1), ∀ s g', ¬cf (evalWithAnswerFn (QueryImpl.ofFn g')
        (gameIC CrtGen.tables (stG lr pk s) (proverP lr pk pre A Lst j.val) E)) →
      KeysPre (stG lr pk s) E (jOf g' (proverP lr pk pre A Lst j.val) E)
        (gLog CrtGen.tables (stG lr pk s) (proverP lr pk pre A Lst j.val) E g') g')
    (hcovA : ∀ g, CovL lr E g (evalWithAnswerFn (QueryImpl.ofFn (join g E))
      ((simulateQ (wrapIC lr hintVoid pre) (A pk)).run ([], hs0 Lst, fun _ => none))).2.1) :
    let q := qP qA QT ℓ
    let ε := simEpsC (nP nA QT ℓ + (2 + verifierTotal)) (q + extractorQueries + verifierQueries)
    Pr{let z ← (simulateQ randomOracle ((simulateQ (htW (AR := Ans) addHint pre)
        (Acomp CrtGen.tables lr E (e1C lr E) tgts1 pk ℓ A)).run (hs0 Lst))).run' ∅}[
        ∃ i : Fin (ℓ + 1), PFailZ pk i.val z] ≤
      ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * ε k +
      ∑ _j : Fin (ℓ + 1), ∑ k ∈ adaptKinds,
        ((extractorQueries + verifierQueries) k : ℝ≥0∞) * ε k +
      ∑ j : Fin (ℓ + 1), Pr{let r ← (simulateQ randomOracle
        (gameDP lr E pk pre A Lst j.val)).run' ∅}[failPc lr pk E cf r] := by
  classical
  intro q ε
  set n := nP nA QT ℓ
  set P : ℕ → OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × AuxP)) :=
    fun i => proverP lr pk pre A Lst i with hPdef
  set P₀ := P ℓ
  set oa := (simulateQ (htW (AR := Ans) addHint pre)
    (Acomp CrtGen.tables lr E (e1C lr E) tgts1 pk ℓ A)).run (hs0 Lst)
  set stF := stG lr pk
  have hb : ∀ j : Fin (ℓ + 1), IsKindQueryBoundIC (P j.val) q ∧
      IsQueryBoundP (P j.val) (fun t => t.isLeft = true) n ∧
      IsQueryBoundP (P j.val) (fun t => t.isRight = true) (eP lr qE ℓ) := fun j =>
    proverP_bounds lr pre pk hA Lst (Nat.lt_succ_iff.1 j.isLt)
  have hb₀ := proverP_bounds lr pre pk hA Lst (le_refl ℓ)
  have hK : ∀ k ∉ adaptKinds, ε k = 0 := simEpsC_eq_zero _ _
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
  have htr : ∀ g, (∃ i : Fin (ℓ + 1), PFailZ pk i.val (evalWithAnswerFn (QueryImpl.ofFn g) oa)) →
      (∃ e ∈ tableQueryLog (runE E P₀) g, simBadC lr pk E P₀ e.1 g) ∨
      (∃ j ∈ (Finset.univ : Finset (Fin (ℓ + 1))), ∃ e ∈ tableQueryLog (gameK CrtGen.tables stF E id
          (evalWithAnswerFn (QueryImpl.ofFn g) (runE E (P j.val)))) g,
        e.1 ∉ (tableQueryLog (runE E (P j.val)) g).map Sigma.fst ∧ simBadC lr pk E (P j.val) e.1 g) ∨
      (∃ j ∈ (Finset.univ : Finset (Fin (ℓ + 1))),
        failPc lr pk E cf
          (evalWithAnswerFn (QueryImpl.ofFn g) (gameDP lr E pk pre A Lst j.val))) := by
    intro g hev
    obtain ⟨i, hi⟩ := hev
    have hiℓ : i.val ≤ ℓ := Nat.lt_succ_iff.1 i.isLt
    have hev4 := clsFail_events_of g lr E pk pre A Lst ℓ i.val cf (hcf i) hd (hcovA g) hi
    obtain ⟨hH, hJ⟩ := prefix_of_clsFail g lr E pk pre A Lst ℓ hiℓ hi
    -- a failure of the `i`-th derived game, or a bad query of its log
    have key : failPc lr pk E cf
        (evalWithAnswerFn (QueryImpl.ofFn g) (gameDP lr E pk pre A Lst i.val)) ∨
        ∃ e ∈ tableQueryLog (gameDP lr E pk pre A Lst i.val) g, simBadC lr pk E (P i.val) e.1 g := by
      rcases hev4 with h0 | h1 | h2 | ⟨e, he, hb'⟩
      · by_cases hf : bindFailA stF E (evalWithAnswerFn (QueryImpl.ofFn g)
            (gameDP lr E pk pre A Lst i.val)) ∨ deadOpenA stF E (evalWithAnswerFn (QueryImpl.ofFn g)
            (gameDP lr E pk pre A Lst i.val)) ∨ cf (evalWithAnswerFn (QueryImpl.ofFn g)
            (gameDP lr E pk pre A Lst i.val))
        · left
          rcases hf with hf | hf | hf
          · exact Or.inl hf
          · exact Or.inr (Or.inl hf)
          · exact Or.inr (Or.inr (Or.inl hf))
        · right
          simp only [not_or] at hf
          obtain ⟨e, he, hbad⟩ := pomBadC_trace pk hG (fun s => s.2.1) (fun s => s.2.2) lr
            CrtGen.tables (P i.val) E liftInvOk_tables (2 ^ 50)
            (fun s => combDetC_pomfritT pk hG (fun s => s.2.1) (fun s => s.2.2) lr E s)
            cf (hcf i) g
            ⟨h0, hf.1, hf.2.1, hf.2.2⟩
          exact ⟨e, he, Or.inl hbad⟩
      · exact Or.inl (Or.inr (Or.inr (Or.inl h1)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h2)))
      · right
        refine ⟨e, he, ?_⟩
        rcases hb' with hb' | hb'
        · exact Or.inl (Or.inl (Or.inr (Or.inl hb')))
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
      exact (simBadC_prefix_congr lr pk E (P i.val) P₀ g e.1 hm hH hJ).1 hbad
    · exact Or.inr (Or.inl ⟨i, Finset.mem_univ _, e,
        (List.mem_append.1 he).resolve_left fun h => hm (List.mem_map_of_mem h), hm, hbad⟩)
  have key := prEvent_le_shared_suffix (D := Dom) (R := Ans) S oa
    (fun z => ∃ i : Fin (ℓ + 1), PFailZ pk i.val z) hSo (runE E P₀) hSA (fun t => ε t.1) _ hcA n
    (isTotalQueryBound_runE E hb₀.2.1) (simBadC lr pk E P₀) Finset.univ
    (fun j : Fin (ℓ + 1) => runE E (P j.val)) (fun _ => gameK CrtGen.tables stF E id)
    (fun j _ => by rw [← gameA_eq_bind]; exact hSG j)
    (∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) * ε k)
    (fun _ a => worstCaseCostBound_of_kindQueryBound _ adaptKinds ε hK _
      (isKindQueryBound_gameK CrtGen.tables stF E id a)) n (2 + verifierTotal)
    (fun j _ => isTotalQueryBound_runE E (hb j).2.1)
    (fun _ a => isTotalQueryBound_gameK CrtGen.tables stF E id a)
    (fun j => simBadC lr pk E (P j.val)) Finset.univ
    (fun j : Fin (ℓ + 1) => gameDP lr E pk pre A Lst j.val) (fun _ r => failPc lr pk E cf r)
    (fun j _ => hSG j) (n + (2 + verifierTotal)) (by omega) le_rfl
    (fun c t hc hcard => prEvent_simBadC_le lr pk E P₀ q hb₀.1 S hKS _ c t hc hcard)
    (fun j _ c t hc hcard => prEvent_simBadC_le lr pk E (P j.val) q (hb j).1 S hKS _ c t hc hcard)
    htr
  exact key

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **U1^cls's term with simultaneous extraction, for fixed key, target stream and cipher table**,
for a forger whose log covers the decoder (`prEvent_pfailZ_sim_le_E` with `E₁^cls`):
the queries of the last derived prover's run (which extends every derived prover's run where a
forgery fails) are charged once, each forgery's extraction and verification queries once per
forgery, and each forgery's failure events. -/
theorem prEvent_clsFailZ_sim_le_E (hd : pk.digest.size = 32) {qA : Kind → ℕ} {nA qE QT : ℕ}
    (hA : ForgerBound A qA nA qE QT) (E : CTable)
    (hcovA : ∀ g, CovL lr E g (evalWithAnswerFn (QueryImpl.ofFn (join g E))
      ((simulateQ (wrapIC lr hintVoid pre) (A pk)).run ([], hs0 Lst, fun _ => none))).2.1) :
    let q := qP qA QT ℓ
    let ε := simEpsC (nP nA QT ℓ + (2 + verifierTotal)) (q + extractorQueries + verifierQueries)
    Pr{let z ← (simulateQ randomOracle ((simulateQ (htW (AR := Ans) addHint pre)
        (Acomp CrtGen.tables lr E (e1C lr E) tgts1 pk ℓ A)).run (hs0 Lst))).run' ∅}[
        ∃ i : Fin (ℓ + 1), PFailZ pk i.val z] ≤
      ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * ε k +
      ∑ _j : Fin (ℓ + 1), ∑ k ∈ adaptKinds,
        ((extractorQueries + verifierQueries) k : ℝ≥0∞) * ε k +
      ∑ j : Fin (ℓ + 1), Pr{let r ← (simulateQ randomOracle
        (gameDP lr E pk pre A Lst j.val)).run' ∅}[failP lr pk E r] :=
  prEvent_clsFailZ_sim_le_Ec lr pk pre A Lst ℓ hd hA E (PostOut E)
    (fun _ _ g' h => keysPre_of_not_postOut CrtGen.tables _ _ E g' h) hcovA

end SimE

/-! ## The joint experiment and the game -/

section Joint

/-- **U1^cls's term with simultaneous extraction, every term explicit**: `pfailSimEps` with
Lemma P^cls's per-query charge `simEpsC`. -/
noncomputable def clsSimEps (q : Kind → ℕ) (qE n ℓ : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ adaptKinds, ((q k : ℝ≥0∞) + (ℓ + 1) * ((extractorQueries + verifierQueries) k : ℝ≥0∞)) *
      simEpsC (n + (2 + verifierTotal)) (q + extractorQueries + verifierQueries) k +
    (ℓ + 1) * (failEps q qE + (2 ^ 128 : ℝ≥0∞)⁻¹)

set_option exponentiation.threshold 1100 in
/-- **`clsSimEps` with the chain charges written out**: Lemma P^cls's `2⁵⁰·2⁻¹²⁸ = 2⁻⁷⁸` per `H₂³`
query of the run and per forgery (`(q₂₃ + ℓ + 1)·2⁻⁷⁸`, the paper's `(Q₃ + ℓ + 1)·2⁻⁷⁸`), the
parallelism term `2⁻¹³⁴` next to KOS's `2⁻¹⁵⁰` per `H₂¹` query (`(q₂₁ + ℓ + 1)·2⁻¹³⁴`); the
combined `H₂²` bound; the hits, statement hits and order hits; and the failure terms per
forgery. -/
theorem clsSimEps_eq (q : Kind → ℕ) (qE n ℓ : ℕ) :
    clsSimEps q qE n ℓ =
      ((q .h21 : ℝ≥0∞) + (ℓ + 1)) * ((2 ^ 150 : ℝ≥0∞)⁻¹ + (2 ^ 134 : ℝ≥0∞)⁻¹) +
      ((q .h22 : ℝ≥0∞) + (ℓ + 1)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
        (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + (2 + verifierTotal) : ℕ) : ℝ≥0∞) / 2 ^ 448) +
      ((q .h23 : ℝ≥0∞) + (ℓ + 1)) * ((2 ^ 50 : ℝ≥0∞) / 2 ^ 128) +
      ∑ k ∈ adaptKinds, ((q k : ℝ≥0∞) + (ℓ + 1) * ((extractorQueries + verifierQueries) k : ℝ≥0∞)) *
        (hitEps (q + extractorQueries + verifierQueries)
          (combCount (some (45, dstP)) (q + extractorQueries + verifierQueries)) k +
          stmtEpsD (q + extractorQueries + verifierQueries) k +
          orderEps (q + extractorQueries + verifierQueries) k) +
      (ℓ + 1) * (failEps q qE + (2 ^ 128 : ℝ≥0∞)⁻¹) := by
  unfold clsSimEps
  congr 1
  have hsplit : ∀ k, simEpsC (n + (2 + verifierTotal)) (q + extractorQueries + verifierQueries) k =
      cellEpsC (n + (2 + verifierTotal)) k +
        (hitEps (q + extractorQueries + verifierQueries)
          (combCount (some (45, dstP)) (q + extractorQueries + verifierQueries)) k +
          stmtEpsD (q + extractorQueries + verifierQueries) k +
          orderEps (q + extractorQueries + verifierQueries) k) := fun k => by
    simp only [simEpsC, add_assoc]
  simp only [hsplit, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [adaptKinds]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [cellEpsC, Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self,
    ↓reduceIte, add_zero, mul_zero, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
  ring

variable (lr : Bool) (pk : UovPk) (pre : TG → SIss) (A : Forger) (Lst : List TG) (ℓ : ℕ)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **U1^cls's term with simultaneous extraction, for a fixed key and target stream**: over the
cipher table and the hash table, some forgery of the game with the wrapped forger and `E₁^cls`
fails with probability at most `clsSimEps`, at the wrapped forger's derived-prover budgets. -/
theorem prEvent_clsFailZ_sim_le (hd : pk.digest.size = 32) {qA : Kind → ℕ} {nA qE QT : ℕ}
    (hA : ForgerBound A qA nA qE QT) {Nd : ℕ}
    (hW : ∀ E, ForgerBound (wrapE lr E A) (qW qA Nd) (nW nA qA Nd) qE QT) :
    Pr{let E ← $ᵗ CTable; let z ← (simulateQ randomOracle ((simulateQ (htW (AR := Ans) addHint pre)
        (Acomp CrtGen.tables lr E (e1C lr E) tgts1 pk ℓ (wrapE lr E A))).run (hs0 Lst))).run' ∅}[
        ∃ i : Fin (ℓ + 1), PFailZ pk i.val z] ≤
      clsSimEps (qP (qW qA Nd) QT ℓ) (eP lr qE ℓ) (nP (nW nA qA Nd) QT ℓ) ℓ := by
  classical
  set q := qP (qW qA Nd) QT ℓ
  set e := eP lr qE ℓ
  set ε := simEpsC (nP (nW nA qA Nd) QT ℓ + (2 + verifierTotal))
    (q + extractorQueries + verifierQueries)
  set c := ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * ε k +
      ∑ _j : Fin (ℓ + 1), ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) * ε k
  have hb0 : ∀ j : Fin (ℓ + 1), IsKindQueryBoundIC (proverP lr pk pre A Lst j.val) q ∧
      IsQueryBoundP (proverP lr pk pre A Lst j.val) (fun t => t.isRight = true) e := fun j => by
    have h := proverP_bounds lr pre pk hA Lst (Nat.lt_succ_iff.1 j.isLt)
    refine ⟨h.1.mono fun k => ?_, h.2.2⟩
    simp only [q, qP, qW, Pi.add_apply]; omega
  have havg := prEvent_avg_le_sum4 _ (fun E z => ∃ i : Fin (ℓ + 1), PFailZ pk i.val z) c
    (Finset.univ : Finset (Fin (ℓ + 1)))
    (fun j E => (simulateQ randomOracle (gameDP lr E pk pre (wrapE lr E A) Lst j.val)).run' ∅)
    (fun E r => bindFailA (stG lr pk) E r) (fun E r => deadOpenA (stG lr pk) E r)
    (fun E r => PostOut E r)
    (fun E r => r.2.2.accept = true ∧
      ((.h23, zOut (stG lr pk (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2)
    (fun E => prEvent_clsFailZ_sim_le_E lr pk pre (wrapE lr E A) Lst ℓ hd (hW E) E
      fun g => (eval_wrapE g E lr pre A pk (hs0 Lst)).2.2.2)
  refine havg.trans ?_
  have htr : ∀ j : Fin (ℓ + 1),
      Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
          (gameDP lr E pk pre (wrapE lr E A) Lst j.val)).run' ∅}[bindFailA (stG lr pk) E r] +
        Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
          (gameDP lr E pk pre (wrapE lr E A) Lst j.val)).run' ∅}[deadOpenA (stG lr pk) E r] +
        Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
          (gameDP lr E pk pre (wrapE lr E A) Lst j.val)).run' ∅}[PostOut E r] ≤
      Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
          (gameA CrtGen.tables (stG lr pk) (proverP lr pk pre A Lst j.val) E)).run' ∅}[
            bindFailA (stG lr pk) E r] +
        Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
          (gameA CrtGen.tables (stG lr pk) (proverP lr pk pre A Lst j.val) E)).run' ∅}[
            deadOpenA (stG lr pk) E r] +
        Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
          (gameA CrtGen.tables (stG lr pk) (proverP lr pk pre A Lst j.val) E)).run' ∅}[
            PostOut E r] := fun j =>
    add_le_add (add_le_add
      (prEvent_transfer _ _ _ _ fun E g h => (events_wrapE g E lr pk pre A Lst j.val).1 h)
      (prEvent_transfer _ _ _ _ fun E g h => (events_wrapE g E lr pk pre A Lst j.val).2.1 h))
      (prEvent_transfer _ _ _ _ fun E g h => (events_wrapE g E lr pk pre A Lst j.val).2.2 h)
  have h3 := (Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin (ℓ + 1)))) => htr j).trans
    (sum_fail_le CrtGen.tables (stG lr pk) (pomfritParams lr) (fun _ => rfl)
      (fun j : Fin (ℓ + 1) => proverP lr pk pre A Lst j.val) Finset.univ e (fun j _ => (hb0 j).2) q
      (fun j _ => (hb0 j).1))
  rw [Finset.sum_add_distrib]
  refine (add_le_add le_rfl (add_le_add h3
    (Finset.sum_le_card_nsmul _ _ (2 ^ 128 : ℝ≥0∞)⁻¹ fun j _ => ?_))).trans_eq ?_
  · exact prEvent_joint_le_of_forall _ _ fun E =>
      prEvent_zUnqueried_le_A CrtGen.tables (stG lr pk) (proverP lr pk pre (wrapE lr E A) Lst j.val) E
  simp only [c, clsSimEps, Finset.card_univ, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  simp only [add_mul, mul_assoc, mul_add]
  ring

end Joint

section Game

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (n ℓ : ℕ) (lr : Bool)

/-- **U1^cls's term with simultaneous extraction in the game** (gap G8-cls): with the wrapped
forger and `E₁^cls`, some forgery fails with probability at most `clsSimEps`, for any number of
targets. -/
theorem prEvent_clsFail_sim_le (A : Forger) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) {Nd : ℕ}
    (hW : ∀ E, ForgerBound (wrapE lr E A) (qW qA Nd) (nW nA qA Nd) qE QT) :
    Pr{let r ← gameE KG pre n ℓ CrtGen.tables lr (fun E => wrapE lr E A) addHint (e1C lr) tgts1}[
        ∃ i : Fin (ℓ + 1), PFail i.val r] ≤
      clsSimEps (qP (qW qA Nd) QT ℓ) (eP lr qE ℓ) (nP (nW nA qA Nd) QT ℓ) ℓ := by
  unfold gameE omuf advCE
  simp only [bind_assoc, pure_bind]
  apply prEvent_bind_le_of_forall_le_of_support KG _ (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)
  intro kp hkp
  rw [eqd_swap ($ᵗ CTable) (unifList TG n) (fun E L => (do
    let r ← (simulateQ (realImpl addHint (pre kp.2))
      (Acomp CrtGen.tables lr E (e1C lr E) tgts1 kp.1 ℓ (wrapE lr E A))).run (fun _ => none, ch0 L)
    pure (kp.1, r.1, r.2))) (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)]
  apply prEvent_bind_le_of_forall_le _ _ (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)
  intro L
  refine le_trans (le_of_eq ?_) (prEvent_clsFailZ_sim_le lr kp.1 (pre kp.2) A L ℓ (hdig kp hkp) hA hW)
  have key : ∀ E : CTable, (simulateQ (realImpl addHint (pre kp.2))
      (Acomp CrtGen.tables lr E (e1C lr E) tgts1 kp.1 ℓ (wrapE lr E A))).run (fun _ => none, ch0 L) =
      (fun z => (z.1.1, (z.1.2.1, chOf z.1.2.2 z.2))) <$>
        (simulateQ randomOracle ((simulateQ (htW (AR := Ans) addHint (pre kp.2))
          (Acomp CrtGen.tables lr E (e1C lr E) tgts1 kp.1 ℓ (wrapE lr E A))).run (hs0 L))).run ∅ :=
    fun E => realImpl_run_eq addHint (pre kp.2) _ (fun _ => none) (ch0 L)
  simp only [key, StateT.run'_eq, map_bind, Functor.map_map, bind_pure_comp]
  have hev : ∀ a : ((List (ByteArray × SIss) × Bool) × HTS) × (specR Ans).QueryCache,
      (∃ i : Fin (ℓ + 1), PFail i.val (kp.1, a.1.1, a.1.2.1, chOf a.1.2.2 a.2)) =
        (∃ i : Fin (ℓ + 1), PFailZ kp.1 i.val a.1) := fun a => rfl
  simp only [hev]

/-- **Theorem U1^cls with simultaneous extraction** (gap G8-cls): for a key generation with
32-byte key digests, any Issuer and a forger `A` with budget `qA`, `nA`, `qE`, `Q_T` whose wrapped
forger has the budget `qW qA Nd`, `nW nA qA Nd`, `qE`, `Q_T`,

    Pr[PomWin(A)] ≤ Adv^{ompr}(red (wrapE, E₁^cls); Q_T + ℓ + 1, ℓ) + clsSimEps(q', q_E', n', ℓ),

`q'`, `q_E'`, `n'` the derived provers' budgets of the wrapped forger (`qP`, `eP`, `nP`). -/
theorem pomfrit_U1_cls_sim (A : Forger) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) {Nd : ℕ}
    (hW : ∀ E, ForgerBound (wrapE lr E A) (qW qA Nd) (nW nA qA Nd) qE QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A addHint (e1C lr) tgts1}[
        PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre (QT + (ℓ + 1)) (red addHint
          (advCE ℓ CrtGen.tables lr (fun E => wrapE lr E A) (e1C lr) tgts1))}[
        Wins ℓ (goodPre relP) r.1 r.2.1 r.2.2] +
      clsSimEps (qP (qW qA Nd) QT ℓ) (eP lr qE ℓ) (nP (nW nA qA Nd) QT ℓ) ℓ :=
  (pomWin_le_wrapE KG pre _ ℓ lr A).trans ((pomfrit_U1_boundE KG pre ℓ CrtGen.tables lr QT _ (e1C lr)
    fun E => (hW E).ht).trans
    (add_le_add le_rfl (prEvent_clsFail_sim_le KG pre _ ℓ lr A hdig hA hW)))

end Game

end VoleMole.ROM.OneMore.Pomfrit
