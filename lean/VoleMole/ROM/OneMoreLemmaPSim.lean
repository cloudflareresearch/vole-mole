import VoleMole.ROM.OneMoreLemmaPBound
import VoleMole.ROM.OneMoreLemmaPPrefix
import VoleMole.ROM.SimExtract

/-!
# Lemma P's term with simultaneous extraction (gap G8)

`lean/docs/security/pomfrit.md` §6.4, `lean/docs/probabilistic-plan.md` §2m, §2n.
`ROM/OneMoreLemmaPBound.lean` bounds `Pr[∃ i ≤ ℓ, PFail i]` by a union over the `ℓ + 1` forgeries:
each forgery's derived game is charged with every query of the forger's run, so the run is charged
`ℓ + 1` times. Here each query of the run is charged **once**, as in the paper (`ε_ext` once,
L8 §9.1), with `ROM/SimUnion.lean`'s shared-run union bound.

* **The per-query bad event** (`simBadP`): Lemma P's (`pomBad`, `ROM/LemmaP.lean`: a bad query of
  the statement committed there, a chain hit, a statement hit) or an order hit (`orderHitL`), in the
  derived game of a prover. It reads the logs before the query only, so it is the same for two
  provers whose logs extend one another (`simBadP_prefix_congr`).
* **Its per-query bound** (`prEvent_simBadP_le`, `simEps`): `pomEps`, with the parameters of
  PomFRIT (`2⁻¹⁵⁰` at `H₂¹`, `ε_QS + 2⁻¹²⁸ + ntot·2⁻⁴⁴⁸` at `H₂²`, `2⁵⁷·2⁻¹²⁸` at `H₂³`), and the
  order hit's `n₃·2⁻¹⁰⁸⁸` at `H₂¹`.
* **The deterministic step**: a failed forgery `i` (`PFailZ`) gives, at the same tables, a failure
  of the `i`-th derived game (`failP`: binding, an opened dead leaf, Post, the verifier's `H₂³`
  input unqueried) or a bad query of its log (`pfail_events`, `pomBad_trace`). A bad query of the
  derived prover's run is a bad query of the last derived prover's run (`prefix_of_pfail`,
  `ROM/OneMoreLemmaPPrefix.lean`), which is charged once.
* **The bounds**: per cipher table (`prEvent_pfailZ_sim_le_E`), joint (`prEvent_pfailZ_sim_le`),
  in the game (`prEvent_pfail_sim_le`), and Theorem U1 (`pomfrit_U1_sim`):

      Pr[PomWin] ≤ Adv^{ompr} + pfailSimEps,
      pfailSimEps = Σ_k (q'_k + (ℓ+1)·r_k)·simEps_k + (ℓ+1)·(failEps(q', q_E') + 2⁻¹²⁸),

  `q'`, `q_E'`, `n'` the derived provers' budgets (`qP`, `eP`, `nP`), `r = extractorQueries +
  verifierQueries` the queries of one extraction and verification, `simEps` at the derived games'
  budget `q' + r`.

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
def simBadP {β : Type} (P : OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × β)))
    (t : Dom) (g : Table) : Prop :=
  pomBad pk hG (fun s => s.2.1) (fun s => s.2.2) lr CrtGen.tables P E (2 ^ 57) t g ∨
    orderHitL (tableQueryLog (gameA CrtGen.tables (stG lr pk) P E)) t g

set_option maxRecDepth 4000 in
/-- **At a query of the shorter run, the bad events agree** for two provers whose logs extend one
another. -/
theorem simBadP_prefix_congr {β : Type}
    (P P' : OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × β))) (g : Table)
    (t : Dom) (ht : t ∈ (tableQueryLog (runE E P) g).map Sigma.fst)
    (hH : ∃ Y, tableQueryLog (runE E P') g = tableQueryLog (runE E P) g ++ Y)
    (hJ : ∃ Y, jOf g P' E = jOf g P E ++ Y) :
    simBadP lr pk E P t g ↔ simBadP lr pk E P' t g := by
  let _ : HasPrg := icPrg E.cipher
  set stF := stT pk hG (fun s : TG × ByteArray × ByteArray => s.2.1) (fun s => s.2.2) lr
  obtain ⟨hA, -, hJ'⟩ := logBefore_prefix CrtGen.tables stF E P P' g ht hH hJ
  have hA' : logBefore t (gLogA CrtGen.tables stF P E g) =
      logBefore t (gLogA CrtGen.tables stF P' E g) := hA
  unfold simBadP pomBad combBadF chainHitL stmtHitD orderHitL
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
combined `H₂²` bound (`ntot` bounds the cached cells), Lemma P's `2⁵⁷` accepted `chal3` at `H₂³`. -/
noncomputable def cellEps (ntot : ℕ) : Kind → ℝ≥0∞
  | .h21 => (2 ^ 150 : ℝ≥0∞)⁻¹
  | .h22 => ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) + (2 ^ 128 : ℝ≥0∞)⁻¹ +
      (ntot : ℝ≥0∞) / 2 ^ 448
  | .h23 => (2 ^ 57 : ℝ≥0∞) / 2 ^ 128
  | _ => 0

/-- **The per-query charge of `simBadP`** in a game with `n k` queries of kind `k`: the chain
charge, the hits, the statement hits and the order hits. -/
noncomputable def simEps (ntot : ℕ) (n : Kind → ℕ) (k : Kind) : ℝ≥0∞ :=
  cellEps ntot k + (hitEps n (combCount (some (45, dstP)) n) k + stmtEpsD n k) + orderEps n k

lemma simEps_eq_zero (ntot : ℕ) (n : Kind → ℕ) (k : Kind) (hk : k ∉ adaptKinds) :
    simEps ntot n k = 0 := by
  cases k <;> simp_all [adaptKinds, simEps, cellEps, hitEps, stmtEpsD, orderEps]

lemma pomEps_le_cellEps (ntot : ℕ) (n : Kind → ℕ) (k : Kind) :
    pomEps pk hG (fun s : TG × ByteArray × ByteArray => s.2.1) (fun s => s.2.2) lr 1313
        (2 ^ 128 : ℝ≥0∞)⁻¹ ntot (2 ^ 57) n k ≤
      cellEps ntot k + (hitEps n (combCount (some (45, dstP)) n) k + stmtEpsD n k) := by
  unfold pomEps
  refine add_le_add ?_ le_rfl
  cases k <;> simp only [cellEps, chainEps, reduceCtorEq, ite_true, ite_false, le_refl,
    Nat.cast_pow, Nat.cast_ofNat]
  exact epsKOS_chal3Blocks_le _ (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])
    (by norm_num [stKT, OneMore.Pomfrit.pomfritRedeemT, pomfritParams])

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **The per-query bound of `simBadP`** (cache form), for a prover with `q k` hash queries of
kind `k`. -/
theorem prEvent_simBadP_le {β : Type}
    (P : OracleComp specIC (ByteArray × ((TG × ByteArray × ByteArray) × β))) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) (K : Finset Dom) [SampleableType ((d : K) → Ans d.val)]
    (hK : ∀ u, combKey 45 dstP u ∈ K) (ntot : ℕ)
    (c : (ofFn fun d : K => Ans d.val).QueryCache) (t : K) (hc : c t = none)
    (hcard : (cachedKeys c).card < ntot) :
    Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[
      simBadP lr pk E P t.val (extendTable K (completeTable c g))] ≤
      simEps ntot (q + extractorQueries + verifierQueries) t.val.1 := by
  classical
  unfold simBadP simEps
  refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
  · refine (prEvent_pomBad_le pk hG (fun s => s.2.1) (fun s => s.2.2) lr CrtGen.tables P E
      liftInvOk_tables (2 ^ 57) (n' := 1313)
      (fun o c1 l => (PomFRIT.pomfritRedeemSystem_length _ _ _ _ _ _ _).trans (by norm_num))
      (εc := (2 ^ 128 : ℝ≥0∞)⁻¹)
      (fun o c1 w => prU_comb_bad_le _ _ w fun hW => pomfrit_comb_bad_gf128 _ _ _ _ w hW)
      q hq K hK ntot c t hc hcard).trans ?_
    exact pomEps_le_cellEps lr pk ntot _ _
  · refine prEvent_completeTable_cell_le c _ hc
      (fun t G => orderHitL (tableQueryLog (gameA CrtGen.tables (stG lr pk) P E)) t.val
        (extendTable K G)) _ fun G => ?_
    simp only [extendTable_update]
    exact prEvent_orderHitL_le _ _ (isKindQueryBound_gameA CrtGen.tables (stG lr pk) P E hq) _ _

end Bad

/-! ## The simultaneous bound, per cipher table -/

section SimE

variable (lr : Bool) (pk : UovPk) (pre : TG → SIss) (A : Forger) (Lst : List TG) (ℓ : ℕ)

/-- **The failure events of a derived game's output** (per forgery): binding, an opened dead leaf,
Post, and the verifier's `H₂³` input unqueried. -/
def failP (E : CTable) (r : Out (((TG × ByteArray × ByteArray) × AuxP) × QueryLog specIC)) :
    Prop :=
  bindFailA (stG lr pk) E r ∨ deadOpenA (stG lr pk) E r ∨ PostOut E r ∨
    (r.2.2.accept = true ∧ ((.h23, zOut (stG lr pk (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Lemma P's term with simultaneous extraction, for fixed key, target stream and cipher table**:
the queries of the last derived prover's run (which extends every derived prover's run where a
forgery fails) are charged once, each forgery's extraction and verification queries once per
forgery, and each forgery's failure events. -/
theorem prEvent_pfailZ_sim_le_E (hd : pk.digest.size = 32) {qA : Kind → ℕ} {nA qE QT : ℕ}
    (hA : ForgerBound A qA nA qE QT) (E : CTable) :
    let q := qP qA QT ℓ
    let ε := simEps (nP nA QT ℓ + (2 + verifierTotal)) (q + extractorQueries + verifierQueries)
    Pr{let z ← (simulateQ randomOracle ((simulateQ (htW (AR := Ans) addHint pre)
        (Acomp CrtGen.tables lr E (e1P lr E) tgts1 pk ℓ A)).run (hs0 Lst))).run' ∅}[
        ∃ i : Fin (ℓ + 1), PFailZ pk i.val z] ≤
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
  set oa := (simulateQ (htW (AR := Ans) addHint pre)
    (Acomp CrtGen.tables lr E (e1P lr E) tgts1 pk ℓ A)).run (hs0 Lst)
  set stF := stG lr pk
  have hb : ∀ j : Fin (ℓ + 1), IsKindQueryBoundIC (P j.val) q ∧
      IsQueryBoundP (P j.val) (fun t => t.isLeft = true) n ∧
      IsQueryBoundP (P j.val) (fun t => t.isRight = true) (eP lr qE ℓ) := fun j =>
    proverP_bounds lr pre pk hA Lst (Nat.lt_succ_iff.1 j.isLt)
  have hb₀ := proverP_bounds lr pre pk hA Lst (le_refl ℓ)
  have hK : ∀ k ∉ adaptKinds, ε k = 0 := simEps_eq_zero _ _
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
      (∃ e ∈ tableQueryLog (runE E P₀) g, simBadP lr pk E P₀ e.1 g) ∨
      (∃ j ∈ (Finset.univ : Finset (Fin (ℓ + 1))), ∃ e ∈ tableQueryLog (gameK CrtGen.tables stF E id
          (evalWithAnswerFn (QueryImpl.ofFn g) (runE E (P j.val)))) g,
        e.1 ∉ (tableQueryLog (runE E (P j.val)) g).map Sigma.fst ∧ simBadP lr pk E (P j.val) e.1 g) ∨
      (∃ j ∈ (Finset.univ : Finset (Fin (ℓ + 1))),
        failP lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (gameDP lr E pk pre A Lst j.val))) := by
    intro g hev
    obtain ⟨i, hi⟩ := hev
    have hiℓ : i.val ≤ ℓ := Nat.lt_succ_iff.1 i.isLt
    have hev4 := pfail_events g lr E pk pre A Lst ℓ i.val hd hi
    obtain ⟨hH, hJ⟩ := prefix_of_pfail g lr E pk pre A Lst ℓ hiℓ hi
    -- a failure of the `i`-th derived game, or a bad query of its log
    have key : failP lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (gameDP lr E pk pre A Lst i.val)) ∨
        ∃ e ∈ tableQueryLog (gameDP lr E pk pre A Lst i.val) g, simBadP lr pk E (P i.val) e.1 g := by
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
          obtain ⟨e, he, hbad⟩ := pomBad_trace pk hG (fun s => s.2.1) (fun s => s.2.2) lr
            CrtGen.tables (P i.val) E liftInvOk_tables (2 ^ 57)
            (fun s => combDetG_pomfritT pk hG (fun s => s.2.1) (fun s => s.2.2) lr E s)
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
      exact (simBadP_prefix_congr lr pk E (P i.val) P₀ g e.1 hm hH hJ).1 hbad
    · exact Or.inr (Or.inl ⟨i, Finset.mem_univ _, e,
        (List.mem_append.1 he).resolve_left fun h => hm (List.mem_map_of_mem h), hm, hbad⟩)
  have key := prEvent_le_shared_suffix (D := Dom) (R := Ans) S oa
    (fun z => ∃ i : Fin (ℓ + 1), PFailZ pk i.val z) hSo (runE E P₀) hSA (fun t => ε t.1) _ hcA n
    (isTotalQueryBound_runE E hb₀.2.1) (simBadP lr pk E P₀) Finset.univ
    (fun j : Fin (ℓ + 1) => runE E (P j.val)) (fun _ => gameK CrtGen.tables stF E id)
    (fun j _ => by rw [← gameA_eq_bind]; exact hSG j)
    (∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) * ε k)
    (fun _ a => worstCaseCostBound_of_kindQueryBound _ adaptKinds ε hK _
      (isKindQueryBound_gameK CrtGen.tables stF E id a)) n (2 + verifierTotal)
    (fun j _ => isTotalQueryBound_runE E (hb j).2.1)
    (fun _ a => isTotalQueryBound_gameK CrtGen.tables stF E id a)
    (fun j => simBadP lr pk E (P j.val)) Finset.univ
    (fun j : Fin (ℓ + 1) => gameDP lr E pk pre A Lst j.val) (fun _ r => failP lr pk E r)
    (fun j _ => hSG j) (n + (2 + verifierTotal)) (by omega) le_rfl
    (fun c t hc hcard => prEvent_simBadP_le lr pk E P₀ q hb₀.1 S hKS _ c t hc hcard)
    (fun j _ c t hc hcard => prEvent_simBadP_le lr pk E (P j.val) q (hb j).1 S hKS _ c t hc hcard)
    htr
  exact key

end SimE

end VoleMole.ROM.OneMore.Pomfrit
