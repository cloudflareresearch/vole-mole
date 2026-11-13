import VoleMole.ROM.SimUnion
import VoleMole.ROM.AdaptComb

/-!
# Simultaneous straight-line extraction for the adaptive games

`ROM/AdaptChain.lean` and `ROM/AdaptComb.lean` bound, for **one** prover `P`, the probability
that the verifier accepts `P`'s proof at the statement `P` chose and the straight-line extractor
fails. A protocol game produces many proofs from **one** run `G` of the adversary and the honest
parties: the `j`-th proof is the output of the prover `proj j <$> G` (Moussaka's `PI`, `PR`).
Adding the single-proof bounds charges every query of `G` once per proof. Here the per-query bad
events of the single-proof bound are charged **once** for the queries of `G`, and per output only
for the extractor's and the verifier's own queries (`ROM/SimUnion.lean`).

* `runE_map`, `gameA_map`: the adaptive game of `f <$> G` is `runE E G` followed by a
  continuation `gameK f` (the extractor and the verifier at the statement `f` chose); its log is
  `G`'s joint run's log followed by the continuation's (`tableQueryLog_gameA_map`).
* `adaptBad_map_congr`, `combAdaptBad_map_congr`: at a query of `G`'s run, the bad events of two
  provers `f <$> G`, `f' <$> G` coincide: they read the logs before the query only, and those
  are `G`'s.
* **`prEvent_sim_le_E`**, **`prEvent_sim_comb_le_E`** (per cipher table): if an event of any
  computation implies, at every table, that some output `j ∈ J` is accepted and not extracted,
  its probability is at most

      Σ_k q_k·ε_k + |J|·Σ_k r_k·ε_k + Σ_{j ∈ J} Pr[bindFail_j ∨ deadOpen_j ∨ cf_j],

  `q` the queries of `G`, `r = extractorQueries + verifierQueries` those of one continuation,
  `ε` the single-proof bound's per-query charge (`adaptEps`, `combAdaptEps`).
* **`prEvent_sim_le`**, **`prEvent_sim_comb_le`** (the joint experiment): averaged over the cipher
  table, with the failure events (binding, an opened dead leaf, Post) bounded per output by the
  single-proof bounds (`prEvent_joint_bindFail_le_A`, `prEvent_joint_deadOpen_le_A`,
  `prEvent_joint_postOut_le_A`).

What stays per output: the verifier's three chain queries and the extractor's (`r`, the paper's
"per-output verification queries"), and the failure events. These are not per-query events of
`G` in the single-proof development (Post, binding and the opened dead leaf are bounded on
average over the cipher table, and the opened dead leaf includes the verifier's fresh `H₂³`
answer), so they keep a factor `|J|`; each is `O(2⁻¹¹⁷)` at `2⁶⁴` queries.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## Provers that are projections of one run -/

section Proj

variable {α γ ι β : Type}

/-- **`runE` of a projection** is the projection of `runE`, with the same joint log. -/
theorem runE_map (E : CTable) (f : γ → α) (G : OracleComp specIC γ) :
    runE E (f <$> G) = (fun r => (f r.1, r.2)) <$> runE E G := by
  induction G using OracleComp.inductionOn with
  | pure a => simp [runE_pure]
  | query_bind t k ih =>
    cases t with
    | inl d =>
      rw [map_bind, runE_inl, runE_inl, map_bind]
      refine congrArg (_ >>= ·) (funext fun u => ?_)
      rw [ih u, Functor.map_map, Functor.map_map]
    | inr x =>
      rw [map_bind, runE_inr, runE_inr, ih (E x), Functor.map_map, Functor.map_map]

theorem tableQueryLog_runE_map (E : CTable) (f : γ → α) (G : OracleComp specIC γ) (g : Table) :
    tableQueryLog (runE E (f <$> G)) g = tableQueryLog (runE E G) g := by
  rw [runE_map, tableQueryLog_map']

theorem jOf_map (E : CTable) (f : γ → ByteArray × β) (G : OracleComp specIC γ) (g : Table) :
    jOf g (f <$> G) E = tableQueryLog G (join g E) := by
  simp only [jOf, tableQueryLog_map']

variable (T : CrtTables) (stF : ι → Statement)

/-- **The continuation of the adaptive game after the run `G`** for the prover `f <$> G`: the
straight-line extractor and the verifier at the statement `f` chose. -/
def gameK (E : CTable) (f : γ → ByteArray × (ι × β)) (r : γ × QueryLog specIC) :
    OracleComp spec (Out ((ι × β) × QueryLog specIC)) :=
  extractIC (stF (f r.1).2.1) E (f r.1, r.2) >>= fun x =>
    (fun t => (x.1, x.2, t)) <$> @verifyQ (icPrg E.cipher) T (stF x.2.aux.1.1) x.1

theorem gameA_map (E : CTable) (f : γ → ByteArray × (ι × β)) (G : OracleComp specIC γ) :
    gameA T stF (f <$> G) E = runE E G >>= gameK T stF E f := by
  simp only [gameA, proverA, runE_map, bind_map_left, bind_assoc]
  rfl

theorem tableQueryLog_gameA_map (E : CTable) (f : γ → ByteArray × (ι × β))
    (G : OracleComp specIC γ) (g : Table) :
    tableQueryLog (gameA T stF (f <$> G) E) g = tableQueryLog (runE E G) g ++
      tableQueryLog (gameK T stF E f (evalWithAnswerFn (QueryImpl.ofFn g) (runE E G))) g := by
  rw [gameA_map, tableQueryLog_bind]

theorem gLog_map (E : CTable) (f : γ → ByteArray × β) (G : OracleComp specIC γ) (st : Statement)
    (g : Table) : ∃ X, gLog T st (f <$> G) E g = tableQueryLog (runE E G) g ++ X := by
  unfold gLog
  rw [gameIC_eq_bind, proverIC_eq_bind, tableQueryLog_bind, tableQueryLog_bind,
    tableQueryLog_runE_map]
  exact ⟨_, List.append_assoc _ _ _⟩

theorem isKindQueryBound_gameK (E : CTable) (f : γ → ByteArray × (ι × β))
    (r : γ × QueryLog specIC) :
    IsKindQueryBound (gameK T stF E f r) (extractorQueries + verifierQueries) :=
  isKindQueryBound_bind (isKindQueryBound_extractIC _ E _) fun x =>
    (isQueryBound_map_iff _ _ _ _ _).2 (@isKindQueryBound_verifyQ (icPrg E.cipher) T _ x.1)

theorem isTotalQueryBound_gameK (E : CTable) (f : γ → ByteArray × (ι × β))
    (r : γ × QueryLog specIC) : IsTotalQueryBound (gameK T stF E f r) (2 + verifierTotal) :=
  isTotalQueryBound_bind (isTotalQueryBound_extractIC _ E _) fun x =>
    (isQueryBound_map_iff _ _ _ _ _).2 (@isTotalQueryBound_verifyQ (icPrg E.cipher) T _ x.1)

end Proj

/-! ## The bad events at a query of the shared run -/

section Congr

variable {γ ι β : Type} (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
  (E : CTable) (G : OracleComp specIC γ)

lemma logBefore_gameA_map (f : γ → ByteArray × (ι × β)) (g : Table) {t : Dom}
    (ht : t ∈ (tableQueryLog (runE E G) g).map Sigma.fst) :
    logBefore t (tableQueryLog (gameA T stF (f <$> G) E) g) =
      logBefore t (tableQueryLog (runE E G) g) := by
  rw [tableQueryLog_gameA_map, logBefore_append_of_mem _ ht]

lemma logBefore_gLog_map (f : γ → ByteArray × β) (st : Statement) (g : Table) {t : Dom}
    (ht : t ∈ (tableQueryLog (runE E G) g).map Sigma.fst) :
    logBefore t (gLog T st (f <$> G) E g) = logBefore t (tableQueryLog (runE E G) g) := by
  obtain ⟨X, hX⟩ := gLog_map T E f G st g
  rw [hX, logBefore_append_of_mem _ ht]

/-- **`chainBad` at a query reads the chain data at that query's input only.** -/
theorem chainBad_congr_at {st : Statement} (C C' : ChainData st) (T : CrtTables)
    (S : Finset Blocks) (N : ℕ) (g : Table) [HasPrg] (k : Kind) (x : ByteArray)
    (hpre : k = .h21 → C.preOf x g = C'.preOf x g)
    (hmid : k = .h22 → C.midOf x g = C'.midOf x g ∧ C.csOf x g = C'.csOf x g)
    (hacc : k = .h23 → C.accOf x g = C'.accOf x g) :
    chainBad C T S N (k, x) g ↔ chainBad C' T S N (k, x) g := by
  cases k
  case h21 => simp only [chainBad]; rw [hpre rfl]
  case h22 => simp only [chainBad, ChainData.wC]; rw [(hmid rfl).1, (hmid rfl).2]
  case h23 => simp only [chainBad]; rw [hacc rfl]
  all_goals simp only [chainBad]

set_option maxRecDepth 4000 in
/-- **At a query of the shared run, the bad events of the issue relations do not depend on which
output the prover projects to.** -/
theorem adaptBad_map_congr (sys : ι → System GF128) (f f' : γ → ByteArray × (ι × β)) (N : ℕ)
    (cb : Option (ℕ × ByteArray)) (g : Table) (t : Dom)
    (ht : t ∈ (tableQueryLog (runE E G) g).map Sigma.fst) :
    adaptBad T stF dec sys (f <$> G) E N cb t g ↔ adaptBad T stF dec sys (f' <$> G) E N cb t g := by
  let _ : HasPrg := icPrg E.cipher
  have hA : logBefore t (tableQueryLog (gameA T stF (f <$> G) E) g) =
      logBefore t (tableQueryLog (gameA T stF (f' <$> G) E) g) := by
    rw [logBefore_gameA_map T stF E G f g ht, logBefore_gameA_map T stF E G f' g ht]
  have hG : ∀ st, logBefore t (gLog T st (f <$> G) E g) = logBefore t (gLog T st (f' <$> G) E g) :=
    fun st => by rw [logBefore_gLog_map T E G f st g ht, logBefore_gLog_map T E G f' st g ht]
  have hJ : jOf g (f <$> G) E = jOf g (f' <$> G) E := by rw [jOf_map, jOf_map]
  unfold adaptBad chainBadA chainHitL stmtHit
  rw [stmtAt_congr dec hA, hA]
  refine or_congr (exists_congr fun s => and_congr_right fun _ => ?_) Iff.rfl
  obtain ⟨k, x⟩ := t
  refine chainBad_congr_at _ _ T chal3Blocks N g k x (fun hk => ?_) (fun hk => ⟨?_, rfl⟩)
    (fun hk => ?_)
  · subst hk
    show preOf T (stF s) (f <$> G) E x g = preOf T (stF s) (f' <$> G) E x g
    unfold preOf
    rw [hG, hJ]
  · subst hk
    show midOf T (stF s) (f <$> G) E x g = midOf T (stF s) (f' <$> G) E x g
    unfold midOf
    rw [hG, hJ]
  · subst hk
    show accOf T (stF s) (f <$> G) E x g = accOf T (stF s) (f' <$> G) E x g
    unfold accOf
    rw [hG, hJ]

set_option maxRecDepth 4000 in
/-- **The same for the combined relations.** -/
theorem combAdaptBad_map_congr {M : ℕ} (sysL : ι → (Fin M → GF128) → System GF128)
    (witL : ι → (ℕ → GF128) → Prop) (dst : ByteArray) (f f' : γ → ByteArray × (ι × β)) (N : ℕ)
    (g : Table) (t : Dom) (ht : t ∈ (tableQueryLog (runE E G) g).map Sigma.fst) :
    combAdaptBad T stF dec (f <$> G) E sysL witL dst N t g ↔
      combAdaptBad T stF dec (f' <$> G) E sysL witL dst N t g := by
  let _ : HasPrg := icPrg E.cipher
  have hA : logBefore t (tableQueryLog (gameA T stF (f <$> G) E) g) =
      logBefore t (tableQueryLog (gameA T stF (f' <$> G) E) g) := by
    rw [logBefore_gameA_map T stF E G f g ht, logBefore_gameA_map T stF E G f' g ht]
  have hA' : logBefore t (gLogA T stF (f <$> G) E g) = logBefore t (gLogA T stF (f' <$> G) E g) :=
    hA
  have hJ : jOf g (f <$> G) E = jOf g (f' <$> G) E := by rw [jOf_map, jOf_map]
  unfold combAdaptBad combBadA chainHitL stmtHit
  rw [stmtAt_congr dec hA', hA]
  refine or_congr (exists_congr fun s => and_congr_right fun _ => ?_) Iff.rfl
  obtain ⟨k, x⟩ := t
  by_cases hk : k = .h22
  · subst hk
    have hmid : (combDataA T stF (f <$> G) E sysL witL dst s).midOf x g =
        (combDataA T stF (f' <$> G) E sysL witL dst s).midOf x g := by
      show midOfA T stF (f <$> G) E (stF s) x g = midOfA T stF (f' <$> G) E (stF s) x g
      unfold midOfA
      rw [hA', hJ]
    have hpre : (combDataA T stF (f <$> G) E sysL witL dst s).pre x g =
        (combDataA T stF (f' <$> G) E sysL witL dst s).pre x g := by
      show preCellsA T stF (f <$> G) E x g = preCellsA T stF (f' <$> G) E x g
      unfold preCellsA
      rw [hA']
    simp only [combBad, ite_true, CombData.qsComb, CombData.wC]
    rw [hmid, hpre]
    exact Iff.rfl
  · simp only [combBad, hk, ite_false]
    refine chainBad_congr_at _ _ T chal3Blocks N g k x (fun hk' => ?_) (fun hk' => absurd hk' hk)
      (fun hk' => ?_)
    · subst hk'
      show preOfA T stF (f <$> G) E (stF s) x g = preOfA T stF (f' <$> G) E (stF s) x g
      unfold preOfA
      rw [hA', hJ]
    · subst hk'
      show accOfA T stF (f <$> G) E (stF s) x g = accOfA T stF (f' <$> G) E (stF s) x g
      unfold accOfA
      rw [hA', hJ]

end Congr

/-! ## The simultaneous union bound, per cipher table -/

section SimE

variable {ι' γ α ι β : Type} (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
  (E : CTable) (G : OracleComp specIC γ) (proj : ι' → γ → ByteArray × (ι × β))

/-- The finite key set of the simultaneous bound: every query of the event's computation, of the
shared run and of each output's game. -/
noncomputable def simKeys (oa : OracleComp spec α) (J : Finset ι') : Finset Dom :=
  possibleQueryKeys oa ∪ possibleQueryKeys (runE E G) ∪
    J.biUnion fun j => possibleQueryKeys (gameA T stF (proj j <$> G) E)

lemma simKeys_oa (oa : OracleComp spec α) (J : Finset ι') :
    AllQueriesSatisfy oa (· ∈ simKeys T stF E G proj oa J) :=
  (allQueriesSatisfy_possibleQueryKeys oa).mono fun _ h =>
    Finset.mem_union_left _ (Finset.mem_union_left _ h)

lemma simKeys_run (oa : OracleComp spec α) (J : Finset ι') :
    AllQueriesSatisfy (runE E G) (· ∈ simKeys T stF E G proj oa J) :=
  (allQueriesSatisfy_possibleQueryKeys _).mono fun _ h =>
    Finset.mem_union_left _ (Finset.mem_union_right _ h)

lemma simKeys_game (oa : OracleComp spec α) (J : Finset ι') (j : ι') (hj : j ∈ J) :
    AllQueriesSatisfy (gameA T stF (proj j <$> G) E) (· ∈ simKeys T stF E G proj oa J) :=
  (allQueriesSatisfy_possibleQueryKeys _).mono fun _ h =>
    Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j, hj, h⟩)

/-- **Simultaneous extraction for the issue relations, per cipher table.** A run `G` of the
adversary and the honest parties (at most `q k` hash queries of kind `k`, `nG` in all), outputs
`j ∈ J` read off it by `proj j` (the provers `proj j <$> G` of the single-proof games), and an
event of any computation `oa` that implies, at every table, that some output is accepted at the
statement it chose and not extracted (`htr`). Then

    Pr[event] ≤ Σ_k q_k·ε_k + Σ_{j ∈ J} Σ_k r_k·ε_k + Σ_{j ∈ J} Pr[bindFail_j ∨ deadOpen_j ∨ cf_j],

`ε = adaptEps` the single-proof bound's per-query charge (at the games' budgets
`q + r`), `r = extractorQueries + verifierQueries`. The single-proof bounds summed over `J` give
`Σ_{j ∈ J} Σ_k (q_k + r_k)·ε_k` instead. -/
theorem prEvent_sim_le_E (sys : ι → System GF128) (hT : liftInvOk T = true) (st₀ : Statement)
    (hparams : ∀ s, (stF s).params = st₀.params) (hdel : ∀ s, (stF s).delayed = false)
    (cb : Option (ℕ × ByteArray)) (hcomb : ∀ s, (stF s).comb = cb)
    (hdec : ∀ s, dec (muIn (stF s)) = some s) {n : ℕ} (hn : ∀ s, (sys s).length = n) (N : ℕ)
    (Wit : ι → ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ s c1 lb w, (stF s).values c1 lb w = (sys s).values w)
    (hdet : ∀ s, @ChainDet (icPrg E.cipher) T (stF s) (sys s) N (Wit s))
    (cf : Out ((ι × β) × QueryLog specIC) → Prop)
    (hcf : ∀ j s g, ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stF s) (proj j <$> G) E)) →
      KeysPre (stF s) E (jOf g (proj j <$> G) E) (gLog T (stF s) (proj j <$> G) E g) g)
    (q : Kind → ℕ) (hq : IsKindQueryBoundIC G q) (nG : ℕ)
    (hnG : IsQueryBoundP G (fun t => t.isLeft = true) nG)
    (J : Finset ι') (j₀ : ι') (oa : OracleComp spec α) (event : α → Prop)
    (htr : ∀ g, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF (proj j <$> G) E)
      r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r)) (Wit (stOut r)) r) :
    let n' := q + extractorQueries + verifierQueries
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤
      ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * adaptEps st₀ n N cb n' k +
      ∑ _j ∈ J, ∑ k ∈ adaptKinds,
        ((extractorQueries + verifierQueries) k : ℝ≥0∞) * adaptEps st₀ n N cb n' k +
      ∑ j ∈ J, Pr{let r ← (simulateQ randomOracle (gameA T stF (proj j <$> G) E)).run' ∅}[
        bindFailA stF E r ∨ deadOpenA stF E r ∨ cf r] := by
  classical
  intro n'
  let ε := adaptEps st₀ n N cb n'
  have hK : ∀ k ∉ adaptKinds, ε k = 0 := adaptEps_eq_zero st₀ n N cb n'
  have hqP : ∀ j, IsKindQueryBoundIC (proj j <$> G) q := fun j =>
    (isQueryBound_map_iff _ _ _ _ _).2 hq
  let S := simKeys T stF E G proj oa J
  let : SampleableType ((d : S) → Ans d.val) := SampleableType.piOfFintype _
  have hbad : ∀ j, ∀ (c : (ofFn fun d : S => Ans d.val).QueryCache) (t : S), c t = none →
      (cachedKeys c).card < nG + (2 + verifierTotal) →
      Pr{let g ← $ᵗ ((d : S) → Ans d.val)}[
        adaptBad T stF dec sys (proj j <$> G) E N cb t.val (extendTable S (completeTable c g))] ≤
        ε t.val.1 := fun j c t hc _ =>
    cached_of_cell S (adaptBad T stF dec sys (proj j <$> G) E N cb) (fun t => ε t.1)
      (fun t g => prEvent_adaptBad_le T stF dec sys (proj j <$> G) E hT st₀ hparams hn N cb q
        (hqP j) t g) c t hc
  refine prEvent_le_shared_suffix S oa event (simKeys_oa T stF E G proj oa J) (runE E G)
    (simKeys_run T stF E G proj oa J) (fun t => ε t.1) _
    (worstCaseCostBound_of_kindQueryBound _ adaptKinds ε hK q (isKindQueryBound_runE E hq)) nG
    (isTotalQueryBound_runE E hnG) (adaptBad T stF dec sys (proj j₀ <$> G) E N cb) J
    (fun _ => runE E G) (fun j => gameK T stF E (proj j)) (fun j hj => ?_) _
    (fun j a => worstCaseCostBound_of_kindQueryBound _ adaptKinds ε hK _
      (isKindQueryBound_gameK T stF E (proj j) a)) nG (2 + verifierTotal)
    (fun _ => isTotalQueryBound_runE E hnG) (fun j a => isTotalQueryBound_gameK T stF E (proj j) a)
    (fun j => adaptBad T stF dec sys (proj j <$> G) E N cb) J
    (fun j => gameA T stF (proj j <$> G) E) (fun _ r => bindFailA stF E r ∨ deadOpenA stF E r ∨ cf r)
    (fun j hj => simKeys_game T stF E G proj oa J j hj) (nG + (2 + verifierTotal)) (by omega)
    le_rfl (hbad j₀) (fun j _ => hbad j) fun g hev => ?_
  · rw [← gameA_map]
    exact simKeys_game T stF E G proj oa J j hj
  obtain ⟨j, hj, hacc, hnex⟩ := htr g hev
  by_cases hf : bindFailA stF E (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA T stF (proj j <$> G) E)) ∨ deadOpenA stF E (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA T stF (proj j <$> G) E)) ∨ cf (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA T stF (proj j <$> G) E))
  · exact Or.inr (Or.inr ⟨j, hj, hf⟩)
  simp only [not_or] at hf
  obtain ⟨e, he, hb⟩ := adaptBad_trace T stF dec sys (proj j <$> G) E hT hdel cb hcomb hdec N Wit
    hvals hdet cf (hcf j) g ⟨⟨hacc, hnex⟩, hf.1, hf.2.1, hf.2.2⟩
  rw [tableQueryLog_gameA_map] at he
  by_cases hm : e.1 ∈ (tableQueryLog (runE E G) g).map Sigma.fst
  · obtain ⟨e', he', heq⟩ := List.mem_map.1 hm
    refine Or.inl ⟨e', he', ?_⟩
    rw [heq]
    exact (adaptBad_map_congr T stF dec E G sys (proj j) (proj j₀) N cb g e.1 hm).1 hb
  · refine Or.inr (Or.inl ⟨j, hj, e, ?_, hm, hb⟩)
    exact (List.mem_append.1 he).resolve_left fun h => hm (List.mem_map_of_mem h)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Simultaneous extraction for the combined relations, per cipher table** (as
`prEvent_sim_le_E`, with `ROM/AdaptComb.lean`'s per-query charge `combAdaptEps`; `nG` the run's
total hash queries enters the `H₂²` charge as `(nG + 2 + verifierTotal)·2⁻⁴⁴⁸`). -/
theorem prEvent_sim_comb_le_E {M : ℕ} (sysL : ι → (Fin M → GF128) → System GF128)
    (witL : ι → (ℕ → GF128) → Prop) (dst : ByteArray) (hT : liftInvOk T = true)
    (st₀ : Statement) (hparams : ∀ s, (stF s).params = st₀.params)
    (hdel : ∀ s, (stF s).delayed = false) (hcomb : ∀ s, (stF s).comb = some (M, dst))
    (hdec : ∀ s, dec (muIn (stF s)) = some s) {n' : ℕ} (hn' : ∀ s l, (sysL s l).length = n')
    {εc : ℝ≥0∞} (hεc : ∀ s w, prU (Fin M → GF128) (fun l => (sysL s l).Holds w ∧ ¬witL s w) ≤ εc)
    (N : ℕ) (Wit : ι → ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ s c1 (v : Prob.Bytes (16 * M)) w,
      (stF s).values c1 v.ba w = (sysL s (combDec v)).values w)
    (hdet : ∀ s, @CombDet (icPrg E.cipher) M T (stF s) (sysL s) (witL s) N (Wit s))
    (cf : Out ((ι × β) × QueryLog specIC) → Prop)
    (hcf : ∀ j s g, ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stF s) (proj j <$> G) E)) →
      KeysPre (stF s) E (jOf g (proj j <$> G) E) (gLog T (stF s) (proj j <$> G) E g) g)
    (q : Kind → ℕ) (hq : IsKindQueryBoundIC G q) (nG : ℕ)
    (hnG : IsQueryBoundP G (fun t => t.isLeft = true) nG)
    (J : Finset ι') (j₀ : ι') (oa : OracleComp spec α) (event : α → Prop)
    (htr : ∀ g, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF (proj j <$> G) E)
      r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r)) (Wit (stOut r)) r) :
    let nn := q + extractorQueries + verifierQueries
    let ntot := nG + 2 + verifierTotal
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤
      ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * combAdaptEps (M := M) dst st₀ n' εc ntot N nn k +
      ∑ _j ∈ J, ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) *
        combAdaptEps (M := M) dst st₀ n' εc ntot N nn k +
      ∑ j ∈ J, Pr{let r ← (simulateQ randomOracle (gameA T stF (proj j <$> G) E)).run' ∅}[
        bindFailA stF E r ∨ deadOpenA stF E r ∨ cf r] := by
  classical
  intro nn ntot
  let ε := combAdaptEps (M := M) dst st₀ n' εc ntot N nn
  have hK : ∀ k ∉ adaptKinds, ε k = 0 := combAdaptEps_eq_zero dst st₀ n' εc ntot N nn
  have hqP : ∀ j, IsKindQueryBoundIC (proj j <$> G) q := fun j =>
    (isQueryBound_map_iff _ _ _ _ _).2 hq
  let S := simKeys T stF E G proj oa J ∪ Finset.univ.image (combKey M dst)
  have hKS : ∀ u, combKey M dst u ∈ S := fun u =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  have hsub : ∀ d, d ∈ simKeys T stF E G proj oa J → d ∈ S := fun _ h =>
    Finset.mem_union_left _ h
  let : SampleableType ((d : S) → Ans d.val) := SampleableType.piOfFintype _
  have hbad : ∀ j, ∀ (c : (ofFn fun d : S => Ans d.val).QueryCache) (t : S), c t = none →
      (cachedKeys c).card < ntot →
      Pr{let g ← $ᵗ ((d : S) → Ans d.val)}[combAdaptBad T stF dec (proj j <$> G) E sysL witL dst N
        t.val (extendTable S (completeTable c g))] ≤ ε t.val.1 := fun j c t hc hcard =>
    prEvent_combAdaptBad_le T stF dec (proj j <$> G) E sysL witL dst hT st₀ hparams hn' hεc N q
      (hqP j) S hKS ntot c t hc hcard
  refine prEvent_le_shared_suffix S oa event ((simKeys_oa T stF E G proj oa J).mono hsub)
    (runE E G) ((simKeys_run T stF E G proj oa J).mono hsub) (fun t => ε t.1) _
    (worstCaseCostBound_of_kindQueryBound _ adaptKinds ε hK q (isKindQueryBound_runE E hq)) nG
    (isTotalQueryBound_runE E hnG) (combAdaptBad T stF dec (proj j₀ <$> G) E sysL witL dst N) J
    (fun _ => runE E G) (fun j => gameK T stF E (proj j)) (fun j hj => ?_) _
    (fun j a => worstCaseCostBound_of_kindQueryBound _ adaptKinds ε hK _
      (isKindQueryBound_gameK T stF E (proj j) a)) nG (2 + verifierTotal)
    (fun _ => isTotalQueryBound_runE E hnG) (fun j a => isTotalQueryBound_gameK T stF E (proj j) a)
    (fun j => combAdaptBad T stF dec (proj j <$> G) E sysL witL dst N) J
    (fun j => gameA T stF (proj j <$> G) E) (fun _ r => bindFailA stF E r ∨ deadOpenA stF E r ∨ cf r)
    (fun j hj => (simKeys_game T stF E G proj oa J j hj).mono hsub) ntot (by omega)
    (by omega) (hbad j₀) (fun j _ => hbad j) fun g hev => ?_
  · rw [← gameA_map]
    exact (simKeys_game T stF E G proj oa J j hj).mono hsub
  obtain ⟨j, hj, hacc, hnex⟩ := htr g hev
  by_cases hf : bindFailA stF E (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA T stF (proj j <$> G) E)) ∨ deadOpenA stF E (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA T stF (proj j <$> G) E)) ∨ cf (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA T stF (proj j <$> G) E))
  · exact Or.inr (Or.inr ⟨j, hj, hf⟩)
  simp only [not_or] at hf
  obtain ⟨e, he, hb⟩ := combAdaptBad_trace T stF dec (proj j <$> G) E sysL witL dst hT hdel hcomb
    hdec N Wit hvals hdet cf (hcf j) g ⟨⟨hacc, hnex⟩, hf.1, hf.2.1, hf.2.2⟩
  rw [tableQueryLog_gameA_map] at he
  by_cases hm : e.1 ∈ (tableQueryLog (runE E G) g).map Sigma.fst
  · obtain ⟨e', he', heq⟩ := List.mem_map.1 hm
    refine Or.inl ⟨e', he', ?_⟩
    rw [heq]
    exact (combAdaptBad_map_congr T stF dec E G sysL witL dst (proj j) (proj j₀) N g e.1 hm).1 hb
  · refine Or.inr (Or.inl ⟨j, hj, e, ?_, hm, hb⟩)
    exact (List.mem_append.1 he).resolve_left fun h => hm (List.mem_map_of_mem h)

end SimE

/-! ## The joint experiment -/

section Joint

variable {ι' γ α ι β : Type}

/-- **Averaging a per-cipher-table bound with per-output failure terms.** -/
theorem prEvent_avg_le_sum3 {X Y : Type} (m : CTable → ProbComp X) (ev : CTable → X → Prop)
    (c : ℝ≥0∞) (J : Finset ι') (m' : ι' → CTable → ProbComp Y) (Q₁ Q₂ Q₃ : CTable → Y → Prop)
    (h : ∀ E, Pr{let r ← m E}[ev E r] ≤
      c + ∑ j ∈ J, Pr{let r ← m' j E}[Q₁ E r ∨ Q₂ E r ∨ Q₃ E r]) :
    Pr{let E ← $ᵗ CTable; let r ← m E}[ev E r] ≤
      c + ∑ j ∈ J, (Pr{let E ← $ᵗ CTable; let r ← m' j E}[Q₁ E r] +
        Pr{let E ← $ᵗ CTable; let r ← m' j E}[Q₂ E r] +
        Pr{let E ← $ᵗ CTable; let r ← m' j E}[Q₃ E r]) := by
  let : MeasurableSpace CTable := ⊤
  have h3 : ∀ j E, Pr{let r ← m' j E}[Q₁ E r ∨ Q₂ E r ∨ Q₃ E r] ≤
      Pr{let r ← m' j E}[Q₁ E r] + Pr{let r ← m' j E}[Q₂ E r] + Pr{let r ← m' j E}[Q₃ E r] :=
    fun j E => (prEvent_or_le _ _ _).trans (by
      rw [add_assoc]; exact add_le_add le_rfl (prEvent_or_le _ _ _))
  rw [prEvent_bind_of_discrete]
  simp only [prEvent_bind_of_discrete]
  calc ∫⁻ E, Pr{let r ← m E}[ev E r] ∂𝒟[$ᵗ CTable]
      ≤ ∫⁻ E, (c + ∑ j ∈ J, (Pr{let r ← m' j E}[Q₁ E r] + Pr{let r ← m' j E}[Q₂ E r] +
          Pr{let r ← m' j E}[Q₃ E r])) ∂𝒟[$ᵗ CTable] :=
        MeasureTheory.lintegral_mono fun E => (h E).trans
          (add_le_add le_rfl (Finset.sum_le_sum fun j _ => h3 j E))
    _ = c * 𝒟[$ᵗ CTable] Set.univ + ∑ j ∈ J, (∫⁻ E, Pr{let r ← m' j E}[Q₁ E r] ∂𝒟[$ᵗ CTable] +
          ∫⁻ E, Pr{let r ← m' j E}[Q₂ E r] ∂𝒟[$ᵗ CTable] +
          ∫⁻ E, Pr{let r ← m' j E}[Q₃ E r] ∂𝒟[$ᵗ CTable]) := by
        rw [MeasureTheory.lintegral_add_left measurable_const, MeasureTheory.lintegral_const,
          MeasureTheory.lintegral_finsetSum _ fun _ _ => measurable_from_top]
        refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
        rw [MeasureTheory.lintegral_add_left measurable_from_top,
          MeasureTheory.lintegral_add_left measurable_from_top]
    _ ≤ _ := add_le_add (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)) le_rfl

/-- The failure terms of one output (binding, an opened dead leaf, Post), as in
`prEvent_accept_le_adaptive`. -/
noncomputable def failEps (q : Kind → ℕ) (qE : ℕ) : ℝ≥0∞ :=
  (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
    (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹)

/-- The per-output failure terms of the outputs `proj j <$> G`, each at `G`'s budgets. -/
theorem sum_fail_le (T : CrtTables) (stF : ι → Statement) (p : Params)
    (hparams : ∀ s, (stF s).params = p) (G : OracleComp specIC γ)
    (proj : ι' → γ → ByteArray × (ι × β)) (J : Finset ι') (qE : ℕ)
    (hqE : IsQueryBoundP G (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC G q) :
    ∑ j ∈ J, (Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA T stF (proj j <$> G) E)).run' ∅}[bindFailA stF E r] +
      Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA T stF (proj j <$> G) E)).run' ∅}[deadOpenA stF E r] +
      Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA T stF (proj j <$> G) E)).run' ∅}[PostOut E r]) ≤
      J.card * failEps q qE := by
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun j _ => ?_
  have hqP : IsKindQueryBoundIC (proj j <$> G) q := (isQueryBound_map_iff _ _ _ _ _).2 hq
  have hqEP : IsQueryBoundP (proj j <$> G) (fun t => t.isRight = true) qE :=
    (isQueryBoundP_map_iff _ _ _).2 hqE
  have hdo := prEvent_joint_deadOpen_le_A T stF (proj j <$> G) p hparams q hqP
  unfold failEps
  gcongr
  · exact (prEvent_joint_bindFail_le_A T stF (proj j <$> G) qE hqEP).trans (add_le_add le_rfl hdo)
  · exact prEvent_joint_postOut_le_A T stF (proj j <$> G) qE hqEP q hqP

/-- **Simultaneous extraction for the issue relations in the joint experiment** (the cipher table
uniform, then the lazy hash oracle): `prEvent_sim_le_E` averaged over the cipher table, with
`cf` = Post, and each output's failure terms bounded by `failEps`. -/
theorem prEvent_sim_le (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
    (sys : ι → System GF128) (hT : liftInvOk T = true) (st₀ : Statement)
    (hparams : ∀ s, (stF s).params = st₀.params) (hdel : ∀ s, (stF s).delayed = false)
    (cb : Option (ℕ × ByteArray)) (hcomb : ∀ s, (stF s).comb = cb)
    (hdec : ∀ s, dec (muIn (stF s)) = some s) {n : ℕ} (hn : ∀ s, (sys s).length = n) (N : ℕ)
    (Wit : ι → ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ s c1 lb w, (stF s).values c1 lb w = (sys s).values w)
    (hdet : ∀ (E : CTable) s, @ChainDet (icPrg E.cipher) T (stF s) (sys s) N (Wit s))
    (G : OracleComp specIC γ) (proj : ι' → γ → ByteArray × (ι × β))
    (qE : ℕ) (hqE : IsQueryBoundP G (fun t => t.isRight = true) qE)
    (q : Kind → ℕ) (hq : IsKindQueryBoundIC G q) (nG : ℕ)
    (hnG : IsQueryBoundP G (fun t => t.isLeft = true) nG)
    (J : Finset ι') (j₀ : ι') (oa : CTable → OracleComp spec α) (event : CTable → α → Prop)
    (htr : ∀ E g, event E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF (proj j <$> G) E)
      r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r)) (Wit (stOut r)) r) :
    let n' := q + extractorQueries + verifierQueries
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * adaptEps st₀ n N cb n' k +
      ∑ _j ∈ J, ∑ k ∈ adaptKinds,
        ((extractorQueries + verifierQueries) k : ℝ≥0∞) * adaptEps st₀ n N cb n' k +
      J.card * failEps q qE := by
  intro n'
  refine (prEvent_avg_le_sum3 _ _ _ J (fun j E => (simulateQ randomOracle
    (gameA T stF (proj j <$> G) E)).run' ∅) (fun E r => bindFailA stF E r)
    (fun E r => deadOpenA stF E r) (fun E r => PostOut E r) fun E =>
      prEvent_sim_le_E T stF dec E G proj sys hT st₀ hparams hdel cb hcomb hdec hn N Wit hvals
        (hdet E) (fun r => PostOut E r)
        (fun j s g h => keysPre_of_not_postOut T (stF s) (proj j <$> G) E g h) q hq nG hnG J j₀
        (oa E) (event E) (htr E)).trans ?_
  exact add_le_add le_rfl (sum_fail_le T stF st₀.params hparams G proj J qE hqE q hq)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Simultaneous extraction for the combined relations in the joint experiment.** -/
theorem prEvent_sim_comb_le (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
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
    (G : OracleComp specIC γ) (proj : ι' → γ → ByteArray × (ι × β))
    (qE : ℕ) (hqE : IsQueryBoundP G (fun t => t.isRight = true) qE)
    (q : Kind → ℕ) (hq : IsKindQueryBoundIC G q) (nG : ℕ)
    (hnG : IsQueryBoundP G (fun t => t.isLeft = true) nG)
    (J : Finset ι') (j₀ : ι') (oa : CTable → OracleComp spec α) (event : CTable → α → Prop)
    (htr : ∀ E g, event E (evalWithAnswerFn (QueryImpl.ofFn g) (oa E)) → ∃ j ∈ J,
      let r := evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF (proj j <$> G) E)
      r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r)) (Wit (stOut r)) r) :
    let nn := q + extractorQueries + verifierQueries
    let ntot := nG + 2 + verifierTotal
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (oa E)).run' ∅}[event E r] ≤
      ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * combAdaptEps (M := M) dst st₀ n' εc ntot N nn k +
      ∑ _j ∈ J, ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) *
        combAdaptEps (M := M) dst st₀ n' εc ntot N nn k +
      J.card * failEps q qE := by
  intro nn ntot
  refine (prEvent_avg_le_sum3 _ _ _ J (fun j E => (simulateQ randomOracle
    (gameA T stF (proj j <$> G) E)).run' ∅) (fun E r => bindFailA stF E r)
    (fun E r => deadOpenA stF E r) (fun E r => PostOut E r) fun E =>
      prEvent_sim_comb_le_E T stF dec E G proj sysL witL dst hT st₀ hparams hdel hcomb hdec hn'
        hεc N Wit hvals (hdet E) (fun r => PostOut E r)
        (fun j s g h => keysPre_of_not_postOut T (stF s) (proj j <$> G) E g h) q hq nG hnG J j₀
        (oa E) (event E) (htr E)).trans ?_
  exact add_le_add le_rfl (sum_fail_le T stF st₀.params hparams G proj J qE hqE q hq)

/-! ## The terms -/

/-- **The hit terms, simultaneously**: `chainHitEps` with the verifier's queries counted once per
output (`m` outputs); `chainHitEpsSim q 1 = chainHitEps q`. -/
noncomputable def chainHitEpsSim (q : Kind → ℕ) (m : ℕ) : ℝ≥0∞ :=
  (q .h1 + 18 * m) * (((18 * (q .h1 + 18) + (q .h21 + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    (q .h21 + m) * (((q .h22 + 1 + (q .h21 + 1) : ℕ) : ℝ≥0∞) / 2 ^ 1088) +
    (q .h22 + m) * (((q .h23 + 1 + (q .h22 + 1) : ℕ) : ℝ≥0∞) / 2 ^ 448)

/-- The combined relations' hit terms, simultaneously. -/
noncomputable def chainHitEpsCombSim (q : Kind → ℕ) (M m : ℕ) : ℝ≥0∞ :=
  chainHitEpsSim q m + (q .h22 + m) * (((q (.comb M) + 1 : ℕ) : ℝ≥0∞) / 2 ^ 448)

/-- **The statement-binding term, simultaneously**: the extractor's and the verifier's `H₂⁰`
queries counted once per output; `stmtBindEpsSim q 1 = stmtBindEps q`. -/
noncomputable def stmtBindEpsSim (q : Kind → ℕ) (m : ℕ) : ℝ≥0∞ :=
  (q .mu + 3 * m) * (((q .h21 + 1 + (q .mu + 3) : ℕ) : ℝ≥0∞) / 2 ^ 256)

lemma chainHitEpsSim_one (q : Kind → ℕ) : chainHitEpsSim q 1 = chainHitEps q := by
  simp only [chainHitEpsSim, chainHitEps, Nat.cast_one, mul_one]

lemma stmtBindEpsSim_one (q : Kind → ℕ) : stmtBindEpsSim q 1 = stmtBindEps q := by
  simp only [stmtBindEpsSim, stmtBindEps, Nat.cast_one, mul_one]

set_option exponentiation.threshold 1100 in
/-- **The simultaneous charge of the issue relations, summed**: the shared run's queries once,
the `m` continuations' `extractorQueries + verifierQueries` each. -/
theorem sim_sum_eq (st₀ : Statement) (n N : ℕ) (q : Kind → ℕ) (J : Finset ι') :
    let n' := q + extractorQueries + verifierQueries
    ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * adaptEps st₀ n N none n' k +
      ∑ _j ∈ J, ∑ k ∈ adaptKinds,
        ((extractorQueries + verifierQueries) k : ℝ≥0∞) * adaptEps st₀ n N none n' k =
      (q .h21 + J.card) * epsKOS #chal3Blocks (Chain.kosL st₀) +
        (q .h22 + J.card) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) +
        (q .h23 + J.card) * ((N : ℝ≥0∞) / 2 ^ 128) + chainHitEpsSim q J.card +
        stmtBindEpsSim q J.card := by
  intro n'
  rw [Finset.sum_const, nsmul_eq_mul]
  simp only [adaptKinds, n', adaptEps]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [chainEps, hitEps, stmtEps, combCount, chainHitEpsSim, stmtBindEpsSim, Pi.add_apply,
    extractorQueries, verifierQueries, reduceCtorEq, or_self, false_or, or_false,
    ↓reduceIte, add_zero, zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring_nf

set_option exponentiation.threshold 1100 in
/-- **The simultaneous charge of the combined relations, summed.** -/
theorem sim_comb_sum_eq (st₀ : Statement) (n' : ℕ) (εc : ℝ≥0∞) (ntot N : ℕ) {M : ℕ}
    (dst : ByteArray) (q : Kind → ℕ) (J : Finset ι') :
    let nn := q + extractorQueries + verifierQueries
    ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * combAdaptEps (M := M) dst st₀ n' εc ntot N nn k +
      ∑ _j ∈ J, ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) *
        combAdaptEps (M := M) dst st₀ n' εc ntot N nn k =
      (q .h21 + J.card) * epsKOS #chal3Blocks (Chain.kosL st₀) +
        (q .h22 + J.card) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          (ntot : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + J.card) * ((N : ℝ≥0∞) / 2 ^ 128) + chainHitEpsCombSim q M J.card +
        stmtBindEpsSim q J.card := by
  intro nn
  rw [Finset.sum_const, nsmul_eq_mul]
  simp only [adaptKinds, nn, combAdaptEps]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [chainEps, hitEps, stmtEps, combCount, chainHitEpsCombSim, chainHitEpsSim,
    stmtBindEpsSim, Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self,
    false_or, or_false, ↓reduceIte, add_zero, zero_add, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv]
  ring

end Joint

end VoleMole.ROM.IC
