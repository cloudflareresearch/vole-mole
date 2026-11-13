import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-!
# The union bound over queries, with a cache-size charge (plan M5, freshness)

VCVio's `prEvent_randomOracle_le_of_bad_queries_weighted` needs, for each query `t`, a bound on
its bad event when the cell `t` **alone** is resampled, for every background table. Some bad events
read a second cell chosen by the answer: L4's combined relations check the system at
`l = H(chal2 ‖ dst)`, so the `H₂²` query at `y` (answer `chal2`) is bad depending on the cell
`chal2 ‖ dst`. That cell is fresh, hence uniform and independent of `chal2`, unless the adversary
queried it before `chal2` was known (L0 §2.2, "independence of l and χ"). No single-cell bound
holds for every background table.

This file generalizes VCVio's theorem (same proof): the bad event of a fresh query `t` may be
bounded **on average over the uncached cells** of the current cache, with a bound allowed to grow
with the number of cached cells (at most `n` for an `n`-query adversary).
* `prEvent_freshBadQuery_le_of_cached`: finite key type; the hypothesis is
  `Pr_g[bad t (completeTable c g)] ≤ error t` for every cache `c` not containing `t` with fewer
  than `n` cached keys.
* `prEvent_randomOracle_le_of_fresh_bad_queries`: any key type, through VCVio's restriction to a
  finite key set `S` containing every possible query (`restrictQueries`, `extendTable`); the
  hypothesis is stated on `S`, which may also contain cells the adversary never queries (the
  second cells of the bad events).

The statements and proofs follow `QueryTracking/RandomOracle/FreshQuery.lean` closely; the private
helpers it uses are re-proved here.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM

variable {D α : Type} {R : D → Type}

/-- The keys of a cache. -/
noncomputable def cachedKeys [Fintype D] (c : (ofFn R).QueryCache) : Finset D := by
  classical
  exact Finset.univ.filter fun d => (c d).isSome

lemma card_cachedKeys_empty [Fintype D] :
    (cachedKeys (∅ : (ofFn R).QueryCache)).card = 0 := by
  classical
  simp only [cachedKeys, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro d _
  show ¬(Option.none : Option (R d)).isSome = true
  simp

lemma card_cachedKeys_cacheQuery [Fintype D] [DecidableEq D] (c : (ofFn R).QueryCache) (t : D)
    (u : R t) : (cachedKeys (c.cacheQuery t u)).card ≤ (cachedKeys c).card + 1 := by
  classical
  refine (Finset.card_le_card fun d hd => ?_).trans (Finset.card_insert_le t _)
  simp only [cachedKeys, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
  by_cases h : d = t
  · exact Finset.mem_insert.2 (Or.inl h)
  · rw [QueryCache.cacheQuery_of_ne _ _ h] at hd
    exact Finset.mem_insert.2 (Or.inr (by simpa [cachedKeys] using hd))

/-- A weighted budget pays for its first query (VCVio's private `query_budget_tail`). -/
theorem query_budget_tail' [∀ d, Nonempty (R d)]
    (t : D) (k : R t → OracleComp (ofFn R) α) (error : D → ℝ≥0∞) (B : ℝ≥0∞)
    (hB : B ≠ ⊤)
    (hb : WorstCaseCostBound (liftM ((ofFn R).query t) >>= k) ⟨error⟩ B) :
    error t ≤ B ∧ ∀ u, WorstCaseCostBound (k u) ⟨error⟩ (B - error t) := by
  have h := (worstCaseCostBound_query_bind_iff t k ⟨error⟩ B).mp hb
  obtain ⟨u⟩ : Nonempty (R t) := inferInstance
  obtain ⟨z, hz⟩ := support_nonempty (costDist (k u) ⟨error⟩)
  have he : error t ≤ B := (le_add_right (le_refl _)).trans (h u z hz)
  refine ⟨he, fun u => ?_⟩
  rw [worstCaseCostBound_iff_support_bound]
  intro z hz
  exact ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top hB he) (h u z hz)

section Finite

variable [Fintype D] [DecidableEq D] [∀ d, SampleableType (R d)] [SampleableType (∀ d, R d)]

/-- **The weighted bad-query bound with a cache-size condition**, finite key type. An adversary
with weighted budget `B` and at most `n` queries, started from a cache with `m` keys
(`m + n ≤ N`): if a fresh query `t` is bad with probability `≤ error t` over the uncached cells
of every cache with fewer than `N` keys, then a fresh bad query occurs with probability `≤ B`. -/
theorem prEvent_freshBadQuery_le_of_cached (oa : OracleComp (ofFn R) α) (error : D → ℝ≥0∞)
    (B : ℝ≥0∞) (hbound : WorstCaseCostBound oa ⟨error⟩ B) (n : ℕ) (hn : IsTotalQueryBound oa n)
    (c : (ofFn R).QueryCache) (m N : ℕ) (hm : (cachedKeys c).card ≤ m) (hmN : m + n ≤ N)
    (bad : D → (∀ d, R d) → Prop)
    (hbad : ∀ (c' : (ofFn R).QueryCache) t, c' t = none → (cachedKeys c').card < N →
      Pr{let g ← $ᵗ (∀ d, R d)}[bad t (completeTable c' g)] ≤ error t) :
    Pr{let g ← $ᵗ (∀ d, R d)}[freshBadQuery oa c g bad] ≤ B := by
  induction oa using OracleComp.inductionOn generalizing B c n m with
  | pure a => simp [freshBadQuery]
  | query_bind t k ih =>
      by_cases hB : B = ⊤
      · simp [hB]
      obtain ⟨he, hk⟩ := query_budget_tail' t k error B hB hbound
      obtain ⟨hn0, hnk⟩ := isTotalQueryBound_query_bind_iff.mp hn
      cases hc : c t with
      | some u =>
          simp_rw [freshBadQuery_query_bind_of_some t k c _ bad hc]
          exact (ih u (B - error t) (hk u) (n - 1) (hnk u) c m hm (by omega)).trans
            tsub_le_self
      | none =>
          simp_rw [freshBadQuery_query_bind_of_none t k c _ bad hc]
          apply (prEvent_or_le _ _ _).trans
          have hfirst := hbad c t hc (by omega)
          have hrest : Pr{let g ← $ᵗ (∀ d, R d)}[freshBadQuery (k (completeTable c g t))
              (c.cacheQuery t (completeTable c g t)) g bad] ≤ B - error t := by
            rw [prEvent_freshBadQuery_suffix t k c hc bad]
            simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
              pure_bind, id_eq] using
              (prEvent_bind_le_of_forall_le ($ᵗ (R t))
              (fun u => (fun g => freshBadQuery (k u) (c.cacheQuery t u) g bad) <$>
                ($ᵗ (∀ d, R d))) id
              (fun u => by
                simpa using ih u (B - error t) (hk u) (n - 1) (hnk u) (c.cacheQuery t u) (m + 1)
                  ((card_cachedKeys_cacheQuery c t u).trans (by omega)) (by omega)))
          calc
            _ ≤ error t + (B - error t) := add_le_add hfirst hrest
            _ = B := by rw [add_comm, tsub_add_cancel_of_le he]

/-- **Exposing a second cell chosen by the first answer.** For a cell `t` and a second cell `p u`
chosen by the answer `u` at `t`, an event of the completed table has probability at most the
chance that `p u` is cached, plus the probability with the answers `u` at `t` and then `v` at `p u`
drawn fresh (first `u`, then `v`) and written into the table. -/
theorem prEvent_completeTable_le_two_cells (c : (ofFn R).QueryCache) (t : D) (p : R t → D)
    (ev : (∀ d, R d) → Prop) :
    Pr{let g ← $ᵗ (∀ d, R d)}[ev (completeTable c g)] ≤
      Pr{let u ← $ᵗ (R t)}[(c (p u)).isSome] +
      Pr{let u ← $ᵗ (R t); let v ← $ᵗ (R (p u)); let g ← $ᵗ (∀ d, R d)}[
        c (p u) = none ∧
          ev (completeTable c (Function.update (Function.update g (p u) v) t u))] := by
  rw [prEvent_uniformTable_update t]
  have key := prEvent_bind_le_add_of_forall_le ($ᵗ (R t))
    (fun u => (fun g => ev (completeTable c (Function.update g t u))) <$> ($ᵗ (∀ d, R d)))
    (fun u => (pure ((c (p u)).isSome = true) : ProbComp Prop))
    (fun u => $ᵗ (R (p u)) >>= fun v => (fun g => c (p u) = none ∧
      ev (completeTable c (Function.update (Function.update g (p u) v) t u))) <$>
        ($ᵗ (∀ d, R d)))
    id id id ?_
  · simpa only [prEvent_norm, id_eq, id_map', bind_pure_comp] using key
  · intro u
    cases hcu : c (p u) with
    | some w =>
        refine (prEvent_le_one _).trans (le_add_right ?_)
        simp
    | none =>
        refine le_add_left (le_of_eq ?_)
        have h := prEvent_uniformTable_update (p u)
          (fun g => ev (completeTable c (Function.update g t u)))
        simpa only [prEvent_norm, id_eq, id_map', true_and] using h

omit [DecidableEq D] [SampleableType (∀ d, R d)] in
/-- An injective choice of the second cell hits the cache with probability at most
`|cache| / |R t|`. -/
theorem prEvent_isSome_le {t : D} [Fintype (R t)] (c : (ofFn R).QueryCache) (p : R t → D)
    (hp : Function.Injective p) :
    Pr{let u ← $ᵗ (R t)}[(c (p u)).isSome] ≤
      ((cachedKeys c).card : ℝ≥0∞) / Fintype.card (R t) := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  gcongr
  refine Finset.card_le_card_of_injOn p (fun u hu => ?_) hp.injOn
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu
  simpa [cachedKeys] using hu

end Finite

/-! ## Three independent draws -/

section Three

variable {U V G : Type} [SampleableType U] [SampleableType V] [SampleableType G]

theorem prEvent_three_eq_triple (P : U → V → G → Prop) :
    Pr{let u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G}[P u v g] =
      Pr{let x ← (do let u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G; pure (u, v, g))}[
        P x.1 x.2.1 x.2.2] := by
  simp only [prEvent_norm]

theorem prEvent_three_mono {P Q : U → V → G → Prop} (h : ∀ u v g, P u v g → Q u v g) :
    Pr{let u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G}[P u v g] ≤
      Pr{let u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G}[Q u v g] := by
  rw [prEvent_three_eq_triple, prEvent_three_eq_triple]
  exact prEvent_mono _ _ _ fun x hx => h _ _ _ hx

theorem prEvent_three_or_le (P Q : U → V → G → Prop) :
    Pr{let u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G}[P u v g ∨ Q u v g] ≤
      Pr{let u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G}[P u v g] +
      Pr{let u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G}[Q u v g] := by
  rw [prEvent_three_eq_triple, prEvent_three_eq_triple, prEvent_three_eq_triple]
  exact prEvent_or_le _ _ _

/-- A bound over the first draw, for all values of the other two. -/
theorem prEvent_three_le_of_first (P : U → V → G → Prop) {ε : ℝ≥0∞}
    (h : ∀ v g, Pr{let u ← $ᵗ U}[P u v g] ≤ ε) :
    Pr{let u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G}[P u v g] ≤ ε := by
  have e : Pr{let u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G}[P u v g] =
      Pr{let u ← $ᵗ U; let x ← (do let v ← $ᵗ V; let g ← $ᵗ G; pure (v, g))}[P u x.1 x.2] := by
    simp only [prEvent_norm]
  rw [e, prEvent_bind_map_swap]
  have := prEvent_bind_le_of_forall_le (do let v ← $ᵗ V; let g ← $ᵗ G; pure (v, g))
    (fun x => (fun u => P u x.1 x.2) <$> ($ᵗ U)) id (fun x => by simpa using h x.1 x.2)
  simpa only [prEvent_norm, id_eq, id_map'] using this

/-- A bound over the second draw, for an event not reading the first, for all values of the
third. -/
theorem prEvent_three_le_of_second (P : V → G → Prop) {ε : ℝ≥0∞}
    (h : ∀ g, Pr{let v ← $ᵗ V}[P v g] ≤ ε) :
    Pr{let _u ← $ᵗ U; let v ← $ᵗ V; let g ← $ᵗ G}[P v g] ≤ ε := by
  have h2 : ∀ _u : U, Pr{let v ← $ᵗ V; let g ← $ᵗ G}[P v g] ≤ ε := fun _ => by
    rw [prEvent_bind_map_swap]
    have := prEvent_bind_le_of_forall_le ($ᵗ G) (fun g => (fun v => P v g) <$> ($ᵗ V)) id
      (fun g => by simpa using h g)
    simpa only [prEvent_norm, id_eq, id_map'] using this
  have := prEvent_bind_le_of_forall_le ($ᵗ U)
    (fun _ => (do let v ← $ᵗ V; let g ← $ᵗ G; pure (P v g))) id (fun u => by simpa using h2 u)
  simpa only [prEvent_norm, id_eq, id_map'] using this

end Three

/-! ## Any key type -/

theorem restrictQueries_queryBound' (S : Finset D) (oa : OracleComp (ofFn R) α)
    (h : AllQueriesSatisfy oa (· ∈ S)) (n : ℕ) (hb : IsTotalQueryBound oa n) :
    IsTotalQueryBound (restrictQueries S oa h) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
      exact ⟨hb.1, fun u => ih u
        (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u) _ (hb.2 u)⟩

theorem restrictQueries_costBound' [∀ d, Nonempty (R d)]
    (S : Finset D) (oa : OracleComp (ofFn R) α) (h : AllQueriesSatisfy oa (· ∈ S))
    (error : D → ℝ≥0∞) (B : ℝ≥0∞) (hb : WorstCaseCostBound oa ⟨error⟩ B) :
    WorstCaseCostBound (restrictQueries S oa h) ⟨fun t => error t.val⟩ B := by
  induction oa using OracleComp.inductionOn generalizing B with
  | pure a => simp [restrictQueries_pure]
  | query_bind t k ih =>
      by_cases hB : B = ⊤
      · rw [worstCaseCostBound_iff_support_bound]
        simp [hB]
      obtain ⟨he, hk⟩ := query_budget_tail' t k error B hB hb
      rw [restrictQueries_query_bind, worstCaseCostBound_query_bind_iff]
      intro u z hz
      have hku := ih u (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u)
        (B - error t) (hk u)
      have hzle := (worstCaseCostBound_iff_support_bound _ _ _).mp hku z hz
      calc
        _ ≤ error t + (B - error t) := add_le_add (le_refl (error t)) hzle
        _ = B := by rw [add_comm, tsub_add_cancel_of_le he]

/-- **The weighted bad-query bound with a cache-size condition**, any key type. `S` is a finite
key set containing every possible query of `oa` (and whatever other cells the bad events read);
any uniform sampler of the tables over `S` may be supplied. If, on those tables, a fresh query `t`
is bad with probability `≤ error t` over the uncached cells of every cache with fewer than `n`
keys, the event has probability `≤ B`. -/
theorem prEvent_randomOracle_le_of_fresh_bad_queries [DecidableEq D] [∀ d, SampleableType (R d)]
    (oa : OracleComp (ofFn R) α) (S : Finset D) (hS : AllQueriesSatisfy oa (· ∈ S))
    [SampleableType ((d : S) → R d.val)] (error : D → ℝ≥0∞) (B : ℝ≥0∞)
    (hbound : WorstCaseCostBound oa ⟨error⟩ B) (n : ℕ) (hn : IsTotalQueryBound oa n)
    (event : α → Prop) (bad : D → (∀ d, R d) → Prop)
    (hbad : ∀ (c : (ofFn fun d : S => R d.val).QueryCache) (t : S), c t = none →
      (cachedKeys c).card < n →
      Pr{let g ← $ᵗ ((d : S) → R d.val)}[bad t.val (extendTable S (completeTable c g))] ≤
        error t.val)
    (htrace : ∀ g, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ q ∈ tableQueryLog oa g, bad q.1 g) :
    Pr{let result ← (simulateQ randomOracle oa).run' ∅}[event result] ≤ B := by
  classical
  let small := restrictQueries S oa hS
  have hrun : (simulateQ randomOracle small).run' ∅ =
      (simulateQ randomOracle oa).run' ∅ := randomOracle_restrictQueries S oa hS ∅
  rw [← hrun]
  let : MeasurableSpace α := ⊤
  have heager := evalDist_simulateQ_randomOracle_run'_eq_completeTable small ∅
  simp only [completeTable_empty] at heager
  rw [(EvalDistEq.of_evalDist_eq heager).prEvent_eq event]
  simp only [prEvent_norm]
  refine (prEvent_mono ($ᵗ ((d : S) → R d.val)) _
    (fun g => freshBadQuery small ∅ g (fun t g => bad t.val (extendTable S g))) ?_).trans ?_
  · intro g hevent
    have hrestrict : (fun d : S => extendTable S g d.val) = g := by
      funext d
      exact extendTable_subtype S g d
    have heval := evalWithAnswerFn_restrictQueries S oa hS (extendTable S g)
    rw [hrestrict] at heval
    obtain ⟨q, hq, hb⟩ := htrace (extendTable S g) (heval ▸ hevent)
    have hlog := tableQueryLog_restrictQueries S oa hS (extendTable S g)
    rw [hrestrict] at hlog
    rw [← hlog] at hq
    obtain ⟨smallq, hsmallq, rfl⟩ := List.mem_map.mp hq
    refine ⟨smallq, by simpa [completeTable_empty] using hsmallq, rfl, ?_⟩
    simpa [completeTable_empty] using hb
  · exact prEvent_freshBadQuery_le_of_cached small (fun t => error t.val) B
      (restrictQueries_costBound' S oa hS error B hbound) n
      (restrictQueries_queryBound' S oa hS n hn) ∅ 0 n (by rw [card_cachedKeys_empty]) (by omega)
      _ hbad

end VoleMole.ROM
