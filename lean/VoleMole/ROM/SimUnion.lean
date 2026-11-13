import VoleMole.ROM.Fresh

/-!
# Simultaneous extraction: one union bound over a shared run and per-output continuations

The single-proof extraction bounds (`ROM/AdaptChain.lean`, `ROM/AdaptComb.lean`) charge a bad
event to **every** query of the game: the prover's, the extractor's and the verifier's. A
protocol game produces many proofs from **one** run of the adversary. Bounding each proof's
extraction failure separately and adding them (`ROM/ExtractReduce.lean`) charges every query of
the run once per proof. The bad events are per query, though: a query of the shared run is bad or
not, whichever output proof later uses it. This file supplies the union bound that charges

* each query of the shared run **once** (with the common bad predicate `badA`), and
* per output `j`, only the queries of its own continuation (the extractor's and the verifier's,
  `K j`) that the shared part did not make (with the output's own predicate `badK j`).

`Pr[event] ≤ B_A + Σ_{j ∈ J} B_K + Σ_i Pr[Q i]` (`prEvent_le_shared_suffix`), `B_A` the weighted
budget of the shared run and `B_K` that of one continuation; the last sum is for further events
of other computations (the failure events of the outputs, bounded separately).

* `SuffixBad`: the queries of a continuation `K` after a prefix `A` that are fresh (uncached and
  not made by `A`) and bad.
* **`prEvent_suffixBad_le`** (finite key set, eager table, any initial cache): the prefix's queries
  are free, the continuation's cost its weighted budget. By induction on the prefix: a query of
  the prefix is exposed and cached, without charge (as VCVio's
  `prEvent_freshBadQuery_le_weighted`, but charging nothing); at the end, `Fresh.lean`'s
  `prEvent_freshBadQuery_le_of_cached` for the continuation with the prefix's cache. The bad events
  may read the whole table, with the cache-size form of `Fresh.lean` (needed for the combined
  relations' `H₂²` charge).
* **`prEvent_le_shared_suffix`**: the lazy random oracle on any key type, through one finite key
  set `S` (VCVio's `restrictQueries`, `extendTable`).

The prefix `A j` of an output need not be the shared run `A` itself: it suffices that a query of
`A j` that is bad for output `j` is a bad query of `A` for `badA` (the trace hypothesis is stated
that way). For a game whose provers are projections of one run (Moussaka's `PI`, `PR`), `A j` is
that run for every `j`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM

variable {D : Type} {R : D → Type} {α γ δ : Type}

section Finite

variable [DecidableEq D] [∀ d, Nonempty (R d)] [∀ d, SampleableType (R d)]
  (S : Finset D) [SampleableType ((d : S) → R d.val)]

/-- A key is not cached (vacuous outside `S`). -/
def CNone (c : (ofFn fun d : S => R d.val).QueryCache) (d : D) : Prop :=
  ∀ h : d ∈ S, c ⟨d, h⟩ = none

/-- The complete table seen by the computations: the table on `S` completed by the cache. -/
noncomputable def tabC (c : (ofFn fun d : S => R d.val).QueryCache) (G : (d : S) → R d.val) :
    ∀ d, R d :=
  extendTable S (completeTable c G)

/-- **A fresh bad query of the continuation `K` after the prefix `A`**, against the table `X`
with cache `c`: a query of `K`'s run that is uncached, was not made by `A`, and is bad. -/
def SuffixBad (A : OracleComp (ofFn R) γ) (K : γ → OracleComp (ofFn R) δ)
    (bad : D → (∀ d, R d) → Prop) (c : (ofFn fun d : S => R d.val).QueryCache)
    (X : ∀ d, R d) : Prop :=
  ∃ e ∈ tableQueryLog (K (evalWithAnswerFn (QueryImpl.ofFn X) A)) X,
    CNone S c e.1 ∧ e.1 ∉ (tableQueryLog A X).map Sigma.fst ∧ bad e.1 X

omit [∀ d, SampleableType (R d)] [SampleableType ((d : S) → R d.val)] in
lemma tabC_cacheQuery (c : (ofFn fun d : S => R d.val).QueryCache) (G : (d : S) → R d.val)
    (t : S) : tabC S (c.cacheQuery t (completeTable c G t)) G = tabC S c G := by
  simp only [tabC, completeTable_cacheQuery_value]

omit [∀ d, SampleableType (R d)] [SampleableType ((d : S) → R d.val)] in
lemma tabC_update_of_some (c : (ofFn fun d : S => R d.val).QueryCache) (G : (d : S) → R d.val)
    {t : S} {v : R t.val} (hc : c t = some v) (u : R t.val) :
    tabC S c (Function.update G t u) = tabC S c G := by
  simp only [tabC, completeTable_update_of_some c G hc u]

omit [DecidableEq D] [∀ d, SampleableType (R d)] [SampleableType ((d : S) → R d.val)] in
lemma tabC_val (c : (ofFn fun d : S => R d.val).QueryCache) (G : (d : S) → R d.val) (t : S) :
    tabC S c G t.val = completeTable c G t := extendTable_subtype S _ t

omit [DecidableEq D] [∀ d, SampleableType (R d)] [SampleableType ((d : S) → R d.val)] in
/-- The base case: the continuation alone, from the cache `c`, is a fresh bad query of its
restriction to `S`. -/
lemma suffixBad_pure_imp (a : γ) (K : γ → OracleComp (ofFn R) δ) (h : AllQueriesSatisfy (K a) (· ∈ S))
    (bad : D → (∀ d, R d) → Prop) (c : (ofFn fun d : S => R d.val).QueryCache)
    (G : (d : S) → R d.val) (hs : SuffixBad S (pure a) K bad c (tabC S c G)) :
    freshBadQuery (restrictQueries S (K a) h) c G (fun t g => bad t.val (extendTable S g)) := by
  obtain ⟨e, he, hc, -, hb⟩ := hs
  simp only [evalWithAnswerFn_pure] at he
  have hres : (fun d : S => tabC S c G d.val) = completeTable c G :=
    funext fun d => tabC_val S c G d
  have hlog := tableQueryLog_restrictQueries S (K a) h (tabC S c G)
  rw [hres] at hlog
  rw [← hlog] at he
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
  exact ⟨q, hq, hc q.1.2, hb⟩

/-- **The fresh bad queries of a continuation after a prefix, the prefix free.** For a prefix `A`
(at most `nA` queries) and a continuation `K` (weighted budget `B`, at most `nK` queries), started
from a cache with at most `m` keys (`m + nA + nK ≤ N`): if a fresh query `t` is bad with
probability `≤ error t` over the uncached cells of every cache with fewer than `N` keys, then a
query of `K` that is uncached, not made by `A`, and bad has probability `≤ B`. -/
theorem prEvent_suffixBad_le (A : OracleComp (ofFn R) γ) (K : γ → OracleComp (ofFn R) δ)
    (h : AllQueriesSatisfy (A >>= K) (· ∈ S)) (error : D → ℝ≥0∞) (B : ℝ≥0∞)
    (hB : ∀ a, WorstCaseCostBound (K a) ⟨error⟩ B) (nA nK : ℕ) (hnA : IsTotalQueryBound A nA)
    (hnK : ∀ a, IsTotalQueryBound (K a) nK) (N : ℕ) (bad : D → (∀ d, R d) → Prop)
    (hbad : ∀ (c' : (ofFn fun d : S => R d.val).QueryCache) (t : S), c' t = none →
      (cachedKeys c').card < N →
      Pr{let g ← $ᵗ ((d : S) → R d.val)}[bad t.val (extendTable S (completeTable c' g))] ≤
        error t.val)
    (c : (ofFn fun d : S => R d.val).QueryCache) (m : ℕ) (hm : (cachedKeys c).card ≤ m)
    (hmN : m + nA + nK ≤ N) :
    Pr{let G ← $ᵗ ((d : S) → R d.val)}[SuffixBad S A K bad c (tabC S c G)] ≤ B := by
  classical
  induction A using OracleComp.inductionOn generalizing c m nA with
  | pure a =>
      have h' : AllQueriesSatisfy (K a) (· ∈ S) := by simpa using h
      refine (prEvent_mono _ _ _ fun G hs => suffixBad_pure_imp S a K h' bad c G hs).trans ?_
      exact prEvent_freshBadQuery_le_of_cached (restrictQueries S (K a) h')
        (fun t => error t.val) B (restrictQueries_costBound' S _ h' error B (hB a)) nK
        (restrictQueries_queryBound' S _ h' nK (hnK a)) c m N hm (by omega)
        (fun t g => bad t.val (extendTable S g)) hbad
  | query_bind t k ih =>
      rw [bind_assoc] at h
      obtain ⟨ht, hk⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      obtain ⟨hn0, hnk⟩ := isTotalQueryBound_query_bind_iff.mp hnA
      let t' : S := ⟨t, ht⟩
      -- one step of the prefix: the query `t` is not a fresh query of `K` and drops out
      have hstep : ∀ (c' : (ofFn fun d : S => R d.val).QueryCache) (X : ∀ d, R d),
          SuffixBad S (liftM ((ofFn R).query t) >>= k) K bad c' X →
          (∃ e ∈ tableQueryLog (K (evalWithAnswerFn (QueryImpl.ofFn X) (k (X t)))) X,
            CNone S c' e.1 ∧ e.1 ≠ t ∧ e.1 ∉ (tableQueryLog (k (X t)) X).map Sigma.fst ∧
              bad e.1 X) := by
        intro c' X ⟨e, he, hc, hn, hb⟩
        simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply,
          tableQueryLog_query_bind, List.map_cons, List.mem_cons, not_or] at he hn
        exact ⟨e, he, hc, hn.1, hn.2, hb⟩
      cases hc : c t' with
      | some u =>
          refine (prEvent_mono _ _ _ fun G hs => ?_).trans
            (ih u (hk u) (nA - 1) (hnk u) c m hm (by omega))
          obtain ⟨e, he, hce, -, hn, hb⟩ := hstep c _ hs
          have hX : tabC S c G t = u := (tabC_val S c G t').trans (by simp [completeTable, hc])
          rw [hX] at he hn
          exact ⟨e, he, hce, hn, hb⟩
      | none =>
          -- expose the fresh answer at `t'` and cache it
          let ev : ((d : S) → R d.val) → Prop := fun G =>
            SuffixBad S (k (completeTable c G t')) K bad (c.cacheQuery t' (completeTable c G t'))
              (tabC S (c.cacheQuery t' (completeTable c G t')) G)
          refine (prEvent_mono _ _ ev fun G hs => ?_).trans ?_
          · obtain ⟨e, he, hce, hne, hn, hb⟩ := hstep c _ hs
            have hX : tabC S c G t = completeTable c G t' := tabC_val S c G t'
            rw [hX] at he hn
            simp only [ev, tabC_cacheQuery]
            refine ⟨e, he, fun h' => ?_, hn, hb⟩
            have hne' : (⟨e.1, h'⟩ : S) ≠ t' := fun heq => hne (congrArg Subtype.val heq)
            rw [QueryCache.cacheQuery_of_ne _ _ hne']
            exact hce h'
          · have hval : ∀ (G : (d : S) → R d.val) (u : R t'.val),
                completeTable c (Function.update G t' u) t' = u := fun G u => by
              simp [completeTable, hc]
            have hsome : ∀ u : R t'.val, (c.cacheQuery t' u) t' = some u := fun u =>
              QueryCache.cacheQuery_self _ _ _
            have hrw : Pr{let G ← $ᵗ ((d : S) → R d.val)}[ev G] =
                Pr{let u ← $ᵗ (R t'.val); let G ← $ᵗ ((d : S) → R d.val)}[
                  SuffixBad S (k u) K bad (c.cacheQuery t' u) (tabC S (c.cacheQuery t' u) G)] := by
              rw [prEvent_uniformTable_update t']
              simp only [ev, hval, tabC_update_of_some S _ _ (hsome _)]
            rw [hrw]
            simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
              id_eq] using
              (prEvent_bind_le_of_forall_le ($ᵗ (R t'.val))
                (fun u => (fun G => SuffixBad S (k u) K bad (c.cacheQuery t' u)
                  (tabC S (c.cacheQuery t' u) G)) <$> ($ᵗ ((d : S) → R d.val))) id
                (fun u => by
                  simpa using ih u (hk u) (nA - 1) (hnk u) (c.cacheQuery t' u) (m + 1)
                    ((card_cachedKeys_cacheQuery c t' u).trans (by omega)) (by omega)))

end Finite

/-! ## The lazy random oracle -/

section Lazy

variable [DecidableEq D] [∀ d, Nonempty (R d)] [∀ d, SampleableType (R d)]

/-- **Lazy = eager on a finite key set** (`ROM/ExtractReduce.lean`'s `prEvent_eq_extendTable`,
repeated here to keep this file light). -/
theorem prEvent_eq_extendTable' (S : Finset D) [SampleableType ((d : S) → R d.val)]
    (oa : OracleComp (OracleSpec.ofFn R) α) (hS : AllQueriesSatisfy oa (· ∈ S)) (P : α → Prop) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[P r] =
      Pr{let G ← $ᵗ ((d : S) → R d.val)}[
        P (evalWithAnswerFn (QueryImpl.ofFn (extendTable S G)) oa)] := by
  let : MeasurableSpace α := ⊤
  have e1 : (simulateQ randomOracle (restrictQueries S oa hS)).run' ∅ =
      (simulateQ randomOracle oa).run' ∅ := randomOracle_restrictQueries S oa hS ∅
  rw [← e1]
  have h1 := evalDist_simulateQ_randomOracle_run'_eq_completeTable (restrictQueries S oa hS) ∅
  simp only [completeTable_empty] at h1
  rw [(EvalDistEq.of_evalDist_eq h1).prEvent_eq P]
  simp only [prEvent_norm]
  congr 2
  funext G
  have hG : (fun d : S => extendTable S G d.val) = G := funext (extendTable_subtype S G)
  have ha := evalWithAnswerFn_restrictQueries S oa hS (extendTable S G)
  rw [hG] at ha
  rw [ha]

/-- **The shared-run union bound** (simultaneous extraction, generic). Against the lazy random
oracle, an event of a computation `oa` is bounded by

    B_A + Σ_{j ∈ J} B_K + Σ_{i ∈ I} Pr[Q i | ob i]

if at every complete table the event implies (`htrace`) that

* some query of the **shared run** `A` is bad for the common predicate `badA` (charged once, at
  `A`'s weighted budget `B_A`), or
* for some output `j ∈ J`, a query of the **continuation** `K j` after its prefix `A' j` that the
  prefix did not make is bad for `badK j` (charged at the continuation's budget `B_K`, the
  prefix's queries free), or
* some further event `Q i` of a computation `ob i` holds.

`S` is a finite key set containing every query of the computations (and the cells the bad
events read); the bad events are bounded over the uncached cells of every cache with fewer than
`N` keys, `N` at least each computation's total query count. -/
theorem prEvent_le_shared_suffix {ι κ γ' δ' α₂ : Type} (S : Finset D)
    [SampleableType ((d : S) → R d.val)]
    (oa : OracleComp (ofFn R) α) (event : α → Prop) (hSo : AllQueriesSatisfy oa (· ∈ S))
    (A : OracleComp (ofFn R) γ) (hSA : AllQueriesSatisfy A (· ∈ S)) (error : D → ℝ≥0∞)
    (BA : ℝ≥0∞) (hBA : WorstCaseCostBound A ⟨error⟩ BA) (n₀ : ℕ) (hn₀ : IsTotalQueryBound A n₀)
    (badA : D → (∀ d, R d) → Prop)
    (J : Finset ι) (A' : ι → OracleComp (ofFn R) γ') (K : ι → γ' → OracleComp (ofFn R) δ')
    (hSK : ∀ j ∈ J, AllQueriesSatisfy (A' j >>= K j) (· ∈ S)) (BK : ℝ≥0∞)
    (hBK : ∀ j a, WorstCaseCostBound (K j a) ⟨error⟩ BK) (nA nK : ℕ)
    (hnA : ∀ j, IsTotalQueryBound (A' j) nA) (hnK : ∀ j a, IsTotalQueryBound (K j a) nK)
    (badK : ι → D → (∀ d, R d) → Prop)
    (I : Finset κ) (ob : κ → OracleComp (ofFn R) α₂) (Q : κ → α₂ → Prop)
    (hSI : ∀ i ∈ I, AllQueriesSatisfy (ob i) (· ∈ S))
    (N : ℕ) (hN₀ : n₀ ≤ N) (hN : nA + nK ≤ N)
    (hbadA : ∀ (c : (ofFn fun d : S => R d.val).QueryCache) (t : S), c t = none →
      (cachedKeys c).card < N →
      Pr{let g ← $ᵗ ((d : S) → R d.val)}[badA t.val (extendTable S (completeTable c g))] ≤
        error t.val)
    (hbadK : ∀ j ∈ J, ∀ (c : (ofFn fun d : S => R d.val).QueryCache) (t : S), c t = none →
      (cachedKeys c).card < N →
      Pr{let g ← $ᵗ ((d : S) → R d.val)}[badK j t.val (extendTable S (completeTable c g))] ≤
        error t.val)
    (htrace : ∀ g, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      (∃ e ∈ tableQueryLog A g, badA e.1 g) ∨
      (∃ j ∈ J, ∃ e ∈ tableQueryLog (K j (evalWithAnswerFn (QueryImpl.ofFn g) (A' j))) g,
        e.1 ∉ (tableQueryLog (A' j) g).map Sigma.fst ∧ badK j e.1 g) ∨
      (∃ i ∈ I, Q i (evalWithAnswerFn (QueryImpl.ofFn g) (ob i)))) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤
      BA + ∑ _j ∈ J, BK + ∑ i ∈ I, Pr{let r ← (simulateQ randomOracle (ob i)).run' ∅}[Q i r] := by
  classical
  let mG := $ᵗ ((d : S) → R d.val)
  have hempty : ∀ G : (d : S) → R d.val, tabC S ∅ G = extendTable S G := fun G => by
    simp only [tabC, completeTable_empty]
  have hcnone : ∀ d, CNone S (∅ : (ofFn fun d : S => R d.val).QueryCache) d := fun _ _ => rfl
  rw [prEvent_eq_extendTable' S oa hSo]
  rw [Finset.sum_congr rfl fun i hi => prEvent_eq_extendTable' S (ob i) (hSI i hi) (Q i)]
  -- the three parts, as events of the uniform table on `S`
  let X₁ : ((d : S) → R d.val) → Prop := fun G =>
    SuffixBad S (pure () : OracleComp (ofFn R) Unit) (fun _ => A) badA ∅ (tabC S ∅ G)
  let X₂ : ι → ((d : S) → R d.val) → Prop := fun j G =>
    SuffixBad S (A' j) (K j) (badK j) ∅ (tabC S ∅ G)
  let X₃ : κ → ((d : S) → R d.val) → Prop := fun i G =>
    Q i (evalWithAnswerFn (QueryImpl.ofFn (extendTable S G)) (ob i))
  refine (prEvent_mono mG _ (fun G => X₁ G ∨ ((∃ j ∈ J, X₂ j G) ∨ (∃ i ∈ I, X₃ i G)))
    fun G hG => ?_).trans ?_
  · rcases htrace _ hG with ⟨e, he, hb⟩ | ⟨j, hj, e, he, hn, hb⟩ | ⟨i, hi, hq⟩
    · left
      simp only [X₁, SuffixBad, tableQueryLog_pure, List.map_nil,
        List.not_mem_nil, not_false_eq_true, true_and, hempty]
      exact ⟨e, he, hcnone _, hb⟩
    · right; left
      refine ⟨j, hj, ?_⟩
      simp only [X₂, SuffixBad, hempty]
      exact ⟨e, he, hcnone _, hn, hb⟩
    · right; right
      exact ⟨i, hi, hq⟩
  rw [add_assoc]
  refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ((prEvent_or_le _ _ _).trans
    (add_le_add ?_ (prEvent_exists_finset_le I mG X₃))))
  · exact prEvent_suffixBad_le S (pure ()) (fun _ => A) (by simpa using hSA) error BA
      (fun _ => hBA) 0 n₀ trivial (fun _ => hn₀) N badA hbadA ∅ 0
      (by rw [card_cachedKeys_empty]) (by omega)
  · refine (prEvent_exists_finset_le J mG X₂).trans (Finset.sum_le_sum fun j hj => ?_)
    exact prEvent_suffixBad_le S (A' j) (K j) (hSK j hj) error BK (hBK j) nA nK (hnA j)
      (hnK j) N (badK j) (hbadK j hj) ∅ 0 (by rw [card_cachedKeys_empty]) (by omega)

/-- **The single-cell form of the bad-event hypothesis gives the cache-size form**: a bound when
the cell `t` alone is resampled, for every background table, holds over the uncached cells of any
cache not containing `t`. -/
theorem cached_of_cell (S : Finset D) [SampleableType ((d : S) → R d.val)]
    (bad : D → (∀ d, R d) → Prop) (error : D → ℝ≥0∞)
    (hbad : ∀ t g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ error t)
    (c : (ofFn fun d : S => R d.val).QueryCache) (t : S) (hc : c t = none) :
    Pr{let g ← $ᵗ ((d : S) → R d.val)}[bad t.val (extendTable S (completeTable c g))] ≤
      error t.val := by
  refine prEvent_completeTable_cell_le c t hc (fun t G => bad t.val (extendTable S G)) _
    fun G => ?_
  simp only [extendTable_update]
  exact hbad t.val _

end Lazy

end VoleMole.ROM
