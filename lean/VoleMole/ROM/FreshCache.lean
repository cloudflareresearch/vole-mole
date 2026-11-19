import VoleMole.ROM.Fresh

/-!
# The union bound over queries, with a bad event that reads the cache (plan M6)

VCVio's `prEvent_freshBadQuery_le` and `ROM/Fresh.lean`'s `prEvent_freshBadQuery_le_of_cached`
test a fresh query `t` with a predicate `bad t g` of the (completed) table only. A collision bound
for an ideal cipher (`ROM/CipherBind.lean`) needs to know which cells were queried *before* `t`:
a collision whose other cells were already queried is the one to charge at `t`, and its
probability is counted by the queried cells. Here the bad predicate also receives the cache of the
earlier queries.

* `cacheOfLog c pre`: the cache `c` extended by the entries of a log prefix `pre`;
  `cacheOfLog_eq_none`: a cell is uncached iff it is not in `c` and not in `pre`.
* `freshBadC oa c g bad`: some query of `oa`'s log (against `completeTable c g`), at a cell absent
  from `c` and from the earlier log, is bad for the cache of the earlier log.
* **`prEvent_freshBadC_le_of_cached`**: if a fresh query `t` is bad with probability `≤ ε` over
  the uncached cells, for every cache `c'` without `t` and with fewer than `N` cached cells, then
  an `n`-query computation started from a cache of `m ≤ N − n` cells meets a fresh bad query with
  probability `≤ n · ε`. The proof is VCVio's, with the cache passed along.
* `prEvent_le_of_freshBadC`: the eager form used below (finite key type, empty cache).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM

variable {D α : Type} {R : D → Type} [DecidableEq D]

/-! ## The cache of a log prefix -/

/-- **The cache after a log prefix**: `c`, then every entry of `pre` cached in order. -/
def cacheOfLog (c : (ofFn R).QueryCache) : QueryLog (ofFn R) → (ofFn R).QueryCache
  | [] => c
  | q :: l => cacheOfLog (c.cacheQuery q.1 q.2) l

@[simp] lemma cacheOfLog_nil (c : (ofFn R).QueryCache) : cacheOfLog c [] = c := rfl

@[simp] lemma cacheOfLog_cons (c : (ofFn R).QueryCache) (q : (t : D) × R t)
    (l : QueryLog (ofFn R)) : cacheOfLog c (q :: l) = cacheOfLog (c.cacheQuery q.1 q.2) l := rfl

lemma cacheQuery_eq_none_iff (c : (ofFn R).QueryCache) (t : D) (u : R t) (d : D) :
    c.cacheQuery t u d = none ↔ c d = none ∧ t ≠ d := by
  by_cases h : d = t
  · subst h
    simp
  · rw [QueryCache.cacheQuery_of_ne c u h]
    exact ⟨fun hd => ⟨hd, Ne.symm h⟩, fun hd => hd.1⟩

/-- **A cell is uncached after a prefix** iff it was not cached and the prefix does not query it. -/
lemma cacheOfLog_eq_none (c : (ofFn R).QueryCache) (l : QueryLog (ofFn R)) (d : D) :
    cacheOfLog c l d = none ↔ c d = none ∧ ∀ q ∈ l, q.1 ≠ d := by
  induction l generalizing c with
  | nil => simp
  | cons q l ih =>
    rw [cacheOfLog_cons, ih, cacheQuery_eq_none_iff]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-- Caching a cell at its cached answer changes nothing. -/
lemma cacheQuery_eq_self (c : (ofFn R).QueryCache) {t : D} {u : R t} (h : c t = some u) :
    c.cacheQuery t u = c := by
  ext s v
  by_cases hs : s = t
  · subst hs
    rw [QueryCache.cacheQuery_self, h]
  · rw [QueryCache.cacheQuery_of_ne c u hs]

/-! ## Fresh bad queries that read the cache -/

/-- **A fresh bad query, reading the cache**: in the log of `oa` against `completeTable c g`, some
entry `q` at a cell that is neither in `c` nor queried earlier is bad for the cache of the earlier
log (`cacheOfLog c pre`) and the completed table. -/
def freshBadC (oa : OracleComp (ofFn R) α) (c : (ofFn R).QueryCache) (g : ∀ d, R d)
    (bad : D → (ofFn R).QueryCache → (∀ d, R d) → Prop) : Prop :=
  ∃ pre q post, tableQueryLog oa (completeTable c g) = pre ++ q :: post ∧
    cacheOfLog c pre q.1 = none ∧ bad q.1 (cacheOfLog c pre) (completeTable c g)

lemma not_freshBadC_pure (a : α) (c : (ofFn R).QueryCache) (g : ∀ d, R d)
    (bad : D → (ofFn R).QueryCache → (∀ d, R d) → Prop) :
    ¬freshBadC (pure a : OracleComp (ofFn R) α) c g bad := by
  rintro ⟨pre, q, post, h, -⟩
  rw [tableQueryLog_pure] at h
  exact (List.append_ne_nil_of_right_ne_nil pre (List.cons_ne_nil q post)) h.symm

/-- A cached query adds no fresh bad query. -/
theorem freshBadC_query_bind_of_some (t : D) (k : R t → OracleComp (ofFn R) α)
    (c : (ofFn R).QueryCache) (g : ∀ d, R d) (bad : D → (ofFn R).QueryCache → (∀ d, R d) → Prop)
    {u : R t} (hc : c t = some u) :
    freshBadC (liftM ((ofFn R).query t) >>= k) c g bad ↔ freshBadC (k u) c g bad := by
  have hG : completeTable c g t = u := by simp [completeTable, hc]
  unfold freshBadC
  rw [tableQueryLog_query_bind, hG]
  constructor
  · rintro ⟨pre, q, post, h, hn, hb⟩
    cases pre with
    | nil =>
      cases h
      simp [hc] at hn
    | cons p pre =>
      rw [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [cacheOfLog_cons, cacheQuery_eq_self c hc] at hn hb
      exact ⟨pre, q, post, h, hn, hb⟩
  · rintro ⟨pre, q, post, h, hn, hb⟩
    refine ⟨⟨t, u⟩ :: pre, q, post, by rw [h]; rfl, ?_, ?_⟩ <;>
      simpa only [cacheOfLog_cons, cacheQuery_eq_self c hc]

/-- A fresh query is bad itself, or the continuation meets a fresh bad query with the query
cached. -/
theorem freshBadC_query_bind_of_none (t : D) (k : R t → OracleComp (ofFn R) α)
    (c : (ofFn R).QueryCache) (g : ∀ d, R d) (bad : D → (ofFn R).QueryCache → (∀ d, R d) → Prop)
    (hc : c t = none) :
    freshBadC (liftM ((ofFn R).query t) >>= k) c g bad ↔
      bad t c (completeTable c g) ∨
        freshBadC (k (completeTable c g t)) (c.cacheQuery t (completeTable c g t)) g bad := by
  unfold freshBadC
  rw [tableQueryLog_query_bind, completeTable_cacheQuery_value]
  constructor
  · rintro ⟨pre, q, post, h, hn, hb⟩
    cases pre with
    | nil =>
      cases h
      exact Or.inl hb
    | cons p pre =>
      rw [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact Or.inr ⟨pre, q, post, h, hn, hb⟩
  · rintro (hb | ⟨pre, q, post, h, hn, hb⟩)
    · exact ⟨[], ⟨t, completeTable c g t⟩, _, rfl, hc, hb⟩
    · exact ⟨⟨t, completeTable c g t⟩ :: pre, q, post, by rw [h]; rfl, hn, hb⟩

/-- Changing the table at a cached cell changes nothing. -/
theorem freshBadC_update_of_some (oa : OracleComp (ofFn R) α) (c : (ofFn R).QueryCache)
    (g : ∀ d, R d) (bad : D → (ofFn R).QueryCache → (∀ d, R d) → Prop) {t : D} {v : R t}
    (hc : c t = some v) (u : R t) :
    freshBadC oa c (Function.update g t u) bad ↔ freshBadC oa c g bad := by
  simp only [freshBadC, completeTable_update_of_some c g hc u]

section Finite

variable [Fintype D] [∀ d, SampleableType (R d)] [SampleableType (∀ d, R d)]

/-- Expose the fresh answer before the continuation (VCVio's `prEvent_freshBadQuery_suffix`). -/
theorem prEvent_freshBadC_suffix (t : D) (k : R t → OracleComp (ofFn R) α)
    (c : (ofFn R).QueryCache) (hc : c t = none)
    (bad : D → (ofFn R).QueryCache → (∀ d, R d) → Prop) :
    Pr{let g ← $ᵗ (∀ d, R d)}[freshBadC (k (completeTable c g t))
      (c.cacheQuery t (completeTable c g t)) g bad] =
    Pr{let u ← $ᵗ (R t); let g ← $ᵗ (∀ d, R d)}[freshBadC (k u) (c.cacheQuery t u) g bad] := by
  rw [prEvent_uniformTable_update t]
  have hval (g : (d : D) → R d) (u : R t) : completeTable c (Function.update g t u) t = u := by
    simp [completeTable, hc]
  simp_rw [hval, freshBadC_update_of_some _ _ _ _ (QueryCache.cacheQuery_self _ _ _)]

/-- **The bad-query bound with a cache-reading bad event**, finite key type. An `n`-query
computation, started from a cache with at most `m` cells (`m + n ≤ N`): if a fresh query `t` is
bad, for the current cache `c'`, with probability `≤ ε` over the uncached cells, whenever `c'` has
fewer than `N` cells, then a fresh bad query occurs with probability `≤ n · ε`. -/
theorem prEvent_freshBadC_le_of_cached (oa : OracleComp (ofFn R) α) (n : ℕ)
    (hn : IsTotalQueryBound oa n) (c : (ofFn R).QueryCache) (m N : ℕ)
    (hm : (cachedKeys c).card ≤ m) (hmN : m + n ≤ N)
    (bad : D → (ofFn R).QueryCache → (∀ d, R d) → Prop) (ε : ℝ≥0∞)
    (hbad : ∀ (c' : (ofFn R).QueryCache) t, c' t = none → (cachedKeys c').card < N →
      Pr{let g ← $ᵗ (∀ d, R d)}[bad t c' (completeTable c' g)] ≤ ε) :
    Pr{let g ← $ᵗ (∀ d, R d)}[freshBadC oa c g bad] ≤ n * ε := by
  induction oa using OracleComp.inductionOn generalizing c n m with
  | pure a => simp [not_freshBadC_pure]
  | query_bind t k ih =>
      obtain ⟨hn0, hnk⟩ := isTotalQueryBound_query_bind_iff.mp hn
      cases hc : c t with
      | some u =>
          simp_rw [freshBadC_query_bind_of_some t k c _ bad hc]
          exact (ih u (n - 1) (hnk u) c m hm (by omega)).trans (by gcongr; exact Nat.sub_le n 1)
      | none =>
          simp_rw [freshBadC_query_bind_of_none t k c _ bad hc]
          apply (prEvent_or_le _ _ _).trans
          have hfirst := hbad c t hc (by omega)
          have hrest : Pr{let g ← $ᵗ (∀ d, R d)}[freshBadC (k (completeTable c g t))
              (c.cacheQuery t (completeTable c g t)) g bad] ≤ ((n - 1 : ℕ) : ℝ≥0∞) * ε := by
            rw [prEvent_freshBadC_suffix t k c hc bad]
            simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
              pure_bind, id_eq] using
              (prEvent_bind_le_of_forall_le ($ᵗ (R t))
              (fun u => (fun g => freshBadC (k u) (c.cacheQuery t u) g bad) <$>
                ($ᵗ (∀ d, R d))) id
              (fun u => by
                simpa using ih u (n - 1) (hnk u) (c.cacheQuery t u) (m + 1)
                  ((card_cachedKeys_cacheQuery c t u).trans (by omega)) (by omega)))
          calc
            _ ≤ ε + ((n - 1 : ℕ) : ℝ≥0∞) * ε := add_le_add hfirst hrest
            _ = n * ε := by
              conv_lhs => lhs; rw [← one_mul ε]
              rw [← add_mul, ← Nat.cast_one, ← Nat.cast_add]
              congr 2
              omega

/-- **The eager bound**: an event of the uniform table that implies a fresh bad query of an
`n`-query computation `oa` (from the empty cache; the bad events of caches with fewer than `n`
cells bounded by `ε`) has probability `≤ n · ε`. -/
theorem prEvent_le_of_freshBadC (oa : OracleComp (ofFn R) α) (n : ℕ)
    (hn : IsTotalQueryBound oa n) (bad : D → (ofFn R).QueryCache → (∀ d, R d) → Prop)
    (ε : ℝ≥0∞)
    (hbad : ∀ (c : (ofFn R).QueryCache) t, c t = none → (cachedKeys c).card < n →
      Pr{let g ← $ᵗ (∀ d, R d)}[bad t c (completeTable c g)] ≤ ε)
    (P : (∀ d, R d) → Prop) (htrace : ∀ g, P g → freshBadC oa ∅ g bad) :
    Pr{let g ← $ᵗ (∀ d, R d)}[P g] ≤ n * ε :=
  (prEvent_mono _ _ _ htrace).trans
    (prEvent_freshBadC_le_of_cached oa n hn ∅ 0 n (by rw [card_cachedKeys_empty]) (by omega)
      bad ε hbad)

end Finite

/-- With the empty cache, `freshBadC` is about the log of `oa` against `g` itself. -/
lemma freshBadC_empty_iff (oa : OracleComp (ofFn R) α) (g : ∀ d, R d)
    (bad : D → (ofFn R).QueryCache → (∀ d, R d) → Prop) :
    freshBadC oa ∅ g bad ↔ ∃ pre q post, tableQueryLog oa g = pre ++ q :: post ∧
      (∀ p ∈ pre, p.1 ≠ q.1) ∧ bad q.1 (cacheOfLog ∅ pre) g := by
  simp only [freshBadC, completeTable_empty, cacheOfLog_eq_none]
  constructor
  · rintro ⟨pre, q, post, h, ⟨-, hn⟩, hb⟩
    exact ⟨pre, q, post, h, hn, hb⟩
  · rintro ⟨pre, q, post, h, hn, hb⟩
    exact ⟨pre, q, post, h, ⟨rfl, hn⟩, hb⟩

omit [DecidableEq D] in
/-- Every entry of the log against a table answers with the table. -/
theorem tableQueryLog_answer (oa : OracleComp (ofFn R) α) (g : ∀ d, R d) :
    ∀ q ∈ tableQueryLog oa g, q = ⟨q.1, g q.1⟩ := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
      intro q hq
      rw [tableQueryLog_query_bind, List.mem_cons] at hq
      rcases hq with rfl | hq
      · rfl
      · exact ih _ q hq

end VoleMole.ROM
