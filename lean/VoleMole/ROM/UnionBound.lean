import VoleMole.ROM.Basic

/-!
# The union bound over random-oracle queries (plan M5)

The generic lemma of M5: if every query to domain `k` is "bad" with probability `≤ ε k` over its
fresh answer, then an adversary making at most `q k` queries to each domain `k` meets a bad query
with probability `≤ Σ_k q k · ε k`.

VCVio already has this (`prEvent_randomOracle_le_of_bad_queries_weighted`,
`QueryTracking/RandomOracle/FreshQuery.lean`), in a stronger form than the plan's sketch:
* the bad predicate `bad t g` may read the **whole answer table** `g` (other cells, including cells
  never queried), as long as resampling the tested cell `t` alone makes it bad with probability
  `≤ ε`, for every background table. This is how "data fixed before the query" is expressed: a
  chain prefix parsed from the `H₂¹` input may also depend on `H₁`, `H₄`, … answers, but not on
  the answer at its own cell;
* the event is about the adversary's output, and the link to bad queries is a deterministic
  implication `htrace` over complete tables (VCVio's `evalWithAnswerFn`, `tableQueryLog`);
* the budget is a weighted pathwise cost (`WorstCaseCostBound`).

This file supplies the per-domain query count of the plan, `IsKindQueryBound oa q` (at most `q k`
queries to domain `k` on every path, repeated queries counted), turns it into VCVio's weighted
budget `Σ_{k ∈ K} q k · ε k` (`worstCaseCostBound_of_kindQueryBound`), and states the union bound
for the hash oracles of `ROM/Basic.lean`:
* `prEvent_exists_bad_query_le`: bad predicates on the table;
* `prEvent_exists_bad_answer_le`: bad predicates on a query's own input and answer (the plan's
  form), with the per-answer bound a phase-A `prU` bound.
-/

open ENNReal

namespace VoleMole.ROM

open VoleMole.Prob OracleComp OracleSpec

variable {α : Type}

/-- **At most `q k` queries to each domain `k`**, on every path (repeated queries count). -/
def IsKindQueryBound (oa : OracleComp spec α) (q : Kind → ℕ) : Prop :=
  IsQueryBound oa q (fun t b => 0 < b t.1) (fun t b => Function.update b t.1 (b t.1 - 1))

lemma isKindQueryBound_query_bind_iff {t : Dom} {k : Ans t → OracleComp spec α}
    {q : Kind → ℕ} :
    IsKindQueryBound (liftM (spec.query t) >>= k) q ↔
      0 < q t.1 ∧ ∀ u, IsKindQueryBound (k u) (Function.update q t.1 (q t.1 - 1)) :=
  Iff.rfl

/-- One query to `k₀` out of a budget `q`: its charge plus the rest (`ε` vanishes outside `K`). -/
lemma sum_update_pred (K : Finset Kind) (q : Kind → ℕ) (ε : Kind → ℝ≥0∞) {k₀ : Kind}
    (hK : ∀ k ∉ K, ε k = 0) (h₀ : 0 < q k₀) :
    ε k₀ + ∑ k ∈ K, (Function.update q k₀ (q k₀ - 1) k : ℝ≥0∞) * ε k = ∑ k ∈ K, q k * ε k := by
  by_cases hk₀ : k₀ ∈ K
  · rw [← Finset.add_sum_erase _ _ hk₀, ← Finset.add_sum_erase _ _ hk₀, Function.update_self,
      ← add_assoc]
    congr 1
    · conv_lhs => lhs; rw [← one_mul (ε k₀)]
      rw [← add_mul]
      congr 1
      exact_mod_cast (by omega : 1 + (q k₀ - 1) = q k₀)
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  · rw [hK _ hk₀, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hk₀)]

/-- **Per-domain query counts give VCVio's weighted budget** `Σ_{k ∈ K} q k · ε k`, charging
`ε k` for each query to domain `k` (`ε` vanishes outside `K`; queries to other domains are free but
still counted by `q`). -/
theorem worstCaseCostBound_of_kindQueryBound (oa : OracleComp spec α) (K : Finset Kind)
    (ε : Kind → ℝ≥0∞) (hK : ∀ k ∉ K, ε k = 0) (q : Kind → ℕ) (hq : IsKindQueryBound oa q) :
    WorstCaseCostBound oa ⟨fun t => ε t.1⟩ (∑ k ∈ K, q k * ε k) := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure a => simp
  | query_bind t k ih =>
      obtain ⟨h₀, hk⟩ := isKindQueryBound_query_bind_iff.1 hq
      rw [worstCaseCostBound_query_bind_iff]
      intro u z hz
      have := (worstCaseCostBound_iff_support_bound _ _ _).1 (ih u _ (hk u)) z hz
      rw [← sum_update_pred K q ε hK h₀]
      exact add_le_add le_rfl this

/-- **The union bound over queries.** An adversary `oa` making at most `q k` queries to each
domain `k`, run against the lazy random oracle: if the event implies, for
every complete answer table, that some logged query `t` is bad (`htrace`), and each bad predicate
has probability `≤ ε t.1` when the cell `t` alone is resampled (`hbad`), then the event has
probability `≤ Σ_{k ∈ K} q k · ε k` (`ε` vanishing outside `K`). -/
theorem prEvent_exists_bad_query_le (oa : OracleComp spec α) (q : Kind → ℕ)
    (hq : IsKindQueryBound oa q) (event : α → Prop) (bad : Dom → Table → Prop) (K : Finset Kind)
    (ε : Kind → ℝ≥0∞) (hK : ∀ k ∉ K, ε k = 0)
    (hbad : ∀ t g, Pr{let u ← $ᵗ (Ans t)}[bad t (Function.update g t u)] ≤ ε t.1)
    (htrace : ∀ g : Table, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ e ∈ tableQueryLog oa g, bad e.1 g) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤ ∑ k ∈ K, q k * ε k :=
  prEvent_randomOracle_le_of_bad_queries_weighted oa (fun t => ε t.1) _
    (worstCaseCostBound_of_kindQueryBound oa K ε hK q hq) event bad hbad htrace

/-- **The union bound, for bad answers** (the plan's form): `bad t u` reads only the query `t` and
its answer `u`, and is bounded by a phase-A uniform probability. -/
theorem prEvent_exists_bad_answer_le (oa : OracleComp spec α) (q : Kind → ℕ)
    (hq : IsKindQueryBound oa q) (event : α → Prop) (bad : (t : Dom) → Ans t → Prop)
    (K : Finset Kind) (ε : Kind → ℝ≥0∞) (hK : ∀ k ∉ K, ε k = 0)
    (hbad : ∀ t, prU (Ans t) (bad t) ≤ ε t.1)
    (htrace : ∀ g : Table, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ e ∈ tableQueryLog oa g, bad e.1 (g e.1)) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤ ∑ k ∈ K, q k * ε k :=
  prEvent_exists_bad_query_le oa q hq event (fun t g => bad t (g t)) K ε hK
    (fun t g => by simpa only [Function.update_self] using prEvent_uniformSample_le (hbad t))
    htrace

end VoleMole.ROM
