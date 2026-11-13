import VoleMole.ROM.OneMoreLemmaPFail

/-!
# Lemma P's term in the one-more game, bounded (gap G8)

`lean/docs/security/pomfrit.md` §6.4. This file bounds `Pr[∃ i ≤ ℓ, PFail i]` in PomFRIT's one-more
game with Lemma P's `E₁` (`e1P`), every term explicit, and plugs it into Theorem U1.

* **Logged computations** (`withLogQ`): a computation returning its own query log, so that the hits
  of `pfail_events` (events of the table and the log) are events of an output.
* **The hit and order-hit union bound** (`prEvent_hitOrder_le`): a chain hit or an order hit among
  the queries of a computation with `n k` queries of kind `k` has probability at most
  `Σ_k n k · (hitEps n … k + orderEps n k)`, with `orderEps n .h21 = n .h3 / 2^1088`.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM

open VoleMole.Prob VoleMole.Verifier

/-! ## A computation with its query log -/

section WithLog

variable {α : Type}

/-- **A computation returning its query log** (against a table, the log of `tableQueryLog`). -/
def withLogQ (oa : OracleComp spec α) : OracleComp spec (α × QueryLog spec) :=
  OracleComp.construct (C := fun _ => OracleComp spec (α × QueryLog spec))
    (fun a => pure (a, []))
    (fun t _ rec => liftM (spec.query t) >>= fun u => (fun r => (r.1, ⟨t, u⟩ :: r.2)) <$> rec u) oa

@[simp] lemma withLogQ_pure (a : α) : withLogQ (pure a : OracleComp spec α) = pure (a, []) := rfl

lemma withLogQ_query_bind (t : Dom) (k : Ans t → OracleComp spec α) :
    withLogQ (liftM (spec.query t) >>= k) =
      liftM (spec.query t) >>= fun u => (fun r => (r.1, ⟨t, u⟩ :: r.2)) <$> withLogQ (k u) := rfl

/-- Per table, the logged computation returns the output and the log. -/
theorem evalWithAnswerFn_withLogQ (g : Table) (oa : OracleComp spec α) :
    evalWithAnswerFn (QueryImpl.ofFn g) (withLogQ oa) =
      (evalWithAnswerFn (QueryImpl.ofFn g) oa, tableQueryLog oa g) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [withLogQ_query_bind]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_map, evalWithAnswerFn_liftM_query,
      QueryImpl.ofFn_apply, tableQueryLog_query_bind]
    rw [ih (g t)]

theorem tableQueryLog_withLogQ (g : Table) (oa : OracleComp spec α) :
    tableQueryLog (withLogQ oa) g = tableQueryLog oa g := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [withLogQ_query_bind, tableQueryLog_query_bind, tableQueryLog_query_bind,
      IC.tableQueryLog_map', ih (g t)]

theorem isKindQueryBound_withLogQ {oa : OracleComp spec α} {q : Kind → ℕ}
    (h : IsKindQueryBound oa q) : IsKindQueryBound (withLogQ oa) q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isKindQueryBound_query_bind_iff] at h
    rw [withLogQ_query_bind, isKindQueryBound_query_bind_iff]
    exact ⟨h.1, fun u => (isQueryBound_map_iff _ _ _ _ _).2 (ih u (h.2 u))⟩

end WithLog

end VoleMole.ROM

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC

/-! ## Chain hits and order hits, union bound -/

section HitOrder

variable {α : Type}

/-- **A chain hit or an order hit** in a logged output: a logged answer that is a target of the
log before it (`hitTargets`), or an `H₂¹` answer that is the `chal1` field of an earlier marker
query `H₃(x)`. -/
def HitOut (o : α × QueryLog spec) : Prop :=
  ∃ e ∈ o.2, (e.2 : Ans e.1).ba ∈ hitTargets cbP (logBefore e.1 o.2) e.1.1 ∨
    (e.1.1 = .h21 ∧ (e.2 : Ans e.1).ba ∈ (kindIns .h3 ((logBefore e.1 o.2).map Sigma.fst)).map xChal1)

/-- The per-query bound of an order hit: `n₃ / 2¹⁰⁸⁸` for an `H₂¹` query. -/
noncomputable def orderEps (n : Kind → ℕ) : Kind → ℝ≥0∞ := fun k =>
  if k = .h21 then (n .h3 : ℝ≥0∞) / 2 ^ 1088 else 0

lemma prEvent_orderHitL_le (oa : OracleComp spec α) (n : Kind → ℕ) (hn : IsKindQueryBound oa n)
    (t : Dom) (g : Table) :
    Pr{let u ← $ᵗ (Ans t)}[orderHitL (tableQueryLog oa) t (Function.update g t u)] ≤
      orderEps n t.1 := by
  have h : ∀ u : Ans t, orderHitL (tableQueryLog oa) t (Function.update g t u) ↔
      t.1 = .h21 ∧ u.ba ∈ (kindIns .h3 ((logBefore t (tableQueryLog oa g)).map Sigma.fst)).map
        xChal1 := fun u => by
    simp only [orderHitL, Function.update_self, logBefore_tableQueryLog_update]
  simp_rw [h]
  unfold orderEps
  split_ifs with ht
  · simp only [ht, true_and]
    refine (prEvent_ba_mem_le t.1.outLen _).trans ?_
    rw [ht]
    have hl : ((kindIns .h3 ((logBefore t (tableQueryLog oa g)).map Sigma.fst)).map xChal1).length
        ≤ n .h3 := by
      rw [List.length_map]
      exact (length_kindIns_le_of_sublist ((logBefore_sublist _ _).map _)).trans
        (length_kindIns_tableQueryLog_le _ hn g .h3)
    have h8 : (2 : ℝ≥0∞) ^ (8 * Kind.h21.outLen) = 2 ^ 1088 := by norm_num [Kind.outLen]
    rw [h8]
    exact ENNReal.div_le_div_right (by exact_mod_cast hl) _
  · simp only [ht, false_and]
    rw [prEvent_false]

/-- **The union bound for chain hits and order hits** among the queries of a computation with
`n k` queries of kind `k`. -/
theorem prEvent_hitOrder_le (oa : OracleComp spec α) (n : Kind → ℕ) (hn : IsKindQueryBound oa n) :
    Pr{let o ← (simulateQ randomOracle (withLogQ oa)).run' ∅}[HitOut o] ≤
      ∑ k ∈ hitKinds, n k * (hitEps n (combCount cbP n) k + orderEps n k) := by
  refine prEvent_exists_bad_query_le (withLogQ oa) n (isKindQueryBound_withLogQ hn) HitOut
    (fun t g => chainHitL cbP (tableQueryLog oa) t g ∨ orderHitL (tableQueryLog oa) t g)
    hitKinds (fun k => hitEps n (combCount cbP n) k + orderEps n k) (fun k hk => ?_)
    (fun t g => ?_) (fun g hg => ?_)
  · rw [hitEps_eq_zero n _ k hk, zero_add]
    unfold orderEps
    rw [ite_eq_right (fun h => hk (by rw [h]; simp [hitKinds]))]
  · exact (prEvent_or_le _ _ _).trans (add_le_add (prEvent_chainHitL_le cbP oa n hn t g)
      (prEvent_orderHitL_le oa n hn t g))
  · rw [evalWithAnswerFn_withLogQ] at hg
    obtain ⟨e, he, hb⟩ := hg
    refine ⟨e, by rw [tableQueryLog_withLogQ]; exact he, ?_⟩
    have hea : e = ⟨e.1, g e.1⟩ := tableQueryLog_answer oa g e he
    have hans : (e.2 : Ans e.1).ba = (g e.1).ba := by rw [hea]
    rcases hb with hb | ⟨hk, hb⟩
    · left; show (g e.1).ba ∈ _; rw [← hans]; exact hb
    · right; refine ⟨hk, ?_⟩; show (g e.1).ba ∈ _; rw [← hans]; exact hb

end HitOrder

end VoleMole.ROM.OneMore.Pomfrit
