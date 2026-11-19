import VoleMole.ROM.FreshCache

/-!
# The log before a query (plan M6, "same chain")

The data a chain commits to at a query `t` are read off the log *before the first query of `t`*:
that prefix does not depend on the answer at `t` (`logBefore_tableQueryLog_update`), so a predicate
of it is "committed" in the sense of `ROM/Chains.lean` (it does not read the query's own answer),
and a bad event "the answer at `t` is one of the targets of the earlier log" has probability
`≤ #targets · 2^{-8·outLen}` when the cell `t` alone is resampled. Generic facts, for any
`OracleSpec.ofFn`:

* `logBefore d L`: the entries of `L` before the first one at `d`;
* `logBefore_tableQueryLog_update`: the log before `d` does not depend on the table at `d`;
* order: of two queried cells one is queried before the other (`mem_or_mem_logBefore`), and
  "before" is transitive (`mem_logBefore_trans`, `logBefore_logBefore`);
* `tableQueryLog_prefix_congr`: two tables that agree on the cells of a log prefix give the same
  prefix, followed by a query at the same cell.
-/

open OracleComp OracleSpec

namespace VoleMole.ROM

section LogPrefix

variable {D α : Type} {R : D → Type} [DecidableEq D]

/-- **The log before the first query of `d`.** -/
def logBefore (d : D) (L : QueryLog (ofFn R)) : QueryLog (ofFn R) :=
  L.takeWhile fun e => !decide (e.1 = d)

@[simp] lemma logBefore_nil (d : D) : logBefore d ([] : QueryLog (ofFn R)) = [] := rfl

lemma logBefore_cons_self (d : D) (u : R d) (L : QueryLog (ofFn R)) :
    logBefore d ((⟨d, u⟩ : (t : D) × R t) :: L) = [] := by
  simp [logBefore]

lemma logBefore_cons_of_ne {d : D} (e : (t : D) × R t) (L : QueryLog (ofFn R)) (h : e.1 ≠ d) :
    logBefore d (e :: L) = e :: logBefore d L := by
  simp [logBefore, h]

lemma logBefore_cons (d : D) (e : (t : D) × R t) (L : QueryLog (ofFn R)) :
    logBefore d (e :: L) = if e.1 = d then [] else e :: logBefore d L := by
  by_cases h : e.1 = d
  · obtain ⟨t, u⟩ := e
    simp only at h
    subst h
    simp [logBefore_cons_self]
  · simp [logBefore_cons_of_ne e L h, h]

lemma ne_of_mem_logBefore {d : D} {L : QueryLog (ofFn R)} {e : (t : D) × R t}
    (h : e ∈ logBefore d L) : e.1 ≠ d := by
  induction L with
  | nil => simp at h
  | cons e' L ih =>
    rw [logBefore_cons] at h
    split_ifs at h with he
    · simp at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact he
      · exact ih h

lemma mem_of_mem_logBefore {d : D} {L : QueryLog (ofFn R)} {e : (t : D) × R t}
    (h : e ∈ logBefore d L) : e ∈ L := by
  induction L with
  | nil => simp at h
  | cons e' L ih =>
    rw [logBefore_cons] at h
    split_ifs at h with he
    · simp at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

lemma not_mem_logBefore_self (d : D) (L : QueryLog (ofFn R)) :
    d ∉ (logBefore d L).map Sigma.fst := by
  intro h
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
  exact ne_of_mem_logBefore he rfl

lemma logBefore_eq_of_not_mem {d : D} {L : QueryLog (ofFn R)} (h : d ∉ L.map Sigma.fst) :
    logBefore d L = L := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    rw [List.map_cons, List.mem_cons, not_or] at h
    rw [logBefore_cons_of_ne e L (Ne.symm h.1), ih h.2]

lemma logBefore_append_of_mem {d : D} {L₁ : QueryLog (ofFn R)} (L₂ : QueryLog (ofFn R))
    (h : d ∈ L₁.map Sigma.fst) : logBefore d (L₁ ++ L₂) = logBefore d L₁ := by
  induction L₁ with
  | nil => simp at h
  | cons e L₁ ih =>
    rw [List.cons_append, logBefore_cons, logBefore_cons]
    split_ifs with he
    · rfl
    · rw [List.map_cons, List.mem_cons] at h
      rw [ih (h.resolve_left fun h' => he h'.symm)]

lemma logBefore_append_of_not_mem {d : D} {L₁ : QueryLog (ofFn R)} (L₂ : QueryLog (ofFn R))
    (h : d ∉ L₁.map Sigma.fst) : logBefore d (L₁ ++ L₂) = L₁ ++ logBefore d L₂ := by
  induction L₁ with
  | nil => rfl
  | cons e L₁ ih =>
    rw [List.map_cons, List.mem_cons, not_or] at h
    rw [List.cons_append, logBefore_cons_of_ne e _ (Ne.symm h.1), ih h.2, List.cons_append]

/-- **A queried cell splits the log**: the log before it, the first query, the rest. -/
lemma exists_split_of_mem {d : D} {L : QueryLog (ofFn R)} (h : d ∈ L.map Sigma.fst) :
    ∃ u rest, L = logBefore d L ++ (⟨d, u⟩ : (t : D) × R t) :: rest := by
  induction L with
  | nil => simp at h
  | cons e L ih =>
    obtain ⟨t, u⟩ := e
    by_cases ht : t = d
    · subst ht
      exact ⟨u, L, by rw [logBefore_cons_self]; rfl⟩
    · rw [List.map_cons, List.mem_cons] at h
      obtain ⟨u', rest, hL⟩ := ih (h.resolve_left fun h' => ht h'.symm)
      refine ⟨u', rest, ?_⟩
      rw [logBefore_cons_of_ne _ L ht, List.cons_append, ← hL]

/-- The log before `d` is a prefix of the log. -/
lemma exists_append_logBefore (d : D) (L : QueryLog (ofFn R)) :
    ∃ rest, L = logBefore d L ++ rest :=
  ⟨L.dropWhile fun e => !decide (e.1 = d), (List.takeWhile_append_dropWhile).symm⟩

lemma logBefore_logBefore {a b : D} {L : QueryLog (ofFn R)}
    (h : a ∈ (logBefore b L).map Sigma.fst) : logBefore a (logBefore b L) = logBefore a L := by
  obtain ⟨rest, hL⟩ := exists_append_logBefore b L
  conv_rhs => rw [hL]
  rw [logBefore_append_of_mem _ h]

lemma mem_logBefore_trans {a b c : D} {L : QueryLog (ofFn R)}
    (hab : a ∈ (logBefore b L).map Sigma.fst) (hbc : b ∈ (logBefore c L).map Sigma.fst) :
    a ∈ (logBefore c L).map Sigma.fst := by
  have h := logBefore_logBefore hbc
  rw [← h] at hab
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hab
  exact List.mem_map.2 ⟨e, mem_of_mem_logBefore he, rfl⟩

lemma mem_of_mem_logBefore_map {d t : D} {L : QueryLog (ofFn R)}
    (h : t ∈ (logBefore d L).map Sigma.fst) : t ∈ L.map Sigma.fst := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
  exact List.mem_map.2 ⟨e, mem_of_mem_logBefore he, rfl⟩

/-- **Of two queried cells, one is queried before the other.** -/
lemma mem_or_mem_logBefore {a b : D} {L : QueryLog (ofFn R)} (ha : a ∈ L.map Sigma.fst)
    (hb : b ∈ L.map Sigma.fst) (hab : a ≠ b) :
    a ∈ (logBefore b L).map Sigma.fst ∨ b ∈ (logBefore a L).map Sigma.fst := by
  induction L with
  | nil => simp at ha
  | cons e L ih =>
    rw [List.map_cons, List.mem_cons] at ha hb
    by_cases hea : e.1 = a
    · left
      rw [logBefore_cons_of_ne e L fun h => hab (hea.symm.trans h), List.map_cons]
      exact List.mem_cons.2 (Or.inl hea.symm)
    by_cases heb : e.1 = b
    · right
      rw [logBefore_cons_of_ne e L fun h => hab (h.symm.trans heb), List.map_cons]
      exact List.mem_cons.2 (Or.inl heb.symm)
    rw [logBefore_cons_of_ne e L hea, logBefore_cons_of_ne e L heb, List.map_cons,
      List.map_cons]
    rcases ih (ha.resolve_left fun h => hea h.symm) (hb.resolve_left fun h => heb h.symm) with
      h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **The log before `d` does not depend on the table at `d`**: two tables that differ only at
`d` give the same log before `d`. -/
theorem logBefore_tableQueryLog_congr (oa : OracleComp (ofFn R) α) (f f' : ∀ d, R d) (d : D)
    (h : ∀ t, t ≠ d → f' t = f t) :
    logBefore d (tableQueryLog oa f') = logBefore d (tableQueryLog oa f) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [tableQueryLog_query_bind, tableQueryLog_query_bind]
    by_cases ht : t = d
    · subst ht
      rw [logBefore_cons_self, logBefore_cons_self]
    · rw [logBefore_cons_of_ne _ _ ht, logBefore_cons_of_ne _ _ ht, h t ht, ih]

/-- **The log before `d` does not depend on the table at `d`.** -/
theorem logBefore_tableQueryLog_update (oa : OracleComp (ofFn R) α) (f : ∀ d, R d) (d : D)
    (u : R d) :
    logBefore d (tableQueryLog oa (Function.update f d u)) = logBefore d (tableQueryLog oa f) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [tableQueryLog_query_bind, tableQueryLog_query_bind]
    by_cases ht : t = d
    · subst ht
      rw [logBefore_cons_self, logBefore_cons_self]
    · rw [logBefore_cons_of_ne _ _ ht, logBefore_cons_of_ne _ _ ht,
        Function.update_of_ne ht, ih]

omit [DecidableEq D] in
/-- **Two tables that agree on the cells of a log prefix give the same prefix**, followed by a
query at the same cell (answered by the second table). -/
theorem tableQueryLog_prefix_congr (oa : OracleComp (ofFn R) α) (f f' : ∀ d, R d)
    (pre : QueryLog (ofFn R)) (e : (t : D) × R t) (post : QueryLog (ofFn R))
    (h : tableQueryLog oa f = pre ++ e :: post) (hag : ∀ t ∈ pre.map Sigma.fst, f' t = f t) :
    ∃ post', tableQueryLog oa f' = pre ++ (⟨e.1, f' e.1⟩ : (t : D) × R t) :: post' := by
  induction oa using OracleComp.inductionOn generalizing pre with
  | pure a => simp at h
  | query_bind t k ih =>
    rw [tableQueryLog_query_bind] at h ⊢
    cases pre with
    | nil =>
      rw [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨_, rfl⟩
    | cons p pre =>
      rw [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have ht : f' t = f t := hag t (by simp)
      obtain ⟨post', hpost⟩ := ih (f t) pre h fun t' ht' => hag t' (by simp [ht'])
      refine ⟨post', ?_⟩
      rw [ht, hpost, List.cons_append]

/-- **The log before `a` does not read a cell `d` it does not contain**: a table differing only at
such a cell gives the same log before `a`. -/
theorem logBefore_tableQueryLog_congr_of_not_mem (oa : OracleComp (ofFn R) α) (f f' : ∀ d, R d)
    {a d : D} (h : ∀ t, t ≠ d → f' t = f t) (hd : d ∉ (logBefore a (tableQueryLog oa f)).map Sigma.fst) :
    logBefore a (tableQueryLog oa f') = logBefore a (tableQueryLog oa f) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [tableQueryLog_query_bind] at hd ⊢
    rw [tableQueryLog_query_bind]
    by_cases ht : t = a
    · subst ht
      rw [logBefore_cons_self, logBefore_cons_self]
    · rw [logBefore_cons_of_ne _ _ ht, List.map_cons, List.mem_cons, not_or] at hd
      have htd : t ≠ d := fun h' => hd.1 h'.symm
      rw [logBefore_cons_of_ne _ _ ht, logBefore_cons_of_ne _ _ ht, h t htd, ih (f t) hd.2]

/-- **A cell queried before `a` stays queried before `a`** when the table is updated at it. -/
theorem mem_logBefore_tableQueryLog_update (oa : OracleComp (ofFn R) α) (f : ∀ d, R d) {a d : D}
    (u : R d) (hd : d ∈ (logBefore a (tableQueryLog oa f)).map Sigma.fst) :
    d ∈ (logBefore a (tableQueryLog oa (Function.update f d u))).map Sigma.fst := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp at hd
  | query_bind t k ih =>
    rw [tableQueryLog_query_bind] at hd ⊢
    by_cases ht : t = a
    · subst ht
      rw [logBefore_cons_self] at hd
      simp at hd
    · rw [logBefore_cons_of_ne _ _ ht, List.map_cons, List.mem_cons] at hd ⊢
      by_cases htd : d = t
      · exact Or.inl htd
      · right
        rw [Function.update_of_ne (Ne.symm htd)]
        exact ih (f t) (hd.resolve_left htd)

end LogPrefix

end VoleMole.ROM
