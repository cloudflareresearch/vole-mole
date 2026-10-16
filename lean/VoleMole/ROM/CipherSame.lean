import VoleMole.ROM.CipherChain

/-!
# The "same chain" identification, deterministically (plan M6, `ε_chain`, `ε_dead`)

At a hash table `g` (and a cipher table `E`) on which the verifier accepts, with no hit
(`chainHit`) in the game's log and no Post (`PostJ`) in `P`'s joint log:

* **Order** (`L0-L2` L1.4): the verifier's chain cells `w_i → cw → x → y → z` were first queried in
  this order (`before_of_noHit`): a later cell's input contains the earlier cell's answer, which would
  otherwise be a hit at the earlier cell.
* **No collisions** (`Coll₁`, and for `H₂¹`, `H₂²`): distinct cells of these kinds have distinct
  answers (`cell_eq_of_noHit`), so the first preimages found in the log are the verifier's cells.
* **Keys before `x`** (C3): a leaf key found in the whole cipher log was already found before `x`
  (`extractKey_pre_eq`), since otherwise its first query is a Post.

Hence the data committed at the verifier's queries are its chain's (`sameChain_ic`), every tree
outside `known` has a committed dead leaf (L2(c)), and, outside an opened dead leaf
(`DeadOpenOut`), the accepted `Δ` hides every committed dead leaf (`deadHidden_ic`, L2(a)).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## The hash entries of a joint log -/

section Align

variable {α : Type}

lemma takeWhile_append_of_mem {γ : Type} {p : γ → Bool} {A : List γ} (B : List γ) {a : γ}
    (ha : a ∈ A) (hp : p a = false) : (A ++ B).takeWhile p = A.takeWhile p := by
  induction A with
  | nil => simp at ha
  | cons x A ih =>
    rw [List.cons_append, List.takeWhile_cons, List.takeWhile_cons]
    by_cases hx : p x = true
    · rcases List.mem_cons.1 ha with rfl | ha'
      · rw [hp] at hx; exact absurd hx Bool.false_ne_true
      · rw [ite_eq_left hx, ite_eq_left hx, ih ha']
    · rw [ite_eq_right hx, ite_eq_right hx]

lemma tableQueryLog_map' {D γ δ : Type} {R : D → Type} (f : γ → δ) (oa : OracleComp (ofFn R) γ)
    (g : ∀ d, R d) : tableQueryLog (f <$> oa) g = tableQueryLog oa g := by
  rw [map_eq_bind_pure_comp, tableQueryLog_bind]
  simp

lemma map_fst_logBefore {D : Type} {R : D → Type} [DecidableEq D] (d : D)
    (L : QueryLog (ofFn R)) :
    (logBefore d L).map Sigma.fst = (L.map Sigma.fst).takeWhile fun t => !decide (t = d) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    rw [logBefore_cons, List.map_cons, List.takeWhile_cons]
    by_cases h : e.1 = d
    · simp [h]
    · simp [h, ih]

lemma hashLog_logBefore (d : Dom) (L : QueryLog specIC) :
    hashLog (logBefore (.inl d) L) = (hashLog L).takeWhile fun t => !decide (t = d) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨t, u⟩ := e
    cases t with
    | inl d' =>
      by_cases h : d' = d
      · subst h
        rw [logBefore_cons_self]
        show [] = (d' :: hashLog L).takeWhile fun t => !decide (t = d')
        simp
      · rw [logBefore_cons_of_ne _ _ (fun h' => h (Sum.inl.inj h'))]
        show d' :: hashLog (logBefore (.inl d) L) = (d' :: hashLog L).takeWhile _
        rw [ih, List.takeWhile_cons]
        simp [h]
    | inr x =>
      rw [logBefore_cons_of_ne _ _ Sum.inr_ne_inl]
      exact ih

/-- **The hash queries of `runE E P` are `P`'s hash queries.** -/
theorem map_fst_tableQueryLog_runE (h : Table) (E : CTable) (P : OracleComp specIC α) :
    (tableQueryLog (runE E P) h).map Sigma.fst = hashLog (tableQueryLog P (join h E)) := by
  induction P using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    cases t with
    | inl d =>
      rw [runE_inl, tableQueryLog_query_bind, tableQueryLog_map', List.map_cons,
        tableQueryLog_query_bind]
      exact congrArg (List.cons d) (ih (h d))
    | inr x =>
      rw [runE_inr, tableQueryLog_map', tableQueryLog_query_bind]
      exact ih (E x)

variable {β : Type} (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β))
  (E : CTable)

/-- **The game's hash log begins with `P`'s hash queries.** -/
theorem map_fst_gLog (g : Table) :
    ∃ R, (gLog T st P E g).map Sigma.fst = hashLog (jOf g P E) ++ R := by
  unfold gLog gameIC game proverIC
  rw [tableQueryLog_bind, tableQueryLog_bind, List.map_append, List.map_append,
    map_fst_tableQueryLog_runE]
  exact ⟨_, by rw [List.append_assoc]; rfl⟩

/-- If `P` queried `d`, the game's cells before `d` are `P`'s hash cells before `d`. -/
lemma map_fst_logBefore_gLog_of_mem (g : Table) {d : Dom}
    (hd : (.inl d : DomIC) ∈ (jOf g P E).map Sigma.fst) :
    (logBefore d (gLog T st P E g)).map Sigma.fst = hashLog (logBefore (.inl d) (jOf g P E)) := by
  obtain ⟨R, hR⟩ := map_fst_gLog T st P E g
  rw [map_fst_logBefore, hR, takeWhile_append_of_mem _ (mem_hashLog.2 hd) (by simp),
    hashLog_logBefore]

/-- **Order in the game's log is order in `P`'s joint log**, for cells `P` queried. -/
lemma mem_logBefore_jOf (g : Table) {a b : Dom}
    (hb : (.inl b : DomIC) ∈ (jOf g P E).map Sigma.fst)
    (hab : a ∈ (logBefore b (gLog T st P E g)).map Sigma.fst) :
    (.inl a : DomIC) ∈ (logBefore (.inl b) (jOf g P E)).map Sigma.fst := by
  rw [map_fst_logBefore_gLog_of_mem T st P E g hb] at hab
  exact mem_hashLog.1 hab

/-- The joint log before `a` inside the joint log before `b`, for `a` before `b` in the game. -/
lemma logBefore_jOf_logBefore (g : Table) {a b : Dom}
    (hab : a ∈ (logBefore b (gLog T st P E g)).map Sigma.fst) :
    logBefore (.inl a) (logBefore (.inl b) (jOf g P E)) = logBefore (.inl a) (jOf g P E) := by
  by_cases hb : (.inl b : DomIC) ∈ (jOf g P E).map Sigma.fst
  · exact logBefore_logBefore (mem_logBefore_jOf T st P E g hb hab)
  · rw [logBefore_eq_of_not_mem hb]

end Align

/-! ## Post, deterministically -/

section PostDet

lemma cipherLog_append (A B : QueryLog specIC) : cipherLog (A ++ B) = cipherLog A ++ cipherLog B := by
  simp [cipherLog, List.filterMap_append]

/-- A cipher-log decomposition lifts to the joint log. -/
lemma exists_split_cipherLog {L : QueryLog specIC} {B₁ B₂ : QueryLog cspec}
    {q : (_ : Cell) × Blk} (h : cipherLog L = B₁ ++ q :: B₂) :
    ∃ R₁ R₂, L = R₁ ++ (⟨.inr q.1, q.2⟩ : (t : DomIC) × AnsIC t) :: R₂ ∧ cipherLog R₁ = B₁ := by
  induction L generalizing B₁ with
  | nil => simp [cipherLog] at h
  | cons e L ih =>
    obtain ⟨t, u⟩ := e
    cases t with
    | inl d =>
      obtain ⟨R₁, R₂, hL, hR⟩ := ih (B₁ := B₁) h
      exact ⟨⟨.inl d, u⟩ :: R₁, R₂, by rw [hL, List.cons_append], hR⟩
    | inr x =>
      change (⟨x, u⟩ :: cipherLog L) = B₁ ++ q :: B₂ at h
      cases B₁ with
      | nil =>
        rw [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨[], L, rfl, rfl⟩
      | cons b B₁ =>
        rw [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        obtain ⟨R₁, R₂, hL, hR⟩ := ih (B₁ := B₁) h
        exact ⟨⟨.inr x, u⟩ :: R₁, R₂, by rw [hL, List.cons_append], by
          change ⟨x, u⟩ :: cipherLog R₁ = _
          rw [hR]⟩

/-- The predicate of `extractKey`. -/
def keyPred (E : CTable) (iv : ByteArray) (i : ℕ) (a : ByteArray) (q : (_ : Cell) × Blk) : Bool :=
  decide ((q.1.2 = lp iv i 0 ∨ q.1.2 = lp iv i 1) ∧
    ba (E (q.1.1, lp iv i 0)) ++ ba (E (q.1.1, lp iv i 1)) = a)

lemma extractKey_eq (log : QueryLog cspec) (E : CTable) (iv : ByteArray) (i : ℕ) (a : ByteArray) :
    extractKey log E iv i a = (log.find? (keyPred E iv i a)).map (·.1.1) := rfl

/-- **Without Post, a key of a committed commitment is found before `x`**: if the commitment `a` is
a block `jj < 256` of an `H₁` input that `P` queried before `x`, the first key with commitment `a`
in the cipher log before `x` is the first one in the whole cipher log. -/
theorem extractKey_pre_eq (E : CTable) {J : QueryLog specIC} (hpost : ¬PostJ E J) (x : Dom)
    (iv : ByteArray) (i : ℕ) (a : ByteArray)
    (ha : (.inl x : DomIC) ∈ J.map Sigma.fst →
      ∃ wH ∈ kindIns .h1 (hashLog (logBefore (.inl x) J)), ∃ jj < 256,
        a = wH.extract (32 * jj) (32 * jj + 32)) :
    extractKey (cipherLog (logBefore (.inl x) J)) E iv i a = extractKey (cipherLog J) E iv i a := by
  by_cases hx : (.inl x : DomIC) ∈ J.map Sigma.fst
  swap
  · rw [logBefore_eq_of_not_mem hx]
  obtain ⟨wH, hwH, jj, hjj, rfl⟩ := ha hx
  obtain ⟨u, rest, hJ⟩ := exists_split_of_mem hx
  set Jx := logBefore (.inl x) J
  have hcl : cipherLog J = cipherLog Jx ++ cipherLog (⟨.inl x, u⟩ :: rest) := by
    rw [hJ, cipherLog_append]
  rw [extractKey_eq, extractKey_eq, hcl, List.find?_append]
  cases hA : (cipherLog Jx).find? (keyPred E iv i (wH.extract (32 * jj) (32 * jj + 32))) with
  | some q => rfl
  | none =>
    simp only [Option.none_or, Option.map_none]
    cases hB : (cipherLog (⟨.inl x, u⟩ :: rest)).find? (keyPred E iv i
        (wH.extract (32 * jj) (32 * jj + 32))) with
    | none => rfl
    | some q₀ =>
      exfalso
      apply hpost
      obtain ⟨hpB, B₁, B₂, hB₁, hnB⟩ := List.find?_eq_some_iff_append.1 hB
      change cipherLog rest = _ at hB₁
      obtain ⟨R₁, R₂, hR, hcR⟩ := exists_split_cipherLog hB₁
      set a := wH.extract (32 * jj) (32 * jj + 32)
      have hnA : ∀ q ∈ cipherLog Jx, keyPred E iv i a q = false := fun q hq => by
        have := List.find?_eq_none.1 hA q hq
        simpa using this
      set pre := Jx ++ (⟨.inl x, u⟩ : (t : DomIC) × AnsIC t) :: R₁
      have hcpre : cipherLog pre = cipherLog Jx ++ cipherLog R₁ := by
        rw [cipherLog_append]; rfl
      have hpre : ∀ q ∈ cipherLog pre, keyPred E iv i a q = false := by
        intro q hq
        rw [hcpre, List.mem_append] at hq
        rcases hq with hq | hq
        · exact hnA q hq
        · rw [hcR] at hq
          have := hnB q hq
          simpa using this
      have hJ' : J = pre ++ (⟨.inr q₀.1, q₀.2⟩ : (t : DomIC) × AnsIC t) :: R₂ := by
        rw [hJ, hR]
        simp only [pre, List.append_assoc, List.cons_append]
      obtain ⟨⟨κ, w⟩, v⟩ := q₀
      have hp0 := hpB
      simp only [keyPred, decide_eq_true_eq] at hp0
      obtain ⟨hw, hcom⟩ := hp0
      have hfresh : ∀ w₀, (w₀ = lp iv i 0 ∨ w₀ = lp iv i 1) →
          (.inr (κ, w₀) : DomIC) ∉ pre.map Sigma.fst := by
        intro w₀ hw₀ hmem
        obtain ⟨q, hq, hq1⟩ := List.mem_map.1 (mem_cipherLog.2 hmem)
        have := hpre q hq
        simp only [keyPred, decide_eq_false_iff_not, not_and] at this
        rw [hq1] at this
        exact this hw₀ hcom
      set w' := if w = lp iv i 0 then lp iv i 1 else lp iv i 0 with hw'def
      have hne := lp_ne iv i
      have hw' : w' ∈ adj w ∧ (w' = lp iv i 0 ∨ w' = lp iv i 1) := by
        rcases hw with h | h
        · subst h
          rw [hw'def, ite_eq_left rfl]
          exact ⟨lp1_mem_adj iv i, Or.inr rfl⟩
        · subst h
          rw [hw'def, ite_eq_right (Ne.symm hne)]
          exact ⟨lp0_mem_adj iv i, Or.inl rfl⟩
      refine ⟨pre, _, R₂, hJ', κ, w, rfl, w', hw'.1, hfresh w hw, hfresh w' hw'.2, ?_⟩
      have hwH' : wH ∈ kindIns .h1 (hashLog pre) :=
        ((sublist_hashLog_of_append (pre := Jx) (post := (⟨.inl x, u⟩ :
          (t : DomIC) × AnsIC t) :: R₁)).filter _ |>.map _ |>.subset) hwH
      have hsplit : split32 a = (E (κ, lp iv i 0), E (κ, lp iv i 1)) := by
        rw [← hcom, split32_ba]
      unfold postTargets
      rw [List.mem_toFinset, List.mem_flatMap]
      refine ⟨wH, hwH', List.mem_flatMap.2 ⟨jj, List.mem_range.2 hjj, ?_⟩⟩
      show (E (κ, w), E (κ, w')) ∈ [split32 a, (split32 a).swap]
      rw [hsplit]
      rcases hw with h | h
      · subst h
        rw [hw'def, ite_eq_left rfl]
        exact List.mem_cons_self
      · subst h
        rw [hw'def, ite_eq_right (Ne.symm hne)]
        exact List.mem_cons_of_mem _ List.mem_cons_self

end PostDet

/-! ## Without hits: order and no collisions -/

section NoHitSec

variable {cb : Option (ℕ × ByteArray)}

lemma mem_hitTargets_block {pre : QueryLog spec} {w : ByteArray} (hw : ((.h1, w) : Dom) ∈ pre.map Sigma.fst)
    (hs : w.size = 545) {i : ℕ} (hi : i < 17) :
    w.extract (32 * i) (32 * i + 32) ∈ hitTargets cb pre .h1 := by
  simp only [hitTargets, List.mem_append]
  refine Or.inl (Or.inl (List.mem_flatMap.2 ⟨w, List.mem_filter.2 ⟨mem_kindIns hw, by simp [hs]⟩,
    List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩⟩))

lemma mem_hitTargets_com {pre : QueryLog spec} {x : ByteArray}
    (hx : ((.h21, x) : Dom) ∈ pre.map Sigma.fst) : xCom x ∈ hitTargets cb pre .h1 := by
  simp only [hitTargets, List.mem_append]
  exact Or.inl (Or.inr (List.mem_map.2 ⟨x, mem_kindIns hx, rfl⟩))

lemma mem_hitTargets_chal1 {pre : QueryLog spec} {y : ByteArray}
    (hy : ((.h22, y) : Dom) ∈ pre.map Sigma.fst) : yChal1 y ∈ hitTargets cb pre .h21 := by
  simp only [hitTargets, List.mem_append]
  exact Or.inl (List.mem_map.2 ⟨y, mem_kindIns hy, rfl⟩)

lemma mem_hitTargets_chal2 {pre : QueryLog spec} {z : ByteArray}
    (hz : ((.h23, z) : Dom) ∈ pre.map Sigma.fst) : zChal2 z ∈ hitTargets cb pre .h22 := by
  simp only [hitTargets, List.mem_append]
  exact Or.inl (Or.inl (List.mem_map.2 ⟨z, mem_kindIns hz, rfl⟩))

lemma mem_hitTargets_ans {pre : QueryLog spec} {e : (t : Dom) × Ans t} (he : e ∈ pre) {k : Kind}
    (hek : e.1.1 = k) (hk : k = .h1 ∨ k = .h21 ∨ k = .h22) :
    (e.2 : Ans e.1).ba ∈ hitTargets cb pre k := by
  have hmem : (e.2 : Ans e.1).ba ∈ ansOf k pre :=
    List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simp [hek]⟩, rfl⟩
  rcases hk with rfl | rfl | rfl <;> simp only [hitTargets, List.mem_append] <;> tauto

variable {β : Type} (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β))
  (E : CTable) {g : Table}

/-- An entry of the game's log at a cell answers with the table. -/
lemma exists_entry {L : QueryLog spec} (hL : ∀ e ∈ L, e = ⟨e.1, g e.1⟩) {t : Dom}
    (ht : t ∈ L.map Sigma.fst) : (⟨t, g t⟩ : (d : Dom) × Ans d) ∈ L := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 ht
  rw [← hL e he]
  exact he

lemma gLog_answer (g : Table) : ∀ e ∈ gLog T st P E g, e = ⟨e.1, g e.1⟩ :=
  tableQueryLog_answer _ g

lemma noHit_cell (hh : NoHit (gameIC T st P E) (chainHit T st P E) g) {t : Dom}
    (ht : t ∈ (gLog T st P E g).map Sigma.fst) :
    (g t).ba ∉ hitTargets st.comb (logBefore t (gLog T st P E g)) t.1 := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 ht
  exact hh e he

/-- **Order without hits**: if a query `b` made before `a` would make `a`'s answer a target, then
`a` was queried before `b`. -/
lemma before_of_noHit (hh : NoHit (gameIC T st P E) (chainHit T st P E) g) {a b : Dom}
    (ha : a ∈ (gLog T st P E g).map Sigma.fst) (hb : b ∈ (gLog T st P E g).map Sigma.fst)
    (hab : a ≠ b)
    (htgt : b ∈ (logBefore a (gLog T st P E g)).map Sigma.fst →
      (g a).ba ∈ hitTargets st.comb (logBefore a (gLog T st P E g)) a.1) :
    a ∈ (logBefore b (gLog T st P E g)).map Sigma.fst :=
  (mem_or_mem_logBefore ha hb hab).resolve_right fun h => noHit_cell T st P E hh ha (htgt h)

/-- **No collisions without hits**: two cells of the game's log of the same kind (`H₁`, `H₂¹`,
`H₂²`) with the same answer are the same cell. -/
lemma cell_eq_of_noHit (hh : NoHit (gameIC T st P E) (chainHit T st P E) g) {a b : Dom}
    (ha : a ∈ (gLog T st P E g).map Sigma.fst) (hb : b ∈ (gLog T st P E g).map Sigma.fst)
    (hk : a.1 = b.1) (hk' : a.1 = .h1 ∨ a.1 = .h21 ∨ a.1 = .h22) (hans : (g a).ba = (g b).ba) :
    a = b := by
  by_contra hab
  have key : ∀ c d : Dom, c.1 = d.1 → (d.1 = .h1 ∨ d.1 = .h21 ∨ d.1 = .h22) →
      c ∈ (logBefore d (gLog T st P E g)).map Sigma.fst → (g c).ba = (g d).ba →
      d ∈ (gLog T st P E g).map Sigma.fst → False := by
    intro c d hcd hdk hc hcd' hd
    have he := exists_entry (fun e he => gLog_answer T st P E g e (mem_of_mem_logBefore he)) hc
    have hmem := mem_hitTargets_ans (cb := st.comb) he hcd hdk
    exact noHit_cell T st P E hh hd (hcd' ▸ hmem)
  rcases mem_or_mem_logBefore ha hb hab with h | h
  · exact key a b hk (hk ▸ hk') h hans hb
  · exact key b a hk.symm hk' h hans.symm ha

end NoHitSec

/-! ## The verifier's chain in the log -/

section Ident

variable {β : Type} (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β))
  (E : CTable) (g : Table)

lemma ans_of_mem_gLog {e : (t : Dom) × Ans t} (he : e ∈ gLog T st P E g) :
    (e.2 : Ans e.1) = g e.1 := by
  obtain ⟨t, v⟩ := e
  have h := gLog_answer T st P E g ⟨t, v⟩ he
  exact eq_of_heq (Sigma.mk.inj h).2

/-- A cell of the game's log found by `firstIn`: present in the prefix, the only cell of its kind
with that answer. -/
lemma firstIn_gLog (hh : NoHit (gameIC T st P E) (chainHit T st P E) g) {k : Kind}
    (hk : k = .h1 ∨ k = .h21 ∨ k = .h22) {ok : ByteArray → Bool} {d : Dom}
    (hd : (k, d.2) = d) {L : QueryLog spec} (hL : ∀ e ∈ L, e ∈ gLog T st P E g)
    (hdL : d ∈ L.map Sigma.fst) (hok : ok d.2 = true) :
    firstIn k ok (g d).ba L = some d.2 := by
  have hdk : d.1 = k := by rw [← hd]
  have hdG : d ∈ (gLog T st P E g).map Sigma.fst := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hdL
    exact List.mem_map.2 ⟨e, hL e he, rfl⟩
  refine firstIn_eq ⟨⟨d, g d⟩, ?_, hd.symm, rfl⟩ hok fun e he hek _ hea => ?_
  · exact exists_entry (fun e he => gLog_answer T st P E g e (hL e he)) hdL
  · have heG := hL e he
    rw [ans_of_mem_gLog T st P E g heG] at hea
    have := cell_eq_of_noHit T st P E hh (List.mem_map.2 ⟨e, heG, rfl⟩) hdG (hek.trans hdk.symm)
      (hek ▸ hk) hea
    rw [this]

lemma inLog_gLog {t : Dom} (h : InLog (@verifyQ (icPrg E.cipher) T st (πOf g P E)) g t) :
    t ∈ (gLog T st P E g).map Sigma.fst := by
  have h' : InLog (@verifyQ (icPrg E.cipher) T st
      (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).1) g t := by
    rw [proverIC_fst]; exact h
  exact @inLog_game (icPrg E.cipher) _ g T st (proverIC st E P) t h'

/-- **The verifier's chain cells in the game's log, without hits**: the leaf commitments read off
the log before the verifier's `H₂¹` input are the reconstructed ones, each leaf hash was queried by
`P` before `x` whenever `P` queried `x`, the first `H₂¹` preimage of `y`'s `chal1` is `x`, the
first `H₂²` preimage of `z`'s `chal2` is `y`, and `x`, `y`, `z` were first queried in this
order. -/
theorem chain_ident (hh : NoHit (gameIC T st P E) (chainHit T st P E) g)
    (keys : ℕ → ℕ → ByteArray) : letI := icPrg E.cipher
    (verify (Hashes.ofTable g) T st (πOf g P E)).accept = true → ∀ {leaves : BAVC.Leaves},
    BAVC.reconstruct (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves →
    let ch := runChain (Hashes.ofTable g) T st (πOf g P E) leaves keys
    let x := runX (Hashes.ofTable g) st (πOf g P E) leaves
    let y := runY (Hashes.ofTable g) st ch
    let z := runZ st ch
    let G := gLog T st P E g
    (∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i,
      comPre (logBefore (.h21, x) G) x i j = some (comAt leaves.coms i j)) ∧
    ((.inl (.h21, x) : DomIC) ∈ (jOf g P E).map Sigma.fst → ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i,
      ∃ wH ∈ kindIns .h1 (hashLog (logBefore (.inl (.h21, x)) (jOf g P E))), ∃ jj < 256,
        comAt leaves.coms i j = wH.extract (32 * jj) (32 * jj + 32)) ∧
    firstIn .h21 (fun _ => true) (yChal1 y) (logBefore (.h22, y) G) = some x ∧
    firstIn .h22 (fun _ => true) (zChal2 z) (logBefore (.h23, z) G) = some y ∧
    ((.h21, x) : Dom) ∈ (logBefore (.h22, y) G).map Sigma.fst ∧
    ((.h22, y) : Dom) ∈ (logBefore (.h23, z) G).map Sigma.fst := by
  let _ : HasPrg := icPrg E.cipher
  intro hacc leaves hr ch x y z G
  set Hs := Hashes.ofTable g
  set π := πOf g P E
  have hHs : ∀ k w, (Hs.hash k w).size = k.outLen := fun k w => by simp [Hs]
  obtain ⟨hf, leaves', hr', -, -⟩ := (accept_iff _ T st π).1 hacc
  have hr0 : BAVC.reconstruct (ivOf Hs ⟨st.params, π⟩ (st.mu1 Hs)) (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩) = some leaves := hr
  rw [hr0] at hr'
  cases hr'
  -- The chain cells.
  set ws := BAVC.leafHashInputs leaves.coms with hws
  set lh := ws.map (Hs.hash .h1)
  set cw := BAVC.comInput lh with hcw
  set com := Hs.hash .h1 cw
  have hlen : ws.length = 17 := length_leafHashInputs _
  have hcs : leaves.coms.size = 32 * BAVC.numLeaves := reconstruct_coms_size hr0
  have hx : x = chal1Input ⟨st.params, π⟩ (st.mu1 Hs) com st.binder1 := rfl
  have hmu : (st.mu1 Hs).size = 32 := size_mu1 Hs hHs st
  have hcom : com.size = 32 := hHs _ _
  have hlh : ∀ h ∈ lh, h.size = 32 := fun h hh' => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hh'
    exact hHs _ _
  have hlhl : lh.length = 17 := by simp [lh, hlen]
  have hcwsz : cw.size = 545 := by
    simp only [hcw, BAVC.comInput, ByteArray.size_push, size_foldl_append lh hlh, hlhl]
  have hblock : ∀ i (hi : i < 17), cw.extract (32 * i) (32 * i + 32) =
      (g (.h1, ws[i]'(by omega))).ba := by
    intro i hi
    simp only [hcw, BAVC.comInput]
    rw [extract_push_of_le _ _ (by rw [size_foldl_append lh hlh, hlhl]; omega),
      extract_foldl_append lh hlh (by omega)]
    simp [lh, Hs]
  have hwsz : ∀ i (hi : i < 17), (ws[i]'(by omega)).size = lhSize i := by
    intro i hi
    have hoff : BAVC.leafOffset i + 2 ^ BAVC.kOf i ≤ BAVC.numLeaves := by
      rw [← leafOffset_succ, ← leafOffset_tau]
      exact leafOffset_mono (by simp only [BAVC.tau]; omega)
    simp only [hws, BAVC.leafHashInputs, List.getElem_map, List.getElem_range, BAVC.hashLen,
      ByteArray.size_push, ByteArray.size_extract, hcs, lhSize]
    omega
  have hc1 : ch.chal1 = (g (.h21, x)).ba := rfl
  have hc1s : ch.chal1.size = 136 := by rw [hc1]; exact Prob.Bytes.size_ba _
  have hc2 : ch.chal2 = (g (.h22, y)).ba := rfl
  have hc2s : ch.chal2.size = 56 := by rw [hc2]; exact Prob.Bytes.size_ba _
  have hy : y = chal2Input (ch.pf st) ch.chal1 ch.hV (st.muDelayed Hs ch.chal1) st.binder2 := rfl
  have hz : z = chal3Input (ch.pf st) ch.chal2 ch.z := rfl
  -- The cells are in the game's log.
  obtain ⟨hxL, hyL, hzL⟩ := inLog_verifyQ g T st π hacc hr0 keys
  obtain ⟨hwL, hcwL⟩ := inLog_verifyQ_h1 g T st π hacc hr0
  have hxG := inLog_gLog T st P E g hxL
  have hyG := inLog_gLog T st P E g hyL
  have hzG := inLog_gLog T st P E g hzL
  have hcwG := inLog_gLog T st P E g hcwL
  have hwG : ∀ i (hi : i < 17), ((.h1, ws[i]'(by omega)) : Dom) ∈ G.map Sigma.fst :=
    fun i hi => inLog_gLog T st P E g (hwL _ (List.getElem_mem _))
  -- Order.
  have hO1 : ∀ i (hi : i < 17), ((.h1, ws[i]'(by omega)) : Dom) ∈
      (logBefore (.h1, cw) G).map Sigma.fst := by
    intro i hi
    refine before_of_noHit T st P E hh (hwG i hi) hcwG (fun h => ?_) fun hb => ?_
    · have := congrArg ByteArray.size (congrArg Prod.snd h)
      simp only at this
      rw [hwsz i hi, hcwsz] at this
      simp only [lhSize] at this
      have : 2 ^ BAVC.kOf i ≥ 128 := by
        unfold BAVC.kOf; split <;> norm_num
      omega
    · rw [← hblock i hi]
      exact mem_hitTargets_block hb hcwsz hi
  have hO2 : ((.h1, cw) : Dom) ∈ (logBefore (.h21, x) G).map Sigma.fst := by
    refine before_of_noHit T st P E hh hcwG hxG (by simp) fun hb => ?_
    have : (g (.h1, cw)).ba = xCom x := by
      rw [hx, xCom_chal1Input hmu hcom]; rfl
    rw [this]
    exact mem_hitTargets_com hb
  have hO3 : ((.h21, x) : Dom) ∈ (logBefore (.h22, y) G).map Sigma.fst := by
    refine before_of_noHit T st P E hh hxG hyG (by simp) fun hb => ?_
    have : (g (.h21, x)).ba = yChal1 y := by
      rw [hy, yChal1_chal2Input _ hc1s, hc1]
    rw [this]
    exact mem_hitTargets_chal1 hb
  have hO4 : ((.h22, y) : Dom) ∈ (logBefore (.h23, z) G).map Sigma.fst := by
    refine before_of_noHit T st P E hh hyG hzG (by simp) fun hb => ?_
    have : (g (.h22, y)).ba = zChal2 z := by
      rw [hz, zChal2_chal3Input _ hc2s, hc2]
    rw [this]
    exact mem_hitTargets_chal2 hb
  have hO12 : ∀ i (hi : i < 17), ((.h1, ws[i]'(by omega)) : Dom) ∈
      (logBefore (.h21, x) G).map Sigma.fst := fun i hi => mem_logBefore_trans (hO1 i hi) hO2
  have hsub : ∀ {d : Dom}, ∀ e ∈ logBefore d G, e ∈ G := fun e he => mem_of_mem_logBefore he
  -- The first preimages.
  have hF1 : firstIn .h1 (fun w => w.size == 545) (xCom x) (logBefore (.h21, x) G) = some cw := by
    have h := firstIn_gLog T st P E g hh (Or.inl rfl) (d := (.h1, cw)) rfl hsub hO2
      (ok := fun w => w.size == 545) (by simp [hcwsz])
    rwa [show (g (.h1, cw)).ba = xCom x by rw [hx, xCom_chal1Input hmu hcom]; rfl] at h
  have hF2 : ∀ i (hi : i < 17), firstIn .h1 (fun w => w.size == lhSize i)
      (cw.extract (32 * i) (32 * i + 32)) (logBefore (.h21, x) G) = some (ws[i]'(by omega)) := by
    intro i hi
    rw [hblock i hi]
    exact firstIn_gLog T st P E g hh (Or.inl rfl) (d := (.h1, ws[i]'(by omega))) rfl hsub
      (hO12 i hi) (by simp [hwsz i hi])
  refine ⟨fun i hi j hj => ?_, fun hxJ i hi j hj => ?_, ?_, ?_, hO3, hO4⟩
  · have hi' : i < 17 := hi
    simp only [comPre, hF1, Option.bind_eq_bind, Option.bind_some, hF2 i hi', Option.pure_def]
    rw [← extract_leafHashInput hcs hi hj]
  · have hi' : i < 17 := hi
    refine ⟨ws[i]'(by omega), mem_hashLog.2 (mem_logBefore_jOf T st P E g hxJ (hO12 i hi')) |>
      fun h => mem_kindIns h, j, ?_, (extract_leafHashInput hcs hi hj).symm⟩
    have : 2 ^ BAVC.kOf i ≤ 256 := by unfold BAVC.kOf; split <;> norm_num
    omega
  · rw [show yChal1 y = (g (.h21, x)).ba by rw [hy, yChal1_chal2Input _ hc1s, hc1]]
    exact firstIn_gLog T st P E g hh (Or.inr (Or.inl rfl)) (d := (.h21, x)) rfl hsub hO3 rfl
  · rw [show zChal2 z = (g (.h22, y)).ba by rw [hz, zChal2_chal3Input _ hc2s, hc2]]
    exact firstIn_gLog T st P E g hh (Or.inr (Or.inr rfl)) (d := (.h22, y)) rfl hsub hO4 rfl

end Ident

/-! ## The "same chain" step and L2 -/

section Same

/-- The commitment of the hidden leaf is the opened one. -/
lemma comAt_reconstruct_hidden [HasPrg] {iv opening delta : ByteArray} {leaves : BAVC.Leaves}
    (h : BAVC.reconstruct iv opening delta = some leaves) {i : ℕ} (hi : i < BAVC.tau) :
    comAt leaves.coms i (BAVC.deltaIndex delta i) = opening.extract (32 * i) (32 * i + 32) := by
  have hj : BAVC.deltaIndex delta i < 2 ^ BAVC.kOf i := hiddenIndex_lt _ _
  rw [reconstruct_eq] at h
  split_ifs at h with hb
  cases h
  rw [Bool.not_eq_true] at hb
  have hsz := (badOpening_false hb).1
  unfold comAt
  rw [leavesOf_eq]
  rw [extract_pieces _ 32 (fun i' hi' j' hj' => by
      split
      · rw [ByteArray.size_extract, hsz]
        have hi'' : i' < 17 := hi'
        show min (32 * i' + 32) (17 * 32 + 105 * 16) - 32 * i' = 32
        omega
      · exact leafCom_size _ _ _) hi hj]
  simp only [beq_self_eq_true, ↓reduceIte]
  rfl

/-- A witness in the log is found. -/
lemma extractKey_isSome_of_hasCell {log : QueryLog cspec} {E : CTable} {iv : ByteArray} {i : ℕ}
    {κ : Blk} (h : HasCell log κ (lp iv i 0) (lp iv i 1)) :
    (extractKey log E iv i (ba (E (κ, lp iv i 0)) ++ ba (E (κ, lp iv i 1)))).isSome := by
  obtain ⟨q, hq, hqκ⟩ := h
  rw [extractKey_eq, Option.isSome_map]
  refine List.find?_isSome.2 ⟨q, hq, ?_⟩
  simp only [keyPred, decide_eq_true_eq]
  rcases hqκ with h | h <;> rw [h] <;> simp

variable {st : Statement} {T : CrtTables}

/-- **The fields the challenges on a chain read**: two chains agreeing on them have the same
challenges on the chain. -/
lemma onChain_congr [HasPrg] {ch ch' : Chain} (hk : ch'.keys = ch.keys) (hiv : ch'.iv = ch.iv)
    (h5 : ch'.h5 = ch.h5) (hc1 : ch'.chal1 = ch.chal1) (hhV : ch'.hV = ch.hV)
    (hc2 : ch'.chal2 = ch.chal2) (hz : ch'.z = ch.z) (hvals : ch'.vals = ch.vals)
    (hcor : (ch'.pf st).corrections = (ch.pf st).corrections)
    (hcm : (ch'.pf st).cmult = (ch.pf st).cmult)
    (hvc : (ch'.pf st).voleCheck = (ch.pf st).voleCheck)
    (hd : (ch'.pf st).correction = (ch.pf st).correction)
    (hqs : (ch'.pf st).qsProof = (ch.pf st).qsProof) :
    ch'.OnChain st T = ch.OnChain st T := by
  have hresp : ch'.resp st T = ch.resp st T := by
    funext Δ; simp only [Chain.resp, hk, hiv, h5, hcor, hcm]
  have hq : ∀ c2 cs qm dl, qsCheck (ch'.pf st) c2 cs qm dl = qsCheck (ch.pf st) c2 cs qm dl := by
    intro c2 cs qm dl
    simp only [VoleMole.Verifier.qsCheck, hqs]
    rfl
  have hck : ∀ rows dl, correctedKeys (ch'.pf st) rows dl = correctedKeys (ch.pf st) rows dl := by
    intro rows dl
    simp only [correctedKeys, hd]
    rfl
  funext Δ
  simp only [Chain.OnChain, Chain.check, hresp, hc1, hhV, hvc, hc2, hz, hvals, hq, hck]

lemma onSet_congr [HasPrg] {ch ch' : Chain} (h : ch'.OnChain st T = ch.OnChain st T)
    (S : Finset Blocks) : onSet st T ch' S = onSet st T ch S := by
  ext Δ
  rw [mem_onSet, mem_onSet, h]

lemma hideSet_congr [HasPrg] {ch ch' : Chain} (h : ch'.OnChain st T = ch.OnChain st T)
    (dead : Fin BAVC.tau → Finset ℕ) : hideSet st T ch' dead = hideSet st T ch dead := by
  ext Δ
  rw [mem_hideSet, mem_hideSet, onSet_congr h]

section SameIC

variable {β : Type} (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β))
  (E : CTable) (g : Table)

lemma gameIC_keys : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.1.keys =
    keysOf (cipherLog (jOf g P E)) E (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) := by
  simp only [gameIC, evalWithAnswerFn_game, evalWithAnswerFn_proverIC, jOf, ivE, πOf,
    cipherLog_tableQueryLog]

lemma gameIC_known : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.1.known =
    knownOf (cipherLog (jOf g P E)) E (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩) := by
  simp only [gameIC, evalWithAnswerFn_game, evalWithAnswerFn_proverIC, jOf, ivE, πOf,
    cipherLog_tableQueryLog]

/-- A field of a proof read off its first `N` bytes, for the five chain fields. -/
lemma field_prefix (p : Params) (b : ByteArray) {N : ℕ} {k : String}
    (hk : k = "corrections" ∨ k = "cmult" ∨ k = "vole_check" ∨ k = "correction")
    (hN : p.o₄ ≤ N) : Proof.field ⟨p, b.extract 0 N⟩ k = Proof.field ⟨p, b⟩ k := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact field_extract_zero p b (Params.field_corrections p) (by have := o₂_le p; unfold Params.o₄ at hN; omega)
  · exact field_extract_zero p b (Params.field_cmult p) (by unfold Params.o₄ Params.o₂ at hN; omega)
  · exact field_extract_zero p b (Params.field_voleCheck p) (by unfold Params.o₄ at hN; omega)
  · exact field_extract_zero p b (Params.field_correction p) (by unfold Params.o₄ at hN; omega)

/-- **The "same chain" step and L2(c), from the identification facts** (`chain_ident`), for
inputs `x`, `y`, `z` built by the verifier from the proof `π` and the chain `ch`. -/
theorem sameChain_core (hpost : ¬PostJ E (jOf g P E)) {π : ByteArray}
    (hf : Proof.checkFormat ⟨st.params, π⟩ = true) {leaves : BAVC.Leaves}
    (hr : @BAVC.reconstruct (icPrg E.cipher) (ivE g st P E) (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩) = some leaves)
    (hπ : π = πOf g P E) {ch : Chain} {x y z com : ByteArray}
    (hchp : ch.proof = π)
    (hchk : ch.keys = keysOf (cipherLog (jOf g P E)) E (ivE g st P E) (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩))
    (hchiv : ch.iv = ivE g st P E) (hch5 : ch.h5 = (Hashes.ofTable g).hash .h5)
    (hchv : ch.vals = st.values ch.chal1 (st.combBytes (Hashes.ofTable g) ch.chal2))
    (hx : x = chal1Input ⟨st.params, π⟩ (st.mu1 (Hashes.ofTable g)) com st.binder1)
    (hmu : (st.mu1 (Hashes.ofTable g)).size = 32) (hcomsz : com.size = 32)
    (hy : y = chal2Input ⟨st.params, π⟩ ch.chal1 ch.hV (st.muDelayed (Hashes.ofTable g) ch.chal1)
      st.binder2) (hc1s : ch.chal1.size = 136) (hV4 : ch.hV.size = 4)
    (hz : z = chal3Input ⟨st.params, π⟩ ch.chal2 ch.z) (hc2s : ch.chal2.size = 56)
    (hcom : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i,
      comPre (logBefore (.h21, x) (gLog T st P E g)) x i j = some (comAt leaves.coms i j))
    (hwH : (.inl (.h21, x) : DomIC) ∈ (jOf g P E).map Sigma.fst → ∀ i < BAVC.tau,
      ∀ j < 2 ^ BAVC.kOf i,
      ∃ wH ∈ kindIns .h1 (hashLog (logBefore (.inl (.h21, x)) (jOf g P E))), ∃ jj < 256,
        comAt leaves.coms i j = wH.extract (32 * jj) (32 * jj + 32))
    (hF3 : firstIn .h21 (fun _ => true) (yChal1 y) (logBefore (.h22, y) (gLog T st P E g)) = some x)
    (hF4 : firstIn .h22 (fun _ => true) (zChal2 z) (logBefore (.h23, z) (gLog T st P E g)) = some y)
    (hO3 : ((.h21, x) : Dom) ∈ (logBefore (.h22, y) (gLog T st P E g)).map Sigma.fst)
    (hO4 : ((.h22, y) : Dom) ∈ (logBefore (.h23, z) (gLog T st P E g)).map Sigma.fst)
    (hdeadOf : deadOf T st P E g = deadAtX T st P E x g) :
    @SameChain (icPrg E.cipher) st T (preOf T st P E) (midOf T st P E) (accOf T st P E)
        (deadOf T st P E g) g ch x y z ∧
      ∀ i ∉ knownOf (cipherLog (jOf g P E)) E (ivE g st P E) (Proof.opening ⟨st.params, π⟩),
        (deadOf T st P E g i).Nonempty := by
  let _ : HasPrg := icPrg E.cipher
  -- `iv` and the keys committed at `x`.
  have hivX : ivX st x g = ivE g st P E := by
    simp only [ivX, ivE, ivOf]
    rw [hx, xIvPre_chal1Input hf hmu hcomsz, hπ]
  have hkeys : keyPre E (logBefore (.h21, x) (gLog T st P E g))
      (logBefore (.inl (.h21, x)) (jOf g P E)) (ivX st x g) x = ch.keys := by
    rw [hchk]
    funext i j
    rw [hivX]
    unfold keyPre
    split_ifs with hv
    · rw [hcom i hv.1 j hv.2]
      simp only
      rw [keysOf_of_reconstruct hr hv.1 hv.2, extractKey_pre_eq E hpost (.h21, x) _ i _
        (fun hxJ => hwH hxJ i hv.1 j hv.2)]
    · rw [keysOf_of_not_valid _ _ _ _ _ hv]
  have hxPre : xPre st.params x = π.extract 0 st.params.o₂ := by
    rw [hx]; exact xPre_chal1Input hf hmu hcomsz
  have hpre0 : (preOf T st P E x g).proof = π.extract 0 st.params.o₂ := hxPre
  have hmidEq : midOf T st P E y g = { preOf T st P E x g with
      proof := (preOf T st P E x g).proof ++ yVc y ++ yCorr st.params y, chal1 := yChal1 y,
      hV := yHV y } := by
    unfold midOf midCore
    rw [hF3]
    simp only
    rw [logBefore_logBefore hO3, logBefore_jOf_logBefore T st P E g hO3]
    rfl
  have hmidProof : (midOf T st P E y g).proof = π.extract 0 st.params.o₄ := by
    rw [hmidEq]
    change (preOf T st P E x g).proof ++ yVc y ++ yCorr st.params y = _
    rw [hpre0, hy, yVc_chal2Input hf _ hc1s, yCorr_chal2Input hf]
    exact prefix_o₄ (pf := ⟨st.params, π⟩)
  have hpf : ch.pf st = ⟨st.params, π⟩ := by rw [Chain.pf, hchp]
  have hfield : ∀ (b : ByteArray) (k : String) (N : ℕ), st.params.o₄ ≤ N →
      (k = "corrections" ∨ k = "cmult" ∨ k = "vole_check" ∨ k = "correction") →
      Proof.field ⟨st.params, b⟩ k = Proof.field ⟨st.params, π.extract 0 N⟩ k →
      Proof.field (ch.pf st) k = Proof.field ⟨st.params, b⟩ k := by
    intro b k N hN hk h
    rw [h, field_prefix _ _ hk hN, hpf]
  have hpre : Chain.SamePrefix st (preOf T st P E x g) ch := by
    refine ⟨hkeys.symm, ?_, ?_, by rw [hchiv]; exact hivX.symm, hch5⟩
    · show Proof.field (ch.pf st) "corrections" =
        Proof.field ⟨st.params, (preOf T st P E x g).proof⟩ "corrections"
      rw [hpre0, hpf, field_extract_zero _ _ (Params.field_corrections _)
        (by have := o₂_le st.params; omega)]
    · show Proof.field (ch.pf st) "cmult" =
        Proof.field ⟨st.params, (preOf T st P E x g).proof⟩ "cmult"
      rw [hpre0, hpf, field_extract_zero _ _ (Params.field_cmult _) (by unfold Params.o₂; omega)]
  have hmidK : (midOf T st P E y g).keys = (preOf T st P E x g).keys := by rw [hmidEq]
  have hmidI : (midOf T st P E y g).iv = (preOf T st P E x g).iv := by rw [hmidEq]
  have hmid5 : (midOf T st P E y g).h5 = (preOf T st P E x g).h5 := by rw [hmidEq]
  have hmidC : (midOf T st P E y g).chal1 = yChal1 y := by rw [hmidEq]
  have hmidV : (midOf T st P E y g).hV = yHV y := by rw [hmidEq]
  have hmidPre : Chain.SamePrefix st (midOf T st P E y g) ch := by
    refine ⟨by rw [hmidK]; exact hpre.1, ?_, ?_, by rw [hmidI]; exact hpre.2.2.2.1,
      by rw [hmid5]; exact hpre.2.2.2.2⟩
    · exact hfield (midOf T st P E y g).proof "corrections" _ le_rfl (Or.inl rfl)
        (by rw [hmidProof])
    · exact hfield (midOf T st P E y g).proof "cmult" _ le_rfl (Or.inr (Or.inl rfl))
        (by rw [hmidProof])
  have hmid : Chain.SameMid st (midOf T st P E y g) ch := by
    refine ⟨hmidPre, ?_, ?_, ?_, ?_⟩
    · rw [hmidC, hy, yChal1_chal2Input _ hc1s]
    · show Proof.field (ch.pf st) "vole_check" =
        Proof.field ⟨st.params, (midOf T st P E y g).proof⟩ "vole_check"
      exact hfield (midOf T st P E y g).proof "vole_check" _ le_rfl (Or.inr (Or.inr (Or.inl rfl)))
        (by rw [hmidProof])
    · show Proof.field (ch.pf st) "correction" =
        Proof.field ⟨st.params, (midOf T st P E y g).proof⟩ "correction"
      exact hfield (midOf T st P E y g).proof "correction" _ le_rfl (Or.inr (Or.inr (Or.inr rfl)))
        (by rw [hmidProof])
    · rw [hmidV, hy, yHV_chal2Input hf _ hc1s hV4]
  refine ⟨⟨hpre, hmid, fun b => ?_⟩, fun i hi => ?_⟩
  · -- The chain committed at `z`.
    let tch : Chain := ⟨(midOf T st P E y g).proof ++ zQs st.params z, (midOf T st P E y g).keys,
      (midOf T st P E y g).iv, (midOf T st P E y g).h5, (midOf T st P E y g).chal1,
      (midOf T st P E y g).hV, zCheck z, zChal2 z,
      st.values (midOf T st P E y g).chal1 (st.combBytes (Hashes.ofTable g) (zChal2 z))⟩
    have htail : tailCore st E (logBefore (.h23, z) (gLog T st P E g))
        (logBefore (.inl (.h23, z)) (jOf g P E)) z g = (tch, deadOf T st P E g) := by
      unfold tailCore
      rw [hF4]
      simp only
      rw [logBefore_logBefore hO4, logBefore_jOf_logBefore T st P E g hO4, hdeadOf]
      unfold midDead
      rw [hF3]
      simp only
      rw [logBefore_logBefore hO3, logBefore_jOf_logBefore T st P E g hO3]
      rfl
    have hc2 : zChal2 z = ch.chal2 := by rw [hz, zChal2_chal3Input _ hc2s]
    have hzc : zCheck z = ch.z := by rw [hz, zCheck_chal3Input _ hc2s]
    have hm1 : (midOf T st P E y g).chal1 = ch.chal1 := hmid.2.1.symm
    have htp : tch.pf st = ⟨st.params, π.extract 0 st.params.o₅⟩ := by
      show (⟨st.params, (midOf T st P E y g).proof ++ zQs st.params z⟩ : Proof) = _
      rw [hmidProof, hz, zQs_chal3Input hf _ hc2s, prefix_o₅ (pf := ⟨st.params, π⟩)]
    have hf5 : ∀ k off n, st.params.field? k = some (off, n) → off + n ≤ st.params.o₅ →
        Proof.field (tch.pf st) k = Proof.field (ch.pf st) k := by
      intro k off n hk hN
      rw [htp, hpf, field_extract_zero _ _ hk hN]
    have hon : tch.OnChain st T = ch.OnChain st T := onChain_congr (st := st) (T := T)
      (by show (midOf T st P E y g).keys = _; exact hmidPre.1.symm)
      (by show (midOf T st P E y g).iv = _; exact hmidPre.2.2.2.1.symm)
      (by show (midOf T st P E y g).h5 = _; exact hmidPre.2.2.2.2.symm) hm1
      (by show (midOf T st P E y g).hV = _; exact hmid.2.2.2.2.symm) hc2 hzc
      (by show st.values _ _ = _; rw [hm1, hc2, hchv])
      (hf5 _ _ _ (Params.field_corrections _)
        (by have := o₂_le st.params; unfold Params.o₅ Params.o₄; omega))
      (hf5 _ _ _ (Params.field_cmult _) (by unfold Params.o₅ Params.o₄ Params.o₂; omega))
      (hf5 _ _ _ (Params.field_voleCheck _) (by unfold Params.o₅ Params.o₄; omega))
      (hf5 _ _ _ (Params.field_correction _) (by unfold Params.o₅ Params.o₄; omega))
      (hf5 _ _ _ (Params.field_qsProof _) (by unfold Params.o₅; omega))
    show accOf T st P E z g b ↔ _
    unfold accOf
    rw [htail]
    exact iff_of_eq (congrArg (deltaBlocks b ∈ ·) (hideSet_congr hon _))
  · -- L2(c): the hidden leaf of a tree outside `known` is a committed dead leaf.
    have hiτ : (i : ℕ) < BAVC.tau := i.isLt
    have hj : BAVC.deltaIndex (Proof.delta ⟨st.params, π⟩) i < 2 ^ BAVC.kOf i :=
      hiddenIndex_lt _ _
    refine ⟨BAVC.deltaIndex (Proof.delta ⟨st.params, π⟩) i, ?_⟩
    rw [hdeadOf]
    unfold deadAtX deadPre
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.2 hj, ?_⟩
    rw [hcom i hiτ _ hj]
    simp only
    rw [hivX, extractKey_pre_eq E hpost (.h21, x) _ i _ (fun hxJ => hwH hxJ i hiτ _ hj),
      @comAt_reconstruct_hidden (icPrg E.cipher) _ _ _ _ hr _ hiτ]
    simp only [knownOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simpa using hi

/-- **`hsame` of `ROM/Accept.lean` for the joint game**, with the chain data of
`ROM/CipherChain.lean`, the hits `chainHit` and the failure event Post (`PostOut`). -/
theorem sameChainHyp_ic : @SameChainHyp (icPrg E.cipher) (β × QueryLog specIC) T st
    (proverIC st E P) (preOf T st P E) (midOf T st P E) (accOf T st P E) (deadOf T st P E)
    (chainHit T st P E) (PostOut E) := by
  let _ : HasPrg := icPrg E.cipher
  intro g
  dsimp only
  have e1 := gameIC_fst T st P g E
  have etr := gameIC_tr T st P g E
  have ek := gameIC_keys T st P E g
  have ekn := gameIC_known T st P E g
  have eaux := gameIC_aux T st P g E
  simp only [gameIC] at e1 etr ek ekn eaux
  unfold PostOut
  rw [etr, ek, ekn, eaux, e1]
  intro hacc hpost hh leaves hr
  obtain ⟨hf, leaves', hr0, -⟩ := (accept_iff _ T st (πOf g P E)).1 hacc
  have hiv := (verify_iv_chal1 _ T st _ hacc hr0).1
  rw [hiv] at hr
  have hHs : ∀ k w, ((Hashes.ofTable g).hash k w).size = k.outLen := fun k w => by simp
  obtain ⟨hcom, hwH, hF3, hF4, hO3, hO4⟩ := chain_ident T st P E g hh _ hacc hr
  exact sameChain_core T st P E g hpost hf hr rfl rfl rfl rfl rfl rfl rfl
    (size_mu1 _ hHs st) (hHs _ _) rfl (Prob.Bytes.size_ba _)
    (by show (voleHashReceiver _ _ _ _ _ _).size = 4; simp [voleHashReceiver]) rfl
    (Prob.Bytes.size_ba _) hcom hwH hF3 hF4 hO3 hO4 (by unfold deadOf ivE; rw [hr])

/-- **`hL2` (L2(a)) of `ROM/Accept.lean` for the joint game**: outside Post and an opened dead
leaf, the accepted `Δ` hides every committed dead leaf. A non-hidden committed dead leaf has the
reconstruction's key `s'` as its key (binding of the commitment); either `P` queried `s'` at one of
the leaf's points, after `x` (a Post), or never (an opened dead leaf). -/
theorem deadHiddenHyp_ic : @DeadHiddenHyp (icPrg E.cipher) (β × QueryLog specIC) T st
    (proverIC st E P) (deadOf T st P E) (chainHit T st P E) (PostOut E) (DeadOpenOut st E) := by
  let _ : HasPrg := icPrg E.cipher
  intro g
  dsimp only
  have e1 := gameIC_fst T st P g E
  have etr := gameIC_tr T st P g E
  have eaux := gameIC_aux T st P g E
  simp only [gameIC] at e1 etr eaux
  unfold PostOut DeadOpenOut
  rw [etr, eaux, e1]
  intro hacc hpost hdead hh i j hj
  obtain ⟨hf, leaves, hr0, -⟩ := (accept_iff _ T st (πOf g P E)).1 hacc
  have hiv := (verify_iv_chal1 _ T st _ hacc hr0).1
  have hr : BAVC.reconstruct (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves := hr0
  have hHs : ∀ k w, ((Hashes.ofTable g).hash k w).size = k.outLen := fun k w => by simp
  obtain ⟨hcom, hwH, -⟩ := chain_ident T st P E g hh (fun _ _ => ByteArray.empty) hacc hr
  have hdeadOf : deadOf T st P E g =
      deadAtX T st P E (runX (Hashes.ofTable g) st (πOf g P E) leaves) g := by
    unfold deadOf ivE; rw [hr0]
  have hivX : ivX st (runX (Hashes.ofTable g) st (πOf g P E) leaves) g = ivE g st P E := by
    simp only [ivX, ivE, ivOf, runX]
    rw [xIvPre_chal1Input hf (size_mu1 _ hHs st) (hHs _ _)]
  rw [hdeadOf] at hj
  unfold deadAtX deadPre at hj
  rw [Finset.mem_filter] at hj
  obtain ⟨hjr, hjd⟩ := hj
  have hjlt : j < 2 ^ BAVC.kOf i := Finset.mem_range.1 hjr
  rw [hcom i i.isLt j hjlt, hivX] at hjd
  simp only at hjd
  rw [extractKey_pre_eq E hpost _ _ i _ (fun hxJ => hwH hxJ i i.isLt j hjlt)] at hjd
  by_contra hne
  have hne' : j ≠ BAVC.deltaIndex (Proof.delta ⟨st.params, πOf g P E⟩) i := Ne.symm hne
  have hsz := leafKey_size hr i.isLt hjlt hne'
  have hcomj : comAt leaves.coms i j =
      ba (E (blk 16 (leafKey leaves i j), lp (ivE g st P E) i 0)) ++
        ba (E (blk 16 (leafKey leaves i j), lp (ivE g st P E) i 1)) := by
    rw [comAt_reconstruct hr i.isLt hjlt hne', ← ba_blk_of_size hsz, leafCom_ic, ba_blk_of_size hsz]
    rfl
  by_cases hc : HasCell (cipherLog (jOf g P E)) (blk 16 (leafKey leaves i j))
      (lp (ivE g st P E) i 0) (lp (ivE g st P E) i 1)
  · have := extractKey_isSome_of_hasCell (E := E) hc
    rw [← hcomj] at this
    rw [Option.isNone_iff_eq_none] at hjd
    rw [hjd] at this
    exact absurd this (by simp)
  · apply hdead
    refine ⟨hacc, leaves, ?_, i, i.isLt, j, hjlt, hne', ?_⟩
    · rw [hiv]; exact hr0
    · rw [hiv]; exact hc

end SameIC

end Same

end VoleMole.ROM.IC
