import VoleMole.ROM.PermOpen

/-!
# Post in the permutation model: point-tied half-targets (`L0-L2` C3)

The PRF view's Post (`PostJ`, `ROM/CipherChain.lean`) charges a record that is the first one of its
key at a block `w` and at a neighbour `w'` and whose two values form a 32-byte block of an earlier
`H₁` input, at *any* points `w`. With inverse queries that event is no longer small: a prover can
pick a target block `(t₀, t₁)`, query `π_κ⁻¹(t₀)` for fresh keys `κ`, and win as soon as
`π_κ(π_κ⁻¹(t₀) ⊞ e₀) = t₁`, with probability about `1/2¹²⁸` per query. The paper's C3 ties every
half-target to its *points*: those of the chain `Θ` whose commitments they are.

* **Half-targets** (`halfT p pre`): for every `H₂¹` input `x` of the log prefix `pre`, its `iv`
  (the answer of the `H₄` query at `ivIn p x`, which the normalized prover made before `x`, N1),
  every leaf `(i, j)` of `x`'s committed commitments (`comPre`, read off the prefix's hash entries
  before `x`, `hashEnt`), the two points `x^Θ_{c,i}`, `x^Θ_{1−c,i}` and the two halves of the
  commitment, in both orders: at most `4608` per `H₂¹` input (`card_halfT_le`).
* **`PostP`**: a record under a key `κ` such that some half-target of the prefix before it has
  both its points unrecorded under `κ` and `π_κ` maps them to its values.
* **`prEvent_perm_postP_le`**: `Pr_π[PostP] ≤ q_E·4608·q₂₁·p²`, `p = 1/(2¹²⁸ − q_E)`
  (`prEvent_perm_prefix_le` at each of the `q_E` records). The paper's `8·L·q₂·q_E·p²`.
* **`keysPre_of_not_postP`**: outside `PostP` the keys committed at the `H₂¹` inputs are found before
  them (`KeysPre` of `ROM/CipherSame.lean`), for the normalized prover. So `sameChainHyp_ic_of`,
  `deadHiddenHyp_ic_of` (and `combFreshHyp_ic_of`) hold with `chainFail := PostPOut`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## The hash entries of a joint log -/

/-- The hash entries of a joint log, with their answers. -/
def hashEnt : QueryLog specIC → QueryLog spec
  | [] => []
  | ⟨.inl d, u⟩ :: L => ⟨d, u⟩ :: hashEnt L
  | ⟨.inr _, _⟩ :: L => hashEnt L

lemma hashEnt_append (A B : QueryLog specIC) : hashEnt (A ++ B) = hashEnt A ++ hashEnt B := by
  induction A with
  | nil => rfl
  | cons e A ih =>
    obtain ⟨t, u⟩ := e
    cases t with
    | inl d => simp only [List.cons_append, hashEnt, ih]
    | inr x => simp only [List.cons_append, hashEnt, ih]

lemma map_fst_hashEnt (L : QueryLog specIC) : (hashEnt L).map Sigma.fst = hashLog L := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨t, u⟩ := e
    cases t with
    | inl d => simp only [hashEnt, List.map_cons, ih]; rfl
    | inr x => simp only [hashEnt]; exact ih

/-- **The hash log of `runE E P` is `P`'s hash entries.** -/
theorem tableQueryLog_runE_eq {α : Type} (h : Table) (E : CTable) (P : OracleComp specIC α) :
    tableQueryLog (runE E P) h = hashEnt (tableQueryLog P (join h E)) := by
  induction P using OracleComp.inductionOn with
  | pure a => simp [hashEnt]
  | query_bind t k ih =>
    cases t with
    | inl d =>
      rw [runE_inl, tableQueryLog_query_bind, tableQueryLog_map', tableQueryLog_query_bind]
      exact congrArg (List.cons _) (ih (h d))
    | inr x =>
      rw [runE_inr, tableQueryLog_map', tableQueryLog_query_bind]
      exact ih (E x)

lemma hashEnt_answer {L : QueryLog specIC} {g : Table} {E : CTable}
    (hL : ∀ e ∈ L, e = ⟨e.1, join g E e.1⟩) : ∀ e ∈ hashEnt L, e = ⟨e.1, g e.1⟩ := by
  induction L with
  | nil => simp [hashEnt]
  | cons e L ih =>
    obtain ⟨t, u⟩ := e
    have ih' := ih fun e he => hL e (List.mem_cons_of_mem _ he)
    cases t with
    | inl d =>
      intro e he
      simp only [hashEnt, List.mem_cons] at he
      rcases he with rfl | he
      · have := hL _ List.mem_cons_self
        have h2 : u = g d := eq_of_heq (Sigma.mk.inj this).2
        rw [h2]
      · exact ih' e he
    | inr x => exact ih'

section Data

variable {β : Type} (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β))
  (E : CTable)

/-- **The game's hash log before a cell of `P`'s is `P`'s hash entries before it.** -/
theorem logBefore_gLog_eq (g : Table) {d : Dom}
    (hd : (.inl d : DomIC) ∈ (jOf g P E).map Sigma.fst) :
    logBefore d (gLog T st P E g) = logBefore d (hashEnt (jOf g P E)) := by
  unfold gLog gameIC game proverIC
  rw [tableQueryLog_bind, tableQueryLog_bind, tableQueryLog_runE_eq, List.append_assoc]
  refine logBefore_append_of_mem _ ?_
  rw [map_fst_hashEnt]
  exact mem_hashLog.2 hd

end Data

/-! ## Half-targets -/

/-- The `iv` of an `H₂¹` input `x` recorded in a hash log: the answer of its `H₄` query. -/
def ivAt (p : Params) (G : QueryLog spec) (x : ByteArray) : Option ByteArray :=
  (G.find? fun e => decide (e.1 = (.h4, ivIn p x))).map fun e => (e.2 : Ans e.1).ba

lemma ivAt_eq {p : Params} {G : QueryLog spec} {x : ByteArray} {g : Table}
    (hG : ∀ e ∈ G, e = ⟨e.1, g e.1⟩) (hx : ((.h4, ivIn p x) : Dom) ∈ G.map Sigma.fst) :
    ivAt p G x = some (g (.h4, ivIn p x)).ba := by
  unfold ivAt
  obtain ⟨e, he, he1⟩ := List.mem_map.1 hx
  obtain ⟨e₀, hf⟩ : ∃ e₀, G.find? (fun e => decide (e.1 = (.h4, ivIn p x))) = some e₀ :=
    Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨e, he, by simp [he1]⟩)
  have hp := List.find?_some hf
  have hm := List.mem_of_find?_eq_some hf
  rw [hf, Option.map_some]
  obtain ⟨t, v⟩ := e₀
  simp only [decide_eq_true_eq] at hp
  subst hp
  have := hG _ hm
  simp only at this
  rw [← (Sigma.mk.inj this).2 |> eq_of_heq]

/-- **The half-targets of a prefix** (see the module docstring). -/
noncomputable def halfT (p : Params) (pre : QueryLog specIC) : Finset (Blk × Blk × Blk × Blk) :=
  ((kindIns .h21 (hashLog pre)).flatMap fun x =>
    match ivAt p (hashEnt pre) x with
    | none => []
    | some iv => (List.range BAVC.tau).flatMap fun i => (List.range (2 ^ BAVC.kOf i)).flatMap
        fun j => match comPre (logBefore (.h21, x) (hashEnt pre)) x i j with
          | none => []
          | some a => [(lp iv i 0, lp iv i 1, (split32 a).1, (split32 a).2),
              (lp iv i 1, lp iv i 0, (split32 a).2, (split32 a).1)]).toFinset

lemma length_flatMap_le {γ δ : Type} (l : List γ) (f : γ → List δ) (b : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ b) : (l.flatMap f).length ≤ b * l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, mul_add, mul_one, add_comm]
    exact add_le_add (ih fun y hy => h y (List.mem_cons_of_mem _ hy)) (h x List.mem_cons_self)

lemma card_halfT_le (p : Params) (pre : QueryLog specIC) :
    #(halfT p pre) ≤ 4608 * (kindIns .h21 (hashLog pre)).length := by
  unfold halfT
  refine (List.toFinset_card_le _).trans (length_flatMap_le _ _ _ fun x _ => ?_)
  split
  · exact Nat.zero_le _
  · rw [List.length_flatMap]
    refine (List.sum_le_sum (g := fun i => 2 * 2 ^ BAVC.kOf i) fun i _ => ?_).trans
      (le_of_eq (by decide))
    refine (length_flatMap_le _ _ 2 fun j _ => ?_).trans (by rw [List.length_range])
    split <;> simp

lemma mem_halfT_ne {p : Params} {pre : QueryLog specIC} {j : Blk × Blk × Blk × Blk}
    (hj : j ∈ halfT p pre) : j.1 ≠ j.2.1 := by
  unfold halfT at hj
  obtain ⟨x, -, hx⟩ := List.mem_flatMap.1 (List.mem_toFinset.1 hj)
  split at hx
  · simp at hx
  · obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hx
    obtain ⟨jj, -, hjj⟩ := List.mem_flatMap.1 hi
    split at hjj
    · simp at hjj
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hjj
      rcases hjj with rfl | rfl
      · exact lp_ne _ _
      · exact (lp_ne _ _).symm

/-! ## Post, point-tied -/

/-- **Post in the permutation model** (`L0-L2` C3(b), point-tied): some record under a key `κ`
such that a half-target of the prefix before it has both points unrecorded under `κ` and `E_κ`
maps them to its values. -/
def PostP (p : Params) (E : CTable) (J : QueryLog specIC) : Prop :=
  ∃ pre e post κ w, J = pre ++ e :: post ∧ e.1 = .inr (κ, w) ∧ ∃ j ∈ halfT p pre,
    (.inr (κ, j.1) : DomIC) ∉ pre.map Sigma.fst ∧ (.inr (κ, j.2.1) : DomIC) ∉ pre.map Sigma.fst ∧
    E (κ, j.1) = j.2.2.1 ∧ E (κ, j.2.1) = j.2.2.2

/-- Post (point-tied), for the game's output. -/
def PostPOut {β : Type} (p : Params) (E : CTable) (r : Out (β × QueryLog specIC)) : Prop :=
  PostP p E r.2.1.aux.2

lemma beforeCipher_sublist : ∀ (n : ℕ) (L : QueryLog specIC), (beforeCipher n L).Sublist L
  | _, [] => List.Sublist.slnil
  | n, ⟨.inl _, _⟩ :: L => (beforeCipher_sublist n L).cons_cons _
  | 0, ⟨.inr _, _⟩ :: _ => List.nil_sublist _
  | n + 1, ⟨.inr _, _⟩ :: L => (beforeCipher_sublist n L).cons_cons _

lemma hashLog_sublist {A B : QueryLog specIC} (h : A.Sublist B) :
    (hashLog A).Sublist (hashLog B) := h.filterMap _

/-- **Post in the permutation model**: `≤ q_E·4608·q₂₁·p²`, `p = 1/(2¹²⁸ − q_E)`, at every hash
table. -/
theorem prEvent_perm_postP_le {α : Type} (p : Params) (h : Table) (P : OracleComp specP α)
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable}[PostP p π.fwd (jP p h π P)] ≤
      qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
  classical
  let TT : QueryLog specIC → Blk → PTable → Finset (Blk × Blk × Blk × Blk) :=
    fun pre _ _ => halfT p pre
  let Ev : ℕ → PTable → Prop := fun n π => ∃ pre e post κ w, jP p h π P = pre ++ e :: post ∧
    (cipherLog pre).length = n ∧ e.1 = .inr (κ, w) ∧ ∃ j ∈ TT pre κ π,
    (.inr (κ, j.1) : DomIC) ∉ pre.map Sigma.fst ∧
    (.inr (κ, j.2.1) : DomIC) ∉ pre.map Sigma.fst ∧ π κ j.1 = j.2.2.1 ∧ π κ j.2.1 = j.2.2.2
  have hstep : ∀ n < qE, Pr{let π ← $ᵗ PTable}[Ev n π] ≤
      ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
    intro n hn
    refine (prEvent_perm_prefix_le p h P n TT (fun _ _ _ _ _ => rfl)
      (fun j => j.1) (fun j => j.2.1) (fun j => j.2.2.1) (fun j => j.2.2.2)
      (fun pre κ σ j hj => mem_halfT_ne hj) (4608 * q .h21) (fun σ κ => ?_)).trans ?_
    · refine (card_halfT_le p _).trans (Nat.mul_le_mul_left _ ?_)
      refine (length_kindIns_le_of_sublist (hashLog_sublist (beforeCipher_sublist n _))).trans ?_
      have := length_kindIns_hashLog_le _ (isKindQueryBound_normP p σ hq) (join h σ.fwd) .h21
      rwa [addH4_of_ne q (by decide)] at this
    · gcongr
      exact (inv_two_le_pE n).trans (pow_le_pow_left₀ zero_le (pE_mono (by omega)) 2)
  have hcover : ∀ π : PTable, PostP p π.fwd (jP p h π P) → ∃ n ∈ range qE, Ev n π := by
    rintro π ⟨pre, e, post, κ, w, hJ, he, j, hj, h1, h2, h3, h4⟩
    have hlen : (cipherLog pre).length < qE := by
      have := length_cipherLog_le _ (isQueryBoundP_right_normP p π hqE) (join h π.fwd)
      have hJ' : tableQueryLog (normP p π P) (join h π.fwd) = pre ++ e :: post := hJ
      obtain ⟨t, u⟩ := e
      simp only at he
      subst he
      rw [hJ'] at this
      have hcl : cipherLog (pre ++ ⟨.inr (κ, w), u⟩ :: post) =
          cipherLog pre ++ ⟨(κ, w), u⟩ :: cipherLog post := by
        simp [cipherLog, List.filterMap_append]
      rw [hcl, List.length_append, List.length_cons] at this
      omega
    exact ⟨_, mem_range.2 hlen, pre, e, post, κ, w, hJ, rfl, he, j, hj, h1, h2, h3, h4⟩
  calc Pr{let π ← $ᵗ PTable}[PostP p π.fwd (jP p h π P)]
      ≤ Pr{let π ← $ᵗ PTable}[∃ n ∈ range qE, Ev n π] := prEvent_mono _ _ _ hcover
    _ ≤ ∑ n ∈ range qE, Pr{let π ← $ᵗ PTable}[Ev n π] := prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _n ∈ range qE, ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 :=
        sum_le_sum fun n hn => hstep n (mem_range.1 hn)
    _ = qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
        rw [sum_const, card_range, nsmul_eq_mul, mul_assoc]

/-! ## Without Post, the committed keys are found before the chain -/

section Keys

variable {β : Type} (T : CrtTables) (st : Statement) (P : OracleComp specP (ByteArray × β))

/-- **Outside `PostP`, the keys committed at the `H₂¹` inputs are found before them** (`KeysPre`),
for the normalized prover at any permutation table. -/
theorem keysPre_of_not_postP_gen (p : Params) (hp : st.params = p) (π : PTable) (g : Table)
    (hpost : ¬PostP p π.fwd (jOf g (normP p π P) π.fwd)) :
    KeysPre st π.fwd (jOf g (normP p π P) π.fwd) (gLog T st (normP p π P) π.fwd g) g := by
  intro x hxmu i hi j hj a hcom _
  set J := jOf g (normP p π P) π.fwd
  set E := π.fwd
  set iv := ivX st x g
  by_cases hx : (.inl (.h21, x) : DomIC) ∈ J.map Sigma.fst
  swap
  · rw [logBefore_eq_of_not_mem hx]
  obtain ⟨u, rest, hJ⟩ := exists_split_of_mem hx
  set Jx := logBefore (.inl (.h21, x)) J
  have hcl : cipherLog J = cipherLog Jx ++ cipherLog (⟨.inl (.h21, x), u⟩ :: rest) := by
    rw [hJ, cipherLog_append]
  rw [extractKey_eq, extractKey_eq, hcl, List.find?_append]
  cases hA : (cipherLog Jx).find? (keyPred E iv i a) with
  | some q => rfl
  | none =>
    simp only [Option.none_or, Option.map_none]
    cases hB : (cipherLog (⟨.inl (.h21, x), u⟩ :: rest)).find? (keyPred E iv i a) with
    | none => rfl
    | some q₀ =>
      exfalso
      apply hpost
      obtain ⟨hpB, B₁, B₂, hB₁, hnB⟩ := List.find?_eq_some_iff_append.1 hB
      change cipherLog rest = _ at hB₁
      obtain ⟨R₁, R₂, hR, hcR⟩ := exists_split_cipherLog hB₁
      have hnA : ∀ q ∈ cipherLog Jx, keyPred E iv i a q = false := fun q hq => by
        have := List.find?_eq_none.1 hA q hq
        simpa using this
      set pre := Jx ++ (⟨.inl (.h21, x), u⟩ : (t : DomIC) × AnsIC t) :: R₁
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
      obtain ⟨-, hcomK⟩ := hp0
      have hfresh : ∀ w₀, (w₀ = lp iv i 0 ∨ w₀ = lp iv i 1) →
          (.inr (κ, w₀) : DomIC) ∉ pre.map Sigma.fst := by
        intro w₀ hw₀ hmem
        obtain ⟨q, hq, hq1⟩ := List.mem_map.1 (mem_cipherLog.2 hmem)
        have := hpre q hq
        simp only [keyPred, decide_eq_false_iff_not, not_and] at this
        rw [hq1] at this
        exact this hw₀ hcomK
      -- The answers of the joint log are the tables'.
      have hans : ∀ e ∈ J, e = ⟨e.1, join g E e.1⟩ :=
        tableQueryLog_answer (normP p π P) (join g E)
      have hpreJ : ∀ e ∈ pre, e ∈ J := fun e he => by
        rw [hJ']; exact List.mem_append_left _ he
      have hG : ∀ e ∈ hashEnt pre, e = ⟨e.1, g e.1⟩ :=
        hashEnt_answer fun e he => hans e (hpreJ e he)
      -- The `iv` of `x` is recorded before `x` (N1).
      have h4 : ((.h4, ivIn p x) : Dom) ∈ (hashEnt pre).map Sigma.fst := by
        rw [map_fst_hashEnt]
        refine mem_hashLog.2 ?_
        have hJ0 : jP p g π P =
            Jx ++ (⟨.inl (.h21, x), u⟩ : (t : DomIC) × AnsIC t) :: rest := hJ
        have := normP_h4_mem p π P g Jx rest x u hJ0
        exact List.map_subset _ (List.subset_append_left _ _) this
      have hiv : ivAt p (hashEnt pre) x = some iv := by
        rw [ivAt_eq hG h4]
        show some (g (.h4, (xIvPre p x ++ x.extract 0 32).push 4)).ba = some (ivX st x g)
        rw [hxmu, ← hp]
        rfl
      -- The commitment committed at `x`, from the prefix.
      have hxpre : (.inl (.h21, x) : DomIC) ∈ pre.map Sigma.fst := by
        simp [pre]
      have hcom' : comPre (logBefore (.h21, x) (hashEnt pre)) x i j = some a := by
        have e1 := logBefore_gLog_eq T st (normP p π P) E g hx
        have e2 : logBefore ((.h21, x) : Dom) (hashEnt J) =
            logBefore ((.h21, x) : Dom) (hashEnt pre) := by
          rw [hJ', hashEnt_append]
          refine logBefore_append_of_mem _ ?_
          rw [map_fst_hashEnt]
          exact mem_hashLog.2 hxpre
        rw [← e2, ← e1]
        exact hcom
      have hsplit : split32 a = (E (κ, lp iv i 0), E (κ, lp iv i 1)) := by
        rw [← hcomK, split32_ba]
      refine ⟨pre, _, R₂, κ, w, hJ', rfl, (lp iv i 0, lp iv i 1, (split32 a).1, (split32 a).2),
        ?_, hfresh _ (Or.inl rfl), hfresh _ (Or.inr rfl), by rw [hsplit], by rw [hsplit]⟩
      unfold halfT
      rw [List.mem_toFinset, List.mem_flatMap]
      refine ⟨x, mem_kindIns (mem_hashLog.2 hxpre), ?_⟩
      rw [hiv]
      simp only
      refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_flatMap.2
        ⟨j, List.mem_range.2 hj, ?_⟩⟩
      rw [hcom']
      exact List.mem_cons_self

/-- `keysPre_of_not_postP_gen` at the statement's own parameters. -/
theorem keysPre_of_not_postP (π : PTable) (g : Table)
    (hpost : ¬PostP st.params π.fwd (jOf g (Wn st P π) π.fwd)) :
    KeysPre st π.fwd (jOf g (Wn st P π) π.fwd) (gLog T st (Wn st P π) π.fwd g) g :=
  keysPre_of_not_postP_gen T st P st.params rfl π g hpost

end Keys

end VoleMole.ROM.IC
