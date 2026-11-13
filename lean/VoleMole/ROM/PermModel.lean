import VoleMole.ROM.CipherChain

/-!
# The ideal cipher as random permutations, with inverse queries (plan M6, permutation model)

`ROM/CipherBind.lean` … `ROM/AdaptFull.lean` model AES in the PRF view: every key's row is a
uniform *function* and the prover makes forward queries only. Here the cipher is the model of
`L0-L2-commitments.md` §3.1: a family `π = (π_k)_k` of independent uniformly random permutations
of `{0,1}¹²⁸` (`PTable`, drawn uniformly, eagerly), and the prover makes **forward and inverse**
queries.

* **The prover** `P : OracleComp specP α`: hash queries (`Dom`) and cipher queries
  `(true, (k, z)) ↦ π_k(z)`, `(false, (k, y)) ↦ π_k⁻¹(y)` (`PCell`, answered by `pans π`).
* **The normalized prover** `normP p π P` (`L0-L2` §3.2, N1 and the record convention of §3.1): a
  forward-only prover of `specIC` that runs `P`, answers an inverse query `(k, y)` by a forward
  query of the cipher at `(k, π_k⁻¹(y))` (so its cipher log holds the *record* `(k, x, π_k(x))` of
  every determination, forward or inverse), and queries `H₄(iv_pre ‖ μ ‖ 4)` with `iv_pre`, `μ`
  parsed from an `H₂¹` input right before that input (N1: the chain's `iv` is in the log at the
  chain). Against the forward table `π.fwd` it outputs what `P` outputs against `π`
  (`evalWithAnswerFn_normP`). The straight-line extractor of `ROM/CipherGame.lean` reads the
  normalized cipher log, i.e. the forward-and-inverse records `(k, z, π_k(z))`, as in `L0-L2` §6.
* **Query counts**: `normP` makes `P`'s cipher queries (`isQueryBoundP_right_normP`), `P`'s hash
  queries plus one `H₄` query per `H₂¹` query (`isKindQueryBound_normP`, `addH4`;
  `isQueryBoundP_left_normP`).
* **The run depends only on the records** (`normP_prefix`, `normP_congr`): a permutation table that
  agrees with `π` on the records of a log prefix gives the same prefix, followed by a cipher query
  under the same key; agreeing on all records gives the same run. This is what makes the eager
  counting of `ROM/PermCount.lean` apply.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ROM

/-! ## The model -/

/-- **A permutation table**: one permutation of the blocks per key. -/
abbrev PTable := Blk → Equiv.Perm Blk

/-- The uniform permutation table (for proofs; never run). Its cardinality is never computed. -/
noncomputable instance instSampleablePTable : SampleableType PTable := SampleableType.ofFintype _

/-- **The forward table** of a permutation table, the cipher the verifier and extractor read. -/
def PTable.fwd (π : PTable) : CTable := fun c => π c.1 c.2

@[simp] lemma PTable.fwd_apply (π : PTable) (c : Cell) : π.fwd c = π c.1 c.2 := rfl

/-- A cipher query: forward `(true, (k, z))` or inverse `(false, (k, y))`. -/
abbrev PCell := Bool × Cell

/-- The answer of a cipher query. -/
def pans (π : PTable) : PCell → Blk
  | (true, c) => π c.1 c.2
  | (false, c) => (π c.1).symm c.2

/-- A query of the prover: a hash query or a forward/inverse cipher query. -/
abbrev DomP := Dom ⊕ PCell

/-- The answer of a prover query. -/
abbrev AnsP : DomP → Type := Sum.elim Ans fun _ => Blk

/-- **The hash oracles and the ideal cipher with inverse queries.** -/
abbrev specP : OracleSpec DomP := OracleSpec.ofFn AnsP

/-- The complete answer table of a hash table and a permutation table. -/
def joinP (h : Table) (π : PTable) : ∀ t, AnsP t
  | .inl d => h d
  | .inr c => pans π c

/-- The `H₄` input of an `H₂¹` input `x`: `iv_pre ‖ μ ‖ 4`, both parsed from `x` (`μ` is the first
32 bytes). -/
def ivIn (p : Params) (x : ByteArray) : ByteArray := (xIvPre p x ++ x.extract 0 32).push 4

variable {α : Type}

/-- **The normalized prover** (`L0-L2` §3.2, N1): `P` with every inverse query `(k, y)` replaced by
the forward query at `(k, π_k⁻¹(y))` (its record), and an `H₄` query of the chain's `iv` before
every `H₂¹` query. -/
def normP (p : Params) (π : PTable) (P : OracleComp specP α) : OracleComp specIC α :=
  OracleComp.construct (C := fun _ => OracleComp specIC α)
    (fun a => pure a)
    (fun t _ rec => match t, rec with
      | .inl d, rec => if d.1 = .h21 then
          liftM (specIC.query (.inl (.h4, ivIn p d.2))) >>= fun _ =>
            liftM (specIC.query (.inl d)) >>= rec
        else liftM (specIC.query (.inl d)) >>= rec
      | .inr (true, c), rec => liftM (specIC.query (.inr c)) >>= rec
      | .inr (false, c), rec =>
          liftM (specIC.query (.inr (c.1, (π c.1).symm c.2))) >>= fun _ => rec ((π c.1).symm c.2))
    P

variable (p : Params) (π : PTable)

@[simp] lemma normP_pure (a : α) : normP p π (pure a : OracleComp specP α) = pure a := rfl

lemma normP_inl (d : Dom) (k : specP.Range (.inl d) → OracleComp specP α) :
    normP p π (liftM (specP.query (.inl d)) >>= k) = if d.1 = .h21 then
      liftM (specIC.query (.inl (.h4, ivIn p d.2))) >>= fun _ =>
        liftM (specIC.query (.inl d)) >>= fun u => normP p π (k u)
    else liftM (specIC.query (.inl d)) >>= fun u => normP p π (k u) := rfl

lemma normP_fwd (c : Cell) (k : specP.Range (.inr (true, c)) → OracleComp specP α) :
    normP p π (liftM (specP.query (.inr (true, c))) >>= k) =
      liftM (specIC.query (.inr c)) >>= fun u => normP p π (k u) := rfl

lemma normP_inv (c : Cell) (k : specP.Range (.inr (false, c)) → OracleComp specP α) :
    normP p π (liftM (specP.query (.inr (false, c))) >>= k) =
      liftM (specIC.query (.inr (c.1, (π c.1).symm c.2))) >>= fun _ =>
        normP p π (k ((π c.1).symm c.2)) := rfl

/-- **The normalized prover outputs what `P` outputs against the permutation oracle.** -/
theorem evalWithAnswerFn_normP (h : Table) (P : OracleComp specP α) :
    evalWithAnswerFn (QueryImpl.ofFn (join h π.fwd)) (normP p π P) =
      evalWithAnswerFn (QueryImpl.ofFn (joinP h π)) P := by
  induction P using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with d | ⟨b, c⟩
    · rw [normP_inl]
      split_ifs <;>
      · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
        exact ih (h d)
    · cases b
      · rw [normP_inv]
        simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
        exact ih _
      · rw [normP_fwd]
        simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
        exact ih _

/-! ## The run depends only on the records -/

/-- The joint log of the normalized prover. -/
abbrev jP (h : Table) (π : PTable) (P : OracleComp specP α) : QueryLog specIC :=
  tableQueryLog (normP p π P) (join h π.fwd)

/-- **Agreeing on the records of a prefix**: a permutation table `π'` that agrees with `σ` on the
records of a prefix of `σ`'s log gives the same prefix, followed by a cipher query under the same
key. -/
theorem normP_prefix (P : OracleComp specP α) (h : Table) (σ π' : PTable)
    (pre post : QueryLog specIC) (e : (t : DomIC) × AnsIC t) (κ w : Blk)
    (hJ : jP p h σ P = pre ++ e :: post) (he : e.1 = .inr (κ, w))
    (hag : ∀ (c : Cell) (v : Blk), (⟨.inr c, v⟩ : (t : DomIC) × AnsIC t) ∈ pre →
      π' c.1 c.2 = v) :
    ∃ w' v' post', jP p h π' P = pre ++ (⟨.inr (κ, w'), v'⟩ : (t : DomIC) × AnsIC t) :: post' := by
  induction P using OracleComp.inductionOn generalizing pre with
  | pure a => simp [jP] at hJ
  | query_bind t k ih =>
    simp only [jP] at ih hJ ⊢
    rcases t with d | ⟨b, c⟩
    · rw [normP_inl] at hJ ⊢
      split_ifs at hJ ⊢ with hd
      · rw [tableQueryLog_query_bind, tableQueryLog_query_bind] at hJ ⊢
        rcases pre with _ | ⟨a, pre⟩
        · rw [List.nil_append, List.cons.injEq] at hJ
          obtain ⟨rfl, -⟩ := hJ
          simp at he
        rcases pre with _ | ⟨b', pre⟩
        · rw [List.cons_append, List.nil_append, List.cons.injEq, List.cons.injEq] at hJ
          obtain ⟨-, rfl, -⟩ := hJ
          simp at he
        rw [List.cons_append, List.cons_append, List.cons.injEq, List.cons.injEq] at hJ
        obtain ⟨rfl, rfl, hJ⟩ := hJ
        obtain ⟨w', v', post', h'⟩ := ih (h d) pre hJ fun c v hc => hag c v (by simp [hc])
        have h'' : tableQueryLog (normP p π' (k (join h π'.fwd (.inl d)))) (join h π'.fwd) =
            pre ++ (⟨.inr (κ, w'), v'⟩ : (t : DomIC) × AnsIC t) :: post' := h'
        exact ⟨w', v', post', by rw [h'']; rfl⟩
      · rw [tableQueryLog_query_bind] at hJ ⊢
        rcases pre with _ | ⟨a, pre⟩
        · rw [List.nil_append, List.cons.injEq] at hJ
          obtain ⟨rfl, -⟩ := hJ
          simp at he
        rw [List.cons_append, List.cons.injEq] at hJ
        obtain ⟨rfl, hJ⟩ := hJ
        obtain ⟨w', v', post', h'⟩ := ih (h d) pre hJ fun c v hc => hag c v (by simp [hc])
        have h'' : tableQueryLog (normP p π' (k (join h π'.fwd (.inl d)))) (join h π'.fwd) =
            pre ++ (⟨.inr (κ, w'), v'⟩ : (t : DomIC) × AnsIC t) :: post' := h'
        exact ⟨w', v', post', by rw [h'']; rfl⟩
    · cases b
      · rw [normP_inv] at hJ ⊢
        rw [tableQueryLog_query_bind] at hJ ⊢
        rcases pre with _ | ⟨a, pre⟩
        · rw [List.nil_append, List.cons.injEq] at hJ
          obtain ⟨rfl, -⟩ := hJ
          simp only [Sum.inr.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, -⟩ := he
          exact ⟨_, _, _, rfl⟩
        rw [List.cons_append, List.cons.injEq] at hJ
        obtain ⟨rfl, hJ⟩ := hJ
        have hx : π' c.1 ((σ c.1).symm c.2) = σ c.1 ((σ c.1).symm c.2) :=
          hag (c.1, (σ c.1).symm c.2) _ List.mem_cons_self
        have hsymm : (π' c.1).symm c.2 = (σ c.1).symm c.2 := by
          rw [Equiv.symm_apply_eq, hx, Equiv.apply_symm_apply]
        obtain ⟨w', v', post', h'⟩ := ih _ pre hJ fun c v hc => hag c v (by simp [hc])
        refine ⟨w', v', post', ?_⟩
        rw [hsymm, h', join_inr, join_inr, PTable.fwd_apply, PTable.fwd_apply, hx]
        rfl
      · rw [normP_fwd] at hJ ⊢
        rw [tableQueryLog_query_bind] at hJ ⊢
        rcases pre with _ | ⟨a, pre⟩
        · rw [List.nil_append, List.cons.injEq] at hJ
          obtain ⟨rfl, -⟩ := hJ
          simp only [Sum.inr.injEq] at he
          subst he
          exact ⟨_, _, _, rfl⟩
        rw [List.cons_append, List.cons.injEq] at hJ
        obtain ⟨rfl, hJ⟩ := hJ
        have hx : π' c.1 c.2 = σ c.1 c.2 := hag c _ List.mem_cons_self
        have hxe : join h π'.fwd (.inr c) = join h σ.fwd (.inr c) := hx
        obtain ⟨w', v', post', h'⟩ := ih _ pre hJ fun c v hc => hag c v (by simp [hc])
        refine ⟨w', v', post', ?_⟩
        rw [hxe, h']
        rfl

/-- **Agreeing on all records gives the same run**: same log and same output. -/
theorem normP_congr (P : OracleComp specP α) (h : Table) (σ π' : PTable)
    (hag : ∀ (c : Cell) (v : Blk), (⟨.inr c, v⟩ : (t : DomIC) × AnsIC t) ∈ jP p h σ P →
      π' c.1 c.2 = v) :
    jP p h π' P = jP p h σ P ∧
      evalWithAnswerFn (QueryImpl.ofFn (join h π'.fwd)) (normP p π' P) =
        evalWithAnswerFn (QueryImpl.ofFn (join h σ.fwd)) (normP p σ P) := by
  induction P using OracleComp.inductionOn with
  | pure a => simp [jP]
  | query_bind t k ih =>
    simp only [jP] at ih hag ⊢
    rcases t with d | ⟨b, c⟩
    · rw [normP_inl] at hag
      rw [normP_inl, normP_inl]
      split_ifs at hag ⊢ with hd
      · rw [tableQueryLog_query_bind, tableQueryLog_query_bind] at hag
        rw [tableQueryLog_query_bind, tableQueryLog_query_bind, tableQueryLog_query_bind,
          tableQueryLog_query_bind]
        obtain ⟨h1, h2⟩ := ih (h d) fun c v hc => hag c v (by simp [hc])
        simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply,
          join_inl]
        exact ⟨by rw [h1], h2⟩
      · rw [tableQueryLog_query_bind] at hag
        rw [tableQueryLog_query_bind, tableQueryLog_query_bind]
        obtain ⟨h1, h2⟩ := ih (h d) fun c v hc => hag c v (by simp [hc])
        simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply,
          join_inl]
        exact ⟨by rw [h1], h2⟩
    · cases b
      · rw [normP_inv] at hag
        rw [normP_inv, normP_inv]
        rw [tableQueryLog_query_bind] at hag
        rw [tableQueryLog_query_bind, tableQueryLog_query_bind]
        have hx : π' c.1 ((σ c.1).symm c.2) = σ c.1 ((σ c.1).symm c.2) :=
          hag (c.1, (σ c.1).symm c.2) _ List.mem_cons_self
        have hsymm : (π' c.1).symm c.2 = (σ c.1).symm c.2 := by
          rw [Equiv.symm_apply_eq, hx, Equiv.apply_symm_apply]
        obtain ⟨h1, h2⟩ := ih ((σ c.1).symm c.2) fun c' v hc => hag c' v (List.mem_cons_of_mem _ hc)
        simp only [evalWithAnswerFn_bind]
        rw [hsymm]
        refine ⟨?_, h2⟩
        rw [h1, join_inr, join_inr, PTable.fwd_apply, PTable.fwd_apply, hx]
      · rw [normP_fwd] at hag
        rw [normP_fwd, normP_fwd]
        rw [tableQueryLog_query_bind] at hag
        rw [tableQueryLog_query_bind, tableQueryLog_query_bind]
        have hx : π' c.1 c.2 = σ c.1 c.2 := hag c _ List.mem_cons_self
        have hxe : join h π'.fwd (.inr c) = join h σ.fwd (.inr c) := hx
        obtain ⟨h1, h2⟩ := ih (join h σ.fwd (.inr c)) fun c' v hc => hag c' v (List.mem_cons_of_mem _ hc)
        simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
        rw [hxe]
        exact ⟨by rw [h1], h2⟩

/-- **N1: every `H₂¹` query is preceded by the `H₄` query of its `iv`.** -/
theorem normP_h4_mem (P : OracleComp specP α) (h : Table) (pre post : QueryLog specIC)
    (x : ByteArray) (u : Ans (.h21, x))
    (hJ : jP p h π P = pre ++ (⟨.inl (.h21, x), u⟩ : (t : DomIC) × AnsIC t) :: post) :
    (.inl (.h4, ivIn p x) : DomIC) ∈ pre.map Sigma.fst := by
  induction P using OracleComp.inductionOn generalizing pre with
  | pure a => simp [jP] at hJ
  | query_bind t k ih =>
    simp only [jP] at ih hJ
    rcases t with d | ⟨b, c⟩
    · rw [normP_inl] at hJ
      split_ifs at hJ with hd
      · rw [tableQueryLog_query_bind, tableQueryLog_query_bind] at hJ
        rcases pre with _ | ⟨a, pre⟩
        · rw [List.nil_append, List.cons.injEq] at hJ
          have := congrArg Sigma.fst hJ.1
          simp at this
        rcases pre with _ | ⟨b', pre⟩
        · rw [List.cons_append, List.nil_append, List.cons.injEq, List.cons.injEq] at hJ
          obtain ⟨rfl, he, -⟩ := hJ
          have hd' := congrArg Sigma.fst he
          simp only [Sum.inl.injEq] at hd'
          subst hd'
          simp
        rw [List.cons_append, List.cons_append, List.cons.injEq, List.cons.injEq] at hJ
        obtain ⟨-, -, hJ⟩ := hJ
        have := ih (h d) pre hJ
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (Or.inr this)
      · rw [tableQueryLog_query_bind] at hJ
        rcases pre with _ | ⟨a, pre⟩
        · rw [List.nil_append, List.cons.injEq] at hJ
          obtain ⟨he, -⟩ := hJ
          have hd' := congrArg Sigma.fst he
          simp only [Sum.inl.injEq] at hd'
          subst hd'
          exact absurd rfl hd
        rw [List.cons_append, List.cons.injEq] at hJ
        obtain ⟨-, hJ⟩ := hJ
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih (h d) pre hJ)
    · cases b
      · rw [normP_inv, tableQueryLog_query_bind] at hJ
        rcases pre with _ | ⟨a, pre⟩
        · rw [List.nil_append, List.cons.injEq] at hJ
          have := congrArg Sigma.fst hJ.1
          simp at this
        rw [List.cons_append, List.cons.injEq] at hJ
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih _ pre hJ.2)
      · rw [normP_fwd, tableQueryLog_query_bind] at hJ
        rcases pre with _ | ⟨a, pre⟩
        · rw [List.nil_append, List.cons.injEq] at hJ
          have := congrArg Sigma.fst hJ.1
          simp at this
        rw [List.cons_append, List.cons.injEq] at hJ
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih _ pre hJ.2)

/-! ## Query counts -/

/-- **At most `q k` queries to each hash domain `k`** (cipher queries are free here). -/
def IsKindQueryBoundP (P : OracleComp specP α) (q : Kind → ℕ) : Prop :=
  IsQueryBound P q (fun t b => match t with | .inl d => 0 < b d.1 | .inr _ => True)
    (fun t b => match t with | .inl d => Function.update b d.1 (b d.1 - 1) | .inr _ => b)

/-- The normalized prover's hash budget: one `H₄` query more per `H₂¹` query. -/
def addH4 (q : Kind → ℕ) : Kind → ℕ := Function.update q .h4 (q .h4 + q .h21)

lemma addH4_of_ne (q : Kind → ℕ) {k : Kind} (hk : k ≠ .h4) : addH4 q k = q k :=
  Function.update_of_ne hk _ _

/-- **The normalized prover's hash queries**: `P`'s and one `H₄` query per `H₂¹` query. -/
theorem isKindQueryBound_normP {P : OracleComp specP α} {q : Kind → ℕ}
    (hq : IsKindQueryBoundP P q) : IsKindQueryBoundIC (normP p π P) (addH4 q) := by
  induction P using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [IsKindQueryBoundP, isQueryBound_query_bind_iff] at hq
    obtain ⟨h0, hk⟩ := hq
    rcases t with ⟨kd, xd⟩ | ⟨b, c⟩
    · rw [normP_inl]
      simp only at h0 hk
      split_ifs with hd
      · simp only at hd
        subst hd
        rw [IsKindQueryBoundIC, isQueryBound_query_bind_iff]
        refine ⟨?_, fun _ => ?_⟩
        · show 0 < addH4 q .h4
          simp only [addH4, Function.update_self]
          omega
        rw [isQueryBound_query_bind_iff]
        refine ⟨?_, fun u => ?_⟩
        · show 0 < Function.update (addH4 q) .h4 (addH4 q .h4 - 1) .h21
          rw [Function.update_of_ne (by decide), addH4_of_ne q (by decide)]
          exact h0
        have hb : Function.update (Function.update (addH4 q) .h4 (addH4 q .h4 - 1)) .h21
            (Function.update (addH4 q) .h4 (addH4 q .h4 - 1) .h21 - 1) =
            addH4 (Function.update q .h21 (q .h21 - 1)) := by
          funext k'
          by_cases h1 : k' = .h21
          · subst h1
            simp [addH4]
          · by_cases h2 : k' = .h4
            · subst h2
              simp only [addH4, Function.update_self, Function.update_of_ne h1,
                Function.update_of_ne (show Kind.h21 ≠ .h4 by decide)]
              omega
            · simp [addH4, Function.update_of_ne h1, Function.update_of_ne h2]
        show IsKindQueryBoundIC (normP p π (k u))
          (Function.update (Function.update (addH4 q) .h4 (addH4 q .h4 - 1)) .h21
            (Function.update (addH4 q) .h4 (addH4 q .h4 - 1) .h21 - 1))
        rw [hb]
        exact ih u (hk u)
      · simp only at hd
        rw [IsKindQueryBoundIC, isQueryBound_query_bind_iff]
        refine ⟨?_, fun u => ?_⟩
        · show 0 < addH4 q kd
          by_cases h4 : kd = .h4
          · subst h4
            simp only [addH4, Function.update_self]
            omega
          · rw [addH4_of_ne q h4]; exact h0
        have hb : Function.update (addH4 q) kd (addH4 q kd - 1) =
            addH4 (Function.update q kd (q kd - 1)) := by
          funext k'
          by_cases h1 : k' = kd
          · subst h1
            by_cases h4 : k' = .h4
            · subst h4
              simp only [addH4, Function.update_self,
                Function.update_of_ne (show Kind.h21 ≠ .h4 by decide)]
              omega
            · simp [addH4, Function.update_of_ne h4]
          · by_cases h2 : k' = .h4
            · subst h2
              simp only [addH4, Function.update_self, Function.update_of_ne h1,
                Function.update_of_ne (Ne.symm hd)]
            · simp [addH4, Function.update_of_ne h1, Function.update_of_ne h2]
        show IsKindQueryBoundIC (normP p π (k u)) (Function.update (addH4 q) kd (addH4 q kd - 1))
        rw [hb]
        exact ih u (hk u)
    · cases b
      · rw [normP_inv, IsKindQueryBoundIC, isQueryBound_query_bind_iff]
        exact ⟨trivial, fun _ => ih _ (hk _)⟩
      · rw [normP_fwd, IsKindQueryBoundIC, isQueryBound_query_bind_iff]
        exact ⟨trivial, fun u => ih u (hk u)⟩

/-- **The normalized prover's cipher queries are `P`'s.** -/
theorem isQueryBoundP_right_normP {P : OracleComp specP α} {n : ℕ}
    (hn : IsQueryBoundP P (fun t => t.isRight = true) n) :
    IsQueryBoundP (normP p π P) (fun t => t.isRight = true) n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rcases t with d | ⟨b, c⟩
    · rw [normP_inl]
      simp only [Sum.isRight_inl, Bool.false_eq_true, ite_false] at hn
      split_ifs
      · rw [isQueryBoundP_query_bind_iff]
        simp only [Sum.isRight_inl, Bool.false_eq_true, not_false_eq_true, true_or, ite_false,
          true_and]
        intro _
        rw [isQueryBoundP_query_bind_iff]
        simp only [Sum.isRight_inl, Bool.false_eq_true, not_false_eq_true, true_or, ite_false,
          true_and]
        exact fun u => ih u (hn.2 u)
      · rw [isQueryBoundP_query_bind_iff]
        simp only [Sum.isRight_inl, Bool.false_eq_true, not_false_eq_true, true_or, ite_false,
          true_and]
        exact fun u => ih u (hn.2 u)
    · simp only [Sum.isRight_inr, not_true_eq_false, false_or, ite_true] at hn
      cases b
      · rw [normP_inv, isQueryBoundP_query_bind_iff]
        simp only [Sum.isRight_inr, not_true_eq_false, false_or, ite_true]
        exact ⟨hn.1, fun _ => ih _ (hn.2 _)⟩
      · rw [normP_fwd, isQueryBoundP_query_bind_iff]
        simp only [Sum.isRight_inr, not_true_eq_false, false_or, ite_true]
        exact ⟨hn.1, fun u => ih u (hn.2 u)⟩

/-- **The normalized prover's total hash queries**: `P`'s `n` and one `H₄` query per `H₂¹`
query. -/
theorem isQueryBoundP_left_normP {P : OracleComp specP α} {n : ℕ} {q : Kind → ℕ}
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (hq : IsKindQueryBoundP P q) :
    IsQueryBoundP (normP p π P) (fun t => t.isLeft = true) (n + q .h21) := by
  induction P using OracleComp.inductionOn generalizing n q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [IsKindQueryBoundP, isQueryBound_query_bind_iff] at hq
    obtain ⟨h0, hk⟩ := hq
    rcases t with d | ⟨b, c⟩
    · rw [normP_inl]
      simp only [Sum.isLeft_inl, not_true_eq_false, false_or, ite_true] at hn
      obtain ⟨hn0, hn⟩ := hn
      simp only at h0 hk
      split_ifs with hd
      · rw [hd] at h0
        rw [isQueryBoundP_query_bind_iff]
        simp only [Sum.isLeft_inl, not_true_eq_false, false_or, ite_true]
        refine ⟨by omega, fun _ => ?_⟩
        rw [isQueryBoundP_query_bind_iff]
        simp only [Sum.isLeft_inl, not_true_eq_false, false_or, ite_true]
        refine ⟨by omega, fun u => ?_⟩
        have := ih u (hn u) (hk u)
        rw [hd, Function.update_self] at this
        convert this using 1
        omega
      · rw [isQueryBoundP_query_bind_iff]
        simp only [Sum.isLeft_inl, not_true_eq_false, false_or, ite_true]
        refine ⟨by omega, fun u => ?_⟩
        have := ih u (hn u) (hk u)
        rw [Function.update_of_ne (Ne.symm hd)] at this
        convert this using 1
        omega
    · simp only [Sum.isLeft_inr, Bool.false_eq_true, ite_false] at hn
      cases b
      · rw [normP_inv, isQueryBoundP_query_bind_iff]
        simp only [Sum.isLeft_inr, Bool.false_eq_true, not_false_eq_true, true_or, ite_false,
          true_and]
        exact fun _ => ih _ (hn.2 _) (hk _)
      · rw [normP_fwd, isQueryBoundP_query_bind_iff]
        simp only [Sum.isLeft_inr, Bool.false_eq_true, not_false_eq_true, true_or, ite_false,
          true_and]
        exact fun u => ih u (hn.2 u) (hk u)

end VoleMole.ROM.IC
