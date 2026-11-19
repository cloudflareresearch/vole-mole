import VoleMole.ROM.PermJoint

/-!
# Families of forward provers indexed by the permutation table (permutation model)

The failure bounds of the permutation model (`ROM/PermBind.lean`, `ROM/PermPost.lean`,
`ROM/PermOpen.lean`, `ROM/PermJoint.lean`) are stated for the normalized prover `normP p π P` of a
fixed prover `P` of the permutation model. Their proofs use two properties of the family
`π ↦ normP p π P` only (besides query bounds and, for Post, N1):

* **prefix**: a table `π'` that agrees with `σ` on the records of a prefix of `σ`'s log gives the
  same prefix, followed by a cipher query under the same key (`normP_prefix`);
* **congruence**: agreeing on all records gives the same log and output (`normP_congr`).

`RecFamily Q` states the two for any family `Q : PTable → OracleComp specIC α` of forward provers.
It holds for constant families (`recFamily_const`), for an inverse query recorded as a forward
query (`recFamily_inv`) and is closed under binds (`RecFamily.bind`), so a derived prover that runs
a normalized adversary and then forward-only computations is a `RecFamily` without being
`normP p π P` of one fixed prover (PomFRIT's derived provers, `ROM/OneMorePerm.lean`: the
verifications there query the chain's `iv` themselves, `normP` would query it again).

The bounds, for a `RecFamily` with uniform query bounds (copies of the `normP` versions, the
proofs unchanged up to the two properties):

* `prEvent_fam_prefix_le` (`prEvent_perm_prefix_le`), `prEvent_fam_coll_le`
  (`prEvent_perm_coll_le`, `≤ 2·q_E²·p²`);
* `keysPre_of_not_postP_Q`: outside Post at `p`, `KeysPre`, for **any** forward prover whose log
  has N1 at `p` (`IvBefore`); `prEvent_fam_postP_le` (`≤ q_E·4608·q₂₁·p²`);
* `prEvent_fam_deadQueried_le` (`≤ q₁·p'²`);
* adaptively: `prEvent_jointF_postP_le`, `prEvent_jointF_bindFail_le`,
  `prEvent_jointF_deadOpen_le`, and `sum_fail_le_fam` (`≤ |J|·failEpsP q q_E`).

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## Families and their two properties -/

section Family

variable {α β : Type}

/-- The joint log of a family member against its own forward table. -/
abbrev jQ (Q : PTable → OracleComp specIC α) (h : Table) (σ : PTable) : QueryLog specIC :=
  tableQueryLog (Q σ) (join h σ.fwd)

/-- `π` agrees with every record of the log `L`. -/
def AgreeOn (L : QueryLog specIC) (π : PTable) : Prop :=
  ∀ (c : Cell) (v : Blk), (⟨.inr c, v⟩ : (t : DomIC) × AnsIC t) ∈ L → π c.1 c.2 = v

lemma AgreeOn.mono {L L' : QueryLog specIC} {π : PTable} (h : AgreeOn L' π) (hs : L ⊆ L') :
    AgreeOn L π := fun c v hc => h c v (hs hc)

/-- **A family of forward provers that depends on the table only through its records.** -/
structure RecFamily (Q : PTable → OracleComp specIC α) : Prop where
  pfx : ∀ (h : Table) (σ π' : PTable) (pre post : QueryLog specIC) (e : (t : DomIC) × AnsIC t)
    (κ w : Blk), jQ Q h σ = pre ++ e :: post → e.1 = .inr (κ, w) → AgreeOn pre π' →
    ∃ w' v' post', jQ Q h π' = pre ++ (⟨.inr (κ, w'), v'⟩ : (t : DomIC) × AnsIC t) :: post'
  cgr : ∀ (h : Table) (σ π' : PTable), AgreeOn (jQ Q h σ) π' →
    jQ Q h π' = jQ Q h σ ∧ evalWithAnswerFn (QueryImpl.ofFn (join h π'.fwd)) (Q π') =
      evalWithAnswerFn (QueryImpl.ofFn (join h σ.fwd)) (Q σ)

/-- A record of a family member's log is answered by its forward table. -/
lemma answer_of_mem_jQ {Q : PTable → OracleComp specIC α} {h : Table} {σ : PTable} {c : Cell}
    {v : Blk} (hm : (⟨.inr c, v⟩ : (t : DomIC) × AnsIC t) ∈ jQ Q h σ) : σ c.1 c.2 = v := by
  have := tableQueryLog_answer (Q σ) (join h σ.fwd) _ hm
  exact (eq_of_heq (Sigma.mk.inj this).2).symm

theorem recFamily_pure (a : α) : RecFamily (fun _ => (pure a : OracleComp specIC α)) where
  pfx h σ π' pre post e κ w hJ := by simp [jQ] at hJ
  cgr h σ π' _ := by simp [jQ]

lemma jQ_query (t : DomIC) (h : Table) (σ : PTable) :
    jQ (fun _ => (liftM (specIC.query t) : OracleComp specIC (AnsIC t))) h σ =
      [⟨t, join h σ.fwd t⟩] :=
  tableQueryLog_query t _

lemma jQ_bind {X : PTable → OracleComp specIC α} {K : PTable → α → OracleComp specIC β}
    (h : Table) (σ : PTable) :
    jQ (fun π => X π >>= K π) h σ = jQ X h σ ++
      jQ (fun π => K π (evalWithAnswerFn (QueryImpl.ofFn (join h σ.fwd)) (X σ))) h σ :=
  tableQueryLog_bind _ _ _

/-- **One query, not depending on the table.** -/
theorem recFamily_query (t : DomIC) :
    RecFamily (fun _ => (liftM (specIC.query t) : OracleComp specIC (AnsIC t))) where
  pfx h σ π' pre post e κ w hJ he _ := by
    rw [jQ_query] at hJ
    rcases pre with _ | ⟨a, pre⟩
    · rw [List.nil_append, List.cons.injEq] at hJ
      obtain ⟨rfl, rfl⟩ := hJ
      simp only at he
      subst he
      exact ⟨w, _, [], by rw [jQ_query]; rfl⟩
    · rw [List.cons_append, List.cons.injEq] at hJ
      simp at hJ
  cgr h σ π' hag := by
    rw [jQ_query, jQ_query]
    rcases t with d | c
    · exact ⟨rfl, rfl⟩
    · have hc : π' c.1 c.2 = σ c.1 c.2 :=
        hag c _ (by rw [jQ_query]; exact List.mem_singleton_self _)
      have : join h π'.fwd (.inr c) = join h σ.fwd (.inr c) := hc
      refine ⟨by rw [this], ?_⟩
      simp only [evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      exact this

/-- **Families are closed under binds** (the continuation may depend on the table and on the
output). -/
theorem RecFamily.bind {X : PTable → OracleComp specIC α} {K : PTable → α → OracleComp specIC β}
    (hX : RecFamily X) (hK : ∀ a, RecFamily fun π => K π a) :
    RecFamily fun π => X π >>= K π where
  pfx h σ π' pre post e κ w hJ he hag := by
    rw [jQ_bind] at hJ
    rw [jQ_bind]
    set aσ := evalWithAnswerFn (QueryImpl.ofFn (join h σ.fwd)) (X σ)
    rcases List.append_eq_append_iff.1 hJ with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
    · -- the record is in the continuation's part
      obtain ⟨hl, hev⟩ := hX.cgr h σ π' (hag.mono fun x hx => by
        rw [h1]; exact List.mem_append_left _ hx)
      obtain ⟨w', v', post', hK'⟩ := (hK aσ).pfx h σ π' a' post e κ w h2 he
        (hag.mono fun x hx => by rw [h1]; exact List.mem_append_right _ hx)
      refine ⟨w', v', post', ?_⟩
      rw [hl, hev, hK', h1, List.append_assoc]
    · rcases c' with _ | ⟨e', c''⟩
      · rw [List.append_nil] at h1
        rw [List.nil_append] at h2
        obtain ⟨hl, hev⟩ := hX.cgr h σ π' (hag.mono fun x hx => by rw [← h1]; exact hx)
        obtain ⟨w', v', post', hK'⟩ := (hK aσ).pfx h σ π' [] post e κ w
          (by rw [List.nil_append]; exact h2.symm) he (fun _ _ hc => by simp at hc)
        refine ⟨w', v', post', ?_⟩
        rw [hl, hev, hK', h1, List.nil_append]
      · rw [List.cons_append, List.cons.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨w', v', post', hX'⟩ := hX.pfx h σ π' pre c'' e κ w h1 he hag
        refine ⟨w', v', post' ++ jQ (fun π => K π (evalWithAnswerFn
          (QueryImpl.ofFn (join h π'.fwd)) (X π'))) h π', ?_⟩
        rw [hX']
        simp
  cgr h σ π' hag := by
    rw [jQ_bind] at hag
    rw [jQ_bind, jQ_bind]
    obtain ⟨hl, hev⟩ := hX.cgr h σ π' (hag.mono fun x hx => List.mem_append_left _ hx)
    set aσ := evalWithAnswerFn (QueryImpl.ofFn (join h σ.fwd)) (X σ)
    obtain ⟨hl', hev'⟩ := (hK aσ).cgr h σ π' (hag.mono fun x hx => List.mem_append_right _ hx)
    refine ⟨?_, ?_⟩
    · rw [hl, hev, hl']
    · rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, hev]
      exact hev'

/-- **A forward prover that does not depend on the table.** -/
theorem recFamily_const (K : OracleComp specIC α) : RecFamily (fun _ => K) := by
  induction K using OracleComp.inductionOn with
  | pure a => exact recFamily_pure a
  | query_bind t k ih =>
    exact RecFamily.bind (X := fun _ => (liftM (specIC.query t) : OracleComp specIC (AnsIC t)))
      (K := fun _ u => k u) (recFamily_query t) ih

theorem RecFamily.map {X : PTable → OracleComp specIC α} (hX : RecFamily X) (f : α → β) :
    RecFamily fun π => f <$> X π := by
  have := hX.bind (K := fun _ a => (pure (f a) : OracleComp specIC β)) fun a => recFamily_pure _
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using this

/-- The inverse-query family. -/
abbrev invQ (κ y : Blk) (f : Blk → Blk → β) (π : PTable) : OracleComp specIC β :=
  liftM (specIC.query (.inr (κ, (π κ).symm y))) >>= fun v => pure (f ((π κ).symm y) v)

lemma jQ_invQ (κ y : Blk) (f : Blk → Blk → β) (h : Table) (σ : PTable) :
    jQ (invQ κ y f) h σ = [⟨.inr (κ, (σ κ).symm y), join h σ.fwd (.inr (κ, (σ κ).symm y))⟩] := by
  simp only [jQ, invQ, tableQueryLog_query_bind, tableQueryLog_pure]

lemma eval_invQ (κ y : Blk) (f : Blk → Blk → β) (h : Table) (σ : PTable) :
    evalWithAnswerFn (QueryImpl.ofFn (join h σ.fwd)) (invQ κ y f σ) =
      f ((σ κ).symm y) (join h σ.fwd (.inr (κ, (σ κ).symm y))) := by
  simp only [invQ, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply,
    evalWithAnswerFn_pure]

/-- **An inverse query `(κ, y)` recorded as the forward query at `π_κ⁻¹(y)`.** -/
theorem recFamily_inv (κ y : Blk) (f : Blk → Blk → β) : RecFamily (invQ κ y f) where
  pfx h σ π' pre post e κ' w hJ he _ := by
    rw [jQ_invQ] at hJ
    rcases pre with _ | ⟨a, pre⟩
    · rw [List.nil_append, List.cons.injEq] at hJ
      obtain ⟨rfl, rfl⟩ := hJ
      simp only [Sum.inr.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact ⟨_, _, [], by rw [jQ_invQ]; rfl⟩
    · rw [List.cons_append, List.cons.injEq] at hJ
      simp at hJ
  cgr h σ π' hag := by
    have hx : π' κ ((σ κ).symm y) = σ κ ((σ κ).symm y) :=
      hag (κ, (σ κ).symm y) _ (by rw [jQ_invQ]; exact List.mem_singleton_self _)
    have hsymm : (π' κ).symm y = (σ κ).symm y := by
      rw [Equiv.symm_apply_eq, hx, Equiv.apply_symm_apply]
    have hv : join h π'.fwd (.inr (κ, (σ κ).symm y)) = join h σ.fwd (.inr (κ, (σ κ).symm y)) := hx
    rw [jQ_invQ, jQ_invQ, eval_invQ, eval_invQ, hsymm, hv]
    exact ⟨rfl, rfl⟩

/-- **Two families with the same log and output at every table.** -/
theorem RecFamily.of_eq {Q Q' : PTable → OracleComp specIC α} (hQ : RecFamily Q)
    (h : ∀ π g, jQ Q' g π = jQ Q g π ∧ evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (Q' π) =
      evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (Q π)) : RecFamily Q' where
  pfx g σ π' pre post e κ w hJ he hag := by
    rw [(h σ g).1] at hJ
    obtain ⟨w', v', post', h'⟩ := hQ.pfx g σ π' pre post e κ w hJ he hag
    exact ⟨w', v', post', by rw [(h π' g).1, h']⟩
  cgr g σ π' hag := by
    rw [(h σ g).1] at hag
    obtain ⟨h1, h2⟩ := hQ.cgr g σ π' hag
    exact ⟨by rw [(h π' g).1, (h σ g).1, h1], by rw [(h π' g).2, (h σ g).2, h2]⟩

end Family

/-! ## The bound for an event charged at one record -/

section Prefix

variable {α : Type} (Q : PTable → OracleComp specIC α) (hQ : RecFamily Q)

include hQ in
/-- **An event charged at the `n`-th record** (`prEvent_perm_prefix_le` for a `RecFamily`). -/
theorem prEvent_fam_prefix_le {J : Type} [Fintype J] (h : Table)
    (n : ℕ) (TT : QueryLog specIC → Blk → PTable → Finset J)
    (hTT : ∀ pre κ σ σ', (∀ κ', κ' ≠ κ → σ' κ' = σ κ') → TT pre κ σ' = TT pre κ σ)
    (z₁ z₂ y₁ y₂ : J → Blk) (hz : ∀ pre κ σ j, j ∈ TT pre κ σ → z₁ j ≠ z₂ j) (K : ℕ)
    (hK : ∀ σ κ, #(TT (beforeCipher n (jQ Q h σ)) κ σ) ≤ K) :
    Pr{let π ← $ᵗ PTable}[∃ pre e post κ w, jQ Q h π = pre ++ e :: post ∧
        (cipherLog pre).length = n ∧ e.1 = .inr (κ, w) ∧ ∃ j ∈ TT pre κ π,
        (.inr (κ, z₁ j) : DomIC) ∉ pre.map Sigma.fst ∧
        (.inr (κ, z₂ j) : DomIC) ∉ pre.map Sigma.fst ∧ π κ (z₁ j) = y₁ j ∧ π κ (z₂ j) = y₂ j] ≤
      K * ((((2 ^ 128 - n) * (2 ^ 128 - n - 1) : ℕ) : ℝ≥0∞))⁻¹ := by
  let kk : PTable → Blk := fun σ => ((kthCell n (jQ Q h σ)).getD default).1
  let XX : PTable → Finset Blk := fun σ => keyIns (kk σ) (beforeCipher n (jQ Q h σ))
  let TTT : PTable → Finset J := fun σ => TT (beforeCipher n (jQ Q h σ)) (kk σ) σ
  let ev : J → PTable → Prop := fun j σ => (kthCell n (jQ Q h σ)).isSome ∧ j ∈ TTT σ ∧
    z₁ j ≠ z₂ j ∧ z₁ j ∉ XX σ ∧ z₂ j ∉ XX σ ∧ σ (kk σ) (z₁ j) = y₁ j ∧ σ (kk σ) (z₂ j) = y₂ j
  have hdec : ∀ σ pre (e : (t : DomIC) × AnsIC t) post κ w, jQ Q h σ = pre ++ e :: post →
      (cipherLog pre).length = n → e.1 = .inr (κ, w) →
      kk σ = κ ∧ beforeCipher n (jQ Q h σ) = pre ∧ kthCell n (jQ Q h σ) = some (κ, w) := by
    intro σ pre e post κ w hJ hn he
    have hs := beforeCipher_kthCell (pre := pre) (post := post) he
    rw [hn, ← hJ] at hs
    exact ⟨by simp only [kk, hs.2, Option.getD_some], hs.1, hs.2⟩
  refine (prEvent_mono _ _ (fun π => ∃ j, ev j π) ?_).trans
    (prEvent_perm_two_le ev kk XX TTT z₁ z₂ y₁ y₂ K n ?_ ?_ ?_ ?_)
  · rintro π ⟨pre, e, post, κ, w, hJ, hn, he, j, hj, h1, h2, h3, h4⟩
    obtain ⟨hk, hb, hc⟩ := hdec π pre e post κ w hJ hn he
    refine ⟨j, by rw [hc]; rfl, ?_, hz _ _ _ _ hj, ?_, ?_, ?_, ?_⟩
    · show j ∈ TT (beforeCipher n (jQ Q h π)) (kk π) π
      rw [hb, hk]; exact hj
    · show z₁ j ∉ keyIns (kk π) (beforeCipher n (jQ Q h π))
      rw [hb, hk, mem_keyIns]; exact h1
    · show z₂ j ∉ keyIns (kk π) (beforeCipher n (jQ Q h π))
      rw [hb, hk, mem_keyIns]; exact h2
    · rw [hk]; exact h3
    · rw [hk]; exact h4
  · intro j σ hj
    exact hj.2
  · rintro j σ ⟨hs, -⟩ π hoff hX
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨pre, u, post, hJ, hn⟩ := exists_of_kthCell hc
    obtain ⟨hk, hb, -⟩ := hdec σ pre _ post c.1 c.2 hJ hn rfl
    obtain ⟨w', v', post', hJ'⟩ := hQ.pfx h σ π pre post _ c.1 c.2 hJ rfl
      (fun c' v hc' => by
        have hmem : (⟨.inr c', v⟩ : (t : DomIC) × AnsIC t) ∈ jQ Q h σ := by
          rw [hJ]; exact List.mem_append_left _ hc'
        rw [← answer_of_mem_jQ hmem]
        by_cases hkc : c'.1 = kk σ
        · have hx : c'.2 ∈ XX σ := by
            show c'.2 ∈ keyIns (kk σ) (beforeCipher n (jQ Q h σ))
            rw [hb, mem_keyIns, ← hkc]
            exact List.mem_map.2 ⟨_, hc', rfl⟩
          have := hX c'.2 hx
          rw [← hkc] at this
          exact this
        · rw [hoff c'.1 hkc])
    obtain ⟨hk', hb', -⟩ := hdec π pre _ post' c.1 w' hJ' hn rfl
    refine ⟨hk'.trans hk.symm, ?_⟩
    show TT (beforeCipher n (jQ Q h π)) (kk π) π = TT (beforeCipher n (jQ Q h σ)) (kk σ) σ
    rw [hb', hk', hb, hk]
    exact hTT pre c.1 σ π fun κ' hκ' => hoff κ' (hk ▸ hκ')
  · intro σ
    exact (card_keyIns_le _ _).trans (length_cipherLog_beforeCipher _ _)
  · intro σ
    exact hK σ (kk σ)

include hQ in
/-- **The collision bound for a `RecFamily`** (`prEvent_perm_coll_le`): `≤ 2·q_E²·p²`. -/
theorem prEvent_fam_coll_le (h : Table) (qE : ℕ)
    (hqE : ∀ π, IsQueryBoundP (Q π) (fun t => t.isRight = true) qE) :
    Pr{let π ← $ᵗ PTable}[freshBadC (runH h (Q π)) ∅ π.fwd collBad] ≤
      2 * qE ^ 2 * pE qE ^ 2 := by
  classical
  let TT : QueryLog specIC → Blk → PTable → Finset (Blk × Blk × Blk × Blk) :=
    fun pre κ σ => collT (cipherLog pre) κ σ
  let Ev : ℕ → PTable → Prop := fun n π => ∃ pre e post κ w, jQ Q h π = pre ++ e :: post ∧
    (cipherLog pre).length = n ∧ e.1 = .inr (κ, w) ∧ ∃ j ∈ TT pre κ π,
    (.inr (κ, j.1) : DomIC) ∉ pre.map Sigma.fst ∧
    (.inr (κ, j.2.1) : DomIC) ∉ pre.map Sigma.fst ∧ π κ j.1 = j.2.2.1 ∧ π κ j.2.1 = j.2.2.2
  have hstep : ∀ n, Pr{let π ← $ᵗ PTable}[Ev n π] ≤ ((4 * n : ℕ) : ℝ≥0∞) * pE qE ^ 2 ∨
      qE ≤ n := by
    intro n
    by_cases hn : n < qE
    · left
      refine (prEvent_fam_prefix_le Q hQ h n TT (fun pre κ σ σ' hσ => collT_congr _ κ σ σ' hσ)
        (fun j => j.1) (fun j => j.2.1) (fun j => j.2.2.1) (fun j => j.2.2.2)
        (fun pre κ σ j hj => mem_collT_ne hj) (4 * n) (fun σ κ => (card_collT_le _ _ _).trans
          (Nat.mul_le_mul_left _ (length_cipherLog_beforeCipher _ _)))).trans ?_
      gcongr
      exact (inv_two_le_pE n).trans (pow_le_pow_left₀ (zero_le) (pE_mono (by omega)) 2)
    · exact Or.inr (by omega)
  have hcover : ∀ π : PTable, freshBadC (runH h (Q π)) ∅ π.fwd collBad →
      ∃ n ∈ range qE, Ev n π := by
    intro π hfb
    rw [freshBadC_empty_iff] at hfb
    obtain ⟨cpre, q, cpost, hlog, hfresh, hbad⟩ := hfb
    rw [← cipherLog_tableQueryLog] at hlog
    obtain ⟨R₁, R₂, hJ, hR⟩ := exists_split_cipherLog hlog
    have hlen : cpre.length < qE := by
      have := length_cipherLog_le _ (hqE π) (join h π.fwd)
      rw [hlog, List.length_append, List.length_cons] at this
      omega
    obtain ⟨⟨k, w⟩, v⟩ := q
    obtain ⟨w', hw', κ, hκ, hn, hs, h1, h2⟩ := hbad
    simp only at hw' hκ hn hs h1 h2 hfresh
    have hnone : ∀ d, cacheOfLog (∅ : cspec.QueryCache) cpre d = none → ∀ e ∈ cpre, e.1 ≠ d :=
      fun d hd => ((cacheOfLog_eq_none _ _ _).1 hd).2
    have hsome : ∀ d, (cacheOfLog (∅ : cspec.QueryCache) cpre d).isSome → ∃ e ∈ cpre, e.1 = d := by
      intro d hd
      by_contra hc
      rw [Option.isSome_iff_ne_none, ne_eq, cacheOfLog_eq_none] at hd
      exact hd ⟨rfl, fun e he he1 => hc ⟨e, he, he1⟩⟩
    refine ⟨cpre.length, mem_range.2 hlen, R₁, _, R₂, k, w, hJ, by rw [hR], rfl,
      (w, w', π κ w, π κ w'), ?_, ?_, ?_, ?_, ?_⟩
    · show (w, w', π κ w, π κ w') ∈ collT (cipherLog R₁) k π
      rw [hR]
      unfold collT
      rw [List.mem_toFinset, List.mem_flatMap]
      rcases hs with hs | hs
      · obtain ⟨e, he, he1⟩ := hsome _ hs
        refine ⟨e, he, ?_⟩
        rw [he1]
        simp only [hκ, ↓reduceIte]
        rcases mem_adj.1 hw' with rfl | rfl <;> simp
      · obtain ⟨e, he, he1⟩ := hsome _ hs
        refine ⟨e, he, ?_⟩
        rw [he1]
        simp only [hκ, ↓reduceIte]
        rcases mem_adj.1 (mem_adj_symm hw') with h' | h' <;> rw [h'] <;> simp
    · rw [← mem_cipherLog, hR]
      intro hm
      obtain ⟨e, he, he1⟩ := List.mem_map.1 hm
      exact hfresh e he he1
    · rw [← mem_cipherLog, hR]
      intro hm
      obtain ⟨e, he, he1⟩ := List.mem_map.1 hm
      exact hnone _ hn e he he1
    · exact h1.symm
    · exact h2.symm
  calc Pr{let π ← $ᵗ PTable}[freshBadC (runH h (Q π)) ∅ π.fwd collBad]
      ≤ Pr{let π ← $ᵗ PTable}[∃ n ∈ range qE, Ev n π] := prEvent_mono _ _ _ hcover
    _ ≤ ∑ n ∈ range qE, Pr{let π ← $ᵗ PTable}[Ev n π] := prEvent_exists_finset_le _ _ _
    _ ≤ ∑ n ∈ range qE, ((4 * n : ℕ) : ℝ≥0∞) * pE qE ^ 2 :=
        sum_le_sum fun n hn => (hstep n).resolve_right (by rw [mem_range] at hn; omega)
    _ = ((∑ n ∈ range qE, 4 * n : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by rw [← sum_mul, Nat.cast_sum]
    _ ≤ ((2 * qE ^ 2 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
        gcongr
        exact sum_range_four_mul_le qE
    _ = 2 * qE ^ 2 * pE qE ^ 2 := by push_cast; ring

include hQ in
/-- **Post at `p` for a `RecFamily`** (`prEvent_perm_postP_le_iv`): `≤ q_E·4608·q₂₁·p²`. -/
theorem prEvent_fam_postP_le (p : Params) (h : Table) (qE : ℕ)
    (hqE : ∀ π, IsQueryBoundP (Q π) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : ∀ π, IsKindQueryBoundIC (Q π) q) :
    Pr{let π ← $ᵗ PTable}[PostP p π.fwd (jQ Q h π)] ≤
      qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
  classical
  let TT : QueryLog specIC → Blk → PTable → Finset (Blk × Blk × Blk × Blk) :=
    fun pre _ _ => halfT p pre
  let Ev : ℕ → PTable → Prop := fun n π => ∃ pre e post κ w, jQ Q h π = pre ++ e :: post ∧
    (cipherLog pre).length = n ∧ e.1 = .inr (κ, w) ∧ ∃ j ∈ TT pre κ π,
    (.inr (κ, j.1) : DomIC) ∉ pre.map Sigma.fst ∧
    (.inr (κ, j.2.1) : DomIC) ∉ pre.map Sigma.fst ∧ π κ j.1 = j.2.2.1 ∧ π κ j.2.1 = j.2.2.2
  have hstep : ∀ n < qE, Pr{let π ← $ᵗ PTable}[Ev n π] ≤
      ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
    intro n hn
    refine (prEvent_fam_prefix_le Q hQ h n TT (fun _ _ _ _ _ => rfl)
      (fun j => j.1) (fun j => j.2.1) (fun j => j.2.2.1) (fun j => j.2.2.2)
      (fun pre κ σ j hj => mem_halfT_ne hj) (4608 * q .h21) (fun σ κ => ?_)).trans ?_
    · refine (card_halfT_le p _).trans (Nat.mul_le_mul_left _ ?_)
      refine (length_kindIns_le_of_sublist (hashLog_sublist (beforeCipher_sublist n _))).trans ?_
      exact length_kindIns_hashLog_le _ (hq σ) (join h σ.fwd) .h21
    · gcongr
      exact (inv_two_le_pE n).trans (pow_le_pow_left₀ zero_le (pE_mono (by omega)) 2)
  have hcover : ∀ π : PTable, PostP p π.fwd (jQ Q h π) → ∃ n ∈ range qE, Ev n π := by
    rintro π ⟨pre, e, post, κ, w, hJ, he, j, hj, h1, h2, h3, h4⟩
    have hlen : (cipherLog pre).length < qE := by
      have := length_cipherLog_le _ (hqE π) (join h π.fwd)
      have hJ' : tableQueryLog (Q π) (join h π.fwd) = pre ++ e :: post := hJ
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
  calc Pr{let π ← $ᵗ PTable}[PostP p π.fwd (jQ Q h π)]
      ≤ Pr{let π ← $ᵗ PTable}[∃ n ∈ range qE, Ev n π] := prEvent_mono _ _ _ hcover
    _ ≤ ∑ n ∈ range qE, Pr{let π ← $ᵗ PTable}[Ev n π] := prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _n ∈ range qE, ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 :=
        sum_le_sum fun n hn => hstep n (mem_range.1 hn)
    _ = qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
        rw [sum_const, card_range, nsmul_eq_mul, mul_assoc]

end Prefix

/-! ## Without Post, the committed keys are found before the chain (any forward prover) -/

section Keys

variable {β : Type} (T : CrtTables) (st : Statement) (Q : OracleComp specIC (ByteArray × β))

/-- **Outside `PostP p`, the keys committed at the `H₂¹` inputs are found before them**, for any
forward prover whose log has N1 at `p` for the `H₂¹` inputs with the statement's `mu₁` (the only
ones `KeysPre` reads). -/
theorem keysPre_of_not_postP_mu (p : Params) (hp : st.params = p) (E : CTable) (g : Table)
    (hN1 : ∀ (pre post : QueryLog specIC) (x : ByteArray) (u : Ans (.h21, x)),
      jOf g Q E = pre ++ (⟨.inl (.h21, x), u⟩ : (t : DomIC) × AnsIC t) :: post →
      x.extract 0 32 = st.mu1 (Hashes.ofTable g) →
      (.inl (.h4, ivIn p x) : DomIC) ∈ pre.map Sigma.fst)
    (hpost : ¬PostP p E (jOf g Q E)) :
    KeysPre st E (jOf g Q E) (gLog T st Q E g) g := by
  intro x hxmu i hi j hj a hcom _
  set J := jOf g Q E
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
      have hans : ∀ e ∈ J, e = ⟨e.1, join g E e.1⟩ :=
        tableQueryLog_answer Q (join g E)
      have hpreJ : ∀ e ∈ pre, e ∈ J := fun e he => by
        rw [hJ']; exact List.mem_append_left _ he
      have hG : ∀ e ∈ hashEnt pre, e = ⟨e.1, g e.1⟩ :=
        hashEnt_answer fun e he => hans e (hpreJ e he)
      have h4 : ((.h4, ivIn p x) : Dom) ∈ (hashEnt pre).map Sigma.fst := by
        rw [map_fst_hashEnt]
        refine mem_hashLog.2 ?_
        have hJ0 : jOf g Q E =
            Jx ++ (⟨.inl (.h21, x), u⟩ : (t : DomIC) × AnsIC t) :: rest := hJ
        have := hN1 Jx rest x u hJ0 hxmu
        exact List.map_subset _ (List.subset_append_left _ _) this
      have hiv : ivAt p (hashEnt pre) x = some iv := by
        rw [ivAt_eq hG h4]
        show some (g (.h4, (xIvPre p x ++ x.extract 0 32).push 4)).ba = some (ivX st x g)
        rw [hxmu, ← hp]
        rfl
      have hxpre : (.inl (.h21, x) : DomIC) ∈ pre.map Sigma.fst := by
        simp [pre]
      have hcom' : comPre (logBefore (.h21, x) (hashEnt pre)) x i j = some a := by
        have e1 := logBefore_gLog_eq T st Q E g hx
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

/-- **Outside `PostP p`, the keys committed at the `H₂¹` inputs are found before them**, for any
forward prover whose log has N1 at `p` (`keysPre_of_not_postP_iv` without the normalization). -/
theorem keysPre_of_not_postP_Q (p : Params) (hp : st.params = p) (E : CTable) (g : Table)
    (hN1 : IvBefore p (jOf g Q E)) (hpost : ¬PostP p E (jOf g Q E)) :
    KeysPre st E (jOf g Q E) (gLog T st Q E g) g :=
  keysPre_of_not_postP_mu T st Q p hp E g (fun pre post x u h _ => hN1 pre post x u h) hpost

end Keys

/-! ## A dead leaf whose leaf hash the prover queried -/

section DeadG

variable {β : Type} (g : Table) (stf : PTable → Statement)
  (Q : PTable → OracleComp specIC (ByteArray × β)) (hQ : RecFamily Q)

/-- The protected inputs of the dead key: its records and the GGM points. (Irreducible.) -/
@[irreducible] noncomputable def deadXQ (σ : PTable) : Finset Blk :=
  keyIns (deadKey g (stf σ) (Q σ) σ.fwd) (jOf g (Q σ) σ.fwd) ∪
    ggmPts (ivE g (stf σ) (Q σ) σ.fwd)

lemma mem_deadXQ {σ : PTable} {x : Blk} : x ∈ deadXQ g stf Q σ ↔
    x ∈ keyIns (deadKey g (stf σ) (Q σ) σ.fwd) (jOf g (Q σ) σ.fwd) ∨
      x ∈ ggmPts (ivE g (stf σ) (Q σ) σ.fwd) := by
  unfold deadXQ
  rw [mem_union]

lemma card_deadXQ_le (σ : PTable) : #(deadXQ g stf Q σ) ≤
    #(keyIns (deadKey g (stf σ) (Q σ) σ.fwd) (jOf g (Q σ) σ.fwd)) + 4606 := by
  unfold deadXQ
  exact (card_union_le _ _).trans (add_le_add le_rfl (card_ggmPts_le _))

include hQ in
/-- **Changing the dead key's permutation off its protected inputs changes nothing else**
(`deadQueried_perm_inv_g` for a `RecFamily`). -/
theorem deadQueried_fam_inv
    (hstf : ∀ σ π : PTable, evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (Q π) =
      evalWithAnswerFn (QueryImpl.ofFn (join g σ.fwd)) (Q σ) → stf π = stf σ)
    {σ π : PTable} (hE : ∃ p', DeadAt g (stf σ) (Q σ) σ.fwd p')
    (hoff : ∀ κ, κ ≠ deadKey g (stf σ) (Q σ) σ.fwd → π κ = σ κ)
    (hX : ∀ x ∈ deadXQ g stf Q σ, π (deadKey g (stf σ) (Q σ) σ.fwd) x =
      σ (deadKey g (stf σ) (Q σ) σ.fwd) x) :
    deadKey g (stf π) (Q π) π.fwd = deadKey g (stf σ) (Q σ) σ.fwd ∧
      dc g (stf π) (Q π) π.fwd 0 = dc g (stf σ) (Q σ) σ.fwd 0 ∧
      dc g (stf π) (Q π) π.fwd 1 = dc g (stf σ) (Q σ) σ.fwd 1 ∧
      deadTargets g (stf π) (Q π) π.fwd = deadTargets g (stf σ) (Q σ) σ.fwd := by
  obtain ⟨hi, -, -, -⟩ := deadAt_deadPt g (stf σ) (Q σ) hE
  set k := deadKey g (stf σ) (Q σ) σ.fwd
  obtain ⟨hJ, hO⟩ := hQ.cgr g σ π fun c v hc => by
    rw [← answer_of_mem_jQ hc]
    by_cases hk : c.1 = k
    · have hx : c.2 ∈ deadXQ g stf Q σ := by
        refine (mem_deadXQ g stf Q).2 (Or.inl (mem_keyIns.2 ?_))
        rw [show (deadKey g (stf σ) (Q σ) σ.fwd, c.2) = c from Prod.ext hk.symm rfl]
        exact List.mem_map.2 ⟨_, hc, rfl⟩
      have := hX c.2 hx
      rw [← hk] at this
      exact this
    · rw [hoff c.1 hk]
  have hπ : πOf g (Q π) π.fwd = πOf g (Q σ) σ.fwd := congrArg Prod.fst hO
  have hJ' : jOf g (Q π) π.fwd = jOf g (Q σ) σ.fwd := hJ
  have hs : stf π = stf σ := hstf σ π hO
  rw [hs]
  have hiv : ivE g (stf σ) (Q π) π.fwd = ivE g (stf σ) (Q σ) σ.fwd := by
    simp only [ivE, hπ]
  have hrt : rtOf g (stf σ) (Q π) π.fwd = rtOf g (stf σ) (Q σ) σ.fwd := by
    unfold rtOf
    rw [hiv, hπ]
    refine recTree_ic_congr_cells fun k' n hn c hc => ?_
    show π k' _ = σ k' _
    by_cases hk : k' = k
    · subst hk
      exact hX _ ((mem_deadXQ g stf Q).2 (Or.inr (gp_mem_ggmPts _ hn hc)))
    · rw [hoff k' hk]
  have hdead : DeadAt g (stf σ) (Q π) π.fwd = DeadAt g (stf σ) (Q σ) σ.fwd := by
    funext p'
    simp only [DeadAt, hπ, hJ', hiv, hrt]
  have hpt : deadPt g (stf σ) (Q π) π.fwd = deadPt g (stf σ) (Q σ) σ.fwd := by
    simp only [deadPt, hdead]
  have hkey : deadKey g (stf σ) (Q π) π.fwd = k := by simp only [k, deadKey, hrt, hpt]
  refine ⟨hkey, ?_, ?_, ?_⟩
  · simp only [dc, hkey, hiv, hpt, k]
  · simp only [dc, hkey, hiv, hpt, k]
  · simp only [deadTargets, hJ', hpt]

include hQ in
/-- **A dead leaf whose leaf hash `Q π` queried** (`prEvent_perm_deadQueried_le_g` for a
`RecFamily`): `≤ q₁·p'²`, `p' = 1/(2¹²⁸ − q_E − 4607)`. -/
theorem prEvent_fam_deadQueried_le
    (hstf : ∀ σ π : PTable, evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (Q π) =
      evalWithAnswerFn (QueryImpl.ofFn (join g σ.fwd)) (Q σ) → stf π = stf σ) (qE : ℕ)
    (hqE : ∀ π, IsQueryBoundP (Q π) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : ∀ π, IsKindQueryBoundIC (Q π) q) :
    Pr{let π ← $ᵗ PTable}[DeadQueried g (stf π) (Q π) π.fwd] ≤
      q .h1 * pE (qE + 4607) ^ 2 := by
  classical
  let kk : PTable → Blk := fun σ => deadKey g (stf σ) (Q σ) σ.fwd
  let TT : PTable → Finset (Blk × Blk × Blk × Blk) := fun σ =>
    (deadTargets g (stf σ) (Q σ) σ.fwd).image fun t =>
      ((dc g (stf σ) (Q σ) σ.fwd 0).2, (dc g (stf σ) (Q σ) σ.fwd 1).2, t.1, t.2)
  let ev : Blk × Blk × Blk × Blk → PTable → Prop := fun j σ =>
    DeadQueried g (stf σ) (Q σ) σ.fwd ∧ j ∈ TT σ ∧ σ (kk σ) j.1 = j.2.2.1 ∧
      σ (kk σ) j.2.1 = j.2.2.2
  have hmemT : ∀ σ j, j ∈ TT σ → j.1 = (dc g (stf σ) (Q σ) σ.fwd 0).2 ∧
      j.2.1 = (dc g (stf σ) (Q σ) σ.fwd 1).2 := by
    intro σ j hj
    obtain ⟨t, -, rfl⟩ := mem_image.1 hj
    exact ⟨rfl, rfl⟩
  refine (prEvent_mono _ _ (fun π => ∃ j, ev j π) ?_).trans
    ((prEvent_perm_two_le ev kk (deadXQ g stf Q) TT (fun j => j.1) (fun j => j.2.1)
      (fun j => j.2.2.1) (fun j => j.2.2.2) (q .h1) (qE + 4606) ?_ ?_ ?_ ?_).trans ?_)
  · intro π hD
    have hm := deadQueried_mem g (stf π) (Q π) hD
    refine ⟨((dc g (stf π) (Q π) π.fwd 0).2, (dc g (stf π) (Q π) π.fwd 1).2,
      π.fwd (dc g (stf π) (Q π) π.fwd 0), π.fwd (dc g (stf π) (Q π) π.fwd 1)), hD,
      mem_image.2 ⟨_, hm, rfl⟩, rfl, rfl⟩
  · rintro j σ ⟨hD, hj, h1, h2⟩
    obtain ⟨hj1, hj2⟩ := hmemT σ j hj
    obtain ⟨hi, -, -, hnc⟩ := deadAt_deadPt g (stf σ) (Q σ) hD.2
    refine ⟨hj, ?_, ?_, ?_, h1, h2⟩
    · rw [hj1, hj2, dc_snd, dc_snd]
      exact lp_ne _ _
    · rw [hj1, dc_snd]
      intro hx
      rcases (mem_deadXQ g stf Q).1 hx with hx | hx
      · rw [mem_keyIns, ← mem_cipherLog] at hx
        obtain ⟨e, he, he1⟩ := List.mem_map.1 hx
        exact hnc ⟨e, he, Or.inl he1⟩
      · obtain ⟨n, hn, c, -, he⟩ := mem_ggmPts hx
        exact lp_ne_gp _ 0 c hi hn he.symm
    · rw [hj2, dc_snd]
      intro hx
      rcases (mem_deadXQ g stf Q).1 hx with hx | hx
      · rw [mem_keyIns, ← mem_cipherLog] at hx
        obtain ⟨e, he, he1⟩ := List.mem_map.1 hx
        exact hnc ⟨e, he, Or.inr he1⟩
      · obtain ⟨n, hn, c, -, he⟩ := mem_ggmPts hx
        exact lp_ne_gp _ 1 c hi hn he.symm
  · rintro j σ ⟨hD, -⟩ π hoff hX
    obtain ⟨hk, h0, h1, hT⟩ := deadQueried_fam_inv g stf Q hQ hstf hD.2 hoff hX
    refine ⟨hk, ?_⟩
    simp only [TT, h0, h1, hT]
  · intro σ
    refine (card_deadXQ_le g stf Q σ).trans (add_le_add ((card_keyIns_le _ _).trans ?_) le_rfl)
    exact length_cipherLog_le _ (hqE σ) _
  · intro σ
    refine card_image_le.trans ((List.toFinset_card_le _).trans ?_)
    rw [List.length_map]
    exact length_kindIns_hashLog_le _ (hq σ) (join g σ.fwd) .h1
  · gcongr
    exact inv_two_le_pE _

end DeadG

/-! ## The failure events, adaptively, for a family -/

section Fails

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement)
  (Q : PTable → OracleComp specIC (ByteArray × (ι × β))) (hQ : RecFamily Q)

include hQ in
/-- **Post at `p`, adaptively, for a `RecFamily`**: `≤ q_E·4608·q₂₁·p²`. -/
theorem prEvent_jointF_postP_le (p : Params) (qE : ℕ)
    (hqE : ∀ π, IsQueryBoundP (Q π) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : ∀ π, IsKindQueryBoundIC (Q π) q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameA T stF (Q π) π.fwd)).run' ∅}[PostPOut p π.fwd r] ≤
      qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
  have h := prEvent_jointP_le_add (fun π => gameA T stF (Q π) π.fwd)
    (fun π r => PostPOut p π.fwd r) (fun _ _ => False)
    (qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2) fun g => by
      refine le_trans ?_ le_self_add
      simp only [PostPOut, evalWithAnswerFn_gameA, gameIC_aux]
      exact prEvent_fam_postP_le Q hQ p g qE hqE q hq
  rwa [prEvent_jointP_false, add_zero] at h

include hQ in
/-- **Binding, adaptively, for a `RecFamily`**: `≤ 2·q_E²·p²` plus an opened dead leaf. -/
theorem prEvent_jointF_bindFail_le (qE : ℕ)
    (hqE : ∀ π, IsQueryBoundP (Q π) (fun t => t.isRight = true) qE) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameA T stF (Q π) π.fwd)).run' ∅}[bindFailA stF π.fwd r] ≤
      2 * qE ^ 2 * pE qE ^ 2 +
        Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
          (gameA T stF (Q π) π.fwd)).run' ∅}[deadOpenA stF π.fwd r] := by
  refine prEvent_jointP_le_add (fun π => gameA T stF (Q π) π.fwd)
    (fun π r => bindFailA stF π.fwd r) (fun π r => deadOpenA stF π.fwd r) _ fun g => ?_
  have hpt : ∀ π : PTable, bindFailA stF π.fwd
      (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF (Q π) π.fwd)) →
      freshBadC (runH g (Q π)) ∅ π.fwd collBad ∨
        deadOpenA stF π.fwd
          (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF (Q π) π.fwd)) := by
    intro π hb
    simp only [bindFailA, deadOpenA, evalWithAnswerFn_gameA, stOut_gameIC] at hb ⊢
    exact bindFail_imp T _ (Q π) g π.fwd hb
  refine (prEvent_mono _ _ _ hpt).trans ((prEvent_or_le _ _ _).trans (add_le_add ?_ le_rfl))
  exact prEvent_fam_coll_le Q hQ g qE hqE

include hQ in
/-- **`ε_open`, adaptively, for a `RecFamily`** (statements with parameters `p`):
`≤ openHashEps q + q₁·p'²`. -/
theorem prEvent_jointF_deadOpen_le (p : Params) (hparams : ∀ s, (stF s).params = p) (qE : ℕ)
    (hqE : ∀ π, IsQueryBoundP (Q π) (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : ∀ π, IsKindQueryBoundIC (Q π) q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameA T stF (Q π) π.fwd)).run' ∅}[deadOpenA stF π.fwd r] ≤
      openHashEps q + q .h1 * pE (qE + 4607) ^ 2 := by
  let m : PTable → ProbComp (Out ((ι × β) × QueryLog specIC)) := fun π =>
    (simulateQ randomOracle (gameA T stF (Q π) π.fwd)).run' ∅
  let A : PTable → Out ((ι × β) × QueryLog specIC) → Prop := fun π r =>
    r.2.2.accept = true ∧
      @LeafUnqueried (icPrg π.fwd.cipher) _ (stF (stOut r)) (hashLog r.2.1.aux.2) r
  have hA : ∀ π, Pr{let r ← m π}[A π r] ≤ openHashEps q := fun π => by
    refine (prEvent_mono _ _ (fun r => (r.2.2.accept = true ∧
        @LeafUnqueried (icPrg π.fwd.cipher) _ (stF (stOut r)) (hashLog r.2.1.aux.2) r ∧
          ((.h23, zOut (stF (stOut r)) r) : Dom) ∈ hashLog r.2.1.aux.2) ∨
        (r.2.2.accept = true ∧ ((.h23, zOut (stF (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2))
        fun r h => (em (((.h23, zOut (stF (stOut r)) r) : Dom) ∈ hashLog r.2.1.aux.2)).elim
          (fun hz => Or.inl ⟨h.1, h.2, hz⟩) fun hz => Or.inr ⟨h.1, hz⟩).trans
      ((prEvent_or_le _ _ _).trans (add_le_add
        (prEvent_leafUnqueried_z_le_A T stF (Q π) p hparams q (hq π) π.fwd)
        (prEvent_zUnqueried_le_A T stF (Q π) π.fwd)))
  have h1 : Pr{let π ← $ᵗ PTable; let r ← m π}[A π r] ≤ openHashEps q :=
    prEvent_avgP_le m A _ hA
  have h2 : Pr{let π ← $ᵗ PTable; let r ← m π}[deadOpenA stF π.fwd r ∧ ¬A π r] ≤
      q .h1 * pE (qE + 4607) ^ 2 := by
    have h := prEvent_jointP_le_add (fun π => gameA T stF (Q π) π.fwd)
      (fun π r => deadOpenA stF π.fwd r ∧ ¬A π r) (fun _ _ => False)
      (q .h1 * pE (qE + 4607) ^ 2) fun g =>
        ((prEvent_mono _ _ _ fun π h => by
          simp only [A, deadOpenA, evalWithAnswerFn_gameA, stOut_gameIC] at h
          exact deadQueried_of_deadOpen T _ (Q π) g π.fwd h.1
            fun hL => h.2 ⟨h.1.1, hL⟩).trans
          (prEvent_fam_deadQueried_le g (fun π => stF (sA g (Q π) π.fwd)) Q hQ
            (fun σ π hO => by simp only [sA, hO]) qE hqE q hq)).trans le_self_add
    rwa [prEvent_jointP_false, add_zero] at h
  calc Pr{let π ← $ᵗ PTable; let r ← m π}[deadOpenA stF π.fwd r]
      ≤ Pr{let π ← $ᵗ PTable; let r ← m π}[A π r ∨ (deadOpenA stF π.fwd r ∧ ¬A π r)] :=
        prEvent_jointP_mono m _ _ fun π r h => (em (A π r)).elim Or.inl fun hA => Or.inr ⟨h, hA⟩
    _ ≤ _ := (prEvent_jointP_or_le m _ _).trans (add_le_add h1 h2)

end Fails

/-- **The per-output failure terms for families** (statements with parameters `p`): as
`sum_fail_leP_iv`, `≤ |J|·failEpsP q q_E`. -/
theorem sum_fail_le_fam {ι' ι β : Type} (T : CrtTables) (stF : ι → Statement) (p : Params)
    (hparams : ∀ s, (stF s).params = p) (Q : ι' → PTable → OracleComp specIC (ByteArray × (ι × β)))
    (J : Finset ι') (hQ : ∀ j ∈ J, RecFamily (Q j)) (qE : ℕ)
    (hqE : ∀ j ∈ J, ∀ π, IsQueryBoundP (Q j π) (fun t => t.isRight = true) qE)
    (q : Kind → ℕ) (hq : ∀ j ∈ J, ∀ π, IsKindQueryBoundIC (Q j π) q) :
    ∑ j ∈ J, (Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
        (gameA T stF (Q j π) π.fwd)).run' ∅}[bindFailA stF π.fwd r] +
      Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
        (gameA T stF (Q j π) π.fwd)).run' ∅}[deadOpenA stF π.fwd r] +
      Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
        (gameA T stF (Q j π) π.fwd)).run' ∅}[PostPOut p π.fwd r]) ≤
      J.card * failEpsP q qE := by
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun j hj => ?_
  have hdo := prEvent_jointF_deadOpen_le T stF (Q j) (hQ j hj) p hparams qE (hqE j hj) q (hq j hj)
  unfold failEpsP
  gcongr
  · exact (prEvent_jointF_bindFail_le T stF (Q j) (hQ j hj) qE (hqE j hj)).trans
      (add_le_add le_rfl hdo)
  · exact prEvent_jointF_postP_le T stF (Q j) (hQ j hj) p qE (hqE j hj) q (hq j hj)

end VoleMole.ROM.IC
