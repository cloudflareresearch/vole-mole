import VoleMole.ROM.OneMoreShiftSim
import VoleMole.ROM.PermFamily

/-!
# PomFRIT's one-more game with AES as random permutations, with inverse queries

`lean/docs/security/pomfrit.md` §6.4, `lean/docs/probabilistic-plan.md` §2o. The one-more game of
`ROM/OneMorePomfrit.lean` reads the cipher as a uniform table `E` (the PRF view) and the forger
makes forward queries only. Here the cipher is a uniform permutation table `π` (`PTable`) and the
forger makes **forward and inverse** cipher queries.

* **The forger** (`ForgerP`): its oracles `specUP` are those of `specU` with the cipher queries of
  the permutation model (`PCell`: `(true, (k, z)) ↦ π_k(z)`, `(false, (k, y)) ↦ π_k⁻¹(y)`).
* **The reduction's normalization** (`normU p π`, `ForgerP.toIC lr π`): every inverse query
  `(k, y)` becomes the forward query at `(k, π_k⁻¹(y))` (its record; the forger gets `π_k⁻¹(y)`),
  and every `H₂¹` query `x` is preceded by the reduction's own query `H₄(iv_pre ‖ μ ‖ 4)` parsed
  from `x` (N1, as `normP`). The forger's view is the permutation oracle (`eval_normU`); the extra
  queries are hidden, as the reduction's other own queries (`auxSpec`).
* **The game** (`gameP`): `game` with the cipher table `π.fwd` and the forger at `π` normalized:
  the forger runs against `π` (forward and inverse), the reduction, verifier and extractor read
  `π.fwd`, the extractor reads the records.
* **Budgets** (`ForgerBoundP`, `ForgerBoundP.toIC`): a forger with budget `qA`, `nA`, `q_E`
  (forward and inverse), `Q_T` normalizes to one with budget `addH4 qA`, `nA + qA₂₁`, `q_E`, `Q_T`.
* **The derived provers per table are a `RecFamily`** (`recFamily_proverP`): they depend on `π`
  only through the records (the forger's inverse queries recorded, the rest forward), so the
  failure bounds of `ROM/PermFamily.lean` apply to them.
* **N1** (`ivBefore_proverP`): in the derived prover's log every `H₂¹` input is preceded by its
  `iv`'s `H₄` query (the forger's by the normalization, the verifications' by the verifier's own
  `iv` query in `chal1Pre`), so outside the point-tied Post `PostPOut` the committed keys are found
  before the chain (`keysPre_proverP`).

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.ZK.Sim VoleMole.Verifier.Bridge

/-! ## N1 on logs -/

section N1

lemma ivBefore_nil (p : Params) : IvBefore p [] := fun pre post x u h => by simp at h

/-- **N1 is closed under concatenation.** -/
lemma ivBefore_append {p : Params} {A B : QueryLog specIC} (hA : IvBefore p A)
    (hB : IvBefore p B) : IvBefore p (A ++ B) := by
  intro pre post x u h
  rcases List.append_eq_append_iff.1 h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · have := hB a' post x u h2
    rw [h1, List.map_append]
    exact List.mem_append_right _ this
  · rcases c' with _ | ⟨e', c''⟩
    · rw [List.append_nil] at h1
      rw [List.nil_append] at h2
      have := hB [] post x u (by rw [List.nil_append]; exact h2.symm)
      simp at this
    · rw [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact hA pre c'' x u h1

/-- **A log without `H₂¹` entries has N1.** -/
lemma ivBefore_of_noH21 {p : Params} {L : QueryLog specIC}
    (h : ∀ e ∈ L, ∀ x, e.1 ≠ .inl (.h21, x)) : IvBefore p L := by
  intro pre post x u hL
  exact absurd rfl (h _ (by rw [hL]; exact List.mem_append_right _ List.mem_cons_self) x)

/-- **A log whose only `H₂¹` entry is the last, with its `iv`'s `H₄` query before it.** -/
lemma ivBefore_append_h21 {p : Params} {L : QueryLog specIC} {x : ByteArray} {u : Ans (.h21, x)}
    (h : ∀ e ∈ L, ∀ x', e.1 ≠ .inl (.h21, x'))
    (h4 : (.inl (.h4, ivIn p x) : DomIC) ∈ L.map Sigma.fst) :
    IvBefore p (L ++ [⟨.inl (.h21, x), u⟩]) := by
  intro pre post x' u' hL
  rcases List.eq_nil_or_concat post with rfl | ⟨post', y, rfl⟩
  · obtain ⟨h1, h2⟩ := List.append_inj' hL rfl
    rw [← h1]
    rw [List.cons.injEq] at h2
    have := congrArg Sigma.fst h2.1
    simp only [Sum.inl.injEq, Prod.mk.injEq, true_and] at this
    subst this
    exact h4
  · have hL' : L ++ [⟨.inl (.h21, x), u⟩] =
        (pre ++ (⟨.inl (.h21, x'), u'⟩ : (t : DomIC) × AnsIC t) :: post') ++ [y] := by
      rw [hL]; simp
    obtain ⟨h1, -⟩ := List.append_inj' hL' rfl
    exact absurd rfl (h _ (by rw [h1]; exact List.mem_append_right _ List.mem_cons_self) x')

/-- **N1 for a forward prover at every table** (hash table `g`, cipher table `E`). -/
def N1C (p : Params) {α : Type} (X : OracleComp specIC α) : Prop :=
  ∀ g E, IvBefore p (tableQueryLog X (join g E))

lemma n1c_pure (p : Params) {α : Type} (a : α) : N1C p (pure a : OracleComp specIC α) :=
  fun g E => by rw [tableQueryLog_pure]; exact ivBefore_nil p

lemma N1C.bind {p : Params} {α β : Type} {X : OracleComp specIC α}
    {K : α → OracleComp specIC β} (hX : N1C p X) (hK : ∀ a, N1C p (K a)) : N1C p (X >>= K) :=
  fun g E => by rw [tableQueryLog_bind]; exact ivBefore_append (hX g E) (hK _ g E)

lemma N1C.map {p : Params} {α β : Type} {X : OracleComp specIC α} (hX : N1C p X) (f : α → β) :
    N1C p (f <$> X) := by
  rw [map_eq_bind_pure_comp]; exact hX.bind fun _ => n1c_pure p _

/-- **A forward prover without `H₂¹` queries has N1.** -/
lemma n1c_of_kind {p : Params} {α : Type} {X : OracleComp specIC α} {q : Kind → ℕ}
    (hq : IsKindQueryBoundIC X q) (h0 : q .h21 = 0) : N1C p X := by
  intro g E
  refine ivBefore_of_noH21 fun e he x hx => ?_
  have hl := length_kindIns_hashLog_le X hq (join g E) .h21
  rw [h0, Nat.le_zero, List.length_eq_zero_iff] at hl
  have hm : ((.h21, x) : Dom) ∈ hashLog (tableQueryLog X (join g E)) :=
    mem_hashLog.2 (List.mem_map.2 ⟨e, he, hx⟩)
  have := mem_kindIns hm
  rw [hl] at this
  simp at this

end N1

/-! ## N1 in the verifier's steps up to `chal1` -/

section Chal1

/-- **The verifier's `chal1` query is preceded by its `iv` query** (the statement's parameters `p`):
`chal1Pre`'s log has N1 at `p`. -/
theorem ivBefore_chal1Pre [HasPrg] (st : Statement) (proof : ByteArray) (g : Table) :
    IvBefore st.params ((tableQueryLog (chal1Pre st proof) g).map
      fun e => (⟨.inl e.1, e.2⟩ : (t : DomIC) × AnsIC t)) := by
  have hmuK : ∀ e ∈ tableQueryLog (mu1Q st) g, e.1.1 = .mu ∨ e.1.1 = .muDelayed := by
    unfold mu1Q; split <;> simp [tableQueryLog_hashQ]
  have hHs : ∀ k w, ((Hashes.ofTable g).hash k w).size = k.outLen := fun k w => by simp
  unfold chal1Pre
  dsimp only
  by_cases hf : ({ params := st.params, bytes := proof } : Proof).checkFormat = true
  · simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false, tableQueryLog_bind,
      evalWithAnswerFn_mu1Q]
    set pf : Proof := { params := st.params, bytes := proof }
    set mu1 := st.mu1 (Hashes.ofTable g)
    have hmu : mu1.size = 32 := size_mu1 _ hHs st
    simp only [tableQueryLog_hashQ]
    split
    · simp only [tableQueryLog_pure, List.append_nil, List.map_append]
      refine ivBefore_of_noH21 fun e he x hx => ?_
      rw [List.mem_append, List.mem_map, List.mem_map] at he
      rcases he with ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
      · have := hmuK e' he'
        simp only [Sum.inl.injEq] at hx
        rw [hx] at this; simp at this
      · simp only [List.mem_singleton] at he'
        subst he'
        simp at hx
    · rename_i leaves _
      simp only [tableQueryLog_bind, tableQueryLog_mapM_hashQ, tableQueryLog_hashQ,
        tableQueryLog_pure, List.append_nil, evalWithAnswerFn_mapM_hashQ, evalWithAnswerFn_hashQ]
      set com := (Hashes.ofTable g).hash .h1 (BAVC.comInput ((BAVC.leafHashInputs leaves.coms).map
        ((Hashes.ofTable g).hash .h1)))
      have hcom : com.size = 32 := hHs .h1 _
      simp only [List.map_append, List.map_cons, List.map_nil, ← List.append_assoc]
      refine ivBefore_append_h21 (fun e he x hx => ?_) ?_
      · simp only [List.mem_append, List.mem_map, List.mem_singleton] at he
        rcases he with ((⟨e', he', rfl⟩ | rfl) | ⟨e', he', rfl⟩) | rfl
        · have := hmuK e' he'
          simp only [Sum.inl.injEq] at hx
          rw [hx] at this; simp at this
        · simp at hx
        · obtain ⟨a, -, rfl⟩ := he'
          simp at hx
        · simp at hx
      · have hx : ivIn st.params (chal1Input pf mu1 com st.binder1) =
            (pf.ivPre ++ mu1).push 4 := by
          unfold ivIn
          rw [show st.params = pf.params from rfl, xIvPre_chal1Input hf hmu hcom,
            extract_mu_chal1Input hmu]
        rw [hx]
        simp
  · simp only [Bool.not_eq_true] at hf
    simp only [hf, Bool.not_false, ite_true, tableQueryLog_pure, List.map_nil]
    exact ivBefore_nil _

end Chal1

/-! ## The forger of the permutation model and its normalization -/

section Forger

/-- The answers of the forger's oracles in the permutation model. -/
abbrev AnsUP : DomP ⊕ (ByteArray ⊕ TG) → Type :=
  Sum.elim AnsP (Sum.elim (fun _ => TG) fun _ => SIss)

/-- **The forger's oracles in the permutation model**: the hashes, the cipher with forward and
inverse queries (`PCell`), `hash_to_target` and the Issuer. -/
abbrev specUP : OracleSpec (DomP ⊕ (ByteArray ⊕ TG)) := OracleSpec.ofFn AnsUP

/-- **A one-more forger of the permutation model.** -/
abbrev ForgerP := UovPk → OracleComp specUP (List (ByteArray × ByteArray))

/-- **The reduction's normalization of one query** at the table `π`: an inverse query `(k, y)` is
the forward query at `(k, π_k⁻¹(y))` (answered `π_k⁻¹(y)`), an `H₂¹` query `x` is preceded by the
reduction's `H₄` query of `x`'s `iv` (`ivIn p x`), the rest are forwarded. -/
def normUImpl (p : Params) (π : PTable) : QueryImpl specUP (OracleComp specU)
  | .inl (.inl d) => if d.1 = .h21 then
      liftM (specU.query (.inl (.inl (.h4, ivIn p d.2)))) >>= fun _ =>
        liftM (specU.query (.inl (.inl d)))
    else liftM (specU.query (.inl (.inl d)))
  | .inl (.inr (true, c)) => liftM (specU.query (.inl (.inr c)))
  | .inl (.inr (false, c)) =>
      liftM (specU.query (.inl (.inr (c.1, (π c.1).symm c.2)))) >>= fun _ =>
        pure ((π c.1).symm c.2)
  | .inr (.inl x) => liftM (specU.query (.inr (.inl x)))
  | .inr (.inr t) => liftM (specU.query (.inr (.inr t)))

/-- **The normalized forger computation** at the table `π`. -/
def normU (p : Params) (π : PTable) {α : Type} (F : OracleComp specUP α) : OracleComp specU α :=
  simulateQ (normUImpl p π) F

/-- **The forger at the table `π`, normalized**: a forger of the PRF view. -/
def ForgerP.toIC (lr : Bool) (π : PTable) (A : ForgerP) : Forger :=
  fun pk => normU (pomfritParams lr) π (A pk)

end Forger

/-! ## The derived provers per table are a `RecFamily` with N1 -/

section Family

variable (lr : Bool) (hint : QueryLog specIC → ByteArray → TG) (pre : TG → SIss) (p : Params)

lemma wrap_normU_bind {α : Type} (π : PTable) (t : DomP ⊕ (ByteArray ⊕ TG))
    (k : AnsUP t → OracleComp specUP α) (s : QueryLog specIC × HTS × Gh) :
    (simulateQ (wrapIC lr hint pre) (normU p π (liftM (specUP.query t) >>= k))).run s =
      (simulateQ (wrapIC lr hint pre) (normUImpl p π t)).run s >>= fun r =>
        (simulateQ (wrapIC lr hint pre) (normU p π (k r.1))).run r.2 := by
  simp only [normU, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

lemma wrap_query (t : DomIC) (s : QueryLog specIC × HTS × Gh) :
    (simulateQ (wrapIC lr hint pre) (liftM (specU.query (.inl t)))).run s =
      (fun u => (u, (s.1 ++ [⟨t, u⟩], s.2))) <$>
        (liftM (specIC.query t) : OracleComp specIC (AnsIC t)) := by
  rw [simulateQ_spec_query]; rfl

lemma log_wrap_query (t : DomIC) (s : QueryLog specIC × HTS × Gh) (f : (t : DomIC) → AnsIC t) :
    tableQueryLog ((simulateQ (wrapIC lr hint pre) (liftM (specU.query (.inl t)))).run s) f =
      [⟨t, f t⟩] := by
  rw [simulateQ_spec_query]
  exact (tableQueryLog_map' _ _ f).trans (tableQueryLog_query t f)

lemma eval_wrap_query (t : DomIC) (s : QueryLog specIC × HTS × Gh) (f : (t : DomIC) → AnsIC t) :
    evalWithAnswerFn (QueryImpl.ofFn f)
      ((simulateQ (wrapIC lr hint pre) (liftM (specU.query (.inl t)))).run s) =
      (f t, (s.1 ++ [⟨t, f t⟩], s.2)) := by
  rw [simulateQ_spec_query]
  exact (evalWithAnswerFn_map _ _ _).trans rfl

lemma wrap_pure {β : Type} (b : β) (s : QueryLog specIC × HTS × Gh) :
    (simulateQ (wrapIC lr hint pre) (pure b : OracleComp specU β)).run s = pure (b, s) := by
  simp

/-- The constant table. -/
def π0 : PTable := fun _ => Equiv.refl _

/-- **The forger's part of the derived prover is a `RecFamily`.** -/
theorem recFamily_wrap {α : Type} (F : OracleComp specUP α) :
    ∀ s, RecFamily fun π => (simulateQ (wrapIC lr hint pre) (normU p π F)).run s := by
  induction F using OracleComp.inductionOn with
  | pure a =>
    intro s
    simp only [normU, simulateQ_pure, StateT.run_pure]
    exact recFamily_pure _
  | query_bind t k ih =>
    intro s
    simp only [wrap_normU_bind]
    refine RecFamily.bind ?_ fun r => ih r.1 r.2
    rcases t with (d | ⟨b, c⟩) | (x | t)
    · exact recFamily_const
        ((simulateQ (wrapIC lr hint pre) (normUImpl p π0 (.inl (.inl d)))).run s)
    · cases b
      · refine (recFamily_inv c.1 c.2
          (fun x v => (x, (s.1 ++ [⟨.inr (c.1, x), v⟩], s.2)))).of_eq fun π g => ?_
        have e : (simulateQ (wrapIC lr hint pre) (normUImpl p π (.inl (.inr (false, c))))).run s =
            (simulateQ (wrapIC lr hint pre)
              (liftM (specU.query (.inl (.inr (c.1, (π c.1).symm c.2)))))).run s >>= fun r =>
                pure ((π c.1).symm c.2, r.2) := by
          simp only [normUImpl, simulateQ_bind, StateT.run_bind]
          refine bind_congr fun r => ?_
          exact wrap_pure lr hint pre _ _
        constructor
        · change tableQueryLog ((simulateQ (wrapIC lr hint pre)
            (normUImpl p π (.inl (.inr (false, c))))).run s) (join g π.fwd) = _
          rw [e]
          refine (tableQueryLog_bind _ _ _).trans ?_
          rw [log_wrap_query, jQ_invQ]
          exact (congrArg (_ ++ ·) (tableQueryLog_pure _ _)).trans (List.append_nil _)
        · change evalWithAnswerFn _ ((simulateQ (wrapIC lr hint pre)
            (normUImpl p π (.inl (.inr (false, c))))).run s) = _
          rw [e]
          refine (evalWithAnswerFn_bind _ _ _).trans ?_
          rw [eval_wrap_query, eval_invQ]
          exact (evalWithAnswerFn_pure _ _).trans rfl
      · exact recFamily_const
          ((simulateQ (wrapIC lr hint pre) (normUImpl p π0 (.inl (.inr (true, c))))).run s)
    · exact recFamily_const
        ((simulateQ (wrapIC lr hint pre) (normUImpl p π0 (.inr (.inl x)))).run s)
    · exact recFamily_const
        ((simulateQ (wrapIC lr hint pre) (normUImpl p π0 (.inr (.inr t)))).run s)

/-- **The forger's part of the derived prover has N1** (at the normalization's parameters). -/
theorem n1c_wrap (π : PTable) {α : Type} (F : OracleComp specUP α) :
    ∀ s, N1C p ((simulateQ (wrapIC lr hint pre) (normU p π F)).run s) := by
  induction F using OracleComp.inductionOn with
  | pure a =>
    intro s
    simp only [normU, simulateQ_pure, StateT.run_pure]
    exact n1c_pure p _
  | query_bind t k ih =>
    intro s
    rw [wrap_normU_bind]
    refine N1C.bind ?_ fun r => ih r.1 r.2
    rcases t with (d | ⟨b, c⟩) | (x | t)
    · by_cases hd : d.1 = .h21
      · intro g E
        obtain ⟨kd, xd⟩ := d
        simp only at hd
        subst hd
        simp only [normUImpl, ite_true, simulateQ_bind, StateT.run_bind]
        rw [tableQueryLog_bind, log_wrap_query]
        convert ivBefore_append_h21 (p := p)
          (L := [⟨.inl (.h4, ivIn p xd), join g E (.inl (.h4, ivIn p xd))⟩]) (x := xd)
          (u := join g E (.inl (.h21, xd))) ?_ (by simp) using 2
        · exact log_wrap_query lr hint pre (.inl (.h21, xd)) _ _
        · intro e he x hx
          simp only [List.mem_singleton] at he
          subst he
          simp at hx
      · have : (simulateQ (wrapIC lr hint pre) (normUImpl p π (.inl (.inl d)))).run s =
            (fun u => (u, (s.1 ++ [⟨.inl d, u⟩], s.2))) <$>
              (liftM (specIC.query (.inl d)) : OracleComp specIC (AnsIC (.inl d))) := by
          simp only [normUImpl, hd, ite_false]
          rfl
        rw [this]
        exact n1c_of_kind (isKindQueryBoundIC_map_hash d _)
          (by simp [Ne.symm hd])
    · cases b
      · intro g E
        simp only [normUImpl, simulateQ_bind, StateT.run_bind]
        rw [tableQueryLog_bind, log_wrap_query]
        convert ivBefore_of_noH21 (p := p)
          (L := [⟨.inr (c.1, (π c.1).symm c.2), join g E (.inr (c.1, (π c.1).symm c.2))⟩] ++ [])
          (by simp) using 2
        exact (congrArg (tableQueryLog · (join g E)) (wrap_pure lr hint pre _ _)).trans
          (tableQueryLog_pure _ _)
      · have : (simulateQ (wrapIC lr hint pre) (normUImpl p π (.inl (.inr (true, c))))).run s =
            (fun u => (u, (s.1 ++ [⟨.inr c, u⟩], s.2))) <$>
              (liftM (specIC.query (.inr c)) : OracleComp specIC Blk) := by
          simp only [normUImpl]
          rfl
        rw [this]
        exact n1c_of_kind (isKindQueryBoundIC_map_cipher c _) rfl
    · show N1C p ((simulateQ (wrapIC lr hint pre) (liftM (specU.query (.inr (.inl x))))).run s)
      rw [simulateQ_spec_query]
      exact N1C.bind (n1c_of_kind (isKindQueryBoundIC_toHIC_auxSpec lr s.1 x) rfl)
        fun _ => n1c_pure p _
    · show N1C p ((simulateQ (wrapIC lr hint pre) (liftM (specU.query (.inr (.inr t))))).run s)
      rw [simulateQ_spec_query]
      exact n1c_pure p _

end Family

/-! ## The derived provers of the normalized forger -/

section Derived

theorem n1c_chal1PreIC (st : Statement) (proof : ByteArray) :
    N1C st.params (chal1PreIC st proof) := by
  unfold chal1PreIC
  refine N1C.bind (n1c_of_kind (isKindQueryBoundIC_liftIC (isKindQueryBound_ivQ st proof))
    (by simp [extractorQueries])) fun iv => ?_
  refine N1C.bind (n1c_of_kind (isKindQueryBoundIC_treeQ _ _ _) rfl) fun A => ?_
  refine N1C.bind (n1c_of_kind (isKindQueryBoundIC_cellsQ _ _ _) rfl) fun M => ?_
  intro g E
  rw [← toHIC_eq_liftIC, log_toHIC]
  exact @ivBefore_chal1Pre (icPrg (fillC M)) st proof g

variable (lr : Bool) (pk : UovPk)

theorem n1c_verPreIC (L : QueryLog specIC) (m sg : ByteArray) (s : HTS × Gh) :
    N1C (pomfritParams lr) (verPreIC lr pk L m sg s) := by
  unfold verPreIC
  split
  · exact n1c_pure _ _
  · refine N1C.bind (n1c_chal1PreIC (st0 lr pk sg) _) fun oc1 => ?_
    cases oc1 with
    | none => exact n1c_pure _ _
    | some c1 =>
      exact N1C.bind (n1c_of_kind (isKindQueryBoundIC_toHIC_auxSpec lr _ _) rfl)
        fun _ => n1c_pure _ _

theorem n1c_verPreAll (L : QueryLog specIC) :
    ∀ (ms : List (ByteArray × ByteArray)) (s : HTS × Gh),
      N1C (pomfritParams lr) (verPreAll lr pk L ms s)
  | [], _ => n1c_pure _ _
  | (m, sg) :: rest, s => (n1c_verPreIC lr pk L m sg s).bind fun s' => n1c_verPreAll L rest s'

theorem n1c_verLastIC (L : QueryLog specIC) (ms : ByteArray × ByteArray) (s : HTS × Gh) :
    N1C (pomfritParams lr) (verLastIC lr pk L ms s) := by
  unfold verLastIC
  refine N1C.bind (n1c_chal1PreIC (st0 lr pk ms.2) _) fun oc1 => ?_
  cases oc1 with
  | none => exact n1c_pure _ _
  | some c1 =>
    exact N1C.bind (n1c_of_kind (isKindQueryBoundIC_toHIC_auxSpec lr _ _) rfl)
      fun _ => n1c_pure _ _

theorem n1c_contP (i : ℕ) (r : List (ByteArray × ByteArray) × QueryLog specIC × HTS × Gh) :
    N1C (pomfritParams lr) (contP lr pk i r) :=
  (n1c_verPreAll lr pk _ _ _).bind fun s => n1c_verLastIC lr pk _ _ s

variable (pre : TG → SIss) (A : ForgerP) (Lst : List TG)

/-- **N1 for the derived provers of the normalized forger**: every `H₂¹` input of the log is
preceded by its `iv`'s `H₄` query. -/
theorem n1c_proverP (π : PTable) (i : ℕ) :
    N1C (pomfritParams lr) (proverP lr pk pre (A.toIC lr π) Lst i) := by
  rw [proverP_eq]
  exact (n1c_wrap lr hintVoid pre (pomfritParams lr) π (A pk) _).bind fun r => n1c_contP lr pk i r

/-- **The derived provers of the normalized forger are a `RecFamily`.** -/
theorem recFamily_proverP (i : ℕ) :
    RecFamily fun π => proverP lr pk pre (A.toIC lr π) Lst i := by
  simp only [proverP_eq]
  exact (recFamily_wrap lr hintVoid pre (pomfritParams lr) (A pk) _).bind fun r =>
    recFamily_const (contP lr pk i r)

/-- **Outside the point-tied Post, `KeysPre`** for the derived provers of the normalized forger. -/
theorem keysPre_proverP (π : PTable) (i : ℕ) (s : TG × ByteArray × ByteArray) (g : Table)
    (h : ¬PostPOut (pomfritParams lr) π.fwd (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameIC CrtGen.tables (stG lr pk s) (proverP lr pk pre (A.toIC lr π) Lst i) π.fwd))) :
    KeysPre (stG lr pk s) π.fwd (jOf g (proverP lr pk pre (A.toIC lr π) Lst i) π.fwd)
      (gLog CrtGen.tables (stG lr pk s) (proverP lr pk pre (A.toIC lr π) Lst i) π.fwd g) g := by
  refine keysPre_of_not_postP_Q CrtGen.tables (stG lr pk s) _ (pomfritParams lr) rfl π.fwd g
    (n1c_proverP lr pk pre A Lst π i g π.fwd) ?_
  unfold PostPOut at h
  rwa [gameIC_aux] at h

end Derived

/-! ## Budgets -/

section Budget

variable {α : Type}

/-- A hash query of the forger of the permutation model. -/
def isHashUP : DomP ⊕ (ByteArray ⊕ TG) → Bool
  | .inl (.inl _) => true
  | _ => false

/-- A cipher query (forward or inverse) of the forger of the permutation model. -/
def isCipherUP : DomP ⊕ (ByteArray ⊕ TG) → Bool
  | .inl (.inr _) => true
  | _ => false

/-- A `hash_to_target` query of the forger of the permutation model. -/
def isHTP : DomP ⊕ (ByteArray ⊕ TG) → Bool
  | .inr (.inl _) => true
  | _ => false

/-- **The forger's hash queries per kind** are within `q` (permutation model). -/
def IsKindQueryBoundUP (oa : OracleComp specUP α) (q : Kind → ℕ) : Prop :=
  IsQueryBound oa q (fun t b => match t with | .inl (.inl d) => 0 < b d.1 | _ => True)
    (fun t b => match t with | .inl (.inl d) => Function.update b d.1 (b d.1 - 1) | _ => b)

/-- **The forger's budget in the permutation model**: at most `qA k` hash queries of kind `k`,
`nA` hash queries in all, `qE` cipher queries (forward and inverse together) and `Q_T`
`hash_to_target` queries. -/
structure ForgerBoundP (A : ForgerP) (qA : Kind → ℕ) (nA qE QT : ℕ) : Prop where
  kinds : ∀ pk, IsKindQueryBoundUP (A pk) qA
  hashes : ∀ pk, IsQueryBoundP (A pk) (fun t => isHashUP t = true) nA
  cipher : ∀ pk, IsQueryBoundP (A pk) (fun t => isCipherUP t = true) qE
  ht : ∀ pk, IsQueryBoundP (A pk) (fun t => isHTP t = true) QT

variable (p : Params) (π : PTable)

lemma normU_query_bind (t : DomP ⊕ (ByteArray ⊕ TG)) (k : AnsUP t → OracleComp specUP α) :
    normU p π (liftM (specUP.query t) >>= k) = normUImpl p π t >>= fun u => normU p π (k u) := by
  simp only [normU, simulateQ_bind, simulateQ_spec_query]

theorem kinds_normU {F : OracleComp specUP α} {q : Kind → ℕ} (hq : IsKindQueryBoundUP F q) :
    IsKindQueryBoundU (normU p π F) (addH4 q) := by
  induction F using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [IsKindQueryBoundUP, isQueryBound_query_bind_iff] at hq
    obtain ⟨h0, hk⟩ := hq
    rw [normU_query_bind]
    rcases t with (⟨kd, xd⟩ | ⟨b, c⟩) | (x | t)
    · simp only at h0 hk
      by_cases hd : kd = .h21
      · subst hd
        simp only [normUImpl, ite_true, bind_assoc]
        refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ?_
        refine ⟨?_, fun _ => ?_⟩
        · show 0 < addH4 q .h4
          simp only [addH4, Function.update_self]
          omega
        refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨?_, fun u => ?_⟩
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
        show IsKindQueryBoundU (normU p π (k u))
          (Function.update (Function.update (addH4 q) .h4 (addH4 q .h4 - 1)) .h21
            (Function.update (addH4 q) .h4 (addH4 q .h4 - 1) .h21 - 1))
        rw [hb]
        exact ih u (hk u)
      · simp only [normUImpl, hd, ite_false]
        refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ?_
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
        show IsKindQueryBoundU (normU p π (k u)) (Function.update (addH4 q) kd (addH4 q kd - 1))
        rw [hb]
        exact ih u (hk u)
    · cases b
      · simp only [normUImpl, bind_assoc]
        refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ?_
        exact ⟨trivial, fun _ => ih _ (hk _)⟩
      · simp only [normUImpl]
        refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ?_
        exact ⟨trivial, fun u => ih u (hk u)⟩
    · simp only [normUImpl]
      refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ?_
      exact ⟨trivial, fun u => ih u (hk u)⟩
    · simp only [normUImpl]
      refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ?_
      exact ⟨trivial, fun u => ih u (hk u)⟩

theorem hashes_normU {F : OracleComp specUP α} {n : ℕ} {q : Kind → ℕ}
    (hn : IsQueryBoundP F (fun t => isHashUP t = true) n) (hq : IsKindQueryBoundUP F q) :
    IsQueryBoundP (normU p π F) (fun t => isHashU t = true) (n + q .h21) := by
  induction F using OracleComp.inductionOn generalizing n q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [IsKindQueryBoundUP, isQueryBound_query_bind_iff] at hq
    obtain ⟨h0, hk⟩ := hq
    rw [normU_query_bind]
    rcases t with (d | ⟨b, c⟩) | (x | t)
    · simp only [isHashUP, not_true_eq_false, false_or, ite_true] at hn
      obtain ⟨hn0, hn⟩ := hn
      simp only at h0 hk
      by_cases hd : d.1 = .h21
      · simp only [normUImpl, hd, ite_true, bind_assoc]
        rw [hd] at h0
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
        refine ⟨by omega, fun _ => ?_⟩
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2
          ⟨Or.inr (by simp only [isHashU, ite_true]; omega), fun u => ?_⟩
        have := ih u (hn u) (hk u)
        rw [hd, Function.update_self] at this
        refine this.mono ?_
        simp only [isHashU, ite_true]
        omega
      · simp only [normUImpl, hd, ite_false]
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
        simp only [isHashU, not_true_eq_false, false_or, ite_true]
        refine ⟨by omega, fun u => ?_⟩
        have := ih u (hn u) (hk u)
        rw [Function.update_of_ne (Ne.symm hd)] at this
        refine this.mono ?_
        omega
    · simp only [isHashUP, Bool.false_eq_true, ite_false] at hn
      cases b
      · simp only [normUImpl, bind_assoc]
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
        simp only [isHashU, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
        exact fun _ => ih _ (hn.2 _) (hk _)
      · simp only [normUImpl]
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
        simp only [isHashU, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
        exact fun u => ih u (hn.2 u) (hk u)
    · simp only [isHashUP, Bool.false_eq_true, ite_false] at hn
      simp only [normUImpl]
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
      simp only [isHashU, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
      exact fun u => ih u (hn.2 u) (hk u)
    · simp only [isHashUP, Bool.false_eq_true, ite_false] at hn
      simp only [normUImpl]
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
      simp only [isHashU, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
      exact fun u => ih u (hn.2 u) (hk u)

theorem cipher_normU {F : OracleComp specUP α} {n : ℕ}
    (hn : IsQueryBoundP F (fun t => isCipherUP t = true) n) :
    IsQueryBoundP (normU p π F) (fun t => isCipherU t = true) n := by
  induction F using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [normU_query_bind]
    rcases t with (d | ⟨b, c⟩) | (x | t)
    · simp only [isCipherUP, Bool.false_eq_true, ite_false] at hn
      by_cases hd : d.1 = .h21
      · simp only [normUImpl, hd, ite_true, bind_assoc]
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
        simp only [isCipherU, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
        intro _
        exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp),
          fun u => ih u (hn.2 u)⟩
      · simp only [normUImpl, hd, ite_false]
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
        simp only [isCipherU, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
        exact fun u => ih u (hn.2 u)
    · simp only [isCipherUP, not_true_eq_false, false_or, ite_true] at hn
      cases b
      · simp only [normUImpl, bind_assoc]
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
        simp only [isCipherU, not_true_eq_false, false_or, ite_true]
        exact ⟨hn.1, fun _ => ih _ (hn.2 _)⟩
      · simp only [normUImpl]
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
        simp only [isCipherU, not_true_eq_false, false_or, ite_true]
        exact ⟨hn.1, fun u => ih u (hn.2 u)⟩
    · simp only [isCipherUP, Bool.false_eq_true, ite_false] at hn
      simp only [normUImpl]
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
      simp only [isCipherU, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
      exact fun u => ih u (hn.2 u)
    · simp only [isCipherUP, Bool.false_eq_true, ite_false] at hn
      simp only [normUImpl]
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
      simp only [isCipherU, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
      exact fun u => ih u (hn.2 u)

theorem ht_normU {F : OracleComp specUP α} {n : ℕ}
    (hn : IsQueryBoundP F (fun t => isHTP t = true) n) :
    IsQueryBoundP (normU p π F) (fun t => isHT t = true) n := by
  induction F using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [normU_query_bind]
    rcases t with (d | ⟨b, c⟩) | (x | t)
    · simp only [isHTP, Bool.false_eq_true, ite_false] at hn
      by_cases hd : d.1 = .h21
      · simp only [normUImpl, hd, ite_true, bind_assoc]
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
        simp only [isHT, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
        intro _
        exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp),
          fun u => ih u (hn.2 u)⟩
      · simp only [normUImpl, hd, ite_false]
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
        simp only [isHT, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
        exact fun u => ih u (hn.2 u)
    · simp only [isHTP, Bool.false_eq_true, ite_false] at hn
      cases b
      · simp only [normUImpl, bind_assoc]
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
        simp only [isHT, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
        exact fun _ => ih _ (hn.2 _)
      · simp only [normUImpl]
        refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
        simp only [isHT, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
        exact fun u => ih u (hn.2 u)
    · simp only [isHTP, not_true_eq_false, false_or, ite_true] at hn
      simp only [normUImpl]
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
      simp only [isHT, not_true_eq_false, false_or, ite_true]
      exact ⟨hn.1, fun u => ih u (hn.2 u)⟩
    · simp only [isHTP, Bool.false_eq_true, ite_false] at hn
      simp only [normUImpl]
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ?_
      simp only [isHT, Bool.false_eq_true, not_false_eq_true, true_or, ite_false, true_and]
      exact fun u => ih u (hn.2 u)

/-- **The normalized forger's budget**: the forger's, with one more `H₄` query per `H₂¹` query
(`q_E` counts forward and inverse queries; each becomes one forward query). -/
theorem ForgerBoundP.toIC {A : ForgerP} {qA : Kind → ℕ} {nA qE QT : ℕ}
    (hA : ForgerBoundP A qA nA qE QT) (lr : Bool) (π : PTable) :
    ForgerBound (A.toIC lr π) (addH4 qA) (nA + qA .h21) qE QT where
  kinds pk := kinds_normU _ π (hA.kinds pk)
  hashes pk := hashes_normU _ π (hA.hashes pk) (hA.kinds pk)
  cipher pk := cipher_normU _ π (hA.cipher pk)
  ht pk := ht_normU _ π (hA.ht pk)

end Budget

/-! ## The forger's view -/

section View

/-- The answers of the permutation model's oracles from those of `specU` and a permutation
table: the cipher answered by `π` forward or inverse. -/
def joinUP (f : (t : DomIC ⊕ (ByteArray ⊕ TG)) → AnsU t) (π : PTable) :
    (t : DomP ⊕ (ByteArray ⊕ TG)) → AnsUP t
  | .inl (.inl d) => f (.inl (.inl d))
  | .inl (.inr c) => pans π c
  | .inr (.inl x) => f (.inr (.inl x))
  | .inr (.inr t) => f (.inr (.inr t))

/-- **The forger's view is the permutation oracle**: at any answer table whose cipher part is the
forward table `π.fwd`, the normalized forger computes what the forger computes against `π` with
forward and inverse queries (the reduction's `H₄` queries are hidden from it). -/
theorem eval_normU (p : Params) (π : PTable) (f : (t : DomIC ⊕ (ByteArray ⊕ TG)) → AnsU t)
    (hf : ∀ c, f (.inl (.inr c)) = π.fwd c) {α : Type} (F : OracleComp specUP α) :
    evalWithAnswerFn (QueryImpl.ofFn f) (normU p π F) =
      evalWithAnswerFn (QueryImpl.ofFn (joinUP f π)) F := by
  induction F using OracleComp.inductionOn with
  | pure a => simp [normU]
  | query_bind t k ih =>
    rw [normU_query_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
    rcases t with (d | ⟨b, c⟩) | (x | t)
    · by_cases hd : d.1 = .h21
      · simp only [normUImpl, hd, ite_true]
        exact ih _
      · simp only [normUImpl, hd, ite_false]
        exact ih _
    · cases b
      · simp only [normUImpl]
        exact ih _
      · simp only [normUImpl]
        show evalWithAnswerFn (QueryImpl.ofFn f) (normU p π (k (f (.inl (.inr c))))) =
          evalWithAnswerFn (QueryImpl.ofFn (joinUP f π)) (k (π.fwd c))
        rw [hf]
        exact ih _
    · simp only [normUImpl]
      exact ih _
    · simp only [normUImpl]
      exact ih _

end View

end VoleMole.ROM.OneMore.Pomfrit
