import VoleMole.ROM.OneMoreClsQueries
import VoleMole.ROM.OneMoreLemmaPSimPerm

/-!
# PomFRIT's Theorem U1^cls with AES as random permutations, with inverse queries

`lean/docs/security/pomfrit.md` §6.4 (G8-cls), `pomfrit-lemmap-tight.md` §6A.5. Theorem U1^cls
(`pomfrit_U1_cls_sim'`, `ROM/OneMoreCls*.lean`) for a forger of the permutation model
(`ForgerP`, `gameP`, `ROM/OneMorePerm.lean`): the cipher is a uniform permutation table `π`, the
forger makes forward and inverse cipher queries.

* **The reduction's forger** (`wrapEP lr A π = wrapE lr π.fwd (A.toIC lr π)`): the forger
  normalized at `π` (inverse queries recorded as forward records, `H₄(iv)` before each `H₂¹`
  query), then wrapped with the forward table `π.fwd` (the decoder's `H₅` queries). The game with
  it is `gamePE` (`gameP` for a forger that depends on `π`); the wrapper changes neither the
  forgeries nor the win (`pomWin_le_wrapP`, `flag_wrapE` at `π.fwd`).
* **The wrapped family is not a `RecFamily`**: the wrapper's `H₅` inputs read `π.fwd` at the
  committed leaf keys, which the forger may never have queried. So, as in the PRF view, Lemma P^cls
  is applied per table (`prEvent_clsFailZ_sim_le_Ec` at `E = π.fwd`, with the point-tied Post
  `PostPOut`), and only the three cipher terms (binding, an opened dead leaf, Post) are moved,
  table by table, to the derived provers of the normalized forger `A.toIC lr π`
  (`events_wrapE`, `postPOut_wrapE`), which are a `RecFamily` (`recFamily_proverP`); they are then
  averaged over `π` by `sum_fail_le_fam` (`failEpsP`). No new averaging lemma is needed.
* **`KeysPre` for the wrapped prover outside its `PostPOut`** (`keysPre_proverP_wrapE`): the
  wrapper queries `iv = H₄(iv_pre ‖ mu₁ ‖ 4)` with the true `mu₁` before every `H₂¹` input `x`, which
  is the normalization's `H₄(ivIn x)` whenever `x` carries the true `mu₁` (`IvMu`,
  `ivMu_proverP_wrapE`): N1 for the `H₂¹` inputs that `KeysPre` reads
  (`keysPre_of_not_postP_mu`). This holds for any forger.
* **Post moves to the forger** (`postP_of_filter`): the wrapped and the plain derived provers' joint
  logs agree up to `H₂⁴`, `H₄`, `H₅` entries; the half-targets of the wrapped log's prefix are among
  those of the plain log's (the `H₂¹` inputs and `H₁` entries agree, and the plain log has every
  `iv` by N1, `n1c_proverP`).
* **Theorem U1^cls, permutation model** (`pomfrit_U1_cls_simP`):

      Pr[PomWin] ≤ Adv^{ompr}(red (wrapEP, E₁^cls); Q_T + ℓ + 1, ℓ) + clsSimEpsP(q', q_E', n', ℓ),

  `clsSimEpsP` is `clsSimEps` with `failEpsP` in place of `failEps`; `q' = qP (qW (addH4 qA) NdC)
  Q_T ℓ`, `q_E' = eP lr q_E ℓ`, `n' = nP (nW (nA + qA₂₁) (addH4 qA) NdC) Q_T ℓ`.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.ZK.Sim VoleMole.Verifier.Bridge

/-! ## N1 for the `H₂¹` inputs with a given `mu₁` -/

section IvMu

/-- **N1 for the `H₂¹` inputs with `mu₁ = m`**: each such `H₂¹` entry of `L` is preceded by the
`H₄` query of its `iv`. -/
def IvMu (p : Params) (m : ByteArray) (L : QueryLog specIC) : Prop :=
  ∀ (pre post : QueryLog specIC) (x : ByteArray) (u : Ans (.h21, x)),
    L = pre ++ (⟨.inl (.h21, x), u⟩ : (t : DomIC) × AnsIC t) :: post → x.extract 0 32 = m →
      (.inl (.h4, ivIn p x) : DomIC) ∈ pre.map Sigma.fst

lemma ivMu_of_ivBefore {p : Params} (m : ByteArray) {L : QueryLog specIC} (h : IvBefore p L) :
    IvMu p m L := fun pre post x u hL _ => h pre post x u hL

lemma ivMu_of_noH21 {p : Params} {m : ByteArray} {C : QueryLog specIC}
    (hC : ∀ x, (.inl (.h21, x) : DomIC) ∉ C.map Sigma.fst) : IvMu p m C := by
  intro pre post x u hL _
  exact absurd (by rw [hL]; simp) (hC x)

lemma ivMu_append {p : Params} {m : ByteArray} {A B : QueryLog specIC} (hA : IvMu p m A)
    (hB : IvMu p m B) : IvMu p m (A ++ B) := by
  intro pre post x u h hx
  rcases List.append_eq_append_iff.1 h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · have := hB a' post x u h2 hx
    rw [h1, List.map_append]
    exact List.mem_append_right _ this
  · rcases c' with _ | ⟨e', c''⟩
    · rw [List.append_nil] at h1
      rw [List.nil_append] at h2
      have := hB [] post x u (by rw [List.nil_append]; exact h2.symm) hx
      simp at this
    · rw [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact hA pre c'' x u h1 hx

/-- **One step**: the log `L`, then entries `C` without `H₂¹` inputs, then the entry `e`, whose
`iv` (if `e` is an `H₂¹` entry with `mu₁ = m`) is in `L ++ C`. -/
lemma ivMu_step {p : Params} {m : ByteArray} {L C : QueryLog specIC} (e : (t : DomIC) × AnsIC t)
    (hL : IvMu p m L) (hC : ∀ x, (.inl (.h21, x) : DomIC) ∉ C.map Sigma.fst)
    (he : ∀ x, e.1 = .inl (.h21, x) → x.extract 0 32 = m →
      (.inl (.h4, ivIn p x) : DomIC) ∈ (L ++ C).map Sigma.fst) :
    IvMu p m (L ++ C ++ [e]) := by
  intro pre post x u h hx
  rcases List.eq_nil_or_concat post with rfl | ⟨post', y, rfl⟩
  · obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    rw [← h1]
    rw [List.cons.injEq] at h2
    exact he x (by rw [h2.1]) hx
  · have h' : L ++ C ++ [e] =
        (pre ++ (⟨.inl (.h21, x), u⟩ : (t : DomIC) × AnsIC t) :: post') ++ [y] := by
      rw [h]; simp
    obtain ⟨h1, -⟩ := List.append_inj' h' rfl
    exact ivMu_append hL (ivMu_of_noH21 hC) pre post' x u h1 hx

end IvMu

/-! ## The wrapped forger's log has N1 for the true `mu₁` -/

section Wrap

variable (g : Table) (E : CTable) (lr : Bool) (pre : TG → SIss)

lemma ivCell_eq_ivIn {x m : ByteArray} (hx : x.extract 0 32 = m) :
    (ivCell lr x m : Dom) = (.h4, ivIn (pomfritParams lr) x) := by
  rw [ivCell, ivIn, hx]

/-- **A hash or cipher query keeps `IvMu`**: before an `H₂¹` query the wrapper asks its `iv` with
the true `mu₁`. -/
lemma ivMu_hash {Lw L : QueryLog specIC} (h : IvMu (pomfritParams lr) (g muCell).ba L) (d : DomIC) :
    IvMu (pomfritParams lr) (g muCell).ba (L ++ cvOf g E lr Lw d ++ [⟨d, join g E d⟩]) := by
  refine ivMu_step _ h (not_h21_of_keep (cvOf_keep g E lr Lw d)) fun x hd hx => ?_
  simp only at hd
  subst hd
  rw [List.map_append]
  refine List.mem_append_right _ ?_
  simp only [cvOf, ite_true, covLog, List.map_cons]
  rw [ivCell_eq_ivIn lr hx]
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- **A target query keeps `IvMu`.** -/
lemma ivMu_ht {L : QueryLog specIC} (h : IvMu (pomfritParams lr) (g muCell).ba L) (x : ByteArray) :
    IvMu (pomfritParams lr) (g muCell).ba (L ++ axT g lr L x) :=
  ivMu_append h (ivMu_of_noH21 fun x1 => axT_not_h21 g lr L x x1)

theorem ivMu_wrapIC_clsW {α : Type} (oa : OracleComp specU α) :
    ∀ (Lw L : QueryLog specIC) (s : HTS × Gh), IvMu (pomfritParams lr) (g muCell).ba L →
      IvMu (pomfritParams lr) (g muCell).ba (evalWithAnswerFn (QueryImpl.ofFn (join g E))
        ((simulateQ (wrapIC lr hintVoid pre) ((simulateQ (clsW lr E) oa).run Lw)).run (L, s))).2.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro Lw L s h; simpa using h
  | query_bind q k ih =>
    intro Lw L s h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with d | (x | t)
    · simp only [clsW, StateT.run_mk, simulateQ_bind, StateT.run_bind, evalWithAnswerFn_bind]
      rw [eval_wrapIC_toU]
      erw [eval_wrapIC_queryL g E lr pre hintVoid d]
      simp only [simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure, (eval_coverAt g E lr Lw d).1,
        (eval_coverAt g E lr Lw d).2]
      exact ih (join g E d) _ _ s (ivMu_hash g E lr h d)
    · simp only [clsW, StateT.run_mk, simulateQ_map, StateT.run_map]
      simp only [evalWithAnswerFn_bind, bind_map_left]
      erw [eval_wrapIC_queryT g E lr pre x L s.1 s.2]
      exact ih _ Lw _ _ (ivMu_ht g lr h x)
    · simp only [clsW, StateT.run_mk, simulateQ_map, StateT.run_map]
      simp only [evalWithAnswerFn_bind, bind_map_left]
      erw [eval_wrapIC_queryI g E lr pre t L s.1 s.2]
      exact ih _ Lw _ _ h

/-- **The wrapped forger's log has N1 for the true `mu₁`**, for any forger. -/
theorem ivMu_wrapE (A : Forger) (pk : UovPk) (hs : HTS) :
    IvMu (pomfritParams lr) (g muCell).ba (evalWithAnswerFn (QueryImpl.ofFn (join g E))
      ((simulateQ (wrapIC lr hintVoid pre) (wrapE lr E A pk)).run ([], hs, fun _ => none))).2.1 := by
  have h := ivMu_wrapIC_clsW g E lr pre (A pk) [] [] (hs, fun _ => none)
    (ivMu_of_noH21 fun _ => by simp)
  simpa only [wrapE, StateT.run'_eq, simulateQ_map, StateT.run_map, evalWithAnswerFn_map] using h

variable (pk : UovPk)

/-- **The wrapped forger's derived provers have N1 for the true `mu₁`.** -/
theorem ivMu_proverP_wrapE (A : Forger) (Lst : List TG) (i : ℕ) :
    IvMu (pomfritParams lr) (g muCell).ba (jOf g (proverP lr pk pre (wrapE lr E A) Lst i) E) := by
  show IvMu _ _ (tableQueryLog (proverP lr pk pre (wrapE lr E A) Lst i) (join g E))
  rw [log_proverP]
  exact ivMu_append (ivMu_wrapE g E lr pre A pk (hs0 Lst))
    (ivMu_of_ivBefore _ (n1c_contP lr pk i _ g E))

/-- **Outside the point-tied Post, `KeysPre`** for the derived provers of the wrapped forger (any
forger). -/
theorem keysPre_proverP_wrapE (A : Forger) (Lst : List TG) (i : ℕ) (s : TG × ByteArray × ByteArray)
    (h : ¬PostPOut (pomfritParams lr) E (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameIC CrtGen.tables (stG lr pk s) (proverP lr pk pre (wrapE lr E A) Lst i) E))) :
    KeysPre (stG lr pk s) E (jOf g (proverP lr pk pre (wrapE lr E A) Lst i) E)
      (gLog CrtGen.tables (stG lr pk s) (proverP lr pk pre (wrapE lr E A) Lst i) E g) g := by
  refine keysPre_of_not_postP_mu CrtGen.tables (stG lr pk s) _ (pomfritParams lr) rfl E g
    (fun pre' post x u hJ hx => ivMu_proverP_wrapE g E lr pre pk A Lst i pre' post x u hJ ?_) ?_
  · rw [hx, stG_mu1]; rfl
  · unfold PostPOut at h
    rwa [gameIC_aux] at h

end Wrap

/-! ## Post of the wrapped forger's derived game is the forger's -/

section Post

lemma logBefore_filter {D : Type} [DecidableEq D] {R : D → Type} (q : (t : D) × R t → Bool)
    (d : D) (hq : ∀ e : (t : D) × R t, e.1 = d → q e = true) (L : QueryLog (ofFn R)) :
    (logBefore d L).filter q = logBefore d (L.filter q) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    by_cases he : e.1 = d
    · obtain ⟨t, u⟩ := e
      simp only at he
      subst he
      rw [logBefore_cons_self, List.filter_cons_of_pos (hq _ rfl), logBefore_cons_self]
      rfl
    · rw [logBefore_cons_of_ne _ _ he]
      by_cases hqe : q e = true
      · rw [List.filter_cons_of_pos hqe, List.filter_cons_of_pos hqe, logBefore_cons_of_ne _ _ he,
          ih]
      · rw [List.filter_cons_of_neg hqe, List.filter_cons_of_neg hqe, ih]

lemma kindIns_h21_filter_keepK (L : QueryLog specIC) :
    kindIns .h21 (hashLog (L.filter keepK)) = kindIns .h21 (hashLog L) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨t, u⟩ := e
    cases t with
    | inl d =>
      by_cases h : keepK ⟨.inl d, u⟩ = true
      · simp only [List.filter_cons, h, ite_true]
        simp only [hashLog, List.filterMap_cons, kindIns, List.filter_cons] at ih ⊢
        split_ifs <;> simp_all
      · have hd : d.1 ≠ .h21 := by
          intro hd; simp [keepK, hd] at h
        simp only [List.filter_cons, h, Bool.false_eq_true, ite_false]
        simp only [hashLog, List.filterMap_cons, kindIns, List.filter_cons] at ih ⊢
        simp [hd, ih]
    | inr c =>
      simp only [List.filter_cons, keepK, ite_true]
      simp only [hashLog, List.filterMap_cons, kindIns] at ih ⊢
      exact ih

lemma mem_of_mem_kindIns {k : Kind} {L : QueryLog specIC} {x : ByteArray}
    (h : x ∈ kindIns k (hashLog L)) : (.inl (k, x) : DomIC) ∈ L.map Sigma.fst := by
  unfold kindIns at h
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
  have hd1 := (List.mem_filter.1 hd).1
  have hk := (List.mem_filter.1 hd).2
  simp only [decide_eq_true_eq] at hk
  obtain ⟨k', x'⟩ := d
  simp only at hk
  subst hk
  exact mem_hashLog.1 hd1

lemma ivAt_some {p : Params} {G : QueryLog spec} {x iv : ByteArray} {g : Table}
    (hG : ∀ e ∈ G, e = ⟨e.1, g e.1⟩) (h : ivAt p G x = some iv) :
    iv = (g (.h4, ivIn p x)).ba := by
  have hm : ((.h4, ivIn p x) : Dom) ∈ G.map Sigma.fst := by
    unfold ivAt at h
    obtain ⟨e, hf, -⟩ := Option.map_eq_some_iff.1 h
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    exact List.mem_map.2 ⟨e, List.mem_of_find?_eq_some hf, hp⟩
  rw [ivAt_eq hG hm] at h
  exact (Option.some.inj h).symm

lemma logBefore_h1_filter_keepH (x : ByteArray) (G : QueryLog spec) :
    (logBefore ((.h21, x) : Dom) G).filter isH1E =
      (logBefore ((.h21, x) : Dom) (G.filter keepH)).filter isH1E := by
  rw [← logBefore_filter keepH _ (fun e he => by simp [keepH, he]), List.filter_filter]
  congr 1
  funext e
  by_cases h : e.1.1 = .h1 <;> simp [isH1E, keepH, h]

/-- **The half-targets of a prefix of the wrapped log are among those of the plain log's prefix**
with the same kept entries, when the plain log has N1. -/
lemma halfT_subset (p : Params) (E : CTable) (g : Table) {J pre pre' post : QueryLog specIC}
    {e : (t : DomIC) × AnsIC t} (hJ : J = pre ++ e :: post) (hN : IvBefore p J)
    (hans : ∀ e ∈ J, e = ⟨e.1, join g E e.1⟩) (hans' : ∀ e ∈ pre', e = ⟨e.1, join g E e.1⟩)
    (hf : pre'.filter keepK = pre.filter keepK) :
    halfT p pre' ⊆ halfT p pre := by
  intro j hj
  unfold halfT at hj ⊢
  rw [List.mem_toFinset, List.mem_flatMap] at hj ⊢
  obtain ⟨x, hx, hjx⟩ := hj
  have hk : kindIns .h21 (hashLog pre') = kindIns .h21 (hashLog pre) := by
    rw [← kindIns_h21_filter_keepK pre', hf, kindIns_h21_filter_keepK]
  refine ⟨x, hk ▸ hx, ?_⟩
  cases hiv : ivAt p (hashEnt pre') x with
  | none => rw [hiv] at hjx; simp at hjx
  | some iv =>
    rw [hiv] at hjx
    have hiv' := ivAt_some (hashEnt_answer hans') hiv
    have hxpre : (.inl (.h21, x) : DomIC) ∈ pre.map Sigma.fst :=
      mem_of_mem_kindIns (hk ▸ hx)
    obtain ⟨u, rest, hpre⟩ := exists_split_of_mem hxpre
    have hansP : ∀ e ∈ pre, e = ⟨e.1, join g E e.1⟩ := fun e he =>
      hans e (by rw [hJ]; exact List.mem_append_left _ he)
    have h4 : ((.h4, ivIn p x) : Dom) ∈ (hashEnt pre).map Sigma.fst := by
      rw [map_fst_hashEnt]
      refine mem_hashLog.2 ?_
      have hJ' : J = logBefore (.inl (.h21, x)) pre ++
          (⟨.inl (.h21, x), u⟩ : (t : DomIC) × AnsIC t) :: (rest ++ e :: post) := by
        rw [hJ]; conv_lhs => rw [hpre]
        simp
      have := hN _ _ x u hJ'
      rw [hpre, List.map_append]
      exact List.mem_append_left _ this
    have hivP : ivAt p (hashEnt pre) x = some iv := by
      rw [ivAt_eq (hashEnt_answer hansP) h4, hiv']
    have hc : comPre (logBefore ((.h21, x) : Dom) (hashEnt pre')) =
        comPre (logBefore ((.h21, x) : Dom) (hashEnt pre)) := by
      refine comPre_congr ?_
      rw [logBefore_h1_filter_keepH, logBefore_h1_filter_keepH x (hashEnt pre),
        ← hashEnt_filter_keepK, ← hashEnt_filter_keepK, hf]
    rw [hivP]
    simp only at hjx ⊢
    rw [← hc]
    exact hjx

/-- **The point-tied Post reads the kept entries, the `H₂¹` inputs' `iv`s and the cipher**: for
two logs with the same kept entries, both answered by `g` and `E`, the first with N1, Post of the
second is Post of the first. -/
lemma postP_of_filter (p : Params) (E : CTable) (g : Table) {J J' : QueryLog specIC}
    (h : J'.filter keepK = J.filter keepK) (hN : IvBefore p J)
    (hans : ∀ e ∈ J, e = ⟨e.1, join g E e.1⟩) (hans' : ∀ e ∈ J', e = ⟨e.1, join g E e.1⟩)
    (hp : PostP p E J') : PostP p E J := by
  obtain ⟨pre', e, post', κ, w, hJ', he, j, hj, h1, h2, h3, h4⟩ := hp
  have hke : keepK e = true := by obtain ⟨t, u⟩ := e; simp only at he; subst he; rfl
  have hf : J.filter keepK = pre'.filter keepK ++ e :: post'.filter keepK := by
    rw [← h, hJ', List.filter_append, List.filter_cons_of_pos hke]
  obtain ⟨pre, post, hJ, hpre⟩ := split_of_filter J hf
  have hans'' : ∀ e ∈ pre', e = ⟨e.1, join g E e.1⟩ := fun e he =>
    hans' e (by rw [hJ']; exact List.mem_append_left _ he)
  refine ⟨pre, e, post, κ, w, hJ, he, j, halfT_subset p E g hJ hN hans hans'' hpre.symm hj, ?_, ?_,
    h3, h4⟩
  · rw [← mem_inr_filter_keepK, hpre, mem_inr_filter_keepK]; exact h1
  · rw [← mem_inr_filter_keepK, hpre, mem_inr_filter_keepK]; exact h2

variable (lr : Bool) (pk : UovPk) (pre : TG → SIss)

/-- **The point-tied Post of the wrapped forger's derived game is the forger's**, table by table,
when the forger's derived prover has N1. -/
theorem postPOut_wrapE (g : Table) (E : CTable) (A : Forger) (Lst : List TG) (i : ℕ)
    (hN : IvBefore (pomfritParams lr) (jOf g (proverP lr pk pre A Lst i) E)) :
    PostPOut (pomfritParams lr) E (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stG lr pk) (proverP lr pk pre (wrapE lr E A) Lst i) E)) →
    PostPOut (pomfritParams lr) E (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stG lr pk) (proverP lr pk pre A Lst i) E)) := by
  intro hp
  obtain ⟨-, -, e3⟩ := eval_proverP_wrapE g E lr pk pre A Lst i
  unfold PostPOut at hp ⊢
  rw [evalWithAnswerFn_gameA, aux_gameIC] at hp ⊢
  exact postP_of_filter _ E g e3 hN (tableQueryLog_answer _ _) (tableQueryLog_answer _ _) hp

end Post

/-! ## The game with a forger that depends on the permutation table -/

section GamePE

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (n ℓ : ℕ) (T : CrtTables)
  (lr : Bool)

/-- **The reduction's forger in the permutation model**: the forger normalized at `π`, wrapped with
the forward table `π.fwd`. -/
noncomputable def wrapEP (lr : Bool) (A : ForgerP) (π : PTable) : Forger :=
  wrapE lr π.fwd (A.toIC lr π)

/-- The composed adversary for a forger `AE π` that depends on the permutation table, with the
hint rule at the forward table. -/
noncomputable def advCPE {Hn : Type} (AE : PTable → Forger)
    (hint : CTable → QueryLog specIC → ByteArray → Hn) (tgts : TG × Hn → List TG) (pk : UovPk) :
    ProbComp (OracleComp (specC Hn) (List (ByteArray × SIss) × Bool)) := do
  let π ← $ᵗ PTable
  pure (Acomp T lr π.fwd (hint π.fwd) tgts pk ℓ (AE π))

/-- **The one-more game with a forger that depends on the permutation table** (`gameP` with
`AE π` in place of `A.toIC lr π`; `gameP` is `gamePE` at `fun π => A.toIC lr π`). -/
noncomputable def gamePE {Hn : Type} (AE : PTable → Forger) (φ : Hn → TG ≃ TG)
    (hint : CTable → QueryLog specIC → ByteArray → Hn) (tgts : TG × Hn → List TG) :=
  omuf KG pre n φ (advCPE ℓ T lr AE hint tgts)

set_option linter.constructorNameAsVariable false in
lemma pomWin_forgesPE {Hn : Type} (AE : PTable → Forger) (φ : Hn → TG ≃ TG)
    (hint : CTable → QueryLog specIC → ByteArray → Hn) (tgts : TG × Hn → List TG)
    {r : UovPk × (List (ByteArray × SIss) × Bool) × (ByteArray → Option (TG × Hn)) ×
      Ch Ans ByteArray Hn TG} (hr : r ∈ support (gamePE KG pre n ℓ T lr AE φ hint tgts))
    (hw : PomWin ℓ r) : Forges ℓ r.2.1 r.2.2.2 := by
  simp only [gamePE, omuf, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨kp, -, a, ha, L, -, r', hr', rfl⟩ := hr
  simp only [advCPE, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ha
  obtain ⟨π, -, rfl⟩ := ha
  have h1 : r'.1 ∈ support (Acomp T lr π.fwd (hint π.fwd) tgts kp.1 ℓ (AE π)) := by
    refine support_simulateQ_run'_subset (realImpl φ (pre kp.2))
      (Acomp T lr π.fwd (hint π.fwd) tgts kp.1 ℓ (AE π)) (fun _ => none, ch0 L) ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨r', hr', rfl⟩
  obtain ⟨hlen, hnd⟩ := acomp_support T lr π.fwd (hint π.fwd) tgts kp.1 ℓ (AE π) h1 hw.1
  exact ⟨hw.1, hlen, hnd, hw.2⟩

set_option linter.constructorNameAsVariable false in
lemma advCPE_bound {Hn : Type} (QT : ℕ) (AE : PTable → Forger)
    (hint : CTable → QueryLog specIC → ByteArray → Hn) (tgts : TG × Hn → List TG)
    (hA : ∀ π pk, IsQueryBoundP (AE π pk) (fun q => isHT q = true) QT)
    (pk : UovPk) : ∀ a ∈ support (advCPE ℓ T lr AE hint tgts pk),
      IsQueryBoundP a (fun q => isTgt q = true) (QT + (ℓ + 1)) := by
  intro a ha
  simp only [advCPE, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ha
  obtain ⟨π, -, rfl⟩ := ha
  exact acomp_bound (E := π.fwd) (hint := hint π.fwd) T lr tgts pk ℓ QT (AE π) (hA π pk)

set_option linter.constructorNameAsVariable false in
/-- **Theorem U1's reduction for a forger that depends on the permutation table**
(`pomfrit_U1_boundE` with `PTable`). -/
theorem pomfrit_U1_boundPE (QT : ℕ) (AE : PTable → Forger)
    (e1 : CTable → QueryLog specIC → ByteArray → TG)
    (hA : ∀ π pk, IsQueryBoundP (AE π pk) (fun q => isHT q = true) QT) :
    Pr{let r ← gamePE KG pre (QT + (ℓ + 1)) ℓ T lr AE addHint e1 tgts1}[PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre (QT + (ℓ + 1)) (red addHint (advCPE ℓ T lr AE e1 tgts1))}[
        Wins ℓ (goodPre relP) r.1 r.2.1 r.2.2] +
      Pr{let r ← gamePE KG pre (QT + (ℓ + 1)) ℓ T lr AE addHint e1 tgts1}[
        ∃ i : Fin (ℓ + 1), PFail i.val r] := by
  refine (prEvent_mono_of_support _ _ _ fun _ hr hw =>
    pomWin_forgesPE KG pre _ ℓ T lr AE _ _ _ hr hw).trans ?_
  refine (omuf_le_of_bound KG pre _ ℓ addHint _ (advCPE_bound ℓ T lr QT AE _ _ hA)
    (goodPre relP)).trans (add_le_add le_rfl (prEvent_mono _ _ _ fun r ⟨i, hr⟩ => ⟨i, ?_⟩))
  obtain ⟨hacc, ⟨x, σ⟩, hp, hng⟩ := hr
  refine ⟨hacc, x, σ, hp, fun ⟨a, e, hs, hrel⟩ => hng ?_⟩
  simp only [hs, Option.map_some]
  exact ⟨_, _, rfl, hrel⟩

/-- **The wrapper does not change the win in the permutation model** (any number of targets):
`flag_wrapE` at `π.fwd` for the normalized forger. -/
theorem pomWin_le_wrapP (A : ForgerP) :
    Pr{let r ← gameP KG pre n ℓ CrtGen.tables lr A addHint (e1C lr) tgts1}[PomWin ℓ r] ≤
      Pr{let r ← gamePE KG pre n ℓ CrtGen.tables lr (wrapEP lr A) addHint (e1C lr) tgts1}[
        PomWin ℓ r] := by
  unfold gameP gamePE omuf advCP advCPE
  simp only [bind_assoc, pure_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun kp => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun π => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun L => ?_
  have key : ∀ A' : Forger, (simulateQ (realImpl addHint (pre kp.2))
      (Acomp CrtGen.tables lr π.fwd (e1C lr π.fwd) tgts1 kp.1 ℓ A')).run (fun _ => none, ch0 L) =
      (fun z => (z.1.1, (z.1.2.1, chOf z.1.2.2 z.2))) <$>
        (simulateQ randomOracle ((simulateQ (htW (AR := Ans) addHint (pre kp.2))
          (Acomp CrtGen.tables lr π.fwd (e1C lr π.fwd) tgts1 kp.1 ℓ A')).run (hs0 L))).run ∅ :=
    fun A' => realImpl_run_eq addHint (pre kp.2) _ (fun _ => none) (ch0 L)
  have h := prEvent_le_of_table
    ((simulateQ (htW (AR := Ans) addHint (pre kp.2))
      (Acomp CrtGen.tables lr π.fwd (e1C lr π.fwd) tgts1 kp.1 ℓ (A.toIC lr π))).run (hs0 L))
    ((simulateQ (htW (AR := Ans) addHint (pre kp.2))
      (Acomp CrtGen.tables lr π.fwd (e1C lr π.fwd) tgts1 kp.1 ℓ (wrapEP lr A π))).run (hs0 L))
    (fun z => z.1.2 = true ∧ z.2.2.2.2 ≤ ℓ) (fun z => z.1.2 = true ∧ z.2.2.2.2 ≤ ℓ)
    fun g hz => by
      obtain ⟨f1, f2⟩ := flag_wrapE g CrtGen.tables lr π.fwd addHint (e1C lr π.fwd) tgts1 kp.1
        (pre kp.2) (A.toIC lr π) ℓ L
      exact ⟨f1 ▸ hz.1, f2 ▸ hz.2⟩
  simp only [key, StateT.run'_eq, Functor.map_map, bind_pure_comp] at h ⊢
  exact h

end GamePE

/-! ## U1^cls's term, averaged over the permutation table -/

/-- **Comparison of two families of games over the permutation table, table by table.** -/
lemma prEvent_transferP {X Y : Type} (oa : PTable → OracleComp spec X)
    (ob : PTable → OracleComp spec Y) (P : PTable → X → Prop) (Q : PTable → Y → Prop)
    (h : ∀ π g, P π (evalWithAnswerFn (QueryImpl.ofFn g) (oa π)) →
      Q π (evalWithAnswerFn (QueryImpl.ofFn g) (ob π))) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (oa π)).run' ∅}[P π r] ≤
      Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (ob π)).run' ∅}[Q π r] :=
  (prEvent_bind_le_sum_of_table ($ᵗ PTable) oa (Finset.univ : Finset Unit) (fun _ π => ob π) P
    (fun _ => Q) fun π g hP => ⟨(), Finset.mem_univ _, h π g hP⟩).trans (by simp)

/-- **`clsSimEps` in the permutation model**: the failure terms `failEpsP` (`L0-L2` with
`p = 1/(2¹²⁸ − q_E)`) in place of `failEps`. -/
noncomputable def clsSimEpsP (q : Kind → ℕ) (qE n ℓ : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ adaptKinds, ((q k : ℝ≥0∞) + (ℓ + 1) * ((extractorQueries + verifierQueries) k : ℝ≥0∞)) *
      simEpsC (n + (2 + verifierTotal)) (q + extractorQueries + verifierQueries) k +
    (ℓ + 1) * (failEpsP q qE + (2 ^ 128 : ℝ≥0∞)⁻¹)

set_option exponentiation.threshold 1100 in
/-- **`clsSimEpsP` with the chain charges written out** (`clsSimEps_eq` with `failEpsP`). -/
theorem clsSimEpsP_eq (q : Kind → ℕ) (qE n ℓ : ℕ) :
    clsSimEpsP q qE n ℓ =
      ((q .h21 : ℝ≥0∞) + (ℓ + 1)) * ((2 ^ 150 : ℝ≥0∞)⁻¹ + (2 ^ 134 : ℝ≥0∞)⁻¹) +
      ((q .h22 : ℝ≥0∞) + (ℓ + 1)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
        (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + (2 + verifierTotal) : ℕ) : ℝ≥0∞) / 2 ^ 448) +
      ((q .h23 : ℝ≥0∞) + (ℓ + 1)) * ((2 ^ 50 : ℝ≥0∞) / 2 ^ 128) +
      ∑ k ∈ adaptKinds, ((q k : ℝ≥0∞) + (ℓ + 1) * ((extractorQueries + verifierQueries) k : ℝ≥0∞)) *
        (hitEps (q + extractorQueries + verifierQueries)
          (combCount (some (45, dstP)) (q + extractorQueries + verifierQueries)) k +
          stmtEpsD (q + extractorQueries + verifierQueries) k +
          orderEps (q + extractorQueries + verifierQueries) k) +
      (ℓ + 1) * (failEpsP q qE + (2 ^ 128 : ℝ≥0∞)⁻¹) := by
  unfold clsSimEpsP
  congr 1
  have hsplit : ∀ k, simEpsC (n + (2 + verifierTotal)) (q + extractorQueries + verifierQueries) k =
      cellEpsC (n + (2 + verifierTotal)) k +
        (hitEps (q + extractorQueries + verifierQueries)
          (combCount (some (45, dstP)) (q + extractorQueries + verifierQueries)) k +
          stmtEpsD (q + extractorQueries + verifierQueries) k +
          orderEps (q + extractorQueries + verifierQueries) k) := fun k => by
    simp only [simEpsC, add_assoc]
  simp only [hsplit, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [adaptKinds]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [cellEpsC, Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self,
    ↓reduceIte, add_zero, mul_zero, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
  ring

variable (lr : Bool) (pk : UovPk) (pre : TG → SIss) (A : ForgerP) (Lst : List TG) (ℓ : ℕ)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **U1^cls's term with simultaneous extraction, permutation model, for a fixed key and target
stream**: over the permutation table and the hash table, some forgery of the game with the wrapped
normalized forger and `E₁^cls` fails with probability at most `clsSimEpsP`. Per table, Lemma P^cls
with the point-tied Post (`prEvent_clsFailZ_sim_le_Ec`, `keysPre_proverP_wrapE`); the cipher terms
moved to the normalized forger's derived provers (`events_wrapE`, `postPOut_wrapE`) and averaged
there (`sum_fail_le_fam`). -/
theorem prEvent_clsFailZ_sim_leP (hd : pk.digest.size = 32) {qA : Kind → ℕ} {nA qE QT : ℕ}
    (hA : ForgerBoundP A qA nA qE QT) :
    Pr{let π ← $ᵗ PTable; let z ← (simulateQ randomOracle
        ((simulateQ (htW (AR := Ans) addHint pre) (Acomp CrtGen.tables lr π.fwd (e1C lr π.fwd)
          tgts1 pk ℓ (wrapEP lr A π))).run (hs0 Lst))).run' ∅}[∃ i : Fin (ℓ + 1), PFailZ pk i.val z] ≤
      clsSimEpsP (qP (qW (addH4 qA) NdC) QT ℓ) (eP lr qE ℓ)
        (nP (nW (nA + qA .h21) (addH4 qA) NdC) QT ℓ) ℓ := by
  classical
  set q := qP (qW (addH4 qA) NdC) QT ℓ
  set e := eP lr qE ℓ
  set ε := simEpsC (nP (nW (nA + qA .h21) (addH4 qA) NdC) QT ℓ + (2 + verifierTotal))
    (q + extractorQueries + verifierQueries)
  set c := ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * ε k +
      ∑ _j : Fin (ℓ + 1), ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) * ε k
  set pL := pomfritParams lr
  have hW : ∀ π : PTable, ForgerBound (wrapEP lr A π) (qW (addH4 qA) NdC)
      (nW (nA + qA .h21) (addH4 qA) NdC) qE QT := fun π =>
    forgerBound_wrapE lr π.fwd (hA.toIC lr π)
  have hb0 : ∀ (π : PTable) (j : Fin (ℓ + 1)),
      IsKindQueryBoundIC (proverP lr pk pre (A.toIC lr π) Lst j.val) q ∧
      IsQueryBoundP (proverP lr pk pre (A.toIC lr π) Lst j.val) (fun t => t.isRight = true) e :=
    fun π j => by
      have h := proverP_bounds lr pre pk (hA.toIC lr π) Lst (Nat.lt_succ_iff.1 j.isLt)
      refine ⟨h.1.mono fun k => ?_, h.2.2⟩
      simp only [q, qP, qW, Pi.add_apply]; omega
  have havg := prEvent_avgP_le_sum4 _ (fun _ z => ∃ i : Fin (ℓ + 1), PFailZ pk i.val z) c
    (Finset.univ : Finset (Fin (ℓ + 1)))
    (fun j π => (simulateQ randomOracle (gameDP lr π.fwd pk pre (wrapEP lr A π) Lst j.val)).run' ∅)
    (fun π r => bindFailA (stG lr pk) π.fwd r) (fun π r => deadOpenA (stG lr pk) π.fwd r)
    (fun π r => PostPOut pL π.fwd r)
    (fun _ r => r.2.2.accept = true ∧
      ((.h23, zOut (stG lr pk (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2)
    (fun π => prEvent_clsFailZ_sim_le_Ec lr pk pre (wrapEP lr A π) Lst ℓ hd (hW π) π.fwd
      (PostPOut pL π.fwd)
      (fun j s g h => keysPre_proverP_wrapE g π.fwd lr pre pk (A.toIC lr π) Lst j.val s h)
      fun g => (eval_wrapE g π.fwd lr pre (A.toIC lr π) pk (hs0 Lst)).2.2.2)
  refine havg.trans ?_
  have htr : ∀ j : Fin (ℓ + 1),
      Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
          (gameDP lr π.fwd pk pre (wrapEP lr A π) Lst j.val)).run' ∅}[bindFailA (stG lr pk) π.fwd r] +
        Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
          (gameDP lr π.fwd pk pre (wrapEP lr A π) Lst j.val)).run' ∅}[deadOpenA (stG lr pk) π.fwd r] +
        Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
          (gameDP lr π.fwd pk pre (wrapEP lr A π) Lst j.val)).run' ∅}[PostPOut pL π.fwd r] ≤
      Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
          (stG lr pk) (proverP lr pk pre (A.toIC lr π) Lst j.val) π.fwd)).run' ∅}[bindFailA (stG lr pk) π.fwd r] +
        Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
          (stG lr pk) (proverP lr pk pre (A.toIC lr π) Lst j.val) π.fwd)).run' ∅}[deadOpenA (stG lr pk) π.fwd r] +
        Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
          (stG lr pk) (proverP lr pk pre (A.toIC lr π) Lst j.val) π.fwd)).run' ∅}[PostPOut pL π.fwd r] := fun j =>
    add_le_add (add_le_add
      (prEvent_transferP _ _ _ _ fun π g h =>
        (events_wrapE g π.fwd lr pk pre (A.toIC lr π) Lst j.val).1 h)
      (prEvent_transferP _ _ _ _ fun π g h =>
        (events_wrapE g π.fwd lr pk pre (A.toIC lr π) Lst j.val).2.1 h))
      (prEvent_transferP _ _ _ _ fun π g h =>
        postPOut_wrapE lr pk pre g π.fwd (A.toIC lr π) Lst j.val
          (n1c_proverP lr pk pre A Lst π j.val g π.fwd) h)
  have h3 := (Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin (ℓ + 1)))) => htr j).trans
    (sum_fail_le_fam CrtGen.tables (stG lr pk) pL (fun _ => rfl)
      (fun (j : Fin (ℓ + 1)) π => proverP lr pk pre (A.toIC lr π) Lst j.val) Finset.univ
      (fun j _ => recFamily_proverP lr pk pre A Lst j.val) e (fun j _ π => (hb0 π j).2) q
      (fun j _ π => (hb0 π j).1))
  rw [Finset.sum_add_distrib]
  refine (add_le_add le_rfl (add_le_add h3
    (Finset.sum_le_card_nsmul _ _ (2 ^ 128 : ℝ≥0∞)⁻¹ fun j _ => ?_))).trans_eq ?_
  · exact prEvent_avgP_le _ _ _ fun π =>
      prEvent_zUnqueried_le_A CrtGen.tables (stG lr pk) (proverP lr pk pre (wrapEP lr A π) Lst j.val)
        π.fwd
  simp only [c, clsSimEpsP, Finset.card_univ, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  simp only [add_mul, mul_assoc, mul_add]
  ring

section Game

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (lr : Bool) (A : ForgerP)

/-- **U1^cls's term with simultaneous extraction in the permutation game**: with the wrapped
normalized forger and `E₁^cls`, some forgery fails with probability at most `clsSimEpsP`, for any
number of targets. -/
theorem prEvent_clsFail_sim_leP (n ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBoundP A qA nA qE QT) :
    Pr{let r ← gamePE KG pre n ℓ CrtGen.tables lr (wrapEP lr A) addHint (e1C lr) tgts1}[
        ∃ i : Fin (ℓ + 1), PFail i.val r] ≤
      clsSimEpsP (qP (qW (addH4 qA) NdC) QT ℓ) (eP lr qE ℓ)
        (nP (nW (nA + qA .h21) (addH4 qA) NdC) QT ℓ) ℓ := by
  unfold gamePE omuf advCPE
  simp only [bind_assoc, pure_bind]
  apply prEvent_bind_le_of_forall_le_of_support KG _ (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)
  intro kp hkp
  rw [eqd_swap ($ᵗ PTable) (unifList TG n) (fun π L => (do
    let r ← (simulateQ (realImpl addHint (pre kp.2))
      (Acomp CrtGen.tables lr π.fwd (e1C lr π.fwd) tgts1 kp.1 ℓ (wrapEP lr A π))).run
        (fun _ => none, ch0 L)
    pure (kp.1, r.1, r.2))) (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)]
  apply prEvent_bind_le_of_forall_le _ _ (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)
  intro L
  refine le_trans (le_of_eq ?_)
    (prEvent_clsFailZ_sim_leP lr kp.1 (pre kp.2) A L ℓ (hdig kp hkp) hA)
  have key : ∀ π : PTable, (simulateQ (realImpl addHint (pre kp.2))
      (Acomp CrtGen.tables lr π.fwd (e1C lr π.fwd) tgts1 kp.1 ℓ (wrapEP lr A π))).run
        (fun _ => none, ch0 L) =
      (fun z => (z.1.1, (z.1.2.1, chOf z.1.2.2 z.2))) <$>
        (simulateQ randomOracle ((simulateQ (htW (AR := Ans) addHint (pre kp.2))
          (Acomp CrtGen.tables lr π.fwd (e1C lr π.fwd) tgts1 kp.1 ℓ (wrapEP lr A π))).run
            (hs0 L))).run ∅ := fun π =>
    realImpl_run_eq addHint (pre kp.2) _ (fun _ => none) (ch0 L)
  simp only [key, StateT.run'_eq, map_bind, Functor.map_map, bind_pure_comp]
  have hev : ∀ a : ((List (ByteArray × SIss) × Bool) × HTS) × (specR Ans).QueryCache,
      (∃ i : Fin (ℓ + 1), PFail i.val (kp.1, a.1.1, a.1.2.1, chOf a.1.2.2 a.2)) =
        (∃ i : Fin (ℓ + 1), PFailZ kp.1 i.val a.1) := fun a => rfl
  simp only [hev]

/-- **Theorem U1^cls with simultaneous extraction, AES as random permutations with inverse
queries** (`pomfrit.md` §6.4, G8-cls): for a key generation with 32-byte key digests, any Issuer and
a forger of the permutation model with budget `qA`, `nA`, `q_E` (forward and inverse), `Q_T`, with
the class extractor `E₁^cls` as the reduction's first-phase rule and the forger run normalized and
wrapped (`wrapEP`),

    Pr[PomWin] ≤ Adv^{ompr}(red (wrapEP, E₁^cls); Q_T + ℓ + 1, ℓ) + clsSimEpsP(q', q_E', n', ℓ),

`q' = qP (qW (addH4 qA) NdC) Q_T ℓ`, `q_E' = eP lr q_E ℓ`,
`n' = nP (nW (nA + qA₂₁) (addH4 qA) NdC) Q_T ℓ`. -/
theorem pomfrit_U1_cls_simP (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBoundP A qA nA qE QT) :
    Pr{let r ← gameP KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A addHint (e1C lr) tgts1}[
        PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre (QT + (ℓ + 1))
          (red addHint (advCPE ℓ CrtGen.tables lr (wrapEP lr A) (e1C lr) tgts1))}[
        Wins ℓ (goodPre relP) r.1 r.2.1 r.2.2] +
      clsSimEpsP (qP (qW (addH4 qA) NdC) QT ℓ) (eP lr qE ℓ)
        (nP (nW (nA + qA .h21) (addH4 qA) NdC) QT ℓ) ℓ :=
  (pomWin_le_wrapP KG pre _ ℓ lr A).trans
    ((pomfrit_U1_boundPE KG pre ℓ CrtGen.tables lr QT (wrapEP lr A) (e1C lr)
      fun π => (forgerBound_wrapE lr π.fwd (hA.toIC lr π)).ht).trans
    (add_le_add le_rfl (prEvent_clsFail_sim_leP KG pre lr A _ ℓ hdig hA)))

end Game

end VoleMole.ROM.OneMore.Pomfrit
