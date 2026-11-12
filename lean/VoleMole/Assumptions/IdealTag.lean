import VoleMole.Assumptions.UOV

/-!
# Programming challenge targets into an ideal hash: det-FDH ≤ A-OMPI ≤ OMPR

`lean/docs/security/uov-assumptions.md` §5.1 (Theorem 1 (a), (c)) and §5.8 (Lemma 2.1 of
`ratatouille.md` with `Tag` a random function). Protocol-independent: everything is generic in the
trapdoor (`Trapdoor`: key generation, preimage relation, sampler `D`), the message type `M` and the
world `specR AR` of the games of `Assumptions/UOV.lean`.

**Generic simulation lemmas** (in `Assumptions/LazyIdeal.lean`, shared with `Shift.lean` and
`CTUFOpenOMPR.lean`).
* `simulateQ_proj_eqd`: a handler `comb` simulates a handler `impl` through a projection `proj` of
  its state, if it does so per query on the states of an invariant that may consume a budget (one
  unit per query of a kind `p`); then the whole simulation does, for every computation within the
  budget. `simulateQ_inv_bound`: the invariant on the support. (The step relation is equality of
  distributions, so a fresh uniform sample on one side may match one on the other.)
* `prEvent_unifList_exists_le₀` (`LazyIdeal`), `prEvent_keyed_unifList_exists_le`: union bound over
  a uniform list.
* `unifList_add`: a uniform list of length `a + b` is a uniform list of length `a` followed by one
  of length `b`.

**The lazy A-OMPI challenger** (`ompiLazy`): it draws each target when requested (at most `q_T`),
instead of from a pre-sampled stream. `ompi_lazy_eqd`, `advOMPI_eq_lazy`: the same game.

**Theorem 1 (a): det-FDH ≤ A-OMPI** (`advFDH_le_ompi`). The reduction `fdhRed A` answers each fresh
`H(m)` with a fresh challenge target, `Sign(m)` with the index oracle at `m`'s index, and turns a
forgery `(m*, s*)` into `(index of m*, s*)` (it evaluates `H(m*)` first, `fwd`). The programming is
perfect (`fdhComb_step`, through `fdhProj`), so for an adversary with at most `k` hash and signing
queries on every path,

    Adv^{euf}_{det}(A; q_H, q_S) ≤ Adv^{ompi}(fdhRed A; k + 1, q_S).

With `Tag` modelled as a random function, UF-Tag (item 12, with the strict win "never signed") *is*
det-FDH with `H = Tag`: this is Lemma 2.1 of `ratatouille.md` in the random-function model, with no
loss. The permutation terms `q_K·2^{−479} + q_K²·2^{−799}` of the paper's Lemma 2.1 come from
modelling KP800 as a permutation with inverse queries; they are not mechanized (see the note).

**Theorem 1 (c): A-OMPI ≤ OMPR** (`advOMPI_le_ompr`). The reduction `ompiRed A` names A-OMPI's
targets by their indices, forwards the index queries to the preimage oracle (caching them, so
repeated indices cost nothing), caps the targets at `q_T`, and after the forgery *pads*: it requests
`Q − (answered indices)` further targets and their preimages, so that it holds exactly `Q + 1`
claims after exactly `Q` preimage queries, as `Wins` requires. A claim fails to be a preimage only
if `D` fails (or errs) on one of the challenger's targets:

    Adv^{ompi}(A; q_T, Q) ≤ Adv^{ompr}(ompiRed A; q_T + Q, Q) + Pr[∃ u ∈ L, ¬ P(D(u)) = u],

`L` the challenger's `q_T + Q` uniform targets; the last term is at most `(q_T + Q)·ρ`, `ρ` the
probability that `D` fails on a uniform target (`failRate`; for pqov `δ(sk)^{255}`, §2). The paper's
"tight" T1(c) holds for `D*` (Lemma D), whose aborts are in `ε_D`; with the real sampler they appear
here. The padding is why the target count is `q_T + Q`.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.ROM.OneMore
open scoped ENNReal

namespace VoleMole.Assumptions.IdealTag

open VoleMole.Assumptions.LazyIdeal (simulateQ_proj_eqd simulateQ_inv_bound prEvent_unifList_exists_le₀
  prEvent_le_bind)

open VoleMole.Assumptions.UOV

/-! ## Uniform lists -/

section Lists

variable {T : Type} [SampleableType T]

lemma bind_const_eqd {α β : Type} (mx : ProbComp α) (my : ProbComp β) :
    (mx >>= fun _ => my) =ᵈ my := by
  let : MeasurableSpace β := ⊤
  exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const mx my)

/-- **Union bound over a uniform list, averaged over a key.** -/
theorem prEvent_keyed_unifList_exists_le {K : Type} (kg : ProbComp K) (bad : K → T → Prop) (n : ℕ) :
    Pr{let k ← kg; let L ← unifList T n}[∃ u ∈ L, bad k u] ≤
      n * Pr{let k ← kg; let u ← $ᵗ T}[bad k u] := by
  let : MeasurableSpace K := ⊤
  have e1 := prEvent_bind_eq_lintegral_of_discrete kg (fun k => unifList T n >>= fun L =>
    pure (k, L)) (fun r => ∃ u ∈ r.2, bad r.1 u)
  have e2 := prEvent_bind_eq_lintegral_of_discrete kg (fun k => ($ᵗ T) >>= fun u => pure (k, u))
    (fun r => bad r.1 r.2)
  simp only [bind_pure_comp] at e1 e2
  have e1' : Pr{let k ← kg; let L ← unifList T n}[∃ u ∈ L, bad k u] =
      ∫⁻ k, Pr{let L ← unifList T n}[∃ u ∈ L, bad k u] ∂𝒟[kg] := by
    rw [← prEvent_map] at e1
    simpa [prEvent_map, Function.comp_def] using e1
  have e2' : Pr{let k ← kg; let u ← $ᵗ T}[bad k u] =
      ∫⁻ k, Pr{let u ← $ᵗ T}[bad k u] ∂𝒟[kg] := by
    simpa [prEvent_map, Function.comp_def] using e2
  rw [e1', e2', ← MeasureTheory.lintegral_const_mul _ measurable_from_top]
  exact MeasureTheory.lintegral_mono fun k => prEvent_unifList_exists_le₀ (bad k) n

omit [SampleableType T] in
lemma length_of_mem_unifList' [SampleableType T] :
    ∀ (m : ℕ) (L : List T), L ∈ support (unifList T m) → L.length = m
  | 0, L, h => by simp only [unifList, support_pure, Set.mem_singleton_iff] at h; subst h; rfl
  | m + 1, L, h => by
    simp only [unifList, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨u, -, L', hL', rfl⟩ := h
    simp [length_of_mem_unifList' m L' hL']

/-- **A uniform list of length `a + b`** is a uniform list of length `a` followed by an
independent one of length `b`. -/
theorem unifList_add (b : ℕ) : ∀ a : ℕ,
    unifList T (a + b) = (do let L₁ ← unifList T a; let L₂ ← unifList T b; pure (L₁ ++ L₂))
  | 0 => by simp [unifList]
  | a + 1 => by
    rw [Nat.add_right_comm]
    simp only [unifList, unifList_add b a, bind_assoc, pure_bind, List.cons_append]

end Lists

/-! ## The lazy A-OMPI challenger -/

section Lazy

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {T S : Type} [SampleableType T]

/-- **The lazy A-OMPI challenger**: the state is A-OMPI's (its stream unused) and the number of
targets still allowed; a target request draws a fresh uniform target. -/
def ompiLazy (D : T → S) : QueryImpl (specI AR T S) (StateT (OMPISt AR T × ℕ) ProbComp)
  | .inl d => StateT.mk fun s =>
      (fun r => (r.1, ({ s.1 with ro := r.2 }, s.2))) <$> ((specR AR).randomOracle d).run s.1.ro
  | .inr (.inl ()) => StateT.mk fun s => match s.2 with
      | 0 => pure (none, s)
      | k + 1 => (fun y => (some y, ({ s.1 with ys := s.1.ys ++ [y] }, k))) <$> ($ᵗ T)
  | .inr (.inr i) => StateT.mk fun s =>
      pure ((s.1.ys[i]?).map D, ({ s.1 with opened := i :: s.1.opened, oq := s.1.oq + 1 }, s.2))

/-- The stream challenger's state seen by the lazy one: the stream dropped, its length kept. -/
def forgetS (c : OMPISt AR T) : OMPISt AR T × ℕ := ({ c with rest := [] }, c.rest.length)

/-- **The lazy challenger is the stream challenger**: with a uniform stream of `m` targets, the
two have the same joint distribution of output and (projected) state. -/
theorem ompi_lazy_eqd (D : T → S) {α : Type} (oa : OracleComp (specI AR T S) α) :
    ∀ (c : OMPISt AR T) (m : ℕ),
      (do let L ← unifList T m
          (fun z : α × OMPISt AR T => (z.1, forgetS z.2)) <$>
            (simulateQ (ompiImpl D) oa).run { c with rest := L }) =ᵈ
        (simulateQ (ompiLazy D) oa).run ({ c with rest := [] }, m) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c m
    simp only [simulateQ_pure, StateT.run_pure, map_pure, forgetS]
    refine (EvalDistEq.bind_congr_of_support _ (g := fun _ => pure (x, ({ c with rest := [] }, m)))
      fun L hL => ?_).trans (bind_const_eqd _ _)
    rw [length_of_mem_unifList' m L hL]
  | query_bind q k ih =>
    intro c m
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases q with d | ⟨⟩ | i
    · simp only [ompiImpl, ompiLazy, StateT.run_mk, bind_map_left]
      refine (eqd_swap _ _ _).trans (EvalDistEq.bind_right _ fun r => ?_)
      exact ih r.1 { c with ro := r.2 } m
    · cases m with
      | zero =>
        simp only [unifList, pure_bind, ompiImpl, ompiLazy, StateT.run_mk]
        simpa only [unifList, pure_bind] using ih none c 0
      | succ m =>
        simp only [unifList, bind_assoc, pure_bind, ompiImpl, ompiLazy, StateT.run_mk,
          bind_map_left]
        refine EvalDistEq.bind_right _ fun u => ?_
        exact ih (some u) { c with ys := c.ys ++ [u] } m
    · simp only [ompiImpl, ompiLazy, StateT.run_mk, pure_bind]
      exact ih _ { c with opened := i :: c.opened, oq := c.oq + 1 } m

variable {PK SK : Type} (tr : Trapdoor PK SK T S)

/-- **The A-OMPI experiment with the lazy challenger.** -/
def ompiLazyExp (qT : ℕ) (A : PK → ProbComp (OracleComp (specI AR T S) (ℕ × S))) :
    ProbComp (PK × (ℕ × S) × OMPISt AR T) := do
  let kp ← tr.keyGen
  let a ← A kp.1
  let r ← (simulateQ (ompiLazy (tr.D kp.2)) a).run (ompi0 [], qT)
  pure (kp.1, r.1, r.2.1)

/-- **`Adv^{ompi}` with the lazy challenger.** -/
theorem advOMPI_eq_lazy (qT Q : ℕ) (A : PK → ProbComp (OracleComp (specI AR T S) (ℕ × S))) :
    advOMPI tr qT Q A = Pr{let r ← ompiLazyExp tr qT A}[OMPIWin tr Q r] := by
  have h : (fun r : PK × (ℕ × S) × OMPISt AR T => (r.1, r.2.1, { r.2.2 with rest := [] })) <$>
      ompiExp tr qT A =ᵈ ompiLazyExp tr qT A := by
    simp only [ompiExp, ompiLazyExp, map_bind, map_pure]
    refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun a => ?_
    have := (ompi_lazy_eqd (tr.D kp.2) a (ompi0 []) qT).bind_left
      (fun r => (pure (kp.1, r.1, r.2.1) : ProbComp _))
    simp only [bind_assoc, ompi0, forgetS, bind_map_left] at this ⊢
    exact this
  unfold advOMPI
  rw [← h.prEvent_eq, prEvent_map]
  rfl

end Lazy

/-! ## Theorem 1 (a): det-FDH ≤ A-OMPI -/

section FDHRed

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {M : Type} [DecidableEq M] {T S : Type} [SampleableType T] [Inhabited T] [Inhabited S]

variable (M T) in
/-- The reduction's state: each hashed message's index and target, the next index, and (ghosts,
for the proof) the signed messages and the number of hash queries. -/
structure FRSt where
  tbl : M → Option (ℕ × T)
  next : ℕ
  signed : List M
  hq : ℕ

/-- The reduction's initial state. -/
def fr0 : FRSt M T := ⟨fun _ => none, 0, [], 0⟩

variable (AR T S) in
/-- A-OMPI's "new target" query. -/
def qNew : OracleComp (specI AR T S) (Option T) :=
  liftM ((specI AR T S).query (.inr (.inl ())))

variable (AR T S) in
/-- A-OMPI's index query. -/
def qIdx (i : ℕ) : OracleComp (specI AR T S) (Option S) :=
  liftM ((specI AR T S).query (.inr (.inr i)))

variable (T S) in
/-- A-OMPI's world query. -/
def qW (d : DR) : OracleComp (specI AR T S) (AR d) :=
  liftM ((specI AR T S).query (.inl d))

omit [Inhabited T] [Inhabited S] in
theorem run_qNew (D : T → S) (s : OMPISt AR T × ℕ) :
    (simulateQ (ompiLazy D) (qNew AR T S)).run s = match s.2 with
      | 0 => pure (none, s)
      | k + 1 => (fun y => (some y, ({ s.1 with ys := s.1.ys ++ [y] }, k))) <$> ($ᵗ T) := by
  unfold qNew
  erw [simulateQ_spec_query]
  rfl

omit [Inhabited T] [Inhabited S] in
theorem run_qIdx (D : T → S) (i : ℕ) (s : OMPISt AR T × ℕ) :
    (simulateQ (ompiLazy D) (qIdx AR T S i)).run s =
      pure ((s.1.ys[i]?).map D, ({ s.1 with opened := i :: s.1.opened, oq := s.1.oq + 1 }, s.2)) := by
  unfold qIdx
  erw [simulateQ_spec_query]
  rfl

omit [Inhabited T] [Inhabited S] in
theorem run_qW (D : T → S) (d : DR) (s : OMPISt AR T × ℕ) :
    (simulateQ (ompiLazy D) (qW T S d)).run s =
      (fun r => (r.1, ({ s.1 with ro := r.2 }, s.2))) <$> ((specR AR).randomOracle d).run s.1.ro := by
  unfold qW
  erw [simulateQ_spec_query]
  rfl

variable (AR S) in
/-- det-FDH's hash query. -/
def qH (m : M) : OracleComp (specF AR M T S) T :=
  liftM ((specF AR M T S).query (.inr (.inl m)))

omit [Inhabited T] [Inhabited S] in
theorem run_qH (D : T → S) (m : M) (c : FDHSt AR M T) :
    (simulateQ (fdhImpl D) (qH AR S m)).run c =
      (fun r => (r.1, { r.2 with hq := r.2.hq + 1 })) <$> hStep m c := by
  unfold qH
  erw [simulateQ_spec_query]
  rfl

/-- The index and target of `m`, allocated from a fresh challenge target if needed (`none` once
the targets are used up). -/
def alloc (m : M) (st : FRSt M T) : OracleComp (specI AR T S) (Option (ℕ × T) × FRSt M T) :=
  match st.tbl m with
  | some iy => pure (some iy, st)
  | none => (fun r : Option T => match r with
      | some y => (some (st.next, y),
          { st with tbl := Function.update st.tbl m (some (st.next, y)), next := st.next + 1 })
      | none => (none, st)) <$> qNew AR T S

/-- **The det-FDH-to-A-OMPI reduction's handler**: the world forwarded, `H(m)` the target of `m`,
`Sign(m)` the index oracle at `m`'s index. -/
def fdhRedImpl : QueryImpl (specF AR M T S) (StateT (FRSt M T) (OracleComp (specI AR T S)))
  | .inl d => StateT.mk fun st => (fun a => (a, st)) <$> qW T S d
  | .inr (.inl m) => StateT.mk fun st =>
      (fun r => ((r.1.map Prod.snd).getD default, { r.2 with hq := r.2.hq + 1 })) <$>
        alloc (AR := AR) (S := S) m st
  | .inr (.inr m) => StateT.mk fun st => alloc (AR := AR) (S := S) m st >>= fun r =>
      match r.1 with
      | some iy => (fun a : Option S => ((a.getD default : S), { r.2 with signed := m :: r.2.signed })) <$>
          qIdx AR T S iy.1
      | none => pure ((default : S), { r.2 with signed := m :: r.2.signed })

/-- The forger followed by the hash of its message: `((m*, s*), H(m*))`. -/
def fwd (a : OracleComp (specF AR M T S) (M × S)) : OracleComp (specF AR M T S) ((M × S) × T) :=
  a >>= fun r => (fun t => (r, t)) <$> qH AR S r.1

/-- The reduction's output: the index of `m*` and `s*`. -/
def outI (z : ((M × S) × T) × FRSt M T) : ℕ × S :=
  (((z.2.tbl z.1.1.1).map Prod.fst).getD 0, z.1.1.2)

variable (AR) in
/-- **The A-OMPI adversary `fdhRed A`** of Theorem 1 (a). -/
def fdhRed {PK : Type} (A : PK → ProbComp (OracleComp (specF AR M T S) (M × S))) (pk : PK) :
    ProbComp (OracleComp (specI AR T S) (ℕ × S)) :=
  (fun a => outI <$> (simulateQ fdhRedImpl (fwd a)).run fr0) <$> A pk

/-- The reduction run against the lazy challenger, as one handler. -/
def fdhComb (D : T → S) :
    QueryImpl (specF AR M T S) (StateT (FRSt M T × (OMPISt AR T × ℕ)) ProbComp) :=
  fun q => StateT.mk fun s => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (ompiLazy D) ((fdhRedImpl (S := S) q).run s.1)).run s.2

theorem collapseF (D : T → S) {α : Type} (oa : OracleComp (specF AR M T S) α) (s : FRSt M T)
    (c : OMPISt AR T × ℕ) :
    (simulateQ (ompiLazy D) ((simulateQ fdhRedImpl oa).run s)).run c =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (fdhComb D) oa).run (s, c) := by
  refine simulateQ_StateT_StateT_compose _ _ _ (fun q s c => ?_) oa s c
  show _ = _ <$> ((fun r : (_ × _) × _ => (r.1.1, (r.1.2, r.2))) <$> _)
  rw [Functor.map_map]
  exact (id_map _).symm

/-- The det-FDH state that a reduction state represents. -/
def fdhProj (s : FRSt M T × (OMPISt AR T × ℕ)) : FDHSt AR M T :=
  ⟨s.2.1.ro, fun m => (s.1.tbl m).map Prod.snd, s.1.signed, s.1.hq⟩

/-- The structural invariant of the joint state. -/
structure FInv (s : FRSt M T × (OMPISt AR T × ℕ)) : Prop where
  ys_of : ∀ m i y, s.1.tbl m = some (i, y) → s.2.1.ys[i]? = some y
  inj : ∀ m m' i y y', s.1.tbl m = some (i, y) → s.1.tbl m' = some (i, y') → m = m'
  op : ∀ i ∈ s.2.1.opened, ∃ m ∈ s.1.signed, ∃ y, s.1.tbl m = some (i, y)
  oq : s.2.1.oq ≤ s.1.signed.length
  nx : s.1.next = s.2.1.ys.length

/-- The invariant with a budget: at least `k` targets left. -/
def FInvK (k : ℕ) (s : FRSt M T × (OMPISt AR T × ℕ)) : Prop := k ≤ s.2.2 ∧ FInv s

/-- Hash and signing queries. -/
def isHS (q : DR ⊕ (M ⊕ M)) : Prop := q.isRight = true

instance : DecidablePred (isHS (DR := DR) (M := M)) := fun _ => inferInstanceAs (Decidable (_ = _))

variable (D : T → S)

theorem comb_world (d : DR) (s : FRSt M T × (OMPISt AR T × ℕ)) :
    (fdhComb (S := S) D (.inl d)).run s = (fun r => (r.1, (s.1, ({ s.2.1 with ro := r.2 }, s.2.2)))) <$>
      ((specR AR).randomOracle d).run s.2.1.ro := by
  simp [fdhComb, fdhRedImpl, simulateQ_map, run_qW, Functor.map_map]

theorem comb_hash_some (m : M) (s : FRSt M T × (OMPISt AR T × ℕ)) (i : ℕ) (y : T)
    (h : s.1.tbl m = some (i, y)) :
    (fdhComb (S := S) D (.inr (.inl m))).run s = pure (y, ({ s.1 with hq := s.1.hq + 1 }, s.2)) := by
  simp [fdhComb, fdhRedImpl, alloc, h]

theorem comb_hash_none (m : M) (s : FRSt M T × (OMPISt AR T × ℕ)) (k : ℕ)
    (h : s.1.tbl m = none) (hk : s.2.2 = k + 1) :
    (fdhComb (S := S) D (.inr (.inl m))).run s = (fun y => (y, ({ s.1 with
        tbl := Function.update s.1.tbl m (some (s.1.next, y)), next := s.1.next + 1,
        hq := s.1.hq + 1 }, ({ s.2.1 with ys := s.2.1.ys ++ [y] }, k)))) <$> ($ᵗ T) := by
  simp [fdhComb, fdhRedImpl, alloc, h, simulateQ_map, run_qNew, hk, Functor.map_map]

theorem comb_sign_some (m : M) (s : FRSt M T × (OMPISt AR T × ℕ)) (i : ℕ) (y : T)
    (h : s.1.tbl m = some (i, y)) :
    (fdhComb (S := S) D (.inr (.inr m))).run s =
      pure (((s.2.1.ys[i]?).map D).getD default, ({ s.1 with signed := m :: s.1.signed },
        ({ s.2.1 with opened := i :: s.2.1.opened, oq := s.2.1.oq + 1 }, s.2.2))) := by
  simp [fdhComb, fdhRedImpl, alloc, h, simulateQ_map, run_qIdx]

theorem comb_sign_none (m : M) (s : FRSt M T × (OMPISt AR T × ℕ)) (k : ℕ)
    (h : s.1.tbl m = none) (hk : s.2.2 = k + 1) :
    (fdhComb (S := S) D (.inr (.inr m))).run s = (fun y =>
      ((((s.2.1.ys ++ [y])[s.1.next]?).map D).getD default, ({ s.1 with
        tbl := Function.update s.1.tbl m (some (s.1.next, y)), next := s.1.next + 1,
        signed := m :: s.1.signed },
        ({ s.2.1 with ys := s.2.1.ys ++ [y], opened := s.1.next :: s.2.1.opened, oq := s.2.1.oq + 1 },
          k)))) <$> ($ᵗ T) := by
  simp [fdhComb, fdhRedImpl, alloc, h, simulateQ_map, simulateQ_bind, run_qNew, run_qIdx, hk,
    Functor.map_map, bind_map_left, map_bind]

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [SampleableType T] [Inhabited T]
  [Inhabited S] in
/-- **Allocating a fresh index keeps the invariant.** -/
theorem finv_alloc {st : FRSt M T} {c : OMPISt AR T} {n : ℕ} (hI : FInv (st, (c, n))) (m : M)
    (h : st.tbl m = none) (y : T) (hq' : ℕ) (n' : ℕ) :
    FInv ({ st with tbl := Function.update st.tbl m (some (st.next, y)),
                    next := st.next + 1, hq := hq' }, ({ c with ys := c.ys ++ [y] }, n')) := by
  have hlt : ∀ m' i y', st.tbl m' = some (i, y') → i < c.ys.length := fun m' i y' hm =>
    (List.getElem?_eq_some_iff.1 (hI.ys_of m' i y' hm)).1
  refine ⟨fun m' i y' hm => ?_, fun m₁ m₂ i y₁ y₂ h₁ h₂ => ?_, fun i hi => ?_, hI.oq, ?_⟩
  · dsimp only at hm ⊢
    by_cases hm' : m' = m
    · subst hm'
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      rw [hI.nx, List.getElem?_append_right le_rfl]
      simp
    · rw [Function.update_of_ne hm'] at hm
      rw [List.getElem?_append_left (hlt m' i y' hm)]
      exact hI.ys_of m' i y' hm
  · dsimp only at h₁ h₂
    by_cases e₁ : m₁ = m <;> by_cases e₂ : m₂ = m
    · rw [e₁, e₂]
    · subst e₁
      rw [Function.update_self] at h₁
      rw [Function.update_of_ne e₂] at h₂
      simp only [Option.some.injEq, Prod.mk.injEq] at h₁
      have := hlt _ _ _ h₂
      have hnx : st.next = c.ys.length := hI.nx
      omega
    · subst e₂
      rw [Function.update_self] at h₂
      rw [Function.update_of_ne e₁] at h₁
      simp only [Option.some.injEq, Prod.mk.injEq] at h₂
      have := hlt _ _ _ h₁
      have hnx : st.next = c.ys.length := hI.nx
      omega
    · rw [Function.update_of_ne e₁] at h₁
      rw [Function.update_of_ne e₂] at h₂
      exact hI.inj _ _ _ _ _ h₁ h₂
  · obtain ⟨m', hm', y', hy'⟩ := hI.op i hi
    refine ⟨m', hm', y', ?_⟩
    have hne : m' ≠ m := fun e => by rw [e, h] at hy'; cases hy'
    dsimp only
    rw [Function.update_of_ne hne]
    exact hy'
  · have hnx : st.next = c.ys.length := hI.nx
    simp [hnx]

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [SampleableType T] [Inhabited T]
  [Inhabited S] [DecidableEq M] in
/-- **Opening an allocated index for a signed message keeps the invariant.** -/
theorem finv_sign {st : FRSt M T} {c : OMPISt AR T} {n : ℕ} (hI : FInv (st, (c, n))) (m : M)
    (i : ℕ) (y : T) (h : st.tbl m = some (i, y)) :
    FInv ({ st with signed := m :: st.signed },
      ({ c with opened := i :: c.opened, oq := c.oq + 1 }, n)) := by
  refine ⟨hI.ys_of, hI.inj, fun j hj => ?_, by simpa using hI.oq, hI.nx⟩
  rcases List.mem_cons.1 hj with rfl | hj
  · exact ⟨m, List.mem_cons_self, y, h⟩
  · obtain ⟨m', hm', y', hy'⟩ := hI.op j hj
    exact ⟨m', List.mem_cons_of_mem _ hm', y', hy'⟩

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [SampleableType T] [Inhabited T]
  [Inhabited S] in
lemma proj_update (st : FRSt M T) (m : M) (i : ℕ) (y : T) :
    (fun m' => (Function.update st.tbl m (some (i, y)) m').map Prod.snd) =
      Function.update (fun m' => (st.tbl m').map Prod.snd) m (some y) := by
  funext m'
  by_cases h : m' = m
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- **The programming is perfect, per query**: on the invariant's states, with a target left for
each hash or signing query, the reduction against the lazy challenger answers as det-FDH's
challenger at the projected state. -/
theorem fdh_step (q : DR ⊕ (M ⊕ M)) (s : FRSt M T × (OMPISt AR T × ℕ)) (k : ℕ)
    (hI : FInvK k s) (hk : isHS q → 0 < k) :
    (fun z => (z.1, fdhProj z.2)) <$> (fdhComb D q).run s =ᵈ (fdhImpl D q).run (fdhProj s) := by
  obtain ⟨st, c, n⟩ := s
  suffices e : (fun z => (z.1, fdhProj z.2)) <$> (fdhComb D q).run (st, c, n) =
      (fdhImpl D q).run (fdhProj (st, c, n)) by rw [e]
  rcases q with d | m | m
  · rw [comb_world]
    erw [Functor.map_map]
    rfl
  · have hn : 0 < n := lt_of_lt_of_le (hk rfl) hI.1
    cases h : st.tbl m with
    | some iy =>
      rw [comb_hash_some D m _ iy.1 iy.2 h]
      simp only [fdhImpl, StateT.run_mk, hStep, fdhProj, h, Option.map_some, map_pure]
      rfl
    | none =>
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [comb_hash_none D m _ n' h rfl]
      simp only [fdhImpl, StateT.run_mk, hStep, fdhProj, h, Option.map_none]
      erw [Functor.map_map, Functor.map_map]
      congr 1
      funext y
      simp only [proj_update]
  · have hn : 0 < n := lt_of_lt_of_le (hk rfl) hI.1
    cases h : st.tbl m with
    | some iy =>
      rw [comb_sign_some D m _ iy.1 iy.2 h]
      simp only [fdhImpl, StateT.run_mk, hStep, fdhProj, h, Option.map_some, map_pure,
        hI.2.ys_of m iy.1 iy.2 h, Option.getD_some]
      rfl
    | none =>
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [comb_sign_none D m _ n' h rfl]
      have hnx : st.next = c.ys.length := hI.2.nx
      simp only [fdhImpl, StateT.run_mk, hStep, fdhProj, h, Option.map_none,
        hnx, List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero,
        Option.map_some, Option.getD_some]
      erw [Functor.map_map, Functor.map_map]
      congr 1
      funext y
      rw [← hnx]
      simp only [proj_update]

/-- **The invariant is kept**, one target consumed per hash or signing query. -/
theorem fdh_inv (q : DR ⊕ (M ⊕ M)) (s : FRSt M T × (OMPISt AR T × ℕ)) (k : ℕ)
    (hI : FInvK k s) (hk : isHS q → 0 < k) :
    ∀ z ∈ support ((fdhComb D q).run s), FInvK (if isHS q then k - 1 else k) z.2 := by
  obtain ⟨st, c, n⟩ := s
  intro z hz
  rcases q with d | m | m
  · rw [comb_world] at hz
    erw [support_map] at hz
    obtain ⟨r, -, rfl⟩ := hz
    exact ⟨by simpa [isHS] using hI.1, ⟨hI.2.ys_of, hI.2.inj, hI.2.op, hI.2.oq, hI.2.nx⟩⟩
  · have hn : 0 < n := lt_of_lt_of_le (hk rfl) hI.1
    have hif : (if isHS (Sum.inr (Sum.inl m) : DR ⊕ (M ⊕ M)) then k - 1 else k) = k - 1 := by simp [isHS]
    rw [hif]
    cases h : st.tbl m with
    | some iy =>
      simp only [comb_hash_some D m (st, c, n) iy.1 iy.2 h] at hz
      subst hz
      exact ⟨by simpa using le_trans (Nat.sub_le _ _) hI.1,
        ⟨hI.2.ys_of, hI.2.inj, hI.2.op, hI.2.oq, hI.2.nx⟩⟩
    | none =>
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [comb_hash_none D m (st, c, n' + 1) n' h rfl] at hz
      erw [support_map] at hz
      obtain ⟨y, -, rfl⟩ := hz
      have h1 : k ≤ n' + 1 := hI.1
      exact ⟨by simp only; omega, finv_alloc hI.2 m h y _ n'⟩
  · have hn : 0 < n := lt_of_lt_of_le (hk rfl) hI.1
    have hif : (if isHS (Sum.inr (Sum.inr m) : DR ⊕ (M ⊕ M)) then k - 1 else k) = k - 1 := by simp [isHS]
    rw [hif]
    cases h : st.tbl m with
    | some iy =>
      simp only [comb_sign_some D m (st, c, n) iy.1 iy.2 h] at hz
      subst hz
      exact ⟨by simpa using le_trans (Nat.sub_le _ _) hI.1, finv_sign hI.2 m iy.1 iy.2 h⟩
    | none =>
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [comb_sign_none D m (st, c, n' + 1) n' h rfl] at hz
      erw [support_map] at hz
      obtain ⟨y, -, rfl⟩ := hz
      have h1 : k ≤ n' + 1 := hI.1
      refine ⟨by simp only; omega, ?_⟩
      have ha := finv_alloc hI.2 m h y st.hq n'
      exact finv_sign ha m st.next y (by simp)

omit [Inhabited T] [Inhabited S] in
theorem run_fwd (a : OracleComp (specF AR M T S) (M × S)) (c : FDHSt AR M T) :
    (simulateQ (fdhImpl D) (fwd a)).run c = (simulateQ (fdhImpl D) a).run c >>= fun r =>
      (fun w => ((r.1, w.1), { w.2 with hq := w.2.hq + 1 })) <$> hStep r.1.1 r.2 := by
  simp only [fwd, simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map, run_qH,
    Functor.map_map]

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [Inhabited T] [Inhabited S] in
theorem hStep_support (m : M) (c : FDHSt AR M T) :
    ∀ w ∈ support (hStep m c), w.2.signed = c.signed ∧ w.2.h m = some w.1 := by
  intro w hw
  unfold hStep at hw
  cases h : c.h m with
  | some t =>
    rw [h] at hw
    simp only [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨rfl, h⟩
  | none =>
    rw [h] at hw
    erw [support_map] at hw
    obtain ⟨t, -, rfl⟩ := hw
    simp

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [DecidableEq M] [SampleableType T]
  [Inhabited T] [Inhabited S] in
theorem isQueryBoundP_fwd {a : OracleComp (specF AR M T S) (M × S)} {k : ℕ}
    (ha : IsQueryBoundP a isHS k) : IsQueryBoundP (fwd a) isHS (k + 1) := by
  refine isQueryBoundP_bind ha fun r _ => ?_
  rw [isQueryBoundP_map_iff]
  unfold qH
  erw [isQueryBoundP_query_iff]
  intro
  exact Nat.one_pos

variable {PK SK : Type} (tr : Trapdoor PK SK T S)

/-- The det-FDH win as read off the forger-then-hash run: `m*` unsigned, `s*` a preimage of
`H(m*)` (recorded in the table), at most `q_S` signing queries. -/
def WinF (qS : ℕ) (pk : PK) (z : ((M × S) × T) × FDHSt AR M T) : Prop :=
  z.1.1.1 ∉ z.2.signed ∧ tr.IsPre pk z.1.1.2 z.1.2 ∧ z.2.signed.length ≤ qS ∧ z.2.h z.1.1.1 = some z.1.2

/-- **det-FDH with `H(m*)` queried by the forger itself** (`fwd`): key, forger, the run. -/
def fdhFwdExp (A : PK → ProbComp (OracleComp (specF AR M T S) (M × S))) :
    ProbComp (PK × ((M × S) × T) × FDHSt AR M T) := do
  let kp ← tr.keyGen
  let a ← A kp.1
  let z ← (simulateQ (fdhImpl (tr.D kp.2)) (fwd a)).run fdh0
  pure (kp.1, z)

omit [Inhabited T] [Inhabited S] in
/-- **det-FDH's win, with `H(m*)` queried by the forger itself.** -/
theorem advFDH_le_fwd (qH qS : ℕ) (A : PK → ProbComp (OracleComp (specF AR M T S) (M × S))) :
    advFDH tr qH qS A ≤ Pr{let x ← fdhFwdExp tr A}[WinF tr qS x.1 x.2] := by
  let G : ProbComp (PK × (M × S) × T × FDHSt AR M T × FDHSt AR M T) := do
    let kp ← tr.keyGen
    let a ← A kp.1
    let r ← (simulateQ (fdhImpl (tr.D kp.2)) a).run fdh0
    let w ← hStep r.1.1 r.2
    pure (kp.1, r.1, w.1, r.2, w.2)
  have h1 : fdhExp tr A = (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1)) <$> G := by
    simp [G, fdhExp, map_bind]
  have h2 : fdhFwdExp tr A =
      (fun x => (x.1, ((x.2.1, x.2.2.1), { x.2.2.2.2 with hq := x.2.2.2.2.hq + 1 }))) <$> G := by
    simp [G, fdhFwdExp, run_fwd, map_bind]
  unfold advFDH
  rw [h1, h2, prEvent_map, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun x hx hw => ?_
  simp only [G, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨kp, -, a, -, r, -, w, hw', rfl⟩ := hx
  obtain ⟨hs, hh⟩ := hStep_support r.1.1 r.2 w hw'
  obtain ⟨hn, hp, -, hq⟩ := hw
  exact ⟨by simpa [hs] using hn, hp, by simpa [hs] using hq, hh⟩

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [SampleableType T] [Inhabited T]
  [Inhabited S] [DecidableEq M] in
theorem finvK_init (n : ℕ) : FInvK n ((fr0, (ompi0 [], n)) : FRSt M T × (OMPISt AR T × ℕ)) :=
  ⟨le_rfl, ⟨fun _ _ _ h => (by simp [fr0] at h), fun _ _ _ _ _ h => (by simp [fr0] at h),
    fun _ h => (by simp [ompi0] at h), le_rfl, rfl⟩⟩

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [SampleableType T] [Inhabited T]
  [Inhabited S] [DecidableEq M] in
theorem fdhProj_init (n : ℕ) :
    fdhProj ((fr0, (ompi0 [], n)) : FRSt M T × (OMPISt AR T × ℕ)) = fdh0 := rfl

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [SampleableType T] [Inhabited T]
  [Inhabited S] [DecidableEq M] in
/-- **A det-FDH win is an A-OMPI win** of the reduction, on the invariant's states. -/
theorem winF_imp (qS : ℕ) (pk : PK) (z : ((M × S) × T) × FRSt M T × (OMPISt AR T × ℕ))
    (hI : FInv z.2) (hw : WinF tr qS pk (z.1, fdhProj z.2)) :
    OMPIWin tr qS (pk, outI (z.1, z.2.1), z.2.2.1) := by
  obtain ⟨⟨⟨m, s⟩, t⟩, st, c, n⟩ := z
  obtain ⟨hn, hp, hl, hh⟩ := hw
  simp only [fdhProj, Option.map_eq_some_iff] at hn hp hl hh
  obtain ⟨⟨i, t'⟩, hi, rfl⟩ := hh
  refine ⟨t', ?_, fun ho => ?_, hp, le_trans hI.oq hl⟩
  · simp only [outI, hi, Option.map_some, Option.getD_some]
    exact hI.ys_of m i t' hi
  · simp only [outI, hi, Option.map_some, Option.getD_some] at ho
    obtain ⟨m', hm', y', hy'⟩ := hI.op i ho
    exact hn (hI.inj m' m i y' t' hy' hi ▸ hm')

/-- **Theorem 1 (a): det-FDH ≤ A-OMPI**, tightly. For a det-FDH forger with at most `k` hash and
signing queries on every path, the reduction `fdhRed AR A` (each fresh hash a fresh challenge
target, each signing query an index query, the forgery `(m*, s*)` named by `m*`'s index) wins
A-OMPI with `k + 1` targets and `q_S` index queries at least as often. -/
theorem advFDH_le_ompi (qH qS k : ℕ) (A : PK → ProbComp (OracleComp (specF AR M T S) (M × S)))
    (hA : ∀ pk, ∀ a ∈ support (A pk), IsQueryBoundP a isHS k) :
    advFDH tr qH qS A ≤ advOMPI tr (k + 1) qS (fdhRed AR A) := by
  refine (advFDH_le_fwd tr qH qS A).trans ?_
  rw [advOMPI_eq_lazy]
  let H : ProbComp (PK × (((M × S) × T) × FRSt M T × (OMPISt AR T × ℕ))) := do
    let kp ← tr.keyGen
    let a ← A kp.1
    let z ← (simulateQ (fdhComb (tr.D kp.2)) (fwd a)).run (fr0, (ompi0 [], k + 1))
    pure (kp.1, z)
  have e1 : fdhFwdExp tr A =ᵈ (fun x => (x.1, (x.2.1, fdhProj x.2.2))) <$> H := by
    simp only [fdhFwdExp, H, map_bind, map_pure]
    refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_congr_of_support _ fun a ha => ?_
    have h := (simulateQ_proj_eqd (fdhComb (tr.D kp.2)) (fdhImpl (tr.D kp.2)) fdhProj isHS FInvK
      (fdh_step _) (fdh_inv _) (fwd a) (k + 1) _ (isQueryBoundP_fwd (hA kp.1 a ha))
      (finvK_init (k + 1))).symm.bind_left (fun z => (pure (kp.1, z) : ProbComp _))
    rw [fdhProj_init] at h
    simpa only [bind_map_left] using h
  have e2 : ompiLazyExp tr (k + 1) (fdhRed AR A) =
      (fun x => (x.1, outI (x.2.1, x.2.2.1), x.2.2.2.1)) <$> H := by
    simp [ompiLazyExp, fdhRed, H, simulateQ_map, collapseF, map_bind]
  rw [e1.prEvent_eq, e2, prEvent_map, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun x hx hw => ?_
  simp only [H, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨kp, -, a, ha, z, hz, rfl⟩ := hx
  obtain ⟨k', hI⟩ := simulateQ_inv_bound (fdhComb (tr.D kp.2)) isHS FInvK (fdh_inv _) (fwd a)
    (k + 1) _ (isQueryBoundP_fwd (hA kp.1 a ha)) (finvK_init (k + 1)) z hz
  exact winF_imp tr qS kp.1 z hI.2 hw

end FDHRed

end VoleMole.Assumptions.IdealTag

namespace VoleMole.Assumptions.IdealTag

open VoleMole.Assumptions.LazyIdeal (simulateQ_proj_eqd simulateQ_inv_bound prEvent_unifList_exists_le₀
  prEvent_le_bind)

open VoleMole.Assumptions.UOV

/-! ## Theorem 1 (c): A-OMPI ≤ OMPR -/

section Helpers

/-- With no query of a kind that is never asked, every computation is within budget `0`. -/
theorem isQueryBoundP_false {ι : Type} {spec : OracleSpec ι} {α : Type} (oa : OracleComp spec α) :
    IsQueryBoundP oa (fun _ => False) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => trivial
  | query_bind t f ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl not_false, fun u => by simp [ih u]⟩

end Helpers

section OMPIRed

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {T S : Type} [SampleableType T]

variable (T S) in
/-- The OMPR reduction's state: the issued targets (in order), the answered index queries (a
cache), and (ghosts) the opened indices and the number of index queries. -/
structure ORSt where
  ys : List T
  ans : List (ℕ × S)
  opened : List ℕ
  oq : ℕ

/-- The reduction's initial state. -/
def or0 : ORSt T S := ⟨[], [], [], 0⟩

variable (AR T S) in
/-- OMPR's challenge query, under the label `x`. -/
def qChal (x : ℕ) : OracleComp (specB AR ℕ Unit T S) (Option T) :=
  liftM ((specB AR ℕ Unit T S).query (.inr (.inl (x, ()))))

variable (AR T S) in
/-- OMPR's preimage query. -/
def qPre (t : T) : OracleComp (specB AR ℕ Unit T S) S :=
  liftM ((specB AR ℕ Unit T S).query (.inr (.inr t)))

variable (T S) in
/-- OMPR's world query. -/
def qWB (d : DR) : OracleComp (specB AR ℕ Unit T S) (AR d) :=
  liftM ((specB AR ℕ Unit T S).query (.inl d))

omit [SampleableType T] in
theorem run_qChal (D : T → S) (x : ℕ) (c : Ch AR ℕ Unit T) :
    (simulateQ (chImpl D) (qChal AR T S x)).run c = pure (match c.rest with
      | u :: r => (some u, { c with rest := r, tg := Function.update c.tg x (some (u, ())) })
      | [] => (none, c)) := by
  unfold qChal
  erw [simulateQ_spec_query]
  rfl

omit [SampleableType T] in
theorem run_qPre (D : T → S) (t : T) (c : Ch AR ℕ Unit T) :
    (simulateQ (chImpl D) (qPre AR T S t)).run c = pure (D t, { c with iq := c.iq + 1 }) := by
  unfold qPre
  erw [simulateQ_spec_query]
  rfl

omit [SampleableType T] in
theorem run_qWB (D : T → S) (d : DR) (c : Ch AR ℕ Unit T) :
    (simulateQ (chImpl D) (qWB T S d)).run c =
      (fun r => (r.1, { c with ro := r.2 })) <$> ((specR AR).randomOracle d).run c.ro := by
  unfold qWB
  erw [simulateQ_spec_query]
  rfl

/-- **The A-OMPI-to-OMPR reduction's handler**: the world forwarded; a target request forwarded
under the next index as label while fewer than `q_T` targets were issued; an index query answered
from the cache, or by the preimage oracle at the indexed target. -/
def ompiRedImpl (qT : ℕ) :
    QueryImpl (specI AR T S) (StateT (ORSt T S) (OracleComp (specB AR ℕ Unit T S)))
  | .inl d => StateT.mk fun st => (fun a => (a, st)) <$> qWB T S d
  | .inr (.inl ()) => StateT.mk fun st =>
      if st.ys.length < qT then
        (fun r : Option T => match r with
          | some y => (some y, { st with ys := st.ys ++ [y] })
          | none => (none, st)) <$> qChal AR T S st.ys.length
      else pure (none, st)
  | .inr (.inr i) => StateT.mk fun st =>
      match st.ans.lookup i with
      | some a => pure (some a, { st with opened := i :: st.opened, oq := st.oq + 1 })
      | none => match st.ys[i]? with
        | some y => (fun a : S => (some a,
            { st with ans := st.ans ++ [(i, a)], opened := i :: st.opened, oq := st.oq + 1 })) <$>
              qPre AR T S y
        | none => pure (none, { st with opened := i :: st.opened, oq := st.oq + 1 })

/-- **Padding**: `j` further targets, under the labels `b, b + 1, …`, and their preimages. -/
def padC : ℕ → ℕ → OracleComp (specB AR ℕ Unit T S) (List (ℕ × S))
  | 0, _ => pure []
  | j + 1, b => qChal AR T S b >>= fun r => match r with
    | some u => qPre AR T S u >>= fun a => (fun l => (b, a) :: l) <$> padC j (b + 1)
    | none => pure []

variable (AR) in
/-- **The OMPR adversary `ompiRed qT Q A`** of Theorem 1 (c): `A` against the reduction's handler,
then its forgery, the answered index queries and `Q − (answered)` padding claims. -/
def ompiRed (qT Q : ℕ) {PK : Type} (A : PK → ProbComp (OracleComp (specI AR T S) (ℕ × S)))
    (pk : PK) : ProbComp (OracleComp (specB AR ℕ Unit T S) (List (ℕ × S))) :=
  (fun a => (simulateQ (ompiRedImpl qT) a).run or0 >>= fun r =>
    (fun pads => r.1 :: r.2.ans ++ pads) <$> padC (Q - r.2.ans.length) r.2.ys.length) <$> A pk

/-- The reduction run against OMPR's challenger, as one handler. -/
def ompiComb (qT : ℕ) (D : T → S) :
    QueryImpl (specI AR T S) (StateT (ORSt T S × Ch AR ℕ Unit T) ProbComp) :=
  fun q => StateT.mk fun s => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (chImpl D) ((ompiRedImpl qT q).run s.1)).run s.2

omit [SampleableType T] in
theorem collapseO (qT : ℕ) (D : T → S) {α : Type} (oa : OracleComp (specI AR T S) α)
    (s : ORSt T S) (c : Ch AR ℕ Unit T) :
    (simulateQ (chImpl D) ((simulateQ (ompiRedImpl qT) oa).run s)).run c =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (ompiComb qT D) oa).run (s, c) := by
  refine simulateQ_StateT_StateT_compose _ _ _ (fun q s c => ?_) oa s c
  show _ = _ <$> ((fun r : (_ × _) × _ => (r.1.1, (r.1.2, r.2))) <$> _)
  rw [Functor.map_map]
  exact (id_map _).symm

/-- The A-OMPI state that a joint state represents: the challenger's first `q_T − |ys|` remaining
targets are A-OMPI's stream. -/
def ompiProj (qT : ℕ) (s : ORSt T S × Ch AR ℕ Unit T) : OMPISt AR T :=
  ⟨s.2.ro, s.2.rest.take (qT - s.1.ys.length), s.1.ys, s.1.opened, s.1.oq⟩

/-- **The invariant of the joint state**, for the challenger's stream `L`. -/
structure OInv (D : T → S) (qT : ℕ) (L : List T) (s : ORSt T S × Ch AR ℕ Unit T) : Prop where
  cache : ∀ p ∈ s.1.ans, (s.1.ys[p.1]?).map D = some p.2
  nodup : (s.1.ans.map Prod.fst).Nodup
  opened : ∀ p ∈ s.1.ans, p.1 ∈ s.1.opened
  iq : s.2.iq = s.1.ans.length
  oq : s.1.ans.length ≤ s.1.oq
  tg : ∀ i y, s.1.ys[i]? = some y → s.2.tg i = some (y, ())
  fresh : ∀ x, s.1.ys.length ≤ x → s.2.tg x = none
  stream : s.1.ys ++ s.2.rest = L
  cap : s.1.ys.length ≤ qT

omit [SampleableType T] in
theorem ocomb_world (qT : ℕ) (D : T → S) (d : DR) (st : ORSt T S) (c : Ch AR ℕ Unit T) :
    (ompiComb qT D (.inl d)).run (st, c) =
      (fun r => (r.1, (st, { c with ro := r.2 }))) <$> ((specR AR).randomOracle d).run c.ro := by
  simp [ompiComb, ompiRedImpl, simulateQ_map, run_qWB, Functor.map_map]

omit [SampleableType T] in
theorem ocomb_chal (qT : ℕ) (D : T → S) (st : ORSt T S) (c : Ch AR ℕ Unit T) :
    (ompiComb qT D (.inr (.inl ()))).run (st, c) =
      if st.ys.length < qT then pure (match c.rest with
        | u :: r => (some u, ({ st with ys := st.ys ++ [u] },
            { c with rest := r, tg := Function.update c.tg st.ys.length (some (u, ())) }))
        | [] => (none, (st, c)))
      else pure (none, (st, c)) := by
  by_cases h : st.ys.length < qT
  · simp only [ompiComb, ompiRedImpl, StateT.run_mk, h, ite_true, simulateQ_map, StateT.run_map,
      run_qChal, map_pure]
    cases c.rest <;> rfl
  · simp [ompiComb, ompiRedImpl, h]

omit [SampleableType T] in
theorem ocomb_idx (qT : ℕ) (D : T → S) (i : ℕ) (st : ORSt T S) (c : Ch AR ℕ Unit T) :
    (ompiComb qT D (.inr (.inr i))).run (st, c) = match st.ans.lookup i with
      | some a => pure (some a, ({ st with opened := i :: st.opened, oq := st.oq + 1 }, c))
      | none => match st.ys[i]? with
        | some y => pure (some (D y),
            ({ st with ans := st.ans ++ [(i, D y)], opened := i :: st.opened, oq := st.oq + 1 },
              { c with iq := c.iq + 1 }))
        | none => pure (none, ({ st with opened := i :: st.opened, oq := st.oq + 1 }, c)) := by
  cases h : st.ans.lookup i with
  | some a => simp [ompiComb, ompiRedImpl, h]
  | none =>
    cases hy : st.ys[i]? with
    | some y =>
      simp only [ompiComb, ompiRedImpl, StateT.run_mk, h, hy, simulateQ_map, StateT.run_map,
        run_qPre, map_pure]
    | none => simp [ompiComb, ompiRedImpl, h, hy]

omit [SampleableType T] in
theorem lookup_mem {i : ℕ} {a : S} {l : List (ℕ × S)} (h : l.lookup i = some a) : (i, a) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨j, b⟩ := p
    by_cases hj : i = j
    · subst hj; simp [List.lookup] at h; subst h; simp
    · have : (i == j) = false := by simpa using hj
      simp [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (ih h)

omit [SampleableType T] in
theorem lookup_none {i : ℕ} {l : List (ℕ × S)} (h : l.lookup i = none) : i ∉ l.map Prod.fst := by
  induction l with
  | nil => simp
  | cons p l ih =>
    obtain ⟨j, b⟩ := p
    by_cases hj : i = j
    · subst hj; simp [List.lookup] at h
    · have : (i == j) = false := by simpa using hj
      simp only [List.lookup, this] at h
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨hj, ih h⟩

omit [SampleableType T] in
/-- **The reduction answers as A-OMPI's challenger, per query**, at the projected state. -/
theorem ompi_step (qT : ℕ) (D : T → S) (L : List T) (q : DR ⊕ (Unit ⊕ ℕ))
    (s : ORSt T S × Ch AR ℕ Unit T) (hI : OInv D qT L s) :
    (fun z => (z.1, ompiProj qT z.2)) <$> (ompiComb qT D q).run s =ᵈ
      (ompiImpl D q).run (ompiProj qT s) := by
  obtain ⟨st, c⟩ := s
  suffices e : (fun z => (z.1, ompiProj qT z.2)) <$> (ompiComb qT D q).run (st, c) =
      (ompiImpl D q).run (ompiProj qT (st, c)) by rw [e]
  rcases q with d | ⟨⟩ | i
  · rw [ocomb_world]
    erw [Functor.map_map]
    rfl
  · rw [ocomb_chal]
    by_cases h : st.ys.length < qT
    · obtain ⟨j, hj⟩ : ∃ j, qT - st.ys.length = j + 1 := ⟨qT - st.ys.length - 1, by omega⟩
      have hj' : qT - (st.ys.length + 1) = j := by omega
      cases hr : c.rest with
      | nil => simp [h, hr, ompiImpl, ompiProj]
      | cons u r => simp [h, hr, ompiImpl, ompiProj, hj, hj']
    · have h0 : qT - st.ys.length = 0 := by omega
      simp [h, ompiImpl, ompiProj, h0]
  · rw [ocomb_idx]
    cases hl : st.ans.lookup i with
    | some a =>
      have hc := hI.cache _ (lookup_mem hl)
      simp only [map_pure, ompiImpl, ompiProj, StateT.run_mk]
      simp only at hc
      rw [hc]
    | none =>
      cases hy : st.ys[i]? with
      | some y => simp [ompiImpl, ompiProj, hy]
      | none => simp [ompiImpl, ompiProj, hy]

omit [SampleableType T] in
/-- **The invariant is kept.** -/
theorem ompi_inv (qT : ℕ) (D : T → S) (L : List T) (q : DR ⊕ (Unit ⊕ ℕ))
    (s : ORSt T S × Ch AR ℕ Unit T) (hI : OInv D qT L s) :
    ∀ z ∈ support ((ompiComb qT D q).run s), OInv D qT L z.2 := by
  obtain ⟨st, c⟩ := s
  intro z hz
  rcases q with d | ⟨⟩ | i
  · rw [ocomb_world] at hz
    erw [support_map] at hz
    obtain ⟨r, -, rfl⟩ := hz
    exact ⟨hI.cache, hI.nodup, hI.opened, hI.iq, hI.oq, hI.tg, hI.fresh, hI.stream, hI.cap⟩
  · rw [ocomb_chal] at hz
    by_cases h : st.ys.length < qT
    · cases hr : c.rest with
      | nil =>
        simp only [h, hr, ite_true] at hz
        subst hz; exact hI
      | cons u r =>
        simp only [h, hr, ite_true] at hz
        subst hz
        have hlt : ∀ i y, st.ys[i]? = some y → i < st.ys.length := fun i y hy =>
          (List.getElem?_eq_some_iff.1 hy).1
        refine ⟨fun p hp => ?_, hI.nodup, hI.opened, hI.iq, hI.oq, fun i y hy => ?_,
          fun x hx => ?_, ?_, ?_⟩
        · have hc := hI.cache p hp
          obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 hc
          simp only
          rw [List.getElem?_append_left (hlt _ _ hy)]
          exact hc
        · simp only at hy ⊢
          by_cases hi : i < st.ys.length
          · rw [List.getElem?_append_left hi] at hy
            rw [Function.update_of_ne (by omega)]
            exact hI.tg i y hy
          · have hi' : i = st.ys.length := by
              have := (List.getElem?_eq_some_iff.1 hy).1
              simp at this; omega
            subst hi'
            rw [List.getElem?_append_right le_rfl] at hy
            simp at hy
            subst hy
            simp
        · simp only at hx ⊢
          simp only [List.length_append, List.length_singleton] at hx
          rw [Function.update_of_ne (by omega)]
          exact hI.fresh x (show st.ys.length ≤ x by omega)
        · have := hI.stream
          simp only [hr] at this ⊢
          simpa using this
        · simp only [List.length_append, List.length_singleton]; omega
    · simp only [h, ite_false] at hz
      subst hz; exact hI
  · rw [ocomb_idx] at hz
    cases hl : st.ans.lookup i with
    | some a =>
      simp only [hl, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hI.cache, hI.nodup, fun p hp => List.mem_cons_of_mem _ (hI.opened p hp), hI.iq,
        Nat.le_succ_of_le hI.oq, hI.tg, hI.fresh, hI.stream, hI.cap⟩
    | none =>
      cases hy : st.ys[i]? with
      | some y =>
        simp only [hl, hy, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨fun p hp => ?_, ?_, fun p hp => ?_, ?_, ?_, hI.tg, hI.fresh, hI.stream, hI.cap⟩
        · rcases List.mem_append.1 hp with hp | hp
          · exact hI.cache p hp
          · simp only [List.mem_singleton] at hp; subst hp; simp [hy]
        · simp only [List.map_append, List.map_cons, List.map_nil]
          exact List.nodup_append.2 ⟨hI.nodup, List.nodup_singleton _,
            fun a ha b hb => by simp at hb; subst hb; exact fun e => lookup_none hl (e ▸ ha)⟩
        · rcases List.mem_append.1 hp with hp | hp
          · exact List.mem_cons_of_mem _ (hI.opened p hp)
          · simp only [List.mem_singleton] at hp; subst hp; exact List.mem_cons_self
        · have h1 : c.iq = st.ans.length := hI.iq
          simp [h1]
        · have h1 : st.ans.length ≤ st.oq := hI.oq
          simp only [List.length_append, List.length_singleton]; omega
      | none =>
        simp only [hl, hy, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨hI.cache, hI.nodup, fun p hp => List.mem_cons_of_mem _ (hI.opened p hp), hI.iq,
          Nat.le_succ_of_le hI.oq, hI.tg, hI.fresh, hI.stream, hI.cap⟩

omit [SampleableType T] in
/-- **What padding produces**: with at least `j` targets left and the labels from `b` on unused,
`j` claims on the distinct labels `≥ b`, each the preimage oracle's answer `D(u)` at the target `u`
recorded under its label (one of the remaining targets), after exactly `j` more preimage queries;
the labels below `b` are untouched. -/
theorem pad_spec (D : T → S) : ∀ (j b : ℕ) (c : Ch AR ℕ Unit T), j ≤ c.rest.length →
    (∀ x, b ≤ x → c.tg x = none) →
    ∀ w ∈ support ((simulateQ (chImpl D) (padC j b)).run c),
      w.1.length = j ∧ (∀ p ∈ w.1, b ≤ p.1) ∧ (w.1.map Prod.fst).Nodup ∧ w.2.iq = c.iq + j ∧
        (∀ x < b, w.2.tg x = c.tg x) ∧
        (∀ p ∈ w.1, ∃ u ∈ c.rest, w.2.tg p.1 = some (u, ()) ∧ p.2 = D u)
  | 0, b, c, _, _, w, hw => by
    simp only [padC, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    simp
  | j + 1, b, c, hj, hf, w, hw => by
    cases hr : c.rest with
    | nil => rw [hr] at hj; simp at hj
    | cons u r =>
      rw [hr] at hj
      simp only [padC, simulateQ_bind, StateT.run_bind, run_qChal, hr, pure_bind, run_qPre,
        simulateQ_map, StateT.run_map] at hw
      erw [support_map] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      set c2 : Ch AR ℕ Unit T := ⟨c.ro, r, Function.update c.tg b (some (u, ())), c.iq + 1⟩ with hc2
      have ih := pad_spec D j (b + 1) c2 (by simp [c2]; simp at hj; omega)
        (fun x hx => by
          simp only [c2]
          rw [Function.update_of_ne (by omega)]
          exact hf x (by omega)) w' hw'
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
      refine ⟨by simp [h1], ?_, ?_, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact le_rfl
        · exact le_trans (Nat.le_succ b) (h2 p hp)
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun hb => ?_, h3⟩
        obtain ⟨p, hp, he⟩ := List.mem_map.1 hb
        have := h2 p hp
        omega
      · simp only [h4, c2]; omega
      · intro x hx
        rw [h5 x (by omega)]
        simp only [c2]
        rw [Function.update_of_ne (by omega)]
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · refine ⟨u, List.mem_cons_self, ?_, rfl⟩
          rw [h5 b (by omega)]
          simp [c2]
        · obtain ⟨u', hu', ht, hd⟩ := h6 p hp
          exact ⟨u', List.mem_cons_of_mem _ hu', ht, hd⟩

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [SampleableType T] in
theorem oinv_init (D : T → S) (qT : ℕ) (L : List T) :
    OInv D qT L ((or0, ch0 L) : ORSt T S × Ch AR ℕ Unit T) :=
  ⟨fun _ h => by simp [or0] at h, by simp [or0], fun _ h => by simp [or0] at h, rfl, le_rfl,
    fun _ _ h => by simp [or0] at h, fun _ _ => rfl, rfl, Nat.zero_le _⟩

variable {PK SK : Type} (tr : Trapdoor PK SK T S)

omit [SampleableType T] in
/-- **An A-OMPI win, with every target of the challenger good, is an OMPR win after padding.** -/
theorem ompiWin_imp (qT Q : ℕ) (pk : PK) (sk : SK) (L : List T) (hL : L.length = qT + Q)
    (z : (ℕ × S) × ORSt T S × Ch AR ℕ Unit T) (hI : OInv (tr.D sk) qT L z.2)
    (hw : OMPIWin tr Q (pk, z.1, ompiProj qT z.2))
    (hg : ∀ u ∈ L, tr.IsPre pk (tr.D sk u) u)
    (w : List (ℕ × S) × Ch AR ℕ Unit T)
    (hwp : w ∈ support ((simulateQ (chImpl (tr.D sk))
      (padC (Q - z.2.1.ans.length) z.2.1.ys.length)).run z.2.2)) :
    Wins Q (goodPre tr.IsPre) pk (z.1 :: z.2.1.ans ++ w.1) w.2 := by
  obtain ⟨⟨i, s⟩, st, c⟩ := z
  obtain ⟨y, hy, hno, hpre, hoq⟩ := hw
  simp only [ompiProj] at hy hno hpre hoq
  have hans : st.ans.length ≤ Q := le_trans hI.oq hoq
  have hrest : Q - st.ans.length ≤ c.rest.length := by
    have h1 := congrArg List.length hI.stream
    simp only [List.length_append] at h1
    have h2 : st.ys.length ≤ qT := hI.cap
    omega
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ :=
    pad_spec (tr.D sk) (Q - st.ans.length) st.ys.length c hrest hI.fresh w hwp
  have hilt : i < st.ys.length := (List.getElem?_eq_some_iff.1 hy).1
  have halt : ∀ p ∈ st.ans, p.1 < st.ys.length := fun p hp => by
    obtain ⟨y', hy', -⟩ := Option.map_eq_some_iff.1 (hI.cache p hp)
    exact (List.getElem?_eq_some_iff.1 hy').1
  have hmemL : ∀ u ∈ st.ys, u ∈ L := fun u hu => by
    rw [← hI.stream]; exact List.mem_append_left _ hu
  have hrestL : ∀ u ∈ c.rest, u ∈ L := fun u hu => by
    rw [← hI.stream]; exact List.mem_append_right _ hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [List.cons_append, List.length_cons, List.length_append, p1]; omega
  · simp only [List.cons_append, List.map_cons, List.map_append, List.nodup_cons, List.mem_append,
      not_or]
    refine ⟨⟨fun hm => ?_, fun hm => ?_⟩, List.nodup_append.2 ⟨hI.nodup, p3, ?_⟩⟩
    · obtain ⟨p, hp, he⟩ := List.mem_map.1 hm
      exact hno (he ▸ hI.opened p hp)
    · obtain ⟨p, hp, he⟩ := List.mem_map.1 hm
      have := p2 p hp
      omega
    · intro a ha b hb e
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hb
      have := halt p hp
      have := p2 q hq
      omega
  · have h1 : c.iq = st.ans.length := hI.iq
    rw [p4, h1]; omega
  · intro p hp
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hp
    rcases hp with rfl | hp | hp
    · refine ⟨y, (), ?_, hpre⟩
      rw [p5 _ hilt]
      exact hI.tg _ _ hy
    · obtain ⟨y', hy', he⟩ := Option.map_eq_some_iff.1 (hI.cache p hp)
      refine ⟨y', (), ?_, ?_⟩
      · rw [p5 _ (halt p hp)]; exact hI.tg _ _ hy'
      · rw [← he]; exact hg y' (hmemL y' (List.mem_of_getElem? hy'))
    · obtain ⟨u, hu, ht, hd⟩ := p6 p hp
      exact ⟨u, (), ht, hd ▸ hg u (hrestL u hu)⟩

/-- **The probability that `D` errs on one of `n` uniform targets** (for the key of `keyGen`):
the price of Theorem 1 (c) with a sampler that may fail. -/
noncomputable def badTargets (n : ℕ) : ℝ≥0∞ :=
  Pr{let kp ← tr.keyGen; let L ← unifList T n}[∃ u ∈ L, ¬tr.IsPre kp.1 (tr.D kp.2 u) u]

/-- **`ρ`: the probability that `D` errs on one uniform target.** -/
noncomputable def failRate : ℝ≥0∞ :=
  Pr{let kp ← tr.keyGen; let u ← $ᵗ T}[¬tr.IsPre kp.1 (tr.D kp.2 u) u]

theorem badTargets_le (n : ℕ) : badTargets tr n ≤ n * failRate tr :=
  prEvent_keyed_unifList_exists_le tr.keyGen (fun kp u => ¬tr.IsPre kp.1 (tr.D kp.2 u) u) n

/-- **Theorem 1 (c): A-OMPI ≤ OMPR**, for every A-OMPI adversary and every trapdoor:

    Adv^{ompi}(A; q_T, Q) ≤ Adv^{ompr}(ompiRed A; q_T + Q, Q) + Pr[D errs on one of q_T + Q targets].

The reduction caches the index queries (so it makes at most `Q` preimage queries) and pads to
exactly `Q + 1` claims with fresh targets. -/
theorem advOMPI_le_ompr (qT Q : ℕ) (A : PK → ProbComp (OracleComp (specI AR T S) (ℕ × S))) :
    advOMPI tr qT Q A ≤ advOMPR tr (qT + Q) Q (ompiRed AR qT Q A) + badTargets tr (qT + Q) := by
  let J : ProbComp ((PK × SK) × List T × ((ℕ × S) × ORSt T S × Ch AR ℕ Unit T)) := do
    let kp ← tr.keyGen
    let a ← A kp.1
    let L ← unifList T (qT + Q)
    let z ← (simulateQ (ompiComb qT (tr.D kp.2)) a).run (or0, ch0 L)
    pure (kp, L, z)
  let F : (PK × SK) × List T × ((ℕ × S) × ORSt T S × Ch AR ℕ Unit T) →
      ProbComp (PK × List (ℕ × S) × Ch AR ℕ Unit T) := fun x =>
    (fun w => (x.1.1, x.2.2.1 :: x.2.2.2.1.ans ++ w.1, w.2)) <$>
      (simulateQ (chImpl (tr.D x.1.2))
        (padC (Q - x.2.2.2.1.ans.length) x.2.2.2.1.ys.length)).run x.2.2.2.2
  -- the A-OMPI experiment, through the reduction
  have hE : ompiExp tr qT A =ᵈ (fun x => (x.1.1, x.2.2.1, ompiProj qT x.2.2.2)) <$> J := by
    simp only [ompiExp, J, map_bind, map_pure]
    refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun a => ?_
    rw [unifList_add, bind_assoc]
    refine EvalDistEq.symm (EvalDistEq.bind_congr_of_support _ fun L1 hL1 => ?_)
    simp only [bind_assoc, pure_bind]
    refine (EvalDistEq.bind_right _ fun L2 => ?_).trans (EvalDistEq.bind_const _ _)
    have h := (simulateQ_proj_eqd (ompiComb qT (tr.D kp.2)) (ompiImpl (tr.D kp.2)) (ompiProj qT)
      (fun _ => False) (fun _ s => OInv (tr.D kp.2) qT (L1 ++ L2) s)
      (fun q s _ hI _ => ompi_step qT _ _ q s hI) (fun q s _ hI _ => by
        simpa using ompi_inv qT _ _ q s hI) a 0 _ (isQueryBoundP_false a)
      (oinv_init _ qT (L1 ++ L2))).bind_left (fun z => (pure (kp.1, z.1, z.2) : ProbComp _))
    have hp : ompiProj qT ((or0, ch0 (L1 ++ L2)) : ORSt T S × Ch AR ℕ Unit T) = ompi0 L1 := by
      have := length_of_mem_unifList' qT L1 hL1
      simp [ompiProj, or0, ch0, ompi0, ← this]
    rw [hp] at h
    simpa only [bind_map_left] using h
  -- the OMPR experiment is `J` followed by the padding
  have hO : omExp tr.keyGen tr.D (qT + Q) (ompiRed AR qT Q A) = J >>= F := by
    simp only [omExp, ompiRed, J, F, bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
      collapseO, map_eq_bind_pure_comp, Function.comp_def, simulateQ_pure, StateT.run_pure]
  unfold advOMPI advOMPR
  rw [hE.prEvent_eq, prEvent_map, hO]
  refine (prEvent_le_prEvent_add_prEvent_and_not J _
    (fun x => OMPIWin tr Q (x.1.1, x.2.2.1, ompiProj qT x.2.2.2) ∧
      ∀ u ∈ x.2.1, tr.IsPre x.1.1 (tr.D x.1.2 u) u)).trans (add_le_add ?_ ?_)
  · refine prEvent_le_bind J F _ _ fun x hx hw w hwF => ?_
    simp only [J, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
    obtain ⟨kp, -, a, -, L, hL, z, hz, rfl⟩ := hx
    obtain ⟨-, hI⟩ := simulateQ_inv_bound (ompiComb qT (tr.D kp.2)) (fun _ => False)
      (fun _ s => OInv (tr.D kp.2) qT L s) (fun q s _ hI _ => by simpa using ompi_inv qT _ _ q s hI)
      a 0 _ (isQueryBoundP_false a) (oinv_init _ qT L) z hz
    simp only [F] at hwF
    erw [support_map] at hwF
    obtain ⟨w', hw', rfl⟩ := hwF
    exact ompiWin_imp tr qT Q kp.1 kp.2 L (length_of_mem_unifList' _ L hL) z hI hw.1 hw.2 w' hw'
  · have hm : (fun x : (PK × SK) × List T × ((ℕ × S) × ORSt T S × Ch AR ℕ Unit T) =>
        (x.1, x.2.1)) <$> J =ᵈ (do let kp ← tr.keyGen; let L ← unifList T (qT + Q); pure (kp, L)) := by
      simp only [J, map_bind, map_pure]
      refine EvalDistEq.bind_right _ fun kp => ?_
      refine (EvalDistEq.bind_right _ fun a => EvalDistEq.bind_right _ fun L =>
        EvalDistEq.bind_const _ _).trans (EvalDistEq.bind_const _ _)
    refine (prEvent_mono _ _ (fun x => ∃ u ∈ x.2.1, ¬tr.IsPre x.1.1 (tr.D x.1.2 u) u)
      fun x hx => ?_).trans (le_of_eq ?_)
    · by_contra hn
      push Not at hn
      exact hx.2 ⟨hx.1, hn⟩
    · have := hm.prEvent_eq (fun y => ∃ u ∈ y.2, ¬tr.IsPre y.1.1 (tr.D y.1.2 u) u)
      rw [prEvent_map] at this
      rw [this]
      simp [badTargets, map_bind]

/-- **Theorem 1 (c) with the failure rate**: `+ (q_T + Q)·ρ`. -/
theorem advOMPI_le_ompr_rate (qT Q : ℕ) (A : PK → ProbComp (OracleComp (specI AR T S) (ℕ × S))) :
    advOMPI tr qT Q A ≤ advOMPR tr (qT + Q) Q (ompiRed AR qT Q A) + (qT + Q : ℕ) * failRate tr :=
  (advOMPI_le_ompr tr qT Q A).trans (add_le_add le_rfl (badTargets_le tr _))

end OMPIRed

end VoleMole.Assumptions.IdealTag

namespace VoleMole.Assumptions.IdealTag

open VoleMole.Assumptions.LazyIdeal (simulateQ_proj_eqd simulateQ_inv_bound prEvent_unifList_exists_le₀
  prEvent_le_bind)

open VoleMole.Assumptions.UOV

/-! ## det-FDH (UF-Tag with `Tag` a random function) ≤ OMPR -/

section Chain

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {M : Type} [DecidableEq M] {T S : Type} [SampleableType T] [Inhabited T] [Inhabited S]
  {PK SK : Type} (tr : Trapdoor PK SK T S)

/-- **det-FDH ≤ OMPR** (Theorem 1 (a) then (c)): for a det-FDH forger with at most `k` hash and
signing queries on every path,

    Adv^{euf}_{det}(A; q_H, q_S) ≤ Adv^{ompr}(B; k + 1 + q_S, q_S) + Pr[D errs on one of k + 1 + q_S targets],

`B = ompiRed (k + 1) q_S (fdhRed A)`. With `Tag` a random function, UF-Tag (strict win) is det-FDH
with `H = Tag`, so this is Lemma 2.1 then T1(c). -/
theorem advFDH_le_ompr (qH qS k : ℕ) (A : PK → ProbComp (OracleComp (specF AR M T S) (M × S)))
    (hA : ∀ pk, ∀ a ∈ support (A pk), IsQueryBoundP a isHS k) :
    advFDH tr qH qS A ≤
      advOMPR tr (k + 1 + qS) qS (ompiRed AR (k + 1) qS (fdhRed AR A)) +
        badTargets tr (k + 1 + qS) :=
  (advFDH_le_ompi tr qH qS k A hA).trans (advOMPI_le_ompr tr (k + 1) qS _)

/-- The same with the failure rate `ρ`: `+ (k + 1 + q_S)·ρ`. -/
theorem advFDH_le_ompr_rate (qH qS k : ℕ) (A : PK → ProbComp (OracleComp (specF AR M T S) (M × S)))
    (hA : ∀ pk, ∀ a ∈ support (A pk), IsQueryBoundP a isHS k) :
    advFDH tr qH qS A ≤
      advOMPR tr (k + 1 + qS) qS (ompiRed AR (k + 1) qS (fdhRed AR A)) +
        (k + 1 + qS : ℕ) * failRate tr :=
  (advFDH_le_ompr tr qH qS k A hA).trans (add_le_add le_rfl (badTargets_le tr _))

end Chain

end VoleMole.Assumptions.IdealTag
