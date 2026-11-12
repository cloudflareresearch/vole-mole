import VoleMole.Assumptions.UOV

/-!
# CT-UF^open with an ideal `Com` from one-more preimage resistance (T4, repaired Lemma U)

`lean/docs/security/uov-assumptions.md` §5.4. `Com` is a lazy random function (`advCTUFIdeal1`,
`Assumptions/UOV.lean`).

**The reduction** `ompRed ℓ F` (an on-demand OMPR adversary, labels `Xc ⊕ ℕ`, no hints) runs the
forger and the challenger's final evaluations (`ciFinal`) with
* the world forwarded;
* `Com(x)`, for a point not yet evaluated, answered by a fresh challenge target with label `x`
  (and remembered);
* `Sign(t)`, for a target not yet signed, forwarded to the preimage oracle (and remembered, so a
  repeated query costs no call).
It then claims `(x*, s*)`, and for every signed `t` the oracle's answer under the label of the
first opening `x` with `Com(x) = t`; it pads to `ℓ + 1` claims with `ℓ − d` fresh targets (labels
`inr i`) and their preimages (`d`: the number of signed targets).

**The theorem** (`advCTUFIdeal1_le_ompr`): for a forger with at most `q_f` `Com` and `q_S` signing
queries and `q_S` openings, with `n = q_f + 2q_S + 1` targets,

    Adv^{ct-uf-open}_1(F) ≤ Adv^{ompr}(ompRed q_S F; n, q_S) + n · preFailPr,

`preFailPr` the probability that the sampler `D` fails on a uniform target. Proof: pre-sample `Com`'s
fresh values as the `n` challenge targets (`LazyIdeal.rfStream_presample`); the reduction against the
OMPR challenger, projected, is that run (`comb_proj`); on every run where the forger wins and no
target is a failure point of `D`, the reduction wins (`win_imp`); union bound over the targets
(`LazyIdeal.prEvent_unifList_exists_le`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.ROM.OneMore
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.CTUFOpen

section Red

variable {DR : Type} (AR : DR → Type) (Xc T S : Type)

/-- The reduction's oracles: OMPR's, with labels `Xc ⊕ ℕ` and no hints. -/
abbrev specO := specB AR (Xc ⊕ ℕ) Unit T S

/-- The reduction's state: the `Com` values it handed out, and the signed targets with the
oracle's answers (each target once, in order). -/
structure RSt where
  com : Xc → Option T
  cache : List (T × S)

variable {AR Xc T S}

def worldQ (d : DR) : OracleComp (specO AR Xc T S) (AR d) :=
  liftM ((specO AR Xc T S).query (.inl d))

def chalQ (l : Xc ⊕ ℕ) : OracleComp (specO AR Xc T S) (Option T) :=
  liftM ((specO AR Xc T S).query (.inr (.inl (l, ()))))

def preQ (t : T) : OracleComp (specO AR Xc T S) S :=
  liftM ((specO AR Xc T S).query (.inr (.inr t)))

variable [DecidableEq Xc] [DecidableEq T] [Inhabited T]

/-- **The reduction's handler** for the forger's oracles. -/
def rImpl : QueryImpl (specCI AR 1 Xc T S) (StateT (RSt Xc T S) (OracleComp (specO AR Xc T S)))
  | .inl (.inl d) => StateT.mk fun st => (fun a => (a, st)) <$> worldQ d
  | .inl (.inr q) => StateT.mk fun st => match st.cache.lookup q.2 with
      | some s => pure (s, st)
      | none => (fun s : S => (s, { st with cache := st.cache ++ [(q.2, s)] })) <$> preQ q.2
  | .inr x => StateT.mk fun st => match st.com x with
      | some v => pure (v, st)
      | none => (fun o : Option T => match o with
          | some u => (u, { st with com := Function.update st.com x (some u) })
          | none => ((default : T), st)) <$> chalQ (.inl x)

/-- **Padding**: `k` fresh targets (labels `inr i`, `inr (i+1)`, …) and their preimages. -/
def padQ : ℕ → ℕ → OracleComp (specO AR Xc T S) (List ((Xc ⊕ ℕ) × S))
  | 0, _ => pure []
  | k + 1, i => do
    let o ← chalQ (.inr i)
    match o with
    | none => pure []
    | some u => do
      let s ← preQ u
      let r ← padQ k (i + 1)
      pure ((.inr i, s) :: r)

/-- The label of a signed target `t`: the first opening `x` with `Com(x) = t`. -/
def labelOf (xs : List Xc) (com : Xc → Option T) (t : T) : Option Xc :=
  xs.find? fun x => com x = some t

/-- The base claims: each signed target's answer under its label (dropped if it has none). -/
def baseCl (o : CTOut 1 S Xc) (st : RSt Xc T S) : List ((Xc ⊕ ℕ) × S) :=
  st.cache.filterMap fun p => (labelOf o.2 st.com p.1).map fun y => ((.inl y : Xc ⊕ ℕ), p.2)

/-- **The reduction's claims**: `(x*, s*)`, the signed targets' answers under their openings'
labels, and `ℓ − d` padding claims. -/
def claimsQ (ℓ : ℕ) (o : CTOut 1 S Xc) (st : RSt Xc T S) :
    OracleComp (specO AR Xc T S) (List ((Xc ⊕ ℕ) × S)) :=
  match o.1 with
  | some (_, x, s) =>
    (fun pads => ((.inl x, s) :: baseCl o st) ++ pads) <$> padQ (ℓ - st.cache.length) 0
  | none => pure []

/-- The reduction's computation, given the forger's computation `f`. -/
def bcomp (ℓ : ℕ) (f : OracleComp (specCI AR 1 Xc T S) (CTOut 1 S Xc)) :
    OracleComp (specO AR Xc T S) (List ((Xc ⊕ ℕ) × S)) :=
  (simulateQ rImpl (f >>= ciFinal)).run ⟨fun _ => none, []⟩ >>= fun r => claimsQ ℓ r.1 r.2

/-- **The OMPR adversary built from an ideal CT-UF^open forger** (one key). -/
def ompRed (ℓ : ℕ) {PK : Type} (F : PK → ProbComp (OracleComp (specCI AR 1 Xc T S) (CTOut 1 S Xc)))
    (pk : PK) : ProbComp (OracleComp (specO AR Xc T S) (List ((Xc ⊕ ℕ) × S))) :=
  bcomp ℓ <$> F pk

end Red

section Comb

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Xc T S : Type} [DecidableEq Xc] [DecidableEq T] [Inhabited T]

/-- The reduction run against the OMPR challenger, as one handler. -/
def combC (pre : T → S) :
    QueryImpl (specCI AR 1 Xc T S) (StateT (RSt Xc T S × Ch AR (Xc ⊕ ℕ) Unit T) ProbComp) :=
  fun q => StateT.mk fun s => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (chImpl pre) ((rImpl q).run s.1)).run s.2

theorem collapseC (pre : T → S) {α : Type} (oa : OracleComp (specCI AR 1 Xc T S) α)
    (s : RSt Xc T S) (c : Ch AR (Xc ⊕ ℕ) Unit T) :
    (simulateQ (chImpl pre) ((simulateQ rImpl oa).run s)).run c =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (combC pre) oa).run (s, c) := by
  refine simulateQ_StateT_StateT_compose _ _ _ (fun q s c => ?_) oa s c
  show _ = _ <$> ((fun r : (_ × _) × _ => (r.1.1, (r.1.2, r.2))) <$> _)
  rw [Functor.map_map]
  exact (id_map _).symm

variable (pre : T → S)

theorem combC_world (d : DR) (s : RSt Xc T S × Ch AR (Xc ⊕ ℕ) Unit T) :
    (combC pre (.inl (.inl d))).run s =
      (fun r => (r.1, (s.1, { s.2 with ro := r.2 }))) <$> ((specR AR).randomOracle d).run s.2.ro := by
  simp only [combC, rImpl, worldQ, StateT.run_mk]
  erw [simulateQ_map, simulateQ_spec_query]
  simp [chImpl, roStep]

theorem combC_sign (q : Fin 1 × T) (s : RSt Xc T S × Ch AR (Xc ⊕ ℕ) Unit T) :
    (combC pre (.inl (.inr q))).run s = pure (match s.1.cache.lookup q.2 with
      | some a => (a, s)
      | none => (pre q.2, ({ s.1 with cache := s.1.cache ++ [(q.2, pre q.2)] },
          { s.2 with iq := s.2.iq + 1 }))) := by
  simp only [combC, rImpl, StateT.run_mk]
  cases h : s.1.cache.lookup q.2 with
  | some a => simp
  | none =>
    simp only [preQ]
    erw [simulateQ_map, simulateQ_spec_query]
    simp [chImpl]

theorem combC_com (x : Xc) (s : RSt Xc T S × Ch AR (Xc ⊕ ℕ) Unit T) :
    (combC pre (.inr x)).run s = pure (match s.1.com x with
      | some v => (v, s)
      | none => match s.2.rest with
        | u :: r => (u, ({ s.1 with com := Function.update s.1.com x (some u) },
            { s.2 with rest := r, tg := Function.update s.2.tg (.inl x) (some (u, ())) }))
        | [] => ((default : T), s)) := by
  simp only [combC, rImpl, StateT.run_mk]
  cases h : s.1.com x with
  | some v => simp
  | none =>
    simp only [chalQ]
    erw [simulateQ_map, simulateQ_spec_query]
    cases hr : s.2.rest with
    | nil => simp [chImpl, hr]
    | cons u r => simp [chImpl, hr]

end Comb

section Proj

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Xc T S : Type} [DecidableEq Xc] [DecidableEq T] [Inhabited T]

/-- **The ideal challenger's state the reduction's run represents**: the world's cache and the
signed targets, `Com`'s table, the unused targets. -/
def projC (s : RSt Xc T S × Ch AR (Xc ⊕ ℕ) Unit T) : CISt AR 1 T × (Xc → Option T) × List T :=
  (⟨s.2.ro, s.1.cache.map fun p => ((0 : Fin 1), p.1)⟩, s.1.com, s.2.rest)

omit [Inhabited T] in
theorem lookup_mem {l : List (T × S)} {t : T} {a : S} (h : l.lookup t = some a) : (t, a) ∈ l := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 h
  simp

omit [Inhabited T] in
theorem lookup_none {l : List (T × S)} {t : T} (h : l.lookup t = none) : ∀ p ∈ l, p.1 ≠ t := by
  intro p hp hpt
  have := List.lookup_eq_none_iff.1 h p hp
  simp [hpt] at this

variable (pre : T → S) (L : List T)

/-- **The reduction's invariant**: cached answers are the oracle's, cached targets distinct and
counted by `iq`; every `Com` value it handed out is the target of its label; targets come from
the stream `L`; no padding label used yet. -/
def InvC (s : RSt Xc T S × Ch AR (Xc ⊕ ℕ) Unit T) : Prop :=
  (∀ p ∈ s.1.cache, p.2 = pre p.1) ∧ (s.1.cache.map Prod.fst).Nodup ∧
    s.2.iq = s.1.cache.length ∧ (∀ x v, s.1.com x = some v → s.2.tg (.inl x) = some (v, ())) ∧
    (∀ l p, s.2.tg l = some p → p.1 ∈ L) ∧ (∀ u ∈ s.2.rest, u ∈ L)

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [DecidableEq Xc] [DecidableEq T] [Inhabited T] in
theorem invC_init : InvC (AR := AR) (Xc := Xc) pre L (⟨fun _ => none, []⟩, ch0 L) := by
  refine ⟨by simp, by simp, rfl, by simp, by simp [ch0], by simp [ch0]⟩

theorem invC_step : QueryImpl.PreservesInv (combC (AR := AR) (Xc := Xc) pre) (InvC pre L) := by
  intro q s hs z hz
  change z ∈ support ((combC pre q).run s) at hz
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  rcases q with (d | q) | x
  · rw [combC_world] at hz
    simp at hz
    obtain ⟨r, -, rfl⟩ := hz
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rw [combC_sign] at hz
    cases hl : s.1.cache.lookup q.2 with
    | some a =>
      simp only [hl, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨h1, h2, h3, h4, h5, h6⟩
    | none =>
      simp only [hl, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨?_, ?_, by simp [h3], h4, h5, h6⟩
      · intro p hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact h1 p hp
        · rfl
      · simp only [List.map_append, List.map_cons, List.map_nil]
        refine List.Nodup.append h2 (List.nodup_singleton _) ?_
        simp only [List.disjoint_singleton]
        intro hm
        obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hm
        exact lookup_none hl p hp hpe
  · rw [combC_com] at hz
    cases hc : s.1.com x with
    | some v =>
      simp only [hc, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨h1, h2, h3, h4, h5, h6⟩
    | none =>
      cases hr : s.2.rest with
      | nil =>
        simp only [hc, hr, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact ⟨h1, h2, h3, h4, h5, h6⟩
      | cons u r =>
        simp only [hc, hr, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
        · intro y v hy
          by_cases hyx : y = x
          · subst hyx
            simp only [Function.update_self, Option.some.injEq] at hy ⊢
            rw [hy]
          · simp only [Function.update_of_ne hyx] at hy
            have hne : (Sum.inl y : Xc ⊕ ℕ) ≠ Sum.inl x := by simpa using hyx
            simp only [Function.update_of_ne hne]
            exact h4 y v hy
        · intro l p hl
          by_cases hlx : l = .inl x
          · subst hlx
            simp only [Function.update_self, Option.some.injEq] at hl
            subst hl
            exact h6 u (by simp [hr])
          · simp only [Function.update_of_ne hlx] at hl
            exact h5 l p hl
        · intro w hw
          exact h6 w (by simp [hr, hw])

/-- **The reduction against the OMPR challenger is the ideal challenger fed from the stream**, step
by step, through `projC`. -/
theorem combC_proj (q : (DR ⊕ (Fin 1 × T)) ⊕ Xc) (s : RSt Xc T S × Ch AR (Xc ⊕ ℕ) Unit T)
    (hs : InvC pre L s) :
    Prod.map id projC <$> (combC pre q).run s =
      (LazyIdeal.rfStream (ciOther fun q => pre q.2) q).run (projC s) := by
  rcases q with (d | q) | x
  · rw [combC_world]
    simp [LazyIdeal.rfStream, ciOther, projC, Functor.map_map]
  · rw [combC_sign]
    obtain ⟨q0, t⟩ := q
    have hq0 : q0 = 0 := Subsingleton.elim _ _
    subst hq0
    cases hl : s.1.cache.lookup t with
    | some a =>
      have hm := lookup_mem hl
      have ha : a = pre t := hs.1 _ hm
      have hmem : ((0 : Fin 1), t) ∈ s.1.cache.map fun p => ((0 : Fin 1), p.1) :=
        List.mem_map.2 ⟨(t, a), hm, rfl⟩
      simp [LazyIdeal.rfStream, ciOther, projC, hmem, ha]
    | none =>
      have hmem : ((0 : Fin 1), t) ∉ s.1.cache.map fun p => ((0 : Fin 1), p.1) := by
        intro h
        obtain ⟨p, hp, hpe⟩ := List.mem_map.1 h
        exact lookup_none hl p hp (Prod.ext_iff.1 hpe).2
      simp [LazyIdeal.rfStream, ciOther, projC, hmem]
  · rw [combC_com]
    cases hc : s.1.com x with
    | some v => simp [LazyIdeal.rfStream, projC, hc]
    | none =>
      cases hr : s.2.rest with
      | nil => simp [LazyIdeal.rfStream, projC, hc, hr]
      | cons u r => simp [LazyIdeal.rfStream, projC, hc, hr]

/-- The whole run, projected. -/
theorem combC_run_proj {α : Type} (oa : OracleComp (specCI AR 1 Xc T S) α) :
    Prod.map id projC <$> (simulateQ (combC pre) oa).run (⟨fun _ => none, []⟩, ch0 L) =
      (simulateQ (LazyIdeal.rfStream (ciOther fun q => pre q.2)) oa).run
        (⟨∅, []⟩, fun _ => none, L) :=
  map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (InvC pre L) projC
    (fun q s hs z hz => invC_step pre L q s hs z hz) (fun q s hs => combC_proj pre L q s hs) oa _
    (invC_init pre L)

end Proj

section Budget

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Xc T S : Type} [DecidableEq Xc] [DecidableEq T] [Inhabited T]

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [DecidableEq Xc] [DecidableEq T] [Inhabited T] in
theorem mapM_comQ_bound (p : (DR ⊕ (Fin 1 × T)) ⊕ Xc → Prop) [DecidablePred p] (k : ℕ)
    (hk : ∀ x : Xc, p (.inr x) → 0 < k) :
    ∀ xs : List Xc, IsQueryBoundP (xs.mapM (comQ (AR := AR) (K := 1) (S := S))) p (xs.length * k)
  | [] => by simp
  | x :: xs => by
    rw [List.mapM_cons]
    refine ((isQueryBoundP_bind (n := k) (m := xs.length * k) ?_ fun y _ => ?_).mono
      (by simp [Nat.succ_mul, Nat.add_comm]))
    · exact (isQueryBoundP_query_iff p _ _).2 (hk x)
    · have h := mapM_comQ_bound p k hk xs
      rw [← Nat.add_zero (xs.length * k)]
      exact isQueryBoundP_bind h fun _ _ => isQueryBoundP_pure _ _ _

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [DecidableEq Xc] [DecidableEq T] [Inhabited T] in
theorem ciFinal_bound_rf (o : CTOut 1 S Xc) :
    IsQueryBoundP (ciFinal (AR := AR) (T := T) o) (fun q => LazyIdeal.isRF q = true) (o.2.length + 1) := by
  unfold ciFinal
  have h := mapM_comQ_bound (AR := AR) (T := T) (S := S) (fun q => LazyIdeal.isRF q = true) 1
    (fun _ _ => Nat.one_pos) ((o.1.map fun f => f.2.1).toList ++ o.2)
  refine ((isQueryBoundP_bind h fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_)
  cases o.1 <;> simp

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [DecidableEq Xc] [DecidableEq T] [Inhabited T] in
theorem ciFinal_bound_sign (o : CTOut 1 S Xc) :
    IsQueryBoundP (ciFinal (AR := AR) (T := T) o) (fun q => isSign q = true) 0 := by
  unfold ciFinal
  have h := mapM_comQ_bound (AR := AR) (T := T) (S := S) (fun q => isSign q = true) 0
    (fun _ h => by simp [isSign] at h) ((o.1.map fun f => f.2.1).toList ++ o.2)
  simpa using isQueryBoundP_bind h fun _ _ => isQueryBoundP_pure _ _ 0

variable (pre : T → S)

/-- **Budget**: with at most `k` `Com` queries the stream loses at most `k` targets, and with at
most `k'` signing queries at most `k'` targets are signed. -/
theorem combC_budget {α : Type} (oa : OracleComp (specCI AR 1 Xc T S) α) (k k' : ℕ)
    (hk : IsQueryBoundP oa (fun q => LazyIdeal.isRF q = true) k)
    (hk' : IsQueryBoundP oa (fun q => isSign q = true) k') (s : RSt Xc T S × Ch AR (Xc ⊕ ℕ) Unit T) :
    ∀ z ∈ support ((simulateQ (combC pre) oa).run s),
      s.2.rest.length ≤ z.2.2.rest.length + k ∧ z.2.1.cache.length ≤ s.1.cache.length + k' := by
  intro z hz
  constructor
  · have := IsQueryBoundP.cost_le_of_mem_support_run_simulateQ (impl := combC pre)
      (fun st => s.2.rest.length - st.2.rest.length) (fun q _ st z hz => ?_)
      (fun q hq st z hz => ?_) hk s z hz
    · simp at this; omega
    · rcases q with (d | q) | x
      · rw [combC_world] at hz
        simp at hz
        obtain ⟨r, -, rfl⟩ := hz; simp
      · rw [combC_sign] at hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz; cases st.1.cache.lookup q.2 <;> simp
      · rw [combC_com] at hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        cases st.1.com x with
        | some v => simp
        | none => cases h : st.2.rest with
          | nil => simp; omega
          | cons u r => simp; omega
    · rcases q with (d | q) | x
      · rw [combC_world] at hz
        simp at hz
        obtain ⟨r, -, rfl⟩ := hz; simp
      · rw [combC_sign] at hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz; cases st.1.cache.lookup q.2 <;> simp
      · simp [LazyIdeal.isRF] at hq
  · have := IsQueryBoundP.cost_le_of_mem_support_run_simulateQ (impl := combC pre)
      (fun st => st.1.cache.length) (fun q _ st z hz => ?_)
      (fun q hq st z hz => ?_) hk' s z hz
    · exact this
    · rcases q with (d | q) | x
      · rw [combC_world] at hz
        simp at hz
        obtain ⟨r, -, rfl⟩ := hz; simp
      · rw [combC_sign] at hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz; cases st.1.cache.lookup q.2 <;> simp
      · rw [combC_com] at hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        cases st.1.com x with
        | some v => simp
        | none => cases st.2.rest <;> simp
    · rcases q with (d | q) | x
      · rw [combC_world] at hz
        simp at hz
        obtain ⟨r, -, rfl⟩ := hz; simp
      · simp [isSign] at hq
      · rw [combC_com] at hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        cases st.1.com x with
        | some v => simp
        | none => cases st.2.rest <;> simp

end Budget

section Pad

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Xc T S : Type} [DecidableEq Xc] (pre : T → S)

theorem padQ_step (k i : ℕ) (c : Ch AR (Xc ⊕ ℕ) Unit T) (u : T) (r : List T) (hr : c.rest = u :: r) :
    (simulateQ (chImpl pre) (padQ (AR := AR) (Xc := Xc) (k + 1) i)).run c =
      (fun w => ((.inr i, pre u) :: w.1, w.2)) <$> (simulateQ (chImpl pre) (padQ k (i + 1))).run
        { c with rest := r, tg := Function.update c.tg (.inr i) (some (u, ())), iq := c.iq + 1 } := by
  simp only [padQ, chalQ, preQ, simulateQ_bind, StateT.run_bind]
  erw [simulateQ_spec_query]
  simp [chImpl, hr]
  erw [simulateQ_spec_query]
  simp [chImpl]

theorem padQ_run : ∀ (k i : ℕ) (c : Ch AR (Xc ⊕ ℕ) Unit T), k ≤ c.rest.length →
    ∀ z ∈ support ((simulateQ (chImpl pre) (padQ (AR := AR) (Xc := Xc) k i)).run c),
      z.1.map Prod.fst = (List.range' i k).map Sum.inr ∧ z.2.iq = c.iq + k ∧
      (∀ l, (∀ j, i ≤ j → l ≠ .inr j) → z.2.tg l = c.tg l) ∧
      (∀ p ∈ z.1, ∃ u ∈ c.rest, z.2.tg p.1 = some (u, ()) ∧ p.2 = pre u)
  | 0, i, c, _, z, hz => by
    simp only [padQ, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  | k + 1, i, c, hk, z, hz => by
    obtain ⟨u, r, hr⟩ : ∃ u r, c.rest = u :: r := by
      cases h : c.rest with
      | nil => simp [h] at hk
      | cons u r => exact ⟨u, r, rfl⟩
    rw [padQ_step pre k i c u r hr] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hk' : k ≤ r.length := by rw [hr] at hk; simpa using hk
    obtain ⟨h1, h2, h3, h4⟩ := padQ_run k (i + 1) _ hk' w hw
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, h1, List.range'_succ]
    · simp only [h2]; omega
    · intro l hl
      rw [h3 l fun j hj => hl j (by omega)]
      exact Function.update_of_ne (hl i le_rfl) _ _
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · refine ⟨u, by simp [hr], ?_, rfl⟩
        rw [h3 _ fun j hj => by simp; omega]
        simp
      · obtain ⟨v, hv, hvt, hvp⟩ := h4 p hp
        exact ⟨v, by simp [hr, hv], hvt, hvp⟩

end Pad

section Win

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Xc T S : Type} [DecidableEq Xc] [DecidableEq T] [Inhabited T] {PK : Type}
  (IsPre : PK → S → T → Prop) (pk : PK) (pre : T → S) (L : List T) (ℓ : ℕ)

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [DecidableEq Xc] [Inhabited T] in
theorem labelOf_spec {xs : List Xc} {com : Xc → Option T} {t : T} {y : Xc}
    (h : labelOf xs com t = some y) : com y = some t := by
  simpa using List.find?_some h

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [DecidableEq Xc] [Inhabited T] in
/-- The base claims' labels are distinct when the signed targets are. -/
theorem baseCl_labels_nodup (o : CTOut 1 S Xc) (st : RSt Xc T S)
    (h : (st.cache.map Prod.fst).Nodup) : ((baseCl o st).map Prod.fst).Nodup := by
  have : (baseCl o st).map Prod.fst =
      (st.cache.map Prod.fst).filterMap fun t => (labelOf o.2 st.com t).map Sum.inl := by
    simp only [baseCl, List.map_filterMap, List.filterMap_map, Option.map_map]
    rfl
  rw [this]
  refine h.filterMap fun t t' b hb hb' => ?_
  simp only [Option.mem_def, Option.map_eq_some_iff] at hb hb'
  obtain ⟨y, hy, rfl⟩ := hb
  obtain ⟨y', hy', hyy⟩ := hb'
  cases hyy
  have h1 := labelOf_spec hy
  have h2 := labelOf_spec hy'
  rw [h1] at h2
  exact Option.some.inj h2

omit [Inhabited T] in
/-- **On a run where the forger wins, the reduction wins, or the sampler fails on a target from
the stream.** `s` is the reduction's state after the forger and the final evaluations, with the
invariant and enough targets left for the padding. -/
theorem win_imp (o : CTOut 1 S Xc) (s : RSt Xc T S × Ch AR (Xc ⊕ ℕ) Unit T) (hinv : InvC pre L s)
    (hd : s.1.cache.length ≤ ℓ) (hrest : ℓ - s.1.cache.length ≤ s.2.rest.length)
    (hw : CIWin (fun _ => IsPre pk) (o, (projC s).1, (projC s).2.1))
    (z : List ((Xc ⊕ ℕ) × S) × Ch AR (Xc ⊕ ℕ) Unit T)
    (hz : z ∈ support ((simulateQ (chImpl pre) (claimsQ ℓ o s.1)).run s.2)) :
    Wins ℓ (goodPre IsPre) pk z.1 z.2 ∨ ∃ u ∈ L, ¬IsPre pk (pre u) u := by
  obtain ⟨hi1, hi2, hi3, hi4, hi5, hi6⟩ := hinv
  obtain ⟨k, x, sx, c, ho, hcx, hpre, hfresh, hopen⟩ := hw
  simp only [projC] at hcx hfresh hopen
  have hfresh' : ∀ p ∈ s.1.cache, p.1 ≠ c := fun p hp =>
    hfresh _ (List.mem_map.2 ⟨p, hp, rfl⟩)
  have hlab : ∀ p ∈ s.1.cache, ∃ y, labelOf o.2 s.1.com p.1 = some y := by
    intro p hp
    obtain ⟨x', hx', hc'⟩ := hopen _ (List.mem_map.2 ⟨p, hp, rfl⟩)
    have : (labelOf o.2 s.1.com p.1).isSome := List.find?_isSome.2 ⟨x', hx', by simpa using hc'⟩
    exact Option.isSome_iff_exists.1 this
  unfold claimsQ at hz
  rw [ho] at hz
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨h1, h2, h3, h4⟩ := padQ_run pre _ 0 s.2 hrest w hw
  have hinl : ∀ y : Xc, w.2.tg (.inl y) = s.2.tg (.inl y) := fun y => h3 _ fun j _ => by simp
  by_cases hall : ∀ u ∈ L, IsPre pk (pre u) u
  swap
  · push Not at hall
    exact Or.inr hall
  left
  have hblen : (baseCl o s.1).length = s.1.cache.length := by
    simp only [baseCl, List.length_filterMap_eq_countP, List.countP_eq_length]
    intro p hp
    obtain ⟨y, hy⟩ := hlab p hp
    simp [hy]
  have hwlen : w.1.length = ℓ - s.1.cache.length := by
    simpa using congrArg List.length h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, hblen, hwlen]
    omega
  · simp only [List.map_append, List.map_cons, h1, List.cons_append]
    refine List.nodup_cons.2 ⟨?_, ?_⟩
    · simp only [List.mem_append, List.mem_map, not_or]
      refine ⟨?_, by simp⟩
      rintro ⟨p, hp, hpx⟩
      obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.1 hp
      obtain ⟨y, hy⟩ := hlab q hq
      simp only [hy, Option.map_some, Option.some.injEq] at hqp
      subst hqp
      simp only [Sum.inl.injEq] at hpx
      subst hpx
      have := labelOf_spec hy
      rw [hcx] at this
      exact hfresh' q hq (Option.some.inj this).symm
    · refine List.Nodup.append (baseCl_labels_nodup o s.1 hi2)
        ((List.nodup_range').map Sum.inr_injective) ?_
      intro a ha hb
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.1 hp
      obtain ⟨y, hy⟩ := hlab q hq
      simp only [hy, Option.map_some, Option.some.injEq] at hqp
      subst hqp
      simp at hb
  · simp only [h2, hi3]; omega
  · intro p hp
    simp only [List.mem_append, List.mem_cons] at hp
    rcases hp with (rfl | hp) | hp
    · refine ⟨c, (), ?_, hpre⟩
      rw [hinl]
      exact hi4 x c hcx
    · obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.1 hp
      obtain ⟨y, hy⟩ := hlab q hq
      simp only [hy, Option.map_some, Option.some.injEq] at hqp
      subst hqp
      have htg := hi4 y q.1 (labelOf_spec hy)
      refine ⟨q.1, (), by rw [hinl]; exact htg, ?_⟩
      rw [hi1 q hq]
      exact hall _ (hi5 _ _ htg)
    · obtain ⟨u, hu, htg, hp2⟩ := h4 p hp
      refine ⟨u, (), htg, ?_⟩
      rw [hp2]
      exact hall u (hi6 u hu)

end Win

section Main

/-- A pointwise split of event computations on the possible draws survives the draw. -/
theorem prEvent_bind_le_add_of_support {α : Type} (mx : ProbComp α) (f g k : α → ProbComp Prop)
    (h : ∀ a ∈ support mx, prEvent (f a) ≤ prEvent (g a) + prEvent (k a)) :
    prEvent (mx >>= f) ≤ prEvent (mx >>= g) + prEvent (mx >>= k) := by
  rw [bind_eq_attach_bind mx f, bind_eq_attach_bind mx g, bind_eq_attach_bind mx k]
  have := prEvent_bind_le_add_of_forall_le (MonadAttach.attach mx) (fun a => f a.1)
    (fun a => g a.1) (fun a => k a.1) id id id fun a => by simpa using h a.1 a.2
  simpa using this

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Xc T S : Type} [DecidableEq Xc] [DecidableEq T] [Inhabited T] [SampleableType T] {PK : Type}
  (IsPre : PK → S → T → Prop) (pk : PK) (pre : T → S) (qf qS : ℕ)

/-- **T4 at a fixed key**: the forger's ideal CT-UF^open win probability is at most the
reduction's OMPR win probability plus the probability that some target is a failure point of
the sampler. -/
theorem ciRun_le (f : OracleComp (specCI AR 1 Xc T S) (CTOut 1 S Xc)) (hf : CIBudget qf qS f) :
    Pr{let r ← ciRun (fun q => pre q.2) f}[CIWin (fun _ => IsPre pk) r] ≤
      Pr{let L ← unifList T (qf + 2 * qS + 1)
         let r ← (simulateQ (chImpl pre) (bcomp qS f)).run (ch0 L)}[Wins qS (goodPre IsPre) pk r.1 r.2] +
      Pr{let L ← unifList T (qf + 2 * qS + 1)}[∃ u ∈ L, ¬IsPre pk (pre u) u] := by
  set n := qf + 2 * qS + 1
  have hRF : IsQueryBoundP (f >>= ciFinal) (fun q => LazyIdeal.isRF q = true) (qf + (qS + 1)) :=
    isQueryBoundP_bind hf.1 fun o ho => (ciFinal_bound_rf o).mono (by have := hf.2.2 o ho; omega)
  have hSg : IsQueryBoundP (f >>= ciFinal) (fun q => isSign q = true) (qS + 0) :=
    isQueryBoundP_bind hf.2.1 fun o _ => ciFinal_bound_sign o
  unfold ciRun bcomp
  generalize f >>= ciFinal (AR := AR) (T := T) = G at hRF hSg ⊢
  let c0 : RSt Xc T S := ⟨fun _ => none, []⟩
  let J : ProbComp (List T × (CTOut 1 S Xc × RSt Xc T S × Ch AR (Xc ⊕ ℕ) Unit T) ×
      (List ((Xc ⊕ ℕ) × S) × Ch AR (Xc ⊕ ℕ) Unit T)) := do
    let L ← unifList T n
    let w ← (simulateQ (combC pre) G).run (c0, ch0 L)
    let z ← (simulateQ (chImpl pre) (claimsQ qS w.1 w.2.1)).run w.2.2
    pure (L, w, z)
  have hE : (simulateQ (LazyIdeal.rfFresh (ciOther fun q => pre q.2)) G).run (⟨∅, []⟩, fun _ => none) =ᵈ (do
      let L ← unifList T n
      (fun w : CTOut 1 S Xc × RSt Xc T S × Ch AR (Xc ⊕ ℕ) Unit T =>
          (w.1, (projC w.2).1, (projC w.2).2.1)) <$>
        (simulateQ (combC pre) G).run (c0, ch0 L)) := by
    refine (LazyIdeal.rfStream_presample (ciOther fun q => pre q.2) G _ n _ _ hRF (by omega)).symm.trans ?_
    refine EvalDistEq.bind_right _ fun L => ?_
    rw [← combC_run_proj pre L G, Functor.map_map]
    exact EvalDistEq.rfl
  have hA : Pr{let r ← (simulateQ (LazyIdeal.rfFresh (ciOther fun q => pre q.2)) G).run (⟨∅, []⟩,
        fun _ => none)}[CIWin (fun _ => IsPre pk) r] =
      Pr{let x ← J}[CIWin (fun _ => IsPre pk) (x.2.1.1, (projC x.2.1.2).1, (projC x.2.1.2).2.1)] := by
    rw [hE.prEvent_eq]
    simp only [J, map_bind, Functor.map_map, map_pure]
    refine prEvent_bind_congr_of_support _ _ _ fun L _ => ?_
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    refine prEvent_bind_congr_of_support _ _ _ fun w _ => ?_
    rw [OracleComp.prEvent_bind_const]
  have hB : Pr{let x ← J}[Wins qS (goodPre IsPre) pk x.2.2.1 x.2.2.2] =
      Pr{let L ← unifList T n
         let r ← (simulateQ (chImpl pre)
           ((simulateQ rImpl G).run c0 >>= (fun r => claimsQ qS r.1 r.2))).run (ch0 L)}[
        Wins qS (goodPre IsPre) pk r.1 r.2] := by
    simp only [J, simulateQ_bind, StateT.run_bind, collapseC, bind_assoc, pure_bind,
      map_eq_bind_pure_comp, Function.comp_def]
  have hC : Pr{let x ← J}[∃ u ∈ x.1, ¬IsPre pk (pre u) u] =
      Pr{let L ← unifList T n}[∃ u ∈ L, ¬IsPre pk (pre u) u] := by
    simp only [J, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine prEvent_bind_congr_of_support _ _ _ fun L _ => ?_
    refine (prEvent_bind_congr_of_support _ _ (fun _ => pure (∃ u ∈ L, ¬IsPre pk (pre u) u))
      fun w _ => ?_).trans ?_
    · rw [OracleComp.prEvent_bind_const]
    · rw [OracleComp.prEvent_bind_const]
  rw [hA, ← hB, ← hC]
  refine le_trans ?_ (prEvent_or_le _ _ _)
  refine prEvent_mono_of_support _ _ _ fun x hx hw => ?_
  simp only [J, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨L, hL, w, hw', z, hz, rfl⟩ := hx
  have hLn := length_of_mem_unifList n L hL
  have hinv := simulateQ_run_preservesInv (combC pre) (InvC pre L) (invC_step pre L) G _
    (invC_init pre L) w hw'
  obtain ⟨hb1, hb2⟩ := combC_budget pre G _ _ hRF hSg _ w hw'
  simp only [ch0, c0, List.length_nil] at hb1 hb2
  exact win_imp IsPre pk pre L qS w.1 w.2 hinv (by omega) (by omega) hw z hz

variable {SK : Type} (tr : Trapdoor PK SK T S)

/-- **T4 (repaired Lemma U), with `Com` a random function**: for an ideal CT-UF^open forger `F`
with at most `q_f` `Com` and `q_S` signing queries and at most `q_S` openings,

    Adv^{ct-uf-open}_1(F) ≤ Adv^{ompr}(ompRed q_S F; q_f + 2q_S + 1, q_S) + (q_f + 2q_S + 1)·preFailPr,

`advOMPR` the on-demand OMPR game of Def. 3.1 (`advOMPR_le_ompr31`: at most Def. 3.1's
advantage of `popAdv (ompRed q_S F)`), `preFailPr` the probability that the sampler fails on a
uniform target. -/
theorem advCTUFIdeal1_le_ompr
    (F : PK → ProbComp (OracleComp (specCI AR 1 Xc T S) (CTOut 1 S Xc)))
    (hF : ∀ pk, ∀ f ∈ support (F pk), CIBudget qf qS f) :
    advCTUFIdeal1 tr F ≤
      advOMPR tr (qf + 2 * qS + 1) qS (ompRed qS F) + ((qf + 2 * qS + 1 : ℕ) : ℝ≥0∞) * preFailPr tr := by
  set n := qf + 2 * qS + 1
  have hfail : Pr{let kp ← tr.keyGen; let L ← unifList T n}[∃ u ∈ L, ¬tr.IsPre kp.1 (tr.D kp.2 u) u] ≤
      n * preFailPr tr :=
    LazyIdeal.prEvent_unifList_exists_le tr.keyGen (fun kp u => ¬tr.IsPre kp.1 (tr.D kp.2 u) u) n
  refine le_trans ?_ (add_le_add le_rfl hfail)
  unfold advCTUFIdeal1 advOMPR omExp ompRed
  simp only [map_bind, bind_map_left, map_pure]
  refine le_trans (prEvent_bind_le_add_of_support _ _
    (fun kp => do
      let f ← F kp.1
      let L ← unifList T n
      let r ← (simulateQ (chImpl (tr.D kp.2)) (bcomp qS f)).run (ch0 L)
      pure (Wins qS (goodPre tr.IsPre) kp.1 r.1 r.2))
    (fun kp => do
      let _ ← F kp.1
      let L ← unifList T n
      pure (∃ u ∈ L, ¬tr.IsPre kp.1 (tr.D kp.2 u) u)) fun kp _ => ?_) (le_of_eq ?_)
  · refine prEvent_bind_le_add_of_support _ _ _ _ fun f hf => ?_
    have := ciRun_le (AR := AR) tr.IsPre kp.1 (tr.D kp.2) qf qS f (hF kp.1 f hf)
    simp only [map_eq_bind_pure_comp, Function.comp_def] at this ⊢
    exact this
  · congr 1
    refine prEvent_bind_congr_of_support _ _ _ fun kp _ => ?_
    rw [OracleComp.prEvent_bind_const]
    simp only [map_eq_bind_pure_comp, Function.comp_def]

end Main

end VoleMole.Assumptions.UOV.CTUFOpen
