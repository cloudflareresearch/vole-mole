import VoleMole.Assumptions.Shift

/-!
# OMPR is at most one-more unforgeability of a blind preimage scheme (Theorem 6, generic core)

`lean/docs/security/uov-assumptions.md` §5.6. Protocol-independent; the one-more game is
`OneMore.omuf` with the programmed target `H_T(x) + h` of `addHint` (PomFRIT's U1 game shape).

**The scheme** (`Client`): an honest client whose session `k` first computes, with its own random
oracle (`specR AC`, the protocol's hashes) and coins `κ`, a label `x` (the `H_T` input), a blinding
`r` and a state (`start`); the blinded request is `H_T(x) + r`; after the Issuer's answer `s` the
sessions are finished and verified by `post` (any oracle computation over the client's oracle and
`H_T`, no Issuer), which returns one acceptance flag. For PomFRIT, `start` is `issue_request` up
to `hash_to_target`'s input, `r` the client's blinding, `post` the finalization and `pomfritVerify`
of every session.

**The forger** (`blindAdv`): from an OMPR adversary `B` (labelled targets on demand, `omExp`),
it runs `B` with its world forwarded (`B`'s world is separate from the client's: the composed
world is the sum `Sum.elim AR AC`), answers `B`'s `k`-th request (`k < n`) by running session `k`
and passing on its blinded request `H_T(x) + r`, and forwards `B`'s preimage queries to the
Issuer. It claims, for each claim `(x', s)` of `B`, the label of `x'`'s session with `s`.

**Theorem** (`ompr_le_blind`): if the sessions' labels are pairwise distinct (on the supports),

    Adv^{ompr}(B; n, ℓ) ≤ Pr[Forges] + Pr[CompFail],

`CompFail`: the forger's `ℓ + 1` claims are preimages of their programmed targets
`H_T(x) + r` (on distinct labels, within `ℓ` Issuer queries) but `post` rejects: a completeness
failure of the client. The proof: the target oracle is programmed perfectly
(`OneMore.real_eqd_comb`), so `B` sees each challenge `t = (t − r) + r` exactly as in `omExp`
(`bcomb_eqd`, the client's runs integrated out: they read only the client's oracle).

With U1 (`pomfrit_U1_ompr`) this is the equivalence of §5.6 up to Lemma P's and the completeness
terms. **Not done**: the PomFRIT instance. It needs the Lean client (`issue_request`, `finalize`)
as an oracle computation over the game's oracles and its completeness in this lazy random-oracle
model (`ZK/CompleteRO.lean` proves it, `≤ 2⁻¹¹³` per session, in the finite-table model), and a
`Forger` with coins.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.ROM.OneMore VoleMole.Assumptions.UOV VoleMole.Assumptions.Shift
open scoped ENNReal

namespace VoleMole.Assumptions.Blind

section Defs

variable {DR DC : Type} (AR : DR → Type) (AC : DC → Type)

/-- The composed world: `B`'s world and the client's oracle. -/
abbrev WA : DR ⊕ DC → Type := Sum.elim AR AC

instance instSampWA [∀ d, SampleableType (AR d)] [∀ d, SampleableType (AC d)] :
    ∀ d, SampleableType (WA AR AC d)
  | .inl d => inferInstanceAs (SampleableType (AR d))
  | .inr d => inferInstanceAs (SampleableType (AC d))

variable (X G : Type)

/-- The oracles of the client's finishing phase: its oracle and `H_T` (with a hint). -/
abbrev specV : OracleSpec (DC ⊕ (X × G)) := OracleSpec.ofFn (Sum.elim AC fun _ : X × G => G × G)

variable (Hn' St : Type)

/-- A session: its index, label, blinding, state, the `H_T` answer, and `B`'s hint. -/
structure Ses where
  idx : ℕ
  x : X
  r : G
  st : St
  u : G
  hB : Hn'

variable (X' : Type)

/-- The forger's state: the number of sessions started, and the session of each of `B`'s labels. -/
structure BSt where
  k : ℕ
  ses : X' → Option (Ses X G Hn' St)

end Defs

variable {DR DC : Type} [DecidableEq DR] [DecidableEq DC] {AR : DR → Type} {AC : DC → Type}
  [∀ d, SampleableType (AR d)] [∀ d, SampleableType (AC d)]
  {X' Hn' X G S St Cn PK : Type} [DecidableEq X'] [DecidableEq X] [AddCommGroup G]

variable (AC X G S St Cn PK) in
/-- **An honest blind-preimage client**: coins, the first phase of session `k` (label, blinding,
state) over its oracle, and the finishing phase of the claimed sessions `(x, r, st, u, s)` (`u`
the `H_T` answer, `s` the Issuer's preimage) with one acceptance flag. -/
structure Client where
  coins : ProbComp Cn
  start : PK → Cn → ℕ → OracleComp (specR AC) (X × G × St)
  post : PK → Cn → List (X × G × St × G × S) → OracleComp (specV AC X G) Bool

/-- The client's oracle inside the composed adversary. -/
def liftC : QueryImpl (specR AC) (OracleComp (specA (WA AR AC) X G G S)) := fun d =>
  liftM ((specA (WA AR AC) X G G S).query (.inl (.inr d)))

/-- The finishing phase inside the composed adversary. -/
def liftV : QueryImpl (specV AC X G) (OracleComp (specA (WA AR AC) X G G S))
  | .inl d => liftM ((specA (WA AR AC) X G G S).query (.inl (.inr d)))
  | .inr q => liftM ((specA (WA AR AC) X G G S).query (.inr (.inl q)))

variable (cl : Client AC X G S St Cn PK) (n : ℕ)

/-- **The blinding forger's handler** for `B`'s queries. -/
def blindImpl (pk : PK) (κ : Cn) :
    QueryImpl (specB AR X' Hn' G S) (StateT (BSt X G Hn' St X') (OracleComp (specA (WA AR AC) X G G S)))
  | .inl d => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specA (WA AR AC) X G G S).query (.inl (.inl d))) :
        OracleComp (specA (WA AR AC) X G G S) (AR d))
  | .inr (.inl (x', hB)) => StateT.mk fun s =>
      if s.k < n then do
        let o ← simulateQ liftC (cl.start pk κ s.k)
        let a ← (liftM ((specA (WA AR AC) X G G S).query (.inr (.inl (o.1, o.2.1)))) :
          OracleComp (specA (WA AR AC) X G G S) (G × G))
        pure (some (a.1 + o.2.1),
          ⟨s.k + 1, Function.update s.ses x' (some ⟨s.k, o.1, o.2.1, o.2.2, a.1, hB⟩)⟩)
      else pure (none, s)
  | .inr (.inr t) => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specA (WA AR AC) X G G S).query (.inr (.inr t))) :
        OracleComp (specA (WA AR AC) X G G S) S)

/-- The initial forger state. -/
def bs0 : BSt X G Hn' St X' := ⟨0, fun _ => none⟩

/-- The claimed sessions: for each claim `(x', s)` of `B` with a session, the session's data and
`s`. -/
def claimed (z : List (X' × S) × BSt X G Hn' St X') : List (X × G × St × G × S) :=
  z.1.filterMap fun p => (z.2.ses p.1).map fun e => (e.x, e.r, e.st, e.u, p.2)

/-- **The blinding forger** (a composed adversary of `OneMore.omuf`, hints the blindings): `B`
with its requests answered by fresh sessions, then the client's finishing phase. Its claims are
the claimed sessions' labels with `B`'s preimages. -/
def blindAdv (B : PK → ProbComp (OracleComp (specB AR X' Hn' G S) (List (X' × S)))) (pk : PK) :
    ProbComp (OracleComp (specA (WA AR AC) X G G S) (List (X × S) × Bool)) := do
  let b ← B pk
  let κ ← cl.coins
  pure do
    let z ← (simulateQ (blindImpl cl n pk κ) b).run bs0
    let f ← simulateQ liftV (cl.post pk κ (claimed z))
    pure ((claimed z).map fun e => (e.1, e.2.2.2.2), f)

/-! ## The forger against the challenger (`red` of `OneMore`), collapsed -/

section Comb

set_option linter.unusedSectionVars false

variable (pre : G → S) (pk : PK) (κ : Cn)

/-- The state of the forger run by `red` against the challenger. -/
abbrev CSt {DR DC : Type} (AR : DR → Type) (AC : DC → Type) (X' X G Hn' St : Type) :=
  BSt X G Hn' St X' × ((X → Option (G × G)) × Ch (WA AR AC) X G G)

/-- The forger, `red` and the challenger as one handler. -/
def bcomb : QueryImpl (specB AR X' Hn' G S) (StateT (CSt AR AC X' X G Hn' St) ProbComp) :=
  fun q => StateT.mk fun s => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (combImpl addHint pre) ((blindImpl cl n pk κ q).run s.1)).run s.2

theorem collapseB {α : Type} (oa : OracleComp (specB AR X' Hn' G S) α) (s : BSt X G Hn' St X')
    (c : (X → Option (G × G)) × Ch (WA AR AC) X G G) :
    (simulateQ (combImpl addHint pre) ((simulateQ (blindImpl cl n pk κ) oa).run s)).run c =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (bcomb cl n pre pk κ) oa).run (s, c) := by
  refine simulateQ_StateT_StateT_compose _ _ _ (fun q s c => ?_) oa s c
  show _ = _ <$> ((fun r : (_ × _) × _ => (r.1.1, (r.1.2, r.2))) <$> _)
  rw [Functor.map_map]
  exact (id_map _).symm

/-- `B`'s part of the composed world's cache. -/
def resL (c : (specR (WA AR AC)).QueryCache) : (specR AR).QueryCache :=
  QueryCache.ofFn fun d => c (.inl d)

lemma resL_cacheQuery_inl (c : (specR (WA AR AC)).QueryCache) (d : DR) (u : AR d) :
    resL (c.cacheQuery (.inl d) u) = (resL c).cacheQuery d u := by
  refine QueryCache.ext fun d' => ?_
  show (c.cacheQuery (.inl d) u) (.inl d') = ((resL c).cacheQuery d u) d'
  by_cases h : d' = d
  · subst h
    erw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
    rfl
  · show Function.update c.toFn (.inl d) (some u) (.inl d') =
      Function.update (resL c).toFn d (some u) d'
    rw [Function.update_of_ne (by simpa using h), Function.update_of_ne h]
    rfl

lemma resL_cacheQuery_inr (c : (specR (WA AR AC)).QueryCache) (d : DC) (u : AC d) :
    resL (c.cacheQuery (.inr d) u) = resL c := by
  refine QueryCache.ext fun d' => ?_
  show Function.update c.toFn (.inr d) (some u) (.inl d') = c (.inl d')
  rw [Function.update_of_ne (by simp)]

/-- **`B`'s world in the composed world is `B`'s world**: a query at `inl d`, restricted to `B`'s
part of the cache. -/
lemma roL (c : (specR (WA AR AC)).QueryCache) (d : DR) :
    (fun r => (r.1, resL r.2)) <$> ((specR (WA AR AC)).randomOracle (.inl d)).run c =
      (((specR AR).randomOracle d).run (resL c) : ProbComp (AR d × (specR AR).QueryCache)) := by
  rw [randomOracle.run_eq, randomOracle.run_eq]
  have h' : (resL c) d = c (.inl d) := rfl
  rw [h']
  cases h : c (.inl d) with
  | some u => simp
  | none =>
    simp only [map_bind, map_pure]
    show ($ᵗ (AR d)) >>= (fun a => pure (a, resL (c.cacheQuery (Sum.inl d) a))) = _
    congr 1
    funext a
    rw [resL_cacheQuery_inl]

/-- The client's oracle leaves `B`'s part of the cache alone. -/
lemma roR_resL (c : (specR (WA AR AC)).QueryCache) (d : DC) :
    ∀ z ∈ support (((specR (WA AR AC)).randomOracle (.inr d)).run c), resL z.2 = resL c := by
  intro z hz
  rw [randomOracle.run_eq] at hz
  cases h : c (.inr d) with
  | some u =>
    simp only [h, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | none =>
    simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact resL_cacheQuery_inr c d u

/-! ### The steps -/

lemma bcomb_inl (d : DR) (w : CSt AR AC X' X G Hn' St) :
    (bcomb cl n pre pk κ (.inl d)).run w =
      ((fun r => ((r.1 : AR d), (w.1, (w.2.1, r.2)))) <$>
        (roStep (Sum.inl d) w.2.2 : ProbComp (AR d × Ch (WA AR AC) X G G)) :
        ProbComp ((specB AR X' Hn' G S).Range (.inl d) × CSt AR AC X' X G Hn' St)) := by
  simp only [bcomb, blindImpl, StateT.run_mk]
  erw [simulateQ_map, simulateQ_spec_query, StateT.run_map, comb_inl]
  simp only [realImpl, StateT.run_mk]
  erw [Functor.map_map, Functor.map_map]

lemma bcomb_iss (t : G) (w : CSt AR AC X' X G Hn' St) :
    (bcomb cl n pre pk κ (.inr (.inr t))).run w =
      pure (pre t, (w.1, (w.2.1, { w.2.2 with iq := w.2.2.iq + 1 }))) := by
  simp only [bcomb, blindImpl, StateT.run_mk]
  erw [simulateQ_map, simulateQ_spec_query, StateT.run_map, comb_iss]
  simp [realImpl]

lemma bcomb_stop (x' : X') (hB : Hn') (w : CSt AR AC X' X G Hn' St) (hk : ¬ w.1.k < n) :
    (bcomb cl n pre pk κ (.inr (.inl (x', hB)))).run w = pure (none, w) := by
  simp [bcomb, blindImpl, hk]

/-- The client's first phase, run against `red` and the challenger. -/
def startRun (w : CSt AR AC X' X G Hn' St) :
    ProbComp ((X × G × St) × ((X → Option (G × G)) × Ch (WA AR AC) X G G)) :=
  (simulateQ (combImpl addHint pre ∘ₛ (liftC (AR := AR) (X := X) (G := G) (S := S)))
    (cl.start pk κ w.1.k)).run w.2

lemma bcomb_serve (x' : X') (hB : Hn') (w : CSt AR AC X' X G Hn' St) (hk : w.1.k < n) :
    (bcomb cl n pre pk κ (.inr (.inl (x', hB)))).run w =
      (startRun cl pre pk κ w >>= fun op =>
        (combImpl (S := S) addHint pre (.inr (.inl (op.1.1, op.1.2.1)))).run op.2 >>= fun ap =>
          pure (some (ap.1.1 + op.1.2.1),
            (BSt.mk (w.1.k + 1) (Function.update w.1.ses x'
              (some (Ses.mk w.1.k op.1.1 op.1.2.1 op.1.2.2 ap.1.1 hB))), ap.2)) :
        ProbComp ((specB AR X' Hn' G S).Range (.inr (.inl (x', hB))) ×
          CSt AR AC X' X G Hn' St)) := by
  simp only [bcomb, blindImpl, hk, ite_true, StateT.run_mk, startRun]
  rw [simulateQ_bind, StateT.run_bind, ← QueryImpl.simulateQ_compose, map_bind]
  refine bind_congr fun op => ?_
  rw [simulateQ_bind, StateT.run_bind, map_bind]
  erw [simulateQ_spec_query]
  refine bind_congr fun ap => ?_
  simp

lemma comb_fresh' (x : X) (h : G) (p : (X → Option (G × G)) × Ch (WA AR AC) X G G)
    (hx : p.1 x = none) (t : G) (r : List G) (hr : p.2.rest = t :: r) :
    (combImpl (S := S) addHint pre (.inr (.inl (x, h)))).run p =
      (pure ((t - h, h), (Function.update p.1 x (some (t - h, h)),
        ⟨p.2.ro, r, Function.update p.2.tg x (some (t, h)), p.2.iq⟩)) :
        ProbComp ((specA (WA AR AC) X G G S).Range (.inr (.inl (x, h))) ×
          ((X → Option (G × G)) × Ch (WA AR AC) X G G))) := by
  simp [combImpl, redImpl, hx]
  erw [simulateQ_spec_query]
  simp [chImpl, hr, addHint, sub_eq_add_neg]

/-- **The client's first phase changes only its own oracle's cache**, and outputs a value of
`start`. -/
lemma startRun_supp (w : CSt AR AC X' X G Hn' St) (z) (hz : z ∈ support (startRun cl pre pk κ w)) :
    z.1 ∈ support (cl.start pk κ w.1.k) ∧ z.2.1 = w.2.1 ∧ z.2.2.rest = w.2.2.rest ∧
      z.2.2.tg = w.2.2.tg ∧ z.2.2.iq = w.2.2.iq ∧ resL z.2.2.ro = resL w.2.2.ro := by
  refine ⟨support_simulateQ_run'_subset (combImpl (S := S) addHint pre ∘ₛ
      (liftC (AR := AR) (X := X) (G := G) (S := S))) (cl.start pk κ w.1.k) w.2 (by
    rw [StateT.run'_eq, support_map]; exact ⟨z, hz, rfl⟩), ?_⟩
  let I : (X → Option (G × G)) × Ch (WA AR AC) X G G → Prop := fun q =>
    q.1 = w.2.1 ∧ q.2.rest = w.2.2.rest ∧ q.2.tg = w.2.2.tg ∧ q.2.iq = w.2.2.iq ∧
      resL q.2.ro = resL w.2.2.ro
  have hI : QueryImpl.PreservesInv (combImpl (S := S) addHint pre ∘ₛ
      (liftC (AR := AR) (X := X) (G := G) (S := S))) I := by
    intro d q hq y hy
    simp only [QueryImpl.apply_compose, liftC] at hy
    erw [simulateQ_spec_query, comb_inl] at hy
    have hy' : y ∈ support ((fun r => (r.1, (q.1, r.2))) <$>
        roStep (AR := WA AR AC) (X := X) (Hn := G) (G := G) (Sum.inr d) q.2) := hy
    simp only [roStep, Functor.map_map, support_map, Set.mem_image] at hy'
    obtain ⟨r, hr, rfl⟩ := hy'
    exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, (roR_resL _ d r hr).trans hq.2.2.2.2⟩
  exact simulateQ_run_preservesInv _ I hI _ w.2 ⟨rfl, rfl, rfl, rfl, rfl⟩ z hz

/-! ### The forger against the challenger is `B` in `omExp` -/

/-- `y` is a label of session `j` (an output of `start j`). -/
def Lab (j : ℕ) (y : X) : Prop := ∃ a ∈ support (cl.start pk κ j), a.1 = y

/-- **The sessions' labels are pairwise distinct** (for PomFRIT: distinct messages). -/
def Distinct : Prop :=
  ∀ i j, i ≠ j → ∀ a ∈ support (cl.start pk κ i), ∀ b ∈ support (cl.start pk κ j), a.1 ≠ b.1

/-- `B`'s challenger state that the forger's state represents: `B`'s part of the world cache, the
stream, for each of `B`'s labels the challenge target of its session's label with `B`'s hint, the
preimage queries. -/
def piB (w : CSt AR AC X' X G Hn' St) : Ch AR X' Hn' G :=
  ⟨resL w.2.2.ro, w.2.2.rest,
    fun x' => (w.1.ses x').bind fun e => (w.2.2.tg e.x).map fun p => (p.1, e.hB), w.2.2.iq⟩

/-- The invariant of the forger's run: one target per remaining session; `red`'s table, the
challenger's labelled targets and the sessions only hold labels of started sessions; each of `B`'s
labels has its own session. -/
structure InvC (w : CSt AR AC X' X G Hn' St) : Prop where
  len : w.2.2.rest.length + w.1.k = n
  rt : ∀ y, w.2.1 y ≠ none → ∃ j < w.1.k, Lab cl pk κ j y
  tg : ∀ y, w.2.2.tg y ≠ none → ∃ j < w.1.k, Lab cl pk κ j y
  ses : ∀ x' e, w.1.ses x' = some e → e.idx < w.1.k ∧ Lab cl pk κ e.idx e.x
  inj : ∀ x' y' e e', w.1.ses x' = some e → w.1.ses y' = some e' → e.idx = e'.idx → x' = y'

lemma fresh_of_inv (hD : Distinct cl pk κ) {w : CSt AR AC X' X G Hn' St} (hw : InvC cl n pk κ w)
    {o : X × G × St} (ho : o ∈ support (cl.start pk κ w.1.k)) :
    w.2.1 o.1 = none ∧ w.2.2.tg o.1 = none ∧ ∀ x' e, w.1.ses x' = some e → e.x ≠ o.1 := by
  have hn : ∀ j < w.1.k, ¬ Lab cl pk κ j o.1 := fun j hj ⟨a, ha, he⟩ =>
    hD j w.1.k (ne_of_lt hj) a ha o ho he
  refine ⟨?_, ?_, fun x' e he hx => ?_⟩
  · by_contra h; obtain ⟨j, hj, hl⟩ := hw.rt _ h; exact hn j hj hl
  · by_contra h; obtain ⟨j, hj, hl⟩ := hw.tg _ h; exact hn j hj hl
  · obtain ⟨hj, hl⟩ := hw.ses x' e he; exact hn _ hj (hx ▸ hl)

lemma pure_eqd_of_eq {α : Type} {a b : α} (h : a = b) :
    (pure a : ProbComp α) =ᵈ (pure b : ProbComp α) := by
  subst h; exact EvalDistEq.rfl

theorem bcomb_step (hD : Distinct cl pk κ) (q : DR ⊕ ((X' × Hn') ⊕ G)) (w : CSt AR AC X' X G Hn' St)
    (hw : InvC cl n pk κ w) :
    (fun z => (z.1, piB z.2)) <$> (bcomb cl n pre pk κ q).run w =ᵈ (chImpl pre q).run (piB w) := by
  rcases q with d | ⟨x', hB⟩ | t
  · rw [bcomb_inl]
    show _ =ᵈ roStep d (piB w)
    simp only [roStep, Functor.map_map]
    erw [← roL w.2.2.ro d, Functor.map_map]
    exact EvalDistEq.rfl
  · by_cases hk : w.1.k < n
    · cases hr : w.2.2.rest with
      | nil => have := hw.len; rw [hr] at this; simp at this; omega
      | cons t r =>
        rw [bcomb_serve cl n pre pk κ x' hB w hk]
        erw [map_bind]
        let C : Ch AR X' Hn' G := ⟨resL w.2.2.ro, r,
          Function.update (piB w).tg x' (some (t, hB)), w.2.2.iq⟩
        refine (EvalDistEq.bind_congr_of_support _ fun op hop => ?_ :
          _ =ᵈ startRun cl pre pk κ w >>= fun _ => pure (some t, C)).trans ?_
        · obtain ⟨ho, h1, h2, h3, h4, h5⟩ := startRun_supp cl pre pk κ w op hop
          obtain ⟨hf1, hf2, hf3⟩ := fresh_of_inv cl n pk κ hD hw ho
          rw [comb_fresh' pre op.1.1 op.1.2.1 op.2 (by rw [h1]; exact hf1) t r (by rw [h2, hr])]
          simp only [pure_bind, sub_add_cancel]
          erw [map_pure]
          refine pure_eqd_of_eq (Prod.ext rfl ?_)
          simp only [piB, C, h3, h4, h5]
          congr 1
          funext y'
          by_cases hy : y' = x'
          · subst hy; simp
          · simp only [Function.update_of_ne hy]
            cases he : w.1.ses y' with
            | none => rfl
            | some e => simp [Function.update_of_ne (hf3 y' e he)]
        · refine (bind_unused _ _).trans ?_
          simp [chImpl, piB, C, hr]
    · have hr : w.2.2.rest = [] := by
        have := hw.len; exact List.eq_nil_of_length_eq_zero (by omega)
      rw [bcomb_stop cl n pre pk κ x' hB w hk]
      simp [chImpl, piB, hr]
  · rw [bcomb_iss]
    simp [chImpl, piB]

theorem bcomb_inv (hD : Distinct cl pk κ) :
    QueryImpl.PreservesInv (bcomb (AR := AR) (X' := X') (Hn' := Hn') cl n pre pk κ)
      (InvC cl n pk κ) := by
  intro q w hw z hz
  rcases q with d | ⟨x', hB⟩ | t
  · rw [bcomb_inl] at hz
    have hz' : z ∈ support ((fun r => ((r.1 : AR d), (w.1, (w.2.1, r.2)))) <$>
        (roStep (Sum.inl d) w.2.2 : ProbComp (AR d × Ch (WA AR AC) X G G))) := hz
    simp only [roStep, Functor.map_map, support_map] at hz'
    obtain ⟨r, -, rfl⟩ := hz'
    exact ⟨hw.len, hw.rt, hw.tg, hw.ses, hw.inj⟩
  · by_cases hk : w.1.k < n
    · cases hr : w.2.2.rest with
      | nil => have := hw.len; rw [hr] at this; simp at this; omega
      | cons t r =>
        simp only [bcomb_serve cl n pre pk κ x' hB w hk, mem_support_bind_iff] at hz
        obtain ⟨op, hop, ap, hap, hz⟩ := hz
        obtain ⟨ho, h1, h2, h3, h4, -⟩ := startRun_supp cl pre pk κ w op hop
        obtain ⟨hf1, hf2, hf3⟩ := fresh_of_inv cl n pk κ hD hw ho
        rw [comb_fresh' pre op.1.1 op.1.2.1 op.2 (by rw [h1]; exact hf1) t r (by rw [h2, hr])]
          at hap
        simp only [support_pure, Set.mem_singleton_iff] at hap hz
        subst hap; subst hz
        have hlen := hw.len
        rw [hr, List.length_cons] at hlen
        have hlab : Lab cl pk κ w.1.k op.1.1 := ⟨op.1, ho, rfl⟩
        refine ⟨by simp; omega, fun y hy => ?_, fun y hy => ?_, fun y' e he => ?_,
          fun y₁ y₂ e₁ e₂ h₁ h₂ hi => ?_⟩
        · by_cases hyx : y = op.1.1
          · exact ⟨w.1.k, Nat.lt_succ_self _, hyx ▸ hlab⟩
          · simp only [Function.update_of_ne hyx, h1] at hy
            obtain ⟨j, hj, hl⟩ := hw.rt y hy
            exact ⟨j, Nat.lt_succ_of_lt hj, hl⟩
        · by_cases hyx : y = op.1.1
          · exact ⟨w.1.k, Nat.lt_succ_self _, hyx ▸ hlab⟩
          · simp only [Function.update_of_ne hyx, h3] at hy
            obtain ⟨j, hj, hl⟩ := hw.tg y hy
            exact ⟨j, Nat.lt_succ_of_lt hj, hl⟩
        · by_cases hy : y' = x'
          · subst hy
            simp only [Function.update_self, Option.some.injEq] at he
            subst he
            exact ⟨Nat.lt_succ_self _, hlab⟩
          · simp only [Function.update_of_ne hy] at he
            obtain ⟨hj, hl⟩ := hw.ses y' e he
            exact ⟨Nat.lt_succ_of_lt hj, hl⟩
        · by_cases hy₁ : y₁ = x' <;> by_cases hy₂ : y₂ = x'
          · rw [hy₁, hy₂]
          · subst hy₁
            simp only [Function.update_self, Option.some.injEq, Function.update_of_ne hy₂] at h₁ h₂
            subst h₁
            exact absurd ((hw.ses y₂ e₂ h₂).1) (by simp at hi; omega)
          · subst hy₂
            simp only [Function.update_self, Option.some.injEq, Function.update_of_ne hy₁] at h₁ h₂
            subst h₂
            exact absurd ((hw.ses y₁ e₁ h₁).1) (by simp at hi; omega)
          · simp only [Function.update_of_ne hy₁, Function.update_of_ne hy₂] at h₁ h₂
            exact hw.inj y₁ y₂ e₁ e₂ h₁ h₂ hi
    · simp only [bcomb_stop cl n pre pk κ x' hB w hk] at hz
      subst hz; exact hw
  · simp only [bcomb_iss] at hz
    subst hz
    exact ⟨hw.len, hw.rt, hw.tg, hw.ses, hw.inj⟩

/-- **The forger against the challenger is `B` in `omExp`**, through `piB`. -/
theorem bcomb_eqd (hD : Distinct cl pk κ) {α : Type} (oa : OracleComp (specB AR X' Hn' G S) α)
    (w : CSt AR AC X' X G Hn' St) (hw : InvC cl n pk κ w) :
    (fun z => (z.1, piB z.2)) <$> (simulateQ (bcomb cl n pre pk κ) oa).run w =ᵈ
      (simulateQ (chImpl pre) oa).run (piB w) :=
  LazyIdeal.simulateQ_proj_eqd_inv _ _ piB (InvC cl n pk κ) (bcomb_inv cl n pre pk κ hD)
    (fun q w hw => bcomb_step cl n pre pk κ hD q w hw) oa w hw

end Comb

/-! ## The finishing phase, and the theorem -/

section Post

set_option linter.unusedSectionVars false

variable (pre : G → S)

set_option linter.unusedSimpArgs false in
/-- **The finishing phase keeps the preimage count and the programmed targets** (it makes no
Issuer query, and the target oracle only programs fresh labels). -/
theorem post_pres {β : Type} (oc : OracleComp (specV AC X G) β)
    (p : (X → Option (G × G)) × Ch (WA AR AC) X G G) (hp : TgInv addHint p) :
    ∀ z ∈ support ((simulateQ (realImpl addHint pre)
        (simulateQ (liftV (AR := AR) (S := S)) oc)).run p),
      z.2.2.iq = p.2.iq ∧ ∀ y v, p.2.tg y = some v → z.2.2.tg y = some v := by
  intro z hz
  rw [← QueryImpl.simulateQ_compose] at hz
  let I : (X → Option (G × G)) × Ch (WA AR AC) X G G → Prop := fun q =>
    q.2.iq = p.2.iq ∧ (∀ y v, p.2.tg y = some v → q.2.tg y = some v) ∧ TgInv addHint q
  have hI : QueryImpl.PreservesInv (realImpl (S := S) addHint pre ∘ₛ
      (liftV (AR := AR) (S := S))) I := by
    intro qq q hq y hy
    have hT := tgInv_preserved (AR := WA AR AC) (X := X) (S := S) addHint pre
    rcases qq with d | ⟨x, h⟩
    · simp only [QueryImpl.apply_compose, liftV] at hy
      erw [simulateQ_spec_query] at hy
      have hy' : y ∈ support ((fun r => (r.1, (q.1, r.2))) <$>
          roStep (AR := WA AR AC) (X := X) (Hn := G) (G := G) (Sum.inr d) q.2) := hy
      simp only [roStep, Functor.map_map, support_map, Set.mem_image] at hy'
      obtain ⟨r, -, rfl⟩ := hy'
      exact ⟨hq.1, hq.2.1, hq.2.2⟩
    · simp only [QueryImpl.apply_compose, liftV] at hy
      erw [simulateQ_spec_query] at hy
      have hTy := hT (Sum.inr (Sum.inl (x, h))) q hq.2.2 y hy
      simp only [realImpl] at hy
      subst hy
      refine ⟨?_, fun y' v hv => ?_, hTy⟩
      · cases hx : q.1 x with
        | some a => simp [hx, hq.1]
        | none => cases hr : q.2.rest <;> simp [hx, hr, hq.1]
      · have hv' := hq.2.1 y' v hv
        cases hx : q.1 x with
        | some a => simpa [hx] using hv'
        | none =>
          have hne : y' ≠ x := by
            rintro rfl
            obtain ⟨a, ha, -⟩ := hq.2.2 y' v.1 v.2 hv'
            simp [hx] at ha
          cases hr : q.2.rest <;> simp [hx, hr, Function.update_of_ne hne, hv']
  obtain ⟨h1, h2, -⟩ := simulateQ_run_preservesInv _ I hI oc p ⟨rfl, fun _ _ h => h, hp⟩ z hz
  exact ⟨h1, h2⟩

lemma length_filterMap_of_isSome {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, (f a).isSome) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h a List.mem_cons_self)
    simp [hb,
      length_filterMap_of_isSome f l fun x hx => h x (List.mem_cons_of_mem _ hx)]

variable (cl : Client AC X G S St Cn PK) (n : ℕ) (pk : PK) (κ : Cn)

/-- **`B`'s win is the forger's**: `B`'s `ℓ + 1` good claims on distinct labels become `ℓ + 1`
preimages of the programmed targets of its sessions' labels, which are distinct. -/
theorem win_mid (hD : Distinct cl pk κ) (rel : PK → S → G → Prop) (ℓ : ℕ) (pk' : PK)
    (z : List (X' × S)) (w : CSt AR AC X' X G Hn' St) (hw : InvC cl n pk κ w)
    (hW : Wins ℓ (goodPre rel) pk' z (piB w)) :
    Wins ℓ (goodPre rel) pk' ((claimed (z, w.1)).map fun e => (e.1, e.2.2.2.2)) w.2.2 := by
  obtain ⟨hlen, hnd, hiq, hg⟩ := hW
  have hs : ∀ p ∈ z, ∃ e, w.1.ses p.1 = some e ∧ ∃ t h, w.2.2.tg e.x = some (t, h) ∧
      rel pk' p.2 t := by
    intro p hp
    obtain ⟨t, h, ht, hr⟩ := hg p hp
    simp only [piB, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at ht
    obtain ⟨e, he, a, ha, rfl, -⟩ := ht
    exact ⟨e, he, a.1, a.2, ha, hr⟩
  refine ⟨?_, ?_, hiq, ?_⟩
  · simp only [claimed, List.length_map]
    refine (length_filterMap_of_isSome _ z fun p hp => ?_).trans hlen
    obtain ⟨e, he, -⟩ := hs p hp
    simp [he]
  · have heq : ((claimed (z, w.1)).map fun e => (e.1, e.2.2.2.2)).map Prod.fst =
        (z.map Prod.fst).filterMap fun x' => (w.1.ses x').map Ses.x := by
      simp [claimed, List.map_filterMap, List.filterMap_map, Function.comp_def]
    rw [heq]
    refine List.Nodup.filterMap (fun x' y' b hx hy => ?_) hnd
    simp only [Option.mem_def, Option.map_eq_some_iff] at hx hy
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨e', he', hee⟩ := hy
    refine hw.inj x' y' e e' he he' ?_
    by_contra hne
    obtain ⟨-, a, ha, hax⟩ := hw.ses x' e he
    obtain ⟨-, a', ha', hax'⟩ := hw.ses y' e' he'
    exact hD _ _ hne a ha a' ha' (hax.trans (hee.symm.trans hax'.symm) |>.symm ▸ rfl)
  · intro q hq
    simp only [claimed, List.mem_map, List.mem_filterMap, Option.map_eq_some_iff] at hq
    obtain ⟨_, ⟨p, hp, e, he, rfl⟩, rfl⟩ := hq
    obtain ⟨e', he', t, h, ht, hr⟩ := hs p hp
    rw [he, Option.some.injEq] at he'
    subst he'
    exact ⟨t, h, ht, hr⟩

end Post

section Main

set_option linter.unusedSectionVars false

variable [SampleableType G] {SK : Type}

/-- **Theorem 6, generic core** (`uov-assumptions.md` §5.6): for every OMPR adversary `B` and every
client whose sessions have distinct labels,

    Adv^{ompr}(B; n, ℓ) ≤ Pr[Forges] + Pr[CompFail]

in the one-more game (`OneMore.omuf`, programmed targets `H_T(x) + r`) of the blinding forger
`blindAdv cl n B`; `CompFail`: the forger's claims are `ℓ + 1` preimages of the programmed targets
of distinct labels within `ℓ` Issuer queries, and the client's finishing phase rejects. -/
theorem ompr_le_blind (tr : Trapdoor PK SK G S) (cl : Client AC X G S St Cn PK) (n ℓ : ℕ)
    (B : PK → ProbComp (OracleComp (specB AR X' Hn' G S) (List (X' × S))))
    (hD : ∀ pk, ∀ κ ∈ support cl.coins, Distinct cl pk κ) :
    advOMPR tr n ℓ B ≤
      Pr{let r ← omuf tr.keyGen tr.D n addHint (blindAdv cl n B)}[Forges ℓ r.2.1 r.2.2.2] +
      Pr{let r ← omuf tr.keyGen tr.D n addHint (blindAdv cl n B)}[
        Wins ℓ (goodPre tr.IsPre) r.1 r.2.1.1 r.2.2.2 ∧ r.2.1.2 = false] := by
  set O := omuf tr.keyGen tr.D n addHint (blindAdv cl n B) with hOdef
  -- a win at the end is a forgery or a completeness failure
  have hsplit : Pr{let r ← O}[Wins ℓ (goodPre tr.IsPre) r.1 r.2.1.1 r.2.2.2] ≤
      Pr{let r ← O}[Forges ℓ r.2.1 r.2.2.2] +
      Pr{let r ← O}[Wins ℓ (goodPre tr.IsPre) r.1 r.2.1.1 r.2.2.2 ∧ r.2.1.2 = false] := by
    refine (prEvent_mono _ _ _ fun r h => ?_).trans (prEvent_or_le _ _ _)
    by_cases hf : r.2.1.2 = true
    · exact Or.inl ⟨hf, h.1, h.2.1, h.2.2.1⟩
    · exact Or.inr ⟨h, by simpa using hf⟩
  refine le_trans ?_ hsplit
  -- the blinding phase in the real game
  let RM : PK × SK → Cn → OracleComp (specB AR X' Hn' G S) (List (X' × S)) → List G →
      ProbComp ((List (X' × S) × BSt X G Hn' St X') × ((X → Option (G × G)) × Ch (WA AR AC) X G G)) :=
    fun kp κ b L => (simulateQ (realImpl addHint (tr.D kp.2))
      ((simulateQ (blindImpl cl n kp.1 κ) b).run bs0)).run (fun _ => none, ch0 L)
  let M1 := do
    let kp ← tr.keyGen
    let b ← B kp.1
    let κ ← cl.coins
    let L ← unifList G n
    let m ← RM kp κ b L
    pure (kp, κ, m)
  let Wmid : (PK × SK) × Cn × ((List (X' × S) × BSt X G Hn' St X') ×
      ((X → Option (G × G)) × Ch (WA AR AC) X G G)) → Prop :=
    fun t => Wins ℓ (goodPre tr.IsPre) t.1.1 ((claimed t.2.2.1).map fun e => (e.1, e.2.2.2.2))
      t.2.2.2.2
  have h1 : Pr{let t ← M1}[Wmid t] ≤ Pr{let r ← O}[Wins ℓ (goodPre tr.IsPre) r.1 r.2.1.1 r.2.2.2] := by
    have hO : O = M1 >>= fun t => (fun r => (t.1.1, ((claimed t.2.2.1).map fun e => (e.1, e.2.2.2.2),
        r.1), r.2)) <$> (simulateQ (realImpl addHint (tr.D t.1.2))
          (simulateQ (liftV (AR := AR) (S := S)) (cl.post t.1.1 t.2.1 (claimed t.2.2.1)))).run
            t.2.2.2 := by
      simp only [hOdef, omuf, M1, RM, blindAdv, bind_assoc, pure_bind, simulateQ_bind,
        StateT.run_bind, simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp,
        Function.comp_def]
    rw [hO]
    refine LazyIdeal.prEvent_le_bind _ _ _ _ fun t ht hW y hy => ?_
    simp only [M1, RM, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ht
    obtain ⟨kp, -, b, -, κ, -, L, -, m, hm, rfl⟩ := ht
    have hT := simulateQ_run_preservesInv (realImpl addHint (tr.D kp.2)) (TgInv addHint)
      (tgInv_preserved addHint (tr.D kp.2)) _ _ (fun x t h hx => by simp [ch0] at hx) m hm
    simp only [support_map, Set.mem_image] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    obtain ⟨hiq, htg⟩ := post_pres (tr.D kp.2) _ m.2 hT r hr
    obtain ⟨hlen, hnd, hiq', hg⟩ := hW
    refine ⟨hlen, hnd, hiq ▸ hiq', fun p hp => ?_⟩
    obtain ⟨t', h', ht', hrel⟩ := hg p hp
    exact ⟨t', h', htg _ _ ht', hrel⟩
  -- programming is perfect
  let CM : PK × SK → Cn → OracleComp (specB AR X' Hn' G S) (List (X' × S)) → List G →
      ProbComp ((List (X' × S) × BSt X G Hn' St X') × ((X → Option (G × G)) × Ch (WA AR AC) X G G)) :=
    fun kp κ b L => (simulateQ (combImpl addHint (tr.D kp.2))
      ((simulateQ (blindImpl cl n kp.1 κ) b).run bs0)).run (fun _ => none, ch0 L)
  let M2 := do
    let kp ← tr.keyGen
    let b ← B kp.1
    let κ ← cl.coins
    let L ← unifList G n
    let m ← CM kp κ b L
    pure (kp, κ, m)
  have h2 : M1 =ᵈ M2 := by
    simp only [M1, M2, RM, CM]
    refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun b =>
      EvalDistEq.bind_right _ fun κ => ?_
    have := (real_eqd_comb addHint (tr.D kp.2) ((simulateQ (blindImpl cl n kp.1 κ) b).run bs0)
      (fun _ => none) (ch0 []) n).bind_left (fun m => pure (kp, κ, m))
    simpa only [bind_assoc, pure_bind, ch0] using this
  -- the forger against the challenger
  let M3 := do
    let kp ← tr.keyGen
    let b ← B kp.1
    let κ ← cl.coins
    let L ← unifList G n
    let w ← (simulateQ (bcomb cl n (tr.D kp.2) kp.1 κ) b).run (bs0, (fun _ => none, ch0 L))
    pure (kp, κ, w)
  have h3 : M2 = (fun t => (t.1, t.2.1, ((t.2.2.1, t.2.2.2.1), t.2.2.2.2))) <$> M3 := by
    simp only [M2, M3, CM, collapseB, map_bind, map_pure, bind_map_left]
  have hinit : ∀ kp κ L, L ∈ support (unifList G n) →
      InvC (AR := AR) (Hn' := Hn') (X' := X') cl n kp κ (bs0, (fun _ => none, ch0 L)) :=
    fun kp κ L hL => ⟨by simp [ch0, bs0, length_of_mem_unifList n L hL], by simp,
      by simp [ch0], by simp [bs0], by simp [bs0]⟩
  have h4 : Pr{let t ← M3}[Wins ℓ (goodPre tr.IsPre) t.1.1 t.2.2.1 (piB t.2.2.2)] ≤
      Pr{let t ← M2}[Wmid t] := by
    rw [h3, prEvent_map]
    refine prEvent_mono_of_support _ _ _ fun t ht hW => ?_
    simp only [M3, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ht
    obtain ⟨kp, -, b, -, κ, hκ, L, hL, w, hw, rfl⟩ := ht
    have hinv := simulateQ_run_preservesInv (bcomb cl n (tr.D kp.2) kp.1 κ) (InvC cl n kp.1 κ)
      (bcomb_inv cl n (tr.D kp.2) kp.1 κ (hD kp.1 κ hκ)) b _ (hinit kp.1 κ L hL) w hw
    exact win_mid cl n kp.1 κ (hD kp.1 κ hκ) tr.IsPre ℓ kp.1 w.1 w.2 hinv hW
  -- `B` in `omExp`
  have h5 : advOMPR tr n ℓ B =
      Pr{let t ← M3}[Wins ℓ (goodPre tr.IsPre) t.1.1 t.2.2.1 (piB t.2.2.2)] := by
    have hE : omExp tr.keyGen tr.D n B =ᵈ
        (fun t => (t.1.1, t.2.2.1, piB t.2.2.2)) <$> M3 := by
      simp only [omExp, M3, map_bind, map_pure]
      refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun b => ?_
      refine (bind_unused cl.coins _).symm.trans (EvalDistEq.bind_congr_of_support _ fun κ hκ => ?_)
      refine EvalDistEq.bind_congr_of_support _ fun L hL => ?_
      have hp : piB (AR := AR) (AC := AC) (X' := X') (Hn' := Hn') (St := St) (X := X)
          (bs0, (fun _ => none, ch0 L)) = ch0 L := by
        simp only [piB, ch0, bs0]
        congr 1
      have := (bcomb_eqd cl n (tr.D kp.2) kp.1 κ (hD kp.1 κ hκ) b _
        (hinit kp.1 κ L hL)).symm.bind_left (fun r => pure (kp.1, r.1, r.2))
      rw [hp] at this
      simpa only [bind_map_left] using this
    unfold advOMPR
    rw [hE.prEvent_eq, prEvent_map]
  rw [h5]
  exact h4.trans ((h2.prEvent_eq _).symm ▸ h1)

end Main

end VoleMole.Assumptions.Blind
