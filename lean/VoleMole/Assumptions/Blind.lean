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
              (some (Ses.mk w.1.k op.1.1 op.1.2.1 op.1.2.2 ap.1.1 hB))), ap.2))) := by
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
      pure ((t - h, h), (Function.update p.1 x (some (t - h, h)),
        ⟨p.2.ro, r, Function.update p.2.tg x (some (t, h)), p.2.iq⟩)) := by
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

end Comb

end VoleMole.Assumptions.Blind
