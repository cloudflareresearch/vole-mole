import VoleMole.Assumptions.UOV
import VCVio.EvalDist.ProbabilityBounds

/-!
# OMPR and OMPR⊕τ: the two reductions between them

`lean/docs/security/uov-assumptions.md` §6 (Proposition 8(a)) and
`lean/docs/security/uov-open-reductions.md` §4.1 (Proposition A1), on the games of
`Assumptions/UOV.lean` (`advOMPR`, `advOMPRShift`). Protocol-independent.

* **A1** (`advOMPR_le_shift`): `Adv^{ompr}(B; n, ℓ) ≤ Adv^{ompr⊕τ}(B₀; n, ℓ)` for `τ ≥ 1`, with
  `B₀ = shiftZero B` the same adversary sending the shift list `[0]` with each request. Tight.
  And `advOMPRShift_mono`: the τ-shift advantage grows with `τ` (same adversary).
* **P8(a)** (`advOMPRShift_le_guess`): `Adv^{ompr⊕τ}(B; n, ℓ) ≤ τ^{ℓ+1} · Adv^{ompr}(R; n, ℓ)` for
  `τ ≥ 1`, with `R = guessRed B` explicit: it draws a guess `g k ∈ [τ]` for each of the `n`
  requests, answers request `k` with the shift list `δs` by `t − δs[g k]` for a fresh challenge `t`,
  and names each claim by its label and request index. `R` is `OneMore.red addHint` of an adapter;
  the proof uses OneMore's perfect programming (`omuf_good_le`), an exact simulation of the
  adapter by the shift game (`adReal_eqd`, `recCh_eqd`) and a count of the guess vectors
  (`guess_count`, `pr_guess_ge`). Names live in `VoleMole.Assumptions.Shift`.

**A simulation lemma** (`LazyIdeal.simulateQ_proj_eqd_inv`, in `Assumptions/LazyIdeal.lean`): if
each query of one stateful handler, projected along `π`, is equal in distribution to another
handler's on the projected state (under an invariant), so is every computation. Used for A1, P8(a)
and `Assumptions/Blind.lean`.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.ROM.OneMore
open scoped ENNReal

namespace VoleMole.Assumptions.Shift

open VoleMole.Assumptions.LazyIdeal (simulateQ_proj_eqd_inv)

open VoleMole.Assumptions.UOV

/-! ## A1: OMPR from OMPR⊕τ, tightly -/

section A1

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn G S : Type} [AddCommGroup G] [SampleableType G]

/-- The zero-shift adapter: every request carries the shift list `[0]`. -/
def zImpl : QueryImpl (specB AR X Hn G S) (OracleComp (specB AR X (List G) G S))
  | .inl d => liftM ((specB AR X (List G) G S).query (.inl d))
  | .inr (.inl (x, _)) => liftM ((specB AR X (List G) G S).query (.inr (.inl (x, [0]))))
  | .inr (.inr t) => liftM ((specB AR X (List G) G S).query (.inr (.inr t)))

variable {PK : Type}

/-- **The A1 adversary**: `B` with the shift list `[0]` sent with each request. -/
def shiftZero (B : PK → ProbComp (OracleComp (specB AR X Hn G S) (List (X × S)))) (pk : PK) :
    ProbComp (OracleComp (specB AR X (List G) G S) (List (X × S))) :=
  simulateQ zImpl <$> B pk

/-- The challenger state with every hint replaced by `[0]`. -/
def zProj (c : Ch AR X Hn G) : Ch AR X (List G) G :=
  ⟨c.ro, c.rest, fun x => (c.tg x).map fun p => (p.1, [0]), c.iq⟩

omit [SampleableType G] in
theorem zImpl_step (pre : G → S) (q : DR ⊕ ((X × Hn) ⊕ G)) (c : Ch AR X Hn G) :
    (fun z => (z.1, zProj z.2)) <$> (chImpl pre q).run c =
      ((chImpl pre ∘ₛ zImpl) q).run (zProj c) := by
  rcases q with d | ⟨x, h⟩ | t
  · simp only [QueryImpl.apply_compose, zImpl]
    erw [simulateQ_spec_query]
    simp [chImpl, roStep, zProj]
  · simp only [QueryImpl.apply_compose, zImpl]
    erw [simulateQ_spec_query]
    cases hr : c.rest with
    | nil => simp [chImpl, zProj, hr]
    | cons u r =>
      simp only [chImpl, zProj, hr, StateT.run_mk, map_pure]
      congr 3
      funext y
      by_cases hy : y = x
      · subst hy; simp
      · simp [Function.update_of_ne hy]
  · simp only [QueryImpl.apply_compose, zImpl]
    erw [simulateQ_spec_query]
    simp [chImpl, zProj]

variable {SK : Type} (tr : Trapdoor PK SK G S)

omit [SampleableType G] in
theorem goodShift_of_goodPre {τ : ℕ} (hτ : 1 ≤ τ) (pk : PK) (s : S) (tg : Option (G × Hn))
    (h : goodPre tr.IsPre pk s tg) : goodShift τ tr.IsPre pk s (tg.map fun p => (p.1, [0])) := by
  obtain ⟨t, h', rfl, hp⟩ := h
  exact ⟨t, [0], rfl, by simpa using hτ, 0, List.mem_singleton_self _, by simpa using hp⟩

/-- **Proposition A1** (`uov-open-reductions.md` §4.1): OMPR⊕τ implies OMPR without loss. For
`τ ≥ 1` every OMPR adversary `B` is matched by `shiftZero B`, which sends the shift `0` with each
request, with at least the same advantage (the runs correspond exactly). -/
theorem advOMPR_le_shift {τ : ℕ} (hτ : 1 ≤ τ) (n ℓ : ℕ)
    (B : PK → ProbComp (OracleComp (specB AR X Hn G S) (List (X × S)))) :
    advOMPR tr n ℓ B ≤ advOMPRShift tr τ n ℓ (shiftZero B) := by
  have hE : omExp tr.keyGen tr.D n (shiftZero B) =ᵈ
      (fun r => (r.1, r.2.1, zProj r.2.2)) <$> omExp tr.keyGen tr.D n B := by
    simp only [omExp, shiftZero, map_bind, map_pure, bind_map_left]
    refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun b =>
      EvalDistEq.bind_right _ fun L => ?_
    have h := simulateQ_proj_eqd_inv (chImpl (tr.D kp.2)) (chImpl (tr.D kp.2) ∘ₛ zImpl) zProj
      (fun _ => True) (fun _ _ _ _ _ => trivial)
      (fun q s _ => by rw [zImpl_step]) b (ch0 L) trivial
    have h0 : zProj (ch0 L : Ch AR X Hn G) = ch0 L := by
      rfl
    rw [h0, QueryImpl.simulateQ_compose] at h
    have := h.symm.bind_left (fun r => pure (kp.1, r.1, r.2))
    simpa only [bind_map_left] using this
  unfold advOMPR advOMPRShift
  rw [hE.prEvent_eq, prEvent_map]
  refine prEvent_mono _ _ _ fun r hw => ?_
  obtain ⟨hlen, hnd, hiq, hg⟩ := hw
  exact ⟨hlen, hnd, hiq, fun p hp => goodShift_of_goodPre tr hτ r.1 p.2 _ (hg p hp)⟩

omit [SampleableType G] in
theorem goodShift_mono {τ τ' : ℕ} (h : τ ≤ τ') {pk : PK} {s : S} {tg : Option (G × List G)}
    (hg : goodShift τ tr.IsPre pk s tg) : goodShift τ' tr.IsPre pk s tg := by
  obtain ⟨t, δs, rfl, hl, hδ⟩ := hg
  exact ⟨t, δs, rfl, hl.trans h, hδ⟩

/-- **More shifts help** (`uov-open-reductions.md` §4.1): `Adv^{ompr⊕τ} ≤ Adv^{ompr⊕τ'}` for
`τ ≤ τ'`, the same adversary. -/
theorem advOMPRShift_mono {τ τ' : ℕ} (h : τ ≤ τ') (n ℓ : ℕ)
    (B : PK → ProbComp (OracleComp (specB AR X (List G) G S) (List (X × S)))) :
    advOMPRShift tr τ n ℓ B ≤ advOMPRShift tr τ' n ℓ B :=
  prEvent_mono _ _ _ fun _ ⟨hl, hn, hi, hg⟩ =>
    ⟨hl, hn, hi, fun p hp => goodShift_mono tr h (hg p hp)⟩

end A1

/-! ## P8(a): OMPR⊕τ from OMPR, by guessing the shift of each request -/

section Guess

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {G S : Type} [AddCommGroup G] [SampleableType G]

variable (X G) in
/-- The adapter's state: the number of requests served, and for each label the index of its
latest request and its shift list. -/
structure AdSt where
  k : ℕ
  idx : X → Option (ℕ × List G)

/-- The initial adapter state. -/
def ad0 : AdSt X G := ⟨0, fun _ => none⟩

/-- The adapter's record of a served request `k` for label `x` with shifts `δs`. -/
def AdSt.push (s : AdSt X G) (x : X) (δs : List G) : AdSt X G :=
  ⟨s.k + 1, Function.update s.idx x (some (s.k, δs))⟩

/-- The shift guessed for request `k`: entry `g k` of the shift list (`0` if there is none). -/
def gShift (g : ℕ → ℕ) (k : ℕ) (δs : List G) : G := (δs[g k]?).getD 0

/-- **The guessing adapter** (an adversary of the composed form of `OneMore`, labels `(x, k)`,
hints the guessed shift): world and preimage queries forwarded; the `k`-th request `(x, δs)`
(`k < n`) becomes a target query at the fresh label `(x, k)` with the hint `δs[g k]`, and its
answer is passed on; past `n` requests, `none`. -/
def adImpl (n : ℕ) (g : ℕ → ℕ) :
    QueryImpl (specB AR X (List G) G S) (StateT (AdSt X G) (OracleComp (specA AR (X × ℕ) G G S)))
  | .inl d => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specA AR (X × ℕ) G G S).query (.inl d)) : OracleComp (specA AR (X × ℕ) G G S) (AR d))
  | .inr (.inl (x, δs)) => StateT.mk fun s =>
      if s.k < n then
        (fun a : G × G => (some a.1, s.push x δs)) <$>
          (liftM ((specA AR (X × ℕ) G G S).query (.inr (.inl ((x, s.k), gShift g s.k δs)))) :
            OracleComp (specA AR (X × ℕ) G G S) (G × G))
      else pure (none, s)
  | .inr (.inr t) => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specA AR (X × ℕ) G G S).query (.inr (.inr t))) : OracleComp (specA AR (X × ℕ) G G S) S)

/-- The adapter's claims: each label with the index of its latest request; the flag `true`. -/
def outA (r : List (X × S) × AdSt X G) : List ((X × ℕ) × S) × Bool :=
  (r.1.map fun p => ((p.1, ((r.2.idx p.1).map Prod.fst).getD 0), p.2), true)

/-- A guess vector as a function on request indices. -/
def gfun {n τ : ℕ} (g : Fin n → Fin τ) : ℕ → ℕ := fun k => if h : k < n then (g ⟨k, h⟩ : ℕ) else 0

variable {PK : Type}

/-- The composed adversary: a uniform guess vector, then `B` through the adapter. -/
noncomputable def guessAdv (n τ : ℕ) [SampleableType (Fin n → Fin τ)]
    (B : PK → ProbComp (OracleComp (specB AR X (List G) G S) (List (X × S)))) (pk : PK) :
    ProbComp (OracleComp (specA AR (X × ℕ) G G S) (List ((X × ℕ) × S) × Bool)) := do
  let g ← $ᵗ (Fin n → Fin τ)
  let b ← B pk
  pure (outA <$> (simulateQ (adImpl n (gfun g)) b).run ad0)

/-- **The P8(a) reduction** `R`: an OMPR adversary (labels `(x, k)`, hints `G`) that runs `B`,
answers its `k`-th request `(x, δs)` with `t − δs[g k]` for a fresh challenge `t` requested for
the label `(x, k)`, and forwards everything else (`OneMore.red addHint` of `guessAdv`). -/
noncomputable def guessRed (n τ : ℕ) [SampleableType (Fin n → Fin τ)]
    (B : PK → ProbComp (OracleComp (specB AR X (List G) G S) (List (X × S)))) :
    PK → ProbComp (OracleComp (specB AR (X × ℕ) G G S) (List ((X × ℕ) × S))) :=
  red addHint (guessAdv n τ B)

end Guess

section GuessSim

set_option linter.unusedSectionVars false

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {G S : Type} [AddCommGroup G]

variable (AR X G) in
/-- The state of the adapter run in the real one-more game: the adapter's state, the target
oracle's table, the challenger. -/
abbrev RSt := AdSt X G × ((X × ℕ → Option (G × G)) × Ch AR (X × ℕ) G G)

variable (pre : G → S) (n : ℕ) (g : ℕ → ℕ)

/-- The adapter run in the real one-more game (`realImpl addHint`), as one handler. -/
def adReal : QueryImpl (specB AR X (List G) G S) (StateT (RSt AR X G) ProbComp) :=
  fun q => StateT.mk fun s => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (realImpl addHint pre) ((adImpl n g q).run s.1)).run s.2

theorem collapseAd {α : Type} (oa : OracleComp (specB AR X (List G) G S) α) (s : AdSt X G)
    (c : (X × ℕ → Option (G × G)) × Ch AR (X × ℕ) G G) :
    (simulateQ (realImpl addHint pre) ((simulateQ (adImpl n g) oa).run s)).run c =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (adReal pre n g) oa).run (s, c) := by
  refine simulateQ_StateT_StateT_compose _ _ _ (fun q s c => ?_) oa s c
  show _ = _ <$> ((fun r : (_ × _) × _ => (r.1.1, (r.1.2, r.2))) <$> _)
  rw [Functor.map_map]
  exact (id_map _).symm

/-- The recording handler: `B`'s queries forwarded unchanged; a served request is recorded as
`AdSt.push`. -/
def recImpl :
    QueryImpl (specB AR X (List G) G S) (StateT (AdSt X G) (OracleComp (specB AR X (List G) G S)))
  | .inl d => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specB AR X (List G) G S).query (.inl d)) : OracleComp (specB AR X (List G) G S) (AR d))
  | .inr (.inl (x, δs)) => StateT.mk fun s =>
      (fun a : Option G => (a, match a with | some _ => s.push x δs | none => s)) <$>
        (liftM ((specB AR X (List G) G S).query (.inr (.inl (x, δs)))) :
          OracleComp (specB AR X (List G) G S) (Option G))
  | .inr (.inr t) => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specB AR X (List G) G S).query (.inr (.inr t))) : OracleComp (specB AR X (List G) G S) S)

/-- The recording handler run against the τ-shift challenger, as one handler. -/
def recCh : QueryImpl (specB AR X (List G) G S) (StateT (AdSt X G × Ch AR X (List G) G) ProbComp) :=
  fun q => StateT.mk fun s => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (chImpl pre) ((recImpl q).run s.1)).run s.2

theorem collapseRec {α : Type} (oa : OracleComp (specB AR X (List G) G S) α) (s : AdSt X G)
    (c : Ch AR X (List G) G) :
    (simulateQ (chImpl pre) ((simulateQ recImpl oa).run s)).run c =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (recCh pre) oa).run (s, c) := by
  refine simulateQ_StateT_StateT_compose _ _ _ (fun q s c => ?_) oa s c
  show _ = _ <$> ((fun r : (_ × _) × _ => (r.1.1, (r.1.2, r.2))) <$> _)
  rw [Functor.map_map]
  exact (id_map _).symm

/-! ### The steps, explicitly -/

lemma adReal_inl (d : DR) (w : RSt AR X G) :
    (adReal (S := S) pre n g (.inl d)).run w =
      ((fun r => (r.1, (w.1, (w.2.1, r.2)))) <$> roStep d w.2.2 :
        ProbComp ((specB AR X (List G) G S).Range (.inl d) × RSt AR X G)) := by
  simp only [adReal, adImpl, StateT.run_mk]
  erw [simulateQ_map, simulateQ_spec_query]
  simp [realImpl, Functor.map_map]

lemma adReal_iss (t : G) (w : RSt AR X G) :
    (adReal (S := S) pre n g (.inr (.inr t))).run w =
      pure (pre t, (w.1, (w.2.1, { w.2.2 with iq := w.2.2.iq + 1 }))) := by
  simp only [adReal, adImpl, StateT.run_mk]
  erw [simulateQ_map, simulateQ_spec_query]
  simp [realImpl]

lemma adReal_stop (x : X) (δs : List G) (w : RSt AR X G) (hk : ¬ w.1.k < n) :
    (adReal (S := S) pre n g (.inr (.inl (x, δs)))).run w = pure (none, w) := by
  simp [adReal, adImpl, hk]

lemma adReal_serve (x : X) (δs : List G) (w : RSt AR X G) (hk : w.1.k < n)
    (hh : w.2.1 (x, w.1.k) = none) (u : G) (r : List G) (hr : w.2.2.rest = u :: r) :
    (adReal (S := S) pre n g (.inr (.inl (x, δs)))).run w =
      pure (some u, (w.1.push x δs,
        (Function.update w.2.1 (x, w.1.k) (some (u, gShift g w.1.k δs)),
          ⟨w.2.2.ro, r, Function.update w.2.2.tg (x, w.1.k)
              (some (u + gShift g w.1.k δs, gShift g w.1.k δs)), w.2.2.iq⟩))) := by
  simp only [adReal, adImpl, hk, ite_true, StateT.run_mk]
  erw [simulateQ_map, simulateQ_spec_query]
  simp [realImpl, hh, hr, addHint]

lemma recCh_inl (d : DR) (v : AdSt X G × Ch AR X (List G) G) :
    (recCh (S := S) pre (.inl d)).run v = ((fun r => (r.1, (v.1, r.2))) <$> roStep d v.2 :
      ProbComp ((specB AR X (List G) G S).Range (.inl d) × (AdSt X G × Ch AR X (List G) G))) := by
  simp only [recCh, recImpl, StateT.run_mk]
  erw [simulateQ_map, simulateQ_spec_query]
  simp [chImpl, Functor.map_map]

lemma recCh_iss (t : G) (v : AdSt X G × Ch AR X (List G) G) :
    (recCh (S := S) pre (.inr (.inr t))).run v = pure (pre t, (v.1, { v.2 with iq := v.2.iq + 1 })) := by
  simp only [recCh, recImpl, StateT.run_mk]
  erw [simulateQ_map, simulateQ_spec_query]
  simp [chImpl]

lemma recCh_nil (x : X) (δs : List G) (v : AdSt X G × Ch AR X (List G) G) (hr : v.2.rest = []) :
    (recCh (S := S) pre (.inr (.inl (x, δs)))).run v = pure (none, v) := by
  simp only [recCh, recImpl, StateT.run_mk]
  erw [simulateQ_map, simulateQ_spec_query]
  simp [chImpl, hr]

lemma recCh_cons (x : X) (δs : List G) (v : AdSt X G × Ch AR X (List G) G) (u : G) (r : List G)
    (hr : v.2.rest = u :: r) :
    (recCh (S := S) pre (.inr (.inl (x, δs)))).run v =
      pure (some u, (v.1.push x δs,
        ⟨v.2.ro, r, Function.update v.2.tg x (some (u, δs)), v.2.iq⟩)) := by
  simp only [recCh, recImpl, StateT.run_mk]
  erw [simulateQ_map, simulateQ_spec_query]
  simp [chImpl, hr]

/-! ### The adapter in the real game is the shift game -/

/-- The τ-shift challenger state that a real-game state of the adapter represents: the label `x`
of a served request `k` has the answer of `(x, k)` and its shift list. -/
def projA (w : RSt AR X G) : AdSt X G × Ch AR X (List G) G :=
  (w.1, ⟨w.2.2.ro, w.2.2.rest,
    fun x => (w.1.idx x).bind fun kd => (w.2.1 (x, kd.1)).map fun a => (a.1, kd.2), w.2.2.iq⟩)

/-- The invariant of the adapter's real run: labels `(x, k)` from the next request on are fresh;
the stream has one target per remaining request; a recorded request's label was answered with the
guessed hint; the ghost targets are the answers plus the hints (no fallback). -/
structure InvA (w : RSt AR X G) : Prop where
  fresh : ∀ x k, w.1.k ≤ k → w.2.1 (x, k) = none
  len : w.2.2.rest.length + w.1.k = n
  idx : ∀ x k δs, w.1.idx x = some (k, δs) → k < w.1.k ∧ ∃ u, w.2.1 (x, k) = some (u, gShift g k δs)
  tg : ∀ y a h, w.2.1 y = some (a, h) → w.2.2.tg y = some (a + h, h)

theorem adReal_step (q : DR ⊕ ((X × List G) ⊕ G)) (w : RSt AR X G) (hw : InvA n g w) :
    (fun z => (z.1, projA z.2)) <$> (adReal (S := S) pre n g q).run w = (recCh pre q).run (projA w) := by
  rcases q with d | ⟨x, δs⟩ | t
  · rw [adReal_inl, recCh_inl]
    simp [projA, roStep, Functor.map_map]
  · by_cases hk : w.1.k < n
    · cases hr : w.2.2.rest with
      | nil => have := hw.len; rw [hr] at this; simp at this; omega
      | cons u r =>
        rw [adReal_serve pre n g x δs w hk (hw.fresh x w.1.k le_rfl) u r hr,
          recCh_cons pre x δs (projA w) u r (by simp [projA, hr])]
        erw [map_pure]
        simp only [projA, AdSt.push]
        congr 4
        funext y
        by_cases hy : y = x
        · subst hy; simp [gShift]
        · simp only [Function.update_of_ne hy]
          cases hi : w.1.idx y with
          | none => rfl
          | some kd =>
            simp only [Option.bind_some]
            rw [Function.update_of_ne (by intro h; exact hy (congrArg Prod.fst h))]
    · have hr : w.2.2.rest = [] := by
        have := hw.len; exact List.eq_nil_of_length_eq_zero (by omega)
      rw [adReal_stop pre n g x δs w hk, recCh_nil pre x δs (projA w) (by simp [projA, hr])]
      simp
  · rw [adReal_iss, recCh_iss]
    simp [projA]

theorem adReal_inv : QueryImpl.PreservesInv (adReal (S := S) (AR := AR) (X := X) pre n g) (InvA n g) := by
  intro q w hw z hz
  rcases q with d | ⟨x, δs⟩ | t
  · simp only [adReal_inl, roStep, Functor.map_map] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨r, -, rfl⟩ := hz
    exact ⟨hw.fresh, hw.len, hw.idx, hw.tg⟩
  · by_cases hk : w.1.k < n
    · cases hr : w.2.2.rest with
      | nil => have := hw.len; rw [hr] at this; simp at this; omega
      | cons u r =>
        simp only [adReal_serve pre n g x δs w hk (hw.fresh x w.1.k le_rfl) u r hr] at hz
        subst hz
        have hlen := hw.len
        rw [hr, List.length_cons] at hlen
        refine ⟨fun y k hk' => ?_, by simp [AdSt.push]; omega, fun y k δs' hy => ?_,
          fun y a h hy => ?_⟩
        · simp only [AdSt.push] at hk'
          show Function.update w.2.1 (x, w.1.k) _ (y, k) = none
          rw [Function.update_of_ne (by intro h; rw [Prod.mk.injEq] at h; omega)]
          exact hw.fresh y k (by omega)
        · by_cases hyx : y = x
          · subst hyx
            simp only [AdSt.push, Function.update_self, Option.some.injEq, Prod.mk.injEq] at hy
            obtain ⟨rfl, rfl⟩ := hy
            exact ⟨Nat.lt_succ_self _, u, by simp⟩
          · simp only [AdSt.push, Function.update_of_ne hyx] at hy ⊢
            obtain ⟨hlt, u', hu'⟩ := hw.idx y k δs' hy
            refine ⟨Nat.lt_succ_of_lt hlt, u', ?_⟩
            rw [Function.update_of_ne (by intro h; exact hyx (congrArg Prod.fst h))]
            exact hu'
        · by_cases hyx : y = (x, w.1.k)
          · subst hyx
            simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hy ⊢
            obtain ⟨rfl, rfl⟩ := hy
            exact ⟨rfl, rfl⟩
          · simp only [Function.update_of_ne hyx] at hy ⊢
            exact hw.tg y a h hy
    · simp only [adReal_stop pre n g x δs w hk] at hz
      subst hz
      exact hw
  · simp only [adReal_iss] at hz
    subst hz
    exact ⟨hw.fresh, hw.len, hw.idx, hw.tg⟩

/-- The invariant of the recording run against the shift challenger. -/
structure InvB (v : AdSt X G × Ch AR X (List G) G) : Prop where
  len : v.2.rest.length + v.1.k = n
  idx : ∀ x k δs, v.1.idx x = some (k, δs) → k < v.1.k ∧ ∃ u, v.2.tg x = some (u, δs)
  tg : ∀ x a, v.2.tg x = some a → ∃ k, v.1.idx x = some (k, a.2)
  inj : ∀ x y k δs δs', v.1.idx x = some (k, δs) → v.1.idx y = some (k, δs') → x = y

theorem recCh_inv : QueryImpl.PreservesInv (recCh (S := S) (AR := AR) (X := X) pre) (InvB (G := G) n) := by
  intro q v hv z hz
  rcases q with d | ⟨x, δs⟩ | t
  · simp only [recCh_inl, roStep, Functor.map_map] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨r, -, rfl⟩ := hz
    exact ⟨hv.len, hv.idx, hv.tg, hv.inj⟩
  · cases hr : v.2.rest with
    | nil =>
      simp only [recCh_nil pre x δs v hr] at hz
      subst hz; exact hv
    | cons u r =>
      simp only [recCh_cons pre x δs v u r hr] at hz
      subst hz
      have hlen := hv.len
      rw [hr, List.length_cons] at hlen
      refine ⟨by simp [AdSt.push]; omega, fun y k δs' hy => ?_, fun y a hy => ?_,
        fun y y' k δs₁ δs₂ h1 h2 => ?_⟩
      · by_cases hyx : y = x
        · subst hyx
          simp only [AdSt.push, Function.update_self, Option.some.injEq, Prod.mk.injEq] at hy
          obtain ⟨rfl, rfl⟩ := hy
          exact ⟨Nat.lt_succ_self _, u, by simp⟩
        · simp only [AdSt.push, Function.update_of_ne hyx] at hy ⊢
          obtain ⟨hlt, u', hu'⟩ := hv.idx y k δs' hy
          exact ⟨Nat.lt_succ_of_lt hlt, u', hu'⟩
      · by_cases hyx : y = x
        · subst hyx
          simp only [Function.update_self, Option.some.injEq] at hy
          subst hy
          exact ⟨v.1.k, by simp [AdSt.push]⟩
        · simp only [AdSt.push, Function.update_of_ne hyx] at hy ⊢
          exact hv.tg y a hy
      · by_cases hyx : y = x <;> by_cases hy'x : y' = x
        · rw [hyx, hy'x]
        · subst hyx
          simp only [AdSt.push, Function.update_self, Option.some.injEq, Prod.mk.injEq,
            Function.update_of_ne hy'x] at h1 h2
          obtain ⟨rfl, rfl⟩ := h1
          exact absurd (hv.idx y' _ _ h2).1 (lt_irrefl _)
        · subst hy'x
          simp only [AdSt.push, Function.update_self, Option.some.injEq, Prod.mk.injEq,
            Function.update_of_ne hyx] at h1 h2
          obtain ⟨rfl, rfl⟩ := h2
          exact absurd (hv.idx y _ _ h1).1 (lt_irrefl _)
        · simp only [AdSt.push, Function.update_of_ne hyx, Function.update_of_ne hy'x] at h1 h2
          exact hv.inj y y' k δs₁ δs₂ h1 h2
  · simp only [recCh_iss] at hz
    subst hz
    exact ⟨hv.len, hv.idx, hv.tg, hv.inj⟩

/-- **Recording is transparent**: the recording run, without its record, is the shift game. -/
theorem recCh_eqd {α : Type} (oa : OracleComp (specB AR X (List G) G S) α)
    (v : AdSt X G × Ch AR X (List G) G) :
    (fun z => (z.1, z.2.2)) <$> (simulateQ (recCh pre) oa).run v =ᵈ
      (simulateQ (chImpl pre) oa).run v.2 := by
  refine simulateQ_proj_eqd_inv (recCh pre) (chImpl pre) Prod.snd (fun _ => True)
    (fun _ _ _ _ _ => trivial) (fun q w _ => ?_) oa v trivial
  rcases q with d | ⟨x, δs⟩ | t
  · rw [recCh_inl]; simp [chImpl, roStep, Functor.map_map]
  · cases hr : w.2.rest with
    | nil => rw [recCh_nil pre x δs w hr]; simp [chImpl, hr]
    | cons u r => rw [recCh_cons pre x δs w u r hr]; simp [chImpl, hr]
  · rw [recCh_iss]; simp [chImpl]

theorem adReal_eqd {α : Type} (oa : OracleComp (specB AR X (List G) G S) α) (w : RSt AR X G)
    (hw : InvA n g w) :
    (fun z => (z.1, projA z.2)) <$> (simulateQ (adReal pre n g) oa).run w =ᵈ
      (simulateQ (recCh pre) oa).run (projA w) :=
  simulateQ_proj_eqd_inv _ _ projA (InvA n g) (adReal_inv pre n g)
    (fun q w hw => by rw [adReal_step pre n g q w hw]) oa w hw

end GuessSim

/-! ### Counting the guesses -/

section Count

/-- **A guess vector agrees with a fixed one on `K` with probability `τ^{−|K|}`**; any event that
this implies is at least as likely. -/
theorem pr_guess_ge {n τ : ℕ} [NeZero τ] [SampleableType (Fin n → Fin τ)] (K : Finset (Fin n))
    (a : Fin n → Fin τ) (P : (Fin n → Fin τ) → Prop) (h : ∀ g, (∀ j ∈ K, g j = a j) → P g) :
    ((τ : ℝ≥0∞) ^ K.card)⁻¹ ≤ Pr{let g ← $ᵗ (Fin n → Fin τ)}[P g] := by
  classical
  refine le_trans (le_of_eq ?_) (prEvent_mono _ _ _ fun g hg => h g hg)
  rw [VoleMole.ROM.prEvent_uniformSample_eq_prU, VoleMole.Prob.prU_eq_card]
  have hset : (Finset.univ.filter fun g : Fin n → Fin τ => ∀ j ∈ K, g j = a j) =
      Fintype.piFinset fun j => if j ∈ K then {a j} else Finset.univ := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    refine ⟨fun hg j => ?_, fun hg j hj => ?_⟩
    · split_ifs with hj
      · simp [hg j hj]
      · simp
    · simpa [hj] using hg j
  have hcard : (Finset.univ.filter fun g : Fin n → Fin τ => ∀ j ∈ K, g j = a j).card =
      τ ^ (n - K.card) := by
    rw [hset, Fintype.card_piFinset]
    have : ∀ j, (if j ∈ K then ({a j} : Finset (Fin τ)) else Finset.univ).card =
        if j ∈ K then 1 else τ := fun j => by split_ifs <;> simp
    simp only [this, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
      Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ, Fintype.card_fin]
  have hk : K.card ≤ n := (Finset.card_le_univ K).trans (by simp)
  rw [hcard, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hτ0 : (τ : ℝ≥0∞) ≠ 0 := by simp [NeZero.ne τ]
  have hτt : (τ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top τ
  push_cast
  rw [show (τ : ℝ≥0∞) ^ n = τ ^ (n - K.card) * τ ^ K.card by
    rw [← pow_add, Nat.sub_add_cancel hk]]
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (pow_ne_zero _ hτ0))
    (Or.inl (ENNReal.pow_ne_top hτt)), mul_comm, ← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero _ hτ0) (ENNReal.pow_ne_top hτt), one_mul]

/-- **A lower bound through a bind**: if the continuation's event has probability at least `c`
wherever `W` holds on the support, the joint event has probability at least `c · Pr[W]`. -/
theorem le_prEvent_bind_of_support {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (W : α → Prop) (q : β → Prop) (c : ℝ≥0∞)
    (h : ∀ a ∈ support mx, W a → c ≤ Pr{let y ← f a}[q y]) :
    c * Pr{let a ← mx}[W a] ≤ Pr{let y ← mx >>= f}[q y] := by
  classical
  let : MeasurableSpace α := ⊤
  have hW : Pr{let a ← mx}[W a] ≤ Pr{let a ← mx}[W a ∧ a ∈ support mx] :=
    prEvent_mono_of_support mx _ _ fun a ha hw => ⟨hw, ha⟩
  refine (mul_le_mul' le_rfl hW).trans ?_
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_eq_evalDist_of_discrete,
    ← MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete]
  refine MeasureTheory.lintegral_mono fun a => ?_
  by_cases hw : W a ∧ a ∈ support mx
  · rw [Set.indicator_of_mem (show a ∈ {x | W x ∧ x ∈ support mx} from hw)]
    exact h a hw.2 hw.1
  · rw [Set.indicator_of_notMem (show a ∉ {x | W x ∧ x ∈ support mx} from hw)]
    exact zero_le

end Count

/-! ### Proposition 8(a) -/

section GuessMain

set_option linter.unusedSectionVars false

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {G S : Type} [AddCommGroup G] [SampleableType G] {PK SK : Type}

/-- **The guesses are right** for a run of the shift game (with its record): for every claim,
the guess for its label's latest request names a shift for which the claim is a preimage. -/
def GuessOK (rel : PK → S → G → Prop) (g : ℕ → ℕ) (pk : PK)
    (y : List (X × S) × AdSt X G × Ch AR X (List G) G) : Prop :=
  ∀ p ∈ y.1, ∃ k δs u δ, y.2.1.idx p.1 = some (k, δs) ∧ y.2.2.tg p.1 = some (u, δs) ∧
    δs[g k]? = some δ ∧ rel pk p.2 (u + δ)

/-- **A shift win with right guesses is a win of the adapter**: its claims are `ℓ + 1` preimages
of the programmed targets of distinct labels. -/
theorem win_of_guess (rel : PK → S → G → Prop) (n : ℕ) (g : ℕ → ℕ) (ℓ τ : ℕ) (pk : PK)
    (cl : List (X × S)) (w : RSt AR X G) (hw : InvA n g w)
    (hW : Wins ℓ (goodShift τ rel) pk cl (projA w).2) (hg : GuessOK rel g pk (cl, projA w)) :
    Forges ℓ (outA (cl, w.1)) w.2.2 ∧
      ∀ p ∈ (outA (cl, w.1)).1, goodPre rel pk p.2 (w.2.2.tg p.1) := by
  obtain ⟨hlen, hnd, hiq, -⟩ := hW
  refine ⟨⟨rfl, by simp [outA, hlen], ?_, hiq⟩, ?_⟩
  · refine List.Nodup.of_map Prod.fst ?_
    simpa [outA, List.map_map, Function.comp_def] using hnd
  · intro p' hp'
    simp only [outA, List.mem_map] at hp'
    obtain ⟨⟨x, s⟩, hp, rfl⟩ := hp'
    obtain ⟨k, δs, u, δ, hidx, htg, hδ, hrel⟩ := hg (x, s) hp
    have hidx' : w.1.idx x = some (k, δs) := hidx
    obtain ⟨-, u', hu'⟩ := hw.idx x k δs hidx'
    have htg' : ((w.1.idx x).bind fun kd => (w.2.1 (x, kd.1)).map fun a => (a.1, kd.2)) =
        some (u, δs) := htg
    rw [hidx'] at htg'
    simp only [Option.bind_some, hu', Option.map_some, Option.some.injEq, Prod.mk.injEq] at htg'
    obtain ⟨rfl, -⟩ := htg'
    have hgs : gShift g k δs = δ := by simp [gShift, hδ]
    have ht := hw.tg (x, k) u' (gShift g k δs) hu'
    refine ⟨u' + δ, δ, ?_, hrel⟩
    simp only [hidx', Option.map_some, Option.getD_some]
    rw [ht, hgs]

/-- **The count for one run**: in a winning run of the shift game, the guesses are right with
probability at least `τ^{−(ℓ+1)}` (the guess vector must hit one good index at the at most `ℓ + 1`
claimed requests). -/
theorem guess_count (rel : PK → S → G → Prop) {n τ : ℕ} [NeZero τ]
    [SampleableType (Fin n → Fin τ)] (ℓ : ℕ) (pk : PK)
    (y : List (X × S) × AdSt X G × Ch AR X (List G) G) (hinv : InvB (AR := AR) n y.2)
    (hW : Wins ℓ (goodShift τ rel) pk y.1 y.2.2) :
    ((τ : ℝ≥0∞) ^ (ℓ + 1))⁻¹ ≤ Pr{let g ← $ᵗ (Fin n → Fin τ)}[GuessOK rel (gfun g) pk y] := by
  classical
  obtain ⟨hlen, hnd, -, hgood⟩ := hW
  -- the claimed requests
  let K : Finset (Fin n) := (y.1.filterMap fun p => (y.2.1.idx p.1).bind fun kd =>
    if h : kd.1 < n then some (⟨kd.1, h⟩ : Fin n) else none).toFinset
  have hK : K.card ≤ ℓ + 1 :=
    (List.toFinset_card_le _).trans ((List.length_filterMap_le _ _).trans hlen.le)
  -- a good index for each claimed request
  let Good : Fin n → Fin τ → Prop := fun j i => ∀ p ∈ y.1, ∀ δs, y.2.1.idx p.1 = some ((j : ℕ), δs) →
    ∃ u δ, y.2.2.tg p.1 = some (u, δs) ∧ δs[(i : ℕ)]? = some δ ∧ rel pk p.2 (u + δ)
  have hex : ∀ j, ∃ i, Good j i := by
    intro j
    by_cases hj : ∃ p ∈ y.1, ∃ δs, y.2.1.idx p.1 = some ((j : ℕ), δs)
    · obtain ⟨p, hp, δs, hidx⟩ := hj
      obtain ⟨t, δs', htg, hl, δ, hδ, hrel⟩ := hgood p hp
      obtain ⟨-, u, hu⟩ := hinv.idx p.1 j δs hidx
      rw [hu, Option.some.injEq, Prod.mk.injEq] at htg
      obtain ⟨rfl, rfl⟩ := htg
      obtain ⟨i, hi, hiδ⟩ := List.getElem_of_mem hδ
      refine ⟨⟨i, lt_of_lt_of_le hi hl⟩, fun q hq δs' hq' => ?_⟩
      have hqp : q.1 = p.1 := hinv.inj q.1 p.1 j δs' δs hq' hidx
      have hqp' : q = p := (List.inj_on_of_nodup_map hnd) hq hp hqp
      subst hqp'
      rw [hidx, Option.some.injEq, Prod.mk.injEq] at hq'
      obtain ⟨-, rfl⟩ := hq'
      exact ⟨u, δ, hu, by simp [hi, hiδ], hrel⟩
    · exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne τ)⟩, fun p hp δs hidx => absurd ⟨p, hp, δs, hidx⟩ hj⟩
  let a : Fin n → Fin τ := fun j => Classical.choose (hex j)
  have hτ1 : (1 : ℝ≥0∞) ≤ τ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne τ)
  refine le_trans (ENNReal.inv_le_inv.2 (pow_le_pow_right₀ hτ1 hK)) (pr_guess_ge K a _ ?_)
  intro g hg p hp
  obtain ⟨t, δs, htg, -⟩ := hgood p hp
  obtain ⟨k, hidx⟩ := hinv.tg p.1 _ htg
  obtain ⟨hk, -⟩ := hinv.idx p.1 k _ hidx
  have hkn : k < n := lt_of_lt_of_le hk (by have := hinv.len; omega)
  have hjK : (⟨k, hkn⟩ : Fin n) ∈ K := by
    simp only [K, List.mem_toFinset, List.mem_filterMap]
    exact ⟨p, hp, by simp [hidx, hkn]⟩
  obtain ⟨u, δ, htg', hδ, hrel⟩ := Classical.choose_spec (hex ⟨k, hkn⟩) p hp δs hidx
  refine ⟨k, δs, u, δ, hidx, htg', ?_, hrel⟩
  simp only [gfun, hkn, dite_true]
  rw [hg _ hjK]
  exact hδ

variable (tr : Trapdoor PK SK G S)

/-- **Proposition 8(a)** (`uov-assumptions.md` §6): for `τ ≥ 1`,

    Adv^{ompr⊕τ}(B; n, ℓ) ≤ τ^{ℓ+1} · Adv^{ompr}(R; n, ℓ),

with `R = guessRed n τ B`, which guesses the shift of each of the `n` requests (uniformly in
`[τ]`), embeds its challenge at the guessed shift, and wins whenever all `ℓ + 1` claims used their
request's guessed shift. -/
theorem advOMPRShift_le_guess (τ : ℕ) [NeZero τ] (n ℓ : ℕ) [SampleableType (Fin n → Fin τ)]
    (B : PK → ProbComp (OracleComp (specB AR X (List G) G S) (List (X × S)))) :
    advOMPRShift tr τ n ℓ B ≤ (τ : ℝ≥0∞) ^ (ℓ + 1) * advOMPR tr n ℓ (guessRed n τ B) := by
  set c : ℝ≥0∞ := ((τ : ℝ≥0∞) ^ (ℓ + 1))⁻¹ with hc
  -- the shift game, with the record
  let mY : PK × SK → ProbComp (List (X × S) × AdSt X G × Ch AR X (List G) G) := fun kp => do
    let b ← B kp.1
    let L ← unifList G n
    (simulateQ (recCh (tr.D kp.2)) b).run (ad0, ch0 L)
  let M : ProbComp ((PK × SK) × List (X × S) × AdSt X G × Ch AR X (List G) G) := do
    let kp ← tr.keyGen
    let y ← mY kp
    pure (kp, y)
  have hS : advOMPRShift tr τ n ℓ B =
      Pr{let r ← M}[Wins ℓ (goodShift τ tr.IsPre) r.1.1 r.2.1 r.2.2.2] := by
    have hE : omExp tr.keyGen tr.D n B =ᵈ (fun r => (r.1.1, r.2.1, r.2.2.2)) <$> M := by
      simp only [omExp, M, mY, map_bind, map_pure, bind_assoc]
      refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun b =>
        EvalDistEq.bind_right _ fun L => ?_
      have := (recCh_eqd (tr.D kp.2) b (ad0, ch0 L)).symm.bind_left (fun r => pure (kp.1, r.1, r.2))
      simpa only [bind_map_left] using this
    unfold advOMPRShift
    rw [hE.prEvent_eq, prEvent_map]
  -- the guesses, drawn after the run
  let Ev : (PK × SK) × (Fin n → Fin τ) × (List (X × S) × AdSt X G × Ch AR X (List G) G) → Prop :=
    fun t => Wins ℓ (goodShift τ tr.IsPre) t.1.1 t.2.2.1 t.2.2.2.2 ∧
      GuessOK tr.IsPre (gfun t.2.1) t.1.1 t.2.2
  have hL : c * Pr{let r ← M}[Wins ℓ (goodShift τ tr.IsPre) r.1.1 r.2.1 r.2.2.2] ≤
      Pr{let t ← M >>= fun r => (do let g ← $ᵗ (Fin n → Fin τ); pure (r.1, g, r.2))}[Ev t] := by
    refine le_prEvent_bind_of_support _ _ _ _ c fun r hr hW => ?_
    simp only [M, mY, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨kp, -, y, ⟨b, -, L, hL, hy⟩, rfl⟩ := hr
    have hinv := simulateQ_run_preservesInv (recCh (tr.D kp.2)) (InvB (AR := AR) (G := G) n)
      (recCh_inv (tr.D kp.2) n) b (ad0, ch0 L)
      ⟨by simp [ch0, ad0, length_of_mem_unifList n L hL], by simp [ad0], by simp [ch0],
        by simp [ad0]⟩ y hy
    have hEq : Pr{let t ← (do let g ← $ᵗ (Fin n → Fin τ); pure (kp, g, y))}[Ev t] =
        Pr{let g ← $ᵗ (Fin n → Fin τ)}[GuessOK tr.IsPre (gfun g) kp.1 y] := by
      simp only [bind_pure_comp]
      rw [prEvent_map]
      simp [Ev, hW]
    refine le_of_le_of_eq ?_ hEq.symm
    exact guess_count tr.IsPre ℓ kp.1 y hinv hW
  -- swapping the guesses before the run
  let CB : ProbComp ((PK × SK) × (Fin n → Fin τ) × (List (X × S) × AdSt X G × Ch AR X (List G) G)) :=
    do
      let kp ← tr.keyGen
      let g ← $ᵗ (Fin n → Fin τ)
      let y ← mY kp
      pure (kp, g, y)
  have hSw : (M >>= fun r => (do let g ← $ᵗ (Fin n → Fin τ); pure (r.1, g, r.2))) =ᵈ CB := by
    simp only [M, CB, bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun kp => ?_
    exact eqd_swap (mY kp) ($ᵗ (Fin n → Fin τ)) fun y g => pure (kp, g, y)
  -- the adapter in the real game
  let CA : ProbComp ((PK × SK) × (Fin n → Fin τ) × (List (X × S) × RSt AR X G)) := do
    let kp ← tr.keyGen
    let g ← $ᵗ (Fin n → Fin τ)
    let b ← B kp.1
    let L ← unifList G n
    let w ← (simulateQ (adReal (tr.D kp.2) n (gfun g)) b).run (ad0, (fun _ => none, ch0 L))
    pure (kp, g, w)
  have hinitA : ∀ (g : ℕ → ℕ) (L : List G), L ∈ support (unifList G n) →
      InvA (AR := AR) (X := X) n g (ad0, (fun _ => none, ch0 L)) := fun g L hL =>
    ⟨fun _ _ _ => rfl, by simp [ch0, ad0, length_of_mem_unifList n L hL], by simp [ad0],
      by simp⟩
  have hA : CB =ᵈ (fun t => (t.1, t.2.1, (t.2.2.1, projA t.2.2.2))) <$> CA := by
    simp only [CB, CA, mY, map_bind, map_pure, bind_assoc]
    refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun g =>
      EvalDistEq.bind_right _ fun b => EvalDistEq.bind_congr_of_support _ fun L hL => ?_
    have := (adReal_eqd (tr.D kp.2) n (gfun g) b _ (hinitA (gfun g) L hL)).symm.bind_left
      (fun y => pure (kp, g, y))
    have hp : projA (AR := AR) (ad0, ((fun _ => none), ch0 L)) =
        ((ad0, ch0 L) : AdSt X G × Ch AR X (List G) G) := rfl
    rw [hp] at this
    simpa only [bind_map_left] using this
  -- the real game is a map of `CA`
  have hO : omuf tr.keyGen tr.D n addHint (guessAdv n τ B) =
      (fun t => (t.1.1, outA (t.2.2.1, t.2.2.2.1), t.2.2.2.2.1, t.2.2.2.2.2)) <$> CA := by
    simp only [omuf, CA, guessAdv, map_bind, map_pure, bind_assoc, pure_bind, simulateQ_map,
      StateT.run_map, collapseAd, Functor.map_map, bind_map_left]
  have hEA : Pr{let t ← CA}[Ev (t.1, t.2.1, (t.2.2.1, projA t.2.2.2))] ≤
      Pr{let r ← omuf tr.keyGen tr.D n addHint (guessAdv n τ B)}[
        Forges ℓ r.2.1 r.2.2.2 ∧ ∀ p ∈ r.2.1.1, goodPre tr.IsPre r.1 p.2 (r.2.2.2.tg p.1)] := by
    rw [hO, prEvent_map]
    refine prEvent_mono_of_support _ _ _ fun t ht hev => ?_
    simp only [CA, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ht
    obtain ⟨kp, -, g, -, b, -, L, hL, w, hw, rfl⟩ := ht
    have hinv := simulateQ_run_preservesInv (adReal (tr.D kp.2) n (gfun g)) (InvA n (gfun g))
      (adReal_inv (tr.D kp.2) n (gfun g)) b _ (hinitA (gfun g) L hL) w hw
    exact win_of_guess tr.IsPre n (gfun g) ℓ τ kp.1 w.1 w.2 hinv hev.1 hev.2
  have h1 := omuf_good_le tr.keyGen tr.D n ℓ addHint (guessAdv n τ B) (goodPre tr.IsPre)
  have hchain : c * advOMPRShift tr τ n ℓ B ≤ advOMPR tr n ℓ (guessRed n τ B) := by
    rw [hS]
    refine hL.trans (le_of_eq_of_le (hSw.prEvent_eq _) ?_)
    rw [hA.prEvent_eq, prEvent_map]
    exact hEA.trans h1
  have hτ0 : (τ : ℝ≥0∞) ^ (ℓ + 1) ≠ 0 := pow_ne_zero _ (by simp [NeZero.ne τ])
  have hτt : (τ : ℝ≥0∞) ^ (ℓ + 1) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top τ)
  calc advOMPRShift tr τ n ℓ B = (τ : ℝ≥0∞) ^ (ℓ + 1) * (c * advOMPRShift tr τ n ℓ B) := by
        rw [hc, ← mul_assoc, ENNReal.mul_inv_cancel hτ0 hτt, one_mul]
    _ ≤ (τ : ℝ≥0∞) ^ (ℓ + 1) * advOMPR tr n ℓ (guessRed n τ B) := mul_le_mul' le_rfl hchain

end GuessMain

end VoleMole.Assumptions.Shift
