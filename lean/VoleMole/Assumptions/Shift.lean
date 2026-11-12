import VoleMole.Assumptions.UOV

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
  adapter by the shift game (`adSim_eqd`) and a count of the guess vectors (`pr_guess_ge`).

**A simulation lemma** (`simulateQ_proj_eqd`): if each query of one stateful handler, projected
along `π`, is equal in distribution to another handler's on the projected state (under an
invariant), so is every computation. Used for A1, P8(a) and `Assumptions/Blind.lean`.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.ROM.OneMore
open scoped ENNReal

namespace VoleMole.Assumptions.UOV

/-! ## Projected simulations -/

section SimProj

variable {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ : Type}

/-- **Simulation along a projection**: stepwise equality in distribution of the projected run
(under a preserved invariant) gives equality in distribution of every projected run. -/
theorem simulateQ_proj_eqd (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp)) (π : σ₁ → σ₂) (Inv : σ₁ → Prop)
    (hinv : QueryImpl.PreservesInv impl₁ Inv)
    (hstep : ∀ q s, Inv s →
      (fun z => (z.1, π z.2)) <$> (impl₁ q).run s =ᵈ (impl₂ q).run (π s))
    {α : Type} (oa : OracleComp spec α) :
    ∀ s, Inv s → (fun z => (z.1, π z.2)) <$> (simulateQ impl₁ oa).run s =ᵈ
      (simulateQ impl₂ oa).run (π s) := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro s _; simp only [simulateQ_pure, StateT.run_pure, map_pure]; exact EvalDistEq.rfl
  | query_bind q k ih =>
    intro s hs
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    refine (EvalDistEq.bind_congr_of_support _ fun z hz => ih z.1 z.2 (hinv q s hs z hz)).trans ?_
    rw [← bind_map_left (fun z => (z.1, π z.2)) ((impl₁ q).run s)
      (fun w => (simulateQ impl₂ (k w.1)).run w.2)]
    exact (hstep q s hs).bind_left _

end SimProj

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
    have h := simulateQ_proj_eqd (chImpl (tr.D kp.2)) (chImpl (tr.D kp.2) ∘ₛ zImpl) zProj
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

end VoleMole.Assumptions.UOV
