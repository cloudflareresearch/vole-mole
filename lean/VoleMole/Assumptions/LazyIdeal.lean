import VoleMole.ROM.OneMore
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Lazy ideal objects and key guessing: generic simulation lemmas

Protocol-independent lemmas for reductions that program an ideal object with challenge values, or
embed a challenge key among `K` keys (`lean/docs/security/uov-assumptions.md` §5.4).

* **A lazy random function** `X → T` next to other oracles (`specRF AO X T`: the other oracles
  `AO`, then the function). `rfFresh implO` answers a fresh point with a fresh uniform value;
  `rfStream implO` answers it with the next value of a stream (and with `default`, without
  recording it, once the stream is used up). `rfStream_presample`: **with at most `k ≤ m` queries
  to the function, a uniform stream of `m` values is a lazy random function**: the two runs have
  the same joint distribution of output, other state and table. This is what lets a reduction
  hand out challenge targets as the function's fresh values.
* `isRF`: the function's queries. `rfStream_rest_le`: in such a run the stream loses at most `k`
  values.
* **Union bound over a stream**: `prEvent_unifList_exists_le`: the probability that some value of
  `m` uniform ones (after a draw `μ`) is bad is at most `m` times that of one uniform value.
* **`K`-key guessing**: `iidVec μ K` (`K` independent draws) and `iidVec_update` (**replacing
  coordinate `i` of the draws by a fresh draw keeps them iid**), the step that lets a one-key
  reduction generate the other `K − 1` keys itself and embed its own at a guessed position.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.ROM.OneMore
open scoped ENNReal

namespace VoleMole.Assumptions.Lazy

lemma eqd_bind_unused {α β : Type} (mx : ProbComp α) (my : ProbComp β) :
    (mx >>= fun _ => my) =ᵈ my := by
  let : MeasurableSpace β := ⊤
  exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const mx my)

/-! ## `K` independent draws, and embedding one at a position -/

section IID

variable {α : Type} (μ : ProbComp α)

/-- `n` independent draws from `μ`. -/
def iidVec : (n : ℕ) → ProbComp (Fin n → α)
  | 0 => pure Fin.elim0
  | n + 1 => do
    let a ← μ
    let v ← iidVec n
    pure (Fin.cons a v)

/-- **Replacing coordinate `i` of `n` independent draws by a fresh draw keeps them
independent**: the distribution a guessing reduction produces when it embeds its own key at `i`
among `n − 1` keys it generates itself. -/
theorem iidVec_update : ∀ {n : ℕ} (i : Fin n) {β : Type} (f : (Fin n → α) → ProbComp β),
    (do let a ← μ; let v ← iidVec μ n; f (Function.update v i a)) =ᵈ
      (do let v ← iidVec μ n; f v)
  | 0, i, _, _ => i.elim0
  | n + 1, i, β, f => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [iidVec, bind_assoc, pure_bind, Fin.update_cons_zero]
      refine EvalDistEq.bind_right _ fun a => ?_
      exact eqd_bind_unused _ _
    · simp only [iidVec, bind_assoc, pure_bind, ← Fin.cons_update]
      refine (eqd_swap _ _ _).trans (EvalDistEq.bind_right _ fun a => ?_)
      exact iidVec_update j fun v => f (Fin.cons a v)

end IID

/-! ## A lazy random function next to other oracles -/

section RF

variable {ιO : Type} (AO : ιO → Type) (X T : Type)

abbrev AnsRF : ιO ⊕ X → Type := Sum.elim AO fun _ => T

/-- The other oracles `AO`, and a function `X → T`. -/
abbrev specRF : OracleSpec (ιO ⊕ X) := OracleSpec.ofFn (AnsRF AO X T)

variable {AO X T}

/-- The function's queries. -/
def isRF : ιO ⊕ X → Bool
  | .inr _ => true
  | .inl _ => false

variable {σ : Type} [DecidableEq X] (implO : QueryImpl (OracleSpec.ofFn AO) (StateT σ ProbComp))

/-- **A lazy random function**: a fresh point gets a fresh uniform value, recorded in the table. -/
def rfFresh [SampleableType T] : QueryImpl (specRF AO X T) (StateT (σ × (X → Option T)) ProbComp)
  | .inl i => StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$> (implO i).run s.1
  | .inr x => StateT.mk fun s => match s.2 x with
      | some t => pure (t, s)
      | none => (fun t => (t, (s.1, Function.update s.2 x (some t)))) <$> ($ᵗ T)

/-- **The function fed from a stream**: a fresh point gets the stream's next value, recorded in
the table; once the stream is used up, `default`, not recorded. -/
def rfStream [Inhabited T] :
    QueryImpl (specRF AO X T) (StateT (σ × (X → Option T) × List T) ProbComp)
  | .inl i => StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$> (implO i).run s.1
  | .inr x => StateT.mk fun s => pure <| match s.2.1 x with
      | some t => (t, s)
      | none => match s.2.2 with
        | u :: r => (u, (s.1, Function.update s.2.1 x (some u), r))
        | [] => ((default : T), s)

/-- **Pre-sampling**: with at most `k ≤ m` queries to the function, feeding it from `m` uniform
values is the lazy random function (same joint distribution of output, other state and table). -/
theorem rfStream_presample [SampleableType T] [Inhabited T] {α : Type}
    (oa : OracleComp (specRF AO X T) α) :
    ∀ (k m : ℕ) (s : σ) (tab : X → Option T), IsQueryBoundP oa (fun q => isRF q = true) k →
      k ≤ m →
      (do let L ← unifList T m
          (fun z : α × σ × (X → Option T) × List T => (z.1, z.2.1, z.2.2.1)) <$>
            (simulateQ (rfStream implO) oa).run (s, tab, L)) =ᵈ
        (simulateQ (rfFresh implO) oa).run (s, tab) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro k m s tab _ _
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact eqd_bind_unused _ _
  | query_bind q cont ih =>
    intro k m s tab hb hkm
    rw [isQueryBoundP_query_bind_iff] at hb
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases q with i | x
    · have hb2 : ∀ u, IsQueryBoundP (cont u) (fun q => isRF q = true) k := fun u => by
        have h := hb.2 u; split_ifs at h with hh
        · simp [isRF] at hh
        · exact h
      simp only [rfStream, rfFresh, StateT.run_mk, bind_map_left]
      refine (eqd_swap _ _ _).trans (EvalDistEq.bind_right _ fun r => ?_)
      exact ih r.1 k m r.2 tab (hb2 r.1) hkm
    · have hk : 0 < k := hb.1.resolve_left (by simp [isRF])
      have hb2 : ∀ u, IsQueryBoundP (cont u) (fun q => isRF q = true) (k - 1) := fun u => by
        have h := hb.2 u; split_ifs at h with hh
        · exact h
        · simp [isRF] at hh
      cases htab : tab x with
      | some t =>
        simp only [rfStream, rfFresh, StateT.run_mk, htab, pure_bind]
        exact ih t (k - 1) m s tab (hb2 t) (by omega)
      | none =>
        obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp only [rfStream, rfFresh, StateT.run_mk, htab, pure_bind, unifList, bind_assoc,
          map_eq_bind_pure_comp, Function.comp_def]
        erw [bind_map_left]
        exact EvalDistEq.bind_right ($ᵗ T) fun u => by
          simpa only [map_eq_bind_pure_comp, Function.comp_def] using
            ih u (k - 1) m s (Function.update tab x (some u)) (hb2 u) (by omega)

/-- **The stream loses at most one value per query to the function**: with at most `k` queries,
at least `|L| − k` values remain. -/
theorem rfStream_rest_le [Inhabited T] {α : Type} (oa : OracleComp (specRF AO X T) α) (k : ℕ)
    (hb : IsQueryBoundP oa (fun q => isRF q = true) k) (s : σ) (tab : X → Option T) (L : List T) :
    ∀ z ∈ support ((simulateQ (rfStream implO) oa).run (s, tab, L)),
      L.length ≤ z.2.2.2.length + k := by
  intro z hz
  have := IsQueryBoundP.cost_le_of_mem_support_run_simulateQ
    (impl := rfStream implO) (fun st => L.length - st.2.2.length) (fun q hq st z hz => ?_)
    (fun q hq st z hz => ?_) hb (s, tab, L) z hz
  · simp at this; omega
  · rcases q with i | x
    · simp [isRF] at hq
    · simp only [rfStream, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      cases st.2.1 x with
      | some t => simp
      | none => cases h : st.2.2 with
        | nil => simp; omega
        | cons u r => simp; omega
  · rcases q with i | x
    · simp only [rfStream, StateT.run_mk, support_map, Set.mem_image] at hz
      obtain ⟨r, -, rfl⟩ := hz
      simp
    · simp [isRF] at hq

end RF

/-! ## A union bound over a stream of uniform values -/

section Union

variable {T : Type} [SampleableType T] {β : Type}

/-- **Some value of a uniform stream is bad** with probability at most the stream's length times
the probability that one uniform value is bad (after a common draw `μ`, e.g. the key). -/
theorem prEvent_unifList_exists_le (μ : ProbComp β) (bad : β → T → Prop) :
    ∀ m : ℕ, Pr{let b ← μ; let L ← unifList T m}[∃ u ∈ L, bad b u] ≤
      m * Pr{let b ← μ; let t ← $ᵗ T}[bad b t]
  | 0 => by simp [unifList]
  | m + 1 => by
    let mx : ProbComp (β × T × List T) := do
      let b ← μ; let t ← $ᵗ T; let L ← unifList T m; pure (b, t, L)
    have h1 : Pr{let b ← μ; let L ← unifList T (m + 1)}[∃ u ∈ L, bad b u] =
        Pr{let x ← mx}[bad x.1 x.2.1 ∨ ∃ u ∈ x.2.2, bad x.1 u] := by
      simp [mx, unifList]
    have h2 : Pr{let x ← mx}[bad x.1 x.2.1] = Pr{let b ← μ; let t ← $ᵗ T}[bad b t] := by
      simp only [mx, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine prEvent_bind_congr_of_support _ _ _ fun b _ => ?_
      refine prEvent_bind_congr_of_support _ _ _ fun t _ => ?_
      rw [OracleComp.prEvent_bind_const]
    have h3 : Pr{let x ← mx}[∃ u ∈ x.2.2, bad x.1 u] =
        Pr{let b ← μ; let L ← unifList T m}[∃ u ∈ L, bad b u] := by
      simp only [mx, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine prEvent_bind_congr_of_support _ _ _ fun b _ => ?_
      rw [OracleComp.prEvent_bind_const]
    rw [h1]
    refine (prEvent_or_le _ _ _).trans ?_
    rw [h2, h3]
    have := prEvent_unifList_exists_le μ bad m
    push_cast
    rw [add_mul, one_mul, add_comm]
    exact add_le_add_left this _

end Union

end VoleMole.Assumptions.Lazy
