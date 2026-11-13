import VoleMole.Assumptions.LazyIdeal

/-!
# A lazy random permutation with inverse queries, and the switch to a random function

The shared step of the permutation-model reductions to OMPR (`lean/docs/security/uov-assumptions.md`
§5.4, §5.8; `Assumptions/CTUFPerm.lean`, `Assumptions/FDHPerm.lean`). KP800 is a permutation
`π` of a finite block type `B` with forward and inverse access; `Com` and `Tag` read `π` on a
structured part of `B`.

* **The fresh value** `unifCompl used`: uniform on the blocks outside `used` (uniform on `B` if
  there is none). `unifCompl_eqd_resample'`: it is "draw uniformly, redraw from the complement on
  a hit"; `prEvent_mem_le`: a uniform block hits `used` with probability `≤ |used|/|B|`.
* **Identical until a flag** (`prEvent_and_not_flag_eq`, `prEvent_le_add_flag`; the generic step
  `prEvent_bind_agree`) and **a union bound over a run** (`prEvent_bad_le`: a monotone bad event
  of the state that each charged step enters with probability `≤ ε` has probability `≤ q·ε`).
  VCVio's total-variation versions are not in the built package set, so these are proved here.
* **The oracles** `specPm A B`: other oracles `A i`, and the permutation, `(true, b) ↦ π(b)`,
  `(false, c) ↦ π⁻¹(c)`. An other query `i` may read `π` at one point `pt i` (the challenger's
  evaluation of `Com`, `Tag`), and is then answered from that value (`implC`).
* **The table** `PTab B`: the records `(input, output, forward?)` in order.
* **Two handlers**, `pmImpl pt implC fresh`: `rpImpl` (`fresh := unifCompl`, **the lazy random
  permutation**: a fresh forward answer is uniform on the unused outputs, a fresh inverse answer
  uniform on the unused inputs) and `rfImpl` (`fresh := $ᵗ B`, a two-sided lazy random function).
* **The switch** (**`prEvent_rp_le_rf`**): for a computation with at most `q` queries that read
  the permutation (forward, inverse, or an other query with a point), started from a table of
  length `n₀`, every event of the run is at most as likely under the function plus
  `q·(n₀ + q)/|B|`. Proof: both handlers resample from one uniform draw and raise a flag on a hit
  (`freshRP`, `freshRF`); they agree off the flag (`pmImplF_agree`), and the function's flag costs
  `≤ (n₀ + q)/|B|` per charged step. This is the PRP/PRF switching term, with inverse queries.
* **An inverse answer in a set** (`prEvent_invHit_le`): under the function, a record made by an
  inverse query has its input in `S` with probability `≤ q_i·|S|/|B|` after `q_i` inverse
  queries. For `Com` and `Tag` (`S` the structured inputs) this is the inverse-query term.

The permutation is sampled lazily (`rpImpl`); that a lazily sampled permutation is distributed as
an eagerly drawn uniform one is the standard fact, not proved here.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace VoleMole.Assumptions.LazyPerm

/-! ## The fresh value of a lazy permutation -/

section Fresh

variable {B : Type} [Fintype B] [DecidableEq B] [SampleableType B]

/-- **A fresh value**: uniform on the blocks outside `used`; uniform on `B` if there is none. -/
noncomputable def unifCompl (used : List B) : ProbComp B :=
  if h : ∃ y, y ∉ used then
    letI : Nonempty {y // y ∉ used} := ⟨⟨h.choose, h.choose_spec⟩⟩
    letI := SampleableType.subtype B (· ∉ used)
    Subtype.val <$> ($ᵗ {y // y ∉ used})
  else $ᵗ B

/-- The point mass of a fresh value. -/
theorem prEvent_unifCompl_eq (used : List B) (h : ∃ y, y ∉ used) (a : B) :
    Pr{let y ← unifCompl used}[y = a] =
      if a ∈ used then 0 else ((Finset.univ.filter (· ∉ used)).card : ℝ≥0∞)⁻¹ := by
  classical
  let : Nonempty {y // y ∉ used} := ⟨⟨h.choose, h.choose_spec⟩⟩
  let := SampleableType.subtype B (· ∉ used)
  have hu : unifCompl used = Subtype.val <$> ($ᵗ {y // y ∉ used}) := by
    simp only [unifCompl, dite_eq_left h]
  rw [hu, prEvent_map, SampleableType.prEvent_uniformSample]
  have hc : Fintype.card {y // y ∉ used} = (Finset.univ.filter (· ∉ used)).card :=
    Fintype.card_subtype _
  split_ifs with ha
  · have : (Finset.univ.filter fun x : {y // y ∉ used} => x.val = a) = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro hx; exact x.2 (hx ▸ ha)
    rw [this]; simp
  · have : (Finset.univ.filter fun x : {y // y ∉ used} => x.val = a) = {⟨a, ha⟩} := by
      ext x; simp [Subtype.ext_iff]
    rw [this, Finset.card_singleton, hc]; simp

/-- **Resampling**: draw uniformly, and redraw from the complement on a hit. -/
noncomputable def resample (used : List B) : ProbComp B := do
  let y ← $ᵗ B
  if y ∈ used then unifCompl used else pure y

/-- **A fresh value is "draw uniformly, redraw on a hit"** (when there is a fresh value). -/
theorem unifCompl_eqd_resample (used : List B) (h : ∃ y, y ∉ used) :
    unifCompl used =ᵈ resample used := by
  classical
  refine evalDistEq_of_forall_prEvent_eq_output fun a => ?_
  set m := (Finset.univ.filter (· ∉ used)).card with hm
  set k := (Finset.univ.filter (· ∈ used)).card with hk
  have hn : Fintype.card B = m + k := by
    rw [hm, hk, ← Finset.card_univ, add_comm]
    exact (Finset.card_filter_add_card_filter_not (s := Finset.univ) (· ∈ used)).symm
  have hm0 : m ≠ 0 := by
    obtain ⟨y, hy⟩ := h
    rw [hm]; exact Finset.card_ne_zero.2 ⟨y, by simpa using hy⟩
  rw [resample, prEvent_bind_eq_tsum_of_countable, prEvent_unifCompl_eq used h a]
  have hpt : ∀ y : B, Pr{let z ← ($ᵗ B : ProbComp B)}[z = y] = ((m + k : ℕ) : ℝ≥0∞)⁻¹ := by
    intro y
    rw [SampleableType.prEvent_uniformSample, ← hn]
    have : (Finset.univ.filter fun z : B => z = y) = {y} := by ext; simp
    rw [this, Finset.card_singleton]; simp
  simp only [hpt]
  rw [ENNReal.tsum_mul_left, tsum_fintype]
  have hsplit : ∑ y : B, Pr{let z ← (if y ∈ used then unifCompl used else pure y)}[z = a] =
      ∑ y ∈ Finset.univ.filter (· ∈ used), Pr{let z ← unifCompl used}[z = a] +
        ∑ y ∈ Finset.univ.filter (· ∉ used), Pr{let z ← (pure y : ProbComp B)}[z = a] := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ used)]
    congr 1
    · exact Finset.sum_congr rfl fun y hy => by
        rw [ite_eq_left (Finset.mem_filter.1 hy).2]
    · exact Finset.sum_congr rfl fun y hy => by
        rw [ite_eq_right (Finset.mem_filter.1 hy).2]
  rw [hsplit, Finset.sum_const, ← hk, prEvent_unifCompl_eq used h a, nsmul_eq_mul]
  have hpure : ∀ y : B, Pr{let z ← (pure y : ProbComp B)}[z = a] = if y = a then 1 else 0 := by
    intro y; simp
  simp only [hpure]
  rw [Finset.sum_ite_eq']
  have hmk : ((m + k : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : m + k ≠ 0)
  have hmk' : ((m + k : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hm' : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm0
  by_cases ha : a ∈ used
  · have : a ∉ Finset.univ.filter (· ∉ used) := by simp [ha]
    simp [ha, this]
  · have : a ∈ Finset.univ.filter (· ∉ used) := by simp [ha]
    simp only [ha, ite_false, this, ite_true]
    rw [← hm]
    have e1 : (k : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹ + 1 = ((m + k : ℕ) : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹ := by
      rw [Nat.cast_add, add_mul, ENNReal.mul_inv_cancel hm' (ENNReal.natCast_ne_top _), add_comm]
    rw [e1, ← mul_assoc, ENNReal.inv_mul_cancel hmk hmk', one_mul]

/-- **A uniform block hits `used`** with probability at most `|used|/|B|`. -/
theorem prEvent_mem_le (used : List B) :
    Pr{let y ← ($ᵗ B : ProbComp B)}[y ∈ used] ≤ used.length / Fintype.card B := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  gcongr
  exact (Finset.card_le_card fun y hy => by simpa using hy).trans (List.toFinset_card_le used)

/-- Without a fresh value, resampling is a uniform block too. -/
theorem unifCompl_eqd_resample' (used : List B) : unifCompl used =ᵈ resample used := by
  by_cases h : ∃ y, y ∉ used
  · exact unifCompl_eqd_resample used h
  · have h' : ∀ y, y ∈ used := by push Not at h; exact h
    have hu : unifCompl used = $ᵗ B := by simp only [unifCompl, dite_eq_right h]
    simp only [resample, h', ite_true, hu]
    exact (LazyIdeal.eqd_bind_unused _ _).symm

end Fresh

/-! ## Identical until a flag, and a union bound over a run -/

section Flag

variable {ι : Type} {spec : OracleSpec ι} {τ : Type}

/-- **Two computations that agree off a flag, followed by continuations that agree off the flag
and see no event once it is set, agree on the event.** -/
theorem prEvent_bind_agree {α β : Type} (mx₁ mx₂ : ProbComp α) (fl : α → Prop)
    (h : ∀ P : α → Prop, Pr{let a ← mx₁}[P a ∧ ¬fl a] = Pr{let a ← mx₂}[P a ∧ ¬fl a])
    (f₁ f₂ : α → ProbComp β) (R : β → Prop)
    (h₁ : ∀ a, fl a → Pr{let b ← f₁ a}[R b] = 0) (h₂ : ∀ a, fl a → Pr{let b ← f₂ a}[R b] = 0)
    (hf : ∀ a, ¬fl a → Pr{let b ← f₁ a}[R b] = Pr{let b ← f₂ a}[R b]) :
    Pr{let b ← mx₁ >>= f₁}[R b] = Pr{let b ← mx₂ >>= f₂}[R b] := by
  classical
  let : MeasurableSpace α := ⊤
  have e1 : (fun a => Pr{let b ← f₁ a}[R b]) =
      ({a | ¬fl a} : Set α).indicator fun a => Pr{let b ← f₂ a}[R b] := funext fun a => by
    by_cases ha : fl a
    · rw [h₁ a ha, Set.indicator_of_notMem (by simpa using ha)]
    · rw [hf a ha, Set.indicator_of_mem (by simpa using ha)]
  have e2 : (fun a => Pr{let b ← f₂ a}[R b]) =
      ({a | ¬fl a} : Set α).indicator fun a => Pr{let b ← f₂ a}[R b] := funext fun a => by
    by_cases ha : fl a
    · rw [h₂ a ha, Set.indicator_of_notMem (by simpa using ha)]
    · rw [Set.indicator_of_mem (by simpa using ha)]
  have hres : 𝒟[mx₁].restrict {a | ¬fl a} = 𝒟[mx₂].restrict {a | ¬fl a} := by
    ext A _
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.of_discrete,
      MeasureTheory.Measure.restrict_apply MeasurableSet.of_discrete]
    have := h (· ∈ A)
    rwa [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete] at this
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  conv_lhs => rw [e1]
  conv_rhs => rw [e2]
  rw [MeasureTheory.lintegral_indicator MeasurableSet.of_discrete,
    MeasureTheory.lintegral_indicator MeasurableSet.of_discrete, hres]

/-- **Once set, the flag stays set** on the support of a run whose handler keeps it. -/
theorem flag_mono (H : QueryImpl spec (StateT (τ × Bool) ProbComp))
    (hm : ∀ t s, ∀ z ∈ support ((H t).run (s, true)), z.2.2 = true) {α : Type}
    (oa : OracleComp spec α) : ∀ s, ∀ z ∈ support ((simulateQ H oa).run (s, true)), z.2.2 = true := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro s z hz; simp only [simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz; subst hz; rfl
  | query_bind t k ih =>
    intro s z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hw2 := hm t s w hw
    obtain ⟨u, s', b⟩ := w
    simp only at hw2; subst hw2
    exact ih u s' z hz

/-- **Identical until the flag** (the fundamental lemma): two handlers that keep the flag set and
agree on every unflagged step from an unflagged state give every event the same probability
with the flag unset. -/
theorem prEvent_and_not_flag_eq (H₁ H₂ : QueryImpl spec (StateT (τ × Bool) ProbComp))
    (hm₁ : ∀ t s, ∀ z ∈ support ((H₁ t).run (s, true)), z.2.2 = true)
    (hm₂ : ∀ t s, ∀ z ∈ support ((H₂ t).run (s, true)), z.2.2 = true)
    (hag : ∀ t s (P : spec.Range t × τ × Bool → Prop),
      Pr{let z ← (H₁ t).run (s, false)}[P z ∧ ¬z.2.2 = true] =
        Pr{let z ← (H₂ t).run (s, false)}[P z ∧ ¬z.2.2 = true])
    {α : Type} (oa : OracleComp spec α) :
    ∀ s (E : α × τ → Prop), Pr{let z ← (simulateQ H₁ oa).run (s, false)}[E (z.1, z.2.1) ∧ ¬z.2.2 = true] =
      Pr{let z ← (simulateQ H₂ oa).run (s, false)}[E (z.1, z.2.1) ∧ ¬z.2.2 = true] := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro s E; rfl
  | query_bind t k ih =>
    intro s E
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hz : ∀ (H : QueryImpl spec (StateT (τ × Bool) ProbComp)),
        (∀ t s, ∀ z ∈ support ((H t).run (s, true)), z.2.2 = true) →
        ∀ w : spec.Range t × τ × Bool, w.2.2 = true →
          Pr{let z ← (simulateQ H (k w.1)).run w.2}[E (z.1, z.2.1) ∧ ¬z.2.2 = true] = 0 := by
      intro H hm w hw
      obtain ⟨u, s', b⟩ := w
      simp only at hw; subst hw
      exact prEvent_eq_zero_of_forall_mem_support _ _ fun z hz' hzz => hzz.2 (flag_mono H hm _ s' z hz')
    refine prEvent_bind_agree _ _ (fun w => w.2.2 = true) (hag t s) _ _ _ (hz H₁ hm₁) (hz H₂ hm₂)
      fun w hw => ?_
    obtain ⟨u, s', b⟩ := w
    simp only [Bool.not_eq_true] at hw; subst hw
    exact ih u s' E

/-- **Up to the flag**: an event under `H₁` is at most the event under `H₂` plus the probability
that the flag is set under `H₂`. -/
theorem prEvent_le_add_flag (H₁ H₂ : QueryImpl spec (StateT (τ × Bool) ProbComp))
    (hm₁ : ∀ t s, ∀ z ∈ support ((H₁ t).run (s, true)), z.2.2 = true)
    (hm₂ : ∀ t s, ∀ z ∈ support ((H₂ t).run (s, true)), z.2.2 = true)
    (hag : ∀ t s (P : spec.Range t × τ × Bool → Prop),
      Pr{let z ← (H₁ t).run (s, false)}[P z ∧ ¬z.2.2 = true] =
        Pr{let z ← (H₂ t).run (s, false)}[P z ∧ ¬z.2.2 = true])
    {α : Type} (oa : OracleComp spec α) (s : τ) (E : α × τ → Prop) :
    Pr{let z ← (simulateQ H₁ oa).run (s, false)}[E (z.1, z.2.1)] ≤
      Pr{let z ← (simulateQ H₂ oa).run (s, false)}[E (z.1, z.2.1)] +
        Pr{let z ← (simulateQ H₂ oa).run (s, false)}[z.2.2 = true] := by
  have hE := prEvent_and_not_flag_eq H₁ H₂ hm₁ hm₂ hag oa s E
  have hT := prEvent_and_not_flag_eq H₁ H₂ hm₁ hm₂ hag oa s fun _ => True
  simp only [true_and] at hT
  have hf : Pr{let z ← (simulateQ H₁ oa).run (s, false)}[z.2.2 = true] =
      Pr{let z ← (simulateQ H₂ oa).run (s, false)}[z.2.2 = true] := by
    have a1 := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ H₁ oa).run (s, false))
      fun z => z.2.2 = true
    have a2 := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ H₂ oa).run (s, false))
      fun z => z.2.2 = true
    rw [OracleComp.prEvent_true_eq_one] at a1 a2
    have hne : Pr{let z ← (simulateQ H₂ oa).run (s, false)}[¬z.2.2 = true] ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)
    rw [hT] at a1
    exact (ENNReal.add_left_inj hne).1 (a1.trans a2.symm)
  calc _ ≤ Pr{let z ← (simulateQ H₁ oa).run (s, false)}[z.2.2 = true] +
        Pr{let z ← (simulateQ H₁ oa).run (s, false)}[E (z.1, z.2.1) ∧ ¬z.2.2 = true] :=
        prEvent_le_prEvent_add_prEvent_and_not _ _ _
    _ = Pr{let z ← (simulateQ H₂ oa).run (s, false)}[E (z.1, z.2.1) ∧ ¬z.2.2 = true] +
        Pr{let z ← (simulateQ H₂ oa).run (s, false)}[z.2.2 = true] := by rw [hf, hE, add_comm]
    _ ≤ _ := add_le_add (prEvent_mono _ _ _ fun _ hh => hh.1) le_rfl

/-- **A union bound over a run**: a monotone bad event of the state that a charged step (of kind
`p`) enters with probability at most `ε` and an uncharged step never enters, on the states of an
invariant `Good k` (`k` the remaining budget), has probability at most `k·ε` after at most `k`
charged queries. -/
theorem prEvent_bad_le (H : QueryImpl spec (StateT τ ProbComp)) (bad : τ → Prop)
    (p : ι → Prop) [DecidablePred p] (Good : ℕ → τ → Prop) (ε : ℝ≥0∞)
    (hstep : ∀ t s k, Good k s → ¬bad s → (p t → 0 < k) →
      Pr{let z ← (H t).run s}[bad z.2] ≤ if p t then ε else 0)
    (hgood : ∀ t s k, Good k s → ¬bad s → (p t → 0 < k) →
      ∀ z ∈ support ((H t).run s), ¬bad z.2 → Good (if p t then k - 1 else k) z.2)
    {α : Type} (oa : OracleComp spec α) :
    ∀ k s, IsQueryBoundP oa p k → Good k s → ¬bad s →
      Pr{let z ← (simulateQ H oa).run s}[bad z.2] ≤ k * ε := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro k s _ _ hb; simp [hb]
  | query_bind t cont ih =>
    intro k s hq hG hb
    rw [isQueryBoundP_query_bind_iff] at hq
    have hk : p t → 0 < k := fun hp => hq.1.resolve_left (not_not.2 hp)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun z => bad z.2) _
      (ε := (if p t then k - 1 else k : ℕ) * ε) fun z hz hzb =>
        ih z.1 _ z.2 (hq.2 z.1) (hgood t s k hG hb hk z hz hzb) hzb).trans ?_
    refine (add_le_add (hstep t s k hG hb hk) le_rfl).trans ?_
    split_ifs with hp
    · have := hk hp
      rw [← one_add_mul, show (1 : ℝ≥0∞) + ((k - 1 : ℕ) : ℝ≥0∞) = k by
        rw [add_comm]; exact_mod_cast Nat.sub_add_cancel this]
    · simp

/-- **A bound after a common draw, with an additive constant**, on the draw's support. -/
theorem prEvent_bind_le_add_const {α : Type} (mx : ProbComp α) (f g : α → ProbComp Prop)
    (c : ℝ≥0∞) (h : ∀ a ∈ support mx, prEvent (f a) ≤ prEvent (g a) + c) :
    prEvent (mx >>= f) ≤ prEvent (mx >>= g) + c := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  calc ∫⁻ a, prEvent (f a) ∂𝒟[mx] ≤ ∫⁻ a, (prEvent (g a) + c) ∂𝒟[mx] :=
        MeasureTheory.lintegral_mono_ae ((evalDist.ae_of_forall_mem_support mx (· ∈ support mx)
          MeasurableSet.of_discrete fun _ ha => ha).mono fun a ha => h a ha)
    _ = ∫⁻ a, prEvent (g a) ∂𝒟[mx] + c * 𝒟[mx] Set.univ := by
        rw [MeasureTheory.lintegral_add_right _ measurable_const, MeasureTheory.lintegral_const]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' (evalDist_apply_univ_le_one mx))

/-- A query bound for a kind bounds every narrower kind. -/
theorem isQueryBoundP_of_imp {ι : Type} {spec : OracleSpec ι} {α : Type} (p p' : ι → Prop)
    [DecidablePred p] [DecidablePred p'] (hpp : ∀ t, p' t → p t) (oa : OracleComp spec α) :
    ∀ n, IsQueryBoundP oa p n → IsQueryBoundP oa p' n := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro n _; trivial
  | query_bind t k ih =>
    intro n hn
    rw [isQueryBoundP_query_bind_iff] at hn ⊢
    refine ⟨hn.1.imp (fun h h' => h (hpp t h')) id, fun u => ?_⟩
    have := ih u _ (hn.2 u)
    refine this.mono ?_
    by_cases h1 : p t <;> by_cases h2 : p' t <;> simp only [h1, h2, ite_true, ite_false] <;>
      first | omega | exact absurd (hpp t h2) h1

end Flag

/-! ## The permutation oracle, lazily -/

section Perm

variable {ι : Type} (A : ι → Type) (B : Type)

/-- The answers: the other oracles `A i`, and a block for a permutation query. -/
abbrev AnsPm : ι ⊕ (Bool × B) → Type := Sum.elim A fun _ => B

/-- **The oracles**: other oracles, and the permutation `(true, b) ↦ π(b)`, `(false, c) ↦ π⁻¹(c)`. -/
abbrev specPm : OracleSpec (ι ⊕ (Bool × B)) := OracleSpec.ofFn (AnsPm A B)

/-- **The permutation's table**: records `(input, output, determined by a forward query?)`. -/
abbrev PTab := List (B × B × Bool)

variable {A B}

/-- **The queries that read the permutation**: a permutation query, or an other query with a
point. -/
def isPm (pt : ι → Option B) : ι ⊕ (Bool × B) → Bool
  | .inl i => (pt i).isSome
  | .inr _ => true

variable [DecidableEq B]

/-- The recorded output at an input. -/
def fwdFind (L : PTab B) (b : B) : Option B := (L.find? fun e => e.1 = b).map fun e => e.2.1

/-- The recorded input at an output. -/
def invFind (L : PTab B) (c : B) : Option B := (L.find? fun e => e.2.1 = c).map fun e => e.1

/-- **A forward step**: the recorded output, or a fresh one (recorded). -/
def fwdS (fresh : List B → ProbComp B) (b : B) (L : PTab B) : ProbComp (B × PTab B) :=
  match fwdFind L b with
  | some y => pure (y, L)
  | none => (fun y => (y, L ++ [(b, y, true)])) <$> fresh (L.map fun e => e.2.1)

/-- **An inverse step**: the recorded input, or a fresh one (recorded). -/
def invS (fresh : List B → ProbComp B) (c : B) (L : PTab B) : ProbComp (B × PTab B) :=
  match invFind L c with
  | some x => pure (x, L)
  | none => (fun x => (x, L ++ [(x, c, false)])) <$> fresh (L.map fun e => e.1)

variable {σ : Type} (pt : ι → Option B) (implC : (i : ι) → Option B → StateT σ ProbComp (A i))

/-- **The handler** with the fresh values `fresh used`: an other query `i` reads the permutation
forward at `pt i` (if any) and is answered by `implC i` from that value; permutation queries are
forward and inverse steps. -/
def pmImpl (fresh : List B → ProbComp B) : QueryImpl (specPm A B) (StateT (PTab B × σ) ProbComp)
  | .inl i => StateT.mk fun s => match pt i with
    | none => (fun u => (u.1, (s.1, u.2))) <$> (implC i none).run s.2
    | some b => fwdS fresh b s.1 >>= fun r =>
        (fun u => (u.1, (r.2, u.2))) <$> (implC i (some r.1)).run s.2
  | .inr (true, b) => StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$> fwdS fresh b s.1
  | .inr (false, c) => StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$> invS fresh c s.1

/-- **The lazy random permutation**: fresh values uniform on the unused outputs (forward) or the
unused inputs (inverse). -/
noncomputable def rpImpl [Fintype B] [SampleableType B] :
    QueryImpl (specPm A B) (StateT (PTab B × σ) ProbComp) :=
  pmImpl pt implC unifCompl

/-- **The two-sided lazy random function**: fresh values uniform. -/
def rfImpl [SampleableType B] : QueryImpl (specPm A B) (StateT (PTab B × σ) ProbComp) :=
  pmImpl pt implC fun _ => $ᵗ B

/-! ### The flagged handlers of the proof -/

/-- A forward step with a flag from the fresh value. -/
def fwdF (fresh : List B → ProbComp (B × Bool)) (b : B) (L : PTab B) :
    ProbComp ((B × Bool) × PTab B) :=
  match fwdFind L b with
  | some y => pure ((y, false), L)
  | none => (fun y => (y, L ++ [(b, y.1, true)])) <$> fresh (L.map fun e => e.2.1)

/-- An inverse step with a flag from the fresh value. -/
def invF (fresh : List B → ProbComp (B × Bool)) (c : B) (L : PTab B) :
    ProbComp ((B × Bool) × PTab B) :=
  match invFind L c with
  | some x => pure ((x, false), L)
  | none => (fun x => (x, L ++ [(x.1, c, false)])) <$> fresh (L.map fun e => e.1)

/-- The handler with flagged fresh values: the flag records a hit. -/
def pmImplF (fresh : List B → ProbComp (B × Bool)) :
    QueryImpl (specPm A B) (StateT ((PTab B × σ) × Bool) ProbComp)
  | .inl i => StateT.mk fun s => match pt i with
    | none => (fun u => (u.1, ((s.1.1, u.2), s.2))) <$> (implC i none).run s.1.2
    | some b => fwdF fresh b s.1.1 >>= fun r =>
        (fun u => (u.1, ((r.2, u.2), s.2 || r.1.2))) <$> (implC i (some r.1.1)).run s.1.2
  | .inr (true, b) => StateT.mk fun s =>
      (fun r => (r.1.1, ((r.2, s.1.2), s.2 || r.1.2))) <$> fwdF fresh b s.1.1
  | .inr (false, c) => StateT.mk fun s =>
      (fun r => (r.1.1, ((r.2, s.1.2), s.2 || r.1.2))) <$> invF fresh c s.1.1

variable [SampleableType B]

/-- The permutation's fresh value, flagged when the first uniform draw hit `used`. -/
noncomputable def freshRP [Fintype B] (used : List B) : ProbComp (B × Bool) := do
  let y ← $ᵗ B
  if y ∈ used then ((fun y' => (y', true)) <$> unifCompl used) else pure (y, false)

/-- The function's fresh value, flagged when it hit `used`. -/
def freshRF (used : List B) : ProbComp (B × Bool) := (fun y => (y, decide (y ∈ used))) <$> ($ᵗ B)

omit [SampleableType B] in
theorem fwdF_val (fresh : List B → ProbComp (B × Bool)) (b : B) (L : PTab B) :
    (fun r => (r.1.1, r.2)) <$> fwdF fresh b L = fwdS (fun u => Prod.fst <$> fresh u) b L := by
  unfold fwdF fwdS
  cases fwdFind L b <;> simp [Functor.map_map]

omit [SampleableType B] in
theorem invF_val (fresh : List B → ProbComp (B × Bool)) (c : B) (L : PTab B) :
    (fun r => (r.1.1, r.2)) <$> invF fresh c L = invS (fun u => Prod.fst <$> fresh u) c L := by
  unfold invF invS
  cases invFind L c <;> simp [Functor.map_map]

omit [SampleableType B] in
theorem fwdS_congr {f g : List B → ProbComp B} (h : ∀ u, f u =ᵈ g u) (b : B) (L : PTab B) :
    fwdS f b L =ᵈ fwdS g b L := by
  unfold fwdS
  cases fwdFind L b
  · exact (h _).map _
  · exact EvalDistEq.rfl

omit [SampleableType B] in
theorem invS_congr {f g : List B → ProbComp B} (h : ∀ u, f u =ᵈ g u) (c : B) (L : PTab B) :
    invS f c L =ᵈ invS g c L := by
  unfold invS
  cases invFind L c
  · exact (h _).map _
  · exact EvalDistEq.rfl

omit [SampleableType B] in
/-- **The flagged handler, without the flag, is the handler** with the fresh values' first
components. -/
theorem pmImplF_proj (fresh : List B → ProbComp (B × Bool)) (g : List B → ProbComp B)
    (hg : ∀ u, Prod.fst <$> fresh u =ᵈ g u) (t : ι ⊕ (Bool × B)) (s : (PTab B × σ) × Bool) :
    (fun z => (z.1, z.2.1)) <$> ((pmImplF pt implC fresh) t).run s =ᵈ
      ((pmImpl pt implC g) t).run s.1 := by
  rcases t with i | ⟨_ | _, b⟩
  · simp only [pmImplF, pmImpl, StateT.run_mk]
    cases hp : pt i with
    | none => simp only [Functor.map_map]; exact EvalDistEq.rfl
    | some b =>
      simp only [map_bind, Functor.map_map]
      have h1 : (fun r => (r.1.1, r.2)) <$> fwdF fresh b s.1.1 =ᵈ fwdS g b s.1.1 := by
        rw [fwdF_val]; exact fwdS_congr hg _ _
      have h2 := h1.bind_left fun r : B × PTab B =>
        (fun u => (u.1, (r.2, u.2))) <$> (implC i (some r.1)).run s.1.2
      simp only [bind_map_left] at h2
      exact h2
  · simp only [pmImplF, pmImpl, StateT.run_mk, Functor.map_map]
    have h1 := invS_congr hg b s.1.1
    rw [← invF_val] at h1
    have h2 := h1.map (fun r => (r.1, (r.2, s.1.2)))
    simp only [Functor.map_map] at h2
    exact h2
  · simp only [pmImplF, pmImpl, StateT.run_mk, Functor.map_map]
    have h1 := fwdS_congr hg b s.1.1
    rw [← fwdF_val] at h1
    have h2 := h1.map (fun r => (r.1, (r.2, s.1.2)))
    simp only [Functor.map_map] at h2
    exact h2

omit [SampleableType B] in
/-- **The flag stays set.** -/
theorem pmImplF_mono (fresh : List B → ProbComp (B × Bool)) (t : ι ⊕ (Bool × B))
    (s : PTab B × σ) : ∀ z ∈ support (((pmImplF pt implC fresh) t).run (s, true)), z.2.2 = true := by
  intro z hz
  rcases t with i | ⟨_ | _, b⟩
  · simp only [pmImplF, StateT.run_mk] at hz
    cases hp : pt i with
    | none =>
      rw [hp] at hz; erw [support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz; rfl
    | some b =>
      rw [hp] at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨r, -, hz⟩ := hz
      erw [support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz; simp
  · simp only [pmImplF, StateT.run_mk] at hz; erw [support_map] at hz
    obtain ⟨r, -, rfl⟩ := hz; simp
  · simp only [pmImplF, StateT.run_mk] at hz; erw [support_map] at hz
    obtain ⟨r, -, rfl⟩ := hz; simp

variable [Fintype B]

theorem freshRP_fst (used : List B) : Prod.fst <$> freshRP used =ᵈ unifCompl used := by
  refine EvalDistEq.trans ?_ (unifCompl_eqd_resample' used).symm
  simp only [freshRP, resample, map_bind]
  refine EvalDistEq.bind_right _ fun y => ?_
  split_ifs <;> simp only [Functor.map_map, map_pure, id_map'] <;> exact EvalDistEq.rfl

omit [Fintype B] in
theorem freshRF_fst (used : List B) : Prod.fst <$> freshRF used =ᵈ ($ᵗ B : ProbComp B) := by
  simp only [freshRF, Functor.map_map, id_map']; exact EvalDistEq.rfl

/-- **The two fresh values agree off the flag.** -/
theorem fresh_agree (used : List B) (P : B × Bool → Prop) :
    Pr{let y ← freshRP used}[P y ∧ ¬y.2 = true] = Pr{let y ← freshRF used}[P y ∧ ¬y.2 = true] := by
  classical
  have e : freshRF used = ($ᵗ B : ProbComp B) >>= fun y => pure (y, decide (y ∈ used)) := by
    rw [freshRF, map_eq_bind_pure_comp]; rfl
  rw [e, freshRP]
  refine prEvent_bind_congr ($ᵗ B : ProbComp B) _ _ _ _ fun y => ?_
  by_cases hy : y ∈ used
  · simp [hy]
  · simp [hy]

/-- **The forward and inverse steps agree off the flag.** -/
theorem fwdF_agree (b : B) (L : PTab B) (P : (B × Bool) × PTab B → Prop) :
    Pr{let r ← fwdF freshRP b L}[P r ∧ ¬r.1.2 = true] =
      Pr{let r ← fwdF freshRF b L}[P r ∧ ¬r.1.2 = true] := by
  unfold fwdF
  cases fwdFind L b with
  | some y => rfl
  | none =>
    simp only [prEvent_map]
    exact fresh_agree _ fun y => P (y, L ++ [(b, y.1, true)])

theorem invF_agree (c : B) (L : PTab B) (P : (B × Bool) × PTab B → Prop) :
    Pr{let r ← invF freshRP c L}[P r ∧ ¬r.1.2 = true] =
      Pr{let r ← invF freshRF c L}[P r ∧ ¬r.1.2 = true] := by
  unfold invF
  cases invFind L c with
  | some y => rfl
  | none =>
    simp only [prEvent_map]
    exact fresh_agree _ fun x => P (x, L ++ [(x.1, c, false)])

/-- **The permutation and the function agree on every unflagged step.** -/
theorem pmImplF_agree (t : ι ⊕ (Bool × B)) (s : PTab B × σ)
    (P : (specPm A B).Range t × (PTab B × σ) × Bool → Prop) :
    Pr{let z ← ((pmImplF pt implC freshRP) t).run (s, false)}[P z ∧ ¬z.2.2 = true] =
      Pr{let z ← ((pmImplF pt implC freshRF) t).run (s, false)}[P z ∧ ¬z.2.2 = true] := by
  rcases t with i | ⟨_ | _, b⟩
  · simp only [pmImplF, StateT.run_mk]
    cases hp : pt i with
    | none => rfl
    | some b =>
      refine prEvent_bind_agree _ _ (fun r => r.1.2 = true) (fwdF_agree b s.1) _ _ _
        (fun r hr => ?_) (fun r hr => ?_) fun _ _ => rfl
      all_goals
        rw [prEvent_map]
        exact prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => hu.2 (by simp [hr])
  · simp only [pmImplF, StateT.run_mk, prEvent_map, Bool.false_or]
    exact invF_agree b s.1 _
  · simp only [pmImplF, StateT.run_mk, prEvent_map, Bool.false_or]
    exact fwdF_agree b s.1 _

/-- **The function's flag**: a charged step from a table of length `n` sets it with probability at
most `n/|B|`, and grows the table by at most one; an uncharged step does neither. -/
theorem pmImplF_rf_flag (t : ι ⊕ (Bool × B)) (s : PTab B × σ) :
    Pr{let z ← ((pmImplF pt implC freshRF) t).run (s, false)}[z.2.2 = true] ≤
      if isPm pt t = true then (s.1.length : ℝ≥0∞) / Fintype.card B else 0 := by
  have hfresh : ∀ u : List B, Pr{let y ← freshRF u}[y.2 = true] ≤ u.length / Fintype.card B :=
    fun u => by simpa [freshRF] using prEvent_mem_le u
  have hF : ∀ b, Pr{let r ← fwdF freshRF b s.1}[r.1.2 = true] ≤
      (s.1.length : ℝ≥0∞) / Fintype.card B := fun b => by
    unfold fwdF
    cases fwdFind s.1 b with
    | some y => simp
    | none => simp only [prEvent_map]; exact (hfresh _).trans_eq (by simp)
  have hI : ∀ c, Pr{let r ← invF freshRF c s.1}[r.1.2 = true] ≤
      (s.1.length : ℝ≥0∞) / Fintype.card B := fun c => by
    unfold invF
    cases invFind s.1 c with
    | some y => simp
    | none => simp only [prEvent_map]; exact (hfresh _).trans_eq (by simp)
  rcases t with i | ⟨_ | _, b⟩
  · simp only [pmImplF, StateT.run_mk, isPm]
    split
    · next hp => simp [hp]
    · next b hp =>
      simp only [hp, Option.isSome_some, ite_true]
      refine (prEvent_bind_le_prEvent_of_forall_eq_zero _ _ (fun r => r.1.2 = true) _
        fun r hr => ?_).trans (hF b)
      rw [prEvent_map]
      exact prEvent_eq_zero_of_forall_mem_support _ _ fun u _ hu => hr (by simpa using hu)
  · simpa [pmImplF, isPm, prEvent_map] using hI b
  · simpa [pmImplF, isPm, prEvent_map] using hF b

omit [Fintype B] [SampleableType B] in
theorem fwdF_len (fresh : List B → ProbComp (B × Bool)) (b : B) (L : PTab B) :
    ∀ r ∈ support (fwdF fresh b L), r.2.length ≤ L.length + 1 := by
  intro r hr
  unfold fwdF at hr
  cases h : fwdFind L b with
  | some y => rw [h] at hr; simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; simp
  | none =>
    rw [h] at hr; erw [support_map] at hr
    obtain ⟨y, -, rfl⟩ := hr; simp

omit [Fintype B] [SampleableType B] in
theorem invF_len (fresh : List B → ProbComp (B × Bool)) (c : B) (L : PTab B) :
    ∀ r ∈ support (invF fresh c L), r.2.length ≤ L.length + 1 := by
  intro r hr
  unfold invF at hr
  cases h : invFind L c with
  | some y => rw [h] at hr; simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; simp
  | none =>
    rw [h] at hr; erw [support_map] at hr
    obtain ⟨y, -, rfl⟩ := hr; simp

omit [Fintype B] [SampleableType B] in
/-- A step grows the table by at most one if it is charged, not at all otherwise. -/
theorem pmImplF_len (fresh : List B → ProbComp (B × Bool)) (t : ι ⊕ (Bool × B))
    (s : (PTab B × σ) × Bool) :
    ∀ z ∈ support (((pmImplF pt implC fresh) t).run s),
      z.2.1.1.length ≤ s.1.1.length + if isPm pt t = true then 1 else 0 := by
  intro z hz
  rcases t with i | ⟨_ | _, b⟩
  · simp only [pmImplF, StateT.run_mk] at hz
    cases hp : pt i with
    | none =>
      rw [hp] at hz; erw [support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz; simp [isPm, hp]
    | some b =>
      rw [hp] at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨r, hr, hz⟩ := hz
      erw [support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      simpa [isPm, hp] using fwdF_len fresh b s.1.1 r hr
  · simp only [pmImplF, StateT.run_mk] at hz; erw [support_map] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    simpa [isPm] using invF_len fresh b s.1.1 r hr
  · simp only [pmImplF, StateT.run_mk] at hz; erw [support_map] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    simpa [isPm] using fwdF_len fresh b s.1.1 r hr

/-- **The switch from the permutation to the function, with inverse queries**: for a computation
with at most `q` queries that read the permutation, from a table of length `n₀`, every event of
the run is at most as likely as under the two-sided random function plus `q·(n₀ + q)/|B|`. -/
theorem prEvent_rp_le_rf {α : Type} (oa : OracleComp (specPm A B) α) (q : ℕ)
    (hq : IsQueryBoundP oa (fun t => isPm pt t = true) q) (L₀ : PTab B) (s₀ : σ)
    (E : α × (PTab B × σ) → Prop) :
    Pr{let z ← (simulateQ (rpImpl pt implC) oa).run (L₀, s₀)}[E z] ≤
      Pr{let z ← (simulateQ (rfImpl pt implC) oa).run (L₀, s₀)}[E z] +
        q * ((L₀.length + q : ℕ) / Fintype.card B) := by
  have hproj : ∀ (fresh : List B → ProbComp (B × Bool)) (g : List B → ProbComp B),
      (∀ u, Prod.fst <$> fresh u =ᵈ g u) →
      Pr{let z ← (simulateQ (pmImpl pt implC g) oa).run (L₀, s₀)}[E z] =
        Pr{let z ← (simulateQ (pmImplF pt implC fresh) oa).run ((L₀, s₀), false)}[
          E (z.1, z.2.1)] := by
    intro fresh g hg
    have h := LazyIdeal.simulateQ_proj_eqd_inv (pmImplF pt implC fresh) (pmImpl pt implC g)
      Prod.fst (fun _ => True) (fun _ _ _ _ _ => trivial)
      (fun t s _ => pmImplF_proj pt implC fresh g hg t s) oa ((L₀, s₀), false) trivial
    rw [← h.prEvent_eq, prEvent_map]
  rw [rpImpl, rfImpl, hproj freshRP unifCompl freshRP_fst, hproj freshRF _ freshRF_fst]
  refine (prEvent_le_add_flag _ _ (fun t s => pmImplF_mono pt implC _ t s)
    (fun t s => pmImplF_mono pt implC _ t s) (pmImplF_agree pt implC) oa (L₀, s₀) E).trans
    (add_le_add le_rfl ?_)
  refine prEvent_bad_le (pmImplF pt implC freshRF) (fun s => s.2 = true)
    (fun t => isPm pt t = true) (fun k s => s.1.1.length + k ≤ L₀.length + q) _
    (fun t s k hG hb hk => ?_) (fun t s k hG hb hk z hz _ => ?_) oa q _ hq (by simp) (by simp)
  · obtain ⟨s', f⟩ := s
    simp only [Bool.not_eq_true] at hb; subst hb
    refine (pmImplF_rf_flag pt implC t s').trans ?_
    split_ifs
    · have hG' : s'.1.length + k ≤ L₀.length + q := hG
      gcongr; exact_mod_cast (by omega : s'.1.length ≤ L₀.length + q)
    · exact le_rfl
  · have hl := pmImplF_len pt implC freshRF t s z hz
    split_ifs at hl ⊢ with hp
    · have := hk hp; omega
    · omega

/-! ### An inverse answer in a given set -/

/-- The inverse queries. -/
def isInv : ι ⊕ (Bool × B) → Bool
  | .inr (false, _) => true
  | _ => false

/-- **An inverse answer in `S`**: a record determined by an inverse query whose input is in
`S`. -/
def InvHit (S : Set B) (L : PTab B) : Prop := ∃ e ∈ L, e.2.2 = false ∧ e.1 ∈ S

omit [SampleableType B] [Fintype B] in
theorem fwdS_invHit (fresh : List B → ProbComp B) (S : Set B) (b : B) (L : PTab B)
    (hL : ¬InvHit S L) : ∀ r ∈ support (fwdS fresh b L), ¬InvHit S r.2 := by
  intro r hr
  unfold fwdS at hr
  cases h : fwdFind L b with
  | some y => rw [h] at hr; simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hL
  | none =>
    rw [h] at hr; erw [support_map] at hr
    obtain ⟨y, -, rfl⟩ := hr
    rintro ⟨e, he, he2, he1⟩
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hL ⟨e, he, he2, he1⟩
    · simp at he2

/-- **An inverse answer of the two-sided random function lands in `S`** with probability at most
`q_i·|S|/|B|` after `q_i` inverse queries. -/
theorem prEvent_invHit_le {α : Type} (oa : OracleComp (specPm A B) α) (qi : ℕ)
    (hq : IsQueryBoundP oa (fun t => isInv t = true) qi) (S : Finset B) (L₀ : PTab B)
    (hL₀ : ¬InvHit (S : Set B) L₀) (s₀ : σ) :
    Pr{let z ← (simulateQ (rfImpl pt implC) oa).run (L₀, s₀)}[InvHit (S : Set B) z.2.1] ≤
      qi * (S.card / Fintype.card B) := by
  classical
  refine prEvent_bad_le (rfImpl pt implC) (fun s => InvHit (S : Set B) s.1)
    (fun t => isInv t = true) (fun _ _ => True) _ (fun t s k _ hb hk => ?_)
    (fun _ _ _ _ _ _ _ _ _ => trivial) oa qi (L₀, s₀) hq trivial hL₀
  rcases t with i | ⟨_ | _, c⟩
  · simp only [isInv, Bool.false_eq_true, ite_false, nonpos_iff_eq_zero]
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hzb => ?_
    simp only [rfImpl, pmImpl, StateT.run_mk] at hz
    split at hz
    · erw [support_map] at hz; obtain ⟨u, -, rfl⟩ := hz; exact hb hzb
    · simp only [mem_support_bind_iff] at hz
      obtain ⟨r, hr, hz⟩ := hz
      erw [support_map] at hz; obtain ⟨u, -, rfl⟩ := hz
      exact fwdS_invHit _ _ _ _ hb r hr hzb
  · simp only [isInv, ite_true, rfImpl, pmImpl, StateT.run_mk, prEvent_map]
    unfold invS
    cases h : invFind s.1 c with
    | some x => simp [hb]
    | none =>
      simp only [prEvent_map]
      refine (prEvent_mono _ _ (fun x => x ∈ (S : Set B)) fun x hx => ?_).trans ?_
      · obtain ⟨e, he, he2, he1⟩ := hx
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact absurd ⟨e, he, he2, he1⟩ hb
        · exact he1
      · rw [SampleableType.prEvent_uniformSample]
        gcongr
        exact fun y hy => by simpa using hy
  · simp only [isInv, Bool.false_eq_true, ite_false, nonpos_iff_eq_zero]
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hzb => ?_
    simp only [rfImpl, pmImpl, StateT.run_mk] at hz
    erw [support_map] at hz; obtain ⟨r, hr, rfl⟩ := hz
    exact fwdS_invHit _ _ _ _ hb r hr hzb

end Perm

/-! ## Stateful simulations: query bounds and outputs -/

section SimBounds

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ : Type}

/-- **Query bounds through a stateful simulation**: if every query of kind `p₁` makes at most one
query of kind `p₂` and every other query none, a `p₁`-bound of `k` gives a `p₂`-bound of `k`. -/
theorem isQueryBoundP_run_simulateQ (red : QueryImpl spec₁ (StateT σ (OracleComp spec₂)))
    (p₁ : ι₁ → Prop) [DecidablePred p₁] (p₂ : ι₂ → Prop) [DecidablePred p₂]
    (hstep : ∀ t s, IsQueryBoundP ((red t).run s) p₂ (if p₁ t then 1 else 0)) {α : Type}
    (oa : OracleComp spec₁ α) :
    ∀ k s, IsQueryBoundP oa p₁ k → IsQueryBoundP ((simulateQ red oa).run s) p₂ k := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro k s _; trivial
  | query_bind t cont ih =>
    intro k s hk
    rw [isQueryBoundP_query_bind_iff] at hk
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    refine (isQueryBoundP_bind (hstep t s) fun z _ => ih z.1 _ z.2 (hk.2 z.1)).mono ?_
    split_ifs with h
    · have := hk.1.resolve_left (not_not.2 h); omega
    · omega

/-- **Outputs of a stateful simulation are outputs of the computation.** -/
theorem mem_support_of_run_simulateQ (red : QueryImpl spec₁ (StateT σ (OracleComp spec₂)))
    {α : Type} (oa : OracleComp spec₁ α) :
    ∀ s, ∀ z ∈ support ((simulateQ red oa).run s), z.1 ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro s z hz; simp only [simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz; subst hz; simp
  | query_bind t cont ih =>
    intro s z hz
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, -, hz⟩ := hz
    simp only [mem_support_bind_iff]
    exact ⟨w.1, by simp, ih w.1 w.2 z hz⟩

end SimBounds

end VoleMole.Assumptions.LazyPerm
