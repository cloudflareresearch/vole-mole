import VoleMole.ZK.LabelRows
import VoleMole.Prob.Uniform

/-!
# Zero knowledge on `main`: labels on the first λ witness rows, under (PU) (`lean/docs/zk.md` §4, §6 H6)

On `main` (faest-arch-opt patches 0001–0004, FAEST's own layout), the CRT gate labels come from the
first λ witness rows (`main:faest/vole_commit.inc:364, 369`). The label offset is then
`Θ = u₀[0..λ)`, and since `d = u₀ + w` is public, `Θ = d[0..λ) + w[0..λ)` (`sibling_eq`). Hybrid H6
(c_mult uniform, H₅ unprogrammed at the sibling labels) is then identical to H5 until some H₅ query
hits a sibling label, and a query hits iff it guesses `w[0..λ)` (`query_hits_sibling_iff`). This
file bounds that bad event by the probability of predicting `w[0..λ)`: condition (PU).

Model (counting style of `LabelRows.lean`): the tape is the tree outputs `(a₀, a_i)` on the witness
rows, uniform after H4; the verifier sees `d = a₀ + w`, `c_i = a₀ + a_i` and its forced labels,
a function `forcedOf` of public data (`mainView`); `Θ = π a₀`, with `π` the projection to the first
λ rows. There are no dedicated label rows.

**The view without Θ is witness-independent, but Θ is not independent of it:**
* `mainView_card`, `mainView_indep`, `mainView_responses_indep`: `(d, c_i, forced labels)` is
  uniform on consistent values for every witness, also with the bijectively masked KOS/QuickSilver
  responses added (`Masking.lean`). This is H5–H7 on the view, as in the patched layout.
* `mainView_theta`, `mainView_theta_card`: but `Θ = π d − π w` is a function of the view and
  `w[0..λ)`: the joint count with `Θ = θ` is `1` iff `θ = π d − π w`. Compare
  `labelView_theta_card` (patched layout), where it is `1` for every `θ`.

**The bad event, bounded by prediction (`MainLayout`):** an abstract layout for any number of proofs
that share a secret `s` (for Moussaka, the opening `r`, which is the label prefix of both its
issuance and its redemption witness): views `view s r`, label offsets `theta j r`, label prefixes
`pre j s` (`w_j[0..λ)`), and a reparametrisation of the tapes that turns the view into the view of
the zero witness and shifts each `Θ_j` by `pre j s` (`mainLayout` for one proof, `MainLayout.prod`
for several).
* `MainLayout.prU_hit_eq`: for any query `Q` (proof index and offset `X − L^{γ}`), computed from
  auxiliary information `aux s` about the secret, the view, and independent coins `ω`, the
  probability that it hits a sibling label **equals** the success probability of the predictor
  `MainLayout.predictor Q`, which runs `Q` on the view of the zero witness (computable without `s`)
  and outputs `Θ_j − offset` as its guess for `pre j s`. An explicit, witness-free reduction.
* `prU_exists_le_sum`, `MainLayout.prU_exists_hit_le_sum`, `MainLayout.prU_exists_hit_le`: for `q`
  queries, `Pr[some query hits] ≤ Σ_k Pr[predictor_k succeeds] ≤ q·ε_PU`, where (PU) is the
  hypothesis that each of these `q` predictors succeeds with probability `≤ ε_PU`.
* `prU_shear`, `MainLayout.prU_exists_hit_responses_le`: the same bound when the queries also see
  the KOS/QuickSilver responses, which may depend on `Θ` and `w` but are a bijection of uniform
  masks (`kosQsEquiv`); the predictor samples them uniformly itself.
* `prU_guess_le_of_uniform`, `MainLayout.prU_exists_hit_le_of_uniform`: if `aux` carries no
  information (constant) and each `pre j` is uniform on `Ul`, then (PU) holds for every predictor,
  unbounded, with `ε_PU = 1/|Ul| = 2^{-λ}`.
* `prU_le_add_of_iff_off`: the identical-until-bad step (H5 → H6) in its probabilistic form: two
  events that agree off `Bad` differ by at most `Pr[Bad]`.

**The attack as a distinguisher:** `attack_test_real` (a real proof always passes the test of
`lean/docs/zk.md` Proposition 4.1 for the right guess of `w[0..λ)`) and `card_attack_test_ideal` (a
uniform `c_mult` passes for exactly `#S` of the values).

What is not here (paper, `lean/docs/zk.md` §§5–6): that H5 and H6 can be coupled to agree off the
bad event (lazy sampling of H₅ at the sibling points), that the adaptive queries before the first
hit are functions of `(aux, view, ω)` with `ω` independent (they see only uniform H₅ answers,
uniform `c_mult` and uniform responses in H6/H7), the summation over proofs through `iv`
(`ε_iv`), and H1–H4, H8.
-/

open Finset VoleMole.Prob ENNReal

namespace VoleMole.ZK

section MainView

variable {Uw Ul Lab : Type*} [AddCommGroup Uw] [AddCommGroup Ul] {τ : ℕ}

/-- The tape on `main`: tree outputs `(a₀, a)` on the witness rows. The label rows are the first λ
of them, so there is no separate label-row tape. -/
abbrev MainTape (Uw : Type*) (τ : ℕ) := Uw × (Fin τ → Uw)

/-- The verifier's view on `main`: `d = a₀ + w`, `c_i = a₀ + a_i`
(`main:src/voleith.hpp:228-233`, `vole_commit.inc:103-122`), and the forced labels, a function
of public data. -/
def mainView (w : Uw) (forcedOf : Uw → (Fin τ → Uw) → Lab) (r : MainTape Uw τ) :
    Uw × (Fin τ → Uw) × Lab :=
  (r.1 + w, fun i => r.1 + r.2 i, forcedOf (r.1 + w) (fun i => r.1 + r.2 i))

/-- Whether a view value is consistent: its labels are the forced labels of its corrections. -/
abbrev MainConsistent (forcedOf : Uw → (Fin τ → Uw) → Lab) (o : Uw × (Fin τ → Uw) × Lab) :
    Prop :=
  o.2.2 = forcedOf o.1 o.2.1

/-- **The label offset is public data plus `w[0..λ)`.** `Θ = π a₀ = π d − π w` for every tape
(over `F₂`, `π d + π w`; `sibling_eq`). -/
theorem mainView_theta (π : Uw →+ Ul) (w : Uw) (forcedOf : Uw → (Fin τ → Uw) → Lab)
    (r : MainTape Uw τ) : π r.1 = π (mainView w forcedOf r).1 - π w := by
  simp [mainView]

variable [Fintype Uw] [DecidableEq Uw] [DecidableEq Lab]

/-- **The view is uniform on consistent values, for every witness** (H5 on `main`). -/
theorem mainView_card (w : Uw) (forcedOf : Uw → (Fin τ → Uw) → Lab)
    (o : Uw × (Fin τ → Uw) × Lab) :
    fiberCard (mainView w forcedOf) o = if MainConsistent forcedOf o then 1 else 0 := by
  obtain ⟨d, c, f⟩ := o
  unfold fiberCard MainConsistent
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨(d - w, fun i => c i - (d - w)), ?_⟩
    ext ⟨a0, a⟩
    simp only [mem_filter, mem_univ, true_and, mem_singleton, mainView, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, -⟩
      exact ⟨by simp, funext fun i => by simp⟩
    · rintro ⟨rfl, rfl⟩
      have e1 : d - w + w = d := sub_add_cancel d w
      have e2 : (fun i => d - w + (c i - (d - w))) = c := funext fun i => by abel
      simp only at h
      exact ⟨e1, e2, by rw [e1, e2]; exact h.symm⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨a0, a⟩ -
    simp only [mainView, Prod.mk.injEq, not_and]
    rintro rfl rfl hf
    exact h hf.symm

/-- The view's distribution does not depend on the witness. -/
theorem mainView_indep (w w' : Uw) (forcedOf : Uw → (Fin τ → Uw) → Lab)
    (o : Uw × (Fin τ → Uw) × Lab) :
    fiberCard (mainView (τ := τ) w forcedOf) o = fiberCard (mainView (τ := τ) w' forcedOf) o := by
  rw [mainView_card, mainView_card]

-- The view type `(Uw × (Fin τ → Uw) × Lab) × O'` needs a larger instance budget.
set_option synthInstance.maxSize 512 in
/-- With the masked responses `φ p m` (a bijection of uniform masks `m` for every tape `p`, which
may depend on `Θ` and `w`; `kosQsEquiv`), the view is still witness-independent (H7 on `main`). -/
theorem mainView_responses_indep {M O' : Type*} [Fintype M] [DecidableEq O'] (w w' : Uw)
    (forcedOf : Uw → (Fin τ → Uw) → Lab) (φ φ' : MainTape Uw τ → M ≃ O')
    (o : Uw × (Fin τ → Uw) × Lab) (o' : O') :
    fiberCard (fun r : MainTape Uw τ × M => (mainView w forcedOf r.1, φ r.1 r.2)) (o, o') =
      fiberCard (fun r : MainTape Uw τ × M => (mainView w' forcedOf r.1, φ' r.1 r.2)) (o, o') := by
  rw [fiberCard_shear, fiberCard_shear, mainView_indep w w']

/-- **Θ is determined by the view and `w[0..λ)`.** Exactly one tape gives view `o` with `Θ = θ` if
`o` is consistent and `θ = π d − π w`, and none otherwise. Compare `labelView_theta_card`. -/
theorem mainView_theta_card [DecidableEq Ul] (π : Uw →+ Ul) (w : Uw)
    (forcedOf : Uw → (Fin τ → Uw) → Lab) (o : Uw × (Fin τ → Uw) × Lab) (θ : Ul) :
    #(univ.filter fun r : MainTape Uw τ => mainView w forcedOf r = o ∧ π r.1 = θ) =
      if MainConsistent forcedOf o ∧ θ = π o.1 - π w then 1 else 0 := by
  by_cases hθ : θ = π o.1 - π w
  · have : (univ.filter fun r : MainTape Uw τ => mainView w forcedOf r = o ∧ π r.1 = θ) =
        univ.filter fun r => mainView w forcedOf r = o := by
      refine filter_congr fun r _ => ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      rw [hθ, mainView_theta π w forcedOf r, h]
    rw [this, ← fiberCard, mainView_card]
    simp [hθ]
  · simp only [hθ, and_false, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro r - ⟨ho, rfl⟩
    exact hθ (by rw [mainView_theta π w forcedOf r, ho])

end MainView

section Layout

/-- **An abstract `main`-layout experiment** for one or several proofs that share a secret `s`.
`view s r` is what the verifier sees on tape `r`; `theta j r` is proof `j`'s label offset; `pre j s`
is proof `j`'s label prefix `w_j[0..λ)`. `reparam s` re-parametrises the tapes so that the view of
`s` becomes the view of the zero witness, `view0`, and each offset moves by `pre j s`. -/
structure MainLayout (S R V J Ul : Type*) [AddCommGroup Ul] where
  view : S → R → V
  view0 : R → V
  theta : J → R → Ul
  pre : J → S → Ul
  reparam : S → R ≃ R
  view0_reparam : ∀ s r, view0 (reparam s r) = view s r
  theta_reparam : ∀ j s r, theta j (reparam s r) = theta j r + pre j s

variable {S R V J Ul X Ω : Type*} [AddCommGroup Ul]

/-- A query `y = (j, X − L^{γ})` hits proof `j`'s sibling label iff its offset is `Θ_j`
(`query_hits_sibling_iff`). -/
def MainLayout.Hit (L : MainLayout S R V J Ul) (y : J × Ul) (r : R) : Prop :=
  y.2 = L.theta y.1 r

/-- **The reduction to (PU).** Run the query on the view of the zero witness, which needs no
secret, and guess `pre j s := Θ_j − offset`. Its coins are the tape and `ω`. -/
def MainLayout.predictor (L : MainLayout S R V J Ul) (Q : X → V → Ω → J × Ul) (x : X) (r : R)
    (ω : Ω) : J × Ul :=
  ((Q x (L.view0 r) ω).1, L.theta (Q x (L.view0 r) ω).1 r - (Q x (L.view0 r) ω).2)

/-- The predictor's success event: its guess is the label prefix of the proof it names. -/
def MainLayout.Predicts (L : MainLayout S R V J Ul) (g : J × Ul) (s : S) : Prop :=
  g.2 = L.pre g.1 s

/-- One proof on `main`: `mainLayout π wit forcedOf`, with `Θ = π a₀` and `pre = π ∘ wit`. -/
def mainLayout {Uw Lab : Type*} [AddCommGroup Uw] {τ : ℕ} (π : Uw →+ Ul) (wit : S → Uw)
    (forcedOf : Uw → (Fin τ → Uw) → Lab) :
    MainLayout S (MainTape Uw τ) (Uw × (Fin τ → Uw) × Lab) Unit Ul where
  view s r := mainView (wit s) forcedOf r
  view0 r := mainView 0 forcedOf r
  theta _ r := π r.1
  pre _ s := π (wit s)
  reparam s := (Equiv.addRight (wit s)).prodCongr (Equiv.subRight fun _ => wit s)
  view0_reparam s r := by
    simp only [mainView, Equiv.prodCongr_apply, Prod.map, Equiv.coe_addRight, Equiv.subRight_apply,
      Pi.sub_apply, add_zero]
    have : (fun i => r.1 + wit s + (r.2 i - wit s)) = fun i => r.1 + r.2 i :=
      funext fun i => by abel
    rw [this]
  theta_reparam _ s r := by simp

/-- Several proofs with a shared secret: the views side by side, proofs indexed by `J₁ ⊕ J₂`. -/
def MainLayout.prod {R₁ R₂ V₁ V₂ J₁ J₂ : Type*} (L₁ : MainLayout S R₁ V₁ J₁ Ul)
    (L₂ : MainLayout S R₂ V₂ J₂ Ul) : MainLayout S (R₁ × R₂) (V₁ × V₂) (J₁ ⊕ J₂) Ul where
  view s r := (L₁.view s r.1, L₂.view s r.2)
  view0 r := (L₁.view0 r.1, L₂.view0 r.2)
  theta j r := Sum.elim (fun j => L₁.theta j r.1) (fun j => L₂.theta j r.2) j
  pre j s := Sum.elim (fun j => L₁.pre j s) (fun j => L₂.pre j s) j
  reparam s := (L₁.reparam s).prodCongr (L₂.reparam s)
  view0_reparam s r := by simp [L₁.view0_reparam, L₂.view0_reparam]
  theta_reparam j s r := by cases j <;> simp [L₁.theta_reparam, L₂.theta_reparam]

variable [Fintype S] [Nonempty S] [Fintype R] [Nonempty R] [Fintype Ω] [Nonempty Ω]

/-- **One query: hitting a sibling label is exactly predicting the label prefix.** For any query
computed from `aux s`, the view and independent coins, the probability that it hits equals the
probability that `L.predictor Q` predicts `pre j s` from `aux s` alone. -/
theorem MainLayout.prU_hit_eq (L : MainLayout S R V J Ul) (aux : S → X)
    (Q : X → V → Ω → J × Ul) :
    prU (S × R × Ω) (fun p => L.Hit (Q (aux p.1) (L.view p.1 p.2.1) p.2.2) p.2.1) =
      prU (S × R × Ω) (fun p => L.Predicts (L.predictor Q (aux p.1) p.2.1 p.2.2) p.1) := by
  let e : S × R × Ω ≃ S × R × Ω :=
    Equiv.prodShear (Equiv.refl S) fun s => (L.reparam s).prodCongr (Equiv.refl Ω)
  conv_rhs => rw [prU_map_equiv e]
  refine prU_congr fun ⟨s, r, ω⟩ => ?_
  simp only [e, Function.comp, Equiv.prodShear_apply, Equiv.refl_apply, Equiv.prodCongr_apply,
    Prod.map, MainLayout.Predicts, MainLayout.predictor, MainLayout.Hit, L.view0_reparam,
    L.theta_reparam]
  generalize Q (aux s) (L.view s r) ω = y
  constructor
  · intro h; rw [h]; abel
  · intro h
    rw [sub_eq_iff_eq_add, add_comm (L.pre y.1 s), add_right_cancel_iff] at h
    exact h.symm

omit [Fintype S] [Nonempty S] [Fintype R] [Nonempty R] [Fintype Ω] [Nonempty Ω] in
/-- **The union bound over finitely many events.** -/
theorem prU_exists_le_sum {α : Type*} [Fintype α] [Nonempty α] {q : ℕ} (P : Fin q → α → Prop) :
    prU α (fun x => ∃ k, P k x) ≤ ∑ k, prU α (P k) := by
  unfold prU
  have : {x | ∃ k, P k x} = ⋃ k, {x | P k x} := by ext; simp
  rw [this]
  exact MeasureTheory.measure_iUnion_fintype_le _ _

/-- **`q` queries: `Pr[some query hits a sibling label] ≤ Σ_k Pr[predictor_k succeeds]`.** -/
theorem MainLayout.prU_exists_hit_le_sum (L : MainLayout S R V J Ul) (aux : S → X) {q : ℕ}
    (Q : Fin q → X → V → Ω → J × Ul) :
    prU (S × R × Ω) (fun p => ∃ k, L.Hit (Q k (aux p.1) (L.view p.1 p.2.1) p.2.2) p.2.1) ≤
      ∑ k, prU (S × R × Ω) (fun p => L.Predicts (L.predictor (Q k) (aux p.1) p.2.1 p.2.2) p.1) :=
  (prU_exists_le_sum _).trans (Finset.sum_le_sum fun k _ => (L.prU_hit_eq aux (Q k)).le)

/-- **ZK on `main` under (PU): the sibling-label bad event is at most `q·ε_PU`.** (PU) is the
hypothesis `hPU`: each of the `q` explicit predictors `L.predictor (Q k)` (the adversary run on a
simulated view) predicts the label prefix from `aux` with probability at most `ε_PU`. -/
theorem MainLayout.prU_exists_hit_le (L : MainLayout S R V J Ul) (aux : S → X) {q : ℕ}
    (Q : Fin q → X → V → Ω → J × Ul) {ε : ℝ≥0∞}
    (hPU : ∀ k, prU (S × R × Ω)
      (fun p => L.Predicts (L.predictor (Q k) (aux p.1) p.2.1 p.2.2) p.1) ≤ ε) :
    prU (S × R × Ω) (fun p => ∃ k, L.Hit (Q k (aux p.1) (L.view p.1 p.2.1) p.2.2) p.2.1) ≤
      q * ε := by
  refine (L.prU_exists_hit_le_sum aux Q).trans ?_
  calc ∑ k, prU (S × R × Ω) (fun p => L.Predicts (L.predictor (Q k) (aux p.1) p.2.1 p.2.2) p.1)
      ≤ ∑ _k : Fin q, ε := Finset.sum_le_sum fun k _ => hPU k
    _ = q * ε := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [Fintype S] [Nonempty S] [Fintype R] [Nonempty R] [Fintype Ω] [Nonempty Ω] in
/-- **Shear for probabilities.** If the second coordinate enters an event only through a bijection
`φ p` of uniform masks, the masks may be replaced by uniform values. -/
theorem prU_shear {P M M' : Type*} [Fintype P] [Nonempty P] [Fintype M] [Nonempty M] [Fintype M']
    [Nonempty M'] (φ : P → M ≃ M') (E : P → M' → Prop) :
    prU (P × M) (fun x => E x.1 (φ x.1 x.2)) = prU (P × M') (fun x => E x.1 x.2) := by
  rw [prU_map_equiv (Equiv.prodShear (Equiv.refl P) φ)]
  rfl

/-- **With the KOS/QuickSilver responses.** The queries also see `φ (s, r) m`, the responses as a
bijection of the uniform masks `m` for every secret and tape (`kosQsEquiv`; they depend on `Θ` and
`w`). The bad event is still at most `q·ε_PU`, for the predictors that sample the responses
uniformly themselves. -/
theorem MainLayout.prU_exists_hit_responses_le {M M' : Type*} [Fintype M] [Nonempty M]
    [Fintype M'] [Nonempty M'] (L : MainLayout S R V J Ul) (aux : S → X) (φ : S × R → M ≃ M')
    {q : ℕ} (Q : Fin q → X → V × M' → Ω → J × Ul) {ε : ℝ≥0∞}
    (hPU : ∀ k, prU (S × R × (M' × Ω)) (fun p => L.Predicts
      (L.predictor (fun x v (mω : M' × Ω) => Q k x (v, mω.1) mω.2) (aux p.1) p.2.1 p.2.2) p.1) ≤ ε) :
    prU ((S × R) × (M × Ω)) (fun p => ∃ k,
      L.Hit (Q k (aux p.1.1) (L.view p.1.1 p.1.2, φ p.1 p.2.1) p.2.2) p.1.2) ≤ q * ε := by
  have h1 := prU_shear (P := S × R) (M := M × Ω) (M' := M' × Ω)
    (fun p => (φ p).prodCongr (Equiv.refl Ω))
    (fun p (mω : M' × Ω) => ∃ k, L.Hit (Q k (aux p.1) (L.view p.1 p.2, mω.1) mω.2) p.2)
  simp only [Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply] at h1
  rw [h1, prU_map_equiv (Equiv.prodAssoc S R (M' × Ω)).symm]
  exact L.prU_exists_hit_le aux (fun k x v (mω : M' × Ω) => Q k x (v, mω.1) mω.2) hPU

omit [Fintype R] [Nonempty R] [Fintype Ω] [Nonempty Ω] in
/-- **(PU) without auxiliary information.** If each label prefix `pre j` is uniform on `Ul`, then
any guess that does not depend on the secret succeeds with probability at most `1/|Ul|`, for every
(unbounded) predictor. -/
theorem prU_guess_le_of_uniform {C : Type*} [Fintype C] [Nonempty C] [Fintype Ul] [DecidableEq Ul]
    (pre : J → S → Ul) (hpre : ∀ j u, #{s | pre j s = u} * Fintype.card Ul ≤ Fintype.card S)
    (B : C → J × Ul) :
    prU (S × C) (fun p => (B p.2).2 = pre (B p.2).1 p.1) ≤ (Fintype.card Ul : ℝ≥0∞)⁻¹ := by
  refine prU_prod_le_left _ fun c => ?_
  classical
  rw [prU_eq_card]
  have hS : (Fintype.card S : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hU : (Fintype.card Ul : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn : (#{s | (B c).2 = pre (B c).1 s} : ℝ≥0∞) * Fintype.card Ul ≤ Fintype.card S := by
    have h := hpre (B c).1 (B c).2
    have he : #{s | (B c).2 = pre (B c).1 s} = #{s | pre (B c).1 s = (B c).2} := by
      congr 1; ext s; simp [eq_comm]
    rw [he]
    exact_mod_cast h
  dsimp only
  refine ENNReal.div_le_of_le_mul ?_
  rw [← ENNReal.div_eq_inv_mul]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hU) (Or.inl (by simp))).2 hn

omit [Fintype R] [Nonempty R] [Fintype Ω] [Nonempty Ω] in
/-- **ZK on `main` with a uniform, unseen label prefix: `q·2^{-λ}`.** If the adversary's auxiliary
information is constant and every label prefix is uniform, the bad event is at most `q/|Ul|`, for
every adversary: (PU) holds statistically. -/
theorem MainLayout.prU_exists_hit_le_of_uniform [Fintype R] [Nonempty R] [Fintype Ω] [Nonempty Ω]
    [Fintype Ul] [DecidableEq Ul] (L : MainLayout S R V J Ul)
    (hpre : ∀ j u, #{s | L.pre j s = u} * Fintype.card Ul ≤ Fintype.card S) (x₀ : X) {q : ℕ}
    (Q : Fin q → X → V → Ω → J × Ul) :
    prU (S × R × Ω) (fun p => ∃ k, L.Hit (Q k x₀ (L.view p.1 p.2.1) p.2.2) p.2.1) ≤
      q * (Fintype.card Ul : ℝ≥0∞)⁻¹ :=
  L.prU_exists_hit_le (fun _ => x₀) Q fun k =>
    prU_guess_le_of_uniform (C := R × Ω) L.pre hpre fun c => L.predictor (Q k) x₀ c.1 c.2

end Layout

/-- **Identical until bad** (the shape of H5 → H6): if two events agree off `Bad`, then
`Pr[E] ≤ Pr[E'] + Pr[Bad]`. -/
theorem prU_le_add_of_iff_off {α : Type*} [Fintype α] [Nonempty α] (E E' Bad : α → Prop)
    (h : ∀ x, ¬Bad x → (E x ↔ E' x)) : prU α E ≤ prU α E' + prU α Bad := by
  refine (prU_mono fun x hx => ?_).trans (prU_or_le E' Bad)
  by_cases hb : Bad x
  · exact Or.inr hb
  · exact Or.inl ((h x hb).1 hx)

section Attack

variable {L B : Type*} [AddCommGroup L] [AddCommGroup B] (h2L : ∀ x : L, x + x = 0)
  (h2B : ∀ x : B, x + x = 0)

/-- The test of `lean/docs/zk.md` Proposition 4.1 on one `c_mult` column `c`: with the forced label
`F`, the public `d[0..λ)` and a guess `g` of `w[0..λ)`, accept iff `c + H(F) + H(F + d + g)` lies in
`S` (the image of the CRT matrix). -/
def attackTest [DecidableEq B] (H : L → B) (S : Finset B) (F dPre g : L) (c : B) : Prop :=
  c + H F + H (F + dPre + g) ∈ S

instance [DecidableEq B] (H : L → B) (S : Finset B) (F dPre g : L) (c : B) :
    Decidable (attackTest H S F dPre g c) := by
  unfold attackTest; infer_instance

include h2L h2B in
/-- **A real proof always passes**, for the right guess `g = w[0..λ)` (`attack_recovers`). -/
theorem attack_test_real [DecidableEq B] (H : L → B) (S : Finset B) (L0 u w : L) (f : B)
    (hf : f ∈ S) (γ : Bool) :
    attackTest H S (forced L0 u γ) (u + w) w (H L0 + H (L0 + u) + f) := by
  unfold attackTest
  rw [attack_recovers h2L h2B]
  exact hf

/-- **An ideal (uniform) `c_mult` passes for exactly `#S` of its `|B|` values.** -/
theorem card_attack_test_ideal [Fintype B] [DecidableEq B] (H : L → B) (S : Finset B)
    (F dPre g : L) : #(univ.filter fun c => attackTest H S F dPre g c) = #S := by
  refine Finset.card_bij (fun c _ => c + H F + H (F + dPre + g)) (fun c hc => (mem_filter.1 hc).2)
    (fun c _ c' _ h => by simpa using h) fun b hb => ⟨b - H (F + dPre + g) - H F,
      mem_filter.2 ⟨mem_univ _, show _ ∈ S by convert hb using 1; abel⟩, by abel⟩

end Attack

end VoleMole.ZK
