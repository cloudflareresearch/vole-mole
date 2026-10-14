import VoleMole.ZK.Labels

/-!
# Zero knowledge: dedicated label rows (`lean/docs/zk.md` §3, hybrid H6, patched layout)

On branch `voleith-label-rows` (faest-arch-opt patch 0005), the relations set
`OWF_CONSTANTS::CRT_DEDICATED_LABEL_ROWS`. The CRT gate labels are then computed from λ dedicated
VOLE rows `[ℓ, ℓ+λ)` directly after the `ℓ = WITNESS_BITS` witness rows
(`constants.hpp:410-414`, `CRT_LABEL_ROWS`, `CRT_LABEL_ROW_OFFSET = QUICKSILVER_ROWS = ℓ`). These
rows count toward `VOLE_CORRECTION_ROWS` (`constants.hpp:430-436`), so they get the cross-tree
corrections `c_i = u₀ + u_i` (`vole_commit.inc:111-121`) and are hashed by KOS
(`voleith.hpp:240-243`, `:457-459`), but they get no witness correction `d`, which covers only the
witness rows (`voleith.hpp:469-476`; the proof's `d` has `WITNESS_BITS / 8` bytes). The label
offset is `Θ := u₀` on the label rows (`vole_commit.inc:341-348`, `crt_label_offset`, used at
`:398`, `:427`, `:457`); the labels themselves are `G·V` resp. `G·Q` on those rows
(`crt_labels`, `:351-372`, `:403`). The verifier applies the `c_i` in `vole_reconstruct_impl`
(`:173-175`) before it computes its labels (`lift_and_hash_vq<P, true>`, `:672`).

Model (counting style of `Masking.lean`): the tape is the tree outputs on the witness rows,
`(a₀, a_i)`, and on the label rows, `(Θ, b_i)`, all uniform. After hybrid H4, `b_i` is uniform
because tree `i` has one hidden leaf, whose PRG output pads it; `Θ = b₀` likewise by tree 0's
hidden leaf. The verifier sees `d = a₀ + w`, `c^w_i = a₀ + a_i`, `c^l_i = Θ + b_i`, and its forced
labels, which are a function `forcedOf` of public data (its reconstructed `Q`, given the opened
seeds and `Δ`; see `vole_u_uniform_given_q` and `label_q_eq`).

* `labelCorrEquiv`: `(Θ, b) ↦ (Θ, Θ + b)` is a bijection, so `Θ` is uniform given the `c^l_i`.
* `labelView_theta_card`: `#{tape | view = o ∧ Θ = θ}` is `1` for consistent `o` and `0` otherwise,
  for every `θ` and every witness `w`. So `Θ` is uniform and independent of the view
  (`labelView_theta_uniform`), and the view does not depend on `w` (`labelView_indep`).
* `labelView_responses_theta_card`: the same holds when the view also contains responses
  `φ p m` that are a bijection of separate uniform masks `m` for every tape `p`, even if `φ`
  depends on `Θ` and `w` (the KOS hash covers the label rows).
* `sibling_eq_labelRows`, `query_hits_sibling_iff_labelRows`: the sibling label is
  `forced + Θ`, with no witness term, and a query hits it iff its offset equals `Θ`.
* `card_query_hits_sibling`, `card_theta_zero`: any query offset computed from the view equals `Θ`
  on exactly a `1/|U_l|` fraction (`2^{-λ}`) of the tapes; so does the event `L⁰ = L¹`
  (`Θ = 0`). These give `ε_lab = (Q₅ + n_mult·Q_V + Q_P)·2^{-λ}`.
-/

open Finset

namespace VoleMole.ZK

section Generic

variable {R O Θ : Type*} [Fintype R] [DecidableEq O] [Fintype O] [Fintype Θ] [DecidableEq Θ]

omit [Fintype O] in
/-- If the joint count `#{r | V r = o ∧ T r = θ}` does not depend on `θ`, then `T` is uniform given
the view: `#{V = o ∧ T = θ} · |Θ| = #{V = o}`. -/
theorem card_theta_uniform (V : R → O) (T : R → Θ) (g : O → ℕ)
    (hg : ∀ o θ, #(univ.filter fun r => V r = o ∧ T r = θ) = g o) (o : O) (θ : Θ) :
    #(univ.filter fun r => V r = o ∧ T r = θ) * Fintype.card Θ = fiberCard V o := by
  unfold fiberCard
  rw [hg o θ, card_eq_sum_card_fiberwise (s := univ.filter fun r => V r = o) (f := T) (t := univ)
    (fun _ _ => mem_univ _)]
  simp_rw [filter_filter, hg]
  simp [mul_comm]

/-- **One guess.** If the joint count does not depend on `θ`, then any guess `A (V r)` computed
from the view equals `T r` on exactly a `1/|Θ|` fraction of the tapes. -/
theorem card_guess_eq (V : R → O) (T : R → Θ) (g : O → ℕ)
    (hg : ∀ o θ, #(univ.filter fun r => V r = o ∧ T r = θ) = g o) (A : O → Θ) :
    #(univ.filter fun r => A (V r) = T r) * Fintype.card Θ = Fintype.card R := by
  have h1 : #(univ.filter fun r => A (V r) = T r) = ∑ o, g o := by
    rw [card_eq_sum_card_fiberwise (f := V) (t := univ) (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun o _ => ?_
    rw [filter_filter, ← hg o (A o)]
    congr 1
    refine filter_congr fun r _ => ?_
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h2 ▸ h1.symm⟩, fun ⟨h1, h2⟩ => ⟨h1 ▸ h2.symm, h1⟩⟩
  have h2 : Fintype.card R = ∑ o, fiberCard V o := by
    unfold fiberCard
    rw [← card_univ, card_eq_sum_card_fiberwise (f := V) (t := univ) (fun _ _ => mem_univ _)]
  have hθ : Nonempty Θ ∨ IsEmpty Θ := (isEmpty_or_nonempty Θ).symm
  rcases hθ with ⟨⟨θ⟩⟩ | hE
  · rw [h1, h2, sum_mul]
    exact sum_congr rfl fun o _ => (hg o θ) ▸ card_theta_uniform V T g hg o θ
  · have : IsEmpty R := ⟨fun r => hE.false (T r)⟩
    simp

omit [Fintype O] [Fintype Θ] in
/-- Shear with a secret: if the view is `(V p, φ p m)` with `φ p` a bijection of the uniform masks
`m` for every `p`, its joint count with `T p` equals that of `V` alone. -/
theorem shear_theta_card {P M O' : Type*} [Fintype P] [Fintype M] [DecidableEq O']
    (V : P → O) (T : P → Θ) (φ : P → M ≃ O') (o : O) (o' : O') (θ : Θ) :
    #(univ.filter fun r : P × M => (V r.1, φ r.1 r.2) = (o, o') ∧ T r.1 = θ) =
      #(univ.filter fun p => V p = o ∧ T p = θ) := by
  have := fiberCard_shear (fun p => (V p, T p)) φ (o, θ) o'
  unfold fiberCard at this
  convert this using 2
  · refine filter_congr fun r _ => ?_
    simp only [Prod.mk.injEq]
    tauto
  · refine filter_congr fun p _ => ?_
    simp only [Prod.mk.injEq]

end Generic

section LabelRows

variable {Uw Ul Lab : Type*} [AddCommGroup Uw] [AddCommGroup Ul] {τ : ℕ}

/-- The cross-tree corrections on the label rows, together with the label offset:
`(Θ, b) ↦ (Θ, Θ + b)`, where `c_i = Θ + b_i` (`vole_commit.inc:111-121`). -/
def labelCorrEquiv : Ul × (Fin τ → Ul) ≃ Ul × (Fin τ → Ul) :=
  Equiv.prodShear (Equiv.refl Ul) fun θ => Equiv.addLeft (fun _ => θ)

theorem labelCorrEquiv_apply (t : Ul × (Fin τ → Ul)) :
    labelCorrEquiv t = (t.1, fun i => t.1 + t.2 i) := rfl

/-- `Θ` is uniform given the label-row corrections: each pair `(θ, c)` has exactly one preimage. -/
theorem labelCorr_fiberCard [Fintype Ul] [DecidableEq Ul] (o : Ul × (Fin τ → Ul)) :
    fiberCard (labelCorrEquiv (τ := τ)) o = 1 :=
  fiberCard_equiv labelCorrEquiv o

/-- The tape: tree outputs `(a₀, a)` on the witness rows and `(Θ, b)` on the label rows. -/
abbrev LabelTape (Uw Ul : Type*) (τ : ℕ) := (Uw × (Fin τ → Uw)) × (Ul × (Fin τ → Ul))

/-- The verifier's view: `d = a₀ + w`, `c^w_i = a₀ + a_i`, `c^l_i = Θ + b_i` (no `d` on the label
rows, `voleith.hpp:469-476`), and the forced labels, a function of public data. -/
def labelView (w : Uw) (forcedOf : Uw → (Fin τ → Uw) → (Fin τ → Ul) → Lab)
    (r : LabelTape Uw Ul τ) : Uw × (Fin τ → Uw) × (Fin τ → Ul) × Lab :=
  (r.1.1 + w, fun i => r.1.1 + r.1.2 i, fun i => r.2.1 + r.2.2 i,
    forcedOf (r.1.1 + w) (fun i => r.1.1 + r.1.2 i) (fun i => r.2.1 + r.2.2 i))

/-- Whether a view value is consistent, i.e. its labels are the forced labels of its corrections. -/
abbrev LabelConsistent (forcedOf : Uw → (Fin τ → Uw) → (Fin τ → Ul) → Lab)
    (o : Uw × (Fin τ → Uw) × (Fin τ → Ul) × Lab) : Prop :=
  o.2.2.2 = forcedOf o.1 o.2.1 o.2.2.1

variable [Fintype Uw] [DecidableEq Uw] [Fintype Ul] [DecidableEq Ul] [DecidableEq Lab]

/-- **Θ is independent of the view.** For every witness `w`, offset `θ` and view value `o`,
exactly one tape gives view `o` with `Θ = θ` if `o` is consistent, and none otherwise. -/
theorem labelView_theta_card (w : Uw) (forcedOf : Uw → (Fin τ → Uw) → (Fin τ → Ul) → Lab)
    (o : Uw × (Fin τ → Uw) × (Fin τ → Ul) × Lab) (θ : Ul) :
    #(univ.filter fun r : LabelTape Uw Ul τ => labelView w forcedOf r = o ∧ r.2.1 = θ) =
      if LabelConsistent forcedOf o then 1 else 0 := by
  obtain ⟨d, cw, cl, f⟩ := o
  unfold LabelConsistent
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨((d - w, fun i => cw i - (d - w)), (θ, fun i => cl i - θ)), ?_⟩
    ext ⟨⟨a0, a⟩, ⟨t, b⟩⟩
    simp only [mem_filter, mem_univ, true_and, mem_singleton, labelView, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨rfl, rfl, rfl, -⟩, rfl⟩
      refine ⟨⟨by simp, funext fun i => by simp⟩, rfl, funext fun i => by simp⟩
    · rintro ⟨⟨rfl, rfl⟩, rfl, rfl⟩
      have e1 : d - w + w = d := sub_add_cancel d w
      have e2 : (fun i => d - w + (cw i - (d - w))) = cw := funext fun i => by abel
      have e3 : (fun i => t + (cl i - t)) = cl := funext fun i => by abel
      simp only at h
      exact ⟨⟨e1, e2, e3, by rw [e1, e2, e3]; exact h.symm⟩, rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨⟨a0, a⟩, ⟨t, b⟩⟩ -
    simp only [labelView, Prod.mk.injEq, not_and]
    rintro ⟨rfl, rfl, rfl, hf⟩ -
    exact h hf.symm

/-- The joint count does not depend on `θ` (nor, by the exact value, on `w`). -/
theorem labelView_theta_indep (w : Uw) (forcedOf : Uw → (Fin τ → Uw) → (Fin τ → Ul) → Lab)
    (o : Uw × (Fin τ → Uw) × (Fin τ → Ul) × Lab) (θ θ' : Ul) :
    #(univ.filter fun r : LabelTape Uw Ul τ => labelView w forcedOf r = o ∧ r.2.1 = θ) =
      #(univ.filter fun r : LabelTape Uw Ul τ => labelView w forcedOf r = o ∧ r.2.1 = θ') := by
  rw [labelView_theta_card, labelView_theta_card]

/-- **Θ is uniform given the view**: `#{view = o ∧ Θ = θ} · |U_l| = #{view = o}`. -/
theorem labelView_theta_uniform (w : Uw) (forcedOf : Uw → (Fin τ → Uw) → (Fin τ → Ul) → Lab)
    (o : Uw × (Fin τ → Uw) × (Fin τ → Ul) × Lab) (θ : Ul) :
    #(univ.filter fun r : LabelTape Uw Ul τ => labelView w forcedOf r = o ∧ r.2.1 = θ) *
      Fintype.card Ul = fiberCard (labelView w forcedOf) o :=
  card_theta_uniform _ (fun r : LabelTape Uw Ul τ => r.2.1) _
    (fun o θ => labelView_theta_card w forcedOf o θ) o θ

/-- The view's distribution does not depend on the witness. -/
theorem labelView_indep (w w' : Uw) (forcedOf : Uw → (Fin τ → Uw) → (Fin τ → Ul) → Lab)
    (o : Uw × (Fin τ → Uw) × (Fin τ → Ul) × Lab) :
    fiberCard (labelView (τ := τ) w forcedOf) o = fiberCard (labelView (τ := τ) w' forcedOf) o := by
  rw [← labelView_theta_uniform w forcedOf o 0, ← labelView_theta_uniform w' forcedOf o 0,
    labelView_theta_card, labelView_theta_card]

/-- **One H₅ query, one chance in `|U_l|`.** For any query offset `A` computed from the view (the
query `forced + A(view)` hits the sibling iff `A(view) = Θ`, `query_hits_sibling_iff_labelRows`),
the hitting tapes are exactly a `1/|U_l|` fraction. -/
theorem card_query_hits_sibling [Fintype Lab] (w : Uw)
    (forcedOf : Uw → (Fin τ → Uw) → (Fin τ → Ul) → Lab)
    (A : Uw × (Fin τ → Uw) × (Fin τ → Ul) × Lab → Ul) :
    #(univ.filter fun r : LabelTape Uw Ul τ => A (labelView w forcedOf r) = r.2.1) *
      Fintype.card Ul = Fintype.card (LabelTape Uw Ul τ) :=
  card_guess_eq _ (fun r : LabelTape Uw Ul τ => r.2.1) _
    (fun o θ => labelView_theta_card w forcedOf o θ) A

/-- The event `L⁰ = L¹` (`Θ = 0`) has probability `1/|U_l|`. -/
theorem card_theta_zero :
    #(univ.filter fun r : LabelTape Uw Ul τ => r.2.1 = 0) * Fintype.card Ul =
      Fintype.card (LabelTape Uw Ul τ) := by
  have := card_query_hits_sibling (τ := τ) (Lab := Unit) (0 : Uw) (fun _ _ _ => ())
    (fun _ => (0 : Ul))
  simpa [eq_comm] using this

-- The view type `(Uw × (Fin τ → Uw) × (Fin τ → Ul) × Lab) × O'` needs a larger instance budget.
set_option synthInstance.maxSize 512 in
/-- **With the masked responses.** Let the view also contain `φ p m`, a bijection of separate
uniform masks `m` (the KOS and QuickSilver masks, `Masking.lean`) for every tape `p`; `φ` may
depend on `Θ` and `w`, since the KOS hash covers the label rows. Then the joint count with `Θ` is
still `1` or `0`, independent of `θ`. -/
theorem labelView_responses_theta_card {M O' : Type*} [Fintype M] [DecidableEq O'] (w : Uw)
    (forcedOf : Uw → (Fin τ → Uw) → (Fin τ → Ul) → Lab) (φ : LabelTape Uw Ul τ → M ≃ O')
    (o : Uw × (Fin τ → Uw) × (Fin τ → Ul) × Lab) (o' : O') (θ : Ul) :
    #(univ.filter fun r : LabelTape Uw Ul τ × M =>
        (labelView w forcedOf r.1, φ r.1 r.2) = (o, o') ∧ r.1.2.1 = θ) =
      if LabelConsistent forcedOf o then 1 else 0 := by
  rw [shear_theta_card (labelView w forcedOf) (fun r : LabelTape Uw Ul τ => r.2.1) φ,
    labelView_theta_card]

-- The view type `(Uw × (Fin τ → Uw) × (Fin τ → Ul) × Lab) × O'` needs a larger instance budget.
set_option synthInstance.maxSize 512 in
/-- With the responses, any query offset computed from the full view still hits `Θ` on exactly a
`1/|U_l|` fraction of the tapes. -/
theorem card_query_hits_sibling_responses [Fintype Lab] {M O' : Type*} [Fintype M]
    [DecidableEq O'] [Fintype O']
    (w : Uw) (forcedOf : Uw → (Fin τ → Uw) → (Fin τ → Ul) → Lab) (φ : LabelTape Uw Ul τ → M ≃ O')
    (A : (Uw × (Fin τ → Uw) × (Fin τ → Ul) × Lab) × O' → Ul) :
    #(univ.filter fun r : LabelTape Uw Ul τ × M =>
        A (labelView w forcedOf r.1, φ r.1 r.2) = r.1.2.1) * Fintype.card Ul =
      Fintype.card (LabelTape Uw Ul τ × M) :=
  card_guess_eq (fun r : LabelTape Uw Ul τ × M => (labelView w forcedOf r.1, φ r.1 r.2))
    (fun r => r.1.2.1) (fun oo => if LabelConsistent forcedOf oo.1 then 1 else 0)
    (fun oo θ => labelView_responses_theta_card w forcedOf φ oo.1 oo.2 θ) A

end LabelRows

section SiblingLabelRows

variable {L : Type*} [AddCommGroup L] (h2L : ∀ x : L, x + x = 0)
include h2L

/-- **Patched layout.** With offset `Θ` on the dedicated label rows, the sibling label is the
forced label plus `Θ`: there is no `d + w` term, since the label rows carry no `d`. Compare
`sibling_eq` (unpatched layout). -/
theorem sibling_eq_labelRows (L0 θ : L) (γ : Bool) : sibling L0 θ γ = forced L0 θ γ + θ := by
  cases γ
  · simp [sibling, forced]
  · simp [sibling, forced, add_assoc, h2L]

/-- A query `forced + g` hits the sibling label iff `g = Θ`. Compare `query_hits_sibling_iff`, where
the query tests a guess of `w[0..λ)`; here it tests a guess of the uniform, secret `Θ`. -/
theorem query_hits_sibling_iff_labelRows (L0 θ g : L) (γ : Bool) :
    forced L0 θ γ + g = sibling L0 θ γ ↔ g = θ := by
  rw [sibling_eq_labelRows h2L]
  exact add_left_cancel_iff

end SiblingLabelRows

end VoleMole.ZK
