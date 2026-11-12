import VoleMole.Privacy.Hybrid
import VoleMole.Privacy.Resample

/-!
# Two interleaved readers on one table, and on two tables

`pr_resample` (`Privacy/Resample.lean`) moves **one** adaptive reader to a private table: its
read set must be a function of its own table. In the many-session games the honest sessions are
two groups that **interleave**: the challenge sessions `A` and the further sessions `B` read the
same tables, and what `B` reads later (a redemption, a spend) depends on what the adversary chose
after seeing `A`'s outputs, so `B`'s read set depends on both. This file gives the lemma for that
case.

## The statement

`τ c a b` is the joint run (the transcript) when `A` reads the table `a` and `B` reads the table
`b`; `RA c a b`, `RB c a b` are their read sets. The run is **jointly consistent** (`hJ`): tables
`a'`, `b'` that agree with `a` on `RA c a b` and with `b` on `RB c a b` give the same run and the
same read sets. The real run is `τ c t t`. Then (**`pr_split_le`**)

    | Pr_t[F(τ t t, t)] − Pr_{a,b}[F(τ a b, mix (RB a b) b a)] | ≤ Pr_{a,b}[RA a b ∩ RB a b ≠ ∅],

`mix r b a` the table that is `b` on `r` and `a` elsewhere: in the **split world** `A` runs on
`a`, `B` on the independent `b`, and whoever looks afterwards (the guess) sees `a` patched with
`B`'s view. The bad event is measured in the split world.

## The proof

A bijection between the good sets. From the split world, `(a, b) ↦ (t*, e*) = (mix Q b a,
mix Q a b)` with `Q = RB a b`; if `RA a b` and `Q` are disjoint, `t*` agrees with `a` on `RA` and
with `b` on `Q`, so `τ t* t* = τ a b` with the same read sets (`hJ`): a good real run with the same
transcript and the same patched table. Back, `(t, e) ↦ (mix Q' e t, mix Q' t e)` with
`Q' = RB t t`. The two maps are inverse on the good sets (`hinv`), so the good parts have the same
probability for every event, and the bad parts have the same probability as well.

With `RA = ∅` (an `A` that reads nothing) this is `pr_resample` up to the order of the tables.
-/

open Finset

namespace VoleMole.Privacy

section Split

variable {C T R X : Type*} [Fintype C] [Fintype T] [Nonempty T]
  (mix : R → T → T → T) (Ag : R → T → T → Prop) (Dj : R → R → Prop)
  (hag : ∀ r a b, Ag r a (mix r a b))
  (hinv : ∀ r a b, mix r (mix r a b) (mix r b a) = a)
  (hoff : ∀ r r' a b, Dj r r' → Ag r b (mix r' a b))
  (τ : C → T → T → X) (RA RB : C → T → T → R)
  (hJ : ∀ c a b a' b', Ag (RA c a b) a a' → Ag (RB c a b) b b' →
    τ c a' b' = τ c a b ∧ RA c a' b' = RA c a b ∧ RB c a' b' = RB c a b)

omit [Nonempty T] in
include hag hinv hoff hJ in
/-- **The good parts have the same size**, for every event `H` of the transcript and the table
the guess sees. -/
theorem card_split_good (H : C → X → T → Prop) [DecidablePred fun z : (C × T) × T =>
      H z.1.1 (τ z.1.1 z.1.2 z.1.2) z.1.2 ∧ Dj (RA z.1.1 z.1.2 z.1.2) (RB z.1.1 z.1.2 z.1.2)]
    [DecidablePred fun z : (C × T) × T =>
      H z.1.1 (τ z.1.1 z.1.2 z.2) (mix (RB z.1.1 z.1.2 z.2) z.2 z.1.2) ∧
        Dj (RA z.1.1 z.1.2 z.2) (RB z.1.1 z.1.2 z.2)] :
    #{z : (C × T) × T | H z.1.1 (τ z.1.1 z.1.2 z.2) (mix (RB z.1.1 z.1.2 z.2) z.2 z.1.2) ∧
        Dj (RA z.1.1 z.1.2 z.2) (RB z.1.1 z.1.2 z.2)} =
      #{z : (C × T) × T | H z.1.1 (τ z.1.1 z.1.2 z.1.2) z.1.2 ∧
        Dj (RA z.1.1 z.1.2 z.1.2) (RB z.1.1 z.1.2 z.1.2)} := by
  -- split world → real world
  let φ : (C × T) × T → (C × T) × T := fun z =>
    ((z.1.1, mix (RB z.1.1 z.1.2 z.2) z.2 z.1.2), mix (RB z.1.1 z.1.2 z.2) z.1.2 z.2)
  -- real world → split world
  let ψ : (C × T) × T → (C × T) × T := fun z =>
    ((z.1.1, mix (RB z.1.1 z.1.2 z.1.2) z.2 z.1.2), mix (RB z.1.1 z.1.2 z.1.2) z.1.2 z.2)
  -- the split world's good run, on the combined table
  have hS : ∀ c a b, Dj (RA c a b) (RB c a b) →
      τ c (mix (RB c a b) b a) (mix (RB c a b) b a) = τ c a b ∧
        RA c (mix (RB c a b) b a) (mix (RB c a b) b a) = RA c a b ∧
        RB c (mix (RB c a b) b a) (mix (RB c a b) b a) = RB c a b := fun c a b h =>
    hJ c a b _ _ (hoff _ _ b a h) (hag _ b a)
  -- the real world's good run, on the split tables
  have hR : ∀ c t e, Dj (RA c t t) (RB c t t) →
      τ c (mix (RB c t t) e t) (mix (RB c t t) t e) = τ c t t ∧
        RA c (mix (RB c t t) e t) (mix (RB c t t) t e) = RA c t t ∧
        RB c (mix (RB c t t) e t) (mix (RB c t t) t e) = RB c t t := fun c t e h =>
    hJ c t t _ _ (hoff _ _ e t h) (hag _ t e)
  refine Finset.card_nbij' φ ψ ?_ ?_ ?_ ?_
  · rintro ⟨⟨c, a⟩, b⟩ hz
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hz ⊢
    obtain ⟨hH, hD⟩ := hz
    obtain ⟨e1, e2, e3⟩ := hS c a b hD
    simp only [φ, e1, e2, e3]
    exact ⟨hH, hD⟩
  · rintro ⟨⟨c, t⟩, e⟩ hz
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hz ⊢
    obtain ⟨hH, hD⟩ := hz
    obtain ⟨e1, e2, e3⟩ := hR c t e hD
    simp only [ψ, e1, e2, e3, hinv]
    exact ⟨hH, hD⟩
  · rintro ⟨⟨c, a⟩, b⟩ hz
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hz
    obtain ⟨-, e3⟩ := (hS c a b hz.2).2
    simp only [φ, ψ, e3, hinv]
  · rintro ⟨⟨c, t⟩, e⟩ hz
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hz
    obtain ⟨-, -, e3⟩ := hR c t e hz.2
    simp only [φ, ψ, e3, hinv]

include hag hinv hoff hJ in
/-- **Two interleaved readers, moved to independent tables**: the real run (both on `t`) and the
split run (`A` on `a`, `B` on `b`, the guess on `a` patched with `B`'s view) differ by at most
the probability, in the split world, that their read sets meet. -/
theorem pr_split_le (F : C → X → T → Prop) :
    |pr (C × T) (fun z => F z.1 (τ z.1 z.2 z.2) z.2) -
        pr ((C × T) × T) (fun z => F z.1.1 (τ z.1.1 z.1.2 z.2) (mix (RB z.1.1 z.1.2 z.2) z.2 z.1.2))| ≤
      pr ((C × T) × T) (fun z => ¬ Dj (RA z.1.1 z.1.2 z.2) (RB z.1.1 z.1.2 z.2)) := by
  classical
  set Fr : (C × T) × T → Prop := fun z => F z.1.1 (τ z.1.1 z.1.2 z.1.2) z.1.2
  set Gr : (C × T) × T → Prop := fun z => Dj (RA z.1.1 z.1.2 z.1.2) (RB z.1.1 z.1.2 z.1.2)
  set Fs : (C × T) × T → Prop := fun z =>
    F z.1.1 (τ z.1.1 z.1.2 z.2) (mix (RB z.1.1 z.1.2 z.2) z.2 z.1.2)
  set Gs : (C × T) × T → Prop := fun z => Dj (RA z.1.1 z.1.2 z.2) (RB z.1.1 z.1.2 z.2)
  have h0 : pr (C × T) (fun z => F z.1 (τ z.1 z.2 z.2) z.2) = pr ((C × T) × T) Fr :=
    (pr_prod_fst (β := T) (fun z : C × T => F z.1 (τ z.1 z.2 z.2) z.2)).symm
  have cF := card_split_good mix Ag Dj hag hinv hoff τ RA RB hJ F
  have cT : #(univ.filter Gs) = #(univ.filter Gr) := by
    have := card_split_good mix Ag Dj hag hinv hoff τ RA RB hJ (fun _ _ _ => True)
    simpa only [true_and] using this
  have pF : pr ((C × T) × T) (fun z => Fs z ∧ Gs z) = pr ((C × T) × T) (fun z => Fr z ∧ Gr z) := by
    rw [pr_def, pr_def]
    exact congrArg (fun n : ℕ => (n : ℝ) / _) cF
  have pG : pr ((C × T) × T) (fun z => ¬ Gs z) = pr ((C × T) × T) (fun z => ¬ Gr z) := by
    rw [pr_def, pr_def]
    have e1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset ((C × T) × T))) (p := Gs)
    have e2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset ((C × T) × T))) (p := Gr)
    have : #{z | ¬ Gs z} = #{z | ¬ Gr z} := by omega
    exact congrArg (fun n : ℕ => (n : ℝ) / _) this
  have u1 : pr ((C × T) × T) Fr ≤ pr ((C × T) × T) (fun z => Fr z ∧ Gr z) + pr ((C × T) × T) (fun z => ¬ Gr z) :=
    (pr_mono fun z hz => by
      by_cases hg : Gr z
      · exact Or.inl ⟨hz, hg⟩
      · exact Or.inr hg).trans (pr_or_le _ _)
  have u2 : pr ((C × T) × T) Fs ≤ pr ((C × T) × T) (fun z => Fs z ∧ Gs z) + pr ((C × T) × T) (fun z => ¬ Gs z) :=
    (pr_mono fun z hz => by
      by_cases hg : Gs z
      · exact Or.inl ⟨hz, hg⟩
      · exact Or.inr hg).trans (pr_or_le _ _)
  have l1 : pr ((C × T) × T) (fun z => Fr z ∧ Gr z) ≤ pr ((C × T) × T) Fr := pr_mono fun _ h => h.1
  have l2 : pr ((C × T) × T) (fun z => Fs z ∧ Gs z) ≤ pr ((C × T) × T) Fs := pr_mono fun _ h => h.1
  rw [h0, abs_sub_le_iff]
  constructor <;> linarith

end Split

end VoleMole.Privacy
