import VoleMole.Privacy.SeedXOFGames
import VoleMole.Spec.PomFRIT

/-!
# Lemma DS (c): PomFRIT's seed XOF on the single SHAKE oracle

PomFRIT's seed XOF evaluates SHAKE128 at `"pomf\0s0" ‖ seed ‖ dig(pk) ‖ msg`
(`pomfrit.cpp:150-161`, `Spec.PomFRIT.expandSeed`). Its input set overlaps proof-system domains
(`H₁`, `H₂⁰` of PomFRIT and Ratatouille spend, `H₃`, `H₂¹`, `H₂²`, `H₂³`; finding F-DS2,
`Protocols/DomainSeparation.lean`: `seed_meets_H20_pomfrit`, `seed_meets_H23`), so it cannot be
split off SHAKE as an independent oracle by disjointness (Lemma DS (a), `ROM/DomainSep.lean`).
Lemma DS (c) (`docs/security/domain-separation.md` §7) says it can be split off anyway, except
with a probability that comes from guessing a 256-bit seed. This file proves it in the
random-oracle model, for one SHAKE oracle `H` on a finite input space.

## The model

* **The single oracle** `H : X → Y`, uniform: SHAKE128 as one random function of its input. Every
  party (the adversary, the honest provers, verifiers and simulators, the honest Clients) reads
  `H`.
* **The layout** (`Layout X K Tl Xr`): every input is either a seed-XOF input `xof k t`
  (`DST ‖ k ‖ t`: a seed `k` and a tail `t`) or another one (`Xr`), bijectively. An input of a
  proof-system domain that has the seed-XOF shape is a seed-XOF input: the overlap is *in* `H`.
  `pomfritLayout m`: SHAKE inputs of length `39 + m`, `seedDst ‖ seed(32) ‖ tail(m)`
  (`pomfritLayout_xof`: the string `expandSeed` hashes, with the tail `dig(pk) ‖ msg`).
* **Reads** (`RdXof f q`): `f` reads `H` freely at inputs that are not seed-XOF inputs, and at
  most at `q` seed-XOF inputs (adaptively). This counts *every* evaluation of `H` at a string of
  the seed-XOF shape by anyone but the honest Clients' own XOF calls, including proof-system
  evaluations whose input happens to have that shape.
* **The game** `W H u t`: everything else, reading `H`, with the honest Clients' XOF answers
  `u : ι → Tl → Y` (Client `i`'s answers at every tail) and further coins `t`. In the real game
  `u i t' = H (xof (c i) t')` at uniform seeds `c i`.

## The results

* **`abs_pr_xof_le`**: the real game and the game in which the honest Clients' XOF answers are
  uniform and independent of `H` (the privacy games' G1, `Privacy/SeedXOFGames.lean`) differ by at
  most `Pr[two seeds collide] + δ`, `δ` bounding `Pr[some seed is in a fixed set of q seeds]`.
  Proof: split `H` into the seed-XOF cells (one per seed, a column over the tails) and the rest
  (`Layout.split`); a `q`-bounded reader of `H` reads at most `q` cells (`RdXof.rdX`); then the
  seed-XOF hop `abs_pr_seed_le` with the rest of `H` part of the other coins.
* **`abs_pr_xof_oracle_le`**: the same with the honest answers taken from an **independent oracle**
  `O` at the same seed-XOF inputs (Lemma DS (c) as stated: the seed XOF added to the independent
  oracles of part (a)): `2·Pr[collision] + δ`.
* The seed counting: `n` Clients, `≤ (n·q + n²)·2⁻²⁵⁶` (`seedXofDS_le`, `seedXofDS_oracle_le`:
  `(n·q + 2n²)·2⁻²⁵⁶`); two Clients, `(2q + 1)·2⁻²⁵⁶` (`seedXofDS_two_le`), the seed-XOF hop's term
  of the PomFRIT games.

The paper's `n_seed·Q·2⁻²⁵⁶` has no collision term; here the collisions cost `n²·2⁻²⁵⁶` (an
artifact of programming at distinct points, negligible next to `n·q·2⁻²⁵⁶`).

## What remains

The theorem says the honest Clients' XOF answers may be taken independent of the single SHAKE
oracle. The privacy games of `Privacy/` then draw the proof-system tables (`H₃` slices, `H₂³`,
`H₅`) as independent tables; equating the single oracle `H` (restricted to the proof-system
domains) with those tables is Lemma DS (a)'s step, mechanized for the proof-system domains in
`ROM/DomainSep.lean` but not composed with the privacy games' finite tables. An adversary's own
XOF queries at seed-XOF inputs that also lie in a proof-system domain are, in the single-oracle
model, reads of that domain's table; in `seedGameP` they read the independent XOF table. That
routing is on paper. SHAKE128 as a random oracle stays the modelling step.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.SeedDS

/-! ## The layout of the single oracle's inputs -/

/-- **A layout of the input space** `X` of the single oracle: every input is either a seed-XOF
input with seed `k : K` and tail `t : Tl`, or another input (`Xr`), bijectively. -/
structure Layout (X K Tl Xr : Type*) where
  e : X ≃ (K × Tl) ⊕ Xr

namespace Layout

variable {X K Tl Xr Y : Type*} (L : Layout X K Tl Xr)

/-- The seed-XOF input with seed `k` and tail `t`. -/
def xof (k : K) (t : Tl) : X := L.e.symm (Sum.inl (k, t))

/-- **A table of the single oracle, split** into its seed-XOF cells (one column over the tails per
seed) and the rest. -/
def split : (X → Y) ≃ (K → Tl → Y) × (Xr → Y) :=
  (L.e.arrowCongr (Equiv.refl Y)).trans ((Equiv.sumArrowEquivProdArrow _ _ _).trans
    (Equiv.prodCongr (Equiv.curry _ _ _) (Equiv.refl _)))

@[simp] lemma split_fst (H : X → Y) (k : K) (t : Tl) : (L.split H).1 k t = H (L.xof k t) := rfl

lemma split_symm_apply (g : K → Tl → Y) (h : Xr → Y) (x : X) :
    L.split.symm (g, h) x = Sum.elim (fun p : K × Tl => g p.1 p.2) h (L.e x) := by
  simp only [split, Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.refl_symm, Equiv.coe_refl, Prod.map_apply, id_eq, Equiv.arrowCongr_symm,
    Equiv.arrowCongr_apply, Function.comp_apply, Equiv.symm_symm]
  rcases L.e x with p | r <;> rfl

lemma split_symm_xof (g : K → Tl → Y) (h : Xr → Y) (k : K) (t : Tl) :
    L.split.symm (g, h) (L.xof k t) = g k t := by
  rw [split_symm_apply]
  simp [xof]

/-- **`f` reads the single oracle at most at `q` seed-XOF inputs** (and freely elsewhere): two
tables that agree at every input other than the seed-XOF inputs outside `Q H` give the same value;
`Q H` holds at most `q` (seed, tail) pairs. -/
def RdXof {α : Sort*} (f : (X → Y) → α) (q : ℕ) : Prop :=
  ∃ Q : (X → Y) → Finset (K × Tl), (∀ H, (Q H).card ≤ q) ∧
    ∀ H H' : X → Y, (∀ x, (∀ p, L.e x = Sum.inl p → p ∈ Q H) → H x = H' x) → f H' = f H

/-- A function of the table that does not read it. -/
lemma RdXof.const {α : Sort*} (a : α) : L.RdXof (fun _ : X → Y => a) 0 :=
  ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩

/-- **Reading one seed-XOF input** (for instance a proof-system input of the seed-XOF shape,
F-DS2) costs one read. -/
lemma RdXof.read_xof [DecidableEq K] [DecidableEq Tl] {α : Sort*} (k : K) (t : Tl) (φ : Y → α) :
    L.RdXof (fun H : X → Y => φ (H (L.xof k t))) 1 := by
  refine ⟨fun _ => {(k, t)}, fun _ => (card_singleton _).le, fun H H' h => ?_⟩
  have := h (L.xof k t) fun p hp => by
    rw [xof, Equiv.apply_symm_apply, Sum.inl.injEq] at hp
    rw [← hp]
    exact mem_singleton_self _
  simp only [this]

/-- Reading an input that is not a seed-XOF input is free. -/
lemma RdXof.read_other {α : Sort*} (x : X) (hx : ∀ p, L.e x ≠ Sum.inl p) (φ : Y → α) :
    L.RdXof (fun H : X → Y => φ (H x)) 0 := by
  refine ⟨fun _ => ∅, fun _ => le_rfl, fun H H' h => ?_⟩
  have := h x fun p hp => absurd hp (hx p)
  simp only [this]

/-- **A reader of the single oracle reads at most `q` seed-XOF cells**, the rest of the table
fixed. -/
lemma RdXof.rdX [DecidableEq K] {α : Sort*} {f : (X → Y) → α} {q : ℕ} (hf : L.RdXof f q)
    (h : Xr → Y) : RdX (fun g : K → Tl → Y => f (L.split.symm (g, h))) q := by
  classical
  obtain ⟨Q, hQ, hf⟩ := hf
  refine ⟨fun g => (Q (L.split.symm (g, h))).image Prod.fst,
    fun g => (card_image_le).trans (hQ _), fun g g' hg => ?_⟩
  refine hf _ _ fun x hx => ?_
  rw [split_symm_apply, split_symm_apply]
  rcases hex : L.e x with p | r
  · have hp := hx p hex
    simp only [Sum.elim_inl]
    rw [hg p.1 (mem_image_of_mem _ hp)]
  · rfl

end Layout

/-! ## Lemma DS (c) -/

section Hop

variable {X K Tl Xr Y ι C T : Type*} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
  [Fintype Tl] [DecidableEq Tl] [Fintype Xr] [DecidableEq Xr] [Fintype Y] [Nonempty Y] [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype C]
  [Nonempty C] [Fintype T] [Nonempty T] (L : Layout X K Tl Xr)

/-- The tape regrouped: the single oracle's table split into its seed-XOF cells and the rest, the
rest joined to the other coins. -/
def regroup : (T × (Xr → Y)) × (K → Tl → Y) ≃ T × (X → Y) :=
  ((Equiv.prodAssoc T (Xr → Y) (K → Tl → Y)).trans
    (Equiv.prodCongr (Equiv.refl T) ((Equiv.prodComm _ _).trans L.split.symm)))

lemma regroup_apply (z : (T × (Xr → Y)) × (K → Tl → Y)) :
    regroup (Y := Y) L z = (z.1.1, L.split.symm (z.2, z.1.2)) := rfl

/-- **Lemma DS (c), the hop to independent answers.** Every party but the honest Clients' XOF
calls reads the single oracle `H` at most at `q` seed-XOF inputs (`hW`). The game in which the
Clients' XOF answers are `H` at their seed-XOF inputs (uniform seeds `x c i`) and the game in which
they are uniform and independent of `H` are `Pr[x c not injective] + δ` apart, where `δ` bounds the
probability that a seed lies in a fixed set of `q` seeds. -/
theorem abs_pr_xof_le (x : C → ι → K) (W : (X → Y) → (ι → Tl → Y) → T → Prop) {q : ℕ}
    (hW : ∀ u t, L.RdXof (fun H => W H u t) q) {δ : ℝ}
    (hδ : ∀ F : Finset K, F.card ≤ q → pr C (fun c => ∃ i, x c i ∈ F) ≤ δ) :
    |pr (C × (T × (X → Y))) (fun z => W z.2.2 (fun i t' => z.2.2 (L.xof (x z.1 i) t')) z.2.1) -
        pr (T × ((X → Y) × (ι → Tl → Y))) (fun z => W z.2.1 z.2.2 z.1)| ≤
      pr C (fun c => ¬ Function.Injective (x c)) + δ := by
  have h := abs_pr_seed_le (K := K) (R := Tl → Y) (T := T × (Xr → Y)) x
    (fun g u t => W (L.split.symm (g, t.2)) u t.1)
    (fun u t => (hW u t.1).rdX L t.2) hδ
  have e1 : pr (C × (T × (X → Y))) (fun z =>
      W z.2.2 (fun i t' => z.2.2 (L.xof (x z.1 i) t')) z.2.1) =
      pr (C × ((T × (Xr → Y)) × (K → Tl → Y))) (fun z =>
        W (L.split.symm (z.2.2, z.2.1.2)) (z.2.2 ∘ x z.1) z.2.1.1) := by
    rw [← pr_equiv (Equiv.prodCongr (Equiv.refl C) (regroup L))]
    refine pr_congr fun z => ?_
    simp only [Equiv.prodCongr_apply, Equiv.coe_refl]
    refine iff_of_eq (congrArg₂ (fun u t => W _ u t) ?_ rfl)
    funext i t'
    exact L.split_symm_xof _ _ _ _
  have e2 : pr (T × ((X → Y) × (ι → Tl → Y))) (fun z => W z.2.1 z.2.2 z.1) =
      pr ((T × (Xr → Y)) × ((K → Tl → Y) × (ι → Tl → Y))) (fun z =>
        W (L.split.symm (z.2.1, z.1.2)) z.2.2 z.1.1) := by
    let e : (T × (Xr → Y)) × ((K → Tl → Y) × (ι → Tl → Y)) ≃ T × ((X → Y) × (ι → Tl → Y)) :=
      { toFun := fun z => (z.1.1, (L.split.symm (z.2.1, z.1.2), z.2.2))
        invFun := fun z => ((z.1, (L.split z.2.1).2), ((L.split z.2.1).1, z.2.2))
        left_inv := fun z => by simp
        right_inv := fun z => by simp }
    rw [← pr_equiv e]
    rfl
  rw [e1, e2]
  exact h

/-- Bounds for every first coordinate average to a bound. -/
lemma abs_pr_prod_sub_le_avg {α β β' : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype β']
    (P : α × β → Prop) (Q : α × β' → Prop) (f : α → ℝ)
    (h : ∀ a, |pr β (fun b => P (a, b)) - pr β' (fun b => Q (a, b))| ≤ f a) :
    |pr (α × β) P - pr (α × β') Q| ≤ (∑ a, f a) / Fintype.card α := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, pr_prod, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hα]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => h a)

/-- With an injective seed map the honest answers from an independent oracle `O` are uniform. -/
lemma pr_oracle_eq {c : ι → K} (hc : Function.Injective c) (F : (ι → Tl → Y) → Prop) :
    pr (K → Tl → Y) (fun O => F (O ∘ c)) = pr (ι → Tl → Y) F := by
  have h := close_restrict (R := Tl → Y) hc F
  simp only [id_eq, sub_eq_zero, abs_nonpos_iff] at h
  exact h

/-- **Lemma DS (c) as stated: the seed XOF an independent oracle.** The game in which the honest
Clients' XOF answers are `H` at their seed-XOF inputs and the game in which they are an
independent oracle `O` at the same inputs (`O (x c i) t'`) are `2·Pr[x c not injective] + δ`
apart. -/
theorem abs_pr_xof_oracle_le (x : C → ι → K) (W : (X → Y) → (ι → Tl → Y) → T → Prop) {q : ℕ}
    (hW : ∀ u t, L.RdXof (fun H => W H u t) q) {δ : ℝ}
    (hδ : ∀ F : Finset K, F.card ≤ q → pr C (fun c => ∃ i, x c i ∈ F) ≤ δ) :
    |pr (C × (T × (X → Y))) (fun z => W z.2.2 (fun i t' => z.2.2 (L.xof (x z.1 i) t')) z.2.1) -
        pr (C × ((T × (X → Y)) × (K → Tl → Y))) (fun z => W z.2.1.2 (z.2.2 ∘ x z.1) z.2.1.1)| ≤
      2 * pr C (fun c => ¬ Function.Injective (x c)) + δ := by
  classical
  have h1 := abs_pr_xof_le L x W hW hδ
  set P1 := pr (T × ((X → Y) × (ι → Tl → Y))) (fun z => W z.2.1 z.2.2 z.1) with hP1
  -- The independent oracle against independent answers: equal for injective seeds.
  have h2 : |pr (C × ((T × (X → Y)) × (K → Tl → Y))) (fun z => W z.2.1.2 (z.2.2 ∘ x z.1) z.2.1.1) -
      pr (C × (T × ((X → Y) × (ι → Tl → Y)))) (fun z => W z.2.2.1 z.2.2.2 z.2.1)| ≤
      (∑ c, if ¬ Function.Injective (x c) then (1 : ℝ) else 0) / Fintype.card C := by
    refine abs_pr_prod_sub_le_avg _ _ _ fun c => ?_
    by_cases hc : Function.Injective (x c)
    · have e : pr ((T × (X → Y)) × (K → Tl → Y)) (fun z => W z.1.2 (z.2 ∘ x c) z.1.1) =
          pr (T × ((X → Y) × (ι → Tl → Y))) (fun z => W z.2.1 z.2.2 z.1) := by
        rw [pr_prod]
        let e' : T × ((X → Y) × (ι → Tl → Y)) ≃ (T × (X → Y)) × (ι → Tl → Y) :=
          (Equiv.prodAssoc _ _ _).symm
        rw [← pr_equiv e'.symm, pr_prod]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        exact pr_oracle_eq hc (fun u => W a.2 u a.1)
      simp only [hc, not_true_eq_false, ↓reduceIte]
      rw [e, sub_self, abs_zero]
    · simp only [hc, not_false_eq_true, ↓reduceIte]
      have := pr_le_one (fun z : (T × (X → Y)) × (K → Tl → Y) => W z.1.2 (z.2 ∘ x c) z.1.1)
      have := pr_nonneg (fun z : (T × (X → Y)) × (K → Tl → Y) => W z.1.2 (z.2 ∘ x c) z.1.1)
      have := pr_le_one (fun z : T × ((X → Y) × (ι → Tl → Y)) => W z.2.1 z.2.2 z.1)
      have := pr_nonneg (fun z : T × ((X → Y) × (ι → Tl → Y)) => W z.2.1 z.2.2 z.1)
      rw [abs_sub_le_iff]
      constructor <;> linarith
  have hnb : (∑ c, if ¬ Function.Injective (x c) then (1 : ℝ) else 0) / Fintype.card C =
      pr C (fun c => ¬ Function.Injective (x c)) := by
    rw [pr_def, Finset.sum_boole]
  have hP : pr (C × (T × ((X → Y) × (ι → Tl → Y)))) (fun z => W z.2.2.1 z.2.2.2 z.2.1) = P1 :=
    pr_prod_snd (α := C) (fun z : T × ((X → Y) × (ι → Tl → Y)) => W z.2.1 z.2.2 z.1)
  rw [hnb, hP] at h2
  have := abs_sub_le (pr (C × (T × (X → Y))) (fun z =>
      W z.2.2 (fun i t' => z.2.2 (L.xof (x z.1 i) t')) z.2.1)) P1
    (pr (C × ((T × (X → Y)) × (K → Tl → Y))) (fun z => W z.2.1.2 (z.2.2 ∘ x z.1) z.2.1.1))
  rw [abs_sub_comm P1] at this
  linarith

end Hop

/-! ## Counting seeds -/

section Seeds

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

/-- `n` uniform seeds meet a fixed set of `q` seeds with probability `≤ n·q / |S|`. -/
theorem pr_exists_mem_le (F : Finset S) {q : ℕ} (hF : F.card ≤ q) :
    pr (ι → S) (fun c => ∃ i, c i ∈ F) ≤ Fintype.card ι * q / Fintype.card S := by
  refine (pr_exists_le_sum _).trans ?_
  have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  calc ∑ i, pr (ι → S) (fun c => c i ∈ F) ≤ ∑ _i : ι, (q : ℝ) / Fintype.card S :=
        Finset.sum_le_sum fun i _ => (pr_coord_mem_le i F).trans (by gcongr)
    _ = Fintype.card ι * q / Fintype.card S := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc]

/-- `n` uniform seeds collide with probability `≤ n² / |S|`. -/
theorem pr_not_injective_le :
    pr (ι → S) (fun c => ¬ Function.Injective c) ≤ (Fintype.card ι) ^ 2 / Fintype.card S := by
  classical
  refine (pr_mono (Q := fun c => ∃ p : ι × ι, p.1 ≠ p.2 ∧ c p.1 = c p.2) fun c hc => ?_).trans ?_
  · by_contra h
    refine hc fun a b hab => ?_
    by_contra hne
    exact h ⟨(a, b), hne, hab⟩
  · refine (pr_exists_le_sum _).trans ?_
    calc ∑ p : ι × ι, pr (ι → S) (fun c => p.1 ≠ p.2 ∧ c p.1 = c p.2)
        ≤ ∑ _p : ι × ι, (1 : ℝ) / Fintype.card S := Finset.sum_le_sum fun p _ => by
          by_cases hp : p.1 = p.2
          · rw [pr_congr (Q := fun _ => False) fun c => by simp [hp], pr_const]
            positivity
          · exact (pr_mono fun c hc => hc.2).trans (pr_coord_eq_le hp)
      _ = (Fintype.card ι) ^ 2 / Fintype.card S := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
          push_cast
          ring

end Seeds

/-! ## PomFRIT's seed XOF on SHAKE inputs -/

section PomFRIT

open VoleMole.Spec.PomFRIT

/-- SHAKE inputs of length `n`. -/
abbrev Str (n : ℕ) := List.Vector UInt8 n

/-- A 32-byte seed. -/
abbrev Seed := List.Vector UInt8 32

lemma seedDst_length : seedDst.length = 7 := rfl

lemma card_seed : (Fintype.card Seed : ℝ) = 2 ^ 256 := by
  rw [card_vector, Prob.card_uint8]
  norm_num

/-- **The seed-XOF input** `seedDst ‖ seed ‖ tail` of length `39 + m`. -/
def xofIn (m : ℕ) (c : Seed) (t : Str m) : Str (39 + m) :=
  ⟨seedDst ++ c.1 ++ t.1, by simp [seedDst_length, c.2, t.2]; omega⟩

/-- The other inputs of length `39 + m`: those that do not start with `seedDst`. -/
abbrev Other (m : ℕ) := {x : Str (39 + m) // x.1.take 7 ≠ seedDst}

lemma take_xofIn (m : ℕ) (c : Seed) (t : Str m) : (xofIn m c t).1.take 7 = seedDst := by
  show List.take 7 (seedDst ++ c.1 ++ t.1) = seedDst
  rw [List.append_assoc, List.take_left' seedDst_length]

lemma drop_xofIn (m : ℕ) (c : Seed) (t : Str m) : (xofIn m c t).1.drop 7 = c.1 ++ t.1 := by
  show List.drop 7 (seedDst ++ c.1 ++ t.1) = c.1 ++ t.1
  rw [List.append_assoc, List.drop_left' seedDst_length]

/-- **The layout of SHAKE inputs of length `39 + m`**: an input starting with `seedDst` is the
seed-XOF input of its next `32` bytes (the seed) and the rest (the tail `dig(pk) ‖ msg`). -/
def pomfritLayout (m : ℕ) : Layout (Str (39 + m)) Seed (Str m) (Other m) where
  e :=
    { toFun := fun x => if h : x.1.take 7 = seedDst then
          Sum.inl (⟨(x.1.drop 7).take 32, by simp [x.2]; omega⟩, ⟨x.1.drop 39, by simp [x.2]⟩)
        else Sum.inr ⟨x, h⟩
      invFun := fun s => match s with
        | Sum.inl p => xofIn m p.1 p.2
        | Sum.inr x => x.1
      left_inv := fun x => by
        by_cases h : x.1.take 7 = seedDst
        · simp only [h, ↓reduceDIte]
          apply Subtype.ext
          show seedDst ++ (x.1.drop 7).take 32 ++ x.1.drop 39 = x.1
          rw [← h, List.append_assoc, show x.1.drop 39 = (x.1.drop 7).drop 32 by
            rw [List.drop_drop], List.take_append_drop, List.take_append_drop]
        · simp only [h, ↓reduceDIte]
      right_inv := fun s => by
        rcases s with ⟨c, t⟩ | x
        · simp only [take_xofIn, ↓reduceDIte, Sum.inl.injEq]
          refine Prod.ext ?_ ?_
          · apply Subtype.ext
            show ((xofIn m c t).1.drop 7).take 32 = c.1
            rw [drop_xofIn, List.take_append_of_le_length (by rw [c.2])]
            simp [c.2]
          · apply Subtype.ext
            show (xofIn m c t).1.drop 39 = t.1
            have e : (xofIn m c t).1.drop 39 = ((xofIn m c t).1.drop 7).drop 32 := by
              rw [List.drop_drop]
            rw [e, drop_xofIn,
              List.drop_append_of_le_length (by rw [c.2])]
            simp [c.2]
        · simp only [x.2, ↓reduceDIte] }

/-- **The layout's seed-XOF input is the string `expandSeed` hashes**: `seedDst ‖ seed ‖ tail`
(with the tail `dig(pk) ‖ msg`, `Spec.PomFRIT.expandSeed`). -/
theorem pomfritLayout_xof (m : ℕ) (c : Seed) (t : Str m) :
    ((pomfritLayout m).xof c t).1 = seedDst ++ c.1 ++ t.1 := rfl

variable {m : ℕ} {Y ι T : Type*} [Fintype Y] [Nonempty Y] [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype T] [Nonempty T]

/-- **Lemma DS (c) for PomFRIT's seed XOF, `n` Clients** (the hop to independent uniform answers):
every other party reads SHAKE at most at `q` inputs of the seed-XOF shape; the honest Clients'
XOF answers can be taken uniform and independent of SHAKE at a cost `≤ (n·q + n²)·2⁻²⁵⁶`. -/
theorem seedXofDS_le (W : (Str (39 + m) → Y) → (ι → Str m → Y) → T → Prop) {q : ℕ}
    (hW : ∀ u t, (pomfritLayout m).RdXof (fun H => W H u t) q) :
    |pr ((ι → Seed) × (T × (Str (39 + m) → Y))) (fun z =>
        W z.2.2 (fun i t' => z.2.2 ((pomfritLayout m).xof (z.1 i) t')) z.2.1) -
      pr (T × ((Str (39 + m) → Y) × (ι → Str m → Y))) (fun z => W z.2.1 z.2.2 z.1)| ≤
      (Fintype.card ι * q + (Fintype.card ι) ^ 2) / 2 ^ 256 := by
  have h := abs_pr_xof_le (pomfritLayout m) (fun c => c) W hW
    (δ := Fintype.card ι * q / Fintype.card Seed) fun F hF => pr_exists_mem_le F hF
  have hc := pr_not_injective_le (ι := ι) (S := Seed)
  rw [card_seed] at h hc
  refine h.trans ?_
  rw [add_div]
  linarith

/-- **Lemma DS (c) for PomFRIT's seed XOF, the seed XOF an independent oracle, `n` Clients**:
`≤ (n·q + 2n²)·2⁻²⁵⁶`. -/
theorem seedXofDS_oracle_le (W : (Str (39 + m) → Y) → (ι → Str m → Y) → T → Prop) {q : ℕ}
    (hW : ∀ u t, (pomfritLayout m).RdXof (fun H => W H u t) q) :
    |pr ((ι → Seed) × (T × (Str (39 + m) → Y))) (fun z =>
        W z.2.2 (fun i t' => z.2.2 ((pomfritLayout m).xof (z.1 i) t')) z.2.1) -
      pr ((ι → Seed) × ((T × (Str (39 + m) → Y)) × (Seed → Str m → Y))) (fun z =>
        W z.2.1.2 (z.2.2 ∘ z.1) z.2.1.1)| ≤
      (Fintype.card ι * q + 2 * (Fintype.card ι) ^ 2) / 2 ^ 256 := by
  have h := abs_pr_xof_oracle_le (pomfritLayout m) (fun c => c) W hW
    (δ := Fintype.card ι * q / Fintype.card Seed) fun F hF => pr_exists_mem_le F hF
  have hc := pr_not_injective_le (ι := ι) (S := Seed)
  rw [card_seed] at h hc
  refine h.trans ?_
  rw [add_div, mul_div_assoc]
  linarith

/-- **Two Clients** (the PomFRIT games' two sessions): `≤ (2q + 1)·2⁻²⁵⁶`, the seed-XOF hop's term
of `Privacy/SeedXOFGames.lean`, now with every party reading the single SHAKE oracle. -/
theorem seedXofDS_two_le (W : (Str (39 + m) → Y) → (Bool → Str m → Y) → T → Prop) {q : ℕ}
    (hW : ∀ u t, (pomfritLayout m).RdXof (fun H => W H u t) q) :
    |pr ((Bool → Seed) × (T × (Str (39 + m) → Y))) (fun z =>
        W z.2.2 (fun i t' => z.2.2 ((pomfritLayout m).xof (z.1 i) t')) z.2.1) -
      pr (T × ((Str (39 + m) → Y) × (Bool → Str m → Y))) (fun z => W z.2.1 z.2.2 z.1)| ≤
      (2 * q + 1 : ℕ) / 2 ^ 256 := by
  have h := abs_pr_xof_le (pomfritLayout m) (fun c => c) W hW
    (δ := 2 * q / Fintype.card Seed) fun F hF => pr_bool_exists_mem_le F hF
  have hc := pr_bool_not_injective_le (S := Seed)
  rw [card_seed] at h hc
  refine h.trans ?_
  push_cast
  rw [add_div]
  linarith

end PomFRIT

end VoleMole.Privacy.SeedDS
