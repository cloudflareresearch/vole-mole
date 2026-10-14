import VoleMole.ZK.Masking

/-!
# Zero knowledge: the grinding distribution (`lean/docs/zk.md`, hybrid H2)

`grind_and_open` (faest-arch-opt `vector_com.inc:982-1066`) hashes
`chal2 ‖ qs_check ‖ qs_proof ‖ ctr` for `ctr = 0, 1, 2, …` and stops at the first output `Δ` that
lies in the acceptance set `A`: the top `w_grind` bits of `Δ` are zero, and the BAVC opening at `Δ`
succeeds. Whether the opening succeeds depends only on `Δ`: `one_tree_bavc::open`
(`vector_com.inc:777-853`, line 818) counts the hidden nodes from `Δ` alone. So `A` is a fixed set.

With the hash outputs modelled as an i.i.d. uniform sequence `f : Fin N → Ω` (`N = 2³²`), the
prover's output `(ctr, Δ)` is the first hit of `f` in `A`. `card_isFirstHit` counts the sequences
whose first hit is `(n, x)`: `|Aᶜ|ⁿ · |Ω|^(N-1-n)` if `x ∈ A`, else `0`. This depends only on
`(|A|, |Ω|, n, N)`. So the counter is geometric, `Δ` is uniform on `A` and independent of the
counter, and the simulator can sample `(ctr, Δ)` directly, programming the outputs at counters
`< ctr` with uniform elements of `Aᶜ`. `card_noHit` is the abort event (counter overflow).
-/

open Finset

namespace VoleMole.ZK

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (A : Finset Ω) {N : ℕ}

/-- `(n, x)` is the first hit of the sequence `f` in `A`: no earlier element is in `A`,
`f n = x`, and `x ∈ A`. This is the `(counter, Δ)` that `grind_and_open` returns. -/
def IsFirstHit (f : Fin N → Ω) (n : Fin N) (x : Ω) : Prop :=
  (∀ i : Fin N, i < n → f i ∉ A) ∧ f n = x ∧ x ∈ A

instance (f : Fin N → Ω) (n : Fin N) (x : Ω) : Decidable (IsFirstHit A f n x) := by
  unfold IsFirstHit; infer_instance

omit [Fintype Ω] [DecidableEq Ω] in
/-- The first hit is unique, so the prover's output is a function of the hash outputs. -/
theorem isFirstHit_unique {f : Fin N → Ω} {n n' : Fin N} {x x' : Ω} (h : IsFirstHit A f n x)
    (h' : IsFirstHit A f n' x') : n = n' ∧ x = x' := by
  obtain ⟨hlt, hfx, hx⟩ := h
  obtain ⟨hlt', hfx', hx'⟩ := h'
  have hn : n = n' := by
    rcases lt_trichotomy n n' with hl | he | hg
    · exact absurd (hfx ▸ hx) (hlt' n hl)
    · exact he
    · exact absurd (hfx' ▸ hx') (hlt n' hg)
  subst hn
  exact ⟨rfl, hfx.symm.trans hfx'⟩

/-- The per-position constraint sets of a first hit at `(n, x)`. -/
def hitSets (n : Fin N) (x : Ω) (i : Fin N) : Finset Ω :=
  if i < n then Aᶜ else if i = n then {x} else univ

theorem isFirstHit_iff_mem_piFinset (f : Fin N → Ω) (n : Fin N) (x : Ω) (hx : x ∈ A) :
    IsFirstHit A f n x ↔ f ∈ Fintype.piFinset (hitSets A n x) := by
  simp only [IsFirstHit, Fintype.mem_piFinset, hitSets]
  constructor
  · rintro ⟨hlt, hfx, -⟩ i
    by_cases hi : i < n
    · simpa [hi] using hlt i hi
    · by_cases hin : i = n
      · subst hin; simp [hfx]
      · simp [hi, hin]
  · intro h
    refine ⟨fun i hi => by simpa [hi] using h i, by simpa using h n, hx⟩

/-- **Grinding distribution.** The number of hash-output sequences whose first hit in `A` is at
counter `n` with value `x ∈ A` is `|Aᶜ|ⁿ · |Ω|^(N-1-n)`. It does not depend on `x`, nor on anything
but the sizes. -/
theorem card_isFirstHit (n : Fin N) (x : Ω) (hx : x ∈ A) :
    #(univ.filter fun f : Fin N → Ω => IsFirstHit A f n x) =
      (#Aᶜ) ^ (n : ℕ) * (Fintype.card Ω) ^ (N - 1 - n) := by
  have hset : (univ.filter fun f : Fin N → Ω => IsFirstHit A f n x) =
      Fintype.piFinset (hitSets A n x) := by
    ext f
    simp [isFirstHit_iff_mem_piFinset A f n x hx]
  rw [hset, Fintype.card_piFinset]
  simp only [hitSets]
  have hcard : ∀ i : Fin N, #(if i < n then Aᶜ else if i = n then ({x} : Finset Ω) else univ) =
      if i < n then #Aᶜ else if i = n then 1 else Fintype.card Ω := by
    intro i
    split_ifs <;> simp
  simp_rw [hcard]
  rw [Finset.prod_ite, Finset.prod_ite]
  simp only [Finset.prod_const, Finset.filter_filter]
  have h1 : (univ.filter fun i : Fin N => i < n) = Iio n := by ext; simp
  have h2 : (univ.filter fun i : Fin N => ¬i < n ∧ ¬i = n) = Ioi n := by
    ext i; simp only [mem_filter, mem_univ, true_and, mem_Ioi]; omega
  rw [h1, h2, Fin.card_Iio, Fin.card_Ioi, one_pow, one_mul]

/-- A value outside `A` is never a first hit. -/
theorem card_isFirstHit_of_not_mem (n : Fin N) (x : Ω) (hx : x ∉ A) :
    #(univ.filter fun f : Fin N → Ω => IsFirstHit A f n x) = 0 := by
  simp [IsFirstHit, hx]

/-- The abort event: no hit within `N` counters. -/
theorem card_noHit :
    #(univ.filter fun f : Fin N → Ω => ∀ i, f i ∉ A) = (#Aᶜ) ^ N := by
  have : (univ.filter fun f : Fin N → Ω => ∀ i, f i ∉ A) = Fintype.piFinset fun _ => Aᶜ := by
    ext f; simp
  rw [this, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Conditioned on the counter, `Δ` is uniform on `A`: any two accepted values are equally likely.
-/
theorem isFirstHit_uniform_on_A (n : Fin N) (x x' : Ω) (hx : x ∈ A) (hx' : x' ∈ A) :
    #(univ.filter fun f : Fin N → Ω => IsFirstHit A f n x) =
      #(univ.filter fun f : Fin N → Ω => IsFirstHit A f n x') := by
  rw [card_isFirstHit A n x hx, card_isFirstHit A n x' hx']

end VoleMole.ZK
