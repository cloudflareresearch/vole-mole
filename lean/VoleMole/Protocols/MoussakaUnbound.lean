import Mathlib
import VoleMole.Protocols.Moussaka

/-!
# Unbound Moussaka: cores of the security proofs (`lean/docs/security/moussaka-unbound.md`)

Unbound tokens (`UnboundToken`, PR #63) commit to a nullifier key `k` instead of a nullifier and a
redemption context: `t = UCom(k, ctx_iss, r)`, and a redemption in context `c` reveals
`nf = Derive(k, c)`. The facts below are the deterministic and finite steps of the note's
arguments. `Derive`, `UCom` and the bound `Com` are arbitrary functions here; binding enters as an
injectivity hypothesis on the inputs the extractor returns.

* Theorem U1 (one-more unforgeability per redemption context), steps 4:
  `key_injOn_of_nf`, `input_injOn_of_nf`, `t_injOn_of_derive`: one accepted redemption per distinct
  nullifier in one context gives distinct keys, distinct commitment inputs and (under binding)
  distinct commitments; `exists_unsigned_per_context`: if there are more of them than unbound
  issuances for the issuance context, some redemption's commitment was never signed, by either
  variant and for any issuance context; `count_le_per_variant`: the contrapositive count.
* Corollary U2: `nf_determined` (a signed commitment and a context determine the nullifier).
* Proposition U3: `squat_cases` (a squatter's key is the honest key or a second preimage).
* Theorem U5, step 4: `swap_invariant`: answering each query `(i, c)` with `F (i ⊕ W c) c` instead
  of `F i c` does not change the distribution of anything computed from the oracle, for uniform
  `F : Bool → C → Y` and any fixed swap pattern `W`; `ideal_worlds_eq`; and the assembly
  `anonymity_unbound` from the zero-knowledge and PRF hops.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.MoussakaUnbound

/-! ## Theorem U1: unforgeability per redemption context -/

section OneMore

variable {ρ κ ι τ γ ν : Type*}

/-- One accepted redemption per distinct nullifier, all in one redemption context `c`, have
pairwise distinct extracted keys: `Derive` is a function. -/
theorem key_injOn_of_nf (R : Finset ρ) (k : ρ → κ) (D : κ → ν)
    (hnf : Set.InjOn (fun j => D (k j)) R) : Set.InjOn k R := fun _ hj _ hj' h =>
  hnf hj hj' (by simp only [h])

/-- The extracted commitment inputs are then pairwise distinct, since each contains its key
(`keyOf`, the `nf_key` field of the `UCom` input). -/
theorem input_injOn_of_nf (R : Finset ρ) (k : ρ → κ) (x : ρ → ι) (keyOf : ι → κ)
    (hkey : ∀ j ∈ R, keyOf (x j) = k j) (D : κ → ν)
    (hnf : Set.InjOn (fun j => D (k j)) R) : Set.InjOn x R := fun j hj j' hj' h => by
  apply key_injOn_of_nf R k D hnf hj hj'
  rw [← hkey j hj, ← hkey j' hj', h]

/-- **Distinct nullifiers in one context, distinct commitments** (Thm U1, step 4, first bullet):
under binding (`f` injective on the extracted inputs), `j ↦ t_j = f (x j)` is injective. -/
theorem t_injOn_of_derive (R : Finset ρ) (k : ρ → κ) (x : ρ → ι) (keyOf : ι → κ)
    (hkey : ∀ j ∈ R, keyOf (x j) = k j) (f : ι → τ) (hbind : Set.InjOn f (x '' R))
    (D : κ → ν) (hnf : Set.InjOn (fun j => D (k j)) R) :
    Set.InjOn (fun j => f (x j)) R := fun j hj j' hj' h =>
  input_injOn_of_nf R k x keyOf hkey D hnf hj hj'
    (hbind ⟨j, hj, rfl⟩ ⟨j', hj', rfl⟩ h)

/-- **Some commitment was never signed** (Thm U1, step 4). The data, all as the extractor returns
them at the end of the run:

* `R`: one accepted unbound redemption per distinct nullifier for `(ctx_iss*, ctx_red*)`, with
  extracted key `k j`, `UCom` input `x j` (with key field `keyOf (x j) = k j` and issuance context
  `ctxOf (x j) = c`), and nullifier `D (k j)` (`D = Derive(·, ctx_red*)`);
* `Iu`, `Ib`: the extracted inputs of every accepted unbound and bound issuance, for any issuance
  context; `ctxOf` reads the issuance context of an input;
* `hdisj`: no redemption input is a bound input (the input spaces differ in the DST byte,
  `Arith.MoussakaUnbound.encodeUnboundComState_ne_encodeComState`);
* `hbind`: joint binding, `f` injective on all of these inputs together.

If there are more redemptions than unbound issuances for `c`, some redemption's commitment
`f (x j)` is not the commitment of any issuance, of either variant, for any context: a CT-UF^open
forgery. -/
theorem exists_unsigned_per_context [DecidableEq ι] [DecidableEq γ] (R : Finset ρ) (k : ρ → κ)
    (x : ρ → ι) (keyOf : ι → κ) (ctxOf : ι → γ) (c : γ) (D : κ → ν) (f : ι → τ)
    (Iu Ib : Finset ι)
    (hkey : ∀ j ∈ R, keyOf (x j) = k j) (hctx : ∀ j ∈ R, ctxOf (x j) = c)
    (hnf : Set.InjOn (fun j => D (k j)) R)
    (hdisj : ∀ j ∈ R, x j ∉ Ib)
    (hbind : Set.InjOn f (↑(Iu ∪ Ib) ∪ x '' R))
    (hlt : (Iu.filter fun y => ctxOf y = c).card < R.card) :
    ∃ j ∈ R, ∀ y ∈ Iu ∪ Ib, f y ≠ f (x j) := by
  have hx := input_injOn_of_nf R k x keyOf hkey D hnf
  obtain ⟨j, hj, hjn⟩ := VoleMole.Moussaka.exists_unsigned_of_card_lt R _ x hx hlt
  refine ⟨j, hj, fun y hy hfy => ?_⟩
  have hxy : y = x j := hbind (Or.inl hy) (Or.inr ⟨j, hj, rfl⟩) hfy
  rcases Finset.mem_union.1 hy with hu | hb
  · exact hjn (Finset.mem_filter.2 ⟨hxy ▸ hu, hxy ▸ hctx j hj⟩)
  · exact hdisj j hj (hxy ▸ hb)

/-- **The count** (Thm U1, contrapositive): if every redemption's commitment is the commitment of
some issuance (no forgery), the accepted distinct nullifiers for `(ctx_iss*, ctx_red*)` are at
most the unbound issuances for `ctx_iss*`. Bound issuances do not count. -/
theorem count_le_per_variant [DecidableEq ι] [DecidableEq γ] (R : Finset ρ) (k : ρ → κ)
    (x : ρ → ι) (keyOf : ι → κ) (ctxOf : ι → γ) (c : γ) (D : κ → ν) (f : ι → τ)
    (Iu Ib : Finset ι)
    (hkey : ∀ j ∈ R, keyOf (x j) = k j) (hctx : ∀ j ∈ R, ctxOf (x j) = c)
    (hnf : Set.InjOn (fun j => D (k j)) R)
    (hdisj : ∀ j ∈ R, x j ∉ Ib)
    (hbind : Set.InjOn f (↑(Iu ∪ Ib) ∪ x '' R))
    (hsigned : ∀ j ∈ R, ∃ y ∈ Iu ∪ Ib, f y = f (x j)) :
    R.card ≤ (Iu.filter fun y => ctxOf y = c).card := by
  by_contra h
  obtain ⟨j, hj, hne⟩ := exists_unsigned_per_context R k x keyOf ctxOf c D f Iu Ib hkey hctx hnf
    hdisj hbind (Nat.lt_of_not_le h)
  obtain ⟨y, hy, hfy⟩ := hsigned j hj
  exact hne y hy hfy

end OneMore

/-! ## Corollary U2 and Proposition U3 -/

section Nullifiers

variable {ι κ τ γ ν : Type*}

/-- **A signed commitment and a context determine the nullifier** (Cor U2.1): two openings of one
commitment (binding: equal inputs) have the same key, so the same nullifier in every context. -/
theorem nf_determined (f : ι → τ) (keyOf : ι → κ) (Derive : κ → γ → ν) {x x' : ι}
    (hbind : f x = f x' → x = x') (h : f x = f x') (c : γ) :
    Derive (keyOf x) c = Derive (keyOf x') c := by
  rw [hbind h]

/-- A second preimage of `nf = Derive(k, c)` in the key. -/
def SecondPreimage (Derive : κ → γ → ν) (c : γ) (k k' : κ) : Prop :=
  k' ≠ k ∧ Derive k' c = Derive k c

/-- **Squatting** (Prop U3): an accepted redemption carrying the honest nullifier `Derive(k, c)`
whose extracted key is `k'` either has the honest key (key recovery) or is a second preimage. -/
theorem squat_cases (Derive : κ → γ → ν) (c : γ) (k k' : κ)
    (hnf : Derive k' c = Derive k c) : k' = k ∨ SecondPreimage Derive c k k' := by
  by_cases h : k' = k
  · exact Or.inl h
  · exact Or.inr ⟨h, hnf⟩

end Nullifiers

/-! ## Theorem U5, step 4: the ideal worlds coincide -/

section Swap

variable {C Y : Type*} [Fintype C] [DecidableEq C] [Fintype Y] [DecidableEq Y]

/-- Answer query `(i, c)` from token `i ⊕ W c` instead of token `i`. -/
def swapW (W : C → Bool) (F : Bool → C → Y) : Bool → C → Y := fun i c => F (xor i (W c)) c

theorem swapW_swapW (W : C → Bool) (F : Bool → C → Y) : swapW W (swapW W F) = F := by
  funext i c
  simp [swapW]

/-- `swapW W` is an involution on pairs of functions, hence a permutation. -/
def swapEquiv (W : C → Bool) : (Bool → C → Y) ≃ (Bool → C → Y) where
  toFun := swapW W
  invFun := swapW W
  left_inv := swapW_swapW W
  right_inv := swapW_swapW W

/-- The oracle of world `b`: query `(i, c)` is answered by token `i ⊕ (b ∧ W c)`. In world `false`
every query is answered by token `i`; in world `true`, the queries in contexts with `W c` are
answered by the other token. -/
def worldOracle (W : C → Bool) (b : Bool) (F : Bool → C → Y) : Bool → C → Y :=
  fun i c => F (xor i (b && W c)) c

theorem worldOracle_false (W : C → Bool) (F : Bool → C → Y) : worldOracle W false F = F := by
  funext i c; simp [worldOracle]

theorem worldOracle_true (W : C → Bool) (F : Bool → C → Y) :
    worldOracle W true F = swapW W F := by
  funext i c; simp [worldOracle, swapW]

/-- **Swap invariance.** For any statistic `g` of the oracle (in an additive monoid), the sum over
all pairs of functions `F` is the same whether the oracle is `F` or `swapW W F`. -/
theorem swap_invariant {M : Type*} [AddCommMonoid M] (W : C → Bool) (g : (Bool → C → Y) → M) :
    ∑ F, g (swapW W F) = ∑ F, g F :=
  Equiv.sum_comp (swapEquiv W) g

/-- **The ideal worlds coincide** (Thm U5, step 4). `A` is any deterministic adversary given as a
function of the whole oracle (an adaptive strategy's output is such a function); `ideal b A` is
the number of `F` (uniform pairs of random functions) on which `A` accepts in world `b`. It does
not depend on `b`. -/
def ideal (W : C → Bool) (A : (Bool → C → Y) → Bool) (b : Bool) : ℕ :=
  (univ.filter fun F => A (worldOracle W b F) = true).card

theorem ideal_worlds_eq (W : C → Bool) (A : (Bool → C → Y) → Bool) :
    ideal W A true = ideal W A false := by
  unfold ideal
  simp only [worldOracle_true, worldOracle_false, Finset.card_filter]
  exact swap_invariant W fun F => if A F = true then 1 else 0

/-- The same with the adversary's own coins `ω` (any finite type) and the probability over
`(ω, F)` uniform. -/
theorem ideal_worlds_eq_coins {Ω : Type*} [Fintype Ω] (W : C → Bool)
    (A : Ω → (Bool → C → Y) → Bool) :
    (univ.filter fun p : Ω × (Bool → C → Y) => A p.1 (worldOracle W true p.2) = true).card =
      (univ.filter fun p : Ω × (Bool → C → Y) => A p.1 (worldOracle W false p.2) = true).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [worldOracle_true, worldOracle_false]
  exact swap_invariant W fun F => if A ω F = true then 1 else 0

/-- The probability that `A` accepts in ideal world `b`. -/
noncomputable def idealProb (W : C → Bool) (A : (Bool → C → Y) → Bool) (b : Bool) : ℝ :=
  (ideal W A b : ℝ) / Fintype.card (Bool → C → Y)

/-- **Theorem U5 from its hops.** `real b`, `sim b` are the probabilities that the adversary
accepts in world `b` with real proofs and with simulated proofs; the PRF hop replaces the honest
keys' `Derive` by the uniform functions of `idealProb`. With the zero-knowledge hop `≤ εZK` and
the PRF hop `≤ εPRF` in each world, the advantage is at most `2·εZK + 2·εPRF`. -/
theorem anonymity_unbound (W : C → Bool) (A : (Bool → C → Y) → Bool) (real sim : Bool → ℝ)
    (εZK εPRF : ℝ) (hzk : ∀ b, |real b - sim b| ≤ εZK)
    (hprf : ∀ b, |sim b - idealProb W A b| ≤ εPRF) :
    |real true - real false| ≤ 2 * εZK + 2 * εPRF := by
  have he : idealProb W A true = idealProb W A false := by
    simp only [idealProb, ideal_worlds_eq W A]
  set I := idealProb W A false
  have h1 := hzk true
  have h2 : |sim false - real false| ≤ εZK := by rw [abs_sub_comm]; exact hzk false
  have h3 : |sim true - I| ≤ εPRF := he ▸ hprf true
  have h4 : |I - sim false| ≤ εPRF := by rw [abs_sub_comm]; exact hprf false
  have t1 := abs_sub_le (real true) (sim true) (real false)
  have t2 := abs_sub_le (sim true) I (real false)
  have t3 := abs_sub_le I (sim false) (real false)
  linarith

end Swap

/-! ## Why the context rule is needed -/

/-- Without the context rule the worlds differ: if one context is queried with both swap flags,
the adversary that compares the two answers wins outright whenever the two tokens' values in that
context differ. Here: two queries to token `false` in context `c`, one with flag `false` and one
with flag `true`; in world `false` the answers are equal, in world `true` they are `F false c` and
`F true c`. -/
example {C Y : Type*} (F : Bool → C → Y) (c : C) :
    (fun b : Bool => (F (xor false (b && false)) c, F (xor false (b && true)) c)) false =
      (F false c, F false c) := rfl

end VoleMole.MoussakaUnbound
