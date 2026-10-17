import Mathlib

/-!
# Ratatouille: the credit-accounting invariant (`lean/docs/security/ratatouille.md`, §4)

This file proves the deterministic core of Ratatouille's balance-security theorem. The
cryptographic part of the proof (straight-line extraction of every accepted request, commitment
binding, Tag collision resistance, UOV unforgeability) reduces an adaptive run of the protocol to
the following combinatorial situation, which is stated here as hypotheses:

* `I` is the finite set of issuance events; event `i` issued `T i` credits.
* `J` is the finite set of accepted spends. Spend `j` publishes `d j`. Its extracted witness has
  current credit `t j`, current refund `x j` and change `t' j` (`spend.hpp`, V1-V4), with
  `t j + x j = t' j + d j` over the integers (L7: the 65-bit adder is exact).
* `parent j` is the signing event that certified the state spent by `j`: an issuance (`inl i`), or
  the response to an earlier spend request (`inr k`). If several refunds were signed for the
  commitment `c' k` (for example, a retry with a different refund), `X k` bounds the refund that
  the spender can claim; with exactly one response per spend, `X k = x' k`.
* Commitment binding gives `t j = T i`, `x j = 0` for an issuance parent and `t j = t' k`,
  `x j ≤ X k` for a spend parent.
* Nullifier uniqueness together with binding (distinct accepted spends have distinct `nf`, hence
  distinct commitments) gives injectivity of `parent` on `J`.

`balance_identity` is the exact conservation law: spent credits plus the value of every
certified-but-unspent state equal issued credits plus granted refunds. `balance_le` is the
balance-security conclusion, `Σ d ≤ Σ T + Σ X`.

`change_correct` checks the 64-bit arithmetic of `spend_request_with_seed`
(`src/ratatouille/ratatouille.cpp:228-236`): the client accepts exactly when the true change
`t + x - d` is a credit value, and then computes it correctly modulo `2^64`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Ratatouille

section Accounting

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

/-- The value certified by a signing event: an issuance carries its initial credit, a spend
response carries the change plus the refund bound. -/
def nodeValue (T : ι → ℕ) (t' X : σ → ℕ) : ι ⊕ σ → ℕ
  | Sum.inl i => T i
  | Sum.inr k => t' k + X k

/-- Hypotheses produced by the cryptographic part of the proof. -/
structure Chain (I : Finset ι) (J : Finset σ) (T : ι → ℕ) (d t x t' X : σ → ℕ)
    (parent : σ → ι ⊕ σ) : Prop where
  /-- V3, exactly over the integers. -/
  conserve : ∀ j ∈ J, t j + x j = t' j + d j
  /-- Binding for an issuance parent. -/
  parent_issue : ∀ j ∈ J, ∀ i, parent j = Sum.inl i → i ∈ I ∧ t j = T i ∧ x j = 0
  /-- Binding for a spend parent; the refund was signed for that commitment. -/
  parent_spend : ∀ j ∈ J, ∀ k, parent j = Sum.inr k → k ∈ J ∧ t j = t' k ∧ x j ≤ X k
  /-- Nullifier uniqueness: no certified state is spent twice. -/
  inj : Set.InjOn parent J

variable {I : Finset ι} {J : Finset σ} {T : ι → ℕ} {d t x t' X : σ → ℕ} {parent : σ → ι ⊕ σ}

lemma Chain.image_subset (h : Chain I J T d t x t' X parent) :
    J.image parent ⊆ I.disjSum J := by
  intro p hp
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
  cases hpj : parent j with
  | inl i => simpa [hpj] using (h.parent_issue j hj i hpj).1
  | inr k => simpa [hpj] using (h.parent_spend j hj k hpj).1

lemma Chain.consumed_le (h : Chain I J T d t x t' X parent) (j : σ) (hj : j ∈ J) :
    t j + x j ≤ nodeValue T t' X (parent j) := by
  cases hpj : parent j with
  | inl i =>
    obtain ⟨-, ht, hx⟩ := h.parent_issue j hj i hpj
    simp [nodeValue, ht, hx]
  | inr k =>
    obtain ⟨-, ht, hx⟩ := h.parent_spend j hj k hpj
    simp only [nodeValue]
    omega

/-- Spent credits plus the change of every spend equal the value of the consumed states, up to
the refund slack `x j ≤ X k`. -/
lemma Chain.spent_plus_change_le (h : Chain I J T d t x t' X parent) :
    ∑ j ∈ J, d j + ∑ j ∈ J, t' j ≤ ∑ p ∈ J.image parent, nodeValue T t' X p := by
  rw [Finset.sum_image h.inj, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have := h.conserve j hj
  have := h.consumed_le j hj
  omega

/-- The total value of all signing events. -/
lemma total_value :
    ∑ p ∈ I.disjSum J, nodeValue T t' X p = ∑ i ∈ I, T i + ∑ j ∈ J, t' j + ∑ j ∈ J, X j := by
  rw [Finset.sum_disjSum]
  simp only [nodeValue, Finset.sum_add_distrib]
  ring

/-- **Balance security (deterministic core).** Spent credits plus the value of every signing
event that was never spent are at most the issued credits plus the refund bounds. -/
theorem balance_identity_le (h : Chain I J T d t x t' X parent) :
    ∑ j ∈ J, d j + ∑ p ∈ I.disjSum J \ J.image parent, nodeValue T t' X p
      ≤ ∑ i ∈ I, T i + ∑ j ∈ J, X j := by
  have hsub := h.image_subset
  have hsplit := Finset.sum_sdiff (f := nodeValue T t' X) hsub
  have hspent := h.spent_plus_change_le
  have htot := total_value (I := I) (J := J) (T := T) (t' := t') (X := X)
  omega

/-- With exactly one refund per spend (`x j = X k` for a spend parent), the law is an identity:
spent + outstanding = issued + refunded. -/
theorem balance_identity (h : Chain I J T d t x t' X parent)
    (hexact : ∀ j ∈ J, ∀ k, parent j = Sum.inr k → x j = X k) :
    ∑ j ∈ J, d j + ∑ p ∈ I.disjSum J \ J.image parent, nodeValue T t' X p
      = ∑ i ∈ I, T i + ∑ j ∈ J, X j := by
  have hsub := h.image_subset
  have hsplit := Finset.sum_sdiff (f := nodeValue T t' X) hsub
  have htot := total_value (I := I) (J := J) (T := T) (t' := t') (X := X)
  have hcons : ∑ j ∈ J, d j + ∑ j ∈ J, t' j = ∑ p ∈ J.image parent, nodeValue T t' X p := by
    rw [Finset.sum_image h.inj, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hc := h.conserve j hj
    cases hpj : parent j with
    | inl i =>
      obtain ⟨-, ht, hx⟩ := h.parent_issue j hj i hpj
      simp only [nodeValue]
      omega
    | inr k =>
      obtain ⟨-, ht, -⟩ := h.parent_spend j hj k hpj
      have hx := hexact j hj k hpj
      simp only [nodeValue]
      omega
  omega

/-- **Balance security.** No adversary spends more than was issued and refunded. -/
theorem balance_le (h : Chain I J T d t x t' X parent) :
    ∑ j ∈ J, d j ≤ ∑ i ∈ I, T i + ∑ j ∈ J, X j :=
  le_trans (Nat.le_add_right _ _) (balance_identity_le h)

end Accounting

section Arithmetic

/-- `2^64`, as a literal so that `omega` sees it. -/
local notation "W" => (18446744073709551616 : ℕ)

/-- The client's acceptance test and change computation in `spend_request_with_seed`
(`ratatouille.cpp:228-236`), on `uint64_t` values modelled as naturals below `2^64`:
`lo = (t + x) mod 2^64`, `overflow = lo < t`; reject if `!overflow && d > lo` or
`overflow && d <= lo`; otherwise `t_next = (lo - d) mod 2^64`. -/
def clientAccepts (t x d : ℕ) : Prop :=
  let lo := (t + x) % W
  let overflow := lo < t
  ¬(¬overflow ∧ d > lo) ∧ ¬(overflow ∧ d ≤ lo)

/-- `t_next` as computed by unsigned 64-bit subtraction. -/
def clientChange (t x d : ℕ) : ℕ := ((t + x) % W + W - d) % W

/-- The client accepts exactly when the true change `t + x - d` is a credit value, i.e. exactly
when the spend relation (V3, V4) has a witness, and then computes the true change. -/
theorem change_correct (t x d : ℕ) (ht : t < W) (hx : x < W) (hd : d < W) :
    (clientAccepts t x d ↔ d ≤ t + x ∧ t + x - d < W) ∧
      (clientAccepts t x d → clientChange t x d = t + x - d) := by
  unfold clientAccepts clientChange
  simp only
  constructor
  · constructor
    · intro h
      omega
    · intro h
      omega
  · intro h
    omega

/-- The overflow flag is exact: `lo < t` iff `t + x ≥ 2^64`. -/
theorem overflow_iff (t x : ℕ) (ht : t < W) (hx : x < W) :
    (t + x) % W < t ↔ W ≤ t + x := by
  omega

end Arithmetic

end VoleMole.Ratatouille
