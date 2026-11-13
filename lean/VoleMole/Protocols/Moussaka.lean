import Mathlib

/-!
# Moussaka: deterministic cores of the security proofs (`lean/docs/security/moussaka.md`)

Two deterministic facts that the written proofs in `lean/docs/security/moussaka.md` use.

* `selector_one_hot` (§5.3 of the note): the redemption relation's selector constraints
  (`src/moussaka/redeem.hpp:223-242`, draft `RedeemRelation`) force a one-hot vector with entry `1`,
  over **any** field. In particular this holds over `GF(2)`, where the implementation constrains
  each `b[u]` to be a bit, and over `F_q`, where the draft does not add bit constraints. Entries at
  or beyond `n` (the padding up to `MAX_ANCHORS`) are constrained to be zero separately, so we only
  look at indices below `n`.

  Constraints: `(Σ_{k ≤ u} b k) * b (u+1) = 0` for `u + 1 < n` (parity), and `Σ_{k < n} b k = 1`
  (weight).

* `exists_unsigned_of_card_lt` (§4, one-more unforgeability): if the accepted redemptions map
  injectively to commitments (distinct `(ctx_red, nf)` and binding), and there are more accepted
  redemptions than signed commitments, then some accepted redemption's commitment was never signed.
  This is the pigeonhole step that turns a one-more forger into a UOV-Com forger.

* `collision_or_forgery` (§4, steps 3–4): with an extracted opening for every accepted issuance and
  redemption, a win yields a `Com` collision among the openings or a redemption opening whose
  commitment was never signed. `ROM/MoussakaOMUF.lean` uses it for Theorem 1.
-/

open Finset

namespace VoleMole.Moussaka

section Selector

variable {F : Type*} [Field F]

/-- Prefix sum `Σ_{k ≤ u} b k`. -/
def pre (b : ℕ → F) (u : ℕ) : F := ∑ k ∈ range (u + 1), b k

lemma pre_succ (b : ℕ → F) (u : ℕ) : pre b (u + 1) = pre b u + b (u + 1) := by
  unfold pre
  rw [sum_range_succ]

/-- After the first nonzero entry `i`, the parity constraints force every later entry (below `n`)
to vanish, and the prefix sum stays equal to `b i`. -/
lemma tail_zero (b : ℕ → F) (n i : ℕ)
    (hpar : ∀ u, u + 1 < n → pre b u * b (u + 1) = 0)
    (hfirst : ∀ k < i, b k = 0) (hi : b i ≠ 0) :
    ∀ m, i ≤ m → m < n → pre b m = b i ∧ ∀ k, i < k → k ≤ m → b k = 0 := by
  intro m
  induction m with
  | zero =>
    intro him _
    have hi0 : i = 0 := Nat.le_zero.mp him
    subst hi0
    refine ⟨by simp [pre], ?_⟩
    intro k hk hk'
    omega
  | succ m ih =>
    intro him hmn
    rcases Nat.lt_or_ge m i with hlt | hge
    · -- m < i ≤ m + 1, so i = m + 1
      have hieq : i = m + 1 := by omega
      subst hieq
      refine ⟨?_, ?_⟩
      · rw [pre_succ]
        have : pre b m = 0 := by
          unfold pre
          apply sum_eq_zero
          intro k hk
          exact hfirst k (by simp at hk; omega)
        rw [this, zero_add]
      · intro k hk hk'
        omega
    · obtain ⟨hpre, hzero⟩ := ih hge (by omega)
      have hb : b (m + 1) = 0 := by
        have h := hpar m hmn
        rw [hpre] at h
        rcases mul_eq_zero.mp h with h1 | h1
        · exact absurd h1 hi
        · exact h1
      refine ⟨?_, ?_⟩
      · rw [pre_succ, hpre, hb, add_zero]
      · intro k hk hk'
        rcases Nat.lt_or_ge k (m + 1) with h | h
        · exact hzero k hk (by omega)
        · have : k = m + 1 := by omega
          rw [this]
          exact hb

/-- **Selector soundness.** The parity and weight constraints imply that `b` restricted to
`[0, n)` is the indicator vector of a single index, with entry exactly `1`. -/
theorem selector_one_hot (b : ℕ → F) (n : ℕ)
    (hpar : ∀ u, u + 1 < n → pre b u * b (u + 1) = 0)
    (hsum : ∑ k ∈ range n, b k = 1) :
    ∃ i < n, b i = 1 ∧ ∀ k < n, k ≠ i → b k = 0 := by
  -- Some entry below n is nonzero, since the sum is 1.
  have hex : ∃ k, k < n ∧ b k ≠ 0 := by
    by_contra h
    push Not at h
    have : ∑ k ∈ range n, b k = 0 := sum_eq_zero (fun k hk => h k (mem_range.mp hk))
    rw [this] at hsum
    exact zero_ne_one hsum
  classical
  let i := Nat.find hex
  have hi_spec : i < n ∧ b i ≠ 0 := Nat.find_spec hex
  have hfirst : ∀ k < i, b k = 0 := by
    intro k hk
    by_contra hne
    exact Nat.find_min hex hk ⟨by have := hi_spec.1; omega, hne⟩
  have hn : 0 < n := by have := hi_spec.1; omega
  obtain ⟨hpre, hzero⟩ :=
    tail_zero b n i hpar hfirst hi_spec.2 (n - 1) (by have := hi_spec.1; omega) (by omega)
  have hpre_n : pre b (n - 1) = 1 := by
    unfold pre
    have : n - 1 + 1 = n := by omega
    rw [this, hsum]
  refine ⟨i, hi_spec.1, ?_, ?_⟩
  · rw [← hpre, hpre_n]
  · intro k hk hki
    rcases Nat.lt_or_ge k i with h | h
    · exact hfirst k h
    · exact hzero k (by omega) (by omega)

/-- The `GF(2)` instance used by the implementation, where every `b[u]` is also a bit. -/
theorem selector_one_hot_gf2 (b : ℕ → ZMod 2) (n : ℕ)
    (hpar : ∀ u, u + 1 < n → pre b u * b (u + 1) = 0)
    (hsum : ∑ k ∈ range n, b k = 1) :
    ∃ i < n, b i = 1 ∧ ∀ k < n, k ≠ i → b k = 0 :=
  selector_one_hot b n hpar hsum

/-- Without the parity constraints the weight constraint alone is not enough over `GF(2)`: three
set bits also sum to `1`. (This is why the draft needs them.) -/
example : (∑ k ∈ range 3, (fun _ : ℕ => (1 : ZMod 2)) k) = 1 := by decide

end Selector

section OneMore

variable {ρ τ : Type*} [DecidableEq τ]

/-- **Pigeonhole step of one-more unforgeability.** `R` is the set of accepted redemptions for one
issuance context, `t j` the commitment extracted from redemption `j`, and `L` the set of
commitments that some honest Anchor signed for that context. If `t` is injective on `R` (binding,
and the Moderator accepts each `(ctx_red, nf)` once) and `R` is larger than `L`, some accepted
redemption opens a commitment that no Anchor signed. -/
theorem exists_unsigned_of_card_lt (R : Finset ρ) (L : Finset τ) (t : ρ → τ)
    (hinj : Set.InjOn t R) (hlt : L.card < R.card) :
    ∃ j ∈ R, t j ∉ L := by
  by_contra h
  push Not at h
  have : R.card ≤ L.card := card_le_card_of_injOn t (fun j hj => h j hj) hinj
  omega

/-- **The deterministic core of Theorem 1** (`lean/docs/security/moussaka.md` §4, steps 3–4).

Openings `x : X` commit to `com x`, carry an issuance context `ctxOf x` and a redemption identity
`rid x` (`(ctx_red, nf)`). `iss` lists the accepted issuance queries `(t, ctx)`; each has an
extracted opening in `S` with that commitment and context. `red` lists the accepted redemptions
`(ctx_iss, (ctx_red, nf))`; each has an extracted opening in `S' ⊆ S` with that context and
identity (`S'`: the openings for which the redemption proof also extracted an Anchor key and a
preimage). If, for some context, more distinct redemption identities were accepted than distinct
commitments were signed, then either two distinct extracted openings collide (`Com` binding) or
some redemption opening's commitment was never submitted to any Anchor (a CT-UF forgery). -/
theorem collision_or_forgery {X τ C ρ : Type*} [DecidableEq τ] [DecidableEq C] [DecidableEq ρ]
    (com : X → τ) (ctxOf : X → C) (rid : X → ρ) (S S' : Set X) (hS' : S' ⊆ S)
    (iss : List (τ × C)) (red : List (C × ρ))
    (hiss : ∀ q ∈ iss, ∃ x ∈ S, com x = q.1 ∧ ctxOf x = q.2)
    (hred : ∀ j ∈ red, ∃ x ∈ S', ctxOf x = j.1 ∧ rid x = j.2)
    (c : C) (hwin : ((iss.filter (·.2 = c)).map (·.1)).toFinset.card <
      ((red.filter (·.1 = c)).map (·.2)).toFinset.card) :
    (∃ x ∈ S, ∃ x' ∈ S, x ≠ x' ∧ com x = com x') ∨ (∃ x ∈ S', com x ∉ iss.map (·.1)) := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨hcoll, hforge⟩ := hno
  -- an opening for every accepted redemption identity in context `c`
  have hchoose : ∀ r ∈ ((red.filter (·.1 = c)).map (·.2)).toFinset,
      ∃ x ∈ S', ctxOf x = c ∧ rid x = r := by
    intro r hr
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hr
    obtain ⟨j, ⟨hj, hjc⟩, rfl⟩ := hr
    obtain ⟨x, hx, h1, h2⟩ := hred j hj
    exact ⟨x, hx, h1.trans hjc, h2⟩
  have : Nonempty X := by
    obtain ⟨r, hr⟩ := Finset.card_pos.1 (lt_of_le_of_lt (Nat.zero_le _) hwin)
    exact ⟨(hchoose r hr).choose⟩
  choose! op hop using hchoose
  set R := ((red.filter (·.1 = c)).map (·.2)).toFinset
  set L := ((iss.filter (·.2 = c)).map (·.1)).toFinset
  have hinj : Set.InjOn (fun r => com (op r)) R := by
    intro r hr r' hr' h
    by_contra hne
    have hx : op r ≠ op r' := fun e => hne (by rw [← (hop r hr).2.2, e, (hop r' hr').2.2])
    exact hcoll _ (hS' (hop r hr).1) _ (hS' (hop r' hr').1) hx h
  obtain ⟨r, hr, hnot⟩ := exists_unsigned_of_card_lt R L (fun r => com (op r)) hinj hwin
  -- `com (op r)` was signed (no forgery), but not in context `c`: a collision
  have hsig := hforge _ (hop r hr).1
  obtain ⟨q, hq, hqt⟩ := List.mem_map.1 hsig
  obtain ⟨x, hx, hxt, hxc⟩ := hiss q hq
  have hqc : q.2 ≠ c := fun e => hnot (by
    simp only [L, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨q, ⟨hq, e⟩, hqt⟩)
  have hne : x ≠ op r := fun e => hqc (by rw [← hxc, e, (hop r hr).2.1])
  exact hcoll _ hx _ (hS' (hop r hr).1) hne (hxt.trans hqt)

end OneMore

end VoleMole.Moussaka
