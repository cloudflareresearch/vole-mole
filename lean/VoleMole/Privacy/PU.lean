import VoleMole.Privacy.Hybrid

/-!
# (PU): unpredictability of a commitment's opening, as a game, and its ideal-permutation bound

On `main` (no dedicated label rows) zero knowledge of the Moussaka and Ratatouille proofs holds up
to the probability that the adversary predicts the first 16 witness bytes, which are the opening
`r` of the token's commitment (`ZK/HopsMain.lean`, `Privacy/MoussakaMain.lean`,
`Privacy/RatatouilleMain.lean`). This file states that event as a game and bounds it in the
ideal-permutation model.

## The game (`puAdv`), standard model

`com : N → R → T` is a commitment with public part `n : N` (nullifier, contexts, credit value) and
opening `r : R`. A **predictor** `P n t aux : Finset R` sees the public part, the commitment
`t = com n r` and auxiliary coins `aux` that are independent of `r`, and outputs a set of
candidates. Its advantage is

    puAdv com P = Pr_{n, r, aux}[ r ∈ P n (com n r) aux ].

**(PU)** for a class of predictors is the assumption that this is small. It is a one-wayness
assumption on `com` in `r` (with `c` guesses allowed, `c` the size of the candidate sets). It is
computational: the predictor `bruteForce com` that returns every opening of `t` wins with
probability `1` (`puAdv_bruteForce`), with one candidate when `com n` is injective
(`card_bruteForce_le`).

## The ideal-permutation model (`pr_predict_perm_le`, `puAdvPerm_le`)

`Com` is one call of Keccak-p[800,12], truncated: `com n r = tr (π (X n r))` with `X n` an
injective encoding of `r` into the 800-bit state and `tr` the truncation (`comP`). Here `π` is a
**uniformly random permutation** of the states, and the predictor is an **oracle algorithm** with
forward and inverse queries to `π` (`PTree`: a decision tree; `PTree.run`), with at most `q`
queries on every path (`PTree.Bound`) and at most `c` candidates. Then

    Pr_{π, n, r, aux}[ r ∈ P^π(n, tr (π (X n r)), aux) ] ≤ (c + q) / (|R| − q) + q / (m − q)

where `m` is the size of the fibres of `tr`. For Keccak-p[800] with a 128-bit opening and a
360-bit (Moussaka) or 256-bit (Ratatouille) commitment: `(c + q)/(2¹²⁸ − q) + q/(2⁴⁴⁰ − q)` and
`(c + q)/(2¹²⁸ − q) + q/(2⁵⁴⁴ − q)` (`puAdvPerm_moussaka_le`, `puAdvPerm_ratatouille_le` in
`Privacy/PUKeccak.lean`).

**The proof** is by symmetry, with no lazy sampling.
* `pr_input_sym_le`: if the predictor's inputs to `π` (`S`, the inputs of its forward queries and
  the answers of its inverse queries) do not contain `X r`, then for every other opening `r'`
  with `X r' ∉ S` the permutation `π ∘ swap (X r) (X r')` gives the same commitment for `r'` and
  the same run. So `r` is one of at least `|R| − q` equally likely openings, and the candidates
  contain it with probability `≤ c / (|R| − q)`.
* `pr_output_sym_le`: likewise for the value `π (X r)`, with `swap (π (X r)) y' ∘ π` for the `y'`
  that have the same truncation: a set of `c` candidates for `π (X r)` contains it with
  probability `≤ c / (m − q)`.
* `PTree.touch`: if the run does touch `X r`, the run cut before the first query that does
  (`PTree.cut`) has not touched it, and that query names `r` (a forward query at `X r`) or
  `π (X r)` (an inverse query at it): one candidate. Union over the `q` positions.

**What this says about Keccak-p[800,12].** Nothing is proved about the real permutation. The
theorem is the generic bound: an attack that uses the permutation only as a black box needs about
`2¹²⁸/(c + q)` queries. The real permutation is one fixed public function, and the predictors of
the privacy theorems are arbitrary functions, so for it (PU) remains an assumption: that
12-round Keccak-p[800] has no structural shortcut for recovering 128 unknown input bits from a
truncated output when the other 672 input bits are known (`lean/docs/zk.md` §4.3).
-/

open Finset

namespace VoleMole.Privacy.PU

/-! ## The game -/

section Game

variable {N R T Aux : Type*} [Fintype N] [Fintype R] [Fintype Aux]

/-- **The (PU) advantage** of the predictor `P` against the commitment `com`: for a uniform
public part `n`, a uniform opening `r` and independent coins `aux`, the candidate set
`P n (com n r) aux` contains `r`. -/
noncomputable def puAdv (com : N → R → T) (P : N → T → Aux → Finset R) : ℝ :=
  pr ((N × R) × Aux) fun z => z.1.2 ∈ P z.1.1 (com z.1.1 z.1.2) z.2

lemma puAdv_nonneg (com : N → R → T) (P : N → T → Aux → Finset R) : 0 ≤ puAdv com P :=
  pr_nonneg _

lemma puAdv_le_one (com : N → R → T) (P : N → T → Aux → Finset R) : puAdv com P ≤ 1 :=
  pr_le_one _

/-- The predictor that returns every opening of the commitment. -/
def bruteForce [DecidableEq T] (com : N → R → T) : N → T → Aux → Finset R :=
  fun n t _ => univ.filter fun r => com n r = t

/-- **(PU) is computational**: the exhaustive predictor always wins. -/
theorem puAdv_bruteForce [DecidableEq T] [Nonempty N] [Nonempty R] [Nonempty Aux]
    (com : N → R → T) : puAdv com (bruteForce (Aux := Aux) com) = 1 := by
  classical
  unfold puAdv
  rw [pr_congr (Q := fun _ => True) fun z => by simp [bruteForce], pr_const]
  simp

omit [Fintype N] [Fintype Aux] in
/-- With an injective commitment the exhaustive predictor outputs at most one candidate. -/
theorem card_bruteForce_le [DecidableEq T] (com : N → R → T)
    (hinj : ∀ n, Function.Injective (com n)) (n : N) (t : T) (a : Aux) :
    (bruteForce com n t a).card ≤ 1 := by
  classical
  refine Finset.card_le_one.2 fun r hr r' hr' => hinj n ?_
  rw [bruteForce, Finset.mem_filter] at hr hr'
  rw [hr.2, hr'.2]

/-- **A predictor whose candidates do not depend on the commitment** wins with probability at most
`c / |R|` (the statistical case: the adversary never sees `t`). -/
theorem puAdv_const_le [Nonempty N] [Nonempty Aux] (com : N → R → T) (P : N → Aux → Finset R)
    {c : ℕ} (hc : ∀ n a, (P n a).card ≤ c) :
    puAdv com (fun n _ a => P n a) ≤ c / Fintype.card R := by
  classical
  unfold puAdv
  let e : (N × Aux) × R ≃ (N × R) × Aux :=
    { toFun := fun z => ((z.1.1, z.2), z.1.2)
      invFun := fun z => ((z.1.1, z.2), z.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e, pr_prod]
  have hNA : (0 : ℝ) < Fintype.card (N × Aux) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hNA]
  calc ∑ a : N × Aux, pr R (fun r => r ∈ P a.1 a.2)
      ≤ ∑ _a : N × Aux, (c : ℝ) / Fintype.card R := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [pr_def]
        gcongr
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        exact_mod_cast hc a.1 a.2
    _ = c / Fintype.card R * Fintype.card (N × Aux) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

end Game

/-! ## Oracle algorithms with forward and inverse queries to a permutation -/

/-- **An oracle algorithm** with forward and inverse queries to a permutation of `K` and an output
in `C`, as a decision tree. -/
inductive PTree (K : Type) (C : Type) : Type
  | done : C → PTree K C
  | fwd : K → (K → PTree K C) → PTree K C
  | inv : K → (K → PTree K C) → PTree K C

namespace PTree

variable {K C C' : Type}

/-- The output of the algorithm with the permutation `π`. -/
def run : PTree K C → Equiv.Perm K → C
  | .done c, _ => c
  | .fwd x k, π => run (k (π x)) π
  | .inv y k, π => run (k (π.symm y)) π

/-- **The inputs of `π` that the run determines**: the forward queries, and the answers of the
inverse queries. -/
def ins [DecidableEq K] : PTree K C → Equiv.Perm K → Finset K
  | .done _, _ => ∅
  | .fwd x k, π => insert x (ins (k (π x)) π)
  | .inv y k, π => insert (π.symm y) (ins (k (π.symm y)) π)

/-- **At most `q` queries on every path.** -/
inductive Bound : PTree K C → ℕ → Prop
  | done (c : C) (q : ℕ) : Bound (.done c) q
  | fwd (x : K) (k : K → PTree K C) (q : ℕ) : (∀ y, Bound (k y) q) → Bound (.fwd x k) (q + 1)
  | inv (y : K) (k : K → PTree K C) (q : ℕ) : (∀ x, Bound (k x) q) → Bound (.inv y k) (q + 1)

lemma card_ins_le [DecidableEq K] {a : PTree K C} {q : ℕ} (h : Bound a q) (π : Equiv.Perm K) :
    (ins a π).card ≤ q := by
  induction h with
  | done c q => simp [ins]
  | fwd x k q _ ih => exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (ih _))
  | inv y k q _ ih => exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (ih _))

/-- **The run depends on `π` only at its inputs.** -/
lemma run_congr [DecidableEq K] (a : PTree K C) (π π' : Equiv.Perm K)
    (h : ∀ x ∈ ins a π, π' x = π x) : run a π' = run a π ∧ ins a π' = ins a π := by
  induction a with
  | done c => exact ⟨rfl, rfl⟩
  | fwd x k ih =>
    have hx : π' x = π x := h x (by simp [ins])
    have := ih (π x) fun z hz => h z (by simp [ins, hz])
    simp only [run, ins, hx]
    exact ⟨this.1, by rw [this.2]⟩
  | inv y k ih =>
    have hy : π'.symm y = π.symm y := by
      rw [Equiv.symm_apply_eq, h (π.symm y) (by simp [ins]), Equiv.apply_symm_apply]
    have := ih (π.symm y) fun z hz => h z (by simp [ins, hz])
    simp only [run, ins, hy]
    exact ⟨this.1, by rw [this.2]⟩

/-- **The algorithm cut before its query number `n`** (counted from `0`): it outputs `f x` if that
query is a forward query at `x`, `g y` if it is an inverse query at `y`, and `e` if the algorithm
stops earlier. -/
def cut (f g : K → C') (e : C') : ℕ → PTree K C → PTree K C'
  | _, .done _ => .done e
  | 0, .fwd x _ => .done (f x)
  | 0, .inv y _ => .done (g y)
  | n + 1, .fwd x k => .fwd x fun y => cut f g e n (k y)
  | n + 1, .inv y k => .inv y fun x => cut f g e n (k x)

lemma bound_cut (f g : K → C') (e : C') (n : ℕ) (a : PTree K C) : Bound (cut f g e n a) n := by
  induction n generalizing a with
  | zero => cases a <;> exact Bound.done _ _
  | succ n ih =>
    cases a with
    | done c => exact Bound.done _ _
    | fwd x k => exact Bound.fwd _ _ _ fun y => ih (k y)
    | inv y k => exact Bound.inv _ _ _ fun x => ih (k x)

/-- The output of a cut algorithm is one of `e`, `f x`, `g y`. -/
lemma run_cut (f g : K → C') (e : C') (n : ℕ) (a : PTree K C) (π : Equiv.Perm K) :
    run (cut f g e n a) π = e ∨ (∃ x, run (cut f g e n a) π = f x) ∨
      ∃ y, run (cut f g e n a) π = g y := by
  induction n generalizing a with
  | zero =>
    cases a with
    | done c => exact Or.inl rfl
    | fwd x k => exact Or.inr (Or.inl ⟨x, rfl⟩)
    | inv y k => exact Or.inr (Or.inr ⟨y, rfl⟩)
  | succ n ih =>
    cases a with
    | done c => exact Or.inl rfl
    | fwd x k => exact ih (k (π x))
    | inv y k => exact ih (k (π.symm y))

/-- **The first touch.** If the run determines `π` at `z`, then for some `n < q` the run cut
before query `n` does not, and query `n` is a forward query at `z` (the cut outputs `f z`) or an
inverse query at `π z` (it outputs `g (π z)`). -/
lemma touch [DecidableEq K] (f g : K → C') (e : C') {a : PTree K C} {q : ℕ} (h : Bound a q)
    (π : Equiv.Perm K) (z : K) (hz : z ∈ ins a π) :
    ∃ n < q, z ∉ ins (cut f g e n a) π ∧
      (run (cut f g e n a) π = f z ∨ run (cut f g e n a) π = g (π z)) := by
  induction h with
  | done c q => simp [ins] at hz
  | fwd x k q _ ih =>
    by_cases hx : z = x
    · exact ⟨0, Nat.succ_pos _, by simp [cut, ins], Or.inl (by rw [hx]; rfl)⟩
    · have hz' : z ∈ ins (k (π x)) π := by
        simp only [ins, Finset.mem_insert] at hz
        exact hz.resolve_left hx
      obtain ⟨n, hn, h1, h2⟩ := ih (π x) hz'
      refine ⟨n + 1, Nat.succ_lt_succ hn, ?_, h2⟩
      simp only [cut, ins, Finset.mem_insert, not_or]
      exact ⟨hx, h1⟩
  | inv y k q _ ih =>
    by_cases hy : z = π.symm y
    · refine ⟨0, Nat.succ_pos _, by simp [cut, ins], Or.inr ?_⟩
      rw [hy, Equiv.apply_symm_apply]; rfl
    · have hz' : z ∈ ins (k (π.symm y)) π := by
        simp only [ins, Finset.mem_insert] at hz
        exact hz.resolve_left hy
      obtain ⟨n, hn, h1, h2⟩ := ih (π.symm y) hz'
      refine ⟨n + 1, Nat.succ_lt_succ hn, ?_, h2⟩
      simp only [cut, ins, Finset.mem_insert, not_or]
      exact ⟨hy, h1⟩

end PTree

/-! ## The two symmetries -/

section Sym

variable {K R T : Type} [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]

/-- **Input symmetry.** A candidate set `C` for the opening that depends on `π` only at inputs
`S ∌ X r` (at most `q` of them) contains `r` with probability at most `c / (|R| − q)`: every
opening `r'` with `X r' ∉ S` is as likely, through `π ∘ swap (X r) (X r')`. -/
theorem pr_input_sym_le (X : R → K) (hX : Function.Injective X) (tr : K → T)
    (C : T → Equiv.Perm K → Finset R) (S : T → Equiv.Perm K → Finset K) {q c : ℕ}
    (hS : ∀ t π, (S t π).card ≤ q) (hC : ∀ t π, (C t π).card ≤ c)
    (hcong : ∀ t π π', (∀ x ∈ S t π, π' x = π x) → C t π' = C t π ∧ S t π' = S t π)
    (hq : q < Fintype.card R) :
    pr (R × Equiv.Perm K) (fun z => z.1 ∈ C (tr (z.2 (X z.1))) z.2 ∧
      X z.1 ∉ S (tr (z.2 (X z.1))) z.2) ≤ c / (Fintype.card R - q : ℝ) := by
  classical
  set Ω := R × Equiv.Perm K
  let t : Ω → T := fun z => tr (z.2 (X z.1))
  set E : Finset Ω := univ.filter fun z => z.1 ∈ C (t z) z.2 ∧ X z.1 ∉ S (t z) z.2 with hE
  let Nb : Ω → Finset R := fun z => univ.filter fun r' => X r' ∉ S (t z) z.2
  let G : Finset (Σ _ : Ω, R) := E.sigma Nb
  let H : Finset (Σ _ : Ω, R) := (univ : Finset Ω).sigma fun z => C (t z) z.2
  let φ : (Σ _ : Ω, R) → (Σ _ : Ω, R) := fun p =>
    ⟨(p.2, p.1.2 * Equiv.swap (X p.1.1) (X p.2)), p.1.1⟩
  have hNb : ∀ z, Fintype.card R - q ≤ (Nb z).card := by
    intro z
    have h1 : (univ.filter fun r' => X r' ∈ S (t z) z.2).card ≤ q :=
      (Finset.card_le_card_of_injOn X (fun r hr => by
        simpa using hr) (fun a _ b _ h => hX h)).trans (hS _ _)
    have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset R))
      (fun r' => X r' ∈ S (t z) z.2)
    rw [Finset.card_univ] at h2
    show Fintype.card R - q ≤ (univ.filter fun r' => X r' ∉ S (t z) z.2).card
    omega
  have hG : E.card * (Fintype.card R - q) ≤ G.card := by
    rw [Finset.card_sigma]
    calc E.card * (Fintype.card R - q) = ∑ _z ∈ E, (Fintype.card R - q) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ z ∈ E, (Nb z).card := Finset.sum_le_sum fun z _ => hNb z
  have hH : H.card ≤ c * Fintype.card Ω := by
    rw [Finset.card_sigma]
    calc ∑ z : Ω, (C (t z) z.2).card ≤ ∑ _z : Ω, c := Finset.sum_le_sum fun z _ => hC _ _
      _ = c * Fintype.card Ω := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have hmaps : ∀ p ∈ G, φ p ∈ H := by
    rintro ⟨⟨r, π⟩, r'⟩ hp
    simp only [G, Finset.mem_sigma, hE, Nb, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨⟨hr, hrS⟩, hr'S⟩ := hp
    simp only [H, φ, Finset.mem_sigma, Finset.mem_univ, true_and]
    have ht : t (r', π * Equiv.swap (X r) (X r')) = t (r, π) := by
      show tr ((π * Equiv.swap (X r) (X r')) (X r')) = tr (π (X r))
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    rw [ht]
    have hag : ∀ x ∈ S (t (r, π)) π, (π * Equiv.swap (X r) (X r')) x = π x := by
      intro x hx
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne]
      · rintro rfl; exact hrS hx
      · rintro rfl; exact hr'S hx
    rw [(hcong _ π _ hag).1]
    exact hr
  have hinj : Set.InjOn φ G := by
    rintro ⟨⟨r, π⟩, r'⟩ _ ⟨⟨ρ, σ⟩, ρ'⟩ _ h
    have ha : (r', π * Equiv.swap (X r) (X r')) = (ρ', σ * Equiv.swap (X ρ) (X ρ')) :=
      congrArg Sigma.fst h
    have h3 : r = ρ := congrArg (fun p : Σ _ : Ω, R => p.2) h
    obtain ⟨h1, h2⟩ := Prod.mk.inj ha
    subst h1 h3
    have : π = σ := mul_right_cancel h2
    subst this
    rfl
  have hcard : E.card * (Fintype.card R - q) ≤ c * Fintype.card Ω :=
    hG.trans ((Finset.card_le_card_of_injOn φ hmaps hinj).trans hH)
  have hΩ : (0 : ℝ) < Fintype.card Ω := by
    have : Nonempty R := Fintype.card_pos_iff.1 (by omega)
    exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) < (Fintype.card R - q : ℝ) := by
    have : (q : ℝ) < Fintype.card R := by exact_mod_cast hq
    linarith
  rw [pr_def, div_le_div_iff₀ hΩ hM]
  have : ((E.card * (Fintype.card R - q) : ℕ) : ℝ) ≤ ((c * Fintype.card Ω : ℕ) : ℝ) := by
    exact_mod_cast hcard
  rw [Nat.cast_mul, Nat.cast_sub hq.le, Nat.cast_mul] at this
  exact this

omit [DecidableEq R] in
/-- **Output symmetry.** A candidate set `Y` for the value `π (X r)` that depends on `π` only at
inputs `S ∌ X r` (at most `q`) contains it with probability at most `c / (m − q)`, `m` the size of
the fibres of the truncation: every `y'` with the same truncation whose preimage is not in `S` is
as likely, through `swap (π (X r)) y' ∘ π`. -/
theorem pr_output_sym_le (X : R → K) [DecidableEq T] (tr : K → T)
    (Y : T → Equiv.Perm K → Finset K) (S : T → Equiv.Perm K → Finset K) {q c m : ℕ}
    (hS : ∀ t π, (S t π).card ≤ q) (hY : ∀ t π, (Y t π).card ≤ c)
    (hcong : ∀ t π π', (∀ x ∈ S t π, π' x = π x) → Y t π' = Y t π ∧ S t π' = S t π)
    (hm : ∀ t, m ≤ (univ.filter fun y => tr y = t).card) (hq : q < m) [Nonempty R] :
    pr (R × Equiv.Perm K) (fun z => z.2 (X z.1) ∈ Y (tr (z.2 (X z.1))) z.2 ∧
      X z.1 ∉ S (tr (z.2 (X z.1))) z.2) ≤ c / (m - q : ℝ) := by
  classical
  set Ω := R × Equiv.Perm K
  let t : Ω → T := fun z => tr (z.2 (X z.1))
  set E : Finset Ω := univ.filter fun z => z.2 (X z.1) ∈ Y (t z) z.2 ∧ X z.1 ∉ S (t z) z.2 with hE
  let Nb : Ω → Finset K := fun z => univ.filter fun y' => tr y' = t z ∧ z.2.symm y' ∉ S (t z) z.2
  let G : Finset (Σ _ : Ω, K) := E.sigma Nb
  let H : Finset (Σ _ : Ω, K) := (univ : Finset Ω).sigma fun z => Y (t z) z.2
  let φ : (Σ _ : Ω, K) → (Σ _ : Ω, K) := fun p =>
    ⟨(p.1.1, Equiv.swap (p.1.2 (X p.1.1)) p.2 * p.1.2), p.1.2 (X p.1.1)⟩
  have hNb : ∀ z, m - q ≤ (Nb z).card := by
    intro z
    have h1 : (univ.filter fun y' => z.2.symm y' ∈ S (t z) z.2).card ≤ q :=
      (Finset.card_le_card_of_injOn z.2.symm (fun r hr => by
        simpa using hr) (fun a _ b _ h => z.2.symm.injective h)).trans (hS _ _)
    have h2 : (univ.filter fun y => tr y = t z) ⊆ Nb z ∪
        univ.filter fun y' => z.2.symm y' ∈ S (t z) z.2 := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [Nb, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hy]
      tauto
    have h3 := (Finset.card_le_card h2).trans (Finset.card_union_le _ _)
    have := hm (t z)
    omega
  have hG : E.card * (m - q) ≤ G.card := by
    rw [Finset.card_sigma]
    calc E.card * (m - q) = ∑ _z ∈ E, (m - q) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ z ∈ E, (Nb z).card := Finset.sum_le_sum fun z _ => hNb z
  have hH : H.card ≤ c * Fintype.card Ω := by
    rw [Finset.card_sigma]
    calc ∑ z : Ω, (Y (t z) z.2).card ≤ ∑ _z : Ω, c := Finset.sum_le_sum fun z _ => hY _ _
      _ = c * Fintype.card Ω := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have hmaps : ∀ p ∈ G, φ p ∈ H := by
    rintro ⟨⟨r, π⟩, y'⟩ hp
    simp only [G, Finset.mem_sigma, hE, Nb, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨⟨hr, hrS⟩, hy', hy'S⟩ := hp
    simp only [H, φ, Finset.mem_sigma, Finset.mem_univ, true_and]
    have ht : t (r, Equiv.swap (π (X r)) y' * π) = t (r, π) := by
      show tr ((Equiv.swap (π (X r)) y' * π) (X r)) = tr (π (X r))
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      exact hy'
    rw [ht]
    have hag : ∀ x ∈ S (t (r, π)) π, (Equiv.swap (π (X r)) y' * π) x = π x := by
      intro x hx
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne]
      · intro h
        rw [π.injective h] at hx
        exact hrS hx
      · rintro rfl
        rw [Equiv.symm_apply_apply] at hy'S
        exact hy'S hx
    rw [(hcong _ π _ hag).1]
    exact hr
  have hinj : Set.InjOn φ G := by
    rintro ⟨⟨r, π⟩, y'⟩ _ ⟨⟨ρ, σ⟩, y''⟩ _ h
    have ha : (r, Equiv.swap (π (X r)) y' * π) = (ρ, Equiv.swap (σ (X ρ)) y'' * σ) :=
      congrArg Sigma.fst h
    have h3 : π (X r) = σ (X ρ) := congrArg (fun p : Σ _ : Ω, K => p.2) h
    obtain ⟨h1, h2⟩ := Prod.mk.inj ha
    subst h1
    have hy : y' = y'' := by
      have := congrArg (fun τ : Equiv.Perm K => τ (X r)) h2
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at this
      exact this
    subst hy
    rw [h3] at h2
    have : π = σ := mul_left_cancel h2
    subst this
    rfl
  have hcard : E.card * (m - q) ≤ c * Fintype.card Ω :=
    hG.trans ((Finset.card_le_card_of_injOn φ hmaps hinj).trans hH)
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) < (m - q : ℝ) := by
    have : (q : ℝ) < m := by exact_mod_cast hq
    linarith
  rw [pr_def, div_le_div_iff₀ hΩ hM]
  have : ((E.card * (m - q) : ℕ) : ℝ) ≤ ((c * Fintype.card Ω : ℕ) : ℝ) := by
    exact_mod_cast hcard
  rw [Nat.cast_mul, Nat.cast_sub hq.le, Nat.cast_mul] at this
  exact this

end Sym

/-! ## Predicting the opening with forward and inverse queries -/

section Predict

variable {K R T : Type} [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R] [DecidableEq T]

/-- **Predicting the opening of a truncated permutation call, in the ideal-permutation model.**
`π` is a uniform permutation of `K`, `r` a uniform opening, `X` an injective encoding of `r` as an
input of `π`, and the commitment is `tr (π (X r))`. An oracle algorithm `A t` with forward and
inverse queries to `π`, at most `q` on every path, that outputs at most `c` candidates, has `r`
among them with probability at most

    (c + q) / (|R| − q) + q / (m − q),

`m` a lower bound on the number of states with a given truncation. -/
theorem pr_predict_perm_le (X : R → K) (hX : Function.Injective X) (tr : K → T)
    (A : T → PTree K (Finset R)) {q c m : ℕ} (hA : ∀ t, (A t).Bound q)
    (hc : ∀ t π, ((A t).run π).card ≤ c)
    (hm : ∀ t, m ≤ (univ.filter fun y => tr y = t).card) (hqR : q < Fintype.card R)
    (hqm : q < m) :
    pr (R × Equiv.Perm K) (fun z => z.1 ∈ (A (tr (z.2 (X z.1)))).run z.2) ≤
      (c + q) / (Fintype.card R - q : ℝ) + q / (m - q : ℝ) := by
  classical
  have : Nonempty R := Fintype.card_pos_iff.1 (by omega)
  -- The cut algorithms: a forward query at `x` names the opening encoded by `x`, an inverse query
  -- at `y` names the value `y`.
  let f : K → Finset R × Finset K := fun x => (univ.filter fun r => X r = x, ∅)
  let g : K → Finset R × Finset K := fun y => (∅, {y})
  let e : Finset R × Finset K := (∅, ∅)
  let B : ℕ → T → PTree K (Finset R × Finset K) := fun n t => PTree.cut f g e n (A t)
  have hBq : ∀ n, n < q → ∀ t π, ((B n t).ins π).card ≤ q := fun n hn t π =>
    (PTree.card_ins_le (PTree.bound_cut f g e n (A t)) π).trans hn.le
  have hf1 : ∀ x, (f x).1.card ≤ 1 := fun x =>
    Finset.card_le_one.2 fun a ha b hb => hX (by
      rw [Finset.mem_filter] at ha hb; rw [ha.2, hb.2])
  have hB1 : ∀ n t π, ((B n t).run π).1.card ≤ 1 ∧ ((B n t).run π).2.card ≤ 1 := by
    intro n t π
    rcases PTree.run_cut f g e n (A t) π with h | ⟨x, h⟩ | ⟨y, h⟩
    · rw [show (B n t).run π = e from h]; simp [e]
    · rw [show (B n t).run π = f x from h]; exact ⟨hf1 x, by simp [f]⟩
    · rw [show (B n t).run π = g y from h]; simp [g]
  -- The three cases.
  have hsplit : ∀ z : R × Equiv.Perm K, z.1 ∈ (A (tr (z.2 (X z.1)))).run z.2 →
      (z.1 ∈ (A (tr (z.2 (X z.1)))).run z.2 ∧ X z.1 ∉ (A (tr (z.2 (X z.1)))).ins z.2) ∨
      ∃ n : Fin q,
        (z.1 ∈ ((B n (tr (z.2 (X z.1)))).run z.2).1 ∧
          X z.1 ∉ (B n (tr (z.2 (X z.1)))).ins z.2) ∨
        (z.2 (X z.1) ∈ ((B n (tr (z.2 (X z.1)))).run z.2).2 ∧
          X z.1 ∉ (B n (tr (z.2 (X z.1)))).ins z.2) := by
    intro z hz
    by_cases hin : X z.1 ∈ (A (tr (z.2 (X z.1)))).ins z.2
    · right
      obtain ⟨n, hn, h1, h2⟩ := PTree.touch f g e (hA _) z.2 (X z.1) hin
      refine ⟨⟨n, hn⟩, ?_⟩
      rcases h2 with h2 | h2
      · left
        refine ⟨?_, h1⟩
        rw [show (B n (tr (z.2 (X z.1)))).run z.2 = f (X z.1) from h2]
        simp [f]
      · right
        refine ⟨?_, h1⟩
        rw [show (B n (tr (z.2 (X z.1)))).run z.2 = g (z.2 (X z.1)) from h2]
        simp [g]
    · exact Or.inl ⟨hz, hin⟩
  have h0 := pr_input_sym_le X hX tr (fun t π => (A t).run π) (fun t π => (A t).ins π)
    (fun t π => PTree.card_ins_le (hA t) π) hc (fun t π π' h => PTree.run_congr (A t) π π' h) hqR
  have h1 : ∀ n : Fin q, pr (R × Equiv.Perm K) (fun z =>
      z.1 ∈ ((B n (tr (z.2 (X z.1)))).run z.2).1 ∧ X z.1 ∉ (B n (tr (z.2 (X z.1)))).ins z.2) ≤
      1 / (Fintype.card R - q : ℝ) := by
    intro n
    have := pr_input_sym_le X hX tr (fun t π => ((B n t).run π).1) (fun t π => (B n t).ins π)
      (hBq n n.2) (c := 1) (fun t π => (hB1 n t π).1) (fun t π π' h => by
        have := PTree.run_congr (B n t) π π' h
        exact ⟨by rw [this.1], this.2⟩) hqR
    simpa using this
  have h2 : ∀ n : Fin q, pr (R × Equiv.Perm K) (fun z =>
      z.2 (X z.1) ∈ ((B n (tr (z.2 (X z.1)))).run z.2).2 ∧
        X z.1 ∉ (B n (tr (z.2 (X z.1)))).ins z.2) ≤ 1 / (m - q : ℝ) := by
    intro n
    have := pr_output_sym_le X tr (fun t π => ((B n t).run π).2) (fun t π => (B n t).ins π)
      (hBq n n.2) (c := 1) (fun t π => (hB1 n t π).2) (fun t π π' h => by
        have := PTree.run_congr (B n t) π π' h
        exact ⟨by rw [this.1], this.2⟩) hm hqm
    simpa using this
  refine (pr_mono hsplit).trans ((pr_or_le _ _).trans ?_)
  have h3 := (pr_exists_le_sum (ι := Fin q) fun n (z : R × Equiv.Perm K) =>
    (z.1 ∈ ((B n (tr (z.2 (X z.1)))).run z.2).1 ∧ X z.1 ∉ (B n (tr (z.2 (X z.1)))).ins z.2) ∨
    (z.2 (X z.1) ∈ ((B n (tr (z.2 (X z.1)))).run z.2).2 ∧
      X z.1 ∉ (B n (tr (z.2 (X z.1)))).ins z.2)).trans
    (Finset.sum_le_sum fun n _ => (pr_or_le _ _).trans (add_le_add (h1 n) (h2 n)))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  refine (add_le_add h0 h3).trans (le_of_eq ?_)
  ring

end Predict

/-! ## The (PU) game in the ideal-permutation model -/

section Perm

variable {K N R T Aux : Type} [Fintype K] [DecidableEq K] [Fintype N] [Nonempty N] [Fintype R]
  [DecidableEq R] [DecidableEq T] [Fintype Aux] [Nonempty Aux]

/-- **A commitment that is one truncated call of `f`**: `com n r = tr (f (X n r))`. With `f`
Keccak-p[800,12] this is `Com` (`Privacy/PUKeccak.lean`). -/
def comP (f : K → K) (X : N → R → K) (tr : K → T) : N → R → T := fun n r => tr (f (X n r))

/-- **The (PU) advantage in the ideal-permutation model**: the permutation `π` is uniform, and the
predictor is an oracle algorithm `A n t aux` with forward and inverse queries to it. This is the
average over `π` of `puAdv (comP π X tr) (fun n t a => (A n t a).run π)` (`puAdvPerm_eq`). -/
noncomputable def puAdvPerm (X : N → R → K) (tr : K → T)
    (A : N → T → Aux → PTree K (Finset R)) : ℝ :=
  pr ((N × Aux) × (R × Equiv.Perm K)) fun z =>
    z.2.1 ∈ (A z.1.1 (tr (z.2.2 (X z.1.1 z.2.1))) z.1.2).run z.2.2

omit [Nonempty N] [DecidableEq R] [DecidableEq T] [Nonempty Aux] in
/-- `puAdvPerm` is `puAdv` of the predictor run with `π`, averaged over the permutation. -/
theorem puAdvPerm_eq (X : N → R → K) (tr : K → T) (A : N → T → Aux → PTree K (Finset R)) :
    puAdvPerm X tr A = (∑ π : Equiv.Perm K, puAdv (comP (⇑π) X tr)
      (fun n t a => (A n t a).run π)) / Fintype.card (Equiv.Perm K) := by
  let e : Equiv.Perm K × ((N × R) × Aux) ≃ (N × Aux) × (R × Equiv.Perm K) :=
    { toFun := fun z => ((z.2.1.1, z.2.2), (z.2.1.2, z.1))
      invFun := fun z => (z.2.2, ((z.1.1, z.2.1), z.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold puAdvPerm
  rw [← pr_equiv e, pr_prod]
  rfl

/-- **(PU) in the ideal-permutation model.** If `X n` is injective for every public part, the
predictor makes at most `q` queries and outputs at most `c` candidates, and every truncation has at
least `m` preimages, then

    puAdvPerm X tr A ≤ (c + q) / (|R| − q) + q / (m − q). -/
theorem puAdvPerm_le (X : N → R → K) (hX : ∀ n, Function.Injective (X n)) (tr : K → T)
    (A : N → T → Aux → PTree K (Finset R)) {q c m : ℕ} (hA : ∀ n t a, (A n t a).Bound q)
    (hc : ∀ n t a π, ((A n t a).run π).card ≤ c)
    (hm : ∀ t, m ≤ (univ.filter fun y => tr y = t).card) (hqR : q < Fintype.card R)
    (hqm : q < m) :
    puAdvPerm X tr A ≤ (c + q) / (Fintype.card R - q : ℝ) + q / (m - q : ℝ) := by
  unfold puAdvPerm
  rw [pr_prod]
  have hNA : (0 : ℝ) < Fintype.card (N × Aux) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hNA]
  calc ∑ a : N × Aux, pr (R × Equiv.Perm K) (fun b =>
        b.1 ∈ (A a.1 (tr (b.2 (X a.1 b.1))) a.2).run b.2)
      ≤ ∑ _a : N × Aux, ((c + q) / (Fintype.card R - q : ℝ) + q / (m - q : ℝ)) :=
        Finset.sum_le_sum fun a _ => pr_predict_perm_le (X a.1) (hX a.1) tr
          (fun t => A a.1 t a.2) (fun t => hA a.1 t a.2) (fun t π => hc a.1 t a.2 π) hm hqR hqm
    _ = ((c + q) / (Fintype.card R - q : ℝ) + q / (m - q : ℝ)) * Fintype.card (N × Aux) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

end Perm

end VoleMole.Privacy.PU
